# tiny-chess engine — original code, written for make.fun tiny-chess-01.
# 0x88 board, negamax + alpha-beta + quiescence, transposition table,
# killer moves, piece-square evaluation. Fixed node budget per move
# (no clock anywhere in the search), so replays are deterministic.
import json
import os
import random
import sys
import urllib.error
import urllib.request

# Pieces: white 1..6 (P N B R Q K), black 9..14.
P, N, B, R, Q, K = 1, 2, 3, 4, 5, 6
VAL = (0, 100, 320, 330, 500, 900, 0, 0, 0, 100, 320, 330, 500, 900, 0)
KN = (31, 33, 14, 18, -31, -33, -14, -18)
KG = (1, -1, 16, -16, 15, 17, -15, -17)
BD = (15, 17, -15, -17)
RD = (1, -1, 16, -16)
QD = BD + RD
MATE = 100000
INF = 10000000
NODES = 100000  # fixed node budget per move
# NOTE: null-move and delta pruning were tested and HURT (-350 Elo on
# trial 0: both flip winning games to losses), so they are not used.
SQ64 = tuple(r * 16 + f for r in range(8) for f in range(8))
# Castling-rights keep-mask: 15 everywhere, cleared on the king/rook squares.
CKEEP = [15] * 128
CKEEP[0] = 15 & ~2
CKEEP[7] = 15 & ~1
CKEEP[4] = 15 & ~3
CKEEP[112] = 15 & ~8
CKEEP[119] = 15 & ~4
CKEEP[116] = 15 & ~12

# Piece-square tables, rank 8 first, white's view; encoded as
# one char per square (value/5 + 10: 'a'=-50 .. 'k'=0 .. 'u'=+50).
PAWN_T = "kkkkuuuummoqllmpkkkoljiklmmgkkkk"
KNIGHT_T = "aceecgkkekmnelnoeknoelmncgklacee"
BISHOP_T = "giiiikkkiklmillmikmmimmmilkkgiii"
ROOK_T = "kkkklmmmjkkkjkkkjkkkjkkkjkkkkkkl"
QUEEN_T = "giijjiigikkkkkkiikllllkijkllllkjkkllllkjilllllkiiklkkkkigiijjiig"
KING_T = "eccaeccaeccaeccageecigggookkoqmk"
KING_EG_T = "acegegikeioqeiqseiqseioqeekkaeee"


def _mk(s, mir):
    # s: one char per square, value/5 + 10 ('a'=-50 .. 'k'=0 .. 'u'=+50).
    # mir: only files a-d stored, mirror to e-h (QUEEN_T is not symmetric).
    a = [0] * 128
    w = 4 if mir else 8
    for r in range(8):
        for f in range(8):
            c = min(f, 7 - f) if mir else f
            a[r * 16 + f] = (ord(s[(7 - r) * w + c]) - 107) * 5
    return tuple(a)


PST = (None, _mk(PAWN_T, 1), _mk(KNIGHT_T, 1), _mk(BISHOP_T, 1),
       _mk(ROOK_T, 1), _mk(QUEEN_T, 0), _mk(KING_T, 1))
PSTKEG = _mk(KING_EG_T, 1)

# Deterministic Zobrist keys (fixed seed: same every run).
_rng = random.Random(0x5EED)
Z = [[_rng.getrandbits(64) for _ in range(128)] for _ in range(15)]
ZC = [_rng.getrandbits(64) for _ in range(16)]
ZE = [_rng.getrandbits(64) for _ in range(8)]
ZS = _rng.getrandbits(64)

# Mutable board state.
BRD = [0] * 128
STM = 0  # 0 white, 1 black
CST = 0  # bits 1 WK 2 WQ 4 BK 8 BQ
EPS = -1
HSH = 0
KSQ = [4, 116]
NODES_USED = 0
TT = {}
KIL = [[0, 0] for _ in range(256)]


class Abort(Exception):
    pass


def parse_fen(fen):
    """FEN -> (board, stm, castle, ep, hash, king_squares)."""
    b = [0] * 128
    parts = fen.split()
    ksq = [4, 116]
    for i, row in enumerate(parts[0].split("/")):
        r = 7 - i
        f = 0
        for c in row:
            if c.isdigit():
                f += int(c)
            else:
                pc = "PNBRQK".index(c.upper()) + 1
                if c.islower():
                    pc += 8
                sq = r * 16 + f
                b[sq] = pc
                if pc & 7 == K:
                    ksq[pc >> 3] = sq
                f += 1
    stm = 0 if parts[1] == "w" else 1
    cst = 0
    if parts[2] != "-":
        for c in parts[2]:
            cst |= {"K": 1, "Q": 2, "k": 4, "q": 8}[c]
    ep = -1
    if parts[3] != "-":
        ep = (int(parts[3][1]) - 1) * 16 + "abcdefgh".index(parts[3][0])
    h = 0
    for sq in SQ64:
        pc = b[sq]
        if pc:
            h ^= Z[pc][sq]
    if stm:
        h ^= ZS
    h ^= ZC[cst]
    if ep >= 0:
        h ^= ZE[ep & 7]
    return b, stm, cst, ep, h, ksq


def load_fen(fen):
    global BRD, STM, CST, EPS, HSH, KSQ
    BRD, STM, CST, EPS, HSH, KSQ = parse_fen(fen)


def attacked(sq, by):
    """Is sq attacked by colour `by` (0 white, 1 black)?"""
    b = BRD
    if by == 0:
        for t in (sq - 15, sq - 17):
            if not t & 0x88 and b[t] == P:
                return True
        pn, pb, pr, pq, pk = N, B, R, Q, K
    else:
        for t in (sq + 15, sq + 17):
            if not t & 0x88 and b[t] == P + 8:
                return True
        pn, pb, pr, pq, pk = N + 8, B + 8, R + 8, Q + 8, K + 8
    for o in KN:
        t = sq + o
        if not t & 0x88 and b[t] == pn:
            return True
    for o in KG:
        t = sq + o
        if not t & 0x88 and b[t] == pk:
            return True
    for i, o in enumerate(QD):
        t = sq + o
        while not t & 0x88:
            pc = b[t]
            if pc:
                if pc == pq or (i < 4 and pc == pb) or (i >= 4 and pc == pr):
                    return True
                break
            t += o
    return False


def gen(caps):
    """Pseudo-legal moves for the side to move. Move int: f | t<<7 | pr<<14."""
    ms = []
    b = BRD
    stm = STM
    for sq in SQ64:
        pc = b[sq]
        if not pc or (pc >> 3) != stm:
            continue
        t = pc & 7
        if t == P:
            step = 16 if stm == 0 else -16
            start = 1 if stm == 0 else 6
            last = 6 if stm == 0 else 1
            t1 = sq + step
            if b[t1] == 0:
                if (sq >> 4) == last:
                    for pr in (5, 4, 3, 2):
                        ms.append(sq | (t1 << 7) | (pr << 14))
                elif not caps:
                    ms.append(sq | (t1 << 7))
                    if (sq >> 4) == start and b[sq + 2 * step] == 0:
                        ms.append(sq | ((sq + 2 * step) << 7))
            for t2 in (sq + step - 1, sq + step + 1):
                if t2 & 0x88:
                    continue
                q = b[t2]
                if q and (q >> 3) != stm:
                    if (sq >> 4) == last:
                        for pr in (5, 4, 3, 2):
                            ms.append(sq | (t2 << 7) | (pr << 14))
                    else:
                        ms.append(sq | (t2 << 7))
                elif t2 == EPS:
                    ms.append(sq | (t2 << 7))
        elif t == N or t == K:
            for o in KN if t == N else KG:
                t2 = sq + o
                if t2 & 0x88:
                    continue
                q = b[t2]
                if not q:
                    if not caps:
                        ms.append(sq | (t2 << 7))
                elif (q >> 3) != stm:
                    ms.append(sq | (t2 << 7))
            if t == K and not caps:
                for bit, kf, kt, rf, em, at in (
                        (1, 4, 6, 7, (5, 6), (4, 5, 6)),
                        (2, 4, 2, 0, (3, 2, 1), (4, 3, 2)),
                        (4, 116, 118, 119, (117, 118), (116, 117, 118)),
                        (8, 116, 114, 112, (115, 114, 113), (116, 115, 114))):
                    if (CST & bit and b[rf] == R + 8 * stm
                            and all(b[s] == 0 for s in em)
                            and not any(attacked(s, 1 - stm) for s in at)):
                        ms.append(kf | (kt << 7))
        else:
            for o in BD if t == B else RD if t == R else QD:
                t2 = sq + o
                while not t2 & 0x88:
                    q = b[t2]
                    if not q:
                        if not caps:
                            ms.append(sq | (t2 << 7))
                    else:
                        if (q >> 3) != stm:
                            ms.append(sq | (t2 << 7))
                        break
                    t2 += o
    return ms


def make(m):
    """Play move m; return an undo record."""
    global STM, CST, EPS, HSH
    f = m & 127
    t = (m >> 7) & 127
    pr = (m >> 14) & 7
    b = BRD
    pc = b[f]
    cap = b[t]
    cs = t
    oc = CST
    oe = EPS
    oh = HSH
    HSH ^= Z[pc][f]
    if (pc & 7) == P and t == EPS and cap == 0:
        cs = t - 16 if pc == P else t + 16
        cap = b[cs]
        b[cs] = 0
    if cap:
        HSH ^= Z[cap][cs]
    b[f] = 0
    npc = pc
    if pr:
        npc = pr + (8 if pc > 8 else 0)
    b[t] = npc
    HSH ^= Z[npc][t]
    if (pc & 7) == K and abs(t - f) == 2:
        if t > f:
            rf, rt = t + 1, t - 1
        else:
            rf, rt = t - 2, t + 1
        rp = b[rf]
        b[rt] = rp
        b[rf] = 0
        HSH ^= Z[rp][rf] ^ Z[rp][rt]
    CST &= CKEEP[f] & CKEEP[t]
    if CST != oc:
        HSH ^= ZC[oc] ^ ZC[CST]
    ne = -1
    if (pc & 7) == P and abs(t - f) == 32:
        ne = (f + t) // 2
    if oe >= 0:
        HSH ^= ZE[oe & 7]
    if ne >= 0:
        HSH ^= ZE[ne & 7]
    EPS = ne
    if (pc & 7) == K:
        KSQ[STM] = t
    STM ^= 1
    HSH ^= ZS
    return (m, cap, cs, oc, oe, oh, pc)


def unmake(u):
    """Undo a move made by make()."""
    global STM, CST, EPS, HSH
    m, cap, cs, oc, oe, oh, pc = u
    f = m & 127
    t = (m >> 7) & 127
    pr = (m >> 14) & 7
    b = BRD
    STM ^= 1
    if (pc & 7) == K:
        KSQ[STM] = f
    if (pc & 7) == K and abs(t - f) == 2:
        if t > f:
            rf, rt = t + 1, t - 1
        else:
            rf, rt = t - 2, t + 1
        b[rf] = b[rt]
        b[rt] = 0
    b[f] = pc
    b[t] = 0
    if cap:
        b[cs] = cap
    CST = oc
    EPS = oe
    HSH = oh


def legal(m):
    u = make(m)
    ok = not attacked(KSQ[STM ^ 1], STM)
    unmake(u)
    return ok


def gen_legal(caps):
    return [m for m in gen(caps) if legal(m)]


def ev():
    """Static evaluation from the side-to-move's view (centipawns)."""
    s = 0
    b = BRD
    wb = bb = 0
    wq = bq = False
    wks = bks = 0
    for sq in SQ64:
        pc = b[sq]
        if not pc:
            continue
        if pc < 8:
            s += VAL[pc] + PST[pc][sq]
            if pc == B:
                wb += 1
            elif pc == Q:
                wq = True
            elif pc == K:
                wks = sq
        else:
            s -= VAL[pc] + PST[pc - 8][sq ^ 0x70]
            if pc == B + 8:
                bb += 1
            elif pc == Q + 8:
                bq = True
            elif pc == K + 8:
                bks = sq
    if wb == 2:
        s += 30
    if bb == 2:
        s -= 30
    if not wq and not bq:
        s += PSTKEG[wks] - PST[K][wks]
        s -= PSTKEG[bks ^ 0x70] - PST[K][bks ^ 0x70]
    return s if STM == 0 else -s


def oscore(m, ttm, ply):
    """Move-ordering score: TT move, captures (MVV-LVA), killers."""
    if m == ttm:
        return 1 << 28
    f = m & 127
    t = (m >> 7) & 127
    pr = (m >> 14) & 7
    v = BRD[t]
    if not v and (BRD[f] & 7) == P and t == EPS:
        v = P + 8 if STM == 0 else P
    if v:
        return (1 << 24) + VAL[v & 7] * 16 - VAL[BRD[f] & 7] // 16 + pr * 256
    if pr:
        return (1 << 23) + pr * 256
    if m == KIL[ply][0]:
        return 1 << 22
    if m == KIL[ply][1]:
        return 1 << 21
    return 0


def order(ms, ttm, ply):
    return [m for _, m in sorted(((oscore(m, ttm, ply), m) for m in ms),
                                 reverse=True)]


def qs(a, b, ply):
    """Quiescence: captures (and promotions) only; all evasions in check."""
    global NODES_USED
    NODES_USED += 1
    if NODES_USED > NODES:
        raise Abort
    if attacked(KSQ[STM], STM ^ 1):
        best = -INF
        for m in order(gen(False), 0, ply):
            u = make(m)
            if attacked(KSQ[STM ^ 1], STM):
                unmake(u)
                continue
            v = -qs(-b, -a, ply + 1)
            unmake(u)
            if v > best:
                best = v
            if best > a:
                a = best
            if a >= b:
                return b
        return best if best > -INF else -MATE + ply
    stand = ev()
    if stand >= b:
        return b
    if stand > a:
        a = stand
    for m in order(gen(True), 0, ply):
        u = make(m)
        if attacked(KSQ[STM ^ 1], STM):
            unmake(u)
            continue
        v = -qs(-b, -a, ply + 1)
        unmake(u)
        if v >= b:
            return b
        if v > a:
            a = v
    return a


def search(d, a, b, ply):
    global NODES_USED
    NODES_USED += 1
    if NODES_USED > NODES:
        raise Abort
    if d <= 0:
        return qs(a, b, ply)
    e = TT.get(HSH)
    ttm = 0
    if e:
        if e[0] >= d:
            if e[1] == 0:
                return e[2]
            if e[1] == 1 and e[2] >= b:
                return e[2]
            if e[1] == 2 and e[2] <= a:
                return e[2]
        ttm = e[3]
    best = -INF
    bestm = 0
    legal_n = 0
    oa = a
    for m in order(gen(False), ttm, ply):
        u = make(m)
        if attacked(KSQ[STM ^ 1], STM):
            unmake(u)
            continue
        legal_n += 1
        v = -search(d - 1, -b, -a, ply + 1)
        unmake(u)
        if v > best:
            best = v
            bestm = m
        if v > a:
            a = v
        if a >= b:
            if not u[1]:
                KIL[ply][1] = KIL[ply][0]
                KIL[ply][0] = m
            break
    if legal_n == 0:
        return -MATE + ply if attacked(KSQ[STM], STM ^ 1) else 0
    if best <= oa:
        flag = 2
    elif best >= b:
        flag = 1
    else:
        flag = 0
    TT[HSH] = (d, flag, best, bestm)
    if len(TT) > 300000:
        TT.clear()
    return best


def root_depth(d, moves, prev):
    """Search the root moves at depth d; return (value, best move)."""
    alpha = -INF
    best = prev
    ordered = [prev] + [m for m in moves if m != prev]
    for i, m in enumerate(ordered):
        u = make(m)
        if i == 0:
            v = -search(d - 1, -INF, INF, 1)
        else:
            v = -search(d - 1, -alpha - 1, -alpha, 1)
            if v > alpha:
                v = -search(d - 1, -INF, -alpha, 1)
        unmake(u)
        if v > alpha:
            alpha = v
            best = m
    return alpha, best


def choose(legal_uci, hist):
    """Best move (ranked list: best first) for the current position."""
    global NODES_USED
    moves = gen_legal(False)
    envset = set(legal_uci)
    moves = [m for m in moves if uci(m) in envset]
    if not moves:
        moves = [parse_uci(legal_uci[0])]
    pool = []
    for m in moves:
        u = make(m)
        h = HSH
        unmake(u)
        if hist.count(h) < 2:
            pool.append(m)
    if pool:
        moves = pool
    best = moves[0]
    bestv = -INF
    NODES_USED = 0
    try:
        for d in range(1, 64):
            v, m = root_depth(d, moves, best)
            best, bestv = m, v
            if v >= MATE - 1000:
                break
    except Abort:
        pass
    return [best] + [m for m in moves if m != best]


def uci(m):
    f = m & 127
    t = (m >> 7) & 127
    pr = (m >> 14) & 7
    a = "abcdefgh"
    s = a[f & 7] + str((f >> 4) + 1) + a[t & 7] + str((t >> 4) + 1)
    return s + "nbrq"[pr - 2] if pr else s


def parse_uci(s):
    f = "abcdefgh".index(s[0]) + (int(s[1]) - 1) * 16
    t = "abcdefgh".index(s[2]) + (int(s[3]) - 1) * 16
    pr = "nbrq".index(s[4]) + 2 if len(s) > 4 else 0
    return f | (t << 7) | (pr << 14)


def sync(g):
    """Replay the game's moves from start_fen; return the position history."""
    load_fen(g["start_fen"])
    hist = [HSH]
    for u in g["moves"]:
        m = parse_uci(u)
        if not m:
            break
        make(m)
        hist.append(HSH)
    if parse_fen(g["fen"])[4] != HSH:
        # Replay disagrees with the env's FEN: trust the FEN.
        load_fen(g["fen"])
        hist = [HSH]
    return hist


ENV = ""


def post(path, body):
    req = urllib.request.Request(
        ENV + path,
        data=json.dumps(body).encode(),
        headers={"content-type": "application/json"},
    )
    try:
        with urllib.request.urlopen(req) as res:
            return json.load(res)
    except urllib.error.HTTPError as e:
        sys.exit(f"{path}: HTTP {e.code} {e.read().decode(errors='replace')}")


def main():
    global ENV
    ENV = os.environ.get("MAKEFUN_ENV_URL") or sys.exit("MAKEFUN_ENV_URL not set")
    while True:
        g = post("/game", {})
        if g["status"] == "done":
            break
        hist = sync(g)
        while g["status"] == "your_move":
            moved = False
            for m in choose(g["legal_moves"], hist):
                r = post("/move", {"game": g["game"], "move": uci(m)})
                if r.get("status") in ("your_move", "over"):
                    g = r
                    hist = sync(g)
                    moved = True
                    break
            if not moved:
                post("/resign", {"game": g["game"]})
                break
        print(f"game {g['game']}: {g.get('outcome')} by {g.get('reason')}",
              file=sys.stderr)
    print(f"done: {g.get('wins')} won, {g.get('draws')} drawn, "
          f"{g.get('losses')} lost", file=sys.stderr)


if __name__ == "__main__":
    main()
