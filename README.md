# tiny-chess-01 entry: NapLan Chess

An original chess engine in Python, written for make.fun's
"Build the strongest chess engine in 4 KB of Python" bounty.

- 0x88 board, negamax + alpha-beta with a transposition table,
  killer moves and MVV-LVA ordering
- Quiescence search over captures and promotions (all evasions
  when in check)
- Evaluation: material + piece-square tables, bishop-pair bonus,
  endgame king table
- Fixed node budget per move (no clock): every replay plays the
  same moves

## Run it

The entry is `main.py` (the whole engine, packed). It plays the
gauntlet through the env at `$MAKEFUN_ENV_URL`:

```sh
MAKEFUN_ENV_URL=http://127.0.0.1:8080 python3 main.py
```

The readable source it was packed from is `engine.py` (kept beside
the entry; the kit's `compress` command packed it).

## License

MIT — see LICENSE.
