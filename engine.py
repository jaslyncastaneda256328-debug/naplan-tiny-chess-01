import json,os,random,sys,urllib.error,urllib.request
P,N,B,R,Q,K=1,2,3,4,5,6
V=(0,100,320,330,500,900,0,0,0,100,320,330,500,900,0)
KN=(31,33,14,18,-31,-33,-14,-18)
KG=(1,-1,16,-16,15,17,-15,-17)
BD=(15,17,-15,-17)
RD=(1,-1,16,-16)
QD=BD+RD
MT=100000
IN=10000000
ND=100000
S64=tuple(r*16+f for r in range(8) for f in range(8))
CK=[15]*128
CK[0]=13;CK[7]=14;CK[4]=12;CK[112]=7;CK[119]=11;CK[116]=3
PT="kkkkuuuummoqllmpkkkoljiklmmgkkkk"
NT="aceecgkkekmnelnoeknoelmncgklacee"
BT="giiiikkkiklmillmikmmimmmilkkgiii"
RT="kkkklmmmjkkkjkkkjkkkjkkkjkkkkkkl"
QT="giijjiigikkkkkkiikllllkijkllllkjkkllllkjilllllkiiklkkkkigiijjiig"
KT="eccaeccaeccaeccageecigggookkoqmk"
ET="acegegikeioqeiqseiqseioqeekkaeee"
def mk(s,m):
  a=[0]*128;w=4 if m else 8
  for r in range(8):
    for f in range(8):
      c=min(f,7-f) if m else f
      a[r*16+f]=(ord(s[(7-r)*w+c])-107)*5
  return tuple(a)
PS=(None,mk(PT,1),mk(NT,1),mk(BT,1),mk(RT,1),mk(QT,0),mk(KT,1))
PE=mk(ET,1)
_g=random.Random(0x5EED)
Z=[[_g.getrandbits(64) for _ in range(128)] for _ in range(15)]
ZC=[_g.getrandbits(64) for _ in range(16)]
ZE=[_g.getrandbits(64) for _ in range(8)]
ZS=_g.getrandbits(64)
BR=[0]*128
ST=0
CS=0
EP=-1
HS=0
KQ=[4,116]
NU=0
TT={}
KL=[[0,0] for _ in range(256)]
class A(Exception):pass
def pf(f):
  b=[0]*128;p=f.split();k=[4,116]
  for i,row in enumerate(p[0].split("/")):
    r=7-i;ff=0
    for c in row:
      if c.isdigit():ff+=int(c)
      else:
        v="PNBRQK".index(c.upper())+1+(8 if c.islower() else 0)
        s=r*16+ff;b[s]=v
        if v&7==K:k[v>>3]=s
        ff+=1
  st=0 if p[1]=="w" else 1
  cs=0
  if p[2]!="-":
    for c in p[2]:cs|={"K":1,"Q":2,"k":4,"q":8}[c]
  ep=-1
  if p[3]!="-":ep=(int(p[3][1])-1)*16+"abcdefgh".index(p[3][0])
  h=0
  for s in S64:
    v=b[s]
    if v:h^=Z[v][s]
  if st:h^=ZS
  h^=ZC[cs]
  if ep>=0:h^=ZE[ep&7]
  return b,st,cs,ep,h,k
def lf(f):
  global BR,ST,CS,EP,HS,KQ
  BR,ST,CS,EP,HS,KQ=pf(f)
def at(sq,by):
  b=BR
  if by==0:
    for t in (sq-15,sq-17):
      if not t&0x88 and b[t]==P:return True
    pn,pb,pr,pq,pk=N,B,R,Q,K
  else:
    for t in (sq+15,sq+17):
      if not t&0x88 and b[t]==P+8:return True
    pn,pb,pr,pq,pk=N+8,B+8,R+8,Q+8,K+8
  for o in KN:
    t=sq+o
    if not t&0x88 and b[t]==pn:return True
  for o in KG:
    t=sq+o
    if not t&0x88 and b[t]==pk:return True
  for i,o in enumerate(QD):
    t=sq+o
    while not t&0x88:
      v=b[t]
      if v:
        if v==pq or (i<4 and v==pb) or (i>=4 and v==pr):return True
        break
      t+=o
  return False
def gn(caps):
  ms=[]
  b=BR;s=ST
  for sq in S64:
    pc=b[sq]
    if not pc or pc>>3!=s:continue
    t=pc&7
    if t==P:
      st=16 if s==0 else -16
      sr=1 if s==0 else 6
      lr=6 if s==0 else 1
      t1=sq+st
      if b[t1]==0:
        if sq>>4==lr:
          for pr in (5,4,3,2):ms.append(sq|(t1<<7)|(pr<<14))
        elif not caps:
          ms.append(sq|(t1<<7))
          if sq>>4==sr and b[sq+2*st]==0:ms.append(sq|((sq+2*st)<<7))
      for t2 in (sq+st-1,sq+st+1):
        if t2&0x88:continue
        v=b[t2]
        if v and v>>3!=s:
          if sq>>4==lr:
            for pr in (5,4,3,2):ms.append(sq|(t2<<7)|(pr<<14))
          else:ms.append(sq|(t2<<7))
        elif t2==EP:ms.append(sq|(t2<<7))
    elif t==N or t==K:
      for o in KN if t==N else KG:
        t2=sq+o
        if t2&0x88:continue
        v=b[t2]
        if not v:
          if not caps:ms.append(sq|(t2<<7))
        elif v>>3!=s:ms.append(sq|(t2<<7))
      if t==K and not caps:
        for bit,kf,kt,rf,em,aq in ((1,4,6,7,(5,6),(4,5,6)),(2,4,2,0,(3,2,1),(4,3,2)),(4,116,118,119,(117,118),(116,117,118)),(8,116,114,112,(115,114,113),(116,115,114))):
          if CS&bit and b[rf]==R+8*s and all(b[x]==0 for x in em) and not any(at(x,1-s) for x in aq):ms.append(kf|(kt<<7))
    else:
      for o in BD if t==B else RD if t==R else QD:
        t2=sq+o
        while not t2&0x88:
          v=b[t2]
          if not v:
            if not caps:ms.append(sq|(t2<<7))
          else:
            if v>>3!=s:ms.append(sq|(t2<<7))
            break
          t2+=o
  return ms
def mv(m):
  global ST,CS,EP,HS
  f=m&127;t=(m>>7)&127;pr=(m>>14)&7
  b=BR;pc=b[f];cap=b[t];cs=t;oc=CS;oe=EP;oh=HS
  HS^=Z[pc][f]
  if (pc&7)==P and t==EP and cap==0:
    cs=t-16 if pc==P else t+16
    cap=b[cs];b[cs]=0
  if cap:HS^=Z[cap][cs]
  b[f]=0
  npc=pc
  if pr:npc=pr+(8 if pc>8 else 0)
  b[t]=npc;HS^=Z[npc][t]
  if (pc&7)==K and abs(t-f)==2:
    if t>f:rf,rt=t+1,t-1
    else:rf,rt=t-2,t+1
    rp=b[rf];b[rt]=rp;b[rf]=0;HS^=Z[rp][rf]^Z[rp][rt]
  CS&=CK[f]&CK[t]
  if CS!=oc:HS^=ZC[oc]^ZC[CS]
  ne=-1
  if (pc&7)==P and abs(t-f)==32:ne=(f+t)//2
  if oe>=0:HS^=ZE[oe&7]
  if ne>=0:HS^=ZE[ne&7]
  EP=ne
  if (pc&7)==K:KQ[ST]=t
  ST^=1;HS^=ZS
  return (m,cap,cs,oc,oe,oh,pc)
def uv(u):
  global ST,CS,EP,HS
  m,cap,cs,oc,oe,oh,pc=u
  f=m&127;t=(m>>7)&127;pr=(m>>14)&7
  b=BR
  ST^=1
  if (pc&7)==K:KQ[ST]=f
  if (pc&7)==K and abs(t-f)==2:
    if t>f:rf,rt=t+1,t-1
    else:rf,rt=t-2,t+1
    b[rf]=b[rt];b[rt]=0
  b[f]=pc;b[t]=0
  if cap:b[cs]=cap
  CS=oc;EP=oe;HS=oh
def lg(m):
  u=mv(m)
  ok=not at(KQ[ST^1],ST)
  uv(u)
  return ok
def gl(caps):
  return [m for m in gn(caps) if lg(m)]
def ev():
  s=0;b=BR;wb=bb=0;wq=bq=False;wks=bks=0
  for sq in S64:
    pc=b[sq]
    if not pc:continue
    if pc<8:
      s+=V[pc]+PS[pc][sq]
      if pc==B:wb+=1
      elif pc==Q:wq=True
      elif pc==K:wks=sq
    else:
      s-=V[pc]+PS[pc-8][sq^0x70]
      if pc==B+8:bb+=1
      elif pc==Q+8:bq=True
      elif pc==K+8:bks=sq
  if wb==2:s+=30
  if bb==2:s-=30
  if not wq and not bq:
    s+=PE[wks]-PS[K][wks]
    s-=PE[bks^0x70]-PS[K][bks^0x70]
  return s if ST==0 else -s
def os(m,ttm,ply):
  if m==ttm:return 1<<28
  f=m&127;t=(m>>7)&127;pr=(m>>14)&7
  v=BR[t]
  if not v and (BR[f]&7)==P and t==EP:v=P+8 if ST==0 else P
  if v:return (1<<24)+V[v&7]*16-V[BR[f]&7]//16+pr*256
  if pr:return (1<<23)+pr*256
  if m==KL[ply][0]:return 1<<22
  if m==KL[ply][1]:return 1<<21
  return 0
def od(ms,ttm,ply):
  return [m for _,m in sorted(((os(m,ttm,ply),m) for m in ms),reverse=True)]
def qs(a,b,ply):
  global NU
  NU+=1
  if NU>ND:raise A
  if at(KQ[ST],ST^1):
    best=-IN
    for m in od(gn(False),0,ply):
      u=mv(m)
      if at(KQ[ST^1],ST):
        uv(u);continue
      v=-qs(-b,-a,ply+1)
      uv(u)
      if v>best:best=v
      if best>a:a=best
      if a>=b:return b
    return best if best>-IN else -MT+ply
  stand=ev()
  if stand>=b:return b
  if stand>a:a=stand
  for m in od(gn(True),0,ply):
    u=mv(m)
    if at(KQ[ST^1],ST):
      uv(u);continue
    v=-qs(-b,-a,ply+1)
    uv(u)
    if v>=b:return b
    if v>a:a=v
  return a
def se(d,a,b,ply):
  global NU
  NU+=1
  if NU>ND:raise A
  if d<=0:return qs(a,b,ply)
  e=TT.get(HS)
  ttm=0
  if e:
    if e[0]>=d:
      if e[1]==0:return e[2]
      if e[1]==1 and e[2]>=b:return e[2]
      if e[1]==2 and e[2]<=a:return e[2]
    ttm=e[3]
  best=-IN;bestm=0;ln=0;oa=a
  for m in od(gn(False),ttm,ply):
    u=mv(m)
    if at(KQ[ST^1],ST):
      uv(u);continue
    ln+=1
    v=-se(d-1,-b,-a,ply+1)
    uv(u)
    if v>best:best=v;bestm=m
    if v>a:a=v
    if a>=b:
      if not u[1]:
        KL[ply][1]=KL[ply][0];KL[ply][0]=m
      break
  if ln==0:return -MT+ply if at(KQ[ST],ST^1) else 0
  if best<=oa:flag=2
  elif best>=b:flag=1
  else:flag=0
  TT[HS]=(d,flag,best,bestm)
  if len(TT)>300000:TT.clear()
  return best
def rd(d,moves,prev):
  alpha=-IN;best=prev
  ordered=[prev]+[m for m in moves if m!=prev]
  for i,m in enumerate(ordered):
    u=mv(m)
    if i==0:v=-se(d-1,-IN,IN,1)
    else:
      v=-se(d-1,-alpha-1,-alpha,1)
      if v>alpha:v=-se(d-1,-IN,-alpha,1)
    uv(u)
    if v>alpha:alpha=v;best=m
  return alpha,best
def ch(legal_uci,hist):
  global NU
  moves=gl(False)
  envset=set(legal_uci)
  moves=[m for m in moves if uc(m) in envset]
  if not moves:moves=[pu(legal_uci[0])]
  pool=[]
  for m in moves:
    u=mv(m);h=HS;uv(u)
    if hist.count(h)<2:pool.append(m)
  if pool:moves=pool
  best=moves[0];bestv=-IN
  NU=0
  try:
    for d in range(1,64):
      v,m=rd(d,moves,best)
      best,bestv=m,v
      if v>=MT-1000:break
  except A:pass
  return [best]+[m for m in moves if m!=best]
def uc(m):
  f=m&127;t=(m>>7)&127;pr=(m>>14)&7
  a="abcdefgh"
  s=a[f&7]+str((f>>4)+1)+a[t&7]+str((t>>4)+1)
  return s+"nbrq"[pr-2] if pr else s
def pu(s):
  f="abcdefgh".index(s[0])+(int(s[1])-1)*16
  t="abcdefgh".index(s[2])+(int(s[3])-1)*16
  pr="nbrq".index(s[4])+2 if len(s)>4 else 0
  return f|(t<<7)|(pr<<14)
def sy(g):
  lf(g["start_fen"])
  hist=[HS]
  for u in g["moves"]:
    m=pu(u)
    if not m:break
    mv(m);hist.append(HS)
  if pf(g["fen"])[4]!=HS:
    lf(g["fen"]);hist=[HS]
  return hist
ENV=""
def po(path,body):
  req=urllib.request.Request(ENV+path,data=json.dumps(body).encode(),headers={"content-type":"application/json"})
  try:
    with urllib.request.urlopen(req) as res:return json.load(res)
  except urllib.error.HTTPError as e:sys.exit(f"{path}: HTTP {e.code} {e.read().decode(errors='replace')}")
def mn():
  global ENV
  ENV=os.environ.get("MAKEFUN_ENV_URL") or sys.exit("MAKEFUN_ENV_URL not set")
  while True:
    g=po("/game",{})
    if g["status"]=="done":break
    hist=sy(g)
    while g["status"]=="your_move":
      moved=False
      for m in ch(g["legal_moves"],hist):
        r=po("/move",{"game":g["game"],"move":uc(m)})
        if r.get("status") in ("your_move","over"):
          g=r;hist=sy(g);moved=True;break
      if not moved:
        po("/resign",{"game":g["game"]});break
if __name__=="__main__":mn()
