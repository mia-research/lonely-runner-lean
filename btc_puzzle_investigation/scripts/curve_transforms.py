import csv, random, math
from math import gcd
from collections import Counter
from ecdsa.ecdsa import generator_secp256k1
from ecdsa.ellipticcurve import Point
G=generator_secp256k1; CURVE=G.curve()
p=0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
BETA=0x7ae96a2b657c07106e64479eac3434e99cf0497512f58995c1396c28719501ee
Gpt=Point(CURVE,G.x(),G.y())
rows=[]
with open("/Users/trentpalelei/Desktop/Math Ex/btc_puzzle_investigation/solved_puzzles_xy.csv") as f:
    for r in csv.DictReader(f):
        rows.append((int(r["bits"]),int(r["private_key"],16),int(r["X"],16),int(r["Y"],16)))
rows=[x for x in rows if x[0]>=25]
NS=(39,65,80,135)
def n_coord(bits,key):
    R=2**(bits-1); u=(key-R)/R; best=None
    for n in NS:
        ks=[k for k in range(1,n) if gcd(k,n)==1]; k=min(ks,key=lambda k:abs(u-k/n)); base=R+(R*k)//n
        if best is None or abs(key-base)<abs(key-best[1]): best=(n,base)
    return NS.index(best[0])
def topbit(bits,key): R=2**(bits-1); return int((key-R)/R>=0.5)
SMALL=(2,3,5,7,11,13,17,19,23,29,31,37,41,43)
def curve_feats(X,Y):
    P=Point(CURVE,X,Y)
    derived=[]
    derived.append(("endoX",(BETA*X)%p))                 # GLV endomorphism x
    try: derived.append(("invYX",(Y*pow(X,-1,p))%p))
    except: derived.append(("invYX",0))
    derived.append(("X2",(X*X)%p)); derived.append(("XYp",(X*Y)%p))
    for name,Q in (("2P",2*P),("3P",3*P),("PpG",P+Gpt),("PmG",P+(-Gpt))):
        derived.append((name+"x",Q.x())); derived.append((name+"y",Q.y()))
    f=[]
    for _,z in derived:
        for m in SMALL: f.append(z%m)
        f.append((z>>100)&7)
    return tuple(f)
def loo_ig(labels,F,fi,nc):
    N=len(labels); base=0.0; fll=0.0
    for i in range(N):
        tr=[j for j in range(N) if j!=i]
        cnt=Counter(labels[j] for j in tr); base+=-math.log((cnt.get(labels[i],0)+1)/(N-1+nc))
        binj=[j for j in tr if F[j][fi]==F[i][fi]]; cf=Counter(labels[j] for j in binj)
        fll+=-math.log((cf.get(labels[i],0)+1)/(len(binj)+nc))
    return (base-fll)/N
def detector(labels,F,nc): return max(loo_ig(labels,F,fi,nc) for fi in range(len(F[0])))
realF=[curve_feats(X,Y) for b,k,X,Y in rows]
print(f"{len(rows)} keys, {len(realF[0])} curve-native features (endomorphism + 2P/3P/P±G + field transforms)\n")
random.seed(1)
for tname,fn in (("n",n_coord),("pos_topbit",topbit)):
    labels=[fn(b,k) for b,k,X,Y in rows]; nc=len(set(labels))
    posF=[realF[i]+(labels[i] if random.random()<0.4 else random.randrange(nc),) for i in range(len(rows))]
    pos=detector(labels,posF,nc); real=detector(labels,realF,nc)
    ck=[]
    for s in range(40):
        pyr=random.Random(700+s); lab=[];FF=[]
        for b,_,_,_ in rows:
            d=2**(b-1)+pyr.randrange(2**(b-1)); P=d*G
            lab.append(fn(b,d)); FF.append(curve_feats(P.x(),P.y()))
        ck.append(detector(lab,FF,nc))
    ck.sort(); above=sum(1 for x in ck if x>=real)
    print(f"[{tname}] POS-ctrl(40%)={pos:+.4f}  REAL={real:+.4f}  ctrl(mean={sum(ck)/len(ck):+.4f},95th={ck[int(.95*len(ck))]:+.4f})  real%ile={100*(1-above/len(ck)):.0f}")
