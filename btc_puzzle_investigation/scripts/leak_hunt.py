import csv, random, math
from math import gcd
from collections import Counter
from ecdsa.ecdsa import generator_secp256k1
G=generator_secp256k1
rows=[]
with open("/Users/trentpalelei/Desktop/Math Ex/btc_puzzle_investigation/solved_puzzles_xy.csv") as f:
    for r in csv.DictReader(f):
        rows.append((int(r["bits"]),int(r["private_key"],16),int(r["X"],16),int(r["Y"],16)))
rows=[x for x in rows if x[0]>=25]
NS=(39,65,80,135)
MODS=list(range(2,42))+[43,47,53,59,61,67,71,73,79,83,89,97,101,127,151,199,211]
def n_coord(bits,key):
    R=2**(bits-1); u=(key-R)/R; best=None
    for n in NS:
        ks=[k for k in range(1,n) if gcd(k,n)==1]
        k=min(ks,key=lambda k:abs(u-k/n)); base=R+(R*k)//n
        if best is None or abs(key-base)<abs(key-best[1]): best=(n,base)
    return best[0]
def posq(bits,key):  # top-2-bit position bucket (which quarter of the interval)
    R=2**(bits-1); return int((key-R)/R*4)
def feats(X,Y):
    f=[]
    for m in MODS:
        f.append(X%m); f.append(Y%m); f.append((X+Y)%m); f.append((X*Y)%m); f.append((X-Y)%m)
    for b in range(0,256,16): f.append((X>>b)&7); f.append((Y>>b)&7)
    for p in (3,5,7,11,13): f.append(pow(X%p,(p-1)//2,p)); f.append(pow(Y%p,(p-1)//2,p))
    return tuple(f)
def loo_ig(labels,F,fidx,nc):
    N=len(labels); base=0.0; fll=0.0
    for i in range(N):
        tr=[j for j in range(N) if j!=i]
        cnt=Counter(labels[j] for j in tr)
        base+=-math.log((cnt.get(labels[i],0)+1)/(N-1+nc))
        binj=[j for j in tr if F[j][fidx]==F[i][fidx]]
        cf=Counter(labels[j] for j in binj)
        fll+=-math.log((cf.get(labels[i],0)+1)/(len(binj)+nc))
    return (base-fll)/N
def detector(labels,F,nc): return max(loo_ig(labels,F,fi,nc) for fi in range(len(F[0])))

realF=[feats(X,Y) for b,k,X,Y in rows]
out={}
for tname,labfn in (("n",lambda b,k:n_coord(b,k)),("position-quarter",lambda b,k:posq(b,k))):
    labels=[labfn(b,k) for b,k,X,Y in rows]; nc=len(set(labels))
    random.seed(1)
    posF=[realF[i]+(labels[i] if random.random()<0.4 else random.randrange(nc),) for i in range(len(rows))]
    pos=detector(labels,posF,nc)
    real=detector(labels,realF,nc)
    random.seed(9); ck=[]
    for _ in range(30):
        lab=[];FF=[]
        for b,_,_,_ in rows:
            d=2**(b-1)+random.randrange(2**(b-1)); P=d*G
            lab.append(labfn(b,d)); FF.append(feats(P.x(),P.y()))
        ck.append(detector(lab,FF,nc))
    ck.sort(); above=sum(1 for x in ck if x>=real)
    out[tname]=dict(pos=pos,real=real,ck_mean=sum(ck)/len(ck),ck_max=max(ck),pct=100*(1-above/len(ck)),nfeat=len(realF[0]))
import json; json.dump(out,open("/tmp/leak_hunt.json","w"))
for t,d in out.items():
    print(f"[{t}] features={d['nfeat']}  POS-control={d['pos']:+.4f}  REAL={d['real']:+.4f}  ctrl(mean={d['ck_mean']:+.4f},max={d['ck_max']:+.4f})  real%ile={d['pct']:.0f}")
