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
MODS=list(range(2,42))+[43,47,53,59,61,67,71,73,79,83,89,97,101,127,151,199,211]
def posq(bits,key):
    R=2**(bits-1); return int((key-R)/R*4)
def feats(X,Y):
    f=[]; names=[]
    for m in MODS:
        f+= [X%m,Y%m,(X+Y)%m,(X*Y)%m,(X-Y)%m]
        names+=[f"X%{m}",f"Y%{m}",f"(X+Y)%{m}",f"(X*Y)%{m}",f"(X-Y)%{m}"]
    for b in range(0,256,16):
        f+=[(X>>b)&7,(Y>>b)&7]; names+=[f"X>>{b}&7",f"Y>>{b}&7"]
    for p in (3,5,7,11,13):
        f+=[pow(X%p,(p-1)//2,p),pow(Y%p,(p-1)//2,p)]; names+=[f"leg(X,{p})",f"leg(Y,{p})"]
    return tuple(f),names
def loo_ig(labels,F,fidx,nc):
    N=len(labels); base=0.0; fll=0.0
    for i in range(N):
        tr=[j for j in range(N) if j!=i]
        cnt=Counter(labels[j] for j in tr); base+=-math.log((cnt.get(labels[i],0)+1)/(N-1+nc))
        binj=[j for j in tr if F[j][fidx]==F[i][fidx]]; cf=Counter(labels[j] for j in binj)
        fll+=-math.log((cf.get(labels[i],0)+1)/(len(binj)+nc))
    return (base-fll)/N
labels=[posq(b,k) for b,k,X,Y in rows]; nc=len(set(labels))
realF=[feats(X,Y)[0] for b,k,X,Y in rows]; _,NAMES=feats(rows[0][2],rows[0][3])
igs=[loo_ig(labels,realF,fi,nc) for fi in range(len(realF[0]))]
best_fi=max(range(len(igs)),key=lambda i:igs[i]); real=igs[best_fi]
random.seed(9); ck=[]
for _ in range(140):
    lab=[];FF=[]
    for b,_,_,_ in rows:
        d=2**(b-1)+random.randrange(2**(b-1)); P=d*G
        lab.append(posq(b,d)); FF.append(feats(P.x(),P.y())[0])
    ck.append(max(loo_ig(lab,FF,fi,nc) for fi in range(len(FF[0]))))
ck.sort(); above=sum(1 for x in ck if x>=real)
print(f"position-quarter, {len(realF[0])} features, {len(ck)} controls")
print(f"  REAL best info-gain = {real:+.4f}  via feature = '{NAMES[best_fi]}'")
print(f"  control max-over-features: mean={sum(ck)/len(ck):+.4f} 95th={ck[int(.95*len(ck))]:+.4f} 99th={ck[int(.99*len(ck))]:+.4f} max={ck[-1]:+.4f}")
print(f"  real percentile = {100*(1-above/len(ck)):.1f}  ({above}/{len(ck)} >= real)")
