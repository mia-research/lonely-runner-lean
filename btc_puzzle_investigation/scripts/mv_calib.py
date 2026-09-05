import csv, random, math
import numpy as np
from math import gcd
from ecdsa.ecdsa import generator_secp256k1
G=generator_secp256k1
rows=[]
with open("/Users/trentpalelei/Desktop/Math Ex/btc_puzzle_investigation/solved_puzzles_xy.csv") as f:
    for r in csv.DictReader(f):
        rows.append((int(r["bits"]),int(r["private_key"],16),int(r["X"],16),int(r["Y"],16)))
rows=[x for x in rows if x[0]>=25]
MODS=list(range(2,42))+[43,47,53,59,61,67,71,73,79,83,89,97,101,127,151,199,211]
def feats(X,Y):
    f=[]
    for m in MODS: f+=[X%m,Y%m,(X+Y)%m,(X*Y)%m,(X-Y)%m]
    for b in range(0,256,16): f+=[(X>>b)&255,(Y>>b)&255]
    return f
NS=(39,65,80,135)
def n_coord(bits,key):
    R=2**(bits-1); u=(key-R)/R; best=None
    for n in NS:
        ks=[k for k in range(1,n) if gcd(k,n)==1]; k=min(ks,key=lambda k:abs(u-k/n)); base=R+(R*k)//n
        if best is None or abs(key-base)<abs(key-best[1]): best=(n,base)
    return NS.index(best[0])
def build(X,y,depth,nc,rs):
    n=len(y); cnt=np.bincount(y,minlength=nc); node={'p':(cnt+1)/(cnt.sum()+nc)}
    if depth>=4 or n<6 or len(np.unique(y))==1: return node
    fs=rs.choice(X.shape[1],size=min(20,X.shape[1]),replace=False); pg=1-((cnt/n)**2).sum(); best=None
    for f in fs:
        col=X[:,f]
        for t in np.unique(np.quantile(col,[.25,.5,.75]).astype(np.int64)):
            L=col<=t; nl=L.sum(); nr=n-nl
            if nl<3 or nr<3: continue
            gl=1-((np.bincount(y[L],minlength=nc)/nl)**2).sum(); gr=1-((np.bincount(y[~L],minlength=nc)/nr)**2).sum()
            g=pg-(nl*gl+nr*gr)/n
            if best is None or g>best[0]: best=(g,f,t,L)
    if best is None or best[0]<=1e-9: return node
    _,f,t,L=best; node.update(f=f,t=t,L=build(X[L],y[L],depth+1,nc,rs),R=build(X[~L],y[~L],depth+1,nc,rs)); return node
def pred1(node,x):
    while 'f' in node: node=node['L'] if x[node['f']]<=node['t'] else node['R']
    return node['p']
def rf_ll_gain(X,y,nc,seed,B=80):
    rs=np.random.default_rng(seed); n=len(y); pr=np.zeros((n,nc)); c=np.zeros(n)
    for _ in range(B):
        idx=rs.integers(0,n,n); oob=np.setdiff1d(np.arange(n),idx); tr=build(X[idx],y[idx],0,nc,rs)
        for i in oob: pr[i]+=pred1(tr,X[i]); c[i]+=1
    ok=c>0; P=pr[ok]/c[ok,None]; yy=y[ok]
    base_cnt=np.bincount(y,minlength=nc); pbase=(base_cnt+1)/(base_cnt.sum()+nc)
    ll_f=-np.log(np.clip(P[np.arange(ok.sum()),yy],1e-9,1)).mean()
    ll_b=-np.log(pbase[yy]).mean()
    return ll_b-ll_f
y=np.array([n_coord(b,k) for b,k,X,Y in rows]); nc=4
realFX=np.array([feats(X,Y) for b,k,X,Y in rows],dtype=np.int64)
rng=np.random.default_rng(0)
def marg(s):
    lk=rng.random(len(y))<s; return np.column_stack([realFX, np.where(lk,y,rng.integers(0,nc,len(y)))])
def inter(s):
    a=rng.integers(0,nc,len(y)); lk=rng.random(len(y))<s; b=np.where(lk,(y-a)%nc,rng.integers(0,nc,len(y)))
    return np.column_stack([realFX,a,b])
print("detection-floor calibration (target=n, metric=OOB log-loss gain in nats):")
print(f"  marginal-100%: {rf_ll_gain(marg(1.0),y,nc,1):+.4f}")
print(f"  marginal-40% : {rf_ll_gain(marg(0.4),y,nc,2):+.4f}")
print(f"  interact-100%: {rf_ll_gain(inter(1.0),y,nc,3):+.4f}")
print(f"  interact-40% : {rf_ll_gain(inter(0.4),y,nc,4):+.4f}")
real=rf_ll_gain(realFX,y,nc,5)
ck=[]
for s in range(25):
    pyr=random.Random(500+s); lab=[];FF=[]
    for b,_,_,_ in rows:
        d=2**(b-1)+pyr.randrange(2**(b-1)); P=d*G; lab.append(n_coord(b,d)); FF.append(feats(P.x(),P.y()))
    ck.append(rf_ll_gain(np.array(FF,dtype=np.int64),np.array(lab),nc,9))
ck.sort()
print(f"  REAL (X,Y)   : {real:+.4f}")
print(f"  control keypairs: mean={sum(ck)/len(ck):+.4f} 95th={ck[int(.95*len(ck))]:+.4f} max={max(ck):+.4f}")
