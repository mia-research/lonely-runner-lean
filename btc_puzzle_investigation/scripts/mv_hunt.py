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
def u_of(bits,key): R=2**(bits-1); return (key-R)/R
NS=(39,65,80,135)
def n_coord(bits,key):
    R=2**(bits-1); u=(key-R)/R; best=None
    for n in NS:
        ks=[k for k in range(1,n) if gcd(k,n)==1]; k=min(ks,key=lambda k:abs(u-k/n)); base=R+(R*k)//n
        if best is None or abs(key-base)<abs(key-best[1]): best=(n,base)
    return NS.index(best[0])
TARGETS={
 "n(4)":        lambda b,k: n_coord(b,k),
 "pos_topbit(2)":lambda b,k: int(u_of(b,k)>=0.5),
 "pos_quarter(4)":lambda b,k: min(3,int(u_of(b,k)*4)),
 "d_mod2(2)":   lambda b,k: k%2,
 "d_mod3(3)":   lambda b,k: k%3,
}
rng=np.random.default_rng(0)
def build(X,y,depth,nc,rs):
    n=len(y); cnt=np.bincount(y,minlength=nc); node={'p':(cnt+1)/(cnt.sum()+nc)}
    if depth>=4 or n<6 or len(np.unique(y))==1: return node
    feats_sel=rs.choice(X.shape[1],size=min(16,X.shape[1]),replace=False)
    pg=1-((cnt/n)**2).sum(); best=None
    for f in feats_sel:
        col=X[:,f]; qs=np.unique(np.quantile(col,[.2,.4,.6,.8]).astype(np.int64))
        for t in qs:
            L=col<=t; nl=L.sum(); nr=n-nl
            if nl<3 or nr<3: continue
            gl=1-((np.bincount(y[L],minlength=nc)/nl)**2).sum()
            gr=1-((np.bincount(y[~L],minlength=nc)/nr)**2).sum()
            g=pg-(nl*gl+nr*gr)/n
            if best is None or g>best[0]: best=(g,f,t,L)
    if best is None or best[0]<=1e-9: return node
    _,f,t,L=best; node.update(f=f,t=t,L=build(X[L],y[L],depth+1,nc,rs),R=build(X[~L],y[~L],depth+1,nc,rs))
    return node
def pred1(node,x):
    while 'f' in node: node=node['L'] if x[node['f']]<=node['t'] else node['R']
    return node['p']
def rf_oob_acc(X,y,nc,seed,B=60):
    rs=np.random.default_rng(seed); n=len(y); proba=np.zeros((n,nc)); cnt=np.zeros(n)
    for _ in range(B):
        idx=rs.integers(0,n,n); oob=np.setdiff1d(np.arange(n),idx)
        tree=build(X[idx],y[idx],0,nc,rs)
        for i in oob: proba[i]+=pred1(tree,X[i]); cnt[i]+=1
    ok=cnt>0; pr=proba[ok]/cnt[ok,None]; pred=pr.argmax(1)
    return (pred==y[ok]).mean()

realFX=np.array([feats(X,Y) for b,k,X,Y in rows],dtype=np.int64)
print(f"{len(rows)} keys, {realFX.shape[1]} features, RF interaction detector\n")
print(f"{'target':16} {'base':>6} {'POS(interact)':>13} {'REAL':>7} {'ctrl mean':>9} {'ctrl 95th':>9} {'real %ile':>9}")
for tname,fn in TARGETS.items():
    y=np.array([fn(b,k) for b,k,X,Y in rows]); nc=int(y.max()+1)
    base=np.bincount(y).max()/len(y)
    # positive control: two interaction features encoding y 40% of the time
    a=rng.integers(0,7,len(y)); leak=(rng.random(len(y))<0.4)
    b2=np.where(leak,(y-a)%7,rng.integers(0,7,len(y)))
    posX=np.column_stack([realFX,a,b2])
    pos=rf_oob_acc(posX,y,nc,1)
    real=rf_oob_acc(realFX,y,nc,2)
    ck=[]
    for s in range(25):
        lab=[];FF=[]
        pyr=random.Random(1000+s)
        for b,_,_,_ in rows:
            d=2**(b-1)+pyr.randrange(2**(b-1)); P=d*G
            lab.append(fn(b,d)); FF.append(feats(P.x(),P.y()))
        ck.append(rf_oob_acc(np.array(FF,dtype=np.int64),np.array(lab),nc,7))
    ck.sort(); above=sum(1 for x in ck if x>=real)
    print(f"{tname:16} {base:6.3f} {pos:13.3f} {real:7.3f} {sum(ck)/len(ck):9.3f} {ck[int(.95*len(ck))]:9.3f} {100*(1-above/len(ck)):8.0f}")
