import numpy as np, pandas as pd, random
from sklearn.metrics import mutual_info_score
from sympy import n_order
random.seed(0)
P=0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
def add(A,B):
    if A is None:return B
    if B is None:return A
    x1,y1=A;x2,y2=B
    if x1==x2 and (y1+y2)%P==0:return None
    l=((3*x1*x1)*pow(2*y1,-1,P) if A==B else (y2-y1)*pow(x2-x1,-1,P))%P
    x3=(l*l-x1-x2)%P;return (x3,(l*(x1-x3)-y1)%P)
df=pd.read_csv("constructed_keys_1to160_100k.csv")
df["Xi"]=df.X.apply(lambda s:int(s,16)); df["Yi"]=df.Y.apply(lambda s:int(s,16))
s=df.sample(20000,random_state=0).reset_index(drop=True)
X=s.Xi.values; Y=s.Yi.values; n=s.n.values
rng=np.random.default_rng(0)
def mi_z(x,y,reps=25):
    x=np.asarray(x);y=np.asarray(y); r=mutual_info_score(x,y)
    nu=np.array([mutual_info_score(x,rng.permutation(y)) for _ in range(reps)])
    return r-nu.mean(),(r-nu.mean())/(nu.std()+1e-12)

print("=== division-polynomial & multiple-point residues vs n [public], proper z ===")
# psi2^2=4(x^3+7); psi3=3x^4+84x ; x(2P),x(3P)
q=7
feats={}
feats["psi2^2 mod7"]=[ (4*(pow(int(v),3,P)+7))%q for v in X]
feats["psi3 mod7"]=[ (3*pow(int(v),4,P)+84*int(v))%q for v in X]
x2=[]; x3=[]
for xi,yi in zip(X,Y):
    P2=add((int(xi),int(yi)),(int(xi),int(yi)))
    P3=add(P2,(int(xi),int(yi))) if P2 else None
    x2.append(P2[0]%q if P2 else 0); x3.append(P3[0]%q if P3 else 0)
feats["x(2P) mod7"]=x2; feats["x(3P) mod7"]=x3
feats["x(2P) mod25"]=[ (add((int(xi),int(yi)),(int(xi),int(yi)))[0])%25 for xi,yi in zip(X,Y)]
for k,v in sorted(feats.items(), key=lambda kv:-mi_z(kv[1],n)[1]):
    adv,z=mi_z(v,n); print(f"  {k:16s} adjMI={adv:+.5f} z={z:+.2f}")

print("\n=== doubling-SLOPE trace autocorrelation at lag ord_n(2) [known d, subsample] ===")
Gx=0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798
Gy=0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8
def slopes(d):
    x,y=Gx,Gy; out=[]
    for b in bin(d)[2:]:
        l=(3*x*x)*pow(2*y,-1,P)%P; out.append(l&1)  # parity of doubling slope
        x3=(l*l-2*x)%P; y=(l*(x-x3)-y)%P; x=x3
        if b=='1':
            if x==Gx: continue
            l2=(y-Gy)*pow(x-Gx,-1,P)%P; x3=(l2*l2-x-Gx)%P; y=(l2*(x-x3)-y)%P; x=x3
    return np.array(out)
sub=df[(df.bits.between(40,90))&(df.n%2==1)&(df.n>2)].sample(300,random_state=0)
diffs=[]
for _,r in sub.iterrows():
    nn=int(r.n)
    try:L=int(n_order(2,nn))
    except Exception:continue
    sl=slopes(int(r.d))
    if L<2 or L>=len(sl)-4:continue
    a=sl[:-L]-0.5; b=sl[L:]-0.5; acL=float(np.mean(a*b))
    rl=[float(np.mean((sl[:-g]-0.5)*(sl[g:]-0.5))) for g in random.sample(range(2,len(sl)-4),min(6,len(sl)-6))]
    diffs.append(acL-np.mean(rl))
diffs=np.array(diffs)
print(f"  keys={len(diffs)} mean[slopeAC(ord_n2)-random]={diffs.mean():+.5f} t={diffs.mean()/(diffs.std()/np.sqrt(len(diffs))+1e-12):+.2f}")
print("\nDONE")
