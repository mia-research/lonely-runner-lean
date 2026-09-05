"""
Build Java-PRNG and Python-PRNG key datasets, interrogate n and k from (X,Y) two
ways, and cross-check the two generators.

Datasets: keys d = 2^(b-1) | (b-1 random bits) with bits from Java's Random (LCG)
or Python's random (Mersenne Twister). Then n,k = best_nk(u), (X,Y) = d*G.

Interrogations (PURE (X,Y) features only -- no n,k in features):
  pooled : does (X,Y) leak n%6/n%8/k%6/k%8?  (best-feature MI, G-test, Bonferroni)
  per-k  : within fixed k (differing k, varying n), does (X,Y) leak n? count p<0.05
  per-n  : within fixed n, does (X,Y) leak k? count p<0.05
Cross-check: Java vs Python side by side. Same result => map-level / generation-
independent. Divergence => a generation-dependent effect to chase.
Results reported with parameters; no verdicts.
"""
import math, random
from math import gcd
import numpy as np

P  = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
Gx = 0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798
Gy = 0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8
def dbl(X1,Y1,Z1):
    if Y1==0: return (0,0,0)
    S=(4*X1*Y1*Y1)%P; M=(3*X1*X1)%P; X3=(M*M-2*S)%P
    Y3=(M*(S-X3)-8*(Y1*Y1%P)**2)%P; Z3=(2*Y1*Z1)%P; return (X3,Y3,Z3)
def addp(X1,Y1,Z1,X2,Y2,Z2):
    if Z1==0: return (X2,Y2,Z2)
    if Z2==0: return (X1,Y1,Z1)
    Z1Z1=Z1*Z1%P; Z2Z2=Z2*Z2%P; U1=X1*Z2Z2%P; U2=X2*Z1Z1%P
    S1=Y1*Z2*Z2Z2%P; S2=Y2*Z1*Z1Z1%P
    if U1==U2: return dbl(X1,Y1,Z1) if S1==S2 else (0,0,0)
    H=(U2-U1)%P; I=((2*H)%P)**2%P; J=H*I%P; r=(2*(S2-S1))%P; V=U1*I%P
    X3=(r*r-J-2*V)%P; Y3=(r*(V-X3)-2*S1*J)%P; Z3=((Z1+Z2)**2-Z1Z1-Z2Z2)%P*H%P
    return (X3,Y3,Z3)
def mulxy(d):
    RX,RY,RZ=0,0,0; AX,AY,AZ=Gx,Gy,1
    while d:
        if d&1: RX,RY,RZ=addp(RX,RY,RZ,AX,AY,AZ)
        AX,AY,AZ=dbl(AX,AY,AZ); d>>=1
    z=pow(RZ,P-2,P); z2=z*z%P; return (RX*z2%P, RY*z2*z%P)
def best_nk(u,nmax=256):
    best=(9e9,1,0)
    for n in range(1,nmax+1):
        k=round(u*n); e=abs(u-k/n)
        if e<best[0]: best=(e,n,k)
    return best[1],best[2]

class JavaRandom:
    def __init__(self,seed): self.s=(seed^0x5DEECE66D)&((1<<48)-1)
    def next(self,bits):
        self.s=(self.s*0x5DEECE66D+0xB)&((1<<48)-1)
        return self.s>>(48-bits)
    def randbits(self,nb):
        v=0;g=0
        while g<nb:
            t=min(32,nb-g); v=(v<<t)|self.next(t); g+=t
        return v

def gen(kind, NK, seed):
    if kind=="java": jr=JavaRandom(seed); rb=lambda nb: jr.randbits(nb); pick=JavaRandom(seed^0xABC)
    else: pr=random.Random(seed); rb=lambda nb: pr.getrandbits(nb)
    br=random.Random(seed^0x999)   # bit-length chooser (shared, neutral)
    ns=[];ks=[];Xs=[];Ys=[]
    for _ in range(NK):
        b=br.randint(40,120); lo=2**(b-1)
        d=lo | rb(b-1)
        u=(d-lo)/lo; n,k=best_nk(u)
        if n<5 or not(0<k<n): continue
        x,y=mulxy(d); ns.append(n);ks.append(k);Xs.append(x);Ys.append(y)
    return np.array(ns),np.array(ks),Xs,Ys

def pure_feats(Xs,Ys):
    f={}
    for m in (2,3,5,7,11,13,17,19,23,29,31):
        f[f"X%{m}"]=np.array([int(x)%m for x in Xs]); f[f"Y%{m}"]=np.array([int(y)%m for y in Ys])
        f[f"XY%{m}"]=np.array([(int(x)*int(y))%m for x,y in zip(Xs,Ys)])
    for p in (3,5,7,11,13):
        f[f"Xleg{p}"]=np.array([pow(int(x)%p,(p-1)//2,p) for x in Xs])
    for b in range(0,256,32): f[f"Xb{b}"]=np.array([(int(x)>>b)&1 for x in Xs])
    return f
def mi_bits(f,t):
    A=int(f.max())+1;B=int(t.max())+1;j=np.zeros((A,B))
    for a,b in zip(f,t): j[a,b]+=1
    j/=j.sum();pa=j.sum(1,keepdims=True);pb=j.sum(0,keepdims=True)
    with np.errstate(divide='ignore',invalid='ignore'):
        term=j*np.log2((j+1e-30)/(pa*pb+1e-30))
    return float(term[j>0].sum()),A,B
def chi2_sf(x,df):
    if x<=0 or df<=0: return 1.0
    t=(x/df)**(1/3);mu=1-2/(9*df);s=math.sqrt(2/(9*df));z=(t-mu)/s
    return 0.5*math.erfc(z/math.sqrt(2))
def spear(a,b):
    ra=np.argsort(np.argsort(a)).astype(float); rb=np.argsort(np.argsort(b)).astype(float)
    ra-=ra.mean(); rb-=rb.mean(); d=math.sqrt((ra@ra)*(rb@rb))
    return (ra@rb)/d if d>0 else 0.0

def analyze(name,ns,ks,Xs,Ys,rng):
    N=len(ns); F=pure_feats(Xs,Ys)
    print(f"\n=== {name}  ({N} keys) ===")
    print("  pooled (X,Y)->target, best-feature MI, Bonferroni:")
    for tn,t in (("n%6",ns%6),("n%8",ns%8),("k%6",ks%6),("k%8",ks%8)):
        best=(9e9,None,0)
        for fn,col in F.items():
            mi,A,B=mi_bits(col,t); g=2*N*math.log(2)*mi; p=chi2_sf(g,(A-1)*(B-1))
            if p<best[0]: best=(p,fn,mi)
        print(f"    {tn}: bestMI={best[2]:.5f}  Bonf-p={min(1,best[0]*len(F)):.3f}  ({best[1]})")
    # per-k and per-n excess counts
    def strat(groupby, target):
        bucket={}
        for i in range(N): bucket.setdefault(int(groupby[i]),[]).append(i)
        G=0;c05=0
        for g,idx in bucket.items():
            if len(idx)<40: continue
            G+=1; tt=target[idx]
            cols={fn:F[fn][idx] for fn in F}
            o=max(abs(spear(col,tt)) for col in cols.values()); c=1
            for _ in range(120):
                ts=rng.permutation(tt)
                if max(abs(spear(col,ts)) for col in cols.values())>=o: c+=1
            if c/121<0.05: c05+=1
        return G,c05
    Gk,ck=strat(ks,ns)   # per-k: fix k, does (X,Y) predict n
    Gn,cn=strat(ns,ks)   # per-n: fix n, does (X,Y) predict k
    print(f"  per-k (fix k, predict n): {Gk} groups, #p<0.05={ck} (exp {0.05*Gk:.0f})")
    print(f"  per-n (fix n, predict k): {Gn} groups, #p<0.05={cn} (exp {0.05*Gn:.0f})")

rng=np.random.default_rng(0)
for kind,label in (("java","JAVA PRNG (LCG)"),("py","PYTHON PRNG (Mersenne Twister)")):
    ns,ks,Xs,Ys=gen(kind, 16000, 12345)
    analyze(label,ns,ks,Xs,Ys,rng)
print("\nCross-check: matching Java vs Python => generation-independent (map-level).")
print("Any pooled Bonf-p<0.01 or per-group excess that appears in ONE generator only")
print("=> generation-dependent, worth crossing against the real keys.")
