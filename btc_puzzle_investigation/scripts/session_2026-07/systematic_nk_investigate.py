"""
Interrogate the per-n EXCESS from systematic_nk_grid.py (28 groups p<0.05 vs ~10).
Two decisive checks:
  A  which FEATURES drive the low-p groups in the D=0 grid?
  B  does the excess survive with RANDOM D (realistic keys, D!=0)? The grid used
     d=base(n,k) exactly (D=0), where d is monotonic in k -- a structured slice.
     Real keys carry random low bits. If the excess is a D=0 artifact it vanishes
     with random D; if it is a real per-n leak it persists.
Report counts with parameters; no verdicts.
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
def spear(a,b):
    ra=np.argsort(np.argsort(a)).astype(float); rb=np.argsort(np.argsort(b)).astype(float)
    ra-=ra.mean(); rb-=rb.mean(); d=math.sqrt((ra@ra)*(rb@rb))
    return (ra@rb)/d if d>0 else 0.0
def feats(n,Xs,Ys):
    f={}
    f["Xmodn"]=np.array([int(x)%n for x in Xs]); f["Ymodn"]=np.array([int(y)%n for y in Ys])
    f["XYmodn2"]=np.array([(int(x)*int(y))%(n*n) for x,y in zip(Xs,Ys)])
    f["XplusYmodn"]=np.array([(int(x)+int(y))%n for x,y in zip(Xs,Ys)])
    for m in (3,5,7,256): f[f"X%{m}"]=np.array([int(x)%m for x in Xs])
    for p in (3,5,7): f[f"Xleg{p}"]=np.array([pow(int(x)%p,(p-1)//2,p) for x in Xs])
    return f
def per_n_p(n,kk,Xs,Ys,rng,reps=300):
    F=feats(n,Xs,Ys)
    winner=max(F,key=lambda nm:abs(spear(F[nm],kk)))
    o=abs(spear(F[winner],kk)); c=1
    for _ in range(reps):
        ks=rng.permutation(kk)
        if max(abs(spear(col,ks)) for col in F.values())>=o: c+=1
    return c/(reps+1), winner

N=64; lo=2**(N-1); rng=np.random.default_rng(1)

# ---- A: D=0 grid, winning features in low-p groups ----
print("A  D=0 grid: per-n p and the winning feature in low-p groups")
gridp={}; winners={}
from collections import Counter
wc=Counter()
for n in range(5,257):
    ks=[k for k in range(1,n) if gcd(k,n)==1]
    if len(ks)<30: continue
    Xs=[];Ys=[]
    for k in ks:
        d=lo+(lo*k)//n; x,y=mulxy(d); Xs.append(x);Ys.append(y)
    p,w=per_n_p(n,np.array(ks),Xs,Ys,rng)
    gridp[n]=p
    if p<0.05: wc[w]+=1
pv=np.array(list(gridp.values()))
print(f"   groups={len(pv)}  #p<0.05={int((pv<0.05).sum())} (exp {0.05*len(pv):.0f})  "
      f"#p<0.01={int((pv<0.01).sum())} (exp {0.01*len(pv):.0f})")
print(f"   winning feature among low-p groups: {dict(wc)}")

# ---- B: RANDOM D (realistic keys), grouped by actual n ----
print("\nB  random-D realistic keys, grouped by their actual n, same per-n test")
_r=random.Random(9)
bucket={}
NKEYS=40000
for _ in range(NKEYS):
    b=_r.randint(40,120); l=2**(b-1)
    d=l+_r.randrange(l); u=(d-l)/l; n,k=best_nk(u)
    if n<5 or not(0<k<n): continue
    x,y=mulxy(d); bucket.setdefault(n,[]).append((k,x,y))
cnt05=0; cnt01=0; G=0
for n,items in bucket.items():
    if len(items)<40: continue
    G+=1
    kk=np.array([it[0] for it in items]); Xs=[it[1] for it in items]; Ys=[it[2] for it in items]
    p,_=per_n_p(n,kk,Xs,Ys,rng,reps=200)
    cnt05+= p<0.05; cnt01+= p<0.01
print(f"   groups={G}  #p<0.05={cnt05} (exp {0.05*G:.0f})  #p<0.01={cnt01} (exp {0.01*G:.0f})")
print("\nRead: if B's #p<0.05 ~ expected while A's is inflated -> the grid excess is a")
print("D=0 (base-key) structural artifact, not a per-n leak in realistic keys.")
print("If B is also inflated -> a real per-n (X,Y)->k effect to chase.")
