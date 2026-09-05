"""
SMART DATA: enumerate the FULL coprime (n,k) grid (n=5..256, k=1..n-1, gcd=1),
build d = base(n,k) at a fixed bit-length, compute real (X,Y). ~20k systematic
points (Sum phi(n) ~ 19,900), not random sampling.

New question none of the pooled tests could answer: does (X,Y) leak k WITHIN a
fixed n, and do different n behave differently? For each n we now have phi(n)
keys, one per coprime k -- a clean k<->key bijection. n is KNOWN per group, so
n-reduced features (X mod n, XY mod n^2) are legitimate here (the stage-2 "given
n, does (X,Y) leak k" question), done systematically per n.

Detector per n: max over features of |Spearman(feature, k)|. Null: shuffle k
WITHIN that n. Report the per-n p distribution (excess of small p across n = a
real per-n leak somewhere) + individual flagged n. Positive control included.
Results are stated with their parameters; no verdicts.
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
def spear(a,b):
    ra=np.argsort(np.argsort(a)).astype(float); rb=np.argsort(np.argsort(b)).astype(float)
    ra-=ra.mean(); rb-=rb.mean(); d=math.sqrt((ra@ra)*(rb@rb))
    return (ra@rb)/d if d>0 else 0.0

N=64; lo=2**(N-1)
grid={}   # n -> list of (k, X, Y)
print("enumerating coprime (n,k) grid, N=64, computing (X,Y)...")
tot=0
for n in range(5,257):
    ks=[k for k in range(1,n) if gcd(k,n)==1]
    if len(ks)<30: continue                      # need enough k for a stable per-n stat
    rowk=[];rowX=[];rowY=[]
    for k in ks:
        d=lo+(lo*k)//n; x,y=mulxy(d)
        rowk.append(k);rowX.append(x);rowY.append(y)
    grid[n]=(np.array(rowk),rowX,rowY); tot+=len(ks)
print(f"grid: {len(grid)} n-groups (phi(n)>=30), {tot} keys total")

def feats_for(n,Xs,Ys):
    f={}
    f["Xmodn"]=np.array([int(x)%n for x in Xs]); f["Ymodn"]=np.array([int(y)%n for y in Ys])
    f["XYmodn2"]=np.array([(int(x)*int(y))%(n*n) for x,y in zip(Xs,Ys)])
    f["XplusYmodn"]=np.array([(int(x)+int(y))%n for x,y in zip(Xs,Ys)])
    for m in (3,5,7,256):
        f[f"X%{m}"]=np.array([int(x)%m for x in Xs])
    for p in (3,5,7):
        f[f"Xleg{p}"]=np.array([pow(int(x)%p,(p-1)//2,p) for x in Xs])
    return f

def Sn(n, kk, F):
    return max(abs(spear(col,kk)) for col in F.values())

rng=np.random.default_rng(0)
obs={}; F_by_n={}
for n,(kk,Xs,Ys) in grid.items():
    F=feats_for(n,Xs,Ys); F_by_n[n]=(kk,F); obs[n]=Sn(n,kk,F)

# per-n permutation p (shuffle k within n)
pvals={}
for n,(kk,F) in F_by_n.items():
    o=obs[n]; c=1
    for _ in range(300):
        ks=rng.permutation(kk)
        if max(abs(spear(col,ks)) for col in F.values())>=o: c+=1
    pvals[n]=c/301
pv=np.array(list(pvals.values()))
print(f"\nper-n test: does (X,Y) leak k within fixed n? (max-feature |Spearman|, within-n shuffle null)")
print(f"   n-groups tested: {len(pv)}")
print(f"   # with p<0.05: {(pv<0.05).sum()}  (expected under no-leak: {0.05*len(pv):.1f})")
print(f"   # with p<0.01: {(pv<0.01).sum()}  (expected: {0.01*len(pv):.1f})")
lowest=sorted(pvals.items(),key=lambda x:x[1])[:6]
print(f"   strongest n (n, p, S_n): " + ", ".join(f"({n},p={p:.3f},S={obs[n]:.2f})" for n,p in lowest))
# Bonferroni on the strongest
bn,bp=lowest[0]
print(f"   Bonferroni on strongest: p={bp:.3f} x {len(pv)} = {min(1,bp*len(pv)):.2f}")

# positive control: plant a k-correlated feature in 3 n-groups
print(f"\n   [CONTROL] inject feature = k-rank+noise into 3 groups:")
ctrl_ns=list(grid.keys())[:3]
for n in ctrl_ns:
    kk,F=F_by_n[n]
    planted=kk + rng.normal(0,kk.std()*0.5,len(kk))   # 0.5-noise copy of k
    Fp=dict(F); Fp["PLANT"]=planted
    o=max(abs(spear(col,kk)) for col in Fp.values()); c=1
    for _ in range(300):
        ks=rng.permutation(kk)
        if max(abs(spear(col,ks)) for col in Fp.values())>=o: c+=1
    print(f"      n={n}: with planted feature p={c/301:.3f} (fires if <0.05)")
print("\nRead: #p<0.05 near expected + Bonferroni high => no per-n (X,Y)->k structure")
print("observed with these features/this N; excess of small p or a Bonferroni hit => a")
print("per-n leak to chase. Control confirms the per-n detector has power.")
