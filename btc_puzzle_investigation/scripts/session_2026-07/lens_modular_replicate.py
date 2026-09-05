"""
DECISIVE test of F1 (Spearman(XY mod n^2/n^2, k/n) spikes at the true n).
82 points + p=0.02 is not enough to believe -- that is how GECT fooled itself.

High-power replication on synthetic keys where we control d,n,k,X,Y exactly:
generate NS uniform keys, compute best-approx (n,k), real (X,Y)=d*G, and measure
the SAME Spearman with the SAME n+-delta localization.

  real mathematical relation -> large |rho|, tiny p on synthetic, spike at delta=0.
  82-key look-elsewhere fluke -> synthetic rho ~ 0 at every delta.
"""
import random
import numpy as np

P  = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
Gx = 0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798
Gy = 0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8
def dbl(X1,Y1,Z1):
    if Y1==0: return (0,0,0)
    S=(4*X1*Y1*Y1)%P; M=(3*X1*X1)%P; X3=(M*M-2*S)%P
    Y3=(M*(S-X3)-8*(Y1*Y1%P)**2)%P; Z3=(2*Y1*Z1)%P; return (X3,Y3,Z3)
def add(X1,Y1,Z1,X2,Y2,Z2):
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
        if d&1: RX,RY,RZ=add(RX,RY,RZ,AX,AY,AZ)
        AX,AY,AZ=dbl(AX,AY,AZ); d>>=1
    z=pow(RZ,P-2,P); z2=z*z%P; return (RX*z2%P, RY*z2*z%P)
def best_nk(u,nmax=256):
    best=(9e9,1,0)
    for n in range(1,nmax+1):
        k=round(u*n); e=abs(u-k/n)
        if e<best[0]: best=(e,n,k)
    return best[1],best[2]
def spearman(a,b):
    ra=np.argsort(np.argsort(a)).astype(float); rb=np.argsort(np.argsort(b)).astype(float)
    ra-=ra.mean(); rb-=rb.mean(); return (ra@rb)/(np.sqrt((ra@ra)*(rb@rb))+1e-30)

NS=3000; N=48; lo=2**(N-1)
_r=random.Random(2026)
print(f"generating {NS} synthetic {N}-bit keys (d,n,k,X,Y all known/exact)...")
Xs=[];Ys=[];ns=[];ks=[]
for _ in range(NS):
    d=lo+_r.randrange(lo); u=(d-lo)/lo; n,k=best_nk(u)
    if n<5 or k==0 or k>=n: continue
    x,y=mulxy(d); Xs.append(x);Ys.append(y);ns.append(n);ks.append(k)
Xs=np.array(Xs,object);Ys=np.array(Ys,object);ns=np.array(ns);ks=np.array(ks)
Msyn=len(ns); print(f"usable: {Msyn}")
s=ks/ns

def rho_at(delta):
    npr=ns+delta
    r=np.array([((int(Xs[i])*int(Ys[i]))%(int(npr[i])**2))/(int(npr[i])**2) for i in range(Msyn)])
    o=spearman(r,s)
    # perm p (few iters, large N so cheap-ish)
    c=1; rng=np.random.default_rng(delta+7)
    for _ in range(300):
        if abs(spearman(r,rng.permutation(s)))>=abs(o): c+=1
    return o, c/301

print(f"\nSpearman(XY mod (n+delta)^2/(.)^2 , k/n) on {Msyn} synthetic keys:")
print(f"    {'delta':>6} | {'rho':>7} | perm-p")
for dd in (-2,-1,0,1,2):
    o,p=rho_at(dd)
    print(f"    {dd:>+6} | {o:+7.4f} | {p:.3f}{'   <-- true n' if dd==0 else ''}")
print("\nlarge rho at delta=0 (only) => REAL public->k relation given n, replicated at")
print("high power. rho~0 everywhere => the 82-key F1 was look-elsewhere; drop it.")
