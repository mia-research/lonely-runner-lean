"""Adversarial 2 only, overflow fixed (native bigint RNG): control-keypair null.
Same position labels, FRESH random (X,Y). If the REAL public key carried
position info, the real detector score would beat random points with identical
labels. Reuses the public feature set from hunt_real."""
import csv, math, random
import numpy as np
from collections import Counter

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

rows=[]
with open('/Users/trentpalelei/Desktop/Math Ex/btc_puzzle_investigation/puzzles_verified.csv') as f:
    for r in csv.DictReader(f):
        rows.append((int(r['puzzle']),int(r['bits']),int(r['private_key'],16),int(r['X'],16),int(r['Y'],16)))
rows.sort()
def pub_features(N,X,Y):
    f={'N':N,'N%4':N%4}
    for m in (2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71):
        f[f'X%{m}']=X%m; f[f'Y%{m}']=Y%m; f[f'XY%{m}']=(X*Y)%m; f[f'X+Y%{m}']=(X+Y)%m
    for b in range(0,256,16): f[f'Xb{b}']=(X>>b)&3
    for p in (3,5,7,11,13,17,19): f[f'Xleg{p}']=pow(X%p,(p-1)//2,p); f[f'Yleg{p}']=pow(Y%p,(p-1)//2,p)
    f['Ypar']=Y&1; f['Xhw']=bin(X).count('1'); f['Xtop']=X>>252
    return f
u=np.array([(k-2**(b-1))/2**(b-1) for _,b,k,_,_ in rows])
Q=np.floor(u*4).astype(int)
names=list(pub_features(*(1,Gx,Gy)).keys())
def loo_mi(lab,col):
    n=len(lab); tot=0.0; nc=len(set(lab))
    for i in range(n):
        tr=[j for j in range(n) if j!=i]; same=[j for j in tr if col[j]==col[i]]
        c_all=Counter(lab[j] for j in tr); c_bin=Counter(lab[j] for j in same)
        tot+=math.log((c_bin.get(lab[i],0)+1)/(len(same)+nc))-math.log((c_all.get(lab[i],0)+1)/(n-1+nc))
    return tot/n
def det(lab,F): return max(loo_mi(lab,F[:,j]) for j in range(F.shape[1]))

realF=np.array([[f[n] for n in names] for f in (pub_features(b,X,Y) for _,b,k,X,Y in rows)])
real=det(Q,realF)
rng=random.Random(7); ck=[]
for it in range(100):
    ff=[]
    for (_,b,k,_,_),q in zip(rows,Q):
        q=int(q); R=2**(b-1); lo=R+q*R//4; hi=R+(q+1)*R//4
        dp=rng.randrange(lo,max(hi,lo+1)); Xp,Yp=mulxy(dp); ff.append(pub_features(b,Xp,Yp))
    ck.append(det(Q,np.array([[f[n] for n in names] for f in ff])))
ck=np.array(ck)
print("=== ADVERSARIAL 2: control-keypair null (same labels, fresh random pubkeys) ===")
print(f"  REAL pubkey best-feature score = {real:+.4f}")
print(f"  RANDOM pubkeys (same labels):  mean={ck.mean():+.4f}  p95={np.quantile(ck,0.95):+.4f}  max={ck.max():+.4f}")
print(f"  real percentile vs control = {100*np.mean(ck<real):.0f}%")
print(f"  VERDICT: {'REAL pubkey beats random -> signal' if real>np.quantile(ck,0.95) else 'KILLED -- real pubkey no better than a random point with the same label'}")
