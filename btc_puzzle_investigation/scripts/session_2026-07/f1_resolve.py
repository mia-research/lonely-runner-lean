"""
Resolve F1 = Spearman(XY mod n^2 / n^2 , k/n) two ways at once.

PART A  MULTIPLE-TESTING-CLEAN matched null. Scan a family of modular pubkey
        reductions; statistic = MAX |rho| over the family. Null = same max over
        matched-random datasets (exact real bit-length multiset, real curve).
        Gives the honest p that accounts for having picked XY mod n^2 as best.

PART B  MECHANISM on the 72 real keys:
        B1 Pearson vs Spearman; jackknife drop-1 (is it a few influential keys?)
        B2 what does it track: k/n vs u(position) vs residual(u-k/n) vs raw k vs raw n
        B3 does the product matter: X mod n^2 alone, Y mod n^2 alone
        B4 why n^2: rho for mod n, n^2, n^3
"""
import csv, random
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
def spear(a,b):
    ra=np.argsort(np.argsort(a)).astype(float); rb=np.argsort(np.argsort(b)).astype(float)
    ra-=ra.mean(); rb-=rb.mean(); return (ra@rb)/(np.sqrt((ra@ra)*(rb@rb))+1e-30)

VARIANTS={
 "Xmodn/n":   lambda x,y,n:(x%n)/n,
 "Ymodn/n":   lambda x,y,n:(y%n)/n,
 "X+Ymodn/n": lambda x,y,n:((x+y)%n)/n,
 "XYmodn/n":  lambda x,y,n:((x*y)%n)/n,
 "Xmodn2/n2": lambda x,y,n:(x%(n*n))/(n*n),
 "XYmodn2/n2":lambda x,y,n:((x*y)%(n*n))/(n*n),
}
def variant_rhos(Xs,Ys,ns,ks):
    s=np.array(ks)/np.array(ns); out={}
    for nm,f in VARIANTS.items():
        r=np.array([f(int(Xs[i]),int(Ys[i]),int(ns[i])) for i in range(len(ns))])
        out[nm]=spear(r,s)
    return out

rows=[]
with open('/Users/trentpalelei/Desktop/Math Ex/btc_puzzle_investigation/puzzles_verified.csv') as f:
    for r in csv.DictReader(f):
        if int(r['bits'])>=11 and int(r['n'])>=5:
            rows.append((int(r['bits']),int(r['X'],16),int(r['Y'],16),int(r['n']),int(r['k'])))
Bs=[b for b,_,_,_,_ in rows]; RX=[x for _,x,_,_,_ in rows]; RY=[y for _,_,y,_,_ in rows]
RN=[n for _,_,_,n,_ in rows]; RK=[k for _,_,_,_,k in rows]; M=len(rows)

real=variant_rhos(RX,RY,RN,RK)
real_max=max(abs(v) for v in real.values())
print(f"PART A  ({M} real keys). per-variant real rho:")
for nm,v in real.items(): print(f"    {nm:11s}: {v:+.3f}")
print(f"    real MAX|rho| = {real_max:.3f}  (variant: {max(real,key=lambda k:abs(real[k]))})")

NB=1000; _r=random.Random(11)
nullmax=[]
for _ in range(NB):
    Xs=[];Ys=[];ns=[];ks=[]
    for b in Bs:
        lo=2**(b-1); tries=0; n,k,d=1,0,lo
        while tries<500:
            d=lo+_r.randrange(lo); u=(d-lo)/lo; n,k=best_nk(u)
            if n>=5 and 0<k<n: break
            tries+=1
        x,y=mulxy(d); Xs.append(x);Ys.append(y);ns.append(n);ks.append(k)
    vr=variant_rhos(Xs,Ys,ns,ks); nullmax.append(max(abs(v) for v in vr.values()))
nullmax=np.array(nullmax)
pcorr=(1+(nullmax>=real_max).sum())/(1+len(nullmax))
print(f"    matched null MAX|rho|: median={np.median(nullmax):.3f} 95pct={np.quantile(nullmax,.95):.3f}")
print(f"    look-elsewhere-CORRECTED p = {pcorr:.3f}")

# ---------------- PART B: mechanism ----------------
print("\nPART B  mechanism (72 real keys)")
s=np.array(RK)/np.array(RN)
xyn2=np.array([((RX[i]*RY[i])%(RN[i]**2))/(RN[i]**2) for i in range(M)])
def pearson(a,b):
    a=a-a.mean(); b=b-b.mean(); return (a@b)/(np.sqrt((a@a)*(b@b))+1e-30)
print(f"  B1 Spearman={spear(xyn2,s):+.3f}  Pearson={pearson(xyn2,s):+.3f}")
jk=[spear(np.delete(xyn2,i),np.delete(s,i)) for i in range(M)]
print(f"     jackknife drop-1 Spearman: min={min(jk):+.3f} max={max(jk):+.3f} "
      f"(#drops with |rho|<0.15: {sum(abs(x)<0.15 for x in jk)}/{M})")

bits=np.array(Bs,float)
u=s.copy()  # k/n ~ position; also compute the actual residual sign proxy
resid=np.array([ ( (d:=0) , 0)[1] for _ in range(M)])  # placeholder
print("  B2 what does XYmodn2/n2 track (Spearman):")
for nm,t in (("k/n",s),("raw k",np.array(RK,float)),("raw n",np.array(RN,float)),
             ("bits",bits)):
    print(f"     vs {nm:6s}: {spear(xyn2,t):+.3f}")
print("  B3 does the product matter (vs k/n):")
xn2=np.array([(RX[i]%(RN[i]**2))/(RN[i]**2) for i in range(M)])
yn2=np.array([(RY[i]%(RN[i]**2))/(RN[i]**2) for i in range(M)])
print(f"     X mod n^2 alone: {spear(xn2,s):+.3f}   Y mod n^2 alone: {spear(yn2,s):+.3f}")
print("  B4 why n^2 (rho of XY mod n^j / n^j vs k/n):")
for j in (1,2,3):
    v=np.array([((RX[i]*RY[i])%(RN[i]**j))/(RN[i]**j) for i in range(M)])
    print(f"     j={j}: {spear(v,s):+.3f}")
