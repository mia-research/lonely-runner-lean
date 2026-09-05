"""
Extend the data with realistic synthetic keys (uniform random, real curve, real
n,k,d,X,Y) at the EXACT real bit-length multiset, x REP copies -> ~20k keys.
High-power UNIFORM baseline for F1, F2, and the Y small-factor profile.

What this resolves:
  - MATH-RELATION hypothesis: if F1/F2 is a curve/decomposition property, it shows
    here at 20k-key power. rho~0 / rates at expectation => NOT a math relation.
  - the exact uniform null for each statistic (tight, SE ~ 1/sqrt(20000)).
What it cannot resolve:
  - whether the REAL keys are themselves uniform (the selection hypothesis) --
    uniform synthetic IS the null for that; only real keys test it.
Real 72-key values printed alongside for comparison.
"""
import csv, random
from math import gcd
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
def phi(n):
    r=n;t=n;p=2
    while p*p<=t:
        if t%p==0:
            while t%p==0:t//=p
            r-=r//p
        p+=1
    if t>1:r-=r//t
    return r
def spear(a,b):
    ra=np.argsort(np.argsort(a)).astype(float); rb=np.argsort(np.argsort(b)).astype(float)
    ra-=ra.mean(); rb-=rb.mean(); return (ra@rb)/(np.sqrt((ra@ra)*(rb@rb))+1e-30)

rows=[]
with open('/Users/trentpalelei/Desktop/Math Ex/btc_puzzle_investigation/puzzles_verified.csv') as f:
    for r in csv.DictReader(f):
        if int(r['bits'])>=11 and int(r['n'])>=5:
            rows.append((int(r['bits']),int(r['X'],16),int(r['Y'],16),int(r['n']),int(r['k'])))
Bs=[b for b,_,_,_,_ in rows]
# real values
rF1=spear(np.array([((int(x)*int(y))%(n*n))/(n*n) for _,x,y,n,_ in rows]),
          np.array([k/n for _,_,_,n,k in rows]))
rYodd=np.mean([y%2==1 for _,_,y,_,_ in rows]); rY3=np.mean([y%3==0 for _,_,y,_,_ in rows])
rGcd=np.mean([gcd(y,n)>1 for _,_,y,n,_ in rows]); rTrueCo=np.mean([gcd(y,n)==1 for _,_,y,n,_ in rows])
rBase=np.mean([phi(n)/n for _,_,_,n,_ in rows])

REP=280; _r=random.Random(2026)
feat=[]; s=[]; yodd=0; y3=0; gcdc=0; trueco=0; base=0.0; tot=0
print(f"generating ~{len(Bs)*REP} synthetic keys...")
for _ in range(REP):
    for b in Bs:
        lo=2**(b-1); tries=0;n,k,d=1,0,lo
        while tries<500:
            d=lo+_r.randrange(lo);u=(d-lo)/lo;n,k=best_nk(u)
            if n>=5 and 0<k<n: break
            tries+=1
        x,y=mulxy(d)
        feat.append(((x*y)%(n*n))/(n*n)); s.append(k/n)
        yodd+=y%2==1; y3+=y%3==0; gcdc+=gcd(y,n)>1; trueco+=gcd(y,n)==1; base+=phi(n)/n; tot+=1
feat=np.array(feat); s=np.array(s)
synF1=spear(feat,s); se=1/np.sqrt(tot)
print(f"\n{'statistic':<26}{'REAL (72)':>12}{'SYNTH uniform (~20k)':>22}")
print(f"{'F1 Spearman(XYmodn2, k/n)':<26}{rF1:>12.3f}{synF1:>16.4f} (SE {se:.3f})")
print(f"{'P(Y odd)':<26}{rYodd:>12.3f}{yodd/tot:>22.4f}")
print(f"{'P(Y = 0 mod 3)':<26}{rY3:>12.3f}{y3/tot:>22.4f}")
print(f"{'gcd(Y,n)>1 rate':<26}{rGcd:>12.3f}{gcdc/tot:>22.4f}")
print(f"{'true-n coprime rate':<26}{rTrueCo:>12.3f}{trueco/tot:>22.4f}")
print(f"{'base coprime (phi/n)':<26}{rBase:>12.3f}{base/tot:>22.4f}")
print(f"\nSE on the synth mean ~ {se:.3f}. If a synth rate/rho sits at its expectation")
print("(F1~0, P(Y odd)~0.5, gcd rate~1-coprime), there is NO math relation -> the real")
print("72-key deviations are selection-or-noise, decidable only by real keys or mechanism.")
