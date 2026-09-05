"""
REALLY LOOK at F2 = gcd(Y,n)>1 running low, with F1's rigor. No verdicts.

A  MEASUREMENT vs FAITHFUL null: gcd(Y,n)>1 rate on real keys vs synthetic keys
   with REAL curve Y (matched bit-length multiset). gcd(X,n) shown alongside
   (the variant that did NOT flicker -> the look-elsewhere context).
B  MECHANISM: is this about n, or a property of Y itself? gcd(Y,n)>1 is dominated
   by the shared factor 2 (n even & Y even). So check Y's small-prime profile
   directly: is Y odd more than 50%? Decompose the gcd rate by n-parity. If it is
   a Y-parity property it shows at n and neighbors alike (explains non-localization).
C  HINT VALUE (the real goal): as an n-EXCLUSION filter. If the true n has
   gcd(Y,n)=1 more than the base coprimality rate, then "drop candidate n with
   gcd(Y,n)>1" prunes the n-search while keeping the true n. Measure the prune
   fraction and the true-n retention.
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

rows=[]
with open('/Users/trentpalelei/Desktop/Math Ex/btc_puzzle_investigation/puzzles_verified.csv') as f:
    for r in csv.DictReader(f):
        if int(r['bits'])>=11 and int(r['n'])>=5:
            rows.append((int(r['bits']),int(r['X'],16),int(r['Y'],16),int(r['n']),int(r['k'])))
B=[b for b,_,_,_,_ in rows]; X=[x for _,x,_,_,_ in rows]; Yc=[y for _,_,y,_,_ in rows]
Ncsv=[n for _,_,_,n,_ in rows]; M=len(rows)

# ---- A: measurement vs faithful matched null ----
obsY=sum(gcd(Yc[i],Ncsv[i])>1 for i in range(M))
obsX=sum(gcd(X[i],Ncsv[i])>1 for i in range(M))
_r=random.Random(3); NB=300
nY=[];nX=[]
for _ in range(NB):
    cY=0;cX=0
    for b in B:
        lo=2**(b-1); tries=0;n,k,d=1,0,lo
        while tries<500:
            d=lo+_r.randrange(lo);u=(d-lo)/lo;n,k=best_nk(u)
            if n>=5 and 0<k<n: break
            tries+=1
        x,y=mulxy(d); cY+=gcd(y,n)>1; cX+=gcd(x,n)>1
    nY.append(cY);nX.append(cX)
nY=np.array(nY);nX=np.array(nX)
pY=(1+(nY<=obsY).sum())/(1+NB); pX=(1+(nX<=obsX).sum())/(1+NB)
print(f"A  gcd(.,n)>1 count (M={M}) vs faithful matched null (real curve, {NB} draws):")
print(f"   gcd(Y,n)>1: real={obsY}  null-med={np.median(nY):.0f}  p(low)={pY:.3f}")
print(f"   gcd(X,n)>1: real={obsX}  null-med={np.median(nX):.0f}  p(low)={pX:.3f}   (the non-flicker variant)")

# ---- B: mechanism -- is it a property of Y itself (factor 2)? ----
Yodd=np.mean([Yc[i]%2==1 for i in range(M)])
print(f"\nB  mechanism -- is it Y's own small-factor profile?")
print(f"   P(Y odd)={Yodd:.3f}  (uniform=0.500; {sum(Yc[i]%2==1 for i in range(M))}/{M})")
print(f"   P(Y=0 mod 3)={np.mean([Yc[i]%3==0 for i in range(M)]):.3f} (uniform=0.333)")
even_n=[i for i in range(M) if Ncsv[i]%2==0]; odd_n=[i for i in range(M) if Ncsv[i]%2==1]
print(f"   gcd(Y,n)>1 rate | n even ({len(even_n)} keys): {np.mean([gcd(Yc[i],Ncsv[i])>1 for i in even_n]):.3f}")
print(f"   gcd(Y,n)>1 rate | n odd  ({len(odd_n)} keys): {np.mean([gcd(Yc[i],Ncsv[i])>1 for i in odd_n]):.3f}")
print(f"   (if the deficit is the factor-2 story, it lives in the even-n keys via Y being odd)")

# ---- C: hint value -- gcd(Y,n)=1 as an n-exclusion filter ----
true_coprime=np.mean([gcd(Yc[i],Ncsv[i])==1 for i in range(M)])
base_coprime=np.mean([phi(Ncsv[i])/Ncsv[i] for i in range(M)])
# average fraction of candidate n (5..256) that the filter RETAINS, per key
retain=[]
for i in range(M):
    keep=sum(gcd(Yc[i],nn)==1 for nn in range(5,257)); retain.append(keep/252)
retain=np.mean(retain)
print(f"\nC  hint value -- 'drop candidate n with gcd(Y,n)>1' as an n-filter:")
print(f"   true-n coprime rate = {true_coprime:.3f}   base coprime rate (phi/n avg) = {base_coprime:.3f}")
print(f"   avg candidate-n retained by the filter = {retain:.3f}  (so it prunes ~{100*(1-retain):.0f}% of n)")
print(f"   filter keeps the TRUE n at {true_coprime:.3f} vs a random n at {retain:.3f}")
print(f"   -> informative-as-a-filter only if true-n retention >> random-n retention.")
