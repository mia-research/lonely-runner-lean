"""
MOST-FAITHFUL synthetic null for F1: match the EXACT bit-length multiset of the 82
real keys, real curve arithmetic, and ask where the real Spearman(XY mod n^2/n^2,
k/n)=~0.25 falls in the distribution of that same statistic over matched-random
datasets. This is the correct null the concern points at: same scales, same mix,
only the key values randomized.

  real rho typical of matched synthetic  -> F1 is a sampling/mixing artifact.
  real rho in the tail                   -> F1 stands out even here; re-open it.
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
def spearman(a,b):
    ra=np.argsort(np.argsort(a)).astype(float); rb=np.argsort(np.argsort(b)).astype(float)
    ra-=ra.mean(); rb-=rb.mean(); return (ra@rb)/(np.sqrt((ra@ra)*(rb@rb))+1e-30)
def F1_rho(Xs,Ys,ns,ks):
    m=len(ns); s=np.array(ks)/np.array(ns)
    r=np.array([((int(Xs[i])*int(Ys[i]))%(int(ns[i])**2))/(int(ns[i])**2) for i in range(m)])
    return spearman(r,s)

rows=[]
with open('/Users/trentpalelei/Desktop/Math Ex/btc_puzzle_investigation/puzzles_verified.csv') as f:
    for r in csv.DictReader(f):
        # bits>=11: band large enough that best-approx n>=5,0<k<n always exists
        # (bits<=10 include the degenerate bits=1 band -> infinite rejection loop)
        if int(r['bits'])>=11 and int(r['n'])>=5:
            rows.append((int(r['bits']),int(r['X'],16),int(r['Y'],16),int(r['n']),int(r['k'])))
Bs=[b for b,_,_,_,_ in rows]
realrho=F1_rho([x for _,x,_,_,_ in rows],[y for _,_,y,_,_ in rows],
               [n for _,_,_,n,_ in rows],[k for _,_,_,_,k in rows])
print(f"{len(rows)} real keys (n>=5). real F1 rho = {realrho:+.3f}")

NB=400; _r=random.Random(11)
print(f"drawing {NB} matched-random datasets (exact bit-length multiset)...")
null=[]
for _ in range(NB):
    Xs=[];Ys=[];ns=[];ks=[]
    for b in Bs:
        lo=2**(b-1); tries=0; n,k,d=1,0,lo
        while tries<500:
            d=lo+_r.randrange(lo); u=(d-lo)/lo; n,k=best_nk(u)
            if n>=5 and 0<k<n: break
            tries+=1
        x,y=mulxy(d); Xs.append(x);Ys.append(y);ns.append(n);ks.append(k)
    null.append(F1_rho(Xs,Ys,ns,ks))
null=np.array(null)
p=(1+(np.abs(null)>=abs(realrho)).sum())/(1+len(null))
print(f"matched-null |rho|: median={np.median(np.abs(null)):.3f}  95pct={np.quantile(np.abs(null),0.95):.3f}")
print(f"real |rho|={abs(realrho):.3f}  ->  p={p:.3f}")
print("  p>>0.05: F1 is a sampling artifact of the 82 keys (same mix reproduces it).")
print("  p<0.05 : F1 stands out even vs the faithful matched null -> re-open.")
