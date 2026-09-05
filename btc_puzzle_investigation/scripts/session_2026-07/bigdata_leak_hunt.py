"""
HIGH-POWER (X,Y)-LEAK HUNT on a large synthetic set. The leak question -- does
(X,Y) carry info about n/k/d-structure -- is a property of the MAP, valid to test
with uniform synthetic keys at arbitrary power (independent of the creator's PRNG,
which we are NOT attacking). 20k keys -> detection floor ~2% vs ~30% at 72 keys.

Targets include the two un-run GECT ideas as LEAK targets:
  #3 special-n class: is n prime / phi(n)=2^r / #distinct-primes / smooth?
  #2 short expansion: continued-fraction length of k/n (expansion complexity).
Plus the core: n, k residues, top-bit position.

Detector: best (X,Y)-feature mutual information, G-test analytic p (2N ln2 * MI ~
chi^2), Bonferroni over the feature bag. At 20k any real map-leak clears the bar.
Also prints the BASELINE distributions of the #2/#3 features (uniform reference).
"""
import csv, random, math
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
def factors(n):
    f=set(); t=n; p=2
    while p*p<=t:
        while t%p==0: f.add(p); t//=p
        p+=1
    if t>1: f.add(t)
    return f
def phi(n):
    r=n
    for p in factors(n): r-=r//p
    return r
def is_prime(n): return n>1 and len(factors(n))==1 and list(factors(n))[0]==n
def cf_len(k,n):
    t=0
    while n: k,n=n,k%n; t+=1
    return t

NS=20000; BITMIN,BITMAX=24,160
_r=random.Random(7)
print(f"generating {NS} synthetic keys, bit-lengths {BITMIN}-{BITMAX}...")
Xs=[];Ys=[];Nn=[];Kk=[]
for _ in range(NS):
    b=_r.randint(BITMIN,BITMAX); lo=2**(b-1); tries=0;n,k,d=1,0,lo
    while tries<500:
        d=lo+_r.randrange(lo);u=(d-lo)/lo;n,k=best_nk(u)
        if n>=5 and 0<k<n: break
        tries+=1
    x,y=mulxy(d); Xs.append(x);Ys.append(y);Nn.append(n);Kk.append(k)
Nn=np.array(Nn);Kk=np.array(Kk); N=len(Nn)

# structural targets (#2 / #3)
n_prime=np.array([1 if is_prime(int(n)) else 0 for n in Nn])
n_phi2r=np.array([1 if (phi(int(n))&(phi(int(n))-1))==0 else 0 for n in Nn])
n_omega=np.array([min(len(factors(int(n))),3) for n in Nn])
n_smooth=np.array([1 if max(factors(int(n)))<=7 else 0 for n in Nn])
cflen=np.array([min(cf_len(int(Kk[i]),int(Nn[i])),8) for i in range(N)])
print("\nBASELINE (uniform) distributions of the #2/#3 features:")
print(f"  #3 P(n prime)={n_prime.mean():.3f}  P(phi=2^r)={n_phi2r.mean():.3f}  "
      f"P(n 7-smooth)={n_smooth.mean():.3f}  mean #distinct-primes={np.mean([len(factors(int(n))) for n in Nn]):.2f}")
print(f"  #2 CF-length of k/n: mean={cflen.mean():.2f} dist={np.bincount(cflen)/N}")

# (X,Y) feature bag
feat={}
for m in (2,3,5,7,11,13,17,19,23,29,31):
    feat[f"X%{m}"]=np.array([int(x)%m for x in Xs]); feat[f"Y%{m}"]=np.array([int(y)%m for y in Ys])
    feat[f"XY%{m}"]=np.array([(int(x)*int(y))%m for x,y in zip(Xs,Ys)])
for p in (3,5,7,11,13,17,19):
    feat[f"Xleg{p}"]=np.array([pow(int(x)%p,(p-1)//2,p) for x in Xs])
    feat[f"Yleg{p}"]=np.array([pow(int(y)%p,(p-1)//2,p) for y in Ys])
for b in range(0,256,16):
    feat[f"Xb{b}"]=np.array([(int(x)>>b)&1 for x in Xs])
    feat[f"Yb{b}"]=np.array([(int(y)>>b)&1 for y in Ys])
# NOTE: features must be computable from (X,Y) ALONE. Any feature that uses n
# (e.g. XY mod n^2) is circular for predicting n/k and is deliberately excluded.
# Alphabets kept small (<=31) so high-N mutual-information bias stays negligible.
fnames=list(feat)

def mi_bits(f,t):
    A=int(f.max())+1;B=int(t.max())+1;j=np.zeros((A,B))
    for a,b in zip(f,t): j[a,b]+=1
    j/=j.sum();pa=j.sum(1,keepdims=True);pb=j.sum(0,keepdims=True)
    with np.errstate(divide='ignore',invalid='ignore'):
        term=j*np.log2((j+1e-30)/(pa*pb+1e-30))
    return float(term[j>0].sum()),A,B
def chi2_sf(x,df):
    if x<=0 or df<=0: return 1.0
    t=(x/df)**(1/3); mu=1-2/(9*df); s=math.sqrt(2/(9*df)); z=(t-mu)/s
    return 0.5*math.erfc(z/math.sqrt(2))

targets={"n%6":Nn%6,"n%8":Nn%8,"k%6":Kk%6,"k%8":Kk%8,
         "n_prime":n_prime,"n_phi2r":n_phi2r,"n_omega":n_omega,"n_smooth":n_smooth,"cflen":cflen}
print(f"\nHIGH-POWER LEAK: best (X,Y)-feature -> target, G-test, Bonferroni x{len(fnames)}:")
print(f"{'target':>9} | {'bestMI(bits)':>12} | {'Bonf-p':>8} | feature")
for tn,t in targets.items():
    best=(9e9,None,0.0)
    for fn in fnames:
        mi,A,B=mi_bits(feat[fn],t); g=2*N*math.log(2)*mi; p=chi2_sf(g,(A-1)*(B-1))
        if p<best[0]: best=(p,fn,mi)
    bp=min(1.0,best[0]*len(fnames))
    print(f"{tn:>9} | {best[2]:>12.5f} | {bp:>8.3f} | {best[1]}{'  << LEAK' if bp<0.01 else ''}")
print("\nAt 20k keys any Bonferroni-p<0.01 is a real map-level leak. All high => (X,Y)")
print("carries no info about these targets even at this power (ECDLP flatness, tight).")
