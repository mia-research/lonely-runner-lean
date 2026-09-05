"""
INTEGRITY TEST of the (n,k,d) decomposition on the constructed datasets and the
real keys. For each key:
  decompose : u=(d-2^(N-1))/2^(N-1) (exact rational) -> (n,k)=best rational approx,
              base = 2^(N-1) + floor(2^(N-1)*k/n),  D = d - base.
  reconstruct: d' = base + D.  ASSERT d' == d.
  curve     : ASSERT mulxy(d') == (X,Y).
  round-trip: (real keys) ASSERT address(X,Y) == recorded address.

Honest framing (the GECT lesson): D = d - base is the residual, so base+D==d is
EXACT by construction -- the test validates the arithmetic + curve + address
pipeline and dataset consistency, NOT that (n,k) ALONE fixes d. We also report the
base-only gap |d - base| to show (n,k) alone lands you within D, not on the key.
"""
import csv, random, hashlib, base58
from math import gcd
from fractions import Fraction

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
def best_nk_exact(d,N,nmax=256):
    lo=2**(N-1); u=Fraction(d-lo,lo); best=None
    for n in range(1,nmax+1):
        k=round(u*n); e=abs(u-Fraction(int(k),n))
        if best is None or e<best[0]: best=(e,n,int(k))
    return best[1],best[2]
def decompose(d,N):
    n,k=best_nk_exact(d,N); lo=2**(N-1); base=lo+(lo*k)//n; return n,k,base,d-base
def address(X,Y):
    pk=(b'\x02' if Y%2==0 else b'\x03')+X.to_bytes(32,'big')
    h=hashlib.new('ripemd160',hashlib.sha256(pk).digest()).digest()
    v=b'\x00'+h; c=hashlib.sha256(hashlib.sha256(v).digest()).digest()[:4]
    return base58.b58encode(v+c).decode()

def run(name, keys, check_addr=False):
    okd=okxy=okad=0; gaps=[]; T=len(keys)
    for (d,N,Xexp,Yexp,addr) in keys:
        n,k,base,D=decompose(d,N)
        dprime=base+D
        okd += (dprime==d)
        gaps.append(abs(d-base))
        X,Y=mulxy(dprime)
        xyok = (Xexp is None) or (X==Xexp and Y==Yexp)
        okxy += (X,Y)==(mulxy(d)) if Xexp is None else xyok
        if check_addr: okad += (address(X,Y)==addr)
    med_gap_bits = sorted(gaps)[len(gaps)//2].bit_length()
    print(f"  {name:28s} keys={T:5d}  reconstruct d'==d: {okd}/{T}  "
          f"mulxy==(X,Y): {okxy}/{T}" + (f"  address ok: {okad}/{T}" if check_addr else "")
          + f"   median |d-base|={med_gap_bits} bits")

# 1) REAL keys (with recorded X,Y,address) -- full on-chain-consistent round-trip
real=[]
with open('/Users/trentpalelei/Desktop/Math Ex/btc_puzzle_investigation/puzzles_verified.csv') as f:
    for r in csv.DictReader(f):
        real.append((int(r['private_key'],16),int(r['bits']),int(r['X'],16),int(r['Y'],16),r['address']))
print("INTEGRITY TEST\n(d'==d is exact by construction: D=d-base. This checks arithmetic/curve/address")
print(" pipeline + dataset consistency, and reports the |d-base| gap = what D must supply.)\n")
run("REAL puzzle keys", real, check_addr=True)

# 2) CONSTRUCTED n-variable dataset: sweep n=5..256, random coprime k, small random D
_r=random.Random(1); Nb=96; lo=2**(Nb-1)
nvar=[]
for n in range(5,257):
    ks=[k for k in range(1,n) if gcd(k,n)==1]
    k=_r.choice(ks); base=lo+(lo*k)//n
    D=_r.randrange(max(1,lo//(4*n*n)))     # small residual, keeps (n,k) as best approx
    d=base+D; X,Y=mulxy(d); nvar.append((d,Nb,X,Y,None))
run("CONSTRUCTED n-variable", nvar)

# 3) CONSTRUCTED k-variable dataset: fix n=251 (prime), sweep all coprime k, small D
n0=251; kvar=[]
for k in range(1,n0):
    base=lo+(lo*k)//n0; D=_r.randrange(max(1,lo//(4*n0*n0)))
    d=base+D; X,Y=mulxy(d); kvar.append((d,Nb,X,Y,None))
run("CONSTRUCTED k-variable (n=251)", kvar)

# 4) honest check: does (n,k) ALONE (D=0) equal d? -> compare decompose->(n,k) match rate
match=0
for (d,N,_,_,_) in nvar:
    n,k,base,D=decompose(d,N); match += (base==d)
print(f"\n  (n,k)-alone reconstructs d exactly (D==0) in {match}/{len(nvar)} n-variable keys")
print("  -> as expected, (n,k) lands on 'base'; the exact key needs D. Datasets are")
print("     internally consistent IF reconstruct/mulxy/address columns all pass above.")
