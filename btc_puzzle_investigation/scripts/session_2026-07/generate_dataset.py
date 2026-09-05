"""
Build a ~20k dataset of constructed integers (keys) across bit lengths 1..160.
Per bit length b: min(130, 2^(b-1)) distinct keys d in [2^(b-1), 2^b) (top bit set
+ random low bits = the puzzle construction). For each key emit the private key
(int/hex/WIF), public key (X,Y), address, and the (n,k,D) decomposition + term
count. Self-integrity check at the end: reconstruct==d and address round-trip.
"""
import csv, random, hashlib, base58
from math import gcd

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
        if e<best[0]: best=(e,n,int(k))
    return best[1],best[2]
def decomp(d,N):
    lo=2**(N-1); u=(d-lo)/lo if N>1 else 0.0
    n,k=best_nk(u) if N>1 else (1,0)
    base=lo+(lo*k)//n; return n,k,base,d-base
def d_terms(n,k,N,d):
    lo=2**(N-1); cur=lo+(lo*k)//n; err=d-cur; t=0
    while err!=0 and t<200:
        Di=lo//abs(err)
        if Di==0: cur+=err; err=0; t+=1; break
        corr=lo//Di; cur+= corr if err>0 else -corr; err=d-cur; t+=1
    return t
def wif(d):
    b=b'\x80'+d.to_bytes(32,'big')+b'\x01'
    return base58.b58encode(b+hashlib.sha256(hashlib.sha256(b).digest()).digest()[:4]).decode()
def address(X,Y):
    pk=(b'\x02' if Y%2==0 else b'\x03')+X.to_bytes(32,'big')
    h=hashlib.new('ripemd160',hashlib.sha256(pk).digest()).digest()
    v=b'\x00'+h; return base58.b58encode(v+hashlib.sha256(hashlib.sha256(v).digest()).digest()[:4]).decode()

PER=660
OUT="/Users/trentpalelei/Desktop/Math Ex/btc_puzzle_investigation/constructed_keys_1to160_100k.csv"
_r=random.Random(20260706)
rows=[]
for b in range(1,161):
    lo=2**(b-1); span=2**(b-1)
    want=min(PER,span)
    if span<=want:
        ds=list(range(lo,lo+span))
    else:
        seen=set()
        while len(seen)<want: seen.add(lo+_r.randrange(span))
        ds=list(seen)
    for d in ds:
        n,k,base,D=decomp(d,b); X,Y=mulxy(d)
        rows.append((b,d,d.to_bytes(32,'big').hex(),wif(d),format(X,'064x'),format(Y,'064x'),
                     address(X,Y),n,k,D,d_terms(n,k,b,d)))
    if b%20==0: print(f"  bit-length {b} done, rows so far {len(rows)}")

with open(OUT,'w',newline='') as f:
    w=csv.writer(f)
    w.writerow(["bits","d","priv_hex","wif","X","Y","address","n","k","D","D_terms"])
    w.writerows(rows)
print(f"\nwrote {len(rows)} rows -> {OUT}")

# self-integrity on a random sample
samp=_r.sample(rows,300)
okd=okad=0
for (b,d,ph,wf,Xh,Yh,ad,n,k,D,dt) in samp:
    base=2**(b-1)+(2**(b-1)*k)//n
    okd += (base+D==d)
    X,Y=int(Xh,16),int(Yh,16); okd_xy = mulxy(d)==(X,Y)
    okad += (address(X,Y)==ad) and okd_xy
print(f"self-check on 300 sampled rows: reconstruct base+D==d {okd}/300, (X,Y)+address ok {okad}/300")
by_bits={}
for r in rows: by_bits[r[0]]=by_bits.get(r[0],0)+1
print(f"bit-lengths covered: {min(by_bits)}..{max(by_bits)}  (e.g. b=1:{by_bits[1]}, b=8:{by_bits[8]}, b=160:{by_bits[160]})")
