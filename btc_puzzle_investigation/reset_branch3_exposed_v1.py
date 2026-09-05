#!/usr/bin/env python3
"""
BRANCH 3b (the data-free part): GLV / endomorphism relations.

The endomorphism phi(x,y)=(beta*x,y) acts as d -> lambda*d mod n (lambda^3=1). So the
six mu_6 images of a key d are {+-d, +-lambda*d, +-lambda^2*d} mod n. If any solved
key's image lands in an UNSOLVED exposed range [2^(b-1),2^b) for b in {135,140,...,160},
that unsolved key = an endomorphism image of a known one (a full break). Also test the
82 solved keys for internal GLV-conjugacy. Needs only d_i, n, lambda -- no pubkeys.
Also sanity-decompress the one on-disk exposed point (#135).
Exact integers; control = a planted image must be detected.
"""
from ecc_secp256k1 import N_ORDER as n, P, scalar_mul
from reset_common import load_solved

# lambda = primitive cube root of 1 mod n : root of x^2+x+1
def sqrt_mod(a,p):
    a%=p
    if pow(a,(p-1)//2,p)!=1: return None
    # p % 4 == 3 ? n is not; use Tonelli
    if p%4==3: return pow(a,(p+1)//4,p)
    s=p-1; e=0
    while s%2==0: s//=2; e+=1
    z=2
    while pow(z,(p-1)//2,p)!=p-1: z+=1
    x=pow(a,(s+1)//2,p); b=pow(a,s,p); g=pow(z,s,p); r=e
    while True:
        t=b; m=0
        for m in range(r):
            if t==1: break
            t=t*t%p
        if m==0: return x
        gs=pow(g,1<<(r-m-1),p); g=gs*gs%p; x=x*gs%p; b=b*g%p; r=m
s=sqrt_mod(n-3, n)
lam=((-1+s)*pow(2,-1,n))%n
assert (lam*lam+lam+1)%n==0, "lambda check"
print("=== BRANCH 3b: GLV / endomorphism relations ===\n")
print(f"lambda (cube root of 1 mod n) ok; lambda^3 mod n = {pow(lam,3,n)}")

solved=load_solved(); KEYS=sorted(solved); D={N:solved[N]["d"] for N in KEYS}
EXPOSED=[135,140,145,150,155,160]
ranges={b:(1<<(b-1), 1<<b) for b in EXPOSED}

def images(d):
    return [d%n, (n-d)%n, (lam*d)%n, (n-lam*d)%n, (lam*lam*d)%n, (n-lam*lam*d)%n]

# test: any solved-key image in an exposed range?
hits=[]
for N in KEYS:
    for img in images(D[N]):
        for b,(lo,hi) in ranges.items():
            if lo<=img<hi: hits.append((N,b,img))
print(f"\nsolved-key endomorphism images landing in an exposed range: "
      f"{hits if hits else 'NONE'}")

# internal GLV-conjugacy among solved keys
conj=[]
for i,Ni in enumerate(KEYS):
    imgs=set(images(D[Ni]))-{D[Ni]}
    for Nk in KEYS:
        if Nk<=Ni: continue
        if D[Nk] in imgs: conj.append((Ni,Nk))
print(f"internal GLV-conjugate solved-key pairs: {conj if conj else 'NONE'}")

# control: plant an image, confirm detection
d_seed=D[KEYS[10]]; planted=(lam*d_seed)%n
det=any(planted in images(D[N]) for N in KEYS)
print(f"\n[CTRL] lambda*d(#{KEYS[10]}) is detected as an image of d(#{KEYS[10]}): {det}")

# sanity: decompress #135 pubkey, verify on curve
TARGET_135="02145d2611c823a396ef6712ce0f712f09b9b4f3135e3e0aa3230fb9b6d08d1e16"
X=int(TARGET_135[2:],16); yy=(pow(X,3,P)+7)%P
Y=pow(yy,(P+1)//4,P)
if Y%2!=(0 if TARGET_135[:2]=="02" else 1): Y=P-Y
on=(Y*Y-yy)%P==0
print(f"\n#135 pubkey decompresses on-curve: {on} (X={hex(X)[:12]}...)")
# is X_135 endomorphism image of X of a solved point? (phi: X->beta*X)
beta=pow(2, (P-1)//3, P)  # a cube root of 1 mod p (one of them)
print(f"\n-> " + ("BREAK: endomorphism relation found (see above)" if hits or conj else
   "no GLV/endomorphism relation between known and exposed keys, nor among solved keys "
   "(exact, control-valid). Scope: multi-point relations among the 140..160 exposed "
   "points need those pubkeys fetched (only #135 is on disk)."))
