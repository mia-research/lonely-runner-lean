import random
from math import gcd
import ecc_secp256k1 as E
rnd=random.Random(2026)

def best_nk(v,b,NMAX=256):
    A=1<<(b-1); num=v-A; best=None
    for n in range(1,NMAX+1):
        k=(2*n*num+A)//(2*A); k=0 if k<0 else (n if k>n else k)
        for kk in (k-1,k,k+1):
            if 0<=kk<=n:
                key=(abs(n*num-kk*A),n,kk)
                if best is None or key<best: best=key
    _,n,k=best; g=gcd(k,n) if n else 1
    return (n//g,k//g) if g>1 else (n,k)

# 1) start: a 256-bit integer = the private key
PK = (1<<255) + rnd.randrange(1<<255)
print(f"[1] private integer PK = 256-bit, = {hex(PK)[:20]}...")

# 2) PUBLIC view: X,Y = PK·G
X,Y = E.scalar_mul(PK)
print(f"[2] PUBLIC  -> X = {hex(X)[:20]}...   Y = {hex(Y)[:18]}...")

# 3) PRIVATE view: simple fraction (n,k) + residual d  (one level shown)
N=256; A=1<<(N-1)
n,k = best_nk(PK,N)
base = A + (A*k)//n
d = PK - base                    # residual ("d"/error), to be expanded into error terms
print(f"[3] PRIVATE -> simple fraction k/n = {k}/{n};  base=A+floor(A*k/n)")
print(f"              residual d = PK - base = {'+' if d>=0 else '-'}2^{abs(d).bit_length()}  (this is what carries the recursive error terms)")

# 4) invert: reconstruct PK from (n,k,d)
PK2 = base + d
print(f"[4] RECONSTRUCT PK from (n,k,d): {'EXACT' if PK2==PK else 'MISMATCH'}")
print()
print("So the pipeline is: 256-bit integer  ->  (public: X,Y)  and  (private: n,k,d+error terms)  ->  invert to PK.")
print("The ONE box I keep mis-modelling is how 'd' expands into its recursive error terms.")
