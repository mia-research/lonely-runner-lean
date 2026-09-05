# ===== TEST THE IDEA: can public-key quantities predict d mod {2,3,6}? =====
# secp256k1, real parameters. Ground truth d known. Measure vs chance.
import numpy as np, math
p = 2**256 - 2**32 - 977
n = 115792089237316195423570985008687907852837564279074904382605163141518161494337
Gx = 0x79be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798
Gy = 0x483ada7726a3c4655da4fbfc0e1108a8fd17b448a68554199c47d08ffb10d4b8
lam = 0x5363ad4cc05c30e0a5261c028812645a122e22ea20816678df02967c1b23bd72  # GLV eigenvalue (lam^3=1 mod n)
beta= 0x7ae96a2b657c07106e64479eac3434e99cf0497512f58995c1396c28719501ee  # beta^3=1 mod p, phi(x,y)=(beta x, y)=[lam]P

def inv(a,m): return pow(a,-1,m)
def add(P,Q):
    if P is None:return Q
    if Q is None:return P
    x1,y1=P;x2,y2=Q
    if x1==x2 and (y1+y2)%p==0:return None
    if P==Q: m=(3*x1*x1)*inv(2*y1,p)%p
    else: m=(y2-y1)*inv((x2-x1)%p,p)%p
    x3=(m*m-x1-x2)%p; y3=(m*(x1-x3)-y1)%p; return (x3,y3)
def mul(k,P):
    R=None; Q=P
    while k>0:
        if k&1: R=add(R,Q)
        Q=add(Q,Q); k>>=1
    return R
G=(Gx,Gy)
# sanity: lam*G == phi(G)=(beta*Gx, Gy)
assert mul(lam%n,G)==((beta*Gx)%p,Gy)

def chi3(x):   # cubic residue symbol -> {0,1,2}
    v=pow(x%p,(p-1)//3,p)
    # v in {1, w, w^2}; map to exponent via matching powers of a fixed cube-root-of-unity in F_p
    w=pow(beta,1,p)  # beta is a primitive cube root of 1 mod p
    for j in range(3):
        if pow(w,j,p)==v: return j
    return None

def test(rng, lo, hi, N, label):
    # collect public-key features vs truth
    d2=np.zeros(N,int); d3=np.zeros(N,int); d6=np.zeros(N,int)
    ypar=np.zeros(N,int); yhalf=np.zeros(N,int); j3=np.zeros(N,int)
    for i in range(N):
        d=rng.randrange(lo,hi)
        P=mul(d,G); x,y=P
        d2[i]=d%2; d3[i]=d%3; d6[i]=d%6
        ypar[i]=y&1                # "compressed parity sign bit"
        yhalf[i]=1 if y< p//2 else 0
        j3[i]=chi3(x)              # GLV orbit index from public x
    def acc_best(feat, truth, k):
        # best deterministic map feat->truth, accuracy; chance=1/k
        from collections import Counter,defaultdict
        vote=defaultdict(Counter)
        for f,t in zip(feat,truth): vote[f][t]+=1
        pred={f:c.most_common(1)[0][0] for f,c in vote.items()}
        return np.mean([pred[f]==t for f,t in zip(feat,truth)])
    def MI(feat,truth):
        from collections import Counter
        Nn=len(feat); H=0.0
        cf=Counter(feat);ct=Counter(truth);cft=Counter(zip(feat,truth))
        import math as m
        mi=0.0
        for (f,t),c in cft.items():
            pft=c/Nn; pf=cf[f]/Nn; pt=ct[t]/Nn
            mi+=pft*m.log2(pft/(pf*pt))
        return mi
    print(f"\n--- {label} (N={N}) ---")
    print(f"  y-parity -> d mod2 : acc={acc_best(ypar,d2,2):.4f} (chance .5000)  MI={MI(ypar,d2):.2e} bits")
    print(f"  y<p/2    -> d mod2 : acc={acc_best(yhalf,d2,2):.4f} (chance .5000)  MI={MI(yhalf,d2):.2e} bits")
    print(f"  chi3(x)  -> d mod3 : acc={acc_best(j3,d3,3):.4f} (chance .3333)  MI={MI(j3,d3):.2e} bits")
    print(f"  (chi3,ypar)->d mod6: acc={acc_best(list(zip(j3,ypar)),d6,6):.4f} (chance .1667)  MI={MI(list(zip(j3,ypar)),d6):.2e} bits")

rng=np.random.default_rng(0)
import random as _r
class R:
    def __init__(s,seed): s.r=_r.Random(seed)
    def randrange(s,a,b): return s.r.randrange(a,b)
r=R(12345)
# Test 1: full-range keys
test(r, 1, n, 4000, "FULL-RANGE keys d in [1,n)")
# Test 2: puzzle-like small keys (like puzzle 135: d in [2^134, 2^135))
test(r, 2**134, 2**135, 4000, "PUZZLE-RANGE keys d in [2^134,2^135)")
