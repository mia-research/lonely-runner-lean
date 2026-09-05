#!/usr/bin/env python3
"""
Adjudicate the pasted ECDLP pipeline's ONE non-circular claim:

    "From public P=(x,y) alone, F(P)=chi3(x)*y unlocks the GLV orbit index
     j mod 3, and the Reciprocal-Floor congruence gives d mod 3."

Its own stated criterion (opening quote):
    "If evaluating [the invariant] requires the original scalar branch,
     the construction is circular."

We test the public channel directly:  does the PUBLIC statistic j(P) = chi3-index
predict the SECRET d mod 3 (or any low residue of d) better than chance?
Matched control = class-permutation. EXACT integer arithmetic, no floats in signal path.
"""
from fractions import Fraction
import random

# ---- secp256k1 ----
p  = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
n  = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141
Gx = 0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798
Gy = 0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8
BETA = 0x7ae96a2b657c07106e64479eac3434e99cf0497512f58995c1396c28719501ee  # cube root of 1 mod p
LAM  = 0x5363ad4cc05c30e0a5261c028812645a122e22ea20816678df02967c1b23bd72  # cube root of 1 mod n

def inv(a, m): return pow(a, -1, m)

def padd(P, Q):
    if P is None: return Q
    if Q is None: return P
    x1,y1 = P; x2,y2 = Q
    if x1==x2 and (y1+y2)%p==0: return None
    if P==Q:
        m = (3*x1*x1) * inv(2*y1, p) % p
    else:
        m = (y2-y1) * inv((x2-x1)%p, p) % p
    x3 = (m*m - x1 - x2) % p
    y3 = (m*(x1-x3) - y1) % p
    return (x3,y3)

def pmul(k, P):
    R=None; Q=P
    while k:
        if k&1: R=padd(R,Q)
        Q=padd(Q,Q); k>>=1
    return R

G=(Gx,Gy)

# ---- sanity: GLV endomorphism phi(P)=(beta*x, y)=lambda*P ----
assert pow(BETA,3,p)==1 and BETA!=1
assert pow(LAM,3,n)==1 and LAM!=1
Pt = pmul(123456789, G)
phi = ((BETA*Pt[0])%p, Pt[1])
assert phi == pmul(LAM*123456789 % n, G), "GLV relation failed"
print("[ok] GLV endomorphism phi(P)=(beta x,y)=lambda P verified")

# ---- chi3 readout: chi3(x)=x^((p-1)/3) in {1,w,w2}; index j in {0,1,2} ----
assert (p-1)%3==0
w = pow(2, (p-1)//3, p)          # a primitive cube root of unity mod p
if w==1:
    for g in range(3,50):
        w=pow(g,(p-1)//3,p)
        if w!=1: break
w2 = w*w % p
def chi3_index(x):
    v = pow(x % p, (p-1)//3, p)
    if v==1: return 0
    if v==w: return 1
    if v==w2: return 2
    return None  # x a cubic multiple only if v in {1,w,w2}; else x is nonzero noncube edgeless

# equivariance check: chi3(beta x) = w * chi3(x)  =>  index shifts by +1 (mod 3)
x0 = Pt[0]
i0 = chi3_index(x0)
i1 = chi3_index(BETA*x0 % p)
print(f"[check] chi3 index of x0={i0}, of beta*x0={i1}, shift={(i1-i0)%3} (expect a fixed nonzero shift)")

print(f"[info] lambda mod 3 = {LAM%3},  n mod 3 = {n%3}")

# ---- MAIN TEST: does public j(P) predict secret d mod 3 ? ----
random.seed(20260813)
N = 12000
# 3x3 contingency  rows=j (public), cols=d mod 3 (secret)
tab = [[0,0,0],[0,0,0],[0,0,0]]
js=[]; ds=[]
none_ct=0
for _ in range(N):
    d = random.randrange(1, n)
    P = pmul(d, G)
    j = chi3_index(P[0])
    if j is None:
        none_ct+=1; continue
    dm = d % 3
    tab[j][dm]+=1
    js.append(j); ds.append(dm)

M=len(js)
print(f"\n[main] usable samples M={M}  (chi3 index undefined on {none_ct})")
print("contingency  rows=j(public)  cols=d mod 3")
for r in range(3):
    print(f"  j={r}: {tab[r]}   (row sum {sum(tab[r])})")
colsum=[sum(tab[r][c] for r in range(3)) for c in range(3)]
print(f"  colsum (d mod 3 marginal): {colsum}")

# Exact chi-square-like statistic via integer expected (kept as Fraction; float only for final display)
def chisq(tab, M):
    rs=[sum(row) for row in tab]; cs=[sum(tab[r][c] for r in range(3)) for c in range(3)]
    s=Fraction(0)
    for r in range(3):
        for c in range(3):
            e=Fraction(rs[r]*cs[c], M)
            if e>0:
                s+=(Fraction(tab[r][c])-e)**2/e
    return s
chi = chisq(tab,M)
print(f"\nchi-square (obs vs independence) = {float(chi):.3f}  (4 dof; ~9.49 is p=0.05)")

# Matched control: permute j labels (destroys any j<->d coupling, preserves marginals)
random.seed(777)
best=0.0; hits=0; R=2000
for _ in range(R):
    jp=js[:]; random.shuffle(jp)
    t2=[[0,0,0],[0,0,0],[0,0,0]]
    for a,b in zip(jp,ds): t2[a][b]+=1
    c2=float(chisq(t2,M))
    if c2>=float(chi): hits+=1
    best=max(best,c2)
print(f"permutation control: {hits}/{R} shuffles reach observed chi ({(hits+1)/(R+1):.4f} exact p); max shuffle chi={best:.2f}")

# also predictability: best single-guess accuracy of d mod 3 from j vs base rate
base = max(colsum)/M
acc = sum(max(tab[r]) for r in range(3))/M
print(f"\nbest-guess accuracy of d mod 3 from j: {acc:.4f}   base rate (guess majority): {base:.4f}")
print(f"info gain over base: {acc-base:+.4f}")
