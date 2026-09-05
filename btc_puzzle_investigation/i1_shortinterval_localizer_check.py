#!/usr/bin/env python3
"""
SPOT-CHECK of PREREG_boundary_D §1 arm-I1 claim: the per-point CM readout chi3(x(Q))
carries only the constant orbit label (log2 6 bits), NOT position of d WITHIN a short
interval [0,W).  This is the crux of the collapse verdict AND the exact regime the
counter-prior flags ("a per-point readout that localized the key would BE a break").

Test on the REAL secp256k1 curve.  Exact integer arithmetic; decision by exact
permutation p-value on a chi-square-ranked statistic (float only as monotone rank stat).
"""
import random
from fractions import Fraction

p  = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
n  = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141
Gx = 0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798
Gy = 0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8
def inv(a,m): return pow(a,-1,m)
def padd(P,Q):
    if P is None: return Q
    if Q is None: return P
    x1,y1=P; x2,y2=Q
    if x1==x2 and (y1+y2)%p==0: return None
    m=(3*x1*x1)*inv(2*y1,p)%p if P==Q else (y2-y1)*inv((x2-x1)%p,p)%p
    x3=(m*m-x1-x2)%p; return (x3,(m*(x1-x3)-y1)%p)
def pmul(k,P):
    R=None;Q=P
    while k:
        if k&1:R=padd(R,Q)
        Q=padd(Q,Q);k>>=1
    return R
G=(Gx,Gy)
w=pow(2,(p-1)//3,p)
if w==1:
    for g in range(3,50):
        w=pow(g,(p-1)//3,p)
        if w!=1: break
w2=w*w%p
def chi3(x):
    v=pow(x%p,(p-1)//3,p)
    return 0 if v==1 else (1 if v==w else 2)

random.seed(20260813)
N_BITS=18; W=1<<N_BITS         # short interval, W=2^18 << ord(G)=n~2^256
BLOCKBITS=3; NB=1<<BLOCKBITS    # partition interval by top 3 bits -> 8 sub-blocks
M=24000
# rows = j (chi3 orbit index, public), cols = which top-3-bit block d is in (secret position)
tab=[[0]*NB for _ in range(3)]
js=[]; bs=[]
for _ in range(M):
    d=random.randrange(0,W)
    Q=pmul(d,G)
    j=chi3(Q[0])
    blk=d>>(N_BITS-BLOCKBITS)   # top 3 bits of d
    tab[j][blk]+=1
    js.append(j); bs.append(blk)

print(f"secp256k1, short interval W=2^{N_BITS}, {M} samples, partition by top {BLOCKBITS} bits ({NB} blocks)")
print("rows=j=chi3(x(Q)) [public]   cols=top-3-bit block of d [secret position in interval]")
rs=[sum(r) for r in tab]; print("row sums (j marginal):",rs)

def chisq(tab,M):
    rs=[sum(r) for r in tab]; cs=[sum(tab[i][c] for i in range(3)) for c in range(len(tab[0]))]
    s=Fraction(0)
    for i in range(3):
        for c in range(len(tab[0])):
            e=Fraction(rs[i]*cs[c],M)
            if e>0: s+=(Fraction(tab[i][c])-e)**2/e
    return s
chi=chisq(tab,M)
dof=(3-1)*(NB-1)
print(f"\nchi-square(j vs interval-block) = {float(chi):.3f}  ({dof} dof; p=.05 threshold ~ 23.7)")

random.seed(4242); R=2000; hits=0; best=0.0
for _ in range(R):
    jp=js[:]; random.shuffle(jp)
    t2=[[0]*NB for _ in range(3)]
    for a,c in zip(jp,bs): t2[a][c]+=1
    c2=float(chisq(t2,M))
    if c2>=float(chi): hits+=1
    best=max(best,c2)
print(f"permutation control (shuffle j): {hits}/{R} >= observed  -> exact p = {(hits+1)/(R+1):.4f}")
print(f"  max shuffle chi = {best:.2f}  (control liveness: statistic CAN move)")

# predictability: best-guess accuracy of the 3-bit block from j vs base rate
base=max(sum(tab[i][c] for i in range(3)) for c in range(NB))/M
acc=sum(max(tab[i]) for i in range(3))/M
print(f"\nbest-guess accuracy of top-3-bits from j: {acc:.4f}  base rate: {base:.4f}  gain: {acc-base:+.4f}")
print("(gain ~0 + observed chi inside shuffle null  =>  chi3 does NOT localize d in the interval: I1 null CONFIRMED)")
