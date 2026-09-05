#!/usr/bin/env python3
"""
The genuinely Z[omega]-native SCALAR invariant of a key: its cubic & sextic
multiplicative character mod n.  Since Z[omega]/(pi_n) ~= F_n (n prime), omega
acts as lambda (lambda^3=1), so d^((n-1)/3) mod n lands in {1,lambda,lambda^2}
= the image of mu_3.  A creator selecting keys with a Z[omega]-multiplicative
bias (e.g. keys that are cubic residues, i.e. in the image of the norm / a
sub-lattice of the CM order) would show here and NOWHERE in the additive
(d mod 3) or Farey tests.  Exact; matched null; firing control.
"""
import csv, random
N  = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141
LAM= 0x5363AD4CC05C30E0A5261C028812645A122E22EA20816678DF02967C1B23BD72
e3=(N-1)//3; e6=(N-1)//6
cube_roots={pow(LAM,j,N):j for j in range(3)}          # {1:0, lam:1, lam^2:2}
# sextic: zeta6 = a primitive 6th root mod n
def prim6():
    for g in range(2,200):
        z=pow(g,e6,N)
        if pow(z,6,N)==1 and all(pow(z,k,N)!=1 for k in (1,2,3)): return z
    raise RuntimeError
Z6=prim6(); six_roots={pow(Z6,j,N):j for j in range(6)}

def chi3(d): return cube_roots.get(pow(d%N, e3, N))     # 0/1/2 or None(=0 residue)
def chi6(d): return six_roots.get(pow(d%N, e6, N))

def counts(vals,k):
    c=[0]*k
    for v in vals:
        if v is not None: c[v]+=1
    return c
def chisq_stat(c):
    tot=sum(c); k=len(c);
    if tot==0: return 0
    # integer-friendly: sum (k*c_i - tot)^2  (monotone in chi^2, no float threshold)
    return sum((k*ci-tot)**2 for ci in c)

# load solved keys
D=[]
with open('puzzles_verified.csv') as f:
    for row in csv.DictReader(f):
        D.append(int(row['private_key'],16))
print(f"{len(D)} solved keys; testing cubic (mu_3) & sextic multiplicative char mod n")

for name,chi,k in [("cubic chi3 (mu_3)",chi3,3),("sextic chi6 (mu_6)",chi6,6)]:
    obs=counts([chi(d) for d in D],k)
    s_obs=chisq_stat(obs)
    rng=random.Random(999)
    NULL=20000; worse=0
    for _ in range(NULL):
        # matched null: random int of SAME bit-length as each key
        c=counts([chi(rng.randrange(1<<(d.bit_length()-1),1<<d.bit_length()) if d.bit_length()>1 else 1) for d in D],k)
        if chisq_stat(c)>=s_obs: worse+=1
    print(f"\n  {name}: observed class counts {obs}")
    print(f"    dispersion stat={s_obs}; matched-null P(>=obs)={worse/NULL:.4f}  (uniform => ~large p)")

# CONTROL: plant keys that are all CUBIC RESIDUES (chi3==0) -> must fire tiny p
rng=random.Random(7)
planted=[]
while len(planted)<len(D):
    x=rng.randrange(2,N); planted.append(pow(x,3,N))   # guaranteed cubic residue
cc=counts([chi3(d) for d in planted],3)
s_c=chisq_stat(cc); worse=0
for _ in range(20000):
    c=counts([chi3(rng.randrange(1,N)) for _ in D],3)
    if chisq_stat(c)>=s_c: worse+=1
print(f"\n  [CONTROL all-cubic-residue keys] counts {cc}; null P(>=obs)={worse/20000:.5f}  (want ~0)")
