#!/usr/bin/env python3
"""
METHOD 2 v2: joint residue-clustering of the SET, with a CONTINUOUS maxT statistic so
the multiple-testing correction is not floored by a discrete p (the v1 flaw: 238
moduli x 1/N_ref floor -> even a blatant injection capped at corrected p~0.045).

T(m) = sum_c count_c^2 (exact integer collision count). Per modulus, standardize
against the null pool: z(m) = (T-mean_m)/std_m (a monotone transform ranked against a
matched permutation null -- allowed by the no-float rule). Statistic = maxZ over m.
Corrected p = fraction of null keysets whose maxZ >= the real maxZ. Base-10 roundness
is the m in {10,100,1000,...} special case. Null = 100k, matched by bit-length.
Positive control (all keys == 0 mod 97) must fire decisively.
"""
import csv, os, random
import numpy as np
from collections import defaultdict
from reset_common import load_solved

solved = load_solved()
KEYS = sorted(solved)
BITS = {N: solved[N]["bits"] for N in KEYS}
Dreal = np.array([solved[N]["d"] for N in KEYS], dtype=object)   # exact python ints

MODULI = list(range(2, 513)) + [1000, 10000, 100000, 1000000, 1024, 65536, 631, 149]
MODULI = sorted(set(MODULI))
M = len(MODULI)

pool = defaultdict(list)
with open(os.path.join(os.path.dirname(__file__),
        "constructed_keys_1to160_100k_exact.csv")) as f:
    for r in csv.DictReader(f):
        pool[int(r["bits"])].append(int(r["d"]))
rng = random.Random(0x105E7)
def null_matrix(K):
    rows=[]
    for _ in range(K):
        rows.append([ (rng.choice(pool[BITS[N]]) if pool.get(BITS[N])
                       else rng.randrange(1<<(BITS[N]-1),1<<BITS[N])) for N in KEYS])
    return rows

def Tvec(drow):
    """T(m) for all moduli for one keyset (list of python ints). Exact integer."""
    out=np.empty(M, dtype=np.int64)
    for j,m in enumerate(MODULI):
        res=[int(d % m) for d in drow]
        cnt=np.bincount(np.array(res,dtype=np.int64), minlength=m)
        out[j]=int((cnt.astype(np.int64)**2).sum())
    return out

print("=== METHOD 2 v2: joint clustering, maxT-corrected ===")
print(f"{M} moduli (2..512 + decimal/binary powers); null=100k\n")

N_REF, N_CAL = 4000, 4000
ref = np.stack([Tvec(r) for r in null_matrix(N_REF)])       # (N_REF, M)
mean = ref.mean(axis=0); std = ref.std(axis=0); std[std==0]=1.0
def maxZ(Tv): return float(((Tv - mean)/std).max())
def argmaxZ(Tv):
    z=(Tv-mean)/std; j=int(z.argmax()); return MODULI[j], z[j], int(Tv[j])

cal = np.stack([Tvec(r) for r in null_matrix(N_CAL)])
cal_maxZ = np.array([maxZ(cal[i]) for i in range(N_CAL)])

def corrected_p(Tv):
    z=maxZ(Tv)
    return (int((cal_maxZ >= z).sum())+1)/(N_CAL+1), z

# real
Tr=Tvec(list(Dreal))
p_real,z_real=corrected_p(Tr)
m_r,zr,Tr_at=argmaxZ(Tr)
print(f"[REAL] most-clustered m={m_r} (z={zr:.2f}, T={Tr_at}); maxZ={z_real:.2f}; "
      f"corrected p = {p_real:.4f}")
# top 5 by z
zall=(Tr-mean)/std
order=np.argsort(-zall)[:5]
print("   top moduli by z: " + ", ".join(f"m={MODULI[j]}:z={zall[j]:.2f}" for j in order))

# control
def clustered_row(mstar=97, frac=1.0):
    row=[]
    for N in KEYS:
        A=1<<(BITS[N]-1)
        if random.random()<frac:
            # smallest multiple of mstar that is >= A and < 2A, else fall back random
            q=((A + mstar -1)//mstar)*mstar
            row.append(q if q < 2*A else random.randrange(A,2*A))
        else:
            row.append(random.randrange(A,2*A))
    return row
random.seed(1)
Tc=Tvec(clustered_row(97,1.0))
p_ctrl,_=corrected_p(Tc)
m_c,zc,_=argmaxZ(Tc)
print(f"\n[CTRL all==0 mod 97] detected m={m_c} (z={zc:.2f}); corrected p = {p_ctrl:.4f} "
      f"-> {'FIRES' if p_ctrl<0.01 else 'weak'}")
Tc2=Tvec(clustered_row(97,0.4))
p_ctrl2,_=corrected_p(Tc2)
print(f"[CTRL 40% == 0 mod 97]  corrected p = {p_ctrl2:.4f} -> {'fires' if p_ctrl2<0.05 else 'no'}")

print(f"\nREAL corrected p = {p_real:.4f} -> "
      + ("JOINT CLUSTERING detected" if p_real<0.05 else
         "no joint residue clustering at any scanned modulus (m<=1e6) beyond the "
         "matched null; base-10 (m=10^k) is included and not significant"))
