#!/usr/bin/env python3
"""
METHOD 5 / Branch 2a: the UNEXAMINED DUAL of every prior test.

Everything so far tested for structure/clustering and found none. The opposite tail --
OVER-UNIFORMITY (repulsion) -- is invisible to those tests: a low-discrepancy generator
(Sobol/Halton/stratified) produces positions that are TOO evenly spread. It passes
KS-uniform (it IS uniform) and its bit-stream can look complex, so nothing we ran can
see it.

Object: normalized positions u_N = (d_N - 2^(N-1)) / 2^(N-1) in [0,1), scaled to exact
integers u~_N = ((d_N - A) << K) // A (K=128; exact, no float). Statistic:
T = sum of squared gaps between sorted positions (incl. the two boundary gaps to 0 and
1). Minimal T <=> perfectly even spread (repulsion); large T <=> clustering. Two-tailed
vs the 100k matched null. Controls: a stratified keyset must fire LOW (repulsion); a
clustered keyset must fire HIGH.
"""
import csv, os, random
from collections import defaultdict
from reset_common import load_solved

K = 128
SCALE = 1 << K
solved = load_solved()
KEYS = sorted(solved)
BITS = {N: solved[N]["bits"] for N in KEYS}

def upos(d, N):
    A = 1 << (N-1)
    return ((d - A) << K) // A            # exact integer in [0, SCALE)

def gapT(positions):
    """sum of squared gaps (incl boundaries 0 and SCALE); exact big int."""
    xs = sorted(positions)
    prev = 0; s = 0
    for x in xs:
        g = x - prev; s += g*g; prev = x
    g = SCALE - prev; s += g*g
    return s

def T_of(dmap):
    return gapT([upos(dmap[N], N) for N in KEYS])

# null pool from 100k (normalized positions by bit-length)
pool = defaultdict(list)
with open(os.path.join(os.path.dirname(__file__),
        "constructed_keys_1to160_100k_exact.csv")) as f:
    for r in csv.DictReader(f):
        pool[int(r["bits"])].append(int(r["d"]))
rng = random.Random(0xD15C)
def null_T():
    ps=[]
    for N in KEYS:
        p = pool.get(BITS[N])
        d = rng.choice(p) if p else rng.randrange(1<<(BITS[N]-1),1<<BITS[N])
        ps.append(upos(d, N))
    return gapT(ps)

B = 8000
print("=== METHOD 5 / Branch 2a: repulsion (over-uniformity) test ===")
print(f"82 normalized positions; null=100k, B={B}; statistic T=sum of squared gaps\n")

nulls = sorted(null_T() for _ in range(B))
def two_tail(T):
    le = sum(1 for t in nulls if t <= T)     # left tail = over-uniform
    ge = sum(1 for t in nulls if t >= T)     # right tail = clustered
    return le/B, ge/B

T_real = T_of({N: solved[N]["d"] for N in KEYS})
p_low, p_high = two_tail(T_real)
# report T as a ratio to the uniform-ideal (n+1 equal gaps) for interpretability
ideal = (SCALE*SCALE)//(len(KEYS)+1)          # T if all gaps equal
print(f"[REAL] T/ideal = {T_real/ideal:.3f}  (1.0=perfectly even, >1 clustered)")
print(f"       p(over-uniform, left) = {p_low:.4f}   p(clustered, right) = {p_high:.4f}\n")

# controls
def strat_row():   # stratified: positions forced onto an even grid
    return {N: (1<<(N-1)) + ((rank*(1<<(N-1)))//len(KEYS)) for rank,N in enumerate(KEYS)}
def clus_row():    # clustered: all positions near 0
    return {N: (1<<(N-1)) + (rng.randrange(0, max(1,(1<<(N-1))//1000))) for N in KEYS}
Ts = T_of(strat_row()); pl,ph = two_tail(Ts)
print(f"[CTRL stratified] T/ideal={Ts/ideal:.3f}  p(left)={pl:.4f} -> {'FIRES low' if pl<0.01 else 'no'}")
Tc = T_of(clus_row()); pl2,ph2 = two_tail(Tc)
print(f"[CTRL clustered]  T/ideal={Tc/ideal:.3f}  p(right)={ph2:.4f} -> {'FIRES high' if ph2<0.01 else 'no'}")

print()
if p_low < 0.05:
    print("  -> REAL positions are OVER-UNIFORM: evidence of a low-discrepancy / stratified")
    print("     generator (invisible to all clustering/structure tests). Investigate which.")
elif p_high < 0.05:
    print("  -> REAL positions are CLUSTERED (should have shown in Method 2; cross-check).")
else:
    print("  -> REAL positions are Poisson-random in spread: neither clustered NOR over-")
    print("     uniform. A stratified/low-discrepancy generator is excluded to this floor;")
    print("     consistent with an unstructured PRNG (control-validated both tails).")
