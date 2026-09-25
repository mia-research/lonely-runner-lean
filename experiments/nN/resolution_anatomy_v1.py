"""Anatomy of the least clearing resolution on the v1 EightResidual (7-subsets of [1,N]).
Resolution D clears S at index j < D when every reading d*(8j+1) mod 8D lies in [D, 7D]
(the instant (8j+1)/(8D); ResolutionClears8 in OrderEightCasesN).  For each set: least D,
D = 2^a * o; at that rung the number of openings j < D each disparity blocks (its cost), the
plain budget (sum of costs < D) versus overlap; who blocks (rank, residue mod 8); for odd o > 1,
whether the non-multiples of 8 fall in one coset of a proper subgroup of (Z/o)^x (the analogue of
Barajas-Serra's {1,2,4}); and at the clearing instant each runner's offset from its nearest
vertex k/8 of the regular 8-gon."""
import itertools, collections, sys, os, time, random
random.seed(1)
from math import gcd
N = int(sys.argv[1]) if len(sys.argv) > 1 else 30
exec(open(os.path.join(os.path.dirname(__file__) or ".", "eight_residual_count_v1.py")).read().split("t0 = time.time()")[0])

def blocked(d, D, j):
    r = (d * (8 * j + 1)) % (8 * D)
    return not (D <= r <= 7 * D)

def least_D(S, cap=64):
    for D in range(1, cap + 1):
        for j in range(D):
            if not any(blocked(d, D, j) for d in S): return D, j
    return None, None

def units(o): return [u for u in range(1, o) if gcd(u, o) == 1]
def subgroup_gen(g, o):
    H, x = set(), 1
    while True:
        H.add(x); x = x * g % o
        if x == 1: return frozenset(H)
def in_one_coset(res, o):
    U = units(o)
    if any(gcd(r, o) != 1 for r in res): return None          # a non-unit residue
    subs = {subgroup_gen(g, o) for g in U}
    proper = [H for H in subs if len(H) < len(U)]
    for H in sorted(proper, key=len):
        r0 = next(iter(res)); inv = pow(r0, -1, o)
        if all((r * inv) % o in H for r in res): return len(H)
    return len(U)

t0 = time.time()
C = collections.Counter(); split = collections.Counter(); budget = collections.Counter()
blk_rank = collections.Counter(); blk_mod8 = collections.Counter(); coset = collections.Counter()
off = collections.Counter(); nsets = 0
for S in itertools.combinations(range(1, N + 1), 7):
    if not any(d % 2 for d in S): continue
    if not all(any(d % q == 0 for d in S) for q in (5, 6, 7, 8)): continue
    if not max(S) > 7 * min(S): continue
    if sum(4 if d % 8 == 4 else 2 for d in S if d % 8) < 8: continue
    if any(free_flank8(S, e) for e in S if e % 8 == 0): continue
    if shifted(S): continue
    s = sorted(S)
    if s[-1] > 7 * s[-2]: continue
    if first_lap(S) or minus_seven(S): continue
    nsets += 1
    D, j = least_D(S)
    C[D] += 1
    if D is None: continue
    a = (D & -D).bit_length() - 1; o = D >> a
    split[(a, o)] += 1
    cost = {d: sum(blocked(d, D, jj) for jj in range(D)) for d in S}
    budget['plain budget holds' if sum(cost.values()) < D else 'needs overlap'] += 1
    # blockers of the other openings at this rung
    for jj in range(D):
        if jj == j: continue
        for d in S:
            if blocked(d, D, jj):
                blk_rank[s.index(d) + 1] += 1; blk_mod8[d % 8] += 1
    if o > 1:
        res = {d % o for d in S if d % 8 and d % o}
        if res and all(gcd(r, o) == 1 for r in res):
            U = units(o); k = len(res)
            hit = in_one_coset(res, o) < len(U)
            coset[(o, 'proper coset' if hit else 'no proper coset')] += 1
            # null: k distinct random units of Z/o
            nul = 0
            for _ in range(20):
                rr = set(random.sample(U, min(k, len(U))))
                nul += in_one_coset(rr, o) < len(U)
            coset[(o, 'null rate x20')] += nul
        else:
            coset[(o, 'a non-unit or no residue')] += 1
    A = 8 * j + 1
    for d in S:
        x = (d * A) % (8 * D) / (8 * D)          # reading in [0,1)
        off[round(abs(x * 8 - round(x * 8)), 2)] += 1
print(f"N = {N}: v1 residual {nsets} sets  ({time.time()-t0:.0f}s)")
print("least clearing D:", sorted(C.items(), key=lambda x: (x[0] is None, x[0])))
print("D = 2^a * o, (a, o):", sorted(split.items()))
print("at the least D:", dict(budget))
print("blocker rank (1 = least) over the other openings:", sorted(blk_rank.items()))
print("blocker residue mod 8:", sorted(blk_mod8.items()))
print("odd part o > 1: non-multiples of 8 (units mod o) in a proper coset, against a null of the same count (x20):")
for o in sorted({k[0] for k in coset}): print("   o =", o, {k[1]: v for k, v in coset.items() if k[0] == o})
tot = sum(off.values())
print("offset from nearest vertex k/8 (in eighths) at the clearing instant: exactly 0:", off[0.0], "of", tot,
      "; <= 0.25:", sum(v for k, v in off.items() if k <= 0.25), "; max:", max(off))
