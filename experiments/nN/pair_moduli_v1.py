"""Pair moduli and the largest flank, on the order-eight residual of [1,40].

Two tests, run from the Prop 11 session while the n=8 session tests the dilation cost.

(A) The largest flank (DoorLargestFlank, REFUTED at n = 8 in DoorsN).  By Theorem 10 the largest
    disparity D has a lonely opening iff some j < D has d*(8j+1) mod 8D in [D, 7D] for every d.
    Where are its failures: inside the v1 residual, and inside the 28 sets no q <= 8 certifies?

(B) Pair moduli.  BHK's order six works at the meeting times k/(v3 - v2) (a pair difference); the
    framework's mirror merge works at k/(a + b) (a pair sum).  For each set, and each pair (a, b),
    the candidate moduli are the divisors q >= 2 of b - a and of a + b.  Two readings:
      lattice  -- some t = k/q is lonely (every d has d*k mod q in [q/8, 7q/8], exact: 8*r in [q, 7q]);
      rule     -- the rung-selection rule at q (rung_selection_v1), which needs a multiple of q in S.
    Reported: coverage of the 28 hard sets and of the whole residual, by the rank of the pair.
"""
import itertools, time
from collections import Counter
_rs = __file__.replace('pair_moduli_v1.py', 'rung_selection_v1.py')
_s = open(_rs).read(); __file__ = _rs; exec(_s[:_s.index("for top in (30, 40):")])

def largest_flank_ok(S):
    D = max(S)
    return any(all(D <= d * (8 * j + 1) % (8 * D) <= 7 * D for d in S) for j in range(D))

def lattice_ok(S, q):
    return any(all(q <= 8 * (d * k % q) <= 7 * q for d in S) for k in range(1, q))

def divisors(n): return [q for q in range(2, n + 1) if n % q == 0]

t0 = time.time()
R = [S for S in itertools.combinations(range(1, 41), 7) if eight_residual(S)]
hard = [S for S in R if not any(rule(S, q, free_exact) for q in range(2, 9))]
print(f"[1,40] residual v1: {len(R)} sets; no q <= 8: {len(hard)}  ({time.time()-t0:.0f}s)")

# (A)
lf_fail = [S for S in R if not largest_flank_ok(S)]
hard_lf = [S for S in hard if not largest_flank_ok(S)]
print(f"(A) largest flank has no lonely opening: {len(lf_fail)} of {len(R)} residual sets; "
      f"of the {len(hard)} hard sets: {len(hard_lf)}")
print("    residual examples:", lf_fail[:8])
print("    hard-set examples:", hard_lf[:8])
qle8 = Counter(any(rule(S, q, free_exact) for q in range(2, 9)) for S in lf_fail)
print(f"    of the largest-flank failures, certified by some q <= 8: {qle8[True]}, not: {qle8[False]}")

# (B)
def pair_report(sets, label):
    kinds = Counter(); first = Counter(); none = []
    for S in sets:
        srt = sorted(S, reverse=True)
        pairs = [(srt[i], srt[j]) for i in range(7) for j in range(i + 1, 7)]
        hit = None
        for rank, (b, a) in enumerate(pairs):
            for kind, m in (('diff', b - a), ('sum', a + b)):
                for q in divisors(m):
                    for how, ok in (('lattice', lattice_ok(S, q)), ('rule', rule(S, q, free_exact))):
                        if ok:
                            kinds[(kind, how)] += 1
                            if hit is None: hit = (rank, kind, how, q)
        if hit is None: none.append(S)
        else: first[hit[0]] += 1
    top = sum(v for r, v in first.items() if r == 0)
    print(f"(B) {label}: {len(sets)} sets; some pair modulus works: {len(sets) - len(none)}; "
          f"first working pair is the top pair (d_max, d_max-1): {top}; "
          f"rank of first working pair {sorted(first.items())[:8]}; none: {len(none)} {none[:5]}")
    return none

def top_pair_only(sets):
    c = Counter()
    for S in sets:
        srt = sorted(S, reverse=True); b, a = srt[0], srt[1]
        d = any(lattice_ok(S, q) or rule(S, q, free_exact) for q in divisors(b - a))
        s = any(lattice_ok(S, q) or rule(S, q, free_exact) for q in divisors(a + b))
        m = any(rule(S, q, free_exact) for q in divisors(b) if q < b)
        c[(d, s, m)] += 1
    return c

pair_report(hard, "the hard sets")
print("    per hard set (top pair diff works, top pair sum works, proper divisor of d_max works):")
for S in hard:
    srt = sorted(S, reverse=True); b, a = srt[0], srt[1]
    D = [q for q in divisors(b - a) if lattice_ok(S, q) or rule(S, q, free_exact)]
    Su = [q for q in divisors(a + b) if lattice_ok(S, q) or rule(S, q, free_exact)]
    M = [q for q in divisors(b) if q < b and rule(S, q, free_exact)]
    print(f"    {S}: diff {b-a} -> {D}; sum {a+b} -> {Su}; d_max {b} -> {M}; largest flank {largest_flank_ok(S)}")
print("(B) whole residual, top pair only (diff, sum, proper divisor of d_max):", dict(top_pair_only(R)))
print(f"total {time.time()-t0:.0f}s")
