"""Follow-up to pair_moduli_v1: the two dichotomies it suggests, on [1,40] exhaustively and on
random residual sets of [1,60] and [1,100].

  D1: some q <= 8 certifies (rung_selection rule)  OR  the largest flank has a lonely opening.
  D2: some q <= 8 certifies  OR  the mirror of the top pair works: some k/q lonely with q | a + b,
      (a, b) the two largest (at t = k/(a+b) the two largest read symmetrically, ||a t|| = ||b t||).
Also: which [1,40] residual sets fail the top-pair-sum test, and the one failing sum, difference
and proper divisor of d_max together.
"""
import itertools, random, time
from collections import Counter
_rs = __file__.replace('pair_moduli_v2.py', 'rung_selection_v1.py')
_s = open(_rs).read(); __file__ = _rs; exec(_s[:_s.index("for top in (30, 40):")])

def largest_flank_ok(S):
    D = max(S)
    return any(all(D <= d * (8 * j + 1) % (8 * D) <= 7 * D for d in S) for j in range(D))
def lattice_ok(S, q):
    return any(all(q <= 8 * (d * k % q) <= 7 * q for d in S) for k in range(1, q))
def divisors(n): return [q for q in range(2, n + 1) if n % q == 0]
def small_q(S): return any(rule(S, q, free_exact) for q in range(2, 9))
def mirror_top(S):
    b, a = sorted(S, reverse=True)[:2]
    return any(lattice_ok(S, q) or rule(S, q, free_exact) for q in divisors(a + b))
def mirror_top_lattice_full(S):
    b, a = sorted(S, reverse=True)[:2]
    return lattice_ok(S, a + b)

t0 = time.time()
R = [S for S in itertools.combinations(range(1, 41), 7) if eight_residual(S)]
sumfail = [S for S in R if not mirror_top(S)]
print(f"[1,40]: {len(R)} residual; top-pair sum fails on {len(sumfail)}: {sumfail}")
print(f"   of those, certified by q <= 8: {sum(small_q(S) for S in sumfail)}")
for S in sumfail:
    b, a = sorted(S, reverse=True)[:2]
    if not any(rule(S, q, free_exact) for q in divisors(b) if q < b) and \
       not any(lattice_ok(S, q) or rule(S, q, free_exact) for q in divisors(b - a)):
        print("   fails sum, difference and proper divisor of d_max:", S, "q<=8:", small_q(S), "largest flank:", largest_flank_ok(S))
c = Counter((small_q(S), largest_flank_ok(S), mirror_top_lattice_full(S)) for S in R)
print("   (q<=8, largest flank, lattice at k/(a+b) exactly):", dict(c))
print(f"   ({time.time()-t0:.0f}s)")

random.seed(7)
for top, want in ((60, 3000), (100, 2000)):
    t1 = time.time(); got = []; tries = 0
    while len(got) < want:
        S = tuple(sorted(random.sample(range(1, top + 1), 7))); tries += 1
        if eight_residual(S): got.append(S)
    c = Counter((small_q(S), largest_flank_ok(S), mirror_top(S)) for S in got)
    d1 = [S for S in got if not small_q(S) and not largest_flank_ok(S)]
    d2 = [S for S in got if not small_q(S) and not mirror_top(S)]
    print(f"[1,{top}] random residual sets {len(got)} (of {tries} drawn): (q<=8, largest flank, top-pair sum) {dict(c)}")
    print(f"   D1 fails: {len(d1)} {d1[:5]}; D2 fails: {len(d2)} {d2[:5]}  ({time.time()-t1:.0f}s)")
