"""The 2-adic family on the v1 EightResidual: instants A/2^k, A odd, 4 <= k <= K (every odd
multiplier, not only A = 1 mod 8).  Within a 2-adic level {2^v * odd} the odd units mod 2^m act
transitively.  Success is compared with the same number of uniform random instants (density null),
and with the openings-only family (A = 1 mod 8) of the same k."""
import itertools, collections, sys, os, random
from fractions import Fraction
random.seed(2)
N = int(sys.argv[1]) if len(sys.argv) > 1 else 30
exec(open(os.path.join(os.path.dirname(__file__) or ".", "eight_residual_count_v1.py")).read().split("t0 = time.time()")[0])
def lonely_at(S, num, den):  # instant num/den
    return all(den <= 8 * ((d * num) % den) <= 7 * den for d in S)
def fam(K, only1=False):
    out = []
    for k in range(4, K + 1):
        for A in range(1, 2 ** k, 2):
            if only1 and A % 8 != 1: continue
            out.append((A, 2 ** k))
    return out
def lonely_real(S, t):
    return all(min((d * t) % 1, 1 - (d * t) % 1) >= 1 / 8 for d in S)
res = collections.Counter(); least = collections.Counter(); n = 0
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
    n += 1
    for K in (5, 6, 7):
        F = fam(K); F1 = fam(K, True)
        res[(K, 'all odd A')] += any(lonely_at(S, A, D) for A, D in F)
        res[(K, 'A = 1 mod 8')] += any(lonely_at(S, A, D) for A, D in F1)
        res[(K, f'null: {len(F)} uniform t')] += any(lonely_real(S, random.random()) for _ in F)
    k = next((k for k in range(4, 12) if any(lonely_at(S, A, 2 ** k) for A in range(1, 2 ** k, 2))), None)
    least[k] += 1
print(f"N = {N}: v1 residual {n} sets")
for key in sorted(res): print("  ", key, res[key])
print("  least k with a lonely A/2^k (A odd):", sorted(least.items(), key=lambda x: (x[0] is None, x[0])))
