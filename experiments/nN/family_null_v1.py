"""Null tests: do structured families of instants beat random instants of the same number?

On 3,000 sets of the v1 residual of [1,40]: the lonely measure per period; then the rung-selection
rule's instants (q <= 8, flank the least multiple of q) and the top pair's mirror meetings
k/(d6 + d7), each against the same number of uniform random instants and against random numerators
over the same denominators.
"""
import itertools, random, time
from fractions import Fraction as Fr
from math import gcd
_rs = __file__.replace('family_null_v1.py', 'rung_selection_v1.py'); _here = __file__
_s = open(_rs).read(); __file__ = _rs; exec(_s[:_s.index("for top in (30, 40):")])
def lonely(S, t): return all(Fr(1, 8) <= (x * t) % 1 <= Fr(7, 8) for x in S)
random.seed(8)
R = [S for S in itertools.combinations(range(1, 41), 7) if eight_residual(S)]
samp = random.sample(R, 3000)
t0 = time.time()
# 1. lonely measure of each set (exact: total cell length over one period)
exec(open(_here.replace('family_null_v1.py', 'cell_census_v1.py')).read().split('def rung_of')[0].split('_s = open(_rs)')[1].split('\n', 1)[1])
meas = sorted(float(sum(Rr - L for L, *_x, Rr, eR, kR in [(c[0], c[1], c[2], c[3], c[4], c[5]) for c in cells(S)])) for S in samp)
print(f"lonely measure per period: min {meas[0]:.3f}, 1% {meas[30]:.3f}, median {meas[1500]:.3f}")
# 2. families vs random instants of the same size
def rule_instants(S):
    out = []
    for q in range(2, 9):
        mult = [d for d in S if d % q == 0]
        if not mult: continue
        e = min(mult)
        out += [Fr(i, q) + Fr(1, 8 * e) for i in range(q) if gcd(i, q) == 1]
    return out
def mirror_top(S):
    s = sorted(S); m = s[-1] + s[-2]; return [Fr(k, m) for k in range(1, m)]
for name, fam in (("rule (q <= 8, flank = least multiple)", rule_instants), ("top pair mirror k/(d6+d7)", mirror_top)):
    hit = rnd = rndq = 0; sizes = []
    for S in samp:
        F = fam(S); sizes.append(len(F))
        hit += any(lonely(S, t) for t in F)
        rnd += any(lonely(S, Fr(random.randrange(1, 10 ** 6), 10 ** 6)) for _ in F)
        # random rationals with denominators like the family's (same denominators, random numerators)
        rndq += any(lonely(S, Fr(random.randrange(1, t.denominator), t.denominator)) for t in F)
    print(f"{name}: mean size {sum(sizes)/len(sizes):.1f};  family {hit}/3000;  same number of uniform random t {rnd}/3000;  random numerators, same denominators {rndq}/3000")
print(f"({time.time()-t0:.0f}s)")
