"""Flank coordinates. Threshold 1/n. Fix a flank runner e; its openings are t_k = (k + 1/n)/d_e, k = 0, 1, 2, ... Every other
runner j reads rho = d_j/d_e (scale-free). At t_k, j sits at rho·(k + 1/n) laps; in the way iff that is within 1/n of an
integer (strict). With rho = A + f (A integer, f in [0,1)): position mod 1 = frac(k·f) + rho/n mod 1, so
  f = 0: never in the way unless rho ≡ 0 (mod n) (then always: the dead lattice);
  f > 0: in the way exactly when frac(k·f) lies in the open arc of length 2/n centred at −rho/n (mod 1).
(1) Check the arc form against direct evaluation from speeds. (2) Enumerate, for rational fractional parts b/c, which pairs
and triples of runners block every opening of a flank (all k), by their denominators, at n = 5 and n = 8."""
from fractions import Fraction as F
import math, random, itertools
from collections import Counter
def cdist(x):
    f = x - math.floor(x); return min(f, 1 - f)
def arc_in_way(rho, k, n):
    A = math.floor(rho); f = rho - A
    if f == 0: return (rho % n) == 0
    x = (k * f) % 1; centre = (-rho / n) % 1
    d = min((x - centre) % 1, (centre - x) % 1)
    return d < F(1, n)
# (1)
rng = random.Random(3); checks = bad = 0
for n in (5, 8):
    for _ in range(400):
        v = sorted({F(rng.randint(0, 3000), rng.choice([1, 2, 3, 5, 7, 12])) for _ in range(n)})
        if len(v) < n: continue
        i = rng.randrange(n); ds = [abs(x - v[i]) for x in v if x != v[i]]
        e = rng.choice(ds)
        for k in range(0, 40):
            t = (k + F(1, n)) / e
            for d in ds:
                if d == e: continue
                checks += 1
                if (cdist(d * t) < F(1, n)) != arc_in_way(d / e, k, n): bad += 1
print(f'(1) arc form vs direct evaluation: {checks} checks, {bad} disagreements')
# (2)
def blocked_residues(A, b, c, n):
    rho = A + F(b, c)
    return frozenset(k for k in range(c) if arc_in_way(rho, k, n))
for n, Cpair, Ctri in ((5, 12, 8), (8, 12, 8)):
    types = []
    for c in range(2, Cpair + 1):
        for b in range(1, c):
            if math.gcd(b, c) != 1: continue
            for A in range(n):
                S = blocked_residues(A, b, c, n)
                if S: types.append((c, A, b, S))
    def shadows(group):
        N = 1
        for c, *_ in group: N = N * c // math.gcd(N, c)
        return all(any((k % c) in S for c, A, b, S in group) for k in range(N))
    pair_sig = Counter(); tri_sig = Counter()
    for g in itertools.combinations(types, 2):
        if sum(len(S) / c for c, A, b, S in g) < 1: continue
        if shadows(g): pair_sig[tuple(sorted(c for c, *_ in g))] += 1
    small = [t for t in types if t[0] <= Ctri]
    for g in itertools.combinations(small, 3):
        if sum(len(S) / c for c, A, b, S in g) < 1: continue
        if any(shadows(p) for p in itertools.combinations(g, 2)): continue
        if shadows(g): tri_sig[tuple(sorted(c for c, *_ in g))] += 1
    beta = {c: max(len(S) for cc, A, b, S in types if cc == c) / c for c in range(2, Cpair + 1)}
    print(f'(2) n={n}: largest share of openings one runner blocks, by denominator c: {{{", ".join(f"{c}: {F(beta[c]).limit_denominator(20)}" for c in beta)}}}')
    print(f'    pairs that block every opening (denominators up to {Cpair}), by denominator pair: {dict(pair_sig)}')
    print(f'    triples that block every opening with no blocking pair inside (denominators up to {Ctri}): {dict(tri_sig)}')
