"""E117: residual members under the current fields, read at the least live lattice as grid + deviation, and
through the cascade.  Construction as residual_members_v4 (largest reading d1 = 8*lcm(1..64)*u, the other six
hill-climbed in (d1/8.9, d1)); added fields: fast pair, block split, one free.  Exact integer arithmetic.
Per member: L0 (least live lattice); at L0 the grid part (multiples of L0, residues of d/L0 mod 8) and the
deviation (non-multiples); whether L0 clears; the cascade landing (e, K), R* = 8 d_min t*."""
exec(open('residual_members_v4.py').read().split("t0 = time.time()")[0])
from fractions import Fraction as F
from math import floor
def fast_pair(S):
    S = sorted(S); a, b = S[-2], S[-1]
    return all(9 * c <= a for c in S[:-2])
def block_split(S):   # some block F with common factor g >= 28 * every other reading
    S = sorted(S)
    for r in range(1, 7):
        for Fb in itertools.combinations(S, r):
            g = reduce(gcd, Fb); rest = [c for c in S if c not in Fb]
            if rest and all(28 * c <= g for c in rest): return True
    return False
def one_free(S):
    return any((lambda g: g >= 2 and x % g)(reduce(gcd, [d for d in S if d != x])) for x in S)
import itertools
FIELDS += [("fast pair", lambda S: not fast_pair(S)), ("block split", lambda S: not block_split(S)),
           ("one free", lambda S: not one_free(S))]
t0 = time.time(); found = []
for r in range(400):
    d1 = L * rnd.randrange(1, 20); lo = int(d1 / 8.9) + 1
    others = [rnd.randrange(lo, d1) for _ in range(6)]
    S = tuple(sorted([d1] + others)); sc = score(S)
    for step in range(300):
        o = list(others); i = rnd.randrange(6)
        base = rnd.randrange(lo, d1); mod = rnd.choice((8, 24, 40))
        o[i] = base - base % mod + rnd.randrange(mod)
        if not (lo <= o[i] <= d1): continue
        T = tuple(sorted([d1] + o)); s2 = score(T)
        if s2 >= sc: others, S, sc = o, T, s2
        if sc == len(FIELDS): break
    if sc == len(FIELDS): found.append(S)
print(f"{time.time() - t0:.0f}s, 400 restarts")

E8 = F(1, 8)
def nd(x):
    x = x % 1
    return min(x, 1 - x)
def cascade(T):
    t = F(1, 8 * min(T)); n = 0
    while True:
        way = [d for d in T if nd(d * t) < E8]
        if not way: return t, n
        t = max((F(floor(d * t - E8) + 1) + E8) / d for d in way); n += 1
def dead(S, D): return any(d % (8 * D) == 0 for d in S)
print("members with all current fields:", len(found))
for S in found:
    L0 = next(D for D in itertools.count(1) if not dead(S, D))
    grid = [d // L0 % 8 for d in S if d % L0 == 0]; dev = [d for d in S if d % L0]
    js = [j for j in range(L0) if clears(S, L0, 8 * j + 1)]
    t, n = cascade(S)
    lands = [(i, (e * t - E8)) for i, e in enumerate(sorted(S)) if (e * t - E8).denominator == 1]
    i, K = lands[0]
    print(f"  L0={L0}: grid part {len(grid)} (d/L0 mod 8 {grid}), deviation {len(dev)}; L0 clears at {len(js)} of {L0} "
          f"j; cascade {n} moves, flank = reading #{i+1} of 7, lap {K}, R* = {float(8*min(S)*t):.3f}, spread {max(S)/min(S):.2f}")
from collections import Counter
summ = Counter()
for S in found:
    t, n = cascade(S); Ss = sorted(S)
    i, K = next((i, e * t - E8) for i, e in enumerate(Ss) if (e * t - E8).denominator == 1)
    summ[('lap %d' % K, 'flank is the largest' if i == 6 else 'flank is a middle reading' if i > 0 else 'flank is the least')] += 1
    summ['bound blocked by the largest'] += nd(Ss[-1] * F(1, 8 * Ss[0])) < E8
print("summary over", len(found), "members:"); [print("  ", k, v) for k, v in sorted(summ.items(), key=str)]
