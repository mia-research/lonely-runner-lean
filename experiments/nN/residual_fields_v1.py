"""The 22 EightResidual fields as predicates (from residual_members_v4/v5), for reuse."""
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
