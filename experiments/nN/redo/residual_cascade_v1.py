"""Owner: follow the cascade on the residual sets.  A set T of 7 distinct positive whole-number readings (the slowest
runner of an arrangement of eight moving runners) is RESIDUAL when every modulus q = 2..8 divides some reading; otherwise
the grid at modulus q (t = 1/q) isolates it at once (every reading at a nonzero multiple of 1/q, at least 1/8 away).
For each residual set with readings <= 40: the cascade's isolation t* = (8k + 1)/(8e) (e the pinning reading), so the
modulus is N = 8e and the multiplier a = 8k + 1; each reading's residue a*d mod 8e (clear iff in [e, 7e]); which
readings are whole multiples of e (their residue is fixed: d/e mod 8, times e) and which are not.  Exact."""
import itertools
from fractions import Fraction as F
from math import floor, gcd
from collections import Counter
from arrangement_lib import nd

def residual(T):
    return all(any(d % q == 0 for d in T) for q in range(2, 9))

def cascade_flank(ds):
    t = F(1, 8 * ds[0]); e, k = ds[0], 0; moves = 0
    while True:
        way = [d for d in ds if nd(d * t) < F(1, 8)]
        if not way: return t, e, k, moves
        cand = {d: (F(floor(d * t - F(1, 8)) + 1) + F(1, 8)) / d for d in way}
        e = max(cand, key=lambda x: cand[x]); t = cand[e]; k = floor(e * t); moves += 1

if __name__ == '__main__':
    res = [T for T in itertools.combinations(range(1, 41), 7) if residual(T)]
    print(f"residual sets with readings <= 40: {len(res)} (of {sum(1 for _ in itertools.combinations(range(1, 41), 7))})")
    ek = Counter(); flank_rank = Counter(); movers = Counter(); kk = Counter(); ex = []
    for T in res:
        t, e, k, mv = cascade_flank(list(T))
        assert t == F(8 * k + 1, 8 * e)
        a, N = 8 * k + 1, 8 * e
        resid = [(a * d) % N for d in T]
        assert all(e <= r <= 7 * e for r in resid)
        mult = [d for d in T if d % e == 0]
        flank_rank[T.index(e)] += 1; kk[min(k, 5)] += 1; movers[7 - len(mult)] += 1
        if len(ex) < 12 and k >= 1: ex.append((T, e, k, [F(r, e) for r in resid], mult))
    print(f"  the pinning reading e by rank (0 = smallest): {sorted(flank_rank.items())}")
    print(f"  the lap k (multiplier 8k+1): {sorted(kk.items())}")
    print(f"  readings that are NOT whole multiples of e (movers): {sorted(movers.items())}")
    for T, e, k, r, mult in ex:
        print(f"  T {T}: modulus 8e = {8 * e}, multiplier {8 * k + 1}; residues / e {[round(float(x), 3) for x in r]}; multiples of e {mult}")
