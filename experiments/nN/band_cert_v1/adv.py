"""Adversarial search: maximise the least clear R over shapes in the band.
Search moves use random rationals; every objective value is computed EXACTLY (Fraction)."""
import sys, random
from fractions import Fraction as F
from core import clear_set
from multiprocessing import Pool

DEN = 10**6

def least(s, Rhi=F(40)):
    S = clear_set(s, F(1), Rhi)
    return S[0][0] if S else None

def rnd_shape(rng):
    s6 = F(rng.randint(7 * DEN + 1, 9 * DEN - 1), DEN)
    xs = sorted(F(rng.randint(DEN + 1, int(s6 * DEN) - 1), DEN) for _ in range(5))
    return [F(1)] + xs + [s6]

def valid(s):
    return all(s[i] < s[i + 1] for i in range(6)) and 7 < s[6] < 9 and s[0] == 1

def climb(seed, iters=4000):
    rng = random.Random(seed)
    best = rnd_shape(rng); bv = least(best)
    step = F(1, 2)
    for it in range(iters):
        cand = list(best)
        for i in rng.sample(range(1, 7), rng.randint(1, 3)):
            d = F(rng.randint(-10**4, 10**4), 10**4) * step
            cand[i] = cand[i] + d
        cand[1:6] = sorted(cand[1:6])
        if not valid(cand):
            continue
        v = least(cand)
        if v is None:
            return ("NO CLEAR R <= 40", cand)
        if v >= bv:
            best, bv = cand, v
        if it % 500 == 499:
            step /= 2
    return (bv, best)

if __name__ == "__main__":
    n = int(sys.argv[1]); base = int(sys.argv[2])
    with Pool(10) as p:
        res = p.map(climb, range(base, base + n))
    res = [r for r in res]
    bad = [r for r in res if isinstance(r[0], str)]
    print("restarts:", n, " failures (no clear R<=40):", len(bad))
    res = [r for r in res if not isinstance(r[0], str)]
    res.sort(key=lambda r: r[0], reverse=True)
    print("max least-clear R found:", float(res[0][0]), "exact", res[0][0])
    for v, s in res[:8]:
        print(round(float(v), 6), [str(x) for x in s], " >15:" , v > 15)
    print("count with least-clear > 15:", sum(1 for v, s in res if v > 15))
    print("count with least-clear > 12:", sum(1 for v, s in res if v > 12))

def witness_all(res):
    from walk import Cert
    from core import is_clear
    C = Cert("cert15.pkl"); fails = 0
    for v, s in res:
        R = C.witness(s)
        if not (R is not None and is_clear(s, R) and (1 <= R <= 7 or 9 <= R <= 15)):
            fails += 1
    return fails
