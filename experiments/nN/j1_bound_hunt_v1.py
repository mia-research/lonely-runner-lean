"""
The framework's proof, item 1, largest block: j = 1.

Exactly one difference is divisible by 8g. At the gcd gap that one difference is dead and
every other is clear -- one blocker, nothing else wrong. The question the framework's proof
has to answer is how far the gap must rise before that one blocker moves off the lap line
without pushing anyone else into the forbidden octants.

Random sampling says the answer is small: over 18,768 j = 1 runners the first clearing gap
never exceeded 10, and {2g, 3g, 5g, 7g} covered 98.7%.

This anneals to MAXIMISE the first clearing gap, on j = 1 only. If a determined search
cannot push it far, the bound is worth stating and proving.

Exact integers; candidates a coprime to 8; no window, no restriction to a = 1 mod 8.
"""
import random, sys
from math import gcd

def g_of(ds):
    g = 0
    for e in ds:
        g = gcd(g, e)
    return g

def clears(ds, D):
    for a in range(1, 8 * D + 1, 2):
        if all(D <= (a * e) % (8 * D) <= 7 * D for e in ds):
            return a
    return None

def first_gap(ds, Dmax=400):
    for D in range(1, Dmax + 1):
        if clears(ds, D) is not None:
            return D
    return None

def is_j1(ds):
    g = g_of(ds)
    return sum(1 for e in ds if (e // g) % 8 == 0) == 1

def anneal(rng, hi, iters, restarts):
    best = (0, None)
    for _ in range(restarts):
        while True:
            ds = sorted(rng.randint(1, hi) for _ in range(7))
            if is_j1(ds):
                break
        cur = first_gap(ds) or 0
        for _ in range(iters):
            j = rng.randrange(7)
            old = ds[j]
            ds[j] = max(1, min(hi, old + rng.choice([-7, -3, -1, 1, 3, 7])))
            if not is_j1(ds):
                ds[j] = old
                continue
            new = first_gap(ds) or 0
            if new >= cur:
                cur = new
            else:
                ds[j] = old
            if cur > best[0]:
                best = (cur, sorted(ds))
    return best

if __name__ == "__main__":
    rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 90210)
    print("annealing to maximise the first clearing gap, on j = 1 runners\n")
    print(f"{'difference bound':>18} {'largest first gap found':>25}")
    print("-" * 46)
    for hi in (60, 300, 2000, 20000):
        D, ds = anneal(rng, hi, iters=900, restarts=18)
        print(f"{hi:>18} {D:>25}")
        print(f"      at {ds}")
