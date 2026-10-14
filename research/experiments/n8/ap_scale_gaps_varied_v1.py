import random
from math import gcd
from functools import reduce
from itertools import combinations
from collections import Counter
def clear_int(e, r, N):
    R = (e*r) % N; return N <= 8*R <= 7*N
def G(V): return reduce(gcd, [b-a for a, b in combinations(V, 2)])
def diffs(V, i): return [abs(v-V[i]) for j, v in enumerate(V) if j != i]
def works(V, i, D):              # some odd r in one period clears every difference at t = r/(8D); D a multiple of g
    ds = diffs(V, i); g = G(V); N = 8*D
    period = 8*D//g
    return [r for r in range(1, period, 2) if all(clear_int(e, r, N) for e in ds)]
def L0(V, i):
    g = G(V); ds = diffs(V, i)
    return next(s for s in range(1, 10**6) if not any(e % (8*s*g) == 0 for e in ds))
cls = lambda x: min(x % 16, (-x) % 16)

# 1. how many of the earlier scale-2 runners had g > 1
rng = random.Random(7)
arrs = [c for c in combinations(range(1, 21), 8) if reduce(gcd, c) == 1] + \
       [tuple(sorted(rng.sample(range(1, 2001), 8))) for _ in range(5000)]
gc = Counter()
for V in arrs:
    g = G(V)
    for i in range(8):
        ds = [e//g for e in diffs(V, i)]
        if any(e % 8 == 0 for e in ds) and not any(e % 16 == 0 for e in ds): gc[g] += 1
print("earlier scale-2 runners by gcd gap g:", dict(sorted(gc.items())))

# 2. the same runners rebuilt at other gap sizes: V = c + g*W
bases = [(1,2,3,4,5,6,8,9), (1,31,75,97,128,160,176,225), (1,2,3,4,5,6,8,17), (3,7,12,20,29,31,44,50)]
print("\nrebuilt at gap g (speeds 11 + g*W): per runner  [slot multiples | first live scale | least working scale | scale-2 rule]")
for W in bases:
    print(" W =", W)
    for g in (1, 2, 3, 5, 7, 12, 30, 1974):
        V = tuple(11 + g*w for w in W)
        assert G(V) == g * G(W)
        row = []
        for i in range(8):
            gg = G(V); ds = [e//gg for e in diffs(V, i)]
            mult = sorted({e//8 for e in ds if e % 8 == 0})
            l0 = L0(V, i)
            least = next(s for s in range(1, 200) if works(V, i, s*gg))
            rule = ""
            if any(e % 8 == 0 for e in ds) and not any(e % 16 == 0 for e in ds):
                pred_fail = len({cls(e) for e in ds if e % 2}) == 4
                actual_fail = not works(V, i, 2*gg)
                rule = "ok" if pred_fail == actual_fail else "MISMATCH"
            row.append(f"{mult or '-'}|{l0}|{least}|{rule or '.'}")
        print(f"   g={G(V):>5}: " + "  ".join(row))

# 3. random W, random g up to 500: rule and scale invariance
bad = 0; n = 0; inv_bad = 0
for _ in range(3000):
    W = tuple(sorted(rng.sample(range(1, 300), 8))); g = rng.randint(2, 500); c = rng.randint(1, 10**6)
    V = tuple(c + g*w for w in W); gg = G(V); gw = G(W)
    for i in range(8):
        ds = [e//gg for e in diffs(V, i)]
        if any(e % 8 == 0 for e in ds) and not any(e % 16 == 0 for e in ds):
            n += 1
            pred_fail = len({cls(e) for e in ds if e % 2}) == 4
            if pred_fail != (not works(V, i, 2*gg)): bad += 1
        if bool(works(V, i, gg)) != bool(works(W, i, gw)): inv_bad += 1
print(f"\nrandom gaps g in [2,500]: scale-2 runners {n}, rule mismatches {bad}; scale-1 verdict differs from the unscaled W: {inv_bad}")
