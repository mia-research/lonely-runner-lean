import random
from math import gcd
from functools import reduce
from itertools import combinations
def clear_int(e, r, N):
    R = (e*r) % N; return N <= 8*R <= 7*N
cls = lambda x: min(x % 16, (-x) % 16)       # the pair {+x, -x} mod 16, labelled by its smaller member
tot = agree = 0; bad = []
rng = random.Random(7)
arrs = [c for c in combinations(range(1, 21), 8) if reduce(gcd, c) == 1] + \
       [tuple(sorted(rng.sample(range(1, 2001), 8))) for _ in range(5000)]
for V in arrs:
    g = reduce(gcd, [b-a for a, b in combinations(V, 2)])
    for i in range(8):
        ds = [abs(v-V[i])//g for j, v in enumerate(V) if j != i]
        if not any(e % 8 == 0 for e in ds) or any(e % 16 == 0 for e in ds):
            continue                                  # first live scale is not 2
        works2 = any(all(clear_int(e, r, 16) for e in ds) for r in range(1, 16, 2))
        odd_classes = {cls(e) for e in ds if e % 2}
        predicted_fail = len(odd_classes) == 4        # the four pairs {±1},{±3},{±5},{±7} all taken
        tot += 1; agree += (predicted_fail == (not works2))
        if predicted_fail == works2 and len(bad) < 5: bad.append((V, i, ds))
print(f"runners whose first live scale is 2: {tot}; rule 'scale 2 fails iff the odd differences take all four ± pairs mod 16' agrees on {agree}")
print("disagreements:", bad)
