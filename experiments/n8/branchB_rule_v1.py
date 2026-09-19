"""Is there a RULE that picks a working reading?  Test candidate rules, exhaustively."""
from itertools import combinations
from collections import Counter
import random

def Wne(S, s):
    M = 8*s
    A = s + ((1 - s) % 8)
    while A <= 7*s:
        if all(min((sp*A) % M, M - (sp*A) % M) >= s for sp in S): return True
        A += 8
    return False

def Wsize(S, s):
    M, c = 8*s, 0
    A = s + ((1 - s) % 8)
    while A <= 7*s:
        if all(min((sp*A) % M, M - (sp*A) % M) >= s for sp in S): c += 1
        A += 8
    return c

rules = {
    "largest reading":        lambda S: max(S),
    "largest odd reading":    lambda S: max([x for x in S if x % 2], default=None),
    "reading of max v2":      lambda S: max(S, key=lambda x: ((x & -x).bit_length(), x)),
    "second largest":         lambda S: sorted(S)[-2],
}
fail = Counter(); tot = 0; sizes = []
ex = {}
for combo in combinations(range(2, 31), 6):
    if not any(x % 8 == 0 for x in combo): continue
    S = (1,) + combo; tot += 1
    sizes.append(Wsize(S, max(S)))
    for name, f in rules.items():
        s = f(S)
        if s is None or not Wne(S, s):
            fail[name] += 1
            ex.setdefault(name, (S, s))
print(f"Branch B profiles, readings from [2,30]: {tot:,}\n")
for name in rules:
    c = fail[name]
    print(f"  {name:<22} failures {c:>7,}  ({100*c/tot:6.3f}%)"
          + (f"   e.g. S={ex[name][0]} s={ex[name][1]}" if c else "   <-- NO FAILURES"))
print(f"\n  |W(S, max S)| over all profiles: min {min(sizes)}, "
      f"median {sorted(sizes)[len(sizes)//2]}, max {max(sizes)}")
print(f"  profiles with |W(S,max S)| = 0: {sizes.count(0):,}")

# wider range, random, to check the rule is not an artefact of [2,30]
rng = random.Random(20260919); bad = 0; N = 60000; mn = 10**9
for _ in range(N):
    while True:
        c = tuple(sorted(rng.sample(range(2, 4000), 6)))
        if any(x % 8 == 0 for x in c): break
    S = (1,) + c
    w = Wsize(S, max(S))
    mn = min(mn, w)
    if w == 0: bad += 1
print(f"\n  RANDOM, readings from [2,4000], {N:,} profiles: "
      f"'largest reading' failures = {bad:,}; min |W(S,max S)| = {mn}")
