import sys, itertools
from math import gcd
from functools import reduce
from lapvector_decide_v1 import attains, diffs

N = int(sys.argv[1])
cnt = 0; profs = set(); fails = []
for rest in itertools.combinations(range(1, N+1), 7):
    V = (0,) + rest
    if reduce(gcd, rest) != 1:
        continue
    cnt += 1
    for i in range(8):
        ds = tuple(sorted(diffs(V, i)))
        if ds in profs:
            continue
        profs.add(ds)
        if attains(list(ds)) is None:
            fails.append((V, i, ds))
print(f"span<={N}: {cnt} arrangements (gcd 1), {len(profs)} distinct runner-profiles, {len(fails)} failures")
for f in fails[:10]:
    print("  FAIL", f)
