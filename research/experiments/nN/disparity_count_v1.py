"""How many distinct disparities does a five-runner subject actually have?
The circle enters through |v_i - v_k|, which can IDENTIFY two runners but never split one."""
from itertools import combinations
import collections
H = 22
dist = collections.Counter(); extreme = collections.Counter(); interior = collections.Counter()
allsmall = 0; tot = 0
for v in combinations(range(0, H+1), 5):
    tot += 1; cards = []
    for k in range(5):
        c = len({abs(v[i]-v[k]) for i in range(5) if i != k})
        cards.append(c); dist[c] += 1
        (extreme if k in (0,4) else interior)[c] += 1
    if max(cards) <= 3: allsmall += 1
print(f"5-runner integer arrangements, speeds in [0,{H}]: {tot}   subjects: {tot*5}")
print(f"  card(diffSet), all subjects        : {dict(sorted(dist.items()))}")
print(f"  extreme subjects (fastest/slowest) : {dict(sorted(extreme.items()))}")
print(f"  interior subjects                  : {dict(sorted(interior.items()))}")
print(f"  arrangements with EVERY subject at card <= 3 (already proved): {allsmall}")
print(f"  maximum card observed: {max(dist)}   (n-1 = 4)")
