#!/usr/bin/env python3
"""Order seven exceptions vs all sets, primitive <= H: share with a common factor in a prefix, g4 = gcd(v1..v4) > 1 or
g5 = gcd(v1..v5) > 1 (an embedded scaled copy, like (2,6,8,10,x,y) = 2 (1,3,4,5) + two others), and the most common
normalised prefixes among those."""
import math, sys
from itertools import combinations
from collections import Counter
exec(open("o7_map_v1.py").read().split("def run(")[0])
H = int(sys.argv[1]) if len(sys.argv) > 1 else 30
tab = Counter(); pref = Counter()
for S in combinations(range(1, H + 1), 6):
    if math.gcd(*S) != 1: continue
    g4 = math.gcd(*S[:4]); g5 = math.gcd(*S[:5])
    key = "g5>1" if g5 > 1 else ("g4>1" if g4 > 1 else "coprime prefixes")
    k, _ = classify(S)
    ex = k in ("T5", "T6")
    tab[(key, "exception" if ex else "T4")] += 1
    if ex and g4 > 1: pref[tuple(x // g4 for x in S[:4])] += 1
print(f"primitive <= {H}:")
for key in ("g5>1", "g4>1", "coprime prefixes"):
    e, t = tab[(key, "exception")], tab[(key, "T4")]
    print(f"   {key}: {e + t} sets, exceptions {e} ({e / max(e + t, 1):.3%})")
print("   exceptions with g4 > 1, by normalised 4-prefix:", pref.most_common(12))
