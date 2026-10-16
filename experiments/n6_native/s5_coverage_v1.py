#!/usr/bin/env python3
"""§5 (v1 = c' D, 3 v1 < v3) coverage by the pair window (runners 2, 3 on one lap j, clear on
[(j + 1/6)/v2, (j + 5/6)/v3]), runner 1 clear on a sub-window, runners 4, 5 by window_two:
  uniform: some j and sub-window of length >= 2/(3 v4);  explicit j0 = floor(v2/(2 v1)) (runner 1 near 1/2) uniform;
  sharp: window_two's own conditions;  then four-block fold;  rest listed. Also (v4 - v3)/D and v3/v1 on the non-uniform sets."""
import math, sys, random
from fractions import Fraction as F
from itertools import combinations
from collections import Counter
exec(open("s56_families_v1.py").read().split("def run(")[0])
def s5(S):
    v1, v2, v3 = S[:3]; D = v3 - v2
    return v3 > 3 * v1 and v1 % D == 0
def pairwins(S, js):
    v1, v2, v3 = S[:3]
    for j in js:
        a, b = F(6 * j + 1, 6 * v2), F(6 * j + 5, 6 * v3)
        if a <= b:
            for x, y in r1_subwindows(v1, a, b): yield x, y
def uni(S, js): return any(y - x >= F(2, 3 * S[3]) for x, y in pairwins(S, js))
def run(sets, label):
    c = Counter(); rest = []; info = Counter()
    for S in sets:
        js = range(0, 4 * S[1] // S[0] + 2)
        if uni(S, [S[1] // (2 * S[0])]): c["uniform, explicit j0"] += 1
        elif uni(S, js): c["uniform, other j"] += 1
        elif fam(S): c["sharp window_two"] += 1
        elif fold(S): c["four-block fold"] += 1
        elif cluster(S): c["cluster box"] += 1
        else: c["rest"] += 1; rest.append(S)
    print(f"{label}: {len(sets)} §5 sets: {dict(c)}; rest {rest[:12]}")
H = int(sys.argv[1]) if len(sys.argv) > 1 else 30
run([S for S in combinations(range(1, H + 1), 5) if math.gcd(*S) == 1 and s5(S)], f"§5 <= {H}")
random.seed(5); big = []
while len(big) < 2000:
    S = tuple(sorted(random.sample(range(1, 1001), 5)))
    if math.gcd(*S) == 1 and s5(S): big.append(S)
run(big, "random §5 <= 1000")
