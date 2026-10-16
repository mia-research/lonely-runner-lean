#!/usr/bin/env python3
"""Observation, §5 (D = v3 - v2 divides v1, 3 v1 < v3; k = v1/D, BHK's split k = 1, 2, >= 3).
Pair windows: runners 2, 3 on one lap j are clear together on P_j = [(j+1/6)/v2, (j+5/6)/v3], nonempty iff
j <= (4 v2 - v3)/(6D) (all before the first meeting time 1/D). At P_j's start runner 1 reads j v1/v2 (+ 1/6 v1/v2) --
a progression with step v1/v2 = k D/v2 -- and runner 4 reads j v4/v2 (+ ...).
Per set, the first of: A uniform pair window (runner 1 clear on a sub-window of P_j of length >= 2/(3 v4));
B pair window with window_two's sharp conditions; C pair-window four-block fold (runners 1 and 4, or 1 and 5, clear on a
common sub-window, the other folded); D any four-block fold; E cluster box (0,m,m,m,m); F rest.
Recorded by k: counts; for A and C the closing j as a fraction of j_max = (4 v2 - v3)/(6D) and runner 1's phase
j v1/v2 mod 1 (sixths)."""
import math, sys, random
from fractions import Fraction as F
from itertools import combinations
from collections import Counter, defaultdict
exec(open("s56_families_v1.py").read().split("def run(")[0].replace("exec(open(\"s56_window_v1.py\")", "exec(open(\"s56_window_v1.py\")"))
def s5(S):
    v1, v2, v3 = S[:3]; D = v3 - v2
    return v3 > 3 * v1 and v1 % D == 0
def clear_sub(v, L, U):
    out = []
    for m in range(int(L * v) - 1, int(U * v) + 2):
        a = max(L, F(6 * m + 1, 6 * v)); b = min(U, F(6 * m + 5, 6 * v))
        if a <= b: out.append((a, b))
    return out
def pair(S):
    v1, v2, v3 = S[:3]; D = v3 - v2
    j = 0
    while 6 * j * D <= 4 * v2 - v3:
        yield j, F(6 * j + 1, 6 * v2), F(6 * j + 5, 6 * v3); j += 1
def classify(S):
    v1, v2, v3, v4, v5 = S
    for j, L, U in pair(S):
        if any(b - a >= F(2, 3 * v4) for a, b in clear_sub(v1, L, U)): return "A", j
    for j, L, U in pair(S):
        if any(sharp(b - a, v4, v5) for a, b in clear_sub(v1, L, U)): return "B", j
    for j, L, U in pair(S):
        for a1, b1 in clear_sub(v1, L, U):
            for x, fv in ((v4, v5), (v5, v4)):
                if any(fv * (b - a) >= F(1, 3) for a, b in clear_sub(x, a1, b1)): return "C", j
    if fold(S): return "D", None
    if cluster(S): return "E", None
    return "F", None
def run(sets, label):
    cnt = defaultdict(Counter); pos = defaultdict(Counter); ex = defaultdict(list)
    for S in sets:
        v1, v2, v3 = S[:3]; D = v3 - v2; k = v1 // D; kb = str(k) if k <= 2 else ">=3"
        how, j = classify(S); cnt[kb][how] += 1
        if how in ("A", "C"):
            jmax = F(4 * v2 - v3, 6 * D)
            pos[(kb, how)][(int(4 * F(j) / jmax) if jmax > 0 else 0, int(6 * ((F(j * v1, v2)) % 1)))] += 1
        if how in ("D", "E", "F") and len(ex[(kb, how)]) < 8: ex[(kb, how)].append(S)
    print(f"== {label}: {len(sets)} sets")
    for kb in ("1", "2", ">=3"): print(f"   k = {kb}: {dict(sorted(cnt[kb].items()))}")
    for key in sorted(pos): print(f"   {key}: (quarter of j_max, sixth of runner-1 phase) top:", pos[key].most_common(6))
    for key in sorted(ex): print("   examples", key, ex[key])
if __name__ == "__main__":
    H = int(sys.argv[1]) if len(sys.argv) > 1 else 36
    run([S for S in combinations(range(1, H + 1), 5) if math.gcd(*S) == 1 and s5(S)], f"primitive §5 <= {H}")
    random.seed(55); big = []
    while len(big) < 2000:
        S = tuple(sorted(random.sample(range(1, 2001), 5)))
        if math.gcd(*S) == 1 and s5(S): big.append(S)
    run(big, "random §5 <= 2000")

