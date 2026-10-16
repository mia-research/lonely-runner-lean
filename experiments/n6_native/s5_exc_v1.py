#!/usr/bin/env python3
"""Exceptions to the simple pair-window fold (§5, k >= 2, not uniform at j0; s5_pf_v1). Per set:
 (i) features: k, alpha/alpha_max (alpha = v1/v2, alpha_max = k/(3k-1)), lam = (v4-v2)/v1, beta = (v4-v2)/v2, mu = v4/(3v5),
     the pair windows j where runner 1 is clear across P_j (its lap n1), and for each why fold5 fails there:
     'w<mu' (runner 4 sweeps less than mu), or the offset z = beta u (mod 1) and the arc [mu - w, 2/3 - mu] it misses;
 (ii) the witness that does close it: first four-block fold over t <= 3/v1 (block, laps, window start/end in units of
     the pair-window index j = v2 t), or sharp window_two at a pair window, or a lap box;
 (iii) grouped by witness type."""
import math, sys, random
from fractions import Fraction as F
from itertools import combinations
from collections import Counter, defaultdict
exec(open("s5_pf_v1.py").read().split("\ndef run(sets")[0])
exec(open("s5_obs_v2.py").read().split("\ndef run(sets")[0].split('exec(open("s5_obs_v1.py")')[1].split("\n", 1)[1])
def diag(S):
    v1, v2, v3, v4, v5 = S; D = v3 - v2; k = v1 // D
    al = F(v1, v2); amax = F(k, 3 * k - 1); be = F(v4 - v2, v2); mu = F(v4, 3 * v5)
    rows = []
    for j, s0, s1 in pair(S):
        p1 = v1 * s0; n1 = math.floor(p1 - F(1, 6)); sw1 = v1 * (s1 - s0)
        if not (p1 - n1 + sw1 <= F(5, 6)): continue
        w = v4 * (s1 - s0); z = frac(be * (j + F(1, 6)))
        why = "w<mu" if w < mu else f"z={float(z):.3f} arc=[{float(mu - w):.3f},{float(F(2,3) - mu):.3f}]"
        rows.append((j, n1, why))
    return k, float(al / amax), float(F(v4 - v2, v1)), float(mu), rows
def witness(S):
    fs = folds(S)
    if fs:
        L, blk, ms, r = fs[0]
        return f"fold, runner {r+1} folded, laps {ms}, start j~{float(L * S[1]):.2f}"
    for j, L, U in pair(S):
        if any(sharp(b - a, S[3], S[4]) for a, b in clear_sub(S[0], L, U)): return f"sharp window_two at pair window j={j}"
    return "other"
H = int(sys.argv[1]) if len(sys.argv) > 1 else 40
sets = [S for S in combinations(range(1, H + 1), 5) if math.gcd(*S) == 1 and s5(S) and S[0] // (S[2] - S[1]) >= 2 and not uni_j0(S) and not simple_fold(S)]
random.seed(56); big = []
while len(big) < 3000:
    S = tuple(sorted(random.sample(range(1, 3001), 5)))
    if math.gcd(*S) == 1 and s5(S) and S[0] // (S[2] - S[1]) >= 2: big.append(S)
sets += [S for S in big if not uni_j0(S) and not simple_fold(S)]
grp = defaultdict(list); feat = Counter()
for S in sets:
    k, ar, lam, mu, rows = diag(S); wt = witness(S)
    key = wt.split(", start")[0].split(" at pair")[0]
    key = key if not key.startswith("fold") else "fold, runner " + key.split("runner ")[1].split(" folded")[0] + " folded, laps " + key.split("laps ")[1]
    grp[key].append((S, k, round(ar, 2), round(lam, 2), round(mu, 3), rows, wt))
    feat[(k, "alpha/amax>=0.8" if ar >= 0.8 else "alpha/amax<0.8", f"{len(rows)} usable pair windows")] += 1
print(f"exceptions: {len(sets)}")
print("features (k, alpha share, usable pair windows):", sorted(feat.items(), key=lambda z: -z[1]))
for key, l in sorted(grp.items(), key=lambda z: -len(z[1])):
    print(f"\n-- witness {key}: {len(l)}")
    for row in l[:4]: print("   ", row)
