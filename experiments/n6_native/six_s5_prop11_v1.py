#!/usr/bin/env python3
"""§5 (D = v3 - v2 divides v1, 3 v1 < v3), split by k = v1/D: k = 1 (Prop 11 part 1, v1 + v2 = v3),
k = 2 (part 2 on v1/2), k >= 3 (Case 5.1). From six_cascade_observe_v1.tsv ([1,40]).
(1) per k: final flank rank of the cascade, most common setter sequences.
(2) BHK's Prop 11 windows (integer time): W_l = [t_l, t_l + 1/(3 v3)], t_l = (l + 1/2)/v3, with runner 1
    reading in [1/6, 1/3] at t_l (BHK (36)). For k = 1 (and k = 2 with runner 1 replaced by v1/2):
    is the cascade endpoint T in some W_l?  Control: among all lonely flank openings of the set in one
    period [0,1), the fraction lying in some W_l. Exact Fractions."""
from fractions import Fraction as F
from collections import Counter, defaultdict
rows = []
for l in list(open("six_cascade_observe_v1.tsv"))[1:]:
    s, c, m, ranks, laps, T, fr = l.rstrip("\n").split("\t")
    if c == "S5": rows.append((eval(s), eval(ranks), F(T), int(fr)))
def cd(x):
    f = x - (x.numerator // x.denominator); return min(f, 1 - f)
def frac(x): return x - (x.numerator // x.denominator)
def in_window(S, t, runner1_speed):
    v3 = S[2]
    u = v3 * t - F(1, 2)                  # t in W_l iff 0 <= v3 t - (l + 1/2) <= 1/3 for some l >= 0
    l = u.numerator // u.denominator
    if l < 0 or u - l > F(1, 3): return False
    tl = (l + F(1, 2)) / v3
    return F(1, 6) <= frac(runner1_speed * tl) <= F(1, 3)
def lonely_openings(S):
    out = []
    for b in S:
        for j in range(b):
            t = F(6 * j + 1, 6 * b)
            if all(cd(d * t) >= F(1, 6) for d in S): out.append(t)
    return out
fin = defaultdict(Counter); seqs = defaultdict(Counter); win = defaultdict(lambda: [0, 0, 0.0])
for S, rk, T, fr in rows:
    D = S[2] - S[1]; k = S[0] // D; key = k if k <= 2 else ">=3"
    fin[key][fr] += 1; seqs[key][rk] += 1
    if k in (1, 2):
        r1 = F(S[0], k)                       # k = 2: BHK apply part 2 to v1/2
        w = win[key]; w[0] += 1; w[1] += in_window(S, T, r1)
        L = lonely_openings(S)
        w[2] += sum(in_window(S, t, r1) for t in L) / len(L)
for key in (1, 2, ">=3"):
    n = sum(fin[key].values())
    print(f"k={key}: sets={n}; final flank rank {dict(sorted(fin[key].items()))}; top setter sequences {seqs[key].most_common(5)}")
    if key in win:
        a, b, c = win[key]
        print(f"   cascade endpoint inside a Prop 11 window: {b}/{a} ({b/a:.3f}); control (share of all lonely openings in a window): {c/a:.3f}")
