#!/usr/bin/env python3
"""E36: when do runners 4 and 5 have a common clear point inside a J123 window (§5 sets)? For each §5 set, every
window W = [J0, J1] of positive length on which runners 1, 2, 3 are all clear, in time order, up to and including
the one containing the cascade's ending T. For each window: readings a4 = frac(d4 J0), a5 = frac(d5 J0), the length
in laps of 4 and of 5 (l4 = d4 |W|, l5 = d5 |W|), and whether 4 and 5 share a clear point of positive length in W.
Control: the first window with a shared point must contain T (the cascade returns the first lonely instant), except
where T's box is a single point. Failing windows are classified: 4 never clear in W; 5 never clear in W; both clear
somewhere but never together. Output: six_s5_window45_v1.tsv (one line per window) and a summary.
Usage: six_s5_window45_v1.py"""
import math
from fractions import Fraction as F
from collections import Counter
s6, s56 = F(1, 6), F(5, 6)
def frac(z): return z - (z.numerator // z.denominator)
def clear_ivs(d, a, b):
    out = []; k = math.floor(a * d - s56)
    while (6*k+1) / (6*d) <= b:
        lo, hi = max(a, (6*k+1)/(6*d)), min(b, (6*k+5)/(6*d))
        if lo <= hi: out.append((lo, hi))
        k += 1
    return out
def windows123(S, upto):
    ivs = [(F(0), upto)]
    for d in S[:3]:
        new = []
        for a, b in ivs:
            for lo, hi in clear_ivs(d, a, b): new.append((lo, hi))
        ivs = new
    return [w for w in ivs if w[0] < w[1]]
rows = [l.rstrip("\n").split("\t") for l in open("six_cascade_observe_v1.tsv")][1:]
out = open("six_s5_window45_v1.tsv", "w")
out.write("set\tidx\tJ0\tJ1\ta4\ta5\tl4\tl5\tshared\tkind\tcontainsT\n")
ctrl = Counter(); fails = Counter(); succ = Counter(); n = 0
maxfail = {"l4": (F(0), None), "l5": (F(0), None)}; minsucc = {"l4": (F(10**9), None), "l5": (F(10**9), None)}
for r in rows:
    if r[1] != "S5": continue
    S = [F(x) for x in eval(r[0])]; T = F(r[5]); n += 1
    W = windows123(S, T + F(1, S[0]))
    first_shared = None
    for idx, (J0, J1) in enumerate(W):
        if J0 > T: break
        c4 = [iv for iv in clear_ivs(S[3], J0, J1) if iv[0] < iv[1]]; c5 = [iv for iv in clear_ivs(S[4], J0, J1) if iv[0] < iv[1]]
        shared = any(max(a1, a2) < min(b1, b2) for a1, b1 in c4 for a2, b2 in c5)
        if shared: kind = "start" if (frac(S[3]*J0) >= s6 and frac(S[3]*J0) <= s56 and frac(S[4]*J0) >= s6 and frac(S[4]*J0) <= s56) else "later"
        else: kind = "4 never clear" if not c4 else ("5 never clear" if not c5 else "both clear, never together")
        l4, l5 = S[3] * (J1 - J0), S[4] * (J1 - J0)
        cT = J0 <= T <= J1
        out.write("\t".join(map(str, [tuple(int(x) for x in S), idx, J0, J1, frac(S[3]*J0), frac(S[4]*J0), l4, l5, shared, kind, cT])) + "\n")
        if shared:
            succ[kind] += 1
            if first_shared is None: first_shared = (J0, J1)
            for key, val in (("l4", l4), ("l5", l5)):
                if val < minsucc[key][0]: minsucc[key] = (val, (tuple(int(x) for x in S), idx))
        else:
            fails[kind] += 1
            for key, val in (("l4", l4), ("l5", l5)):
                if val > maxfail[key][0]: maxfail[key] = (val, (tuple(int(x) for x in S), idx))
    k = [math.floor(d * T) for d in S]
    point = max((6*k[i]+1)/(6*S[i]) for i in range(5)) == min((6*k[i]+5)/(6*S[i]) for i in range(5))
    if first_shared is None: ctrl["no shared window up to T" + (" (T a single point)" if point else "")] += 1
    else: ctrl["first shared window contains T" if first_shared[0] <= T <= first_shared[1] else ("first shared window before T" + (" (T a single point)" if point else ""))] += 1
out.close()
print(f"§5 sets: {n}")
print("control:", dict(ctrl))
print("failing windows before the ending:", dict(fails), "; total", sum(fails.values()))
print("windows with a shared clear point:", dict(succ))
print("largest failing length: in 4-laps", float(maxfail["l4"][0]), maxfail["l4"][1], "; in 5-laps", float(maxfail["l5"][0]), maxfail["l5"][1])
print("smallest succeeding length: in 4-laps", float(minsucc["l4"][0]), minsucc["l4"][1], "; in 5-laps", float(minsucc["l5"][0]), minsucc["l5"][1])
