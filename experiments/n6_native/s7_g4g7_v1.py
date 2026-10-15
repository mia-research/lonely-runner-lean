#!/usr/bin/env python3
"""E53: BHK's exceptional orbits G4, G7 (§7) and the single-window criterion, exact. For every exceptional set to 80
(s7_exceptional_v2_80.out: BHK's main route fails; orbit size n; relaxed meeting-time route works or not):
 - orbit group: the points ({k v3/D}, {k v1/D}); G4 = <(1/2, 1/4)>, G7 = <(2/7, 1/7)> (as sets);
 - BHK's named meeting time: G4 at x3 = 1/2, x1 = 1/4; G7 at x3 = 4/7, x1 = 2/7;
 - the window there, exactly, against the formulas W4 = 1/(3v3) + 1/(12 v1),
   W7 = 11/(42 v3) + min(17/(42 v3), 5/(42 v1));
 - criterion: W >= L(rho)/v4 (window_two), rho = v5/v4; against the relaxed flag (any meeting time)."""
from fractions import Fraction as F
from collections import Counter
s6, s56 = F(1, 6), F(5, 6)
def frac(z): return z - (z.numerator // z.denominator)
def Lform(rho):
    m = max(-(-(rho + 1) // 3) - 1, 0)
    return max(F(1, 3) + 1 / (3 * rho), (m + F(1, 3)) / rho)
def window_at(S, t):
    lo, hi = F(-10**9), F(10**9)
    for d in S[:3]:
        x = frac(d * t)
        if not (s6 <= x <= s56): return None
        lo = max(lo, t - (x - s6) / d); hi = min(hi, t + (s56 - x) / d)
    return hi - lo
G4 = {(F(k % 4, 4) * 2 % 1, F(k, 4) % 1) for k in range(4)}
G4 = {(frac(F(k, 2)), frac(F(k, 4))) for k in range(4)}
G7 = {(frac(F(2 * k, 7)), frac(F(k, 7))) for k in range(7)}
c = Counter(); formula_ok = Counter(); crit = Counter(); other = Counter(); ex = []
for line in open("s7_exceptional_v2_80.out"):
    if not line.startswith("EXC"): continue
    v1, v2, v3, v4, v5, n, rel = map(int, line.split()[1:8])
    S = [F(x) for x in (v1, v2, v3, v4, v5)]; D = v3 - v2
    pts = {(frac(F(v3 * k, D)), frac(F(v1 * k, D))) for k in range(D)}
    grp = "G4" if pts == G4 else ("G7" if pts == G7 else f"other n={len(pts)}")
    c[grp] += 1
    if grp not in ("G4", "G7"): other[(grp, rel)] += 1; continue
    tgt = (F(1, 2), F(1, 4)) if grp == "G4" else (F(4, 7), F(2, 7))
    k = next(k for k in range(D) if (frac(F(v3 * k, D)), frac(F(v1 * k, D))) == tgt)
    W = window_at(S, F(k, D))
    Wf = F(1, 3 * v3) + F(1, 12 * v1) if grp == "G4" else F(11, 42 * v3) + min(F(17, 42 * v3), F(5, 42 * v1))
    formula_ok[(grp, W == Wf)] += 1
    ok = W >= Lform(S[4] / S[3]) / S[3]
    crit[(grp, "W >= L/v4" if ok else "W < L/v4", "relaxed works" if rel else "relaxed fails")] += 1
    if not ok and rel and len(ex) < 5: ex.append((v1, v2, v3, v4, v5))
print("exceptional sets by orbit group:", dict(c))
print("window at BHK's named meeting time equals the formula:", dict(formula_ok))
print("criterion vs relaxed (any meeting time):")
for k_, v in sorted(crit.items()): print("  ", v, k_)
print("other groups (should be none):", dict(other))
print("criterion fails but another meeting time works, e.g.:", ex)
