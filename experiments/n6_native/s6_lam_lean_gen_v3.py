#!/usr/bin/env python3
"""v3: full generator of `s6_unit_dir` (λ = ±1) for S6Branch_v1.lean."""
import sys, math
from fractions import Fraction as F
sys.setrecursionlimit(100000)
exec(open("s6_lam_cert_v1.py").read().split("roots = {")[0])
exec(open("s6_lam_small_v1.py").read().split("res = []")[0])
def q(x): return f"({x.numerator}/{x.denominator} : ℝ)" if x.denominator != 1 else f"({x.numerator} : ℝ)"
VAR = {0: "U", 1: "Q", 2: "M"}; cnt = [0]
def leaf(kind, m, a, L, hdl):
    if kind == "after": return [f"exact closeA {m} {q(a)} {q(L)} (by norm_num) (by norm_num) {hdl} (fun p h1 h2 => by nlinarith) (fun p h1 h2 => by nlinarith)"]
    if kind == "before": return [f"exact closeB {m} {q(a)} {q(L)} (by norm_num) (by norm_num) {hdl} (fun p h1 h2 => by nlinarith) (fun p h1 h2 => by nlinarith)"]
    return [f"exact closeS hδ {q(a)} {q(L)} (by norm_num) (by norm_num) {hdl} (fun p h1 h2 => by nlinarith) (fun p h1 h2 => by nlinarith)"]
def tl(t, L, hdl):
    if t[0] == "leaf": return leaf(t[1][0], t[1][1], t[1][2], L, hdl)
    _, d, mid, l, r = t; v = VAR[d]; cnt[0] += 1; h = f"h{v}{cnt[0]}"
    out = [f"rcases le_total {v} {q(mid)} with {h} | {h}"]
    for sub in (l, r):
        s = tl(sub, L, hdl); out.append("· " + s[0]); out += ["  " + x for x in s[1:]]
    return out
def T(cell, lam, L, allow): return build(cell, lam, L, allow, 0, {"leaf": 0, "node": 0})
tA1 = T(((F(1), F(4, 3)), (F(1), F(12, 11)), (F(0), F(1, 3))), 1, F(1, 15), False)
tB1 = T(((F(3, 2), F(3, 2)), (F(1), F(8, 7)), (F(0), F(1, 3))), 1, F(1, 15), True)
tC1 = T(((F(2), F(2)), (F(1), F(4, 3)), (F(0), F(1, 3))), 1, F(1, 20), True)
tAm = T(((F(1), F(2)), (F(1), F(4, 3)), (F(0), F(1, 3))), -1, F(1, 15), False)
def ind(lines, n): return [" " * n + x for x in lines]
small = {}
for D in range(15, 20):
    for v1 in range(1, D):
        if 3 * v1 >= 2 * D: continue
        v2, v3 = D, 2 * D; v4 = v3 + v1
        if math.gcd(v1, D) != 1: small[(D, v1)] = "cop"; continue
        if 4 * v2 * v3 <= v4 * (5 * v2 - v3): small[(D, v1)] = "unif"; continue
        q4, u, mu = F(v4, v3), F(2), F(v4, 3 * (v4 + 1))
        small[(D, v1)] = next(((k, m, j) for j in range(D) for k in ("after", "before", "sum") for m in range(-2, 3) if ok(k, m, F(j, D), q4, u, mu)))
def small_case(D, v1):
    s = small[(D, v1)]
    if s == "cop": return ["exact absurd hcop (by norm_num)"]
    if s == "unif": return ["exfalso; norm_num at hnr"]
    k, m, j = s
    fin = "(by simp only [hQv, hUv, hMv]; norm_num; nlinarith [hMmax, hM0])"
    if k == "after": return [f"exact closeAP {j} {m} (by norm_num) (by norm_num) (by norm_num) {fin} {fin}"]
    if k == "before": return [f"exact closeBP {j} {m} (by norm_num) (by norm_num) (by norm_num) {fin} {fin}"]
    return [f"exact closeSP hδ {j} (by norm_num) {fin} {fin}"]
L = ["  rcases hl1 with rfl | rfl",
     "  · rcases lt_or_ge 2 c with hc3 | hc2",
     "    · have hU43 : U ≤ 4 / 3 := hU3 hc3"]
L += ind(tl(tA1, F(1, 15), "hDL15"), 6)
L += ["    · have hδ : v4 = v3 + v1 := hδ2 hc2 (by rfl)",
      "      rcases (show c = 1 ∨ c = 2 by omega) with rfl | rfl",
      "      · have hUe : U = 2 := by rw [hUdef]; norm_num",
      "        rcases le_or_lt 20 D with hD20 | hD20",
      "        · have hDL20 : 1 ≤ (D : ℝ) * (1 / 20) := by",
      "            have : (20 : ℝ) ≤ D := by exact_mod_cast hD20",
      "            linarith"]
L += ind(tl(tC1, F(1, 20), "hDL20"), 10)
L += ["        · subst hv2 hv3 hδ",
      "          interval_cases D"]
for D in range(15, 20):
    L.append("          · interval_cases v1")
    vs = [v1 for v1 in range(1, D) if 3 * v1 < 2 * D]
    for v1 in vs:
        s = small_case(D, v1); L.append("            · " + s[0]); L += ["              " + x for x in s[1:]]
L += ["      · have hUe : U = 3 / 2 := by rw [hUdef]; norm_num"]
L += ind(tl(tB1, F(1, 15), "hDL15"), 8)
L += ["  · skip"]
L += ind(tl(tAm, F(1, 15), "hDL15"), 4)
open("S6LamBody_v3.txt", "w").write("\n".join(L) + "\n")
print(len(L), "lines")
