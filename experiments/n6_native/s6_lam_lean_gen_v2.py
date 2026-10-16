#!/usr/bin/env python3
"""v2: generates the whole λ = ±1 theorem (s6_unit_dir) for S6Branch_v1.lean: setup, the closers, the case trees
(c ≥ 3 / c = 2 / c = 1 with D ≥ 20 from s6_lam_cert_v1; c = 1 with D = 15..19 from s6_lam_small_v1)."""
import sys, math
from fractions import Fraction as F
sys.setrecursionlimit(100000)
exec(open("s6_lam_cert_v1.py").read().split("roots = {")[0])
def q(x): return f"({x.numerator}/{x.denominator} : ℝ)" if x.denominator != 1 else f"({x.numerator} : ℝ)"
VAR = {0: "U", 1: "Q", 2: "M"}
cnt = [0]
def leaf_lines(kind, m, a, L, hdl):
    if kind == "after":
        return [f"exact closeA {m} {q(a)} {q(L)} (by norm_num) (by norm_num) {hdl} (fun p h1 h2 => by nlinarith) (fun p h1 h2 => by nlinarith)"]
    if kind == "before":
        return [f"exact closeB {m} {q(a)} {q(L)} (by norm_num) (by norm_num) {hdl} (fun p h1 h2 => by nlinarith) (fun p h1 h2 => by nlinarith)"]
    return [f"exact closeS {q(a)} {q(L)} (by norm_num) (by norm_num) (by norm_num) {hdl} (fun p h1 h2 => by nlinarith) (fun p h1 h2 => by nlinarith)"]
def tree_lines(t, L, hdl):
    if t[0] == "leaf":
        kind, m, a = t[1]; return leaf_lines(kind, m, a, L, hdl)
    _, d, mid, l, r = t; v = VAR[d]; cnt[0] += 1; h = f"h{v}{cnt[0]}"
    out = [f"rcases le_total {v} {q(mid)} with {h} | {h}"]
    for sub in (l, r):
        sl = tree_lines(sub, L, hdl)
        out.append("· " + sl[0]); out += ["  " + x for x in sl[1:]]
    return out
def T(cell, lam, L, allow):
    st = {"leaf": 0, "node": 0}; return build(cell, lam, L, allow, 0, st)
tA1 = T(((F(1), F(4, 3)), (F(1), F(12, 11)), (F(0), F(1, 3))), 1, F(1, 15), False)
tB1 = T(((F(3, 2), F(3, 2)), (F(1), F(8, 7)), (F(0), F(1, 3))), 1, F(1, 15), True)
tC1 = T(((F(2), F(2)), (F(1), F(4, 3)), (F(0), F(1, 3))), 1, F(1, 20), True)
tAm = T(((F(1), F(2)), (F(1), F(4, 3)), (F(0), F(1, 3))), -1, F(1, 15), False)
# small cases
exec(open("s6_lam_small_v1.py").read().split("res = []")[0])
small = []
for D in range(15, 20):
    for v1 in range(1, D):
        if 3 * v1 >= 2 * D or math.gcd(v1, D) != 1: continue
        v2, v3 = D, 2 * D; v4 = v3 + v1
        if 4 * v2 * v3 <= v4 * (5 * v2 - v3): continue
        q4, u, mu = F(v4, v3), F(2), F(v4, 3 * (v4 + 1))
        hit = next(((k, m, j) for j in range(D) for k in ("after", "before", "sum") for m in range(-2, 3) if ok(k, m, F(j, D), q4, u, mu)), None)
        small.append((D, v1, hit))
def ind(lines, n): return [" " * n + x for x in lines]
L = []
L += ["  rcases hl1 with rfl | rfl"]
L += ["  · -- λ = 1", "    rcases lt_or_ge 2 c with hc3 | hc2"]
L += ["    · -- c ≥ 3 (U ≤ 4/3)", "      have hU43 : U ≤ 4 / 3 := hU3 hc3"]
L += ind(tree_lines(tA1, F(1, 15), "hDL15"), 6)
L += ["    · rcases (show c = 1 ∨ c = 2 by omega) with rfl | rfl"]
L += ["      · -- c = 1 (U = 2): δ = v₁", "        have hUe : U = 2 := by rw [hUdef]; norm_num", "        rcases le_or_lt 20 D with hD20 | hD20"]
L += ["        · have hDL20 : 1 ≤ (D : ℝ) * (1 / 20) := by have : (20 : ℝ) ≤ D := by exact_mod_cast hD20", "            linarith"]
L += ind(tree_lines(tC1, F(1, 20), "hDL20"), 10)
# small: D in 15..19
L += ["        · -- D = 15..19: the 37 explicit cases", "          sorry"]
L += ["      · -- c = 2 (U = 3/2)", "        have hUe : U = 3 / 2 := by rw [hUdef]; norm_num"]
L += ind(tree_lines(tB1, F(1, 15), "hDL15"), 8)
L += ["  · -- λ = -1"]
L += ind(tree_lines(tAm, F(1, 15), "hDL15"), 4)
open("S6LamBody_v2.txt", "w").write("\n".join(L) + "\n")
print(len(L), "lines; small cases", len(small))
