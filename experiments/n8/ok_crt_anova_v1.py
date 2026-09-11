#!/usr/bin/env python3
"""CRT ANOVA on S_x -- the axiom check for the number-thermodynamics transfer.

ENDPOINT_RESONANCE_v1 proves S : Z/M -> Q is periodic, M = 8*lcm(H), and mean zero.
SIGMA_ALPHA_v1 Sec.5 reduces n=8 to: for every Case-2 tuple some pair {x,y} has
S_x/x + S_y/y < |G_H|/2.  That is a LARGE-DEVIATION question on the finite abelian
group Z/M.

number_thermodynamics.md Sec.5 asserts a free energy that is "additive over the CRT
factorisation ... with no cross terms" (the Euler-product / no-interaction axiom).
The VERIFICATION DEMAND for carrying that here:

    Z/M  =  prod_j Z/p_j^{a_j}      (the independent subsystems)
    Is S additive over that product, i.e. S(x) = sum_j T_j(x mod p_j^{a_j})?

Decided EXACTLY by ANOVA (Hoeffding decomposition) over the product group: S splits
orthogonally as sum over subsets T of factors, Var(S) = sum_T Var(S_T).  "No cross
terms" == all |T| >= 2 components vanish.  If they do, S is a sum of INDEPENDENT
bounded mean-zero variables and Chernoff gives a genuine rate function sum_p I_p --
which is exactly the estimate the pair-existence statement needs.  If they do not,
this names the axiom that fails, and by how much.

Exact Fraction throughout; no float on any decision path.
"""
from fractions import Fraction as F
from math import lcm
from functools import reduce
from itertools import combinations
import sys

# ---- the grid G(H) and S_x, transcribed verbatim from ok_wolf_period_v1.py ----
def ivs(E):
    out = []
    for e in E:
        for k in range(0, e + 1):
            lo, hi = max(F(8*k-1, 8*e), F(0)), min(F(8*k+1, 8*e), F(1))
            if lo < hi: out.append((lo, hi))
    return out
def merge(iv):
    iv = sorted(iv); m = []
    for lo, hi in iv:
        if m and lo <= m[-1][1]: m[-1][1] = max(m[-1][1], hi)
        else: m.append([lo, hi])
    return m
def complement(m):
    g, cur = [], F(0)
    for lo, hi in m:
        if cur < lo: g.append((cur, lo))
        cur = max(cur, hi)
    if cur < 1: g.append((cur, F(1)))
    return g
def psi(t):
    t = t - int(t)
    if t < 0: t += 1
    if t <= F(1, 8): return 3 * t / 4
    if t <= F(7, 8): return F(1, 8) - t / 4
    return 3 * (t - 1) / 4

def factor(m):
    f, d = [], 2
    while d * d <= m:
        if m % d == 0:
            q = 1
            while m % d == 0: m //= d; q *= d
            f.append(q)
        d += 1
    if m > 1: f.append(m)
    return f

def anova(S, mods):
    """Exact Hoeffding decomposition of S over prod_j Z/mods[j].
    S is a dict keyed by the coordinate tuple.  Returns {subset: Var(component)}."""
    k = len(mods); M = 1
    for m in mods: M *= m
    idx = list(S.keys())
    # conditional means E[S | x_U] for every subset U, exact
    cmean = {}
    for r in range(k + 1):
        for U in combinations(range(k), r):
            acc = {}
            for key in idx:
                sub = tuple(key[j] for j in U)
                acc[sub] = acc.get(sub, F(0)) + S[key]
            cnt = M
            for j in U: cnt //= mods[j]
            cmean[U] = {s: v / cnt for s, v in acc.items()}
    # Mobius: S_T(x_T) = sum_{U subset T} (-1)^{|T|-|U|} E[S | x_U]
    var = {}
    for r in range(k + 1):
        for T in combinations(range(k), r):
            tot = F(0)
            seen = {}
            for key in idx:
                sub = tuple(key[j] for j in T)
                if sub in seen: continue
                v = F(0)
                for r2 in range(len(T) + 1):
                    for U in combinations(T, r2):
                        sgn = (-1) ** (len(T) - r2)
                        v += sgn * cmean[U][tuple(key[j] for j in U)]
                seen[sub] = v
            cnt = M
            for j in T: cnt //= mods[j]
            tot = sum(v * v for v in seen.values()) * cnt / M
            var[T] = tot
    return var

def study(H, label):
    G = complement(merge(ivs(H))); MG = sum(v - u for u, v in G); N = len(G)
    L = reduce(lcm, H); M = 8 * L
    mods = factor(M)
    Sx = lambda x: sum(psi(F(x) * v) - psi(F(x) * u) for u, v in G)
    print(f"\n{'='*76}\n{label}   H = {H}")
    print(f"  |G| = {MG}   N = {N}   M = 8*lcm(H) = {M} = {' * '.join(map(str,mods))}")
    table = {}
    for x in range(M):
        table[tuple(x % m for m in mods)] = Sx(x)
    mean = sum(table.values()) / M
    print(f"  mean S = {mean}   (must be 0: {mean == 0})")
    var = anova(table, mods)
    tot = sum(v for T, v in var.items() if T)
    print(f"  Var(S) = {tot}  = {float(tot):.6f}")
    print(f"  {'order':>5}  {'share of Var':>14}   components")
    for r in range(1, len(mods) + 1):
        s = sum(v for T, v in var.items() if len(T) == r)
        det = "  ".join(f"{'x'.join(str(mods[j]) for j in T)}:{float(v/tot):.4f}"
                        for T, v in sorted(var.items()) if len(T) == r and v != 0)
        flag = " <-- MAIN EFFECTS" if r == 1 else (" <-- CROSS TERMS" if r == 2 else "")
        print(f"  {r:>5}  {float(s/tot):>14.6f}   {det}{flag}")
    inert = [mods[j] for j in range(len(mods))
             if all(v == 0 for T, v in var.items() if j in T)]
    print(f"  INERT local factors (S does not depend on them at all): {inert}")
    return float(sum(v for T, v in var.items() if len(T) == 1) / tot)

cases = [([2, 6, 8, 10, 14], "the E* grid"),
         ([1, 3, 4, 5, 7],   "its base"),
         ([1, 2, 3, 4, 5],   "an AP prefix"),
         ([1, 2, 3, 4, 5, 7], "6-subset of T2"),
         ([1, 4, 5, 6, 7],   "base of T3")]
shares = []
for H, lab in cases:
    shares.append((lab, study(H, lab)))
print(f"\n{'='*76}\nMAIN-EFFECT SHARE OF Var(S)  (1.0 == no cross terms == the axiom holds)")
for lab, s in shares:
    print(f"  {lab:>16}: {s:.6f}")

# ---------------------------------------------------------------------------
# CONTROL: is the order-<=2 vanishing FORCED, or a property of the test set?
# S = sum_{e in H} S_e, and S_e depends on x only through x mod 8e, so the ANOVA
# support of S_e is contained in primes(8e) = {2} u primes(e).  PREDICTION, made
# before running: max interaction order = 1 + max_e omega_odd(e), and the
# order-3 components that appear are exactly {2} u P for P subset primes(e).
# A test set of H whose members are all 2^a p^b CANNOT show order 3.  The cases
# below break that, at a predicted place.
print(f"\n\n{'#'*76}\nCONTROL -- forcing check.  Predicted max order = 1 + max_e omega_odd(e).")
for H, lab, pred in (([1, 2, 4, 8, 15],  "e=15,  omega_odd=2", 3),
                     ([1, 2, 3, 5, 21],  "e=21,  omega_odd=2", 3),
                     ([2, 4, 8, 16, 15], "e=15,  2-power rest", 3),
                     ([1, 2, 4, 8, 105], "e=105, omega_odd=3", 4),
                     ([1, 2, 4, 8, 9],   "e=9,   omega_odd=1 (null)", 2)):
    print(f"\n[predicted max order {pred}]", end="")
    study(H, lab)
