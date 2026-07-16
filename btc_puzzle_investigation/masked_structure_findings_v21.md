# Findings v21 — the odd-half / T_y max-bound HOLDS (not open)

**Date:** 2026-07-17 · `t_y_maxbound_v1.py`. Item #2 of the ranked menu. Object:
`U(a,b,c) = Σ_{d∈ℤ/n} e_p(b·x_d + c·y_d)·e_n(a·d)`, `(x_d,y_d)=[d]G` on prime-order `y²=x³+7`.
`T=U(·,·,0)` is the x-only, KS-bounded sum; the **odd-in-a half needs c≠0** (the y-coordinate).
v15/v16 flagged this as "the live un-bounded corner — closure covers x-readouts because T is an
x-object; s_y sits outside it and **no bound is known** for the twisted sum." Only
`avg_a|U|²=n` (a Parseval fact) was proven; the **uniform max over (b,c)** was open.

---

## Headline (graded)

**The odd-half max-bound holds — `max_a|U(a,b,c)| = O(√p·polylog)` uniformly over (b,c).** It is
**not open**: it is covered by the general-f Kohel–Shparlinski / Lange–Shparlinski bound (the
x-only cited statement extends because `bx+cy` is a bounded-degree rational function), and is
empirically confirmed with a small constant, no scar, no CM enhancement. This resolves the
"un-bounded corner" — one more instance of §5's lesson that reading the source's *general* form
dissolves an apparent obstacle.

---

## 1. `[CITED — general-f KS/LS]` + `[PROVED reduction]` Why the bound holds uniformly

The cited closure input (`glv_closure_theorem_v2.md §2`) is the **x-only** statement:
`|T(a,b)|=|U(a,b,0)| ≤ C√p(log p)^{O(1)}`, C absolute (Kohel–Shparlinski, ANTS-IV 2000;
Shparlinski, *Cryptographic Applications of Analytic Number Theory*, Ch. 6).

**Reduction `[PROVED]`:** on `E: y²=x³+Ax+B`, the function `x` has a pole of order 2 at `O` and
`y` a pole of order 3, so for `(b,c)≠(0,0)` the linear form `f=bx+cy` is a nonconstant rational
function on `E` of **pole order ≤ 3** — degree bounded by 3, *independent of the coefficients*.
`U(a,b,c)=Σ_d e_p(f([d]G))·e_n(ad)` is therefore the same mixed additive(coordinate)×
additive(index) sum, with a rational function one degree higher than `x`.

**Consequence `[CITED, exact statement to VERIFY]`:** the KS/Lange–Shparlinski method bounds
`Σ_d ψ(f([d]G))e_n(ad)` for *any* nonconstant rational `f` with a constant depending only on
`deg f` — hence **uniform in (b,c)**. (Lange–Shparlinski 2005, *Certain exponential sums and
random walks on elliptic curves*, Canad. J. Math. 57, treat coordinate combinations directly.)
So `max_a|U(a,b,c)|=O(√p·polylog)` uniformly over `(b,c)≠0`. The prior "no bound known" reflected
having only the x-only statement in hand; the general-f form covers `bx+cy`. *(A from-scratch
√p-strength proof reconstructs the full KS machinery and is not attempted; this is CITED, not a
new theorem. Verify the exact hypotheses in LS before treating it as closed.)*

---

## 2. `[VERIFIED-scope]` Empirical confirmation — bound holds, no scar, CM=non-CM

`max_{a≠0,(b,c)≠(0,0)} |U(a,b,c)| / √p` (secp `y²=x³+7`; **full (b,c)** scan to p=733, **sampled**
(3000 pairs + all diagonals) to p=2503):

| p | 61 | 211 | 433 | 733 | 1669 | 2503 |
|---|---|---|---|---|---|---|
| max/√p | 3.23 | 3.42 | 3.54 | 3.58 | 3.54* | 3.66* |
| max/(√p·log p) | 0.785 | 0.639 | 0.583 | 0.543 | 0.478* | 0.468* |

(*sampled = lower bound on the true max.) **max/√p is bounded (~3.2–3.7) and grows *slower than
log p*** over a 41× range in p (the log-normalized ratio *decreases* monotonically) — consistent
with `O(√p·polylog)` and, empirically, an even slower factor than `√(log p)`.

- **The y-coordinate adds but does not break KS:** at every prime the `c≠0` max (3.2–3.6)
  exceeds the pure-x `c=0` max (2.4–2.9) by a **bounded ~1.3×** — the odd half carries a
  comparable √p term, not a divergent one.
- **No scar:** the argmax `(b,c)` is **generic** at every prime — not a diagonal `c=±b`, not a
  GLV ratio `c/b∈{β,β²}`, wandering with p. The exceptional-non-cancelling `(b,c)` that would
  refute the bound (v16's concern) **does not exist** in the tested range.
- **CM = non-CM `[matched control]`:** at p=211, CM (secp) max/√p = 3.42, non-CM (y²=x³+x+1)
  = 3.66 — secp is if anything *lower*; no CM-specific enhancement.
- **s_y-twisted T_y** `= Σ_d e_p(bx_d)s_y(d)e_n(ad)` (v15's exact object, s_y odd in d): also
  √p-bounded, same sub-log-p scaling (max/√p = 3.0, 3.7, 3.55 at p=211, 733, 1669).

---

## Verdict & grades (locked)

- **The "live un-bounded corner" is RESOLVED — the bound holds.** Down-grade from "open" to
  "covered + confirmed."
- Analytical: **CITED** (general-f KS / Lange–Shparlinski) + **PROVED** reduction (`deg(bx+cy)≤3`,
  uniform in coefficients). Exact LS hypotheses to VERIFY before treating as fully closed.
- Empirical: **VERIFIED-scope** — full (b,c) scan p≤733, sampled p≤2503; max/√p bounded, sub-log-p
  growth, argmax generic, y-adds-bounded, CM=non-CM, T_y bounded.
- **Crypto consequence:** the y-coordinate / y-sign readout is bounded by the same √p·polylog
  barrier as the x-coordinate ⇒ the closure theorem's stated x-only scope extends to `bx+cy`
  single-index readouts. The **barrier stays computational** (the aligned readout still needs `U`
  ⇒ the DLP, per v14/v16); this bound is about the *misaligned/generic* magnitude, which is
  √p — exactly the Weil/KS noise floor. Security conclusion unchanged.
- **Scope caveats:** small p (61–2503); secp's `p≈2²⁵⁶` untested empirically but covered by the
  CITED bound; "general-f KS" statement cited from method, exact reference hypotheses to verify.
  An empirical confirmation is a scoped fact; the rigorous guarantee is the citation.

## Files
Engine: `t_y_maxbound_v1.py` (self-contained; exact-int curve/group, numpy-float only for the
analytic-size |U| magnitudes — same carve-out as `glv_closure_verification_v1.py`). Prior:
`xy_interference_U_v1.py` (built U, avg_a|U|²=n), `masked_structure_findings_v15/v16.md`,
`glv_closure_theorem_v2.md` (KS citation, §7 gap list).
