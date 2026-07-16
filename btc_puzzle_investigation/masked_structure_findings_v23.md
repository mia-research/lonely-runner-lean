# Findings v23 — no cheap partial of the joint (x,y) shadow (single-key); multi-key stays open

**Date:** 2026-07-17 · `cheap_partial_shadow_v1.py`. Item #4 — the handover's "highest-value lead":
the aligned joint (x,y) readout leaks 0.93 (v16), but building it needs `U(a₀,b,c)` = all `(x_d,y_d)`
= the DLP. **Can a cheap (DLP-free) readout capture a *fraction* of that 0.93?**

## Headline (graded)

**No — for single-key readouts, and now it is a closure-theorem statement, not a thermodynamic
heuristic.** Every cheap readout sits at the noise floor, 2–3 orders of magnitude below the aligned
0.93; the multi-key / joint-SET version stays open (outside KS).

## 1. `[PROVED given KS + bounded 2D-Wiener]` The closure theorem extends to (x,y) readouts

A cheap readout is a point-function `F(P)`, expandable as `F(P)=Σ_{b,c} F̂(b,c) e_p(bx+cy)`. Then
`Corr_F(a) = (1/n)Σ_d F(P_d)e_n(-ad) = Σ_{b,c} F̂(b,c)·U(a,b,c)/n`. **Item #2 (v21)** gives
`|U(a,b,c)| ≤ C√p·polylog` **uniformly over (b,c)**, so
> `|Corr_F(a)| ≤ ‖F̂‖₁·C√p·polylog / n = p^{-1/2+o(1)}`   whenever `‖F̂‖₁ = ‖F‖_A(2D) = p^{o(1)}`.

So **any bounded-2D-Wiener readout of (x,y) decorrelates from `d` at the noise floor** — the exact
`glv_closure_theorem_v2` statement, extended from x-only readouts to joint (x,y) readouts by the
item-#2 bound. The 0.93 shadow requires the *aligned* `F̂(b,c)=conj(U)/|U|` (unbounded Wiener norm,
`‖F̂‖₁~p²`), i.e. `U` ⇒ the DLP. `[Grade: PROVED given KS + a 2D analog of Lemma W (‖F‖_A(2D)=p^{o(1)}
for lattice/sector readouts) — the same conditional structure as the original closure theorem.]`

## 2. `[VERIFIED-scope, p≤2089]` Empirical battery — cheap readouts sit at the floor

Metric `ρ(F)=max_{a≠0}|Corr_F(a)|/‖F‖₂` (normalization-free correlation with the leaking character;
`ρ=1` = perfect leak, needs `d`; random/cheap → `√(ln n/n)` floor).

| p | 127 | 433 | 1051 | 2089 |
|---|---|---|---|---|
| random floor | 0.207 | 0.104 | 0.084 | 0.059 |
| **best cheap readout** | 0.252 | 0.158 | 0.113 | 0.086 |
| best / floor | 1.22 | 1.52 | 1.34 | 1.46 |
| `ρ_best·√(n/ln n)` | 1.29 | 1.28 | 1.41 | 1.43 |

12 cheap readouts tested (y-sign/half, y mod 2/6, x mod 6, x-half, `e_p(x±y)`, `sign(xy)`,
`y-half·x-parity`, …). The **best** cheap readout is a bounded `~1.2–1.5×` the random floor, its
**absolute `ρ` decays to 0 as `√(ln n/n)`** (the `ρ·√(n/ln n)` row is flat) — the noise-floor
scaling. **No cheap readout captures a constant fraction of the shadow.** The **aligned** readout
(needs `U`) is 2–3 orders of magnitude above (v16: 0.93 in `‖·‖_∞` units). Matches §1.

## 3. Scope — the multi-key / joint-SET version stays OPEN

§1–§2 close the **single-key** cheap-partial question. **Not covered** (per `glv_closure_theorem_v2
§7`): a cheap readout of the **joint SET** `{[d_i]G}` of several exposed public keys — a
bilinear/multilinear sum, **outside KS as stated**. This is the genuine untouched frontier and is
exactly the stance principle "only a joint SET property survives the ECDLP scramble." **Do not read
§1–§2 as closing it.**

## Verdict & grades (locked)
- **No cheap partial of the single-key (x,y) shadow** — `[PROVED given KS + 2D-Lemma-W]` (§1) +
  `[VERIFIED-scope p≤2089]` (§2). Upgrades v18's thermodynamic/soft-mode closure of this lead to a
  direct closure-theorem statement (via item #2).
- **Multi-key / joint-SET cheap readout:** **OPEN** (outside KS). Not touched here.
- **Barrier stays computational** — the 0.93 shadow needs `U` ⇒ the DLP; security conclusion
  unchanged. Chains with item #2 (√p-bound) and item #3 (no soft mode): the single-key leakage
  question is now closed from three sides (magnitude bound, no metastable mode, no cheap partial).
- **Scope:** single-key, `p≤2089`; secp `p≈2²⁵⁶` untested empirically, covered by the cited bound;
  §1 conditional on KS + 2D-Lemma-W (empirically supported, not proved to full rigor).

## Files
Engine: `cheap_partial_shadow_v1.py` (analytic-size magnitudes, no key in path — carve-out per
`glv_closure_verification_v1.py`). Uses item #2's bound (`masked_structure_findings_v21.md`). Prior:
`xy_interference_U_v1.py` (the 0.93 shadow), `glv_closure_theorem_v2.md` (closure + §7 gaps),
`masked_structure_findings_v16/v18.md`.
