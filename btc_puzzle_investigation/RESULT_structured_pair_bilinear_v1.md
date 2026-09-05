# RESULT — Structured-pair (diagonal `v=k·u`) bilinear panel: KS-covered at fixed `k`

**Date 2026-07-19.** Frontier §X.7 (GLM "frontier F": *"stop testing random pairs; test structured
pairs `Q=[2]P,[3]P`, sextant-aligned, at `k=32,64` — if cross-terms fail to cancel that is a bilinear
leak that escapes KS"*). Pre-registered `PREREG_structured_pair_bilinear_v1.md`. Script
`structured_pair_bilinear_v1.py`. Exact-integer state path; float only in FFT/phase magnitudes
(carve-out). Seed 20260719. Scope: `b=7`, `p ≤ 2¹⁷`.

## The primary claim is ANALYTICAL — the witness only confirms it

`bilinear_closure_proof_v1.md` (Theorem B) already bounds the **full** two-point sum over independent
`(u,v)`: `S(a,b)=Σ_{u,v} A(P_u)B(P_v)C(P_{u+v})e_n(au+bv)`, `|S|/n² = O(p^{−1/2})`. The **structured
pair** is the **diagonal slice** `v = k·u` — a measure-zero restriction Theorem B does not bound
directly. Setting `v=k·u` collapses it to the single-index sum
`Ĉ_k(a') = Σ_u A(P_u)B(P_{ku})C(P_{(1+k)u}) e_n(a'u)`.

**Reduction:** `[k]` is the degree-`k²` scalar-multiplication rational map, so
`F_k(P_u)=A(P_u)B(P_{ku})C(P_{(1+k)u})` is a **single** bounded-degree rational readout on `E`
(pole order `D_k ≈ 2(1+k)²`). The KS single-sum bound then gives
`max_{a'}|Ĉ_k(a')| ≤ (2D_k+1)√p ≈ c·k²·√p`, so the normalized correlation
`C_k = (1/n)max_{a'≠0}|Ĉ_k| = O(k²·p^{−1/2}) → 0` at fixed `k`. **Structured pairs at fixed `k` do
NOT escape KS.** The GLM intuition ("structured pairs escape") is the opposite of the truth: making
`Q=[k]P` *structured* turns the two-point object into a *single* bounded-degree readout, which is
exactly the shape KS bounds.

## Witness result — CONFIRMS-REDUCTION (all four pre-committed signatures hold)

Main grid, `p=6007`, `n=6163` (NULL-A floor `0.0388 ± 0.0027`; analytic `√(ln n/n)=0.0376`;
`p^{1/4}=8.8`):

| k | type | D_k | C_k | z vs floor | ceiling C_k·n≤(2D_k+1)√p | cell |
|---:|---|---:|---:|---:|:--:|:--|
| 2 | generic | 18 | 0.0365 | −0.84 | ok | ceiling-in-power |
| 3 | generic | 32 | 0.0377 | −0.40 | ok | ceiling-in-power |
| 5 | generic | 72 | 0.0452 | +2.34 | ok | ceiling-in-power |
| 8 | generic | 162 | 0.0402 | +0.53 | ok | floor-only |
| 16 | generic | 578 | 0.0432 | +1.62 | ok | floor-only |
| 32 | generic | 2178 | 0.0357 | −1.11 | ok | floor-only |
| 64 | generic | 8450 | 0.0388 | +0.00 | ok | floor-only |
| −1 | μ₆ | 3 | 0.0370 | −0.66 | ok | ceiling-in-power |
| λ | μ₆ | 3 | 0.0393 | +0.19 | ok | ceiling-in-power |
| λ² | μ₆ | 3 | 0.0393 | +0.19 | ok | ceiling-in-power |

1. **Flat at the floor, `k`-independent.** Every `C_k` sits in the NULL-A cloud (`z ∈ [−1.1, +2.3]`,
   no escape — the escape threshold is `z≥5`). Exactly Correction 1: Parseval pins `avg|Ĉ_k|²=n`, so
   the generic bounded-degree readout does NOT saturate its `k²` ceiling — it sits at the floor,
   independent of `k`. (The lone `k=5` blip, `z=+2.34`, rank 7/200 ≈ p 0.035 uncorrected, does not
   persist: `k=8…64` are back at the floor.)
2. **Ceiling never violated** (`C_k·n ≤ (2D_k+1)√p` holds every row); for `k≤5`/μ₆ the ceiling is
   *in-power* (non-vacuous), for `k=8…64` it is vacuous at this `p` (`FLOOR-ONLY`, correctly tagged) —
   the floor test is still matched and valid there.
3. **μ₆-aligned collapses to degree 3** (Correction 2). `k∈{−1,λ,λ²}` give `C_k ≈ 0.037–0.039`, sitting
   at the **NULL-C plain-degree-3 floor** `0.0382 ± 0.0020` — no `k²` inflation, as predicted for an
   automorphism (`x_{λu}=βx_u` exactly). `λ` and `λ²` are identical (complex conjugates).
4. **`p^{−1/2}` decay** (fixed `k=2,3` across the ladder `p=127→111109`): `C_2 ~ n^{−0.46}`, NULL-A
   floor `~ n^{−0.44}` — both the KS floor exponent `−½`, with `C_k/floor ∈ [0.89,1.12]` at every `p`.
5. **Controls fired.** NULL-B (random multiplier, same structure) `0.0391` = same floor ⇒ the *values*
   `k=2..64` are not special. Planted control FIRES at `ρ=4·floor` (rank-1, recovered 0.90×) and
   `ρ=0.10` (0.85×), correctly silent at `ρ=0`. Parseval guard `Q_k≈1` at every cell (no halt).

> **Structured pairs `Q=[k]P` at fixed `k` are KS-covered at the tested scale.** `C_k` sits at the
> degree-matched random-readout floor `≈√(ln n)·p^{−1/2}`, `k`-independent, decaying `p^{−1/2}`,
> bounded by the KS ceiling `≈c·k²·p^{−1/2}`, μ₆-aligned at the degree-3 floor — on `E:y²=x³+7`,
> `p∈[127, 111109]`, `k≤64`, planted power `ρ_min ≈ 4·floor`. **§X.7's structured-pair sub-object is
> closed given KS via the bounded-degree diagonal reduction, for fixed `k` at this scale.**

## What stays OPEN (named residual — not a closure of ECDLP)

- **(i) `k ≳ p^{1/4}`** (`= 2⁶⁴` at secp). The KS ceiling `c·k²·√p` is only non-vacuous for
  `k ≪ p^{1/4}`; a multiplier growing with `p` is a **growing-degree** readout = the separate
  **unbounded-degree GAP** (§X frontier / V-3). This witness has zero power there (the `k=16,32,64`
  cells at these small `p` are already ceiling-vacuous, floor-only).
- **(ii) the `m=1` aligned readout** `F̂=conj(Ĉ)/|Ĉ|` — needs `Ĉ` itself ⇒ all `x_d` ⇒ **the DLP**.
- **(iii) `p = 2²⁵⁶`** — SCALE BANNER; zero power here.

## Disclosed deviations from the prereg + one code fix

- **D1 — NULL-A degree cap.** Prereg §3 specifies NULL-A pole order `≈D_k`; for `k=64`, `D_k=8450`,
  and evaluating a degree-8450 random polynomial at every `u` over 200 reps is infeasible. Capped
  NULL-A at degree 8. **Justified and validated by Correction 1** (the floor is degree-independent):
  NULL-A (deg-8) `0.0388`, NULL-B (random-multiplier, varying high degree) `0.0391`, NULL-C (deg-3)
  `0.0382`, and analytic `√(ln n/n)` `0.0376` **all agree to ~3%** — three different-degree nulls give
  the same floor, empirically confirming degree-independence and the cap. The `k²` factor is a
  *ceiling* property (checked separately, never violated), not the floor.
- **Code fix (not a spec deviation).** The first run's planted-control check compared the peak to
  frequency `1` while the injected `exp(−2πi·u/n)` term lands at `n−1` (FFT sign convention); the
  magnitude was recovered correctly (0.96×) but `peak_rank1` read False → a spurious VOID. Fixed the
  inject sign so the plant lands at `a₀=1`; control then fires as specified. The real-data result was
  identical before and after (the plant is a separate positive control).

## Bearing on the GGM question

This **does not move outside GGM at tested scale — and it turns an OPEN frontier into a proof-given-KS
closure.** The group law (point addition) is the one operation GGM hides; the structured-pair panel
was the sharpest place a concrete-arithmetic handle on it could have lived. It does not: at fixed
multiplier the addition-coupled readout is a bounded-degree single readout that KS pins to the
`√p` generic floor, `k`-independent. The residual where an outside-GGM lever could still exist
narrows to exactly the unbounded-degree corner (i) and the DLP itself (ii) — i.e. it collapses back
onto the *already-known* open frontiers, carrying no new structure past them.

## Suggested master update (next compile, via compile-diff)
§X.7 structured-pair clause → `bounded-by RESULT_structured_pair_bilinear_v1 (given KS, fixed k,
p≤2¹⁷)`; keep residual (i)/(ii)/(iii) OPEN verbatim. Reconciles X.7 with `bilinear_closure_proof_v1`
(which closed the full off-diagonal two-point sum; this closes the diagonal slice).
