# RESULT — Testing the external review's IDEAS (not just its method)

**Date 2026-07-19.** An external review (GLM-class) of `POSITIVE_FINDINGS_MASTER_v3.md` proposed (a) a
"missed opportunity" — that `√p·ζ₆` Frobenius eigenvalues on the `χ₂(y)`-cover `C:w⁴=x³+7` are a *new
CM fingerprint* left un-assessed; (b) three next steps — run the chirality check, map the 0.93 shadow's
frequency support, test bit-level coordinate readouts. This session **tested the ideas**, with matched
controls, per the language + anomaly-drill rules. **Both testable ideas dissolved under the matched
control**; the third (frequency support) is set up and not yet run. No verdict of closure; every result
below is a bounded magnitude with power + scope. Signal-path arithmetic exact; float only in FFT
statistics ranked vs matched permutation nulls and in eigenvalue-angle sizes.

Artifacts: `mu6_cohomology_split_v1.{py,log}` (prior session), `mu6_cohomology_split_v2.{py,log}`
(prior session, pre-registered, **run this session**), `mu6_cohomology_sharpen_v1.{py,log}`,
`bit_readout_leak_test_v1.{py,log}`, `bit_readout_leak_matchednull_v2.{py,log}`.

---

## 1. The `mu6`-cohomology "missed opportunity" — geometric, not CM `[VERIFIED]`

**The review's particulars were confabulated** (traced against `mu6_cohomology_split_v1.log`): the
non-CM control was `x³+2x+5` (not `x³+x+1`), ran clean at all 9 primes incl. p=31, `EXIT 0`; the √-3
membership check was already computed on every row; the CM-vs-non-CM comparison completed. The
"√p·ζ₆ = CM fingerprint" claim is refuted at the object level: **at p=43 and p=79 a non-CM curve gives
the byte-identical `L_new` with the same ζ₆ angles.**

**The prior session had already self-corrected** and pre-registered the right refinement in
`mu6_cohomology_split_v2.py` (written, never run — no log). Running it this session:

- **P-A `[VERIFIED, 14/14 both curves]`:** `A_new` ordinary ⟺ `p≡1 mod 4`. The `√p·ζ₆` angles are the
  **supersingular** case, forced by `Q(i) ⊂ End⁰(A_new)` from the μ₄ automorphism `w→iw` — present for
  **any** cubic. Geometric, not a CM signal. (**P-C confirmed**: CM and non-CM ss rows overlap.)
- **P-B, sharpened and FALSIFIED as a clean fingerprint.** The committed prediction (CM has `√-3` in the
  `H¹_new` eigenvalue field at *every* ordinary prime; generic non-CM never) is **false**:

  | cover | `√-3 ∈` Frob field, ordinary p≤160 | `Q(ζ₁₂)`-split (v2, p≤109) |
  |---|---|---|
  | CM `x³+7` | **5/7** (fails p=73,157: field `= Q(i)`, deg 2) | 6/6 |
  | non-CM `x³+2x+5` | 3/7 | 5/6 |
  | non-CM `x³+x+1` | 3/7 | — |

  CM sits higher in both tests but **not cleanly and not significantly** at this sample (Fisher ≈ 0.6).

**Reading (bounded, no closure).** `A_new` has **geometric** CM by `Q(ζ₁₂)` `[PROVED from μ₁₂⊂Aut(C)]`
for the `j=0` cover — a real automorphism-level fact a generic cover lacks. But at the **per-prime**
level the Frobenius lands in a `p`-dependent subfield of `Q(ζ₁₂)` (sometimes just `Q(i)`, deg 2), so
neither the eigenvalue angle, the splitting field, nor `√-3`-membership is a **decidable per-prime CM
invariant**; the CM structure surfaces only as a **Frobenius-field density**. **Untested:** many more
ordinary primes to resolve the density gap (compute-bound: `F_{p³}` enumeration).

> **⚠ CORRECTION (2026-07-19, after user challenge).** The v1 text here originally read *"Bound-irrelevant
> regardless … this deflates the review's centerpiece at every level and does not touch ECDLP."*
> **That was dismissal-by-verdict — the exact negative bias this project bans**, applied to the one word
> that should never be waved off: **supersingular.** The `≤4√p` magnitude bound is angle-independent,
> yes — but "the ζ₆ is geometric supersingularity" is **not** a reason to close the thread. Supersingularity
> is the classical ECDLP lever (MOV / Frey–Rück), and **secp's `p ≡ 3 mod 4`**, so the cover's new
> surface `A_new` is supersingular **at secp itself** (E ordinary, `A_new` supersingular, `A_new`
> embedding degree 3 ⇒ its internal DLP reduces to `F_{p³}`). The ζ₆-is-not-CM finding stands; but it is
> a **pointer to a supersingular, easy-DLP object in the cover's Jacobian**, which is the opposite of
> irrelevant. Mapped as a lever candidate in **`RESULT_supersingular_cover_lever_v1.md`**.

## 2. Bit-level coordinate readouts — a null mismatch, corrected `[VERIFIED artifact / EMPIRICAL scoped null]`

Idea (review Rec #3 / master X.1 & VIII.3): cheap **non-μ₆-covariant** coordinate bits of `[d]G` leak
`d`. These sit in the unbounded-degree GAP (V-3), the master's own untested complement. Curve
`E:y²=x³+7`, `p=50227`, `n=#E=50497` prime; bijection `d↔[d]G`; statistic = single-frequency
concentration `C(F)=max_{a≠0}|F̂(a)|/rms`, ranked vs a value-permutation null. **PLANT fires** (z=755;
detection floor ~1% mixing, z=13), **RANDOM null** (z=−0.97).

- **v1 gave a false "ESCAPE"**: x&1 z=5.80, hi(x) 5.33, hi(y) 7.91 — **but every readout showed
  rank-p = 0.0033** (the real statistic beat all 300 nulls), a *systematic* shift = the tell of a
  symmetry-mismatched null, not per-readout signal.
- **Mechanism:** `x_{−d}=x_d` exactly (verified) ⇒ `x&1, hi(x), x mod 4, x&15` are **even in d**;
  `y&1, hi(y)` complemented-even. The value-permutation null destroys that μ₂ symmetry. **= master
  retraction #6.**
- **Matched null** (permute `{d,n−d}` orbits, preserve even/odd symmetry + value multiset) collapses it:

  | readout | z (plain shuffle) | **z (matched)** | rank-p (matched) |
  |---|---|---|---|
  | x & 1 | 6.06 | **0.57** | 0.23 |
  | hi(x) | 5.89 | **0.44** | 0.26 |
  | x mod 4 | 4.47 | **−0.43** | 0.62 |
  | y & 1 | 3.38 | **−1.05** | 0.87 |
  | hi(y) | 9.33 | **2.34** | 0.03 |

**Scoped result `[EMPIRICAL]`:** no single-frequency concentration above the symmetry-matched floor for
these six coordinate-bit readouts, on `E:y²=x³+7` at `n=50497`, `z_matched ∈ [−1.05, 2.34]` (all below
the `z≥5` escape; plant power reaches ~1% mixing). Per the language rule this is a bounded magnitude in
one statistic on one curve, **not** "bits don't leak." **Untested and explicitly out of scope:** the
distributed / effective-support (`N_eff`) channel (a bit may leak multi-frequency, which single-peak
concentration cannot see); larger `n`; other primes; joint multi-bit / multi-point readouts; `2²⁵⁶`.

## 3. The chirality check (review Rec #1) — void, already `[VERIFIED]`

`RESULT_twist_gauge_covariance_v2.md` §5.2 (this session, earlier) proved the `π_p↔π̄_p` action trivial
(`X∈ℤ` conjugation-fixed ⇒ `σ'=σ` pointwise), so `sign(FLD)` cannot flip. The review read master v3,
which predates that audit. Superseded — do not run.

## 4. Net + the one idea still open

Two substantive ideas tested; both apparent positives were **artifacts caught by the matched control**
(the bit "ESCAPE" = μ₂-symmetry null mismatch; the CM "fingerprint" = geometric supersingularity + a
non-separating density). This is the symmetric-rigor loop, and it is a genuine result: the review's
Path-B reduction leads (bit readouts) and its cohomology centerpiece do not survive at the tested
scale, for reasons that are stated (μ₂ symmetry; geometric μ₄; the bound is angle-independent).

**Still open — the master's own #1 lead, not yet run (review Rec #2):** the **frequency-support
pattern** of the 0.93 joint-(x,y) shadow — *which* `(b,c)` carry the alignment and their μ₃/GLV grading,
not the scalar magnitude (VIII.1 / X.1). This is the "right basis not yet found" place. It needs a
proper `experiment-designer` pre-registration (statistic on the support set, matched null, power) before
running; it is the correct next test.

## 5. Suggested master update (next compile, via compile-diff)
- §X (new item) **`mu6`-cohomology / χ₂(y) `H¹_new`** → `bounded-by RESULT_external_review_idea_tests_v1`:
  ζ₆ angles geometric (P-A/P-C, VERIFIED 14 primes); `A_new` geom-CM by `Q(ζ₁₂)` `[PROVED]` but no
  decidable per-prime fingerprint (5/7 vs 3/7); bound-irrelevant.
- §X.1 non-covariant cheap readouts → add `bit-readout single-freq concentration at matched floor,
  n=50497, one curve [EMPIRICAL]`; keep `N_eff` / larger-n / multi-bit OPEN verbatim.
- Retraction ledger → add: *"bit-readout 5–9σ 'ESCAPE' → μ₂-symmetry null mismatch (x_{−d}=x_d), a
  re-occurrence of #6; collapses to z≈0 against the {d,n−d}-orbit-matched null."*
