# Other Gaps — Analytic Promotion Memo (v1)

**Date:** 2026-03-03  
**Scope:** Gap 2, Gap 3, Gap 4 after insertion of `§17.20` route in `v11`.

---

## 1) Executive assessment

Most likely next analytic closure is **Gap 2**.

- Gap 2 already has exact geometry, exact kernel, affine TCP scaffolding, and strong finite-window coverage.
- The missing step is a single theorem promotion: prove the sharpened component-wise D.2 lower bound uniformly.

Gap 3 and Gap 4 are still analytically plausible, but both need a deeper structural theorem rather than a constant sharpening.

---

## 2) Evidence base (support only)

### Gap 2 (`|E_div|>=2`)
- `lrc_case2_multidiv_batch_summary_n13_d23_f123_m80_v1.md`:
  - 1155 templates, 20874 checks, 0 phi violations.
- `lrc_case2_multidiv_tcp_summary_n13_d23_f1234_tcp_affine_m420_v1.md`:
  - 3300 templates, 195448 target checks, 0 phi violations, 0 affine-LB violations.
- TCP rows show strictly positive slopes for all listed templates:
  - `a_F min = 21/2 > 0`, `M0 max = 340`.

### Gap 3 (composite-`n` general Case-2)
- `lrc_case2_d3_batch_summary_n8n9n10_v1.md`:
  - n=8,9,10 composite-safe batches, 0 violations.
- `lrc_case2_classwise_deficit_summary_v2.md`:
  - `LB_5` had 0 violations on exhaustive n<=6 and random n=7..12 samples.
- `lrc_case2_aggregate_deficit_summary_v1.md`:
  - exhaustive n=3..7 and random n=8..12 had 0 violations for `x0>=n-1`.

### Gap 4 (universal S3)
- Prime-n S3 theorem exists as a standalone proof artifact:
  - `lrc_s3_proof_prime_n_v1.md`.
- Open residual is composite/general canonical promotion (see `lrc_open_gaps_v1.md`, `lrc_case2_structural_necessity_chain_v1.md`).

---

## 3) Gap-by-gap analytic viability

### Gap 2 — **High viability / best next target**

**Current blocker:** theorem proof of
`D2-multidiv-sharp` (component-wise lower bound), not computational infrastructure.

**Analytic route likely to work:**
1. Prove exact component decomposition of `B_div` from interval intersections (`S = ∩_f S_f`).
2. On each component-band intersection, apply frozen-fixed partition + per-cell TM3 bound (same style as `§17.20` but componentized).
3. Sum component bounds with explicit constants to derive
   `B_safe >= floor(((n-1)/n)S - (2L0*nu + zeta))`.
4. Extract affine `(a_F,b_F)` and define `M0(F)` analytically.
5. Use existing finite `T(F)` checks only as bounded verification.

**Why this is realistic:** all required objects (`S,nu,zeta`, component intersections, affine rows) already exist in artifacts and are stable.

### Gap 3 — **Medium viability**

**Most promising route:** promote the classwise deficit chain to a theorem:
`LB_5(E) >= n-1` universally, where
`LB_5 = Σ_s N_s * max(0, n - UB_5(s))`.

This would yield `x0>=n-1>=phi(n)` directly.

**Risk:** this is a global structural inequality; current evidence is strong but still sampled for higher n.
A proof likely needs a nontrivial universal inequality on class multiplicity moments.

### Gap 4 — **Medium-low to medium viability**

Prime-n S3 argument is strong, but universal S3 needs a composite-compatible replacement for the prime anchor `z`-property.

**Candidate analytic direction:** gcd-stratified obstruction theorem on the event-path classes (from structural necessity chain), rather than anchor-only counting.

**Risk:** anchor membership/divisibility interactions are exactly the known failure mode; direct anchor generalization is brittle.

---

## 4) Recommended priority order

1. **Promote Gap 2 now** (highest probability, shortest path to theorem-grade result).
2. **Parallel draft for Gap 3 classwise-deficit theorem** (`LB_5` universal target).
3. **Gap 4 composite residual** only after Gap 2 theorem promotion lands.

---

## 5) Concrete theorem-first next steps

### Step A (Gap 2)
Draft and prove a new lemma chain:
- `G2.A` exact component-band decomposition,
- `G2.B` per-component frozen-fixed TM3 bound,
- `G2.C` aggregate sharpened D.2 bound,
- `G2.D` affine extraction and explicit `M0(F)`.

Then bind current TCP artifacts as support-only checks.

### Step B (Gap 3)
Formalize universal target lemma:
- `CD.5-uniform`: `LB_5(E) >= n-1` for all Case-2 tuples.

Prepare proof attempts via moment/Bonferroni constraints on `q_s(a)` under event-path realizability (not arbitrary class assignments).

### Step C (Gap 4)
Refactor S3 into:
- prime theorem (already proved),
- composite theorem candidate on gcd-stratified event classes,
without assuming anchor-only sufficiency.

---

## 6) Bottom line

Yes: at least one of the other gaps is analytically promotable now with computation only as support.
The strongest candidate is **Gap 2**.
