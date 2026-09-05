# Next-session prompt v2 — the untested residue (2026-08-01)

**Supersedes nothing.** Read `NEXT_SESSION_PROMPT_2026-07-31_v1.md` first for orientation, the
counter-prior, and the disciplines. This file adds **only the items that were specified, claimed,
or implied during 2026-07-30/31 and never actually measured.**

> **EXPLICITLY OUT OF SCOPE HERE:** the C-side pooled-tilt lead (`inv`, `pow7`). Settled in
> `RESULT_cside_pooled_tilt_settlement_v1.md`; do not re-open it in this thread.
>
> **ALSO OUT OF SCOPE, PERMANENTLY:** anything whose matched null is drawn from a generator pool,
> and anything taking the 82 solved keys as its object. **The tell: check the NULL's provenance
> before the curve's.** If the null comes from `constructed_keys_*.csv` (known-MT19937), the test
> is a generator test whatever the instrument. Scalars are to be **constructed at any bit-length,
> in any quantity** — the 82 are 82 arbitrary integers and impose a sample ceiling that does not
> exist. (Two scope violations of this shape occurred on 2026-07-31; both are recorded and
> withdrawn — `PREREG_e3_twist_and_cm_controls_v1.md`, and §4 of
> `ANALYSIS_correlation_hierarchy_weil_closure_v1.md`.)

---

## A. The 120° census certificate — a published grade rests on an unproved direction

**Status: specified, ring corrected, NEVER IMPLEMENTED** (`grep` confirms no script computes it).

`CORRECTION_120deg_census_certification_direction_v1.md`: the census computes
`min_l g_l` over 5 modular embeddings and reports `g = 2`. But reduction can only **raise** gcd
degree, so `min_l g_l ≥ g_true` — a computed `0` certifies `g_true = 0` exactly, a computed **`2`
certifies only `g_true ≤ 2`**. Witness: the gate's own PLANT-B (true `g₃ = 0`) reads `2` at
`l = 13` and `l = 37`.

**The repair, fully specified, needs implementing:**
- Work in `ℤ[ζ_M] = ℤ[y]/Φ_M(y)`, `M = lcm(N,k)`, with `ζ_N := y^{M/N}` and `ζ_k := y^{M/k}`
  **pinned jointly** (independent choices are not an embedding when `gcd(N,k) > 1`).
- ⚠ The first revision of that CORRECTION named `ℤ[x]/(Φ_N(x), Φ_k(x))` — **the ZERO RING**
  (`Res(Φ_N,Φ_k) = 1` in every case in scope, so the ideal is `(1)`). It would have passed
  unconditionally. Do not reuse it.
- ⚠ `reduce_phi_prime` (`audit_n1_vsign_v2_core.py:198`) reduces mod `1+x+…+x^{n−1}`, which is
  `Φ_n` **only for `n` prime**. Rewrite for general `Φ_M`.
- **State and use the conjunction:** `Res_T = 0 ∧ S₁ = 0` gives `g ≥ 2`; `min_l g_l` gives
  `g ≤ 2`. **Neither alone gives `g = 2`.**

**Payoff:** promotes the 120° law's 2464 cells from `[VERIFIED]` back to a genuinely exact claim.
Cheap — pure algebra on polynomials already computed.

## B. Revive the cross-`j` Aut-contrast — the ONE mechanism test that never ran

**Status: two preregs written, gate-audited (v1: 10 defects; v2: 20 defects), ARMS NEVER RUN.**

`PREREG_jclass_120deg_discriminator_v2.md` asks whether the `ζ₃` lock is present on curves whose
`Aut` lacks `μ₃` — a **necessary condition** for any mechanism routing the `ζ₃` through the
curve's automorphism/CM structure. It died three times, each deeper than the last:

1. `y² = x³ + Ax` contains `(0,0)`, 2-torsion ⇒ `2 | #E` always ⇒ **never prime order**
   (29,184 `(p,A)` pairs, zero odd).
2. `j = 1728` is **supersingular** at `p ≡ 3 mod 4` ⇒ cofactor-2 only at `p ≡ 1 mod 4` ⇒ 0/22
   frozen primes met the arm rule.
3. `b₁ = 0` — which the whole 4-dim reconstruction rests on — is **derived from `χ₄^p = χ̄₄`,
   valid only at `p ≡ 3 mod 4`**. The arm exists exclusively where its own premise is unavailable.

**The revival, and it dissolves all three:**
- **Drop the prime-order requirement.** It was a convenience of the cell construction, never
  mathematics. `E(F_p) ≅ ℤ/N` with `N = h·n'` composite works: `root_of_order` already handles
  composite orders (the D5 fix), and cells are `±`-cosets. Measured availability: `j=1728` curves
  with cofactor `h ≤ 8` exist at 11 of 12 primes tested (18–90 curves each; `h ∈ {2,4,8}`), and
  `χ₂(−A) = −1` selects the **cyclic** `ℤ/2n'` branch (21/21), keeping the index 1-dimensional.
- **MEASURE `b₁` instead of deriving it.** At `p ≡ 1 mod 4` compute `b₁` from `#C(F_p)` directly
  rather than assuming the `μ₄`-block argument. This is the step that unblocks (3).
- Note `j = 0` can **never** have cofactor 2 (rational 2-torsion ⇒ `B = −c³` ⇒ `x³−c³` splits since
  `−3` is a square exactly when `p ≡ 1 mod 3`, which is when `j=0` is ordinary ⇒ full `ℤ/2×ℤ/2`
  ⇒ `4 | #E`). So the arms **cannot** be matched on cofactor — run JGEN at both cofactors as the
  internal control and declare the comparison void if they disagree.

**Read v2's own defect list before rebuilding** — especially **F-C fires vacuously on an empty
arm** (universally quantified over zero cells, with F-EMPTY ordered last), which would have emitted
a mechanism verdict from no data. Order F-EMPTY first.

**Relevance check first:** `NEXT_SESSION_PROMPT_..._v1.md` records the commutative-CM mechanism as
REFUTED and SL₂-on-tensor as surviving. Decide whether a cross-`j` contrast still discriminates
against the *surviving* mechanism before spending on it — if it does not, retire B explicitly
rather than leaving it dangling.

## C. The interval channel — objects never run

Context: `RESULT_interval_cubic_structure_v1.md`, `RESULT_interval_multireadout_v2.md`. Constructed
scalars, secp's own `p`, unlimited `N`. Field and group-law difference sets are null at ≈1.4% /
≈4.3% marginal excess and 6% coherent block. What was **not** run:

1. **The swap-invariant SUM object `x(P_i + P_j)`.** `ANALYSIS_diffset_readout_parity_void_v1.md`
   establishes that on a **negation-closed** index set (field differences) every odd character
   (`χ₂`, `χ₆`) is ill-posed unordered and identically zero symmetrized — so `χ₃` is the only
   nontrivial readout there. The sum-set is swap-invariant, so **the full `χ₂`/`χ₃`/`χ₆` family is
   legal on it.** This is the readout axis that actually exists. **Never run.**
2. **`χ₂` and `χ₆` on the GROUP-LAW difference.** Also legal (`x(−Q) = x(Q)` removes the sign
   ambiguity), and never read because the run mis-tagged them `[parity-void]`. The file's scope
   correction is recorded; the numbers were never taken.
3. **The `E₆` control debt (BLOCKING for item 2).** C-NEG on the group arm gave `E₆` at the 99.7th
   percentile. Same single-draw artifact class as A below — **recalibrate under the `n ≥ 20` rule
   before using `E₆` on that object.**
4. **`M = 2000`.** Detectable marginal excess falls like `1/M` (≈0.3%) and the coherent-block floor
   like `1/√M` (≈2%). gmpy2 2.3.1 is installed; with the pool-table precomputation this is minutes,
   not an afternoon.
5. **Triples / higher-order objects** on the same sets, and **non-dyadic intervals** / non-uniform
   sampling within an interval.

## D. Standing repairs — apply to everything above

- **`C-NEG` must be `n ≥ 20` independent draws with percentiles checked for uniformity.** As
  specified (ONE draw vs the 95th percentile) it false-alarms **5% of the time under a correct
  null** — it voided the spectral run at 96.0, and 20 draws then gave **0/20 above the 95th**.
  This defect is in every result of the interval line. Verdicts survive (a false-alarm-biased
  control cannot manufacture a false *pass*), but do not carry the specification forward.
- **Check readout parity × index-set parity before running any probe.** Product odd ⇒ identically
  zero or ill-posed ⇒ zero information, and no sample size fixes it. This is the 4th logged
  instance; it caught a would-be false positive (`k=200`, `E₆ = 536493` vs a 99th of 353761) in
  the very run that established it.
- **Measure `pow` cost before sizing any job.** Assumed ~6 µs, measured **84.7 µs** — a 14× error
  that turned an 8-minute plan into an 85-minute one, killed at 70 minutes with no output.
- **Precompute the pool difference table once**; the null and the greedy plant then cost nothing.
  Field pass went 85 min → 114 s.
- **Never pipe a long run through `tail`** — it buffers to EOF. Use `-u` and a log file.
- **OOS retest before naming anything.** The `k=128` group-arm fire (99.4 pctile) died 0/5 on fresh
  seeds; with 7 arms at a 99th threshold, `1 − 0.99⁷ ≈ 6.8%` of runs produce one by chance.

## E. Lower priority / carried

- Non-archimedean (p-adic) Weil-number purity — item 2's true residual (archimedean is done).
- `d ↦ d^k` for `k ∉ {−1, 7}` — `inv` is null and `pow7` is an unreplicated sub-detection; the
  classification in `ANALYSIS_correlation_hierarchy_weil_closure_v1.md` §3 says the admissible
  family is `k ≡ ±1 mod 6`, so `k = 5, 11, 13` are the untried members. Low priority.
- **The proof, not a measurement:** that monodromy forces the 120° pairing uniformly (#26). The
  mechanism side is measurement-complete; this is what actually remains.

---

## Method note carried from 2026-07-31

The two things that caught real errors were **mechanical**, not care: a control firing on a bad
plant, and the `experiment-designer` gate. Reasoning that never reached an artifact was lost twice
in one session (the pool-table optimization; the group-law parity exemption). **Bank findings to
files as they are derived, not at the end.**
