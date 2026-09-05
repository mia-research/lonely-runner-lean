# PREREG v1 — is `v = sinθ₁·sinθ₂ ≤ 0` for the N1 twisted sheaf?

**Date:** 2026-07-25 · **Written BEFORE any multi-prime data is collected.** The only `v` values seen so
far are the 6 unforced cells already reported (`p=13`, `p=43`) in
`RESULT_n1_phase_inequality_reduction_v1.md` §5/§5b; those are **in-sample** and are explicitly NOT
counted as confirmation below. Exact integers in the signal path; no float threshold decides a verdict.

**Why it matters.** `RESULT_n1_phase_inequality_reduction_v1` §3 proves (algebra):
`v ≤ 0 ⟹ |sinθ₁+sinθ₂| ≤ 1 ⟹ S_y ≤ 2`, and `v ≤ 0 ⟺ e₂ ≥ −2p` where `e₂` is the `t²` coefficient of
`L(C,t,χ)`. So `v ≤ 0` is a **sufficient route** to the single open inequality of the N1 story.

---

## 1. The statistic, and the instrument that makes it cheap

For each prime `p` (with `#E(F_p) = n` prime) and each `a ≠ 0`:

- `P₁(a) := Σ_i αᵢ = −(twisted sum over F_p)` — the record's `V(a)`, cost `O(p)`.
- `P₂(a) := Σ_i αᵢ²` — the same twisted sum over `F_{p²}`, cost **`O(p²)`**.
- Newton: `e₂ = (P₁² − P₂)/2`. Then from the proved dictionary `e₂ = −2p − 4p·v`:

> **`v = −(e₂ + 2p)/(4p)`,  and the test is `v ≤ 0` ⟺ `e₂ ≥ −2p`.**

**This avoids the eigenvalue solve entirely.** The record's instrument is `O(p⁴)` (D1: `p≥61` exceeds
budget); `O(p²)` reaches `p` in the thousands. **That is the whole point of this design.**

## 2. Machinery controls — run BEFORE any new prime, and required to pass

- **M1 (cross-validation against the expensive instrument).** At `p = 13` and `p = 43`, the `O(p²)`
  route must reproduce the `v` values already obtained from the `O(p⁴)` eigenvalue solve
  (`−0.7300` at `p=13`; `−0.1451/−0.5977/−0.6788/−0.6976/−0.7295` at `p=43`), to `1e−9`.
  **Fail ⇒ the cheap instrument is wrong and the sweep does not run.**
- **★ M2 (PLANTED POSITIVE — the control the previous work lacked).** Construct a synthetic eigenvalue
  4-tuple with `|αᵢ| = √p`, closed under `α↦−ᾱ`, and **`v > 0` by construction** (e.g.
  `sinθ₁ = sinθ₂ = 0.6 ⇒ v = +0.36`). Feed its power sums `P₁, P₂` through the *same* extraction code.
  **Required: the pipeline reports `v = +0.36` (to `1e−9`), i.e. it CAN report a positive `v`.**
  Without this, a sweep returning "all `v ≤ 0`" is uninterpretable — exactly the defect flagged in
  `RESULT_n1_phase_inequality_reduction_v1` §0a.
- **M3 (degenerate/forced check).** `e₃ = −p·e₁` and `e₄ = p²` must hold in the reconstructed `L` at
  every tested `(p,a)`; these are the record's independently verified forced identities. A violation
  means the parametrization — not the claim — is wrong.

## 3. Arms (only after §2 passes)

All primes `p` with `#E(F_p)` prime, `p` in a **pre-frozen** list: the smallest 40 such primes above
`100`, plus the smallest 10 above `2000`. Both strata reported separately.
**Stratify the report by `p mod 4`** (`sin` vs `cos` form) — secp is `p ≡ 3 mod 4`, so that stratum is
the one that matters and must be reported on its own, never pooled.

For each prime record: `min_a v(a)`, `max_a v(a)`, `#{a : v(a) > 0}`, and `v` at the maximising `a`.

## 4. Pre-committed outcomes (all four are legitimate)

1. **`max_a v ≤ 0` at every prime, both strata** ⇒ `v ≤ 0` is `[VERIFIED — out-of-sample, N primes]`,
   and the route to `S_y ≤ 2` stands as a **conjecture with a proof-shaped target** (`e₂ ≥ −2p`).
   **It is still not a proof** — no promotion of `S_y ≤ 2` follows.
2. **Any prime with `v(a) > 0` and `|u| ≤ 1` still holding** ⇒ **the ROUTE is dead, the inequality is
   NOT refuted** (`v ≤ 0` is sufficient, not necessary — §3 of the RESULT). Report as: route closed,
   inequality untouched. **This is a real and useful outcome, not a failure.**
3. **Any prime with `|u| > 1`** ⇒ that would refute `S_y ≤ 2` itself, contradicting 120 primes of
   prior verification ⇒ **suspect the instrument first**; re-run M1/M3 before reporting anything.
4. **`v → 0` behaviour at the maximising `a`** is recorded as EXPLORATORY only — the record already
   grades the analogous convergence question **R-INDET**, and this design has no power to resolve it.

## 5. Falsification

The claim "`v ≤ 0` always" is falsified by **a single** `(p,a)` with `v > 0` surviving M1/M3. No
aggregate statistic, no p-value: this is a deterministic universal claim, so one counterexample decides
it. Correspondingly **no multiple-comparison correction applies**, and **counts are not evidence of
strength** — `N/N` primes passing is a scope statement, not a significance claim.

## 6. Scope, stated in advance

- `v ≤ 0` is **sufficient, not necessary** for the target inequality. Outcome 2 above is therefore not a
  refutation of anything except this route.
- All primes here are `O(10²–10³)`; **secp is `2²⁵⁶`**. Per the record's banner (#5), no measurement at
  this scale has power against structure at secp. This tests a *proposed general law*, and its value is
  as a proof target, not as evidence about secp.
- The `p ≡ 1 mod 4` stratum uses `cos`, not `sin`; it is reported but is **not** secp's class.

## 7. Deviations file: `PREREG_n1_v_sign_sweep_v1_DEVIATIONS.md`, created at the first deviation.
