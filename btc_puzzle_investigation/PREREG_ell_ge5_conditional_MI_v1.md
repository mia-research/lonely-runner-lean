# PREREG v1 — ℓ≥5 CONDITIONAL mutual information `I(j;k | ideal data)`

**Date:** 2026-07-25 · Pre-registered BEFORE any conditional statistic touches the frozen arms.
Exact integers for the number theory; MI / targeted MI are monotone statistics ranked against exact
permutation nulls (project float rule satisfied — no float threshold decides a verdict).

**Target = the one blind spot the marginal probe pre-committed it could not see.**
`RESULT_ell_ge5_mutual_information_v1.md` §4 / `PREREG…v2` N4 state, frozen before data: *a marginal
`I(j;k)`-null does not exclude `I(j;k | t,v,U) > 0`; an ℓ≥5 bridge that is purely conditional on the
ideal data would be invisible to marginal MI.* This probe builds the instrument for that alternative.

---

## 0. Objects (identical to the marginal probe — same `build_arm`, same freeze convention)

For a prime-order CM instance `(p, n)` on `D = −3` (`j=0`, secp's discriminant), one uniformly-chosen
prime-order twist per `p` (rule N5, unchanged):

- `t = p + 1 − n` (Frobenius trace), `U = |t − 1|`, and `4p = t² + 3v²` ⇒ `v = isqrt((4p − t²)/3)`.
- `j = expo(p, n, ℓ, ζ_n)`  (`χ_ℓ(p mod n) = ζ_n^j`),  `k = expo(n, p, ℓ, ζ_p)`  (`χ_ℓ(n mod p) = ζ_p^k`).

**Forced degeneracy (checked in-script before this freeze):** the sampler requires `p ≡ n ≡ 1 (mod ℓ)`,
so `t = p+1−n ≡ 1 (mod ℓ)` for **every** instance ⇒ `t mod ℓ` carries no information. The first varying
ℓ-adic digit of the ideal data is therefore

> **`w := ((t − 1)/ℓ) mod ℓ`**  — the direct generalization of the ℓ=3 mediator.

Justification (pre-registered, not fished): the ℓ=3 law **(E3)** `e(π̄′) − e(ν′) ≡ (t−1)/3 (mod 3)` is
**`[VERIFIED — 12000/12000]`, not proved** (`RESULT_bridge_mechanism_and_constant_v1` says so explicitly),
and `c₃ = s·(e(π̄′)−e(ν′))`, so the mediating ideal residue at ℓ=3 is `(t−1)/3 mod 3`. Replacing `3→ℓ`
gives `w` above. NOTE: this fixes the mediator by pre-commitment; whether an ℓ≥5 analogue of E3 holds is
the hypothesis under test — "no free choice" overstates (the mediator is chosen, the law is not given).

---

## 1. Statistics (two, both choice-free; primary + co-primary)

Let `d_b := (j − b·k) mod ℓ` for `b ∈ (ℤ/ℓ)*` (the choice-free family of shift residuals from N1).

- **PRIMARY — stratified conditional MI (omnibus, catches non-shift dependence):**
  `Îc := Σ_{w} (N_w / N) · MI_w(j ; k)`, where `MI_w` is the plug-in MI of `(j,k)` restricted to the
  stratum `{instances with mediator = w}`. This **is** the sample `I(j;k | w)`.
- **CO-PRIMARY — targeted conditional shift (fewer df, more power for a shift bridge):**
  `Tc := max_{b ∈ (ℤ/ℓ)*} I( d_b ; w )` — does any choice-free alignment of the shift get predicted
  by the mediator `w`.

**Choice-freeness (M0, to be verified in-script before any arm):** `Îc` is invariant under independent
unit relabelings `j→a·j`, `k→c·k` (`a,c ∈ (ℤ/ℓ)*`) because within-stratum MI is bijection-invariant and
`w` is an arithmetic quantity untouched by the root-of-unity choice. `Tc` is invariant because relabeling
permutes which `b` attains the max, which the permutation null recomputes. R1 fix inherited: at ℓ=3 the
only unit is 2, relabelings drawn from `(ℤ/ℓ)*` only.

## 2. Nulls (two DISTINCT permutation nulls — one per statistic, stated exactly)

- **For `Îc` (within-stratum shuffle):** independently within each `w`-stratum, permute `k` against `j`.
  Preserves each stratum's marginals of `j` and of `k`; breaks only the within-stratum `j↔k` association.
  This is the classical stratified conditional-independence permutation test. `H0`: `j ⊥ k | w`.
- **For `Tc` (mediator shuffle):** hold the `(j,k)` pairing (hence every `d_b`) fixed; permute the
  `w`-labels across instances. Breaks `d↔w` while preserving both marginals. `H0`: `d_b ⊥ w ∀b`.
- Both: `sh = 20000` shuffles, exact count `p = (#{null ≥ obs − 1e−12} + 1)/(sh + 1)`.

## 3. Machinery controls (test the STATISTIC, not the frozen data — run BEFORE arms, pre-approval-safe)

- **M0 (choice-freeness):** `Îc`, `Tc` bit-identical under all unit relabelings. **Pass = required.**
- **★ Mc+ (the load-bearing synthetic-positive — the analogue of the marginal probe's M1):**
  draw `w ~ U(ℤ/ℓ)`, `k ~ U(ℤ/ℓ)` independent, set `j := (k + w) mod ℓ`. Then **marginally `j ⊥ k`**
  (marginal `MI(j;k)` p ≈ 1 — the completed probe is BLIND to this coupling) **but** `Îc` and `Tc` must
  fire (`p ≤ 1e−3`). This is the decidable proof that the conditional instrument sees the uniform-shift
  bridge the marginal one cannot. **Report the marginal-MI p on the SAME synthetic data beside it.**
- **Mc− (synthetic-null):** `w, j, k` all independent uniform ⇒ `Îc`, `Tc` null (`p` not small).
  Shows the conditional stats do not fire on structureless noise.
- **R2 power (injection):** partial conditional shift — `j := (k + w) mod ℓ` w.p. `s`, else `j ~ U`.
  `s = 0` is the null (must not fire). Report, per ℓ ∈ {5,7,11,13} at the arm `N`, the smallest `s`
  detected at ≥ 80% by `Îc` and by `Tc`.

## 4. Data controls (frozen NOW, before any arm is read)

- **C+ (ℓ=3, D=−3, bridge KNOWN):** conditional stats must FIRE. Sharper than the marginal C+: the
  marginal C+ fired only because `c₃`'s mass at 0 (`P=5/9`) broke uniformity; conditioning on `w`
  removes the `s=0` washout, so `Îc`/`Tc` should fire **at least as strongly** as marginal MI did.
- **C− (ℓ=3, D=−11, no bridge):** conditional stats null.
- **C-cong (R3, conditional form):** for each instance's `U`, two independent primes `P ≡ Q (mod U)`,
  same bit-length, both `≡ 1 mod ℓ`; compute the conditional stats on `χ_ℓ(U mod Q)` vs `χ_ℓ(U mod P)`
  **stratified by the same `w`**. Fires ⇒ the shared-`U` congruence (not the CM tie) can generate
  conditional dependence — deflates any positive to elementary. Null ⇒ CM tie does work beyond it.
- **C−r (random base), every arm:** `χ_ℓ(random mod n)` vs `k`, stratified by `w`. Must be null.

## 5. Arms

`ℓ ∈ {5, 7, 11, 13}`, `D = −3`, in-sample `N ≈ 8000` (30-bit `p`, seed 13 — the SAME frozen sample the
marginal probe used, so this is a strictly additional read of already-frozen data, not a new fish).
**Decision rule = the anomaly-drill protocol, pre-committed:**

1. Any arm with `Îc` or `Tc` `p < 0.05/(#arms × #stats) = 0.05/8 = 0.00625` (Bonferroni) is a **flicker**,
   **not** a signal. It is claimed nothing.
2. Every flicker is sent to a **fully independent out-of-sample retest** (fresh seed, 32-bit `p`,
   `N = 12000`) BEFORE any naming — the record already has 4 chance patterns die on OOS retest.
3. A flicker that **replicates OOS** at `p < 0.00625` is reported as `[VERIFIED — conditional bridge
   detected]`, then characterized (which `w`→shift map, per drill rules: eigenvector/law, never a
   verdict). One that dies is logged as a 5th (etc.) chance pattern.
4. **All arms null (in + OOS)** ⇒ the result is a **BOUND**, graded with POWER (from R2) and SCOPE (§6),
   never "no structure": *no conditional bridge mediated by `w = (t−1)/ℓ mod ℓ` is detectable at ℓ=5,7,
   11,13*.

## 6. Scope — pre-committed bounds (stated as bounds, not closures)

- **One mediator.** This tests conditioning on `w = (t−1)/ℓ mod ℓ` (the E3 generalization). A conditional
  bridge mediated by a *different* reduction of `(t,v,U)` — e.g. `v mod ℓ`, a mod-`ℓ²` digit, or global
  (non-residue) structure of `(t,v)` — is **out of scope** and would need its own mediator. Reported as
  EXPLORATORY beside the primary: a richer mediator `ρ = (w, v mod ℓ)` (`ℓ²` strata) for `Tc` only,
  with its own multiplicity note — under-powered omnibus at ℓ=13, hence not primary.
- **Rational, not ideal.** Still the rational exponents `(j,k)`; a null does not touch ℓ-th power
  reciprocity in `ℚ(ζ_ℓ)` at the ideal level (Lemmermeyer Ch. 7 — classical), where a genuine relation
  can wash to rational independence.
- **Small ℓ only.** secp's own factors `149, 631, …` remain out of MI reach (`ℓ²` strata × `ℓ` mediator).
- **Marginal cross-check retained:** `Mc+` proves `Îc`/`Tc` fire where marginal MI is provably blind, so
  a conditional positive here would be genuinely new information relative to the completed probe.

## 7. Falsification & prior art

- **Falsifies the "purely-conditional ℓ≥5 bridge (via `w`)" hypothesis** iff all arms null in + OOS with
  `Mc+` and `C+` both firing (instrument proven live, target absent).
- **Confirms it** iff an arm replicates OOS with C-cong null (CM tie, not congruence) and C−/C−r clean.
- Exploration, not novelty: the general power-reciprocity law is classical; the contribution is a
  *verified conditional instrument*. Public data only; no leakage / ECDLP content.

## Registered deviations file: `PREREG_ell_ge5_conditional_MI_v1_DEVIATIONS.md` (created at first deviation).
