# PRE-REGISTRATION — closed form for the twist-level sum `B`, and the chirality of `sign(FLD)`

**File:** `PREREG_twist_sum_B_closedform_v1.md`
**Status:** WRITTEN BEFORE ANY DATA IS SEEN. No `A`, `B`, `FLD`, `CRV`, `NE`, `NW`, `σ` value
was computed, read, or inspected in the course of writing this document. The only computation
performed was a **scope-sizing prime count** (§6.4), which touches no statistic.
**Date:** 2026-07-19
**Binding on:** any run of `_twist_split_B_v1.py`, `_sigma_chi2_scan_v1.py`, or a derivative,
that reports a closed form, congruence law, sign law, or bound for `A`, `B`, or `CRV`.

Deviations from this document are permitted and are **not** presumed wrong — they must be
listed, item by item, in a companion `PREREG_twist_sum_B_closedform_v1_DEVIATIONS.md` before
any number from the run is quoted anywhere.

---

## 0. Definitions imported verbatim (not restated, not re-derived)

- `σ` is defined by `_sigma_chi2_scan_v1.py :: build()` + `sigma_fn()`. **σ is not redefined
  anywhere in this spec.** Every arm that needs a modified lift obtains it by *injecting a
  different basis* into the identical code path (§7.3), never by editing a formula.
- `chi2` is `_sigma_chi2_scan_v1.py :: chi2_table()`.
- `A`, `B`, `FLD = A + B`, `CRV = A − B`, `NE`, `NW` are as computed by
  `_twist_split_B_v1.py :: run()`.
- `π_p`, `R1`, `R2`, `DET`, `beta` are `build()`'s outputs; `reduced_basis` /
  `cornacchia_4p_D3` are in `lift_sextant_rhombus_law_proof_v2.py`.

### GIVEN facts (imported; not re-tested, not re-derived, not counted as findings)

- **G1.** `FLD = 0` unless `p ≡ 19 (mod 24)`; `|FLD| = 6·h(−p)` there.
  (`RESULT_fld_classnumber_v2.md`: Steps 0/1/3 PROVED, Step 4 CITED-Dirichlet, lemma L1
  verified 86/86 — L1 is an open lemma and every use of G1 below inherits that status.)
- **G2.** `3 | A`, `3 | B`, and `A/3 ≡ NE (mod 2)`, `B/3 ≡ NW (mod 2)`.
- **G3.** `|CRV|/√p` is bounded (`CRV²/p ≲ 3.7` observed).

---

## 1. OBJECT

**The object is `B := Σ_{x : χ₂(x³+7) = −1} σ(x)·χ₂(x)` — an exact integer, one per prime `p`.**
Equivalently, via `CRV = FLD − 2B`, the object is the E/twist *split* of the field sum, i.e. the
component of `⟨σ, χ₂⟩` that the field-level closed form G1 does **not** already determine.

`B` is the object. `CRV`, `FLD − CRV`, and `A = FLD − B` are re-expressions of it under G1 and
are not separate objects; a result about any of them is a result about `B` and must be reported
with `B`'s scope.

### 1.1 Tautology / shared-construction audit (done now, before any test)

This is the failure mode that produced `z = +5000` on `r = v − w` vs `w`. Three tiers, and the
tier assignment is **binding on how a hit may be described**:

| tier | features | shares construction with `B`? | may be called a "closed form"? |
|---|---|---|---|
| **1a** | `h(−p)`, `h(−3p)`, `L`, `M²`, `|M|`, `t`, `n`, `p`, `p mod k` indicators, cubic/quadratic residue symbols of 2,3,7, `FLD` | **No.** Built from `p` and `#E` alone. Conjugation-EVEN (§7.5). | **Yes** |
| **1b** | `M` (signed), `χ₂(M)`, `u`, `v`, `u−v`, `sign(FLD)`, `orient`, `beta`-branch | **Yes, at the level of sign convention.** σ's lift is built from `reduced_basis(p)`, i.e. from the *same* `π_p` whose sign convention fixes `M`. A `B ↔ M` sign relation is therefore **not** an independent identity until Arm III resolves whether either sign is intrinsic. | **Only conditionally**, and only after Arm III returns; must be labelled `[ORIENTATION-CONDITIONAL]` |
| **2** | `NE`, `NW`, `NE mod 2`, `NW mod 2`, flap size, `#{ε=2}`, `A` | **Yes, directly.** `NW` is the orbit count of the *same* flap∩W set that `B` sums over. `B/3 ≡ NW (mod 2)` (G2) is an identity, not a discovery. | **No — never.** Covariates only. |

**Binding ordering constraint:** Arm III (chirality) is run and committed **before** any tier-1b
feature is interpreted. A tier-1b hit reported before Arm III closes is inadmissible.

**Named non-finding:** "`B/3 mod 2` is predicted by `NW mod 2`" is G2. It is excluded from every
candidate list below by name. Any run reporting it as a hit has reported a tautology.

---

## 2. STATISTIC — one primary per arm, named now

### Arm I — magnitude closed form for `B`
**Primary statistic:** `T₁ := #{ p ∈ OOS₁ : 3·⟨c, F(p)⟩ = B(p) }`, i.e. the count of
out-of-sample primes at which the **coefficient vector `c` frozen on the in-sample window**
reproduces `B` **exactly as an integer**. `c` is obtained by the §4.1 fitting stage; once the
in-sample stage is committed to git, `c` is immutable.
**Decision rule (pre-committed):** the closed form is ACCEPTED iff `T₁ = |OOS₁|` — 100%, exact
integer equality, no tolerance. Anything less is a rate, reported as a rate (§5.3), never as a law.
**Null distribution of `T₁`:** Binomial(`|OOS₁|`, `q`) with `q` the per-prime match probability
under control N1 (§3.1), `q ≤ 0.15` for `p < 2500` and `q ≤ 0.06` for `p ≥ 2500` (§5.1).

*Why not a max over candidates.* A max of 37 exact-match indicators is upward-biased and low
power. `T₁` is a single pooled count against a single frozen predictor; **all** multiplicity over
the candidate list is discharged at the freeze, not by a correction after the fact.

### Arm II — congruence / sign law for `B`
**Primary statistic:** `T₂ := #{ p ∈ OOS₁ : rule ρ* predicts the target correctly }`, where `ρ*`
is the **single** rule carried forward from the in-sample stage under the tie-break of §4.2.
**Decision rule:** ACCEPTED iff `T₂ = |OOS₁|`.
**Null:** Binomial(`|OOS₁|`, `1/k`), `k` = number of target values (2 for sign / mod-2, 3 for
mod-3, 4 for mod-4).

### Arm III — chirality of `sign(FLD)` and `sign(B)`
**Primary statistic:** `T₃ := #{ p ∈ SCOPE_III : FLD' = −FLD **and** B' = −B }`, where the primed
quantities are recomputed on the conjugate ideal (§7.3).
**Mandatory joint reporting (not optional):** the full 2×2 table
`(FLD' = −FLD ? yes/no) × (B' = −B ? yes/no)` with all four cell counts, at every reported `T₃`.
A single number `T₃` without its 2×2 table is an incomplete report.
**Null (coin-flip hypothesis):** `T₃ ~ Binomial(N, 1/2)`.

**Total primary statistics: 3.** Family-wise ledger: Bonferroni `α = 0.05/3 = 0.0167` across arms,
on top of the within-arm handling. Every arm's power (§5) already clears this by ≥ 3 orders of
magnitude, so the ledger is not load-bearing — it is stated so it cannot be added later.

---

## 3. MATCHED CONTROL (per arm) — what it preserves, what it destroys

### 3.1 Arms I & II — control N1, the **FLD-preserving orbit-sign permutation**

Aimed at the object: the hypothesis is "`B` carries information *beyond* what G1 already fixes
about `FLD`". The null must therefore keep `FLD` **exactly** and destroy only the E/W split.

Construction, per prime, exact integers only:
1. Compute the flap `F = {x : eps(x) ≠ 0}` and `σ` from the unmodified code path.
2. Partition `F` into μ₃-orbits; assert `σ·χ₂` is constant on each orbit (this is the
   μ₆-invariance the readout has **by definition** at `p ≡ 3 mod 4`). Record the orbit sign
   multiset `S`, `|S| = NE + NW`, and the membership map orbit → {E-side, W-side}.
   *If the constancy assertion fails at any `p` (expected possible at `p ≡ 1 mod 4`), N1 is
   restricted to `p ≡ 3 mod 4` and the excluded primes are reported by name and count.*
3. Draw a uniform **permutation** of `S` (the multiset of signs), reassigned to the *same*
   orbit-to-side membership map. Set `A* = 3·Σ_{E-side} `, `B* = 3·Σ_{W-side}`.

| N1 **preserves** | N1 **destroys** |
|---|---|
| `p` and every arithmetic invariant of `p` | the arithmetic assignment of a sign to a given μ₃-orbit |
| flap support, flap size, μ₃-orbit decomposition | — and nothing else |
| `NE`, `NW`, and their parities | |
| `FLD = A* + B*` **exactly** (the multiset sum is invariant under permutation) | |
| `3 | A*`, `3 | B*`, and G2's parity `B*/3 ≡ NW (mod 2)` (automatic: a sum of `NW` values `±1`) | |

**N1 is a valid null precisely because it does not destroy μ₃/μ₆-invariance, the parity
obstruction, or `FLD` — the three structures the readout possesses by construction.** A plain
"shuffle `σ` over `F_p`" would destroy all three and is **banned by this spec**: it would
reproduce the 6–7σ soft-shadow null-mismatch failure.

Exact permutation p-values: the N1 distribution of `B*` is the exact hypergeometric-style
distribution of a signed sub-sum; computed as an integer count over Fractions, **no float**.

**Secondary null N2** (weaker, reported alongside, never primary): iid `±1` per orbit. Preserves
everything above *except* `FLD`. Its only role is to show what is lost by not holding `FLD` fixed.

### 3.2 Arm III — control G (the **gauge orbit within the same ideal**)

`sign(FLD)` can only be a chirality question if it is first a *function of the ideal*. For each
`p ∈ SCOPE_III`, enumerate the ≤ 8 re-presentations of the **same** lattice:
`(±R1, ±R2)` and `(±R2, ±R1)`; recompute `DET` from the pair and rerun the identical
`build`/`sigma_fn`/`run` path.

| G **preserves** | G **destroys** |
|---|---|
| the ideal `(π_p)`, hence `p`, `h(−p)`, `|M|`, `L` | the basis labelling and the sign/order of the basis vectors |
| the lattice, hence the flap as a *set* — this must be checked, not assumed | |

**Requirement:** `|FLD|` constant across all 8 (it must be, by G1). **If `sign(FLD)` varies within
the gauge orbit at any `p`, Arm III is answered before conjugation is applied**: `sign(FLD)` is
not a function of the ideal, and the pre-committed conclusion is §9 outcome III-e.

---

## 4. PLANTED CONTROL (positive control — must FIRE)

### 4.1 Arm I planted control — three plants through the identical pipeline
Replace the target `B` by a synthetic target, run the **identical** fit-freeze-OOS pipeline:

- **P1 (single feature):** `B^plant := 3·L`. Pipeline must return `Δrank = 0` in-sample and
  `T₁ = |OOS₁|`.
- **P2 (integer combination):** `B^plant := 3·(2·h(−p) − t + 5)`. Tests the linear-combination
  machinery, not a lookup. Must return `T₁ = |OOS₁|`.
- **P3 (class-dependent, mirrors G1's own shape):** `B^plant := 3·h(−p)·1[p ≡ 19 mod 24]`. Tests
  that the interaction columns (§4.3) can express a congruence-gated law. Must return
  `T₁ = |OOS₁|`.
- **P4 (approximate law, calibration not acceptance):** `B^plant :=` P1's value at a random 30%
  of primes and N1-drawn at the other 70%. This plant **must NOT** be accepted by `T₁` (it is not
  exact) and **must** show up as an agreement rate ≈ 0.30 in the §5.3 rate report. This calibrates
  the sweep's blind spot.

**If P1, P2, or P3 fails to fire, the Arm I null is uninformative and no bound may be quoted from
it — full stop.**

### 4.2 Arm II planted control
`target^plant := (χ₂(L) with label p mod 24)` — a rule that is true by construction. The rule
search must recover it, in-sample and at `T₂ = |OOS₁|`. Plus a negative plant: a target drawn
uniformly at random per prime, which must **not** yield any surviving rule (if it does, the
vacuity guard of §4.4 is too weak and the arm is invalid).

### 4.3 Arm III planted controls (two, one per parity)
- **Chirality-ODD plant (must flip):** `M`. By the definition of conjugation on `Z[ω]`,
  `conj(u,v) = (u − v, −v)`, so `M = v/3 ↦ −M`. The rebuilt-basis pipeline must return
  `M' = −M` at **every** `p`. It must also return `beta' ≠ beta` with `beta·beta' ≡ 1 (mod p)`.
  **If `beta' = beta` at any `p`, the conjugation did not change the prime ideal and Arm III is
  void at that `p`.**
- **Chirality-EVEN plant (must not flip):** `L = 2u − v ↦ 2(u−v) − (−v) = 2u − v = L`, and
  `enorm(R1) = p`, and `|FLD| = 6h(−p)` by G1. All three must be invariant under conjugation.
  **If `|FLD'| ≠ |FLD|` at any `p`, the conjugate lift is not isometric to the original —
  implementation error — and the arm halts before interpretation.**

### 4.4 Vacuity guard (applies to Arms I and II)
A rule or fit is admissible only if every label cell it uses contains ≥ 2 in-sample primes, and
only if `N_IS ≥ 3·K` for the design in use. Otherwise the arm ABSTAINS and reports "insufficient
support", with the realized counts. This is the guard against the silent 8→3 filter.

---

## 5. POWER — numbers, computed now

### 5.1 Per-prime null match probability under N1
`B/3` is a sum of `NW` signs `±1`; the flap occupies ≈ 1/4 of `F_p` (Cap Law, `204/822 = 0.248`
recorded in `_sigma_chi2_scan_v1.py`), of which ≈ 1/2 lies on the twist x-set, so `NW ≈ p/24`.
The N1 probability that a *fixed* integer target is hit is
`P ≤ C(NW, ⌈NW/2⌉)/2^NW ≈ 0.798/√NW`:

| `p` | `NW ≈ p/24` | per-prime match prob `q` |
|---|---|---|
| 500 | 21 | 0.174 |
| 1000 | 42 | 0.123 |
| 2500 | 104 | 0.078 |
| 6000 | 250 | 0.050 |
| 12000 | 500 | 0.036 |

**Conservative values used in all power statements: `q = 0.15` for `p < 2500`, `q = 0.06` for
`p ≥ 2500`.** (Conservative = *larger* than the table, so the stated powers are lower bounds.)

### 5.2 Arm I — exact-law power
- **How many primes before "`B` matches candidate `C` on `k/k`" beats the hypothesis-list size?**
  With list size `K = 37` (§4.3 design) and `q = 0.15`: need `K·q^k < 0.05`, i.e. `q^k < 1.35e−3`.
  `k = 4`: `37·5.06e−4 = 1.9e−2` ✓. `k = 3`: `37·3.4e−3 = 0.125` ✗.
  **→ `k = 4` unforced in-sample primes suffice for a single-feature exact match to beat the list
  at FWER 1.9e−2; `k = 5` gives FWER 2.8e−3.**
- **Frozen-coefficient OOS stage** (the primary): with coefficients immutable, each OOS prime is an
  independent factor `q ≤ 0.06`. `|OOS₁| = 206` (§6.4) ⇒ null `P(T₁ = 206) ≤ 0.06^206 ≈ 10^−252`.
  Even a degenerate `|OOS₁| = 5` gives `7.8e−7`. **Power against an exact law is 1.000** (an exact
  law hits every prime by definition).
- **Blind spot, stated as a number:** power against a law holding at per-prime rate `q_true < 1`
  is `q_true^(N_IS + N_OOS) = q_true^383`. At `q_true = 0.95` this is `3e−9`. **The exact test has
  effectively zero power against approximate laws** — which is why §5.3 is mandatory, not optional.

### 5.3 Arm I — approximate-law power (the mandatory rate report)
Report, for every one of the `K` candidates, the **per-prime agreement rate** `r̂` against the N1
null rate `q₀ = 0.15`, with the exact-permutation p-value. Detection thresholds at `N_IS = 177`,
one-sided 3σ, power 0.80:
`N ≥ ((3√(q₀(1−q₀)) + 0.84√(q(1−q)))/(q − q₀))²`

| true rate `q` | `N` required | power at `N = 177` |
|---|---|---|
| 0.40 | 34 | > 0.999 |
| 0.30 | 94 | > 0.95 |
| 0.25 | 206 | ≈ 0.75 |
| 0.20 | 810 | < 0.30 — **not detectable in this scope** |

**→ The sweep detects a candidate agreeing at rate ≥ 0.30 with power > 0.95, at rate 0.25 with
power ≈ 0.75, and CANNOT detect rate ≤ 0.20.** Every Arm I null statement inherits this floor.

### 5.4 Arm II
Binary target (`sign(B)`, `1[B=0]`, a mod-2 law), list size `K₂ = 72` (§6.3): need
`K₂·2^−N < 0.05` ⇒ **`N = 11` OOS primes**. Scope supplies `|OOS₁| = 206` ⇒ FWER `≤ 72·2^−206`.
Mod-3 target: `N = 7`. Mod-4 target: `N = 6`.
Power against a rule that is right at rate 0.9 (not exact): `0.9^206 ≈ 4e−10` under the exact
criterion; such a rule is instead visible in the §5.3-style rate report, detectable down to rate
0.65 vs a 0.5 null at `N = 206` with power > 0.99.

### 5.5 Arm III
Flip-always (`q = 1`) vs coin-flip (`q = 1/2`):
`N = 10 → 9.8e−4`; `N = 20 → 9.5e−7`; `N = 46 → 1.4e−14`.
**→ `N = 20` distinguishes flip-always from coin-flip at `p < 1e−6`; `N = 11` clears the
Bonferroni `α = 0.0167`.**
Power to reject "always" when the true flip rate is `q`: `1 − q^N`.
`q = 0.8, N = 20 → 0.988`; `q = 0.9, N = 46 → 0.992`; `q = 0.95, N = 46 → 0.905`.
Scope supplies `N_IS = 46`, `|OOS₁| = 53` (§6.4). **→ a defect rate ≥ 0.10 is caught with
probability 0.992 in-sample.**

---

## 6. SCOPE — inherited by every number this run produces

Every number reported from this run must carry: **`p` prime, `p ≡ 1 (mod 6)`, `p > 7`, window,
curve `y² = x³ + 7`, `σ` per `_sigma_chi2_scan_v1.build/sigma_fn` with the documented multi-probe
`beta` calibration.** No number may be stated without it.

### 6.1 The `n`-prime filter is DROPPED — and this is a declared deviation from the source scripts
Both `_sigma_chi2_scan_v1.py` and `_twist_split_B_v1.py` `return None` unless `n = #E` is prime.
**None of `σ`, `A`, `B`, `FLD`, `CRV`, `NE`, `NW` depends on the primality of `n`.** That filter
removes ~75% of eligible primes (§6.4: 95 survive vs 710 available below 12000) and is exactly the
silent-filter failure mode. This spec therefore runs on **all** `p ≡ 1 mod 6, p > 7` in the
windows, and records `1[n prime]` as a **covariate**, with a pre-registered secondary
stratification by it. Any run that keeps the `n`-prime filter must say so and must re-derive every
power number in §5 with the reduced counts.

### 6.2 FORCED cases — excluded from exactly one tally, by name
The parity obstruction G2 forces `B ≠ 0` when `NW` is odd. **Primes with `NW` odd are excluded
from, and only from, the `1[B = 0]` tally of Arm II** (a forced-nonzero prime carries zero
information about a zero law). They are **retained** in Arm I and Arm III, where the target is
`B` itself and parity agreement is a genuine prediction. Both counts (retained, excluded) are
reported at every use.

### 6.3 The hypothesis lists — FIXED HERE, before data

**Arm I, tier 1a (conj-even, orientation-free, construction-disjoint from σ's sign convention).**
Class numbers by **exact reduced-form counting** (§8), never an analytic formula.
Let `D₁ = −p` if `p ≡ 3 mod 4` else `−4p`; `D₂ = −3p` if `−3p ≡ 1 mod 4` else `−12p`.

```
F1  1                              F13 1[p ≡ 3 mod 4]
F2  h(D₁)                          F14 1[p ≡ 19 mod 24]
F3  h(D₂)                          F15 1[p ≡ 7 mod 24]
F4  Fraction(h(D₂), h(D₁))         F16 1[2 is a cube mod p]
F5  h(D₁)·h(D₂)                    F17 1[3 is a cube mod p]
F6  h(D₁) + h(D₂)                  F18 1[7 is a cube mod p]
F7  L,  4p = L² + 27M², L ≡ 1 (3)  F19 χ₂(2)
F8  |M|                            F20 χ₂(3)
F9  M² = (4p − L²)/27              F21 χ₂(7)
F10 t = p + 1 − n                  F22 χ₂(L)
F11 n                              F23 FLD
F12 p
```
Real class numbers `h(3p)`, `h(p)` are **excluded** — their computation needs a regulator and
invites a float into the signal path (§8). The biquadratic field `Q(√−3, √−p)` enters through the
Brauer products F4/F5/F6 only.

**Arm I, tier 1b (orientation-carrying; ARM-III-CONDITIONAL, secondary fit only):**
`G1 M` (signed), `G2 χ₂(M)`, `G3 u`, `G4 v`, `G5 u − v`, `G6 sign(FLD)`, `G7 orient ∈ {−1,+1}`,
`G8 1[beta == b1]`.

**Tier 2 (covariates; may never appear in a "closed form" claim):**
`NW, NE, NW mod 2, NE mod 2, |flap|, #{ε = 2}, A`.

**Arm II rule list, `K₂ = 6 × 12 = 72`:**
targets `{ NW mod 2, NE mod 2, B/3 mod 3, B/3 mod 4, sign(B) on B ≠ 0, 1[B = 0] }`
× labels `{ p mod 4, p mod 8, p mod 9, p mod 24, p mod 36, χ₂(M), χ₂(L), 1[2 cube], 1[3 cube],
1[7 cube], M mod 3, t mod 3 }`.
**`B/3 mod 2` with label `NW mod 2` is EXCLUDED BY NAME — it is G2, a tautology.**
`NW mod 2` and `NE mod 2` are retained as *targets* (not predictors): "is the parity itself an
arithmetic function of `p`?" is a necessary condition for any tier-1a closed form to exist, and
is the sharpest single question in Arm II.

### 6.4 Windows (declared now; scope-sizing counts computed with no statistic touched)

| window | `p ≡ 1 mod 6` | of which `p ≡ 3 mod 4` | of which `p ≡ 19 mod 24` | (`n` prime) |
|---|---|---|---|---|
| **IS** `[11, 2500)` | **177** | 91 | **46** | 23 |
| **OOS₁ (FROZEN)** `[2500, 6000)` | **206** | 108 | **53** | 26 |
| **OOS₂ (SEALED)** `[6000, 12000)` | **327** | 166 | **83** | 46 |

- `SCOPE_I` = `SCOPE_II` = all `p ≡ 1 mod 6` in the window.
- `SCOPE_III` = `p ≡ 19 mod 24` (where `FLD ≠ 0` by G1): 46 in-sample, 53 in OOS₁.
- `N_IS = 177 ≥ 3K = 111` for the `K = 37` pooled design ✓ (§4.4 satisfied).
- Per-class fits (mod 24 classes 1/7/13/19, ≈ 43–46 primes each) use features F1–F10 only,
  `3K = 30 ≤ 43` ✓.

### 6.5 Runtime budget and the ONE permitted probe
`sigma_fn`'s pre-flight is `O(p)` with `Fraction` arithmetic; total cost over IS ∪ OOS₁ is not
known in advance. A **single timing probe** is permitted on one prime `p ≡ 1 mod 6` in
`[12000, 13000)` — **outside every window** — with all outputs discarded except elapsed seconds.
Budget: 6 h wall clock. If exceeded, the **only** permitted response is to truncate OOS₂ (never
IS, never OOS₁), and the truncation must be reported with the realized counts.

---

## 7. THE CHIRALITY ARM — operational definition

### 7.1 Why this arm exists (structural, derived from the definitions, not from data)
`M` is defined by `4p = L² + 27M²` with `L ≡ 1 mod 3` pinning `L` but leaving `M`'s **sign** free;
that sign is fixed by which of the two primes above `p` the code's `cornacchia_4p_D3` happens to
return. At `p ≡ 19 mod 24` we have `p ≡ 3 mod 4`, so `χ₂(−1) = −1` and hence
`χ₂(−M) = −χ₂(M)`: **`−χ₂(M)` is conjugation-ODD.** Meanwhile `σ`'s lift is built from
`reduced_basis(p)`, i.e. from the **same** `π_p`. So `sign(FLD) = −χ₂(M)` (54/54) relates two
quantities that share a sign convention. Whether it is an identity or a convention is decided by
one experiment, never run.

### 7.2 Conjugation on `Z[ω]`, in `build()`'s coordinates
A vector `(a, b)` denotes `a + bω`. Then `conj(a + bω) = a + bω̄ = a + b(−1 − ω) = (a − b) − bω`:
```
conj(a, b) = (a − b, −b)          det = [[1, −1], [0, −1]] = −1   (orientation-reversing)
```

### 7.3 "Recompute with `π̄_p`" — exact operational meaning
1. `eis, eps, beta, R1, R2, DET = build(p)` (unmodified).
2. `R1' = conj(R1)`, `R2' = conj(R2)`, `DET' = R1'[0]·R2'[1] − R1'[1]·R2'[0]`. **Assert
   `DET' = −DET`.**
3. Refactor `build` into `build_from_basis(p, R1, R2)` — **plumbing only**. The refactor must be
   accompanied by a diff showing that the bodies of `eis`, `om2`, `reduce_P`, the multi-probe
   `beta` calibration, and `eps` are byte-identical apart from the basis parameter. **No formula
   in `σ` is edited.** `build(p) ≡ build_from_basis(p, *reduced_basis(p))` must be verified to
   return identical `(FLD, A, B, NE, NW)` at every `p ∈ IS` — a regression check that must pass
   before the arm runs.
4. Call `build_from_basis(p, R1', R2')` → `eis', eps', beta', R1', R2', DET'`.
   **Assert (must fire, §4.3): `beta' ≠ beta` and `beta·beta' ≡ 1 (mod p)`.**
5. `sig', orient' = sigma_fn(p, eis', eps', R1', R2', DET')`. **Assert exactly one of `('-','+')`
   passes the 100%-agreement pre-flight** (see §7.4).
6. Recompute `A', B', FLD', CRV', NE', NW'` by the unmodified `_twist_split_B_v1.run` body.
7. **Assert `|FLD'| = |FLD|`** (required by G1; failure = implementation error, arm halts).

### 7.4 The `sigma_fn` try-order gauge hole — pre-registered check
`sigma_fn` returns the **first** of `('-', '+')` that passes; if **both** pass, `'-'` wins with
nothing tested. This is the same shape as the documented `beta`-calibration bug at `p = 823`.
Pre-registered assertion: exactly one orientation passes at every `p ∈ SCOPE_III`. Primes where
**both** pass are **excluded from Arm III with their count and their `p` values DISCLOSED in the
result** — never silently — because at those primes `sign(FLD)` is a coin toss of the source
order, not a property of the object.

### 7.5 Chirality parity of the named quantities (derived here, before the run)
`L = 2u − v ↦ 2(u − v) − (−v) = 2u − v` → **EVEN**.  `M = v/3 ↦ −v/3` → **ODD**.
`enorm(R1) = p` → **EVEN**.  `h(D₁), h(D₂), t, n, p` → **EVEN** (functions of `p` and `#E`).
`χ₂(M) ↦ χ₂(−M) = χ₂(−1)χ₂(M) = −χ₂(M)` at `p ≡ 3 mod 4` → **ODD**.

### 7.6 What each outcome establishes (PRE-COMMITTED — see also §9)
- **III-a `FLD' = −FLD` and `B' = −B` at all `N`:** `sign(FLD)` and `sign(B)` are chirality-ODD.
  They are invariants of the **pair** `(p, choice of prime above p)`, not of `p` alone. The 54/54
  law then upgrades to a genuinely intrinsic statement: **`sign(FLD)·χ₂(M) = −1` is
  conjugation-INVARIANT** (both factors flip). Reported as an identity between two orientation-odd
  quantities, with G1's lemma-L1 status inherited.
- **III-b `FLD' = +FLD` at all `N`:** `sign(FLD)` is conjugation-EVEN while `−χ₂(M)` is
  conjugation-ODD ⇒ the two cannot agree in both chiralities ⇒ the 54/54 agreement is carried by a
  **shared normalization** inside the code path. Pre-committed action: locate it (candidates named
  now: `cornacchia_4p_D3`'s `for sx in (1,−1): for sy in (1,−1)` return order; `gauss_reduce`'s
  swap order; `sigma_fn`'s `('-','+')` try order), report which, and re-scope the sign law to that
  convention. The magnitude law `|FLD| = 6h(−p)` is untouched by either outcome.
- **III-c mixed:** `sign(FLD)` is not determined by chirality alone. Report the exact partition of
  the flipping and non-flipping sets by `p mod 24`, `orient`, `orient'`, `χ₂(M)`, `1[n prime]`, and
  `1[beta == b1]`. This is a **new object**, not a closure; the pre-committed output is its
  characterization plus the next probe.
- **III-d `FLD` flips but `B` does not (or vice versa):** the E/W split carries an orientation
  structure the field sum does not. This is the most informative cell of the 2×2 and is the reason
  `T₃` is a joint statistic. Pre-committed output: characterize `A' + A` and `B' + B` as sequences
  and test them against N1.
- **III-e `sign(FLD)` varies within the gauge orbit G (§3.2), before conjugation:** `sign(FLD)` is
  not a function of the ideal at all; Arm III abstains and reports this as its finding.

---

## 8. EXACTNESS

- **All of `σ`, `χ₂`, `A`, `B`, `FLD`, `CRV`, `NE`, `NW`, `L`, `M`, `u`, `v`, `t`, `n`, class
  numbers, cube/quadratic-residue indicators, the N1 permutation, and every p-value are Python
  `int` or `fractions.Fraction`.** No `float` in the signal path. `check_no_float.sh` must pass on
  every file added or modified by this run, before any result is quoted.
- **Class numbers** `h(D₁), h(D₂)` by **exact reduced-form counting**: count `(a,b,c) ∈ Z³` with
  `b² − 4ac = D`, `|b| ≤ a ≤ c`, `b ≥ 0` when `|b| = a` or `a = c`. Integer loops only. Real
  quadratic class numbers are excluded from the feature list precisely because their standard
  computation needs a regulator (§6.3).
- **`L, M` extraction, exact:** take `π = R1` after asserting `enorm(R1) == p`; walk the 6 units
  `{±1, ±ω, ±ω²}` to the associate with `3 | v`; set `M = v/3`, `L = 2u − v`, and fix the overall
  sign by `L ≡ 1 (mod 3)`. Assert `4p == L² + 27M²`. All integer.
- **Weil/√p references** are reported as the exact `Fraction(CRV², p)` (as the existing script
  already does for `C²/p`) — never as a float square root.
- **N1 p-values** are exact permutation counts (integer numerator / integer denominator), compared
  against thresholds as exact rationals. No float decides any verdict.
- **Float carve-out:** the power-analysis normal approximations in §5.3/§5.5 are computed in float.
  They are **analytic sizing only**, computed before the run, on no data, with no key and no
  statistic in the path. They set sample sizes; they never enter a decision.

---

## 9. PRE-COMMITMENT — what we conclude for each outcome

Filled in **before** the run. Every conclusion below carries the §6 scope and the §5 power number;
none may be restated without them.

### Arm I
| outcome | pre-committed conclusion |
|---|---|
| Planted control P1/P2/P3 fails to fire | **The Arm I null is uninformative.** No bound, no rate, no "no closed form" statement may be quoted. Fix the pipeline and rerun. |
| `Δrank = 0` in-sample **and** `T₁ = |OOS₁|` | `B` has an exact `Q`-linear closed form in tier-1a over the scope. Report the coefficient vector, the in-sample and OOS counts, the N1 p-value, and immediately open the SEALED OOS₂ window as confirmation. Grade `[EMPIRICAL, k/k over scope]` — **not** PROVED. Next probe named: derive it from the Eisenstein period / Jacobi-sum structure. |
| `Δrank = 0` in-sample but `T₁ < |OOS₁|` | The in-sample relation is a fit, not a law. Report `T₁/|OOS₁|` and the N1 p-value of that rate. **This is the outcome three prior chance patterns produced; it is expected to be reported as such, not rescued by refitting.** No refit on OOS₁ is permitted. |
| `Δrank ≠ 0` in-sample (no relation exists) **and** best rate `r̂ < 0.30` | **Bounded absence, with power:** "No exact `Q`-linear closed form for `B` in the 37-column tier-1a design over `p ≡ 1 mod 6`, `p ∈ [11, 6000)`; and no candidate in the list agrees at a per-prime rate ≥ 0.30 (power > 0.95) or ≥ 0.25 (power ≈ 0.75). Rates ≤ 0.20 are **not excluded** (power < 0.30)." **This is a magnitude, not a closure.** Mandatory accompanying report: the residual sequence `r_p = B/3 − fit`, its N1-relative distribution, its own §5.3 rate scan against every unmodelled label, and the explicit statement of §9.1. |
| `Δrank ≠ 0` but some candidate rate `r̂ ≥ 0.30` | A partial/conditional law. Characterize the subset on which it holds by the pre-registered labels; do **not** name that subset as the new scope (that is post-hoc subsetting) — instead freeze it and retest on OOS₂. |

### Arm II
| outcome | pre-committed conclusion |
|---|---|
| Positive plant fails, or the random-target negative plant yields a surviving rule | Arm II is invalid; §4.4 guard is too weak; no statement. |
| A rule survives in-sample and `T₂ = |OOS₁|` | A congruence/sign law for `B` over the scope, at FWER `≤ 72·k^−206`. Grade `[EMPIRICAL]`. If the surviving target is `NW mod 2` or `NE mod 2`, note explicitly that this establishes the **necessary condition** for a tier-1a closed form, and feed it back to Arm I as a new feature — in a **new pre-registration**, not this one. |
| No rule survives | "No rule in the 72-rule list predicts the target on 100% of `p ≡ 1 mod 6` in `[11, 6000)`; binary rules holding at a rate ≥ 0.65 would have been detected with power > 0.99; rates ≤ 0.58 are not excluded." Report the top rates with exact p-values. |

### Arm III
| outcome | pre-committed conclusion |
|---|---|
| `beta' = beta`, or `|FLD'| ≠ |FLD|`, at any `p` | Implementation error. Arm halts, no interpretation. |
| Gauge orbit G shows `sign(FLD)` non-constant | Outcome III-e (§7.6). Arm abstains; that abstention **is** the finding. |
| `T₃ = N` with the 2×2 concentrated in the (flip, flip) cell | Outcome III-a. `sign(FLD)·χ₂(M) = −1` promoted to a conjugation-invariant identity; `sign(B)` likewise chirality-odd. `p ≤ 1.4e−14` vs coin-flip at `N = 46`. |
| `T₃ = 0` with FLD invariant | Outcome III-b. The 54/54 sign law is re-scoped to the code's normalization convention, the convention is named, and `|FLD| = 6h(−p)` is reported unaffected. |
| Any mixed 2×2 | Outcomes III-c / III-d. Report the full partition; the arm ends in a characterization and a named next probe, never a verdict. |

### 9.1 Mandatory subspace clause (applies to every "absence" outcome above)
An absence in this design is an absence **in the pre-registered family**: exact `Q`-linear
combinations of 37 conjugation-even columns, and 72 congruence rules. It says nothing about a law
living in a quantity not projected onto. The following are **named now** as the un-probed
directions any absence must be reported alongside:
1. non-linear (quadratic, multiplicative) functions of tier-1a features;
2. `L`-function / period quantities of `E` and its sextic twist beyond the trace `t`
   (e.g. `a_p` of the twist, the sextic-twist family as `p` varies);
3. Jacobi sums `J(χ₆, χ₂)`, `J(χ₃, χ₃)` as *elements of `Z[ω]`* rather than through `(L, M)`;
4. a law on the **orbit-sign sequence** `(ε_j)` itself rather than on its sum `B` — i.e. the effect
   may live in the μ₃-orbit *labelling*, a subspace this design integrates out by construction;
5. `A` and `B` jointly as a 2-vector under a group action not diagonalized by the E/W split.

An absence stated without this list, or stated as "`B` has no closed form", is a spec violation.

---

## 10. OUT-OF-SAMPLE DISCIPLINE (three prior chance patterns died here)

1. Run IS only. Produce: the fitted `c`, the surviving rule `ρ*`, all rate reports, all planted
   controls, all assertions.
2. **`git commit` the frozen `c` and `ρ*`** (and the Arm III implementation) **before** OOS₁ is
   computed. The commit hash is the freeze certificate and must appear in the result document.
3. Run OOS₁ with `c` and `ρ*` immutable. **No refitting on OOS₁ under any outcome.**
4. OOS₂ `[6000, 12000)` stays **SEALED** and is opened only to confirm an ACCEPTED law
   (`T₁ = |OOS₁|` or `T₂ = |OOS₁|`) — never to rescue a failed one.
5. If any of the §4.4 guards abstains in-sample, **OOS₁ is not unsealed at all**; the run reports
   "insufficient support" with the realized counts. This is the pre-committed anti-p-hacking rule:
   the windows may not be widened to manufacture support.

---

## 11. Run order (binding)

`Arm III` → commit → `Arm I` IS → commit (freeze) → `Arm I` OOS₁ → `Arm II` IS → commit (freeze)
→ `Arm II` OOS₁ → (OOS₂ only on an ACCEPT).

Arm III first, because §1.1 makes every tier-1b interpretation conditional on it.
