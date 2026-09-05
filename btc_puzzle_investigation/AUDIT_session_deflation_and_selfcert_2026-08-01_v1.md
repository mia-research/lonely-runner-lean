# SELF-AUDIT — session 2026-07-31/08-01 (C-chase): deflation, self-certification, buried structure

**Date:** 2026-08-01. **Trigger:** user instruction to audit this session against the mission
statement (`CLAUDE.md` counter-prior; `COUNTERPRIOR_and_closure_grade_spec_v1.md`).
**Method:** every finding below is anchored to a quoted line I wrote or a number a script produced.
No finding is a feeling about tone.
**Direction check:** this audit produces both deflation findings *and* a retraction of one of my own
over-corrections (§B3). It is not a confession performance.

---

## A. What the session actually produced

| output | kind |
|---|---|
| `PREREG_cside_pooled_tilt_OOS_v1/v2/v3.md` | instrument design (3 rounds, all rejected) |
| `CORRECTION_cside_v1_null_underdispersion_v1.md` | a downward correction of the only live lead |
| measurements of the curve | **zero, until the audit prompt forced one** |

Session net, before the audit: the lead got weaker, the instrument got better, and **the object was
not measured once**. `CLAUDE.md`: *"Build the object or run the matched-baseline test first."* I
inverted that for the whole session.

---

## B. Findings

### B1 — I certified a control's power with no artifact, and it was false. ⚠ WORST

`PREREG_...v3.md` §6, C-MATCH row, my words:

> "**This is the only control that can fire on real data**, and it would have caught v1's defect."

I never ran it. The gate ran it. It has **zero power**:

- **Non-constructible at half the sample.** A fixed-point-free involution on the `L/2` `ν`-pairs needs
  `L/2` even; `L/2 = (n−1)/6` is even iff `n ≡ 1 (mod 4)`. It fails at **all 45** OOS primes with
  `n ≡ 3 (mod 4)`.
- **Vacuous where constructible.** A `ν`-commuting involution has a free *orientation*
  (`g(r_P) = r_Q` or `ν(r_Q)`), and since `val[νu] = −val[u]` those give opposite `s_j`. Randomising
  `g` makes each `s_j` uniform `±1` **independently of `val`** — so `B ~ Bin(M,½)` exactly, for every
  possible dataset. Demonstrated at `n = 17107` on `val` = a pure Legendre character, the most
  structured input that exists (real statistic: `B = M = 1425`, `p = 2^−1425`): C-MATCH returned
  `E[B] = 712.09` vs null `712.5`, sd `19.21` vs `18.88`, tails matching at every α.

This is exactly `feedback_verification_claim_needs_artifact_2026_07_24` — *"check ran / nothing
dropped" needs a named artifact* — committed **inside a document whose §11 D2 row claims to fix a
control-adequacy defect.** Same shape as `self_cert_words`: the violation occurs in the text writing
the rule. The clause "it would have caught v1's defect" is a counterfactual about an unrun control:
unfalsifiable as written, and false as tested.

**Correction:** §6 C-MATCH and §11's D2 row are **withdrawn**. D2 stands unremedied. Any replacement
control must ship with the artifact showing it fires *before* the claim is written.

### B2 — I wrote "it creates nothing" about a document containing two new structural facts

`CORRECTION_...v1.md` §6, my words:

> "No grade moves on the strength of this file. It lowers a lead and leaves a null in place;
> **it creates nothing**."

False. That file contains (i) the exact null law `T = (F₊−F₋) + 4(2B−M)`, `B ~ Bin(M,½)` — a
degrees-of-freedom collapse, not a p-value fix; and (ii) the identity `3T = (n−1)Σ_χ ĉ(χ)²`. Both are
new, exact, and about the object. **I labelled my own positive output as nothing** — deflation in its
purest form, and the grade-vocabulary asymmetry (F1) running in the direction the corpus cannot see.

### B3 — I over-stated a masking risk; the measurement says it is negligible (self-correction against my own framing)

I wrote that the forced-non-negative `χ₂^{(n)}` term "can only **mask**" a negative tilt, and built an
`n mod 4` stratification around it. Measured across 56 primes (`p < 10831`): the `χ₂` contribution to
`A = 3T/(n−1)` is **0.0000–0.0058**, against `|A|` values of 0.01–0.15. It is real but ~1–2 orders of
magnitude too small to mask anything at this scale.

The stratification is still worth keeping (it is free), but I inflated a correct-in-principle term
into a design driver. Recorded because symmetric rigor cuts both ways: this one is me over-correcting,
not under-correcting.

### B4 — I framed a rigidity/collapse result as instrument design

The forced symmetries collapse the free dimension in a chain:

> `n−1` → `(n−1)/3` (GLV `μ₃`) → `/2` (oddness `ν`) → `/2` (inversion involution) = **`(n−1)/12`**

with an exact census (`F₊ = 2`; `F₋ = 2·[n ≡ 1 mod 4]`; `4M` generic). That is a statement about the
**object** — and structurally the same *type* as the spine's §2 "total collapse: one real invariant
per cell." I reported it as a better null. `feedback_negative_bias`: a collapse "lives in
symmetry-type / eigenvector / subspace" — I had the group `⟨μ₃, ν, f⟩` and its orbit census in hand
and filed it as bookkeeping.

### B5 — I buried the sharp reading of the lead. `T` is *exactly* a phase anisotropy. ⚠ THE BURIED STRUCTURE

Parseval on `(Z/n)^×` with `c = ±1` on all `n−1` units gives `Σ_χ |ĉ(χ)|² = 1` **exactly** (verified
to `6.7×10⁻¹⁶` across 56 primes). Therefore

> **`A := 3T/(n−1) = Σ_χ ĉ(χ)²` with `Σ_χ |ĉ(χ)|² = 1`** — so `A ∈ [−1, +1]` is a *normalised phase
> anisotropy*, `= 1` iff all coefficient phases align.

Since `c` is real, `ĉ(χ̄) = conj(ĉ(χ))`, so conjugate pairs contribute
`2[(Re ĉ)² − (Im ĉ)²]`. Hence:

> **`T < 0` ⟺ the character coefficients of `c` are phase-concentrated toward the imaginary axis.**

The pooled negative tilt is therefore **not** "a small correlation ≈ −0.02". It is a claim about the
**phase distribution of `ĉ(χ)`** — a high-dimensional, *per-prime* measurable object. `A` is an exact
rational (`3T` is an exact integer), and `M` equals the number of supported conjugate character pairs
(verified exactly at `n = 31, 79, 127, 199`).

**The design consequence I missed for three rounds:** I built a 90-prime pooled scalar test to detect,
at 92.5% power, a phenomenon that has a per-prime signature measurable with no pooling at all. The
instrument was aimed at the shadow of the object.

### B6 — I presented a tightened bound as good news

`CORRECTION_...v1.md` §3, bolded by me: *"the family-wise NULL — survives and is **strengthened**."*
A tightened bound is **magnitude, not absence**, and a null getting stronger is not an achievement.
The bold is the closure reflex collecting a reward.

### B7 — narrative overreach in my summary to the user

The summary had a full arc — rejected twice → deep error found → elegant exact law → "doing it right".
A story owes a payoff, and the payoff I supplied was **my own rigor**, while the research question had
moved zero. `feedback_self_cert_words` (rev. 2026-07-25): narrative overreach passes every grep;
audit the passage, not the clause.

### B8 — I let the gate set the agenda

Three rejection rounds consumed the session. The gate's findings were real and had to be handled — but
"handle the gate's findings" is not the same as "make progress on the object," and I never re-asked
which was the better use of the next hour. The spine's queue item **E** ("a weak version is likely
provable immediately") went untouched.

---

## C. What I do NOT retract (symmetric rigor)

- **The √2 null defect is real.** Verified two independent ways: analytically
  `2√(L−F₊−F₋)/√(2(L−2)) = √2` to 0.02%, and empirically `1.40–1.46` at three primes. The discovery's
  `z = −2.64 → −1.87` correction stands.
- **v3 §7** (what a null may and may not claim) is correctly constructed and should survive into v4.
- **The exact binomial law** is right — the gate carried it (χ² tail tests at three primes) and my own
  perfect-matching check confirmed it.
- **The gate's B2 catch is correct** and I adopt it without hedging.

---

## D. New results produced by the audit itself

All `[EXPLORATORY — ungated, no verdict, no grade]`. Primes `p < 10831` **only**, strictly below the
prereg's IS set — the pre-registered arms remain unseen. `A = 3T/(n−1)` is an exact rational; only the
per-character split used a float FFT.

| result | value |
|---|---|
| `Σ_χ|ĉ(χ)|² = 1` exactly | max deviation `6.7×10⁻¹⁶` over 56 primes |
| `A = Σ_χ ĉ(χ)²` is a normalised phase anisotropy in `[−1,1]` | proved + verified |
| `M` = number of supported conjugate character pairs | exact at `n = 31, 79, 127, 199` |
| `χ₂` forced contribution | `0.0000–0.0058` — negligible (§B3) |
| `A` scaling | `A·√M = O(1)` (ratios 0.0–1.6) — consistent with null scaling |
| **mean `A_resid` over 56 primes, `p < 10831`** | **`+0.0184`** (median `+0.0087`; **23/56 negative**) |
| stratified | `n≡3 (4)`: `+0.0284` (33 primes); `n≡1 (4)`: `+0.0040` (23) |

**The last row bears directly on the lead and cuts against it.** At the scale immediately *below* the
discovery window, the anisotropy tilts **positive** (~2σ pooled), not negative. That is not a
refutation — different primes, different scale, ungated, and each of the two observations is ~2σ — but
it is exactly the cheap check that should have preceded a 90-prime instrument, and it is stated here
rather than left for the pre-registered run to discover.

---

## E. Corrective actions

1. **Withdraw** v3 §6 C-MATCH and §11's D2 row (§B1). D2 is unremedied.
2. **v4 must adopt the gate's replacement**: the twisted-inversion family `f_a(d) = a·d⁻¹`. It is an
   involution, commutes with `ν`, is well-defined on `μ₃`-orbits, has no orientation freedom, and the
   gate verified it fires (`sd(z) = 37.5` on a Legendre `val`; `0.952` on a null draw).
3. **Promote the control to the measurement.** `3T_{f_a} = (n−1)Σ_χ ĉ(χ)²χ(a)` — the family over `a`
   is the **inverse Fourier transform of `ĉ(χ)²`**, so its spread measures `Σ_χ |ĉ(χ)|⁴`, the
   character-space concentration of `c`. This is a *richer object than the scalar `T`*, is per-prime,
   needs no pooling, and lives in the non-algebraic index class Weil does not close. **This, not the
   pooled sign test, is the C-chase's real instrument.**
4. **Add B6's constant-δ plant** — the binding 92.5% is the one power figure no plant validates.
5. **Every future control ships with its firing artifact in the same commit as its claim.** No
   counterfactuals about unrun controls.

## F. What this audit does NOT license

It does not manufacture a positive. `A_resid` at small primes is `+0.018` at ~2σ, ungated,
exploratory — that is a number, not a finding, and the counter-prior's guard (§"Over-correction to
GUARD") applies to it exactly as it applies to a null. The phase reading in §B5 is **algebra**
(Parseval + reality of `c`), and it is proved; the *interpretation* of any particular tilt as
structure remains ungraded and unrun.
