# PRE-REGISTRATION — is the Sy sign-skew real? (committed BEFORE computing)

**Date:** 2026-07-18. Written and committed **before** any out-of-sample computation. The audit
([[AUDIT_negative_bias_session2to4_v1]]) found `Sy = Σ_P s_y(P)χ₂(y_P)` skews positive
(+16/−6 in [100,4000), +19/−10 in [4000,10000), pooled ~2.7σ). That was IN-SAMPLE and post-hoc. This
pre-reg fixes every free choice so the confirmation cannot be engineered.

## The deck-stacking risks, and how each is removed HERE

1. **Sign convention is a free knob.** → REMOVED: `Sy` is a sum over ALL points `P≠O` (both `(x,±y)`),
   with `s_y(P)=+1 iff y≤(p−1)/2`. No generator, no root choice. It is a **canonical integer** given
   `(E,p)`. The only convention is centered-`s_y`, fixed now; I will additionally report the statistic
   under the FLIPPED convention `s_y=+1 iff y>(p−1)/2` — the skew MUST flip sign under it (else bug),
   and its magnitude must be identical. This is a consistency check, not a second test.
2. **Choosing the explanatory variable post-hoc (h(−p) vs h(−3p) vs t vs …).** → REMOVED: the ONE
   pre-registered explanatory hypothesis is stated below (H2). Any other correlate found later is
   reported as EXPLORATORY with Holm correction and cannot upgrade the conclusion.
3. **Choosing the sample after peeking.** → REMOVED: the out-of-sample set is fixed now as **all
   primes `p∈[10000,40000)`, `p≡1 mod 6`, `p≡3 mod 4`, `n=#E(F_p)` prime** (I have looked at `Sy`
   only up to `p<10000`; this range is fresh). No prime dropped for any other reason; the `n`-prime
   filter count is reported.
4. **Picking the statistic that happens to be significant.** → REMOVED: ONE primary statistic (S1),
   fixed below. S2/S3 are secondary, Holm-corrected.
5. **No control that could expose self-deception.** → ADDED: the random-`b` control (C1) and the
   sign-shuffle null (C2), both specified below.

## Statistics (all exact ints; float only for the binomial p-value / normalized mean)

- **S1 (PRIMARY): sign lean.** `k = #{p in sample : Sy(p) > 0}` out of `M` nonzero-Sy primes.
  Two-sided exact binomial test vs `1/2`. **Decision:** skew CONFIRMED iff `p_binom < 0.01`
  (pre-set α=0.01, one test). Reported with `k/M`.
- **S2 (secondary): normalized mean.** mean of `Sy/(2√p)` over the sample; sign and t-stat.
- **S3 (secondary): magnitude structure.** already-known `6|Sy` (μ₃-forced) re-confirmed on the fresh
  sample (must hold; a bug-check, not a finding).

## Hypotheses

- **H0 (null):** `Sy(p)` sign is a fair coin; `k/M ≈ 1/2`; the in-sample lean was chance.
- **H1 (skew real):** `Sy` leans positive out-of-sample (`k/M > 1/2`, S1 significant).
- **H2 (the ONE pre-registered explanation):** the lean is a **generic property of the
  `Σ s_y·χ₂(y)` statistic over `y²=x³+b`, not special to `b=7`** — i.e. it is driven by the
  distribution of `χ₂` on square roots in the lower half (the same object the class-number formula
  for `h(−p)` measures), NOT by the secp curve. **Test:** control C1 below. If C1 shows the SAME lean
  for random `b`, H2 is supported and the skew is "real but curve-generic". If ONLY `b=7` leans, H2 is
  rejected and the skew is curve-specific (a stronger, stranger claim — flag, do not celebrate).

## Controls (must behave as stated or the run is void)

- **C1 (random-b, the deck-check):** for each of 8 fixed `b∈{1,2,3,5,11,13,17,7}` (7 last), compute
  the same sign-lean statistic over the SAME prime sample. Pre-set expectation: if the skew is the
  general `s_y·χ₂` phenomenon (H2), all `b` lean the same way; `b=7` is unremarkable. **This is the
  control that catches me fooling myself** — a lean unique to `b=7` would be extraordinary and demands
  a mechanism, not a headline.
- **C2 (sign-shuffle null):** assign each prime a random ± (seeded), recompute `k`. Must give
  `k/M ≈ 1/2` (calibrates S1's null). 1000 draws; report the null's central mass.

## Power

`M ≈ 60–70` primes expected in `[10000,40000)` (p≡1 mod6, p≡3 mod4, n prime, ~1/2 have n prime).
At `M=64`: to reject `1/2` at α=0.01 with power 0.8 needs a true rate `≈ 0.68`. The in-sample rate was
`35/51 ≈ 0.686`. So **if the in-sample rate is the true rate, this sample has ~0.8 power.** If the true
lean is weaker (say 0.60), power is low (~0.35) and a null result is INCONCLUSIVE, not a refutation —
this is pre-stated so a null is not over-read.

## Falsification / decision rules (committed)

- If S1 `p_binom < 0.01` AND C2 calibrates AND C1 shows the lean is curve-generic → **skew CONFIRMED,
  curve-generic (H2)**; report as a scoped fact about `Σ s_y χ₂` at these primes, tied to lower-half
  `χ₂` distribution. NOT a leak (x/y character sum).
- If S1 `p_binom < 0.01` but C1 shows it is `b=7`-SPECIFIC → **CONFIRMED but anomalous**; flag as an
  open object, do NOT explain, name the next probe.
- If S1 `p_binom ≥ 0.01` → **NOT CONFIRMED out-of-sample**; the in-sample lean is declared chance /
  underpowered per the power note. No positive claimed. (Symmetric with how a negative would be
  treated — [[feedback_dont_pre_evaluate_shut_thinking_2026_07_11]].)
- The convention-flip check (risk 1) and `6|Sy` (S3) must both pass or the run is a BUG, not a result.

**Nothing below the line is looked at until this file is saved.**
