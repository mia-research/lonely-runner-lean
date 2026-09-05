# ⊘ WITHDRAWN — PREREG — E3 controls (twist / CM)

> ## STATUS: WITHDRAWN 2026-07-31, BEFORE ANY RUN. DO NOT EXECUTE. DO NOT REVIVE.
>
> **Reason: the entire E₃ line is a generation-side test, and this spec did not see it.**
>
> `E₃`'s decision comes from a contrast between the **82 solved keys** and a matched null drawn
> from `constructed_keys_1to160_100k.csv` — a **known-MT19937 pool**. The estimand is therefore
> *"do the real puzzle integers differ from a known generator's output?"* That is the PRNG /
> generation mechanism, which is out of scope by a standing project boundary
> (`btc_puzzle_investigation/CLAUDE.md` Scope; `feedback_no_prng_generation_side_2026_07_14`).
> **Varying the curve does not change this** — the curve is the *instrument*; the real-vs-MT19937
> contrast is the *object*.
>
> **And the decisive argument, which is stronger than the boundary:** puzzle #135 is unsolved, so
> there is no key. **No statistic computed on solved keys can transfer to an unsolved one except
> through a model of how the keys were generated.** Both branches of this spec's falsification are
> therefore useless for the actual target, whichever fires.
>
> **The `experiment-designer` gate launched on this file was killed before it produced an artifact.**
> No arm was run. No `E₃` was computed on `y² = x³ + 2` or on any curve.
>
> **What was NOT wrong, and is retained elsewhere** (pure curve arithmetic, no key set):
> the Cornacchia routine and its validation (534/534 unramified cases vs brute force; the `D=−3`
> output reproduces secp's on-file trace via `(t₀+3f₀)/2`); the closed-form sextic-twist orders at
> secp's `P`; the identification of `y² = x³ + 2` as the twist with a 220-bit prime subgroup; and
> the facts that `j=1728` is **supersingular** at `P ≡ 3 mod 4` and that `D ∈ {−4,−8,−11,−19,−43,−67}`
> are inert at `P` while `−7` and `−163` split. Those are statements about the curve and stand.
>
> **Error class.** Third scope violation of the same shape in one session — after the solved-key
> bit-length item (retracted) and before it, the `j=1728` E3 control proposed in
> `CORRECTION_e3_cmvanishing_interaction_reading_v1.md` §5. Each time I found a curve-flavoured
> justification for an object whose estimand is a property of the key set. **The tell is the NULL:
> if the matched null is drawn from a generator pool, the test is a generator test, whatever the
> instrument.** Check the null's provenance before the curve's.

---

*Original spec retained below, unexecuted, for the record only.*

**Date:** 2026-07-31. **Status: SPEC ONLY.** No `E₃` has been computed on any new curve.
Nothing runs until the `experiment-designer` gate returns.

---

## 0. What this tests, and the reading it puts at risk

`RESULT_diffset_cubic_cmvanishing_v1.md` reports `E₃ = 13125` on secp (98.4th pctile, `p≈0.033`)
against `E₃' = 3711` on a non-CM curve `E'` over the same prime (67.1st, `p≈0.660`), and reads this
as *"a `j=0` curve fingerprint, not a `d`-fingerprint."*

`CORRECTION_e3_cmvanishing_interaction_reading_v1.md` corrects the inference: both arms use the same
82 keys **and the same matched null**, so a property of the curve alone is present in both and
**cancels in the contrast**. What the pair establishes is a **key-set × curve interaction**.

**The untested question this spec asks:** the `E'` arm varies `j` *and* CM-ness *and* the whole
embedding at once. **No control has varied the curve while holding `j = 0` fixed.** If the effect is
a `j=0` fingerprint, it must appear on *any* `j=0` curve over the same prime — the GLV endomorphism
`x ↦ βx` acts identically on every sextic twist, so the `μ₃` structure of the `x`-coordinate set is
twist-independent.

## 1. The arms — all over secp's own prime `P`, all with `χ₃` the cubic character of `F_P`

| arm | curve | order | status |
|---|---|---|---|
| **A-secp** | `y² = x³ + 7` | `n` prime, 256 bits | published: `E₃ = 13125`, 98.4th |
| **A-twist** | **`y² = x³ + 2`** | `#E = 114286177161 · q`, `q` **prime, 220 bits** | **NEW — the test** |
| **A-nonCM** | `y² = x³ + x + 1` | `n' ≈ 2^180` prime | published: `E₃' = 3711`, 67.1st |

`y² = x³ + 2` is a **different sextic twist of the same `j = 0`**: same field, same `χ₃`, same
automorphism group `μ₆`, same CM order `ℤ[ω]`, same GLV `β`. Only the embedding `d ↦ x([d]G)`
changes.

**Order derivation is closed-form — no SEA, no factoring.** `4P = t₀² + 3f₀²` (Cornacchia, validated
against brute force on 534 unramified `(D,p)` cases; the `D=−3` output reproduces secp's on-file
trace via `(t₀+3f₀)/2`). The six sextic twists have traces `±t₀, ±(t₀±3f₀)/2`; the target order was
identified by killing a random point against the six candidates, and `B = 2` realizes it.
`q > 2^{130} > \max_i d_i`, so `d ↦ [d]G'` is **injective on the 82 keys** — the requirement, not
primality of `#E`.

## 2. Statistic (FROZEN — identical to the predecessor)

`X_i = x([d_i]G)`; `E₃ = |Σ_{i<j} χ₃(X_i − X_j)|²`, equivalently `[(2a−b−c)² + 3(b−c)²]/4` on the
cubic-class counts `(a,b,c)` of the 3321 pairwise differences. *(Verified against the published
numbers: `(1111,1140,1070) → 3711` exactly.)* Exact integers throughout; `χ₃` by exponentiation, no
float in the signal path.

**Matched null (FROZEN):** 10,000 resamples of 82 bit-length-matched `d`-values from
`constructed_keys_1to160_100k.csv` (known-MT19937), mapped onto **the same arm's curve**. Region and
`α` frozen before the real 82 are mapped on that arm. Seed 20260731.

## 3. ★ PRE-COMMITTED PREDICTIONS

| | reading | prediction for **A-twist** |
|---|---|---|
| **H-j0** | the record's own: *"a `j=0` curve fingerprint"* | **FIRES** — pctile ≥ 95th. The `μ₃`/GLV structure is twist-independent, so a `j=0` fingerprint must reproduce |
| **H-twist** | the effect depends on the specific embedding `d ↦ x([d]G)` | **DOES NOT FIRE** — pctile in the null body |

**H-j0 is the record's own reading and this arm can refute it.** That is the point of the test.

## 4. FALSIFICATION — decidable, exhaustive, ordered

- **F-1 (H-j0 supported).** A-twist pctile ≥ 95th. The effect is `j=0`-general; the E3 anomaly is a
  property of the curve class, and the interaction reading of the CORRECTION is weakened.
- **F-2 (★ H-j0 REFUTED).** A-twist pctile ≤ 90th. **Then "a `j=0` curve fingerprint" is false as
  stated** — two curves with identical `j`, CM order, `Aut`, prime and character give different
  answers, so the effect is not a function of the curve class. This is the **more consequential**
  outcome and must be reported as a positive finding.
- **F-3 (indeterminate).** pctile strictly between 90th and 95th. **No verdict.** Report the number,
  do not adjudicate; the arm is underpowered at that separation and a re-spec is required.
- **F-4 (instrument failure).** Any control in §5 fails ⇒ **no arm number is read at all.**

**Not pre-committing a Bonferroni claim.** With A-secp at `p≈0.033` the family is already
Bonferroni-non-significant, as the predecessor states. This spec tests **reproduction across twists**,
not significance, and no arm's `p` will be reported as significant.

## 5. Controls — all must fire before any arm number is read

| id | control | requirement |
|---|---|---|
| **C-ORD** | `[q]G' = O` and `[q/r]G' ≠ O` for every prime `r | q`; `q` prime, 220 bits | asserted |
| **C-INJ** | the 82 mapped points are pairwise distinct on **every** arm | asserted (else `χ₃(0)` undefined) |
| **C-FORCED** | `a+b+c = 3321`; `E₃ ≡ 0 mod 3` | as in the predecessor |
| **C-PLANT** | `ε = 0.05` concentration plant on A-twist's null must reject with power `≥ 0.9` | the predecessor achieved 0.938 on `E'` |
| **C-REPRO** | the pipeline reproduces the **published** `E₃ = 13125` (secp) and `3711` (`E'`) exactly | **load-bearing** — a rewrite that does not reproduce the known numbers says nothing about a new curve |
| **C-EXACT** | `check_no_float.py` on the run script | clean |

**C-REPRO is the gate on the port**, exactly as it was for the 120° instrument, where it caught a
faithful port and a broken plant.

## 6. Scope

**Would establish:** whether `E₃`'s secp excursion reproduces on a second `j=0` twist over the same
prime with the same character, `n = 82`, one null of 10,000, at the stated power.

**Would NOT establish:** (i) significance — the family is Bonferroni-non-significant and this does
not change that; (ii) anything about `d`-structure vs curve-structure beyond the twist question —
the CM-vs-cubic discriminator needs a CM curve with `Aut = μ₂`, and at secp's `P` the
class-number-1 discriminants `−7` and `−163` split but their orders are ~250-bit composites that
would need factoring, while `−4, −8, −11, −19, −43, −67` are inert (`j=1728` is additionally
**supersingular** at `P ≡ 3 mod 4`, so it is not an ordinary-`μ₄` control at all); (iii) any leakage
or ECDLP consequence.

**Power ceiling, stated.** `N = 82` is the entire sample and cannot grow. No number of arms makes
`p ≈ 0.033` strong. This spec tests **reproduction**, which is what a fixed small sample can support.

## 7. Deviations

`PREREG_e3_twist_and_cm_controls_v1_DEVIATIONS.md`, opened at freeze. Freeze = SHA-256 of this file,
printed by the runner.
