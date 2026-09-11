# Retraction: the small-denominator lemma was already in the corpus

2026-09-12. Retracts the novelty claim in `SMALL_DENOMINATOR_WITNESS_v1.md` §3. The
mathematics in that file is correct; the claim that it was new to the project is false.

---

## 1. What was already there  `[quoted]`

`docs/n8/TIGHT_INSTANCES_v1.md` §1 (dated **2026-09-07**, five days earlier), marked
`[PROVED]`:

> "For `q ∈ {2,…,8}` and `gcd(a,q)=1`, `‖v·a/q‖ = |va mod q|/q ≥ 1/q` whenever `q ∤ v`. So:
> — `q ≤ 7`: if `q` divides no speed, `t = a/q` gives `M(T) ≥ 1/q > 1/8` — **strictly**.
> — `q = 8`: if 8 divides no speed, `t = m/8` (`m` odd) gives `M(T) ≥ 1/8` — **tightly**.
> … Hence the **residual case** — the only one needing an argument — is `T` containing a
> multiple of 5, of 6, of 7 **and of 8**. Everything else is one line."

`docs/n8/HALVING_AND_TIGHT_WITNESS_v1.md` §1, same date:

> "So **LRC(8) is equivalent to: every 7-set holding a multiple of 5, of 6, of 7 and of 8
> has `M(T) ≥ 1/8`.**"

And `TIGHT_INSTANCES_v1` itself attributes the `q = 8` rung further back, to
`N11_TRANSLATION_v1.md` §3.

**Both** of `SMALL_DENOMINATOR_WITNESS_v1`'s headline results were therefore already
established: the lemma (§1 there) and the residual characterisation (§4 there). The prior
statement of the residual is **sharper** than mine — "a multiple of 5, of 6, of 7 and of 8",
the minimal form — where I wrote "hits every `d ∈ {2,…,8}`" and derived the minimal form only
later, in conversation.

## 2. How the check failed  `[recorded]`

`SMALL_DENOMINATOR_WITNESS_v1` §3 reported: *"`grep` over `docs/n8/` and `reports/` finds no
witness at any denominator below 8 … The `d < 8` cases were not in the project."*

The grep was `t = 1/[234567]` — **literal digits**. The corpus states the result with a
**variable**: `t = a/q`, `t = 1/q`, `q ≤ 7`. A digit pattern cannot match a general statement.

Worse, the correct search *was* launched — a broad grep including `divides no speed` — and it
exceeded its timeout and went to background. I abandoned it and substituted the narrow one
rather than waiting. When the broad search finally returned it found
`TIGHT_INSTANCES_v1.md:18` on the first line of output.

**Rule this establishes:** a novelty check must search for the *statement*, not for an
instance of it. Grep for the hypothesis in words (`divides no speed`, `residual case`), not
for a formula with the parameters filled in. And a novelty claim must not be published on a
search that was cut short.

## 3. What of 2026-09-11 survives, and at what confidence

| item | status |
|---|---|
| the lemma `d ≤ 8`, `d ∤ e` ⟹ witness | **NOT NEW** — `TIGHT_INSTANCES_v1` §1 |
| the residual = hits every `d ≤ 8` | **NOT NEW**, and prior form is sharper |
| coverage 69.29% of Case 2, exhaustive `[1..18]` | measurement of a known lemma; the number appears new |
| `N*(V,n) = Σ_{d≤n, d∤v} φ(d)` as a witness count | the counting form appears new; the underlying lemma is not |
| Case 1 ⟺ 2-adic span `≤ 2` | reframing of the known `q = 8` rung |
| grid certificate `L(a) ≤ U(a)` | no prior hit found |
| first-order obstruction ⟺ Unit-Complete | "Unit-Complete" is named in **six** prior documents; the *derivation* found no prior hit |
| frame-free "residue unique" restatement | no prior hit found |
| per-runner moduli | no prior hit found |

**Confidence caveat, stated because it is earned:** every "no prior hit" above rests on the
same tool that just failed. They are searched-and-not-found, not established as new, and none
should be presented as novel without a search for the *statement* in words.

## 4. What is unaffected

The mathematics of `SMALL_DENOMINATOR_WITNESS_v1` §1 and §4, the controls, and the coverage
tables all stand — they were verified independently of the novelty claim.
`DENOMINATOR_TOWER_v1`, `PRIME_BOUND_NULL_v1` and `RESIDUAL_ANGLE_v1` build on the lemma, not
on its being new, and are unaffected.

## 5. Ledger

`[RETRACTED]` `SMALL_DENOMINATOR_WITNESS_v1` §3's novelty claim, in full.
`[quoted]` §1, the prior statements with file and line.
`[recorded]` §2, the cause: a literal-digit grep against a general statement, plus publishing
on a search that had been abandoned mid-run.
`[UNVERIFIED]` every remaining novelty attribution in §3's table.

`n = 8` is **not proved.**
