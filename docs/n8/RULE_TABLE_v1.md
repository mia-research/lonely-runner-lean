# The rule table for door 4: what is derived, what is fitted, and why fitting does not converge

2026-09-18. Artefacts: `experiments/n8/rule_table_v1/`. Continues `DOOR4_v1` §13, which ruled the
density route an import and set the native task: **exhibit a rule naming a lonely `(e, k)`, with its
conditions shown exhaustive.**

---

## 1. Rules derived from the framework  `[these stand]`

**R0 — the first opening admits only the nearest flank.** `[PROVED]`
`Flanks.inWay_at_first_opening_of_lt`, `eq_min_of_lonely_first_opening`. Flank `b`'s opening `k = 0`
is `1/(n·b)`, where a runner at `m < b` reads `m/(n·b) < 1/n` and is in the way. So the `k = 0` layer
is **exhaustively** the single flank `b = min ds`.

**R0′ — the opening lower bound.** At flank `b`, opening `k`, the nearest runner reads
`m(nk+1)/(nb)`; if `m(nk+1) < b` that is below `1/n` and `m` is in the way. So

    lonely at (b, k)  ⟹  b ≤ m·(n·k + 1),   i.e.   k ≥ ⌈(b/m − 1)/n⌉

Verified with **0 violations over 1,252,558 openings**. It subsumes R0 at `k = 0`. It is a correct
pruning rule but a weak one — it removes 2.7% of openings.

**R1 — the nearest flank, with an exact condition at `m = 1`.** Take `b = min ds`. When `m = 1` the
flank has only `k = 0`, and the condition there is **exactly** *no difference divisible by 8*:
agreement **20,000/20,000**. This settles all three tight configurations, whose locators sit at
`±1 (mod 8)` (`DOOR4_v1` §9a).

R1 covers 0.552 at `k = 0` and 0.82 allowing `k < m`.

## 2. Rules fitted to the data  `[these do not stand]`

Continuing the table by choosing a fallback flank fails, and the failure is measurable.

| step | coverage on `[1,14]` | uncovered |
|---|---|---|
| R1 (nearest flank) | 0.769 | 792 |
| R1 ∨ "largest flank" | 0.9843 | **54** |
| R1 ∨ largest ∨ "largest odd not divisible by 8" | 0.9848 | 52 |

The 54 uncovered are highly structured — **every one contains both 7 and 8**, and every one contains
a multiple of 8. But no single fallback clears them: flank 7 serves 49 of 54, "second largest" serves
46, "largest not divisible by 8" serves 2.

**And the residue grows with the range.** The same three rules leave **52** sets uncovered on
`[1,14]` and **107** on `[1,17]`. The *fraction* improves (0.9848 → 0.9945) while the *count* rises.
Adding rules one at a time is not converging on anything; it is fitting a list to a sample.

## 3. The distinction that matters

A framework rule is **derived** — it comes from the construction and carries a condition the
construction supplies. R0, R0′ and R1's `m = 1` condition are of that kind: each has a one-line
reason and an exact statement.

"Take the largest flank", "take the largest odd flank not divisible by 8" are **fitted** — chosen
because they scored well on a sample, with no reason behind them and exceptions that multiply. They
are not rules in `FRAMEWORK_CONJECTURE_v1` §3's sense, and a table built from them would not have its
conditions *shown* exhaustive, only *observed* so on a range.

**This reinforces `DOOR4_v1` §6** rather than working around it. §6 showed no single designated flank
works; §2 here shows no short list of them works either. Whatever names the flank must be
**parameterised by the set** — computed from `ds` — rather than selected from a fixed menu.

## 4. Seventh sampler failure

Random sampling reported that "largest flank" clears **100%** of R1's failures — 7,374 of 7,374.
Exhaustive search over `[1,14]` finds **54** it does not clear. The sampler again missed the
structured hard cases, which here are exactly the sets containing both 7 and 8.

The standing rule stands: on this problem, exhaustive enumeration over a bounded range is the only
search that has ever found the binding cases. Every coverage figure above is exhaustive.

---

## 5. Combinations of flanks — the owner's question, and it changes the picture

**The question.** If no single flank rule works and no short list of them works, is it the right
*combination* of flanks that is required?

**A mechanism I tried first, and it failed.** Making a runner the flank *neutralises* it — at its own
openings it sits exactly on the band edge and never blocks — so the flank to choose should be the
runner that otherwise blocks most. It has a reason, and it is worse than the fitted rule:

| rule | `[1,14]` | `[1,17]` |
|---|---|---|
| nearest (R1) | 0.7692 | 0.5697 |
| worst blocker, globally | 0.7773 | 0.7493 |
| worst blocker at the nearest flank | 0.8962 | 0.9504 |
| largest (fitted) | 0.9630 | 0.9859 |

Having a reason did not make it right. `[REFUTED]`

### 5a. No pair suffices; a triple does  `[VERIFIED — exhaustive]`

Testing every pair and triple of flank **ranks** (0 = smallest … 6 = largest):

| | `[1,14]` | `[1,17]` |
|---|---|---|
| best single rank (6, the largest) | 0.9630 | 0.9859 |
| best pair, `(4,6)` | 0.9977 | 0.9993 |
| **pairs covering every set** | **none** | **none** |
| **triple `(4,5,6)` — the three largest** | **1.0000** | **1.0000** |
| triple `(2,4,6)` | 1.0000 | 1.0000 |
| triple `(3,5,6)` | 0.9997 | 0.9999 |

Not every triple works — `(3,5,6)` fails. But `(4,5,6)` holds across **widening exhaustive ranges**:

| range | primitive sets | failures of `(4,5,6)` |
|---|---|---|
| `[1,17]` | 19,440 | **0** |
| `[1,20]` | 77,400 | **0** |
| `[1,22]` | 170,213 | **0** |
| spread-biased sample | 40,000 | **0** |

≈307,000 sets, zero failures — and all three tight configurations are covered. **This behaves
unlike the fitted single-flank rules**, whose uncovered count *grew* with the range (54 → 107).

### 5b. The binding case is unique

Distribution of the number of working flanks per set:

| working flanks | 1 | 2 | 3 | 4 | 5 | 6 | 7 |
|---|---|---|---|---|---|---|---|
| `[1,20]` | **1** | 40 | 657 | 4,500 | 15,305 | 28,314 | 28,583 |

Across 77,400 sets there is **exactly one** with a single working flank — `(2,3,4,5,6,7,16)`, the same
set in both ranges — and its unique flank is the **largest**, rank 6. No set anywhere has its only
working flank below rank 4, which is precisely what the triple `(4,5,6)` needs.

### 5c. Status, stated exactly

**The owner's reframing is right**: combinations succeed where single flanks and short lists fail, and
the jump is from "no pair ever suffices" to "this triple never fails".

**But it is `[EMPIRICAL]`, not derived.** The triple was found by searching all 21 pairs and 35
triples, so its origin is fitting — and `(2,4,6)` works equally well, which undercuts any story about
the three largest specifically. What is missing is a *reason* three flanks suffice and two never do.
Until that exists this is a candidate rule with an exhaustive range behind it, not a rule with its
conditions shown exhaustive.

**What would settle it**: an argument that the set of working flanks can never be confined to ranks
`0–3`. The data says it is confined to a single flank exactly once in 77,400 sets, and that flank is
the largest.
