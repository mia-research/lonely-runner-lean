# How the needle moved: a review of method, not results

Covers the arc from the depth investigation to the present, across 34 commits. The question is
**what process turned a measurement into a rule, a rule into a mechanism, and a mechanism into a
theorem** — and what was gained by refusing to apply anything wholesale.

---

## 1. The loop that produced every result

Every theorem in this arc came out of the same four-step loop. Not one came from planning a proof.

```
  measure something exactly  →  ask WHY that number and not another
        →  compute the object the answer names  →  the answer is a framework constant
```

The fourth step is the one that matters. **Every time the loop closed, the answer named something
already in the framework** — never a new tool:

| measurement | the "why" | the constant it named |
|---|---|---|
| divisor-closed clears, 1.66M profiles | clear set of `q mod b` is *all nonzero residues* for `b ≤ 7`, breaks at 8 | `n − 1`, Theorem 4.8's constant |
| solution count never exactly 1 | a reflection `r ↦ b − r` acts | obstructed at `b ≡ 0` (collision) and `b ≡ 1` (guard relation) |
| left-endpoint family covers 0% | it is integral only when `8 ∣ b`, and blocked there | `reflect_fails_zero` — a theorem, not a shortfall |
| min speed blocks 21.94% | rate depends on `β = a/gcd` | `β=1` is `self_never_blocks`; `β=2` is the Klein `{±1}` subgroup |
| rational vs integer readings | clear denominators, `a₁ = Q` | "the reduced speed set contains 1" |

The one time an *external* tool was reached for — Hunter–Kounias — it was both an import (violating
the firewall in spirit) and wrong (a counterexample at `(1,6,275,350,545,672,762)`). That is the
single cleanest datum in this review.

## 2. The eight moves, and the instance that taught each

**1. A percentage is an unfinished question, not a result.** Depth measured 81.3%; chasing the other
18.7% produced the exact mechanism. This recurred at every scale and is now standing practice.

**2. Convert the search into what it computes.** "Is there a way to turn the search into a rule?"
produced the gap rule (`N/(s·s')`, `N ∈ ℤ`) and the reach rule (the fold as an `↔`). A search is an
algorithm; asking for its closed form is always available and was never wasted.

**3. Let each proved part pose the next question.** The chain `converse → iff → returns a point →
what kind of number → bounded denominator → finite check → no division` was not planned. Each
theorem's *output* determined what to ask next. Planning would not have found it.

**4. Ask why it does NOT follow, not whether it does.** The 603 divisor-closed failures: asking
"why" found a `1/8` offset in my own rounding and closed the category. Asking "does it work" had
already produced a false structural "facet" built on `b = 2`.

**5. Drop the non-native step.** "Is rounding needed, when everything else is exact?" — no. Every
error in that thread (the offset, the phantom failures, a 35-vs-28 threshold confusion) came from the
one imported step. Removing it left a clean `ℤ` statement.

**6. Explain the complement.** "Any stated fraction needs the other percentage explained." Applied
three times, it produced: a theorem (the 0%), a unification (61.17% is one phenomenon, not three),
and a correction (the cost is 5.76%, not 21.94%). Every application paid.

**7. Name which axiom of the mapping fails.** When the cage did not transfer to candidate points, the
useful output was not "it fails" but *"the cage is stated at grid instants; `(8m+1)/sₖ` is one only
when `sₖ ∣ (8m+1)`; the condition lives mod `8sₖ` and reducing mod 8 discards what decides it."*
That diagnosis produced `gcd_covariant` — the cage's actual content.

**8. A rule must name a candidate.** A scan reported 100% coverage everywhere; its "endpoint rule"
searched every reading at every level, i.e. the whole candidate set, so it restated `finite_check`.
A mechanism names one candidate; a search does not.

## 3. What refutation bought

Nine things were refuted in this arc. **None was a loss.** Each removed a family of attacks and left
a reusable reason.

| refuted | the reason, which is the asset |
|---|---|
| `s = s*` (18,809 counterexamples) | `(s·A) mod 8s = s` for *every* reading — the argument never singled out `s*` |
| largest reading (794) | no threshold; failures persist at `s_max = 41,48,56,80` |
| even readings caged (49.7% block) | domain mismatch — grid instants vs candidates |
| Hunter–Kounias | an import; and fails |
| product of conditionals (2,594/3,000) | joint density sits *below* the product — **all** independence-style arguments foreclosed |
| bounded centre offset | grows with `m`; binding constraint is the largest even-quotient modulus |
| left endpoints (0%) | `reflect_fails_zero` — foreclosed by a theorem we already had |
| extending the primorial to 2310 | "nonzero residue ⟹ clear" is exactly what breaks at `b = 8` |
| density as the object | abundance is the *worst* frame when correlation is adverse |

The two most valuable entries are the ones that closed whole families: adverse correlation kills
every counting argument, and the extremal-witness supply is **exhausted at 38.83%** (spine plus both
endpoint families, gated by `8 ∣ m` or `8 ∣ b`, one of the three foreclosed). Those are permanent
reductions of the search space.

## 4. Why "holus bolus" failed, and what replaced it

Three times a proved result was carried across wholesale and was wrong:

- the cage applied to candidate points — false, even readings block half the time;
- `witness_normalised` applied as the general witness supply — provably cannot finish 43.91% of the
  divisor-closed category, because integrality admits only *interior* witnesses and normalisation
  produces *extremal* ones;
- the `b ≥ 28` margin argument "confirmed" on a population that was almost entirely the easy half.

What replaced it each time was the same discipline: **exhibit the mapping, check its hypotheses, and
name the axiom that fails.** That is the project's own driver, and it converted all three failures
into content — `gcd_covariant`, the integrality obstruction, and the `lcm(bᵢ) = m` split.

The narrow-but-complete result also beat the broad one consistently. The all-`b ≤ 7` sub-category is
tiny (240 profiles under `m = 6000`) and **closed by argument**. The wholesale claims were larger and
wrong.

## 5. Failure modes that recurred, and what caught them

| mode | instance | what caught it |
|---|---|---|
| range/sampling bias | categories C3, C4: 0 failures sampled → 408 and 177 exhaustive | testing the *known* counterexample first |
| unrepresentative population | `b ≥ 28` "confirmed" | splitting on the structural variable (`lcm = m`) |
| circular rule | scan reporting 100% | asking what the rule actually names |
| proxy counting | 745 theorems (versioned supersets); a doc-comment line counted as a declaration | counting the object, comments stripped |
| unearned novelty | "sharpens the conjecture" | a literature check, which found an existing normal form |
| claim without artifact | "axiom-clean" with nothing deposited | `compile-diff`, which demanded the witness |

Five of the six were caught by an external check or by the owner, not by me mid-flow. That is the
honest reading of the record.

## 6. What the method has NOT delivered

Stated plainly, because the review is about process and the process has a ceiling here.

- **No live frontier has been closed.** Divisor-closed is `[VERIFIED]` on 51,295 exhaustive profiles,
  not proved. Branch B resists every named rule tried (best union 59.49%).
- One category *was* closed by argument — divisor-closed with every middle quotient `≤ 7` — and it is
  narrow.
- The gains are: a proved reduction to `ℤ`, the reflection apparatus, four route-families closed with
  reasons, two frontiers shown to be one question, and 39 axiom-clean declarations.

The method reliably converts measurements into mechanisms and mechanisms into theorems. It has not
yet converted a mechanism into an existence proof, and the reason is now specific rather than vague:
**every tool built so far locates extremal objects, and the remaining cases admit only interior
ones.**
