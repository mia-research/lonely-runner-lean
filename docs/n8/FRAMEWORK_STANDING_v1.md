# Where the framework stands

*Version 1, 2026-09-20. A statement of standing, written after the session that refuted
`DoorFirstLap`, amended the obligation of record, and established that the analytic route is closed
for a proved reason. It supersedes no numbered result. Nothing here is graded above what its own
artefact supports.*

---

## 1. The contribution, stated once

**The framework is a reduction, and the reduction is proved.**

The lonely runner conjecture at eight runners asks for a real instant `t > 0`, quantified over a
continuum. The framework converts that into a finite arithmetic question about data read off the
speeds, and it does so by theorems rather than by measurement.

| step | declaration | hypotheses |
|---|---|---|
| loneliness of a subject is `Lonely` on its own disparities | `Arrangement.lonelyAt_iff_lonely_diffSet` | **none** |
| every lonely instant is matched by a lonely **opening** no later than it | `ConstructionN.reading_complete`, `opening_le` | positivity, nonemptiness |
| so loneliness is a statement about flanks | `Flanks.exists_flank_of_lonely`, `lonely_iff_exists_flank` | positivity, nonemptiness; over `ℝ` |
| an opening is the first spine point of a **candidate scale** `e/(8k+1)` | `ScaleCandidates.flankOpening_eq_spine`, `candidateScale` | `0 < e` |
| **the obligation, with no time and no iteration** | `ScaleCandidates.lonely_iff_exists_candidate_scale` (Thm 6.15) | positivity, nonemptiness |
| the same on arrangements, both directions | `LRC.Spec.doorFlank_iff`, `doors_agree` | injectivity |
| and it closes the conjecture | `LRC.Spec.lonelyRunnerAt8_of_doorFlank` | — |
| the openings at a flank are **periodic in `k` with period dividing `e`**; the count is exactly `e` when every `gcd(d,e)` divides `e` with the quotients coprime | Theorem 15.39 (`Openings.lcm_div_eq`) | as stated there |

`[PROVED — Lean, axiom-clean at [propext, Classical.choice, Quot.sound], no sorry]`

Read together: **the subject is lonely at some positive instant iff some candidate scale `e/(8k+1)`
is clear for every disparity**, with `e` a disparity of the subject and `k` a lap index, both read off
the speeds. No quantifier over time. No iteration. No bound on when or on how many.

Two things follow and are worth stating separately. The search space per
flank is finite and of known size. And the conjecture at eight runners becomes, per input, a question
about residues — which is why the rest of this document is arithmetic.

## 2. The analytic route is closed, and this is proved

Not "nobody managed it". The clear set can have empty interior.

For the arithmetic progression `{1,…,7}` — the extremal case — the set of lonely instants on `(0,2]`
is **exactly** `{1/8, 3/8, 5/8, 7/8, 9/8, 11/8, 13/8, 15/8}`: eight isolated points, Lebesgue measure
zero. `[VERIFIED — exact rational arithmetic; experiments/n8/clear_set_measure_v1.{py,out}]`

Every analytic method — averaging, integration, perturbation, compactness, stability radius —
locates a target through neighbourhoods. At the extremal configuration there are none. The
clearance condition is also discontinuous in the data: `u = 1/2` has period 2 in the opening index
while `u = 1/2 + ε` has period enormous, so no limiting argument transfers information between
nearby configurations.

This is the load-bearing reason behind §6A rows six and seven. They are not stylistic preferences.
**Appendix A route 1 said this from the start** — *"the set on which such a comparison would have to
find room has length zero in the case that matters. Any argument must name an instant."*

## 3. Two senses of "analytical", and which one is available

- **Analytic**, using analysis: closed, by §2.
- **Analytical**, meaning derived and general rather than enumerated: available, and it is what §1 is.

`reading_complete` holds for every positive difference set by an argument, not by cases.
`TwoMover.card_allowed_two_mul` holds for every `p, q` by a formula, not by a table. Grading the
framework against the first sense while building the second is a mismatch of labels, not a shortfall
of results.

## 4. What is proved on top of the reduction

Each of these names an instant. None is a bound, a cap, a count or a rate.

| rule | condition | instant | grade |
|---|---|---|---|
| **Theorem 4.8** | `d_max ≤ 7·d_min` | `1/(8·d_min)` | `[PROVED — Construction8.ratio_condition]` |
| **window rule** | the six non-flank disparities lie in `[e/A, 7e/A]`, `A ≡ 1 (mod 8)` | `A/(8e)` | `[PROVED — FirstLap.flank_clear_of_window, _of_bounds]` |
| **integer ratios** (`m = 0` movers) | every `d/e` an integer | any opening, iff `8 ∤ d/e` | `[PROVED — Flanks.integer_ratio_clear_iff]` |
| **one mover** (`m = 1`) | one non-integer ratio | an opening of that flank, index bounded by `~1/min(f,1−f)` | `[PROVED — Flanks.exists_clear_step, n ≥ 4]` |
| **critical family** | six disparities in `[2s,7s]` plus `16ks` | `flankOpening 8 (16k) k` | `[PROVED — WitnessFamily.lonely_witness_family]`; a **corollary** of the window rule, which fires wherever it does |
| **mover half-period** | any single mover | — | `[PROVED — TwoMover.card_allowed_two_mul, _lt]`: a mover never blocks more than half its own period, and blocks exactly half only at `q = 2` |

**On reach figures.** None are quoted here. The conjecture ranges over `Fin 8 → ℝ`, which carries no
canonical measure, so "fraction of arrangements covered" is a property of the enumeration. The same
window rule scores **1.80%** on log-uniform reals and **84.95%** on uniform reals in `[1,10]`
(`experiments/n8/`, this session). §6.7's **39%** inherits the same exposure and should be read the
same way. Reach numbers are diagnostics on a named scheme; they are not progress, and they are not
quoted as such.

## 5. What is open, as a disjunction

At a flank `e`, a disparity `d` reads `circDist(k·f_d + c_d)` with `f_d = fract(d/e)` and
`c_d = (d/e)/8` (`Flanks.fractional_ratio_circDist`). Disparities with `f_d = 0` are static and
decided by divisibility; the rest are **movers**. The obligation is the ladder in the number of
movers `m`:

| `m` | status |
|---|---|
| 0 | `[PROVED]` — `integer_ratio_clear_iff` |
| 1 | `[PROVED]` — `exists_clear_step` |
| 2 | **false unconditionally.** `(u₁,u₂) = (1/2, 7/2)` has period 2 and both indices blocked; the failing class is exactly both denominators `2` with one blocked at `A ≡ 1` and the other at `A ≡ 9 (mod 16)`. `[VERIFIED — exhaustive over denominators ≤ 29]`. Under the exclusion the core lemma is `[PROVED]` (§4); the lift to `lcm(q₁,q₂)` is not yet written. Proposition 6.10 was **withdrawn** and nothing here reinstates it |
| ≥3 | open |

## 6. The obstacle to climbing that ladder

Stated without measurement: **at the largest flank every other disparity is a mover**, since `d < e`
forces `e ∤ d`. So `m = 6` at `d_max` for every difference set, without exception. Flanks with few
movers are flanks that divide many disparities, and those are small flanks with few openings
(Theorem 15.39: the period divides `e`, so at most `e` of them).

The two requirements therefore pull against each other, and this is not a conjecture about the
ladder — it is why a selector maximising the smallest modulus performed **worse** than simply taking
`d_max` when measured. Climbing to `m = 2` is not shown to advance the general case, and `m = 2`
already needed an exclusion class that `m = 1` did not.

## 7. What the empirical work did, and did not do

It guided and it confirmed. It found the critical family, the concentration of witnesses at high
flank rank, and the denominator-2 failure class. It never carried a theorem, and the manuscript's
grading says so nearly everywhere.

Two places it leaked into load-bearing status, both corrected on 2026-09-20:

- **`DoorFirstLap`** — a cap `τ = d_min·t ≤ 1` extrapolated from an exhaustive `[1,22]` measurement
  and written into `Spec/Doors.lean` as a `Prop`. It is `[REFUTED]` by §6.7's own 28-move case at
  `τ = 2401/1872`. Lean did not catch it because a `def … : Prop` is a statement, not a claim: it is
  type-checked, never proved, and the axiom and `sorry` scans have no proof to inspect.
- **Coverage percentages** used as progress rather than as diagnostics (§4).

## 8. What is not claimed

The conjecture at eight runners is not proved. No cap, no bound on the opening index, and no witness map total on the inputs is supplied. The discharge criterion in `LRC/Spec/Target.lean` — a witness
map plus a theorem that it works, quantified over every injective `v` and every subject — is
unchanged and unmet.

**The standing is this.** The reduction is done, proved, and stands on its own. The arithmetic
sitting above it is open, and the two partial mechanisms proved so far are not on a route to closing
it. That the analytic route is closed is itself a proved result rather than a record of attempts, and
it is the reason the remaining work is arithmetic.
