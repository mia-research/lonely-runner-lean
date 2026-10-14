# Door 4, opened: the flank search modulo `b`

2026-09-18. Lean: `LRC/Cascade/Flanks.lean`, three new theorems, all axiom-clean, build 2443 jobs.
Artefacts: `experiments/n8/door4_v1/`. Door 4 is `ExistenceAt8_flank` — see `ATTACK_SURFACE_v1`.

---

## 1. The modulus drops from `n·b` to `b`  `[PROVED]`

`clear_at_int_flank_iff_emod` works modulo `n·b`. Split `a = n·q + s` with `0 ≤ s < n`. Then
`a(nk+1) = n(ak + q) + s`, so the residue modulo `n·b` is `n·((ak+q) mod b) + s`, and:

    Flanks.clear_at_int_flank_iff_emod_b :
      clear at flank b, opening k  ↔  b − s ≤ n·((a·k + q) mod b) ≤ (n−1)·b − s

Checked against the direct form before formalising: **200,000 cases, 0 disagreements**.

**Two things this makes visible that the `n·b` form hides.**

- The condition on `k` is an **arithmetic progression `a·k + q` modulo `b`, landing in a fixed
  interval** — one progression per runner. At `n = 8` the interval has length exactly `3b/4`: the
  middle three quarters.
- **The flank contributes no constraint.** For `a = b` the progression is constant at `q = ⌊b/8⌋`,
  which is exactly the interval's **left edge** — verified 20,000/20,000. So at order 8 there are
  **six** real conditions, not seven.

So door 4 over whole numbers is: *six arithmetic progressions mod `b`, each required to land in its
own interval of relative length `3/4`, must have a common `k`.*

Heuristic density `(3/4)^6 = 0.1780`. Observed at flank `b = max ds`: **median 0.1831**, 10th
percentile 0.1364, minimum 0.0476 over 3,000 sets, and **zero** sets where that flank had no lonely
opening. The conditions behave close to independently, which is why the union bound — `6 × 1/4 = 1.5`
— is the wrong instrument: it adds the failure probabilities where the truth is nearer a product.

## 2. The `k = 0` layer collapses to one flank  `[PROVED]`

    Flanks.inWay_at_first_opening_of_lt : 0 < m → m < b → inWay n m (flankOpening n b 0)
    Flanks.eq_min_of_lonely_first_opening : a lonely first opening forces b = min ds

Flank `b`'s opening `k = 0` is `1/(n·b)`, where a runner at difference `m < b` reads `m/(n·b) < 1/n`
and is in the way. So **only the nearest flank can be free at `k = 0`**, where the condition is
`clear_at_bound_of_ratio`.

This was found as a measured coincidence and then explained: over 20,000 primitive sets, "some flank
works at `k = 0`" and "the *minimum* flank works at `k = 0`" hold on **exactly** the same 11,167 sets.

## 3. How deep the search goes

| | coverage |
|---|---|
| `k = 0` (now a single flank) | 0.552 |
| `k ≤ 2` | 0.938 |
| `k ≤ 8` | 0.999 |

Tight sets `{1,2,3,4,5,6,7}`, `{1,2,3,4,5,7,12}`, `{1,4,5,6,7,11,13}`: all settled at **`k = 0`**, at
flank `b = 1`, where the condition collapses to *no difference divisible by 8*. **The tight
configurations are not the hard ones for door 4.** The named hard arrangements need `k = 6` and
`k = 4`.

**`k` is not bounded**, and a layered proof by cases on `k` therefore cannot terminate:
`bounded_k_attack_v1` reaches `k = 369` at spread ≈ 14,125. The layers above are coverage, not a
proof strategy.

## 4. What door 4 now needs

Stated in the framework's objects, with no trajectory in it:

> Let `b = max ds`. For each `a ∈ ds` write `a = 8q_a + s_a` with `0 ≤ s_a < 8`. Show there is
> `k ∈ [0, b)` with `(a·k + q_a) mod b ∈ [(b − s_a)/8, (7b − s_a)/8]` for every `a`.

Six non-trivial conditions, each of relative length `3/4`. The union bound is vacuous at `1.5`;
measurement says the true density is near the product `0.178`. **The gap between those two numbers is
the whole problem**, and closing it means showing the six progressions cannot conspire — which is a
statement about `a·k mod b` for six values of `a`, not about the cascade.

Known obstruction, recorded so it is not rediscovered: the interval does not factor under CRT, so
splitting `b` into prime parts does not split the condition.

---

## 5. The conditions are near-independent  `[VERIFIED]`

6,000 pairs at flank `b = max ds`:

| | |
|---|---|
| marginal clear density | **0.7498** (predicted `3/4`) |
| joint minus product | mean `+0.0063`, median `+0.0024`, range `−0.0398` to `+0.2222` |
| pairs deviating by more than 0.15 | **1 of 6,000** |
| count vs the independent prediction `b·(3/4)^6` | median ratio **1.028**, min 0.261 |

So the union bound is not merely crude, it is the wrong shape: it adds failure probabilities where
the truth is within 3% of a product. That is the quantitative reason door 4 is worth attacking and
the counting routes are not.

**Where correlation does appear, it is a gcd effect.** The worst pair found was `a₁ = 28, a₂ = 56`
at `b = 84`, where `gcd(28,84) = gcd(56,84) = 28`: there `p₁ = p₂ = p₁₂ = 0.667`, so one condition
*implies* the other. A runner sharing a large gcd with the flank has a coarse progression — `a·k mod b`
ranges only over multiples of `gcd(a,b)` — and coarse progressions correlate.

## 6. No designated-flank rule works  `[REFUTED — four rules]`

The natural next move is to name the flank rather than quantify over `ds`. It fails. Over 20,000
primitive sets, counting lonely openings at the flank each rule selects:

| rule | min | median | sets with **zero** |
|---|---|---|---|
| `b = max ds` | 2 | 15 | 0 |
| `b` minimising the largest `gcd(a,b)` | 0 | 11 | **357** |
| `b` maximising `b / max gcd(a,b)` | 0 | 12 | **9** |
| largest `b` coprime to all others | 0 | 12 | **259** |
| **best over all seven flanks** | 3 | 15 | 0 |

`b = max ds` is the best simple rule and beats every gcd-aware refinement — the gcd intuition of §5
predicts correlation correctly but selects flanks badly. **And `b = max ds` still fails**: on the tight
set `{1,2,3,4,5,7,12}` it gives **zero**, while flank `b = 1` gives one.

**Consequence.** Any proof of door 4 must genuinely use the existential over flanks. A theorem of the
form *"flank `R(ds)` always has a lonely opening"* is false for all four natural choices of `R`, and
the statement `ExistenceAt8_flank` has its `∃ e ∈ ds` for a reason. This closes the designated-flank
family of approaches.

## 7. Where the statement is tight

Best-over-all-flanks is `≥ 3` on 20,000 random sets but exactly **1** on each of the three tight
configurations `{1,2,3,4,5,6,7}`, `{1,2,3,4,5,7,12}`, `{1,4,5,6,7,11,13}` — a single lonely opening
across all seven flanks, at `b = 1`, `k = 0`, `t = 1/8`.

So door 4 is tight precisely at the extremal configurations, as it should be, and any argument must
survive a margin of exactly one opening there. An argument with slack to spare will not be provable;
it has to be exact at those three points.

---

## 8. The Fourier split: the main term is robust, but relation size does not control the error

Writing `N(b)` for the number of lonely openings at flank `b` and expanding each interval indicator
over `ℤ/b`:

    N(b) = b · Σ_{h : Σ hᵢaᵢ ≡ 0 (mod b)}  Π Îᵢ(hᵢ) · e(Σ hᵢqᵢ / b)

The `h = 0` term is `b·Π(|Iᵢ|/b)`, and **every** error term requires a non-trivial relation
`Σ hᵢaᵢ ≡ 0 (mod b)` among the six non-flank runners.

**The main term is robust** `[VERIFIED — 4,000 flanks, `b = max ds`]`:

| actual / main term | min | 1% | median | max |
|---|---|---|---|---|
| | **0.324** | 0.550 | **1.013** | 2.076 |

It is never overwhelmed: the error reaches at most about 68% of the main term in the worst case
observed, and `N(b) > 0` throughout. The median of 1.013 confirms the expansion.

**But relation size does not predict the deficiency** `[REFUTED — my own hypothesis]`. The natural
next step is to bound the error by the size of the smallest relation, since a large `|h|` forces small
`Î(h)`. Measured on the extremes, searching `|hᵢ| ≤ 3`:

| flank | ratio | smallest relation (L1 weight) |
|---|---|---|
| `(9,11,14,16,25,37,52)`, `b=52` | 0.324 | **3** |
| `(1,28,30,55,58,70,84)`, `b=84` | 0.329 | **3** |
| `(11,16,25,27,43,75,81)`, `b=81` | 0.344 | **3** |
| *typical*: `(3,27,33,52,60,73,85)`, `b=85` | **1.000** | **2** |
| *typical*: `(20,26,36,59,63,73,85)`, `b=85` | **1.000** | **2** |

**The typical flanks have *smaller* relations than the worst ones.** A weight-2 relation here is just
`aᵢ + aⱼ = b` — present and harmless. So the error is not governed by how short the shortest relation
is; the phases `e(Σ hᵢqᵢ/b)` and the coefficients `Îᵢ(hᵢ)` matter as much as the relation lattice,
and they can cancel or reinforce independently of `|h|`.

**What this closes.** An argument of the form *"the smallest relation is large, therefore the error is
small, therefore `N(b) > 0`"* will not work, and neither will its contrapositive as a case split.
Whatever controls the error at door 4 is finer than the relation lattice alone.

**What it leaves.** The main term is right and robust — median ratio 1.013, never overwhelmed across
4,000 flanks. Door 4's arithmetic remains favourable; what is missing is an error bound, and the
measurement now says that bound cannot come from relation size by itself.

---

## 9. Two locators, six conditions — the owner's split, tested

**The suggestion.** Loneliness constrains only the subject's **two adjacent gaps**; the other six of
the eight gaps are free. So perhaps the error is tied to the six free gaps rather than to the two
that locate the isolation event.

### 9a. The locators are real, and they have an arithmetic identity  `[VERIFIED]`

At `t = 1/8` a runner's distance is `circDist(a/8) = min(a mod 8, 8 − a mod 8)/8`. So:

    distance exactly 1/8  ⟺  a ≡ ±1 (mod 8)
    distance  < 1/8       ⟺  a ≡ 0  (mod 8)

Checked on the three tight configurations at their **unique** lonely opening (`b = 1`, `k = 0`):

| tight set | distances | exactly at `1/8` |
|---|---|---|
| `{1,2,3,4,5,6,7}` | `1/8, 1/4, 3/8, 1/2, 3/8, 1/4, 1/8` | **1 and 7** |
| `{1,2,3,4,5,7,12}` | `1/8, 1/4, 3/8, 1/2, 3/8, 1/8, 1/2` | **1 and 7** |
| `{1,4,5,6,7,11,13}` | `1/8, 1/2, 3/8, 1/4, 1/8, 3/8, 3/8` | **1 and 7** |

**Every one is located by exactly two runners, and in every case they are the residues `±1 (mod 8)`
— here `1` and `7`.** That is a clean identification of the objects the owner named, and it was not
in the record.

It also explains §3: at `b = 1, k = 0` the criterion is *no difference divisible by 8*, i.e. no
runner at residue `0`; the runners at `±1` sit on the boundary and are clear by the `≤` in `Lonely`.

### 9b. At solutions, almost nothing else is tight  `[VERIFIED]`

Runners within `1/8 + 1/100` of the subject, over 21,678 lonely openings:

| runners near the boundary | 1 | 2 | 3 | 4 | 5 | 6 |
|---|---|---|---|---|---|---|
| openings | **17,905** | 3,322 | 368 | 67 | 14 | 2 |

**83% of lonely openings have exactly one runner near the boundary**, 15% have two. So at a solution
the other five have genuine slack — the constraint is six-dimensional but few conditions are active
where it is satisfied.

### 9c. But the exclusion does not concentrate — the strong form fails  `[REFUTED]`

If the six conditions were really two-plus-free, blocking would concentrate in two runners. It does
not. Over 1,500 flanks, the share of all blocking done by the top two runners:

| | min | median | max | six equal would give |
|---|---|---|---|---|
| all blocking | 0.333 | **0.344** | 0.475 | 0.333 |
| sole blocking | 0.353 | 0.450 | 0.767 | 0.333 |

**Median 0.344 against 0.333 — the six block essentially uniformly.** The concentration in *sole*
blocking is mild (0.450). So the error cannot be attributed to a distinguished pair: which runners
are tight varies with `k`, and every runner blocks its share.

### 9d. What this leaves

The split is real at **solutions** and false at **constraints**. Two runners locate the isolation
event — identified here as the residues `±1 (mod 8)` — and at a typical solution only one runner is
even close to binding. But all six conditions do equal work in excluding the non-solutions, so an
error bound cannot be built by demoting four of them.

The usable part is 9a: the extremal configurations are exactly those carrying runners at `±1 (mod 8)`
with nothing at `0 (mod 8)`, and their single lonely opening is `t = 1/8`. That is a complete
description of where door 4 is tight, in residues, and it is the sharpest handle yet on the three
cases any proof has to be exact at.

---

## 10. Is the constraint system an artefact of the ordering?

Three things could be meant, and they separate cleanly.

**The listing order: no.** The constraint system at flank `b` is indexed by the *elements* of `ds`,
which is a `Finset` — unordered. Nothing in it can depend on how the differences are listed.

**The subject choice: absorbed, but it is where the difficulty lives.** Every set of 7 distinct
positive reals arises as a difference set, via `v = (0, a₁, …, a₇)`, so quantifying over all `ds`
adds nothing and loses nothing. But *which* `ds` an arrangement hands you depends on which runner is
the subject, and that choice matters enormously. Across the eight subjects of one arrangement, the
best-count spread is **median 10, max 22** (1,500 arrangements).

**The mechanism is duplicate collapse.** In the extremal arrangement `v = (0,1,…,7)`:

| subject | differences | as a set | card |
|---|---|---|---|
| 0 | `1,2,3,4,5,6,7` | `{1,…,7}` | **7** |
| 1 | `1,1,2,3,4,5,6` | `{1,…,6}` | 6 |
| 3 | `1,1,2,2,3,3,4` | `{1,2,3,4}` | **4** |
| 7 | `1,2,3,4,5,6,7` | `{1,…,7}` | **7** |

Interior subjects lose differences to collapse — `|vⱼ − vᵢ|` coincides ahead and behind — so they
face **four** conditions, not seven, and are correspondingly easier. Per-subject best counts for that
arrangement are `[1, 2, 3, 2, 2, 3, 2, 1]`: **only the two extreme subjects are tight.**

(This is also why `ds.card ≤ 7` in the target must be `≤` and not `=`, measured earlier at §1 of
`EXISTENCE_FRAME_CHECK_v1`: the collapse is real and common.)

**And in generic arrangements it inverts.** The hardest subject is an extreme runner in only
**6 of 1,500** arrangements — against 2/8 = 0.25 by chance — while the hardest subject index is
strongly peaked in the middle:

    index:   0    1    2    3    4    5    6    7
    hardest: 11   72  289  488  420  190   28    2

So "the extremes are hardest" is a property of the *extremal* arrangement, where collapse spares the
interior, and it reverses in the generic case. No fixed subject index is ever safe, and the hardest
subject's count was never zero (min 3 over 1,500).

**What this means for the error bound.** The eight subjects of one arrangement are coupled — they
share the 28 pairwise differences, each appearing in exactly two of the eight sets — and
`ExistenceAt8` discards that coupling by quantifying over `ds` independently. That discard is
*correct and unavoidable*: LRC asks for every runner to be lonely, so knowing that *some* subject is
easy would not help. The coupling is not a resource the error bound can draw on.

**A correction.** The script that produced these numbers printed a label claiming every subject of the
extremal arrangement is tight. The data it printed alongside, `[1,2,3,2,2,3,2,1]`, says otherwise —
only the extremes are. The label was wrong and is fixed in the deposited copy.

---

## 11. The first moment over *all* flanks — the sharpest form so far

§6 showed no designated-flank rule works, so the existential over flanks is essential. That makes the
natural object the **sum over flanks**, not any single one:

    T(ds) = Σ_{b ∈ ds} N(b)        door 4 holds  ⟺  T(ds) ≥ 1

with exact main term `M(ds) = Σ_b b · Π_{a≠b} |I_a(b)|/b`, so the sufficient condition is

    error := M(ds) − T(ds)  ≤  M(ds) − 1,     i.e.   error/M < 1 − 1/M.

**Summing is far more robust than any single flank.** Worst ratio `T/M`: **0.598** summed against
**0.324** at `b = max ds`; 1st percentile 0.784 against 0.550.

**And the error shrinks as the speeds grow while the requirement relaxes:**

| range | worst error/`M` | required | cushion |
|---|---|---|---|
| `[1,30)` | 0.560 | 0.866 | 1.5× |
| `[1,70)` | 0.386 | 0.921 | 2.4× |
| `[1,150)` | 0.228 | 0.965 | 4.2× |
| `[1,1000)` | **0.088** | 0.995 | 11× |

So the hard cases look like the small ones. **§12 corrects this**: bucketing by sampling range is not
bucketing by `Σ ds`, and the true behaviour is not monotone.

### 11a. The binding cases, exhaustively  `[VERIFIED — all 19,440 primitive 7-subsets of [1,17]]`

| | |
|---|---|
| minimum `T(ds)` | **2** — never 1, never 0 |
| main-term floor | `M ≥ 5.2402`, at `(1,2,3,4,5,6,8)` |
| smallest cushion `(M−1)/error` | **1.127×**, at `(1,5,6,7,8,11,13)` — `T = 2`, `M = 9.855`. **Superseded by §12a: 1.084× on a wider exhaustive range.** |
| worst `error/M` | **0.7971**, required `< 0.8985` |

Note that `T`-extremal sets are **not** the LRC-extremal sets: the three tight configurations have
`max_b N(b) = 1` but `T = 4, 4, 5`, while the `T`-minimal sets are `(1,2,3,4,5,7,8)` and relatives,
all containing a difference `≡ 0 (mod 8)`.

### 11b. A fifth sampler failure, and it mattered here

Random sampling over `[1,30)` reported a worst `error/M` of **0.560**. Exhaustive search over
`[1,14]` finds **0.7971** — the sampler understated the worst case by 42% and would have suggested a
1.5× cushion where the true figure is 1.13×. Every worst-case figure in §11a is exhaustive for that
reason.

### 11c. What to prove

> For every finite `ds ⊂ ℤ_{>0}` with `|ds| = 7` and `gcd(ds) = 1`:
> `M(ds) − Σ_{b ∈ ds} N(b)  ≤  M(ds) − 1`.

Measured cushion at the binding case: **1.127×**. This is the first door-4 target that is a single
inequality with a quantified margin and a main term with a proven floor (`M ≥ 5.24`).

**Two claims in this section are corrected by §12 and should not be carried forward.** The cushion is
**1.084×**, not 1.127×, on a wider exhaustive range — and still falling with search effort. And the
error does **not** decay with `Σ ds`: it rises to a peak near `Σ ds ≈ 50` before falling, so "bound
the error by a decreasing function and check the finite remainder" is **not available**. The rest of
this section stands; that conclusion does not.

---

## 12. The error does **not** decay monotonically — §11's reading was wrong

§11 read the decay off buckets of the **sampling range** `[1,V)`. Each such bucket mixes many values
of `Σ ds`, so it does not show the dependence on `Σ ds` at all. Re-bucketed properly:

| `Σ(ds)` | 28–31 | 32–45 | **46–63** | 64–90 | 91–127 | 182–255 | 725–1023 | 1449–2042 |
|---|---|---|---|---|---|---|---|---|
| worst error/`M` | 0.623 | 0.743 | **0.797** | 0.694 | 0.530 | 0.363 | 0.203 | 0.134 |

**The worst error rises to a peak near `Σ ds ≈ 50` and only then decays**, roughly as `S^{−0.44}`. So
"bound the error by a decreasing function of `Σ ds` and check the finite remainder" is not available:
there is no decreasing bound that is valid at the small end.

The **median** error, by contrast, is essentially zero throughout (−0.019 to +0.029) — `T ≈ M` for
typical sets. The error is a worst-case phenomenon, not a typical one.

### 12a. The cushion shrinks with search effort  `[unresolved]`

| search | minimum cushion `(M−1)/error` |
|---|---|
| exhaustive, all primitive 7-subsets of `[1,17]` | 1.127× |
| **exhaustive, all primitive 7-subsets with `Σ ds ≤ 80` (213,713 sets)** | **1.0838×** at `(1,3,4,5,7,18,40)` |
| hill-climbing, 400 restarts × 300 steps | 1.140× |
| targeted shape, 5 clustered + 2 spread, 120,000 sets | 1.243× |
| targeted shape, 4 clustered + 3 spread, 120,000 sets | 1.524× |

**The cushion has fallen 1.127 → 1.084 as the exhaustive range widened, and I have no argument that
it stays above 1.** If it ever drops below 1, the first-moment bound fails for that set — door 4 would
still hold there (`T ≥ 2` throughout), but this *argument* would not prove it.

### 12b. Three searches, and only exhaustive works  `[sixth sampler lesson]`

Hill-climbing (1.140×) and both targeted shapes (1.243×, 1.524×) **failed to beat the exhaustive
minimum** of 1.084×. The worst cases are not reachable by local search from random starts, and the
shape I inferred from the worst exhaustive example did not generalise. Exhaustive enumeration over
bounded `Σ ds` is the only method here that has found anything, and it is limited to `Σ ds ≤ 80`.

### 12c. What is and is not established

**Established.** `T ≥ 2` on every set checked — roughly 450,000 across all methods, with none at
`T ≤ 1` and none where the first-moment bound fails. The main term is exact and its floor is
`M ≥ 5.24`.

**Not established, and I could not prove it.** That the error is bounded by any decreasing function
of `Σ ds` — it is not monotone — and that the cushion stays above 1. The first-moment route remains
the sharpest formulation of door 4, but it is not yet a proof strategy with a proven margin; it is a
sufficient condition that holds everywhere it has been checked and is tightening as the search widens.

---

## 13. Method correction: §§5, 8, 11, 12 are density, not BSM

**The owner's ruling, and it is right.** §§5, 8, 11 and 12 work with a main term, an error term, a
Fourier decomposition and a first moment. Those are **imported density objects**. The framework is
BSM: its objects are readings, laps, flanks, openings, bands, and **rules with their conditions shown
exhaustive** (`FRAMEWORK_CONJECTURE_v1` §3). Estimating a density and bounding its error is not an
exhibition of a rule, and the standing ruling is that *tools are fine, targets and statements must
stay native*.

So the decay I was chasing in §12 is a property of an imported statistic, and its failure to be
monotone is a fact about that statistic — not about the cascade. Chasing it further would be
refining an import.

### 13a. Which door-4 results are native, and stand

| result | status |
|---|---|
| `clear_at_int_flank_iff_emod` — the band criterion as an integer congruence | **native**, `[PROVED]` |
| `clear_at_int_flank_iff_emod_b` — modulus `n·b → b`; six progressions in bands | **native**, `[PROVED]` |
| the flank sits on its own band's edge, so six conditions not seven | **native**, `[VERIFIED]` |
| `inWay_at_first_opening_of_lt`, `eq_min_of_lonely_first_opening` — `k = 0` collapses to the nearest flank | **native**, `[PROVED]` |
| the two locators are the residues `±1 (mod 8)` | **native**, `[VERIFIED]` |
| **no designated-flank rule works** (§6) | **native** — and it is a statement *about rules* |
| main term, error, cushion, first moment (§§5, 8, 11, 12) | **imported** — density |

### 13b. What the native attack on door 4 actually is

Not: estimate how many openings are lonely and bound the error.

But: **exhibit a rule naming a lonely `(e, k)`, with its conditions shown exhaustive.** That is what
§6.7 does for the cascade, and it is the standard `FRAMEWORK_CONJECTURE_v1` §3 sets.

§6 is therefore the most native result here, and it is a genuine constraint on any such rule: the rule
cannot be *"take flank `R(ds)`"* for any of the four natural choices of `R`, so it must carry
conditions. Material already in hand for those conditions:

- **`k = 0` at the nearest flank** — a rule with a condition, covering 0.552 (§3), and now with the
  companion theorem that no other flank can serve at `k = 0`.
- **`b = 1, k = 0`, condition "no difference `≡ 0 (mod 8)`"** — settles all three tight
  configurations, where the locators sit at `±1 (mod 8)` (§9a).

The next native step is to continue that table — name the next rule and its condition — rather than
to sharpen an error term. §12's measurements are left in place as a record of what the density route
showed, and are not to be built on.
