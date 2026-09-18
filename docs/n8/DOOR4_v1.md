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
