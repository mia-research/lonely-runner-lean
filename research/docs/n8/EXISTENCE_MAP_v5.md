# Where Existence at order 8 is proved, and where it is not — v5

Supersedes `EXISTENCE_MAP_v4.md`, which superseded v3. Built from the commit record and the
Lean tree, not recollection. Every v3 and v4 item is carried **with its reason and its scope**;
additions and corrections are marked. (A first draft of v4 dropped nine closure reasons, a scope
range and a named theorem; `compile-diff` caught it. The same gate was run on this file.)

**The headline change in v5 is a reduction of the open set, not an addition to the proved set.**
An audit of my own theorem statements found two hypotheses that the category never required. The
larger one excluded every mixed-scale divisor-closed profile by fiat.

## 0. The doors (from `LRC/Spec/Doors.lean`)

`doors_agree` proves `DoorArrives ↔ DoorCapped ↔ DoorFlank ↔ DoorFAM ↔ LonelyForSubject v k`, per
arrangement and per subject, under `hv : Function.Injective v`. The bridge to the target is four
separate theorems, `lonelyRunnerAt8_of_doorFlank` / `_doorArrives` / `_doorCapped` / `_doorFAM`, so
closing any one **for every arrangement and every subject** closes the conjecture. No `sorry` in `Spec/` or `Cascade/`; Existence is a `Prop`, not a hole.
The 26 `sorry`s in `LRC/` sit in `Theorem101_DI`, `Theorem121_Main`, `Theorem52_Weyl` and the
`SmallN` alternates — the general-`n` programme, not order 8.

## 1. Proved analytically

| class | mechanism | scope |
|---|---|---|
| ratio bound `S ≤ 7` | clears at `R = 1` (`u = 1/8`) | all orders, `S ≤ n−1` |
| **Branch A** — integer readings, `8 ∤ sⱼ` | `Guard.odd_clear_of_not_dvd`; all four spine points clear at once | **arbitrary magnitudes** |
| flanks with ≤ 1 fractional ratio | nearest-integer walk, `TwoWalker` | — |
| flanks with off-lattice ratio pairs | lattice-crossing, `TwoWalker` | — |
| divisor-closed, every middle quotient `≤ 7` | `small_b_blocks_iff` + `q` coprime to 210, `g(210) = 10` | **narrow**: 240 profiles under `m = 6000` |
| `\|S\| ≥ 2` (never a singleton) | `SolutionPair`, via a reflection centre | 6,758 of 19,880 (34.0%) |

**Added this arc:**

| class | mechanism | scope |
|---|---|---|
| a flank has exactly `e` openings | `Openings.lcm_div_eq`; `L = lcm_j(e/gcd(d_j,e)) = e` when the multiset has `gcd 1` | all flanks; `[propext, Quot.sound]` only |
| the last class belongs to `1/n` | `LastClass.last_class_forces`: `k ≡ -1 (mod q)` blocked with `q ≤ n` ⟹ `p = 1, q = n` | all orders |
| `q ≤ n-1` throughout ⟹ clear | `LastClass.lcm_minus_one_clear` at `k = L-1` | any mover count, any order |
| shadowing forces `q ≥ n` | `LastClass.shadow_needs_full_denom` | **hypothesis: every mover `0 < p < q`**; sharp, minimum attained is exactly 8 |
| the `-7` opening is index-free | `MinusSeven.inWay_minus_seven`: `inWay d (8L-7) e ↔ dist(7d, 8eℤ) < e` | requires `e ∣ L·d` |
| `max\|d\| ≤ 7·min\|d\|` ⟹ lonely | `MinusSeven.flank_clear_of_no_tiny`, witness `(8L-7)/(8e)` | fires on ~29% of uniformly sampled subjects |
| first-lap clearance | `FirstLap.flank_clear_of_window`: `e ≤ d·A ≤ 7e` for all others ⟹ clear at `A` | fires on ~43% of uniformly sampled subjects |
| the window witness is under the cap | `FirstLap.opening_lt_first_lap`: `A/(8e) < 1/d` for every `d` in the window | links to `DoorFirstLap` |
| the covering count | `CoverCount.cover_count_gcd`: mover `d` covers exactly `c·gcd(d,e)` of the `e` openings | was v4 §2 *verified on 9,323,468 movers*; now **proved** |
| shadowing needs the count | `CoverCount.shadow_needs_count` is the union bound `e ≤ Σ_j (B j).card`; the `gcd` form `Σ_j c_j·gcd(d_j,e) ≥ e` is that **composed with** `cover_count_gcd` | **necessary, not sufficient** — at `e=16` it reads `24 ≥ 16` and the flank is clear |
| divisor-closed, every quotient `≥ 10` | `DivisorOrder6.clear_of_order6`: order-6 real witness rounded to the nearest integer | **per modulus**; supersedes the `b ≥ 28` threshold |
| divisor-closed, every quotient `≤ 9` | `SmallModuli.clear_one`: `q = 1`, since `L(b) = 1` there | and `clear_one_fails` shows `9` is exactly its reach |
| one candidate reaches a ratio-7 window | `SmallModuli.reach_window`: for `0 < q < b`, clear ⟺ `(8q+1)/7 ≤ b ≤ 8q+1` | the `n-1` constant as the reach of a single candidate |
| the anatomy of `q = L(m)` | `CanonicalCandidate`: `L(m) = u·b + ⌈(v·b-1)/8⌉`, `v = (m/b) mod 8` | collider ⟹ residue `0`; `1 ≤ v ≤ 4` always clear; collider step is exactly `L(b)` |
| a collider kills the `m`-lattice | `CanonicalCandidate.collider_kills_lattice` | every multiple of `m/8` is blocked at a collider |
| every obstacle sits at zero | `WindowGeometry.blocked_iff_near_zero` | the blocked set is one **cyclic interval centred on 0**, radius ≈ `b/8` |
| a window covers its divisors | `WindowGeometry.window_ge_half`, `window_covers_divisor`: `2w(b) ≥ b`, so `b' ∣ b` proper gives `b' ≤ w(b)` | licenses nested construction down a divisor tower |
| **mixed profiles, no homogeneity** | `Derestricted.profile_clear_mixed`: band at moduli `≥ 10`, window directly below `10` | **removes a hypothesis that was mine**; `Derestricted.window_of_band` isolates where `10 ≤ b` is needed |
| the `-7` opening, no size hypothesis | `Derestricted.flank_clear_minus_seven` | **removes a hypothesis that was mine** |
| small moduli are pure non-divisibility | `ReducedOpen.small_clear_iff`: `2 ≤ b ≤ 7` ⟹ clear ⟺ `b ∤ q`; `b ∈ {8,9}` ⟹ also `b ∤ (q+1)` | extends `small_b_blocks_iff` past its `b = 8` break |
| the reduced obligation is sufficient | `ReducedOpen.clear_of_reducedWitness` | a `q` meeting it clears every modulus |

## 2. Verified exhaustively, not proved

| class | evidence |
|---|---|
| divisor-closed, general | 185,729 exhaustive (`m < 500`), 0 failures; settled by an explicit rule |
| Branch B, general | 244,790 exhaustive (**readings `[2,30]`**), every profile has a witness |
| all integer arrangements `v₈ ≤ 40` | 148.5M runner instances, `R ≤ 44856/3749` |
| `\|S\| ≥ 2` on the remaining 66% | surviving `m−q` orbit in 19,880 of 19,880 |
| witness normalisation **on LRC bad sets** | orders 4–9, 12 arms, 0 mismatches |

**Added this arc:**

| class | evidence |
|---|---|
| **`DoorThreeLargest`** — first clear flank within the 3 largest | **exhaustive** over 52,813,573 multisets from `[1,40]`, `gcd 1`: rank 1 in 52,808,303, rank 2 in 5,229, rank 3 in 41, **rank 4 never**, **no multiset with zero clear flanks**. Witness `experiments/n8/three_largest_v2_N40.out`. The tree's tag reads `[EMPIRICAL — 35,872 sets]` (sampled, not exhaustive) and **has not been edited**; this row describes new evidence, not a change made to `Doors.lean`. Scope: positive-difference multisets, `gcd 1`, `max ≤ 40` |
| maximum shadowed flanks is 6 of 7 | exhaustive over 645,482 multisets from `[1,20]`, `gcd 1`; attained by exactly one, `(2,3,4,5,6,7,16)` |
| ~~mover `d` covers exactly `c·gcd(d,e)` openings~~ | **promoted to §1** — `CoverCount.cover_count_gcd`. The 9,323,468-mover check stands as the pre-proof verification |
| greedy nesting settles divisor **towers** | 200,000/200,000 random towers and 50,894/50,894 exhaustive divisor towers, no failures (`experiments/n8/tower_greedy_v2.py`). **Not proved** — see §5 |
| the mixed condition of `Derestricted.profile_clear_mixed` is satisfiable | 8,000 sampled divisor-closed profiles (`experiments/n8/mixed_reach_v1.py`): a qualifying `q` exists in **100.00%**, and clears wherever it fires (8,000/8,000). Existence of such a `q` is **not proved** |
| `L(m)` clears `b` iff `v ≠ 0` and `⌈(v·b-1)/8⌉ ≤ ⌊(7b-1)/8⌋` | 13,499 `(m,b)` pairs, `m < 2000`, no exceptions (`experiments/n8/Lm_mechanism_v1.py`). Rates by `v = (m/b) mod 8`: `0` → 0.00%, `1..4` → 100%, `5` → 91.63%, `6` → 85.11%, `7` → 10.56% |
| shadowing is a small-`L` phenomenon | `P(shadowed ∣ L)`: 49% at `L=1`, 12.5% at `L=8`, 0.05% at `L≥64`, 0.00% at `L≥512`; median `L` 3 shadowed vs 73 clear. Sampled, not exhaustive |

## 3. Open — no proof

- **Branch B**, integer readings containing a collider `8 ∣ sⱼ`, in general.
- **Rational readings** — shown equal to *integer speed sets with no unit speed*
  (200,000 sets, 0 mismatches). Costs exactly one theorem, **`unit_never_blocks`**, worth
  **5.76%** of candidates.
- **Real / irrational speeds.**
- **`R < 16`** (`DoorCapped`) — untouched in this arc.

Named more precisely this arc:

- **`DoorThreeLargest`** — exhaustive to `[1,40]`, not proved.
- **The wrapping regime.** First-lap clearance settles the no-wrap case outright; what is owed is
  where `d·A` exceeds `8e` and the residue genuinely reduces — about 57% of subjects.
- ~~**Middle band `8 ≤ b ≤ 27`**~~ — **reduced**. The threshold fell to `b ≥ 10`
  (`DivisorOrder6`), the small end closed outright at `b ≤ 9` (`SmallModuli.clear_one`), and the
  audit showed the remaining `{8,9}` gap was an artefact of a hypothesis of mine: for `2 ≤ b ≤ 9`
  clearing is pure non-divisibility (`ReducedOpen.small_clear_iff`). The band is **closed
  per modulus** — whether a single `q` meets all moduli at once is the next bullet, still open.
- **Mixed quotient profiles** — **reduced, not closed.** With the homogeneity removed, the
  obligation is now `ReducedOpen.ReducedWitness`: find `q` clearing every modulus `≥ 10`, subject
  only to `b ∤ q` at each modulus `b ≤ 7` and `b ∤ q`, `b ∤ (q+1)` at each `b ∈ {8,9}`. The small
  moduli forbid **at most two residues each, explicitly named**, instead of being an unanalysed
  obstruction. The whole difficulty now sits at the moduli `≥ 10`.
- **Divisor towers** — greedy nesting works on 250,894 towers with no failure; the induction is
  not closed (§5).
- **Three or more non-integer ratios on a common lattice.** Decidable in `ℤ`; not proved.

## 4. The toolkit, all proved and axiom-clean

Not existence results; they say where to look and in what category.

*Reduction to `ℤ`* — `GapRule` (3), `ReachRule` (13), `ArithForm` (2): the covering question is a
finite conjunction of integer inequalities, proved equivalent to the real statement.

*Structure of blocking* — `gcd_covariant`, `rescaled_blocks_iff`, `divisor_reduces`,
`small_b_blocks_iff`, `BlockerCount` (3): blocking depends only on coprime parts; the collision
criterion is rescaling-covariant; the `n−1` constant governs small moduli.

*Symmetry* — `TimeReversal` (2), `Involution` (3), `TwoPatterns` (3), `Degenerate2` (3),
`SolutionPair` (3): one symmetry at four levels; the centre is `c ≡ 0` for good moduli and `c ≡ −1`
for obstructed ones; `b = 2` is the unique degenerate modulus.

*Witnesses* — `witness_normalised` (extremal), `EdgeWitness` (4, interior): if a witness exists, one
exists with a constraint exactly tight, and two, one per end.

**All axiom-clean**, witness at `experiments/n8/v12_new_axioms_v1.out`, which carries **79 unique
declarations, all axiom-clean: 73 reporting axioms and 6 depending on none at all, 0 `sorryAx`** — including `GeneralOrder` (3), `SplitLaw` (4),
`GeneralReflect` (7), `FlankBridge` (6), `SmallQFlank` (2). *(v3 said "54 declarations" against
this same file; the file has 79. A first correction **in v4** said "73 over 73", which counted only
the axiom-reporting lines and dropped the 6 axiom-free ones. Both are corrected, not carried.)*

*Added this arc*, each with its own witness file, all axiom-clean:
`LastClass` (8) → `experiments/n8/LastClass_v1.out`; `MinusSeven` (5) →
`experiments/n8/MinusSeven_v1.out`; `Openings` (4) → `experiments/n8/Openings_v1.out`;
`FirstLap` (7) → `experiments/n8/FirstLap_v1.out`. The `Openings` and several `FirstLap`
declarations need only `[propext, Quot.sound]`.

*Added in v5*, each with its own witness file, all axiom-clean: `CoverCount` (4) →
`experiments/n8/CoverCount_v1.out`; `DivisorOrder6` (6) → `DivisorOrder6_v1.out`;
`SmallModuli` (6) → `SmallModuli_v1.out` (all six need only `[propext, Quot.sound]`);
`CanonicalCandidate` (6) → `CanonicalCandidate_v1.out`; `WindowGeometry` (5) →
`WindowGeometry_v1.out`; `Derestricted` (3) → `Derestricted_v1.out`; `ReducedOpen` (3) →
`ReducedOpen_v1.out`. **33 declarations added in v5.**

## 5. Routes closed with reasons — do not re-attempt

v3 listed **eleven** rows (an earlier draft of **v4** said twelve; that was a miscount). All
eleven are carried **with their reasons**:

| route | why it fails |
|---|---|
| counting / density | joint density sits **below** the product of conditionals; correlation is adverse |
| extremal witnesses | supply **exhausted at 38.83%**, gated by `8 ∣ m` or `8 ∣ b` |
| bounded centre offset | offset grows with `m` (7,962 at `m = 99,078`) |
| product of conditionals | inequality false, 2,594 of 3,000 |
| Hunter–Kounias | an import, and has a counterexample |
| `s = s*` / largest reading | 18,809 and 794 counterexamples |
| primorial `2310` | "nonzero residue ⟹ clear" is what breaks at `b = 8` |
| doubly-tight witness | 1.615% have none |
| one witness on both patterns | 2.99% have none |
| iterating the walk | `tight_of_step` needs **unit** steps; steps of `b` leap constraints |
| symmetric shrink margin | 67.49% die at depth 0 |

**Added this arc:**

| route | why it fails |
|---|---|
| largest flank always clear | **refuted** — `[-4,0,1,3,4,5,7,8]`, subject 0, `e = 8` live and shadowed. Independently, `Doors.lean` already records `DoorLargestFlank` `[REFUTED]` by `(2,3,5,7,8,13,16)` |
| pinning via largest-flank rigidity | the "32 cores, no minimal size-6" result was an artefact of capping the pool at `q ≤ 8`. Uncapped: 87,338 shadowing configurations at every flank `e ≥ 8`, denominators 2–24, **85,532 contain no core** |
| a bounded family of multipliers | the least `\|c\|` clearing a flank grows with the arrangement: 41, 57, 129, 409 over ranges ±12, ±30, ±100, ±400 |
| rearranging the flank vocabulary | it is an **exact reformulation**, not a reduction: with `σ_j = d_j/(8e)`, "flank `e` clear at `c`" **is** "lonely at `t = c/(8e)`" — 60,000 cases, 0 mismatches |
| density / coverage as an explanatory quantity | not a framework object, and inert: union coverage measured **flat at 0.81 across ranks 0–5** (.809 to .797) and .724 at rank 6, while the clear-rate moved 99.45% → 86.15%. The native quantity `L` carried the whole effect |
| a global reflection centre for `\|S\| ≥ 2` | the window is preserved by `r ↦ c-r` exactly when `c = L+U`, which is `b` for `b%8 ∈ [2,7]` and `b-1` for `b%8 ∈ {0,1}`. A global centre needs `C ≡ 0` at good moduli and `C ≡ -1` at obstructed ones — CRT-solvable iff every good modulus is coprime to every obstructed one. Divisor-closed moduli share factors by construction, so it exists in **22.8%** of 4,000 sampled profiles against **22.5%** for the all-good case already proved (`experiments/n8/global_centre_v1.py`). Exhausted; needs a different mechanism, not a better centre |
| length-only invariants for the tower induction | **both refuted** (`experiments/n8/tower_step_v1.py`, `tower_step_v2.py`): `\|I\| ≥ w(b)-1` fails at `b = 18, b' = 9`; `\|I\| ≥ ⌈b/2⌉` fails at `b = 6, b' = 3`. Greedy's surviving interval has a specific **position** inside `[L(b), U(b)]`, and a length-only invariant discards it. A positional invariant is owed |
| `m`-lattice candidates on Branch B | one collider kills them all at once (`collider_kills_lattice`): `L(m)`, `⌈m/4⌉`, `⌈3m/8⌉` each clear **0.00%** of 20,000 sampled Branch B profiles (`experiments/n8/branchB_rule_v1.py`). The witness must be placed at the collider's scale |

## 6. What the reductions bought

Recorded plainly, because each narrows what a proof must do:

- the question is posed over `ℤ`, not `ℝ` — **proved** equivalent;
- the witness is normalisable, extremally **and** interiorly — **proved**;
- two frontiers (integer vs rational readings) are **one question** split by whether `1` survives
  reduction;
- the reflection obstruction is a **moving centre**, not a failure;
- a surviving orbit is exactly *the system with obstructed intervals shrunk by one residue* — a
  strictly tighter system, so the remaining gap is quantified rather than vague.

*Added this arc:*

- a flank's opening count is **exactly `e`** — proved, so "the survivor is `d_max`" and "the
  survivor has the largest `L`" are the same statement, not rival explanations;
- shadowing is governed by that opening count, not by any density;
- dead flanks and live shadowed flanks are **different exceptions** and must not be pooled;
- the small moduli of a divisor-closed profile carry **no difficulty**: clearing there is pure
  non-divisibility, so the open set is now located entirely at the moduli `≥ 10`;
- a **per-object** theorem must not be wrapped in a **whole-profile** hypothesis it never
  needed — the check is cheap and it recovered **86.55 percentage points of divisor-closed
  profiles** (13.45% → 100.00% of 8,000 sampled) that were never actually blocked.

## 7. Corrections on the record

- The rank table's 100% at rank 0 is 100% **of a sample**; the explicit counterexample above
  shadows the largest flank. "Minimum 3 clear flanks" is likewise a sampled floor, now exhaustive
  to `[1,40]`.
- Two structural reads of the rank-3 sets were floated and **both fail**: they do not all carry a
  scaled Klein core `{g,3g,4g,5g,7g}` (several families occur), and "contains 7" is 32 of 41 at
  `[1,40]`, not universal (witness `experiments/n8/rank3_core_v1_N40.out`).
- `shadow_needs_full_denom` is **not** contradicted by shadowed flanks with `max q = 1`; those are
  dead flanks and `q = 1` movers, outside its hypotheses.
- **"Twenty values to two" was misleading.** The `b ≥ 28 → b ≥ 10` improvement is real and
  twelvefold *in profiles* (0.60% → 7.33%), but it is not a near-closure: most divisor-closed
  profiles are mixed, and both threshold routes needed a homogeneity hypothesis. Values of `b`
  are not the unit that matters; profiles are.
- **Two hypotheses were mine, not the category's** — the homogeneity in
  `profile_clear_of_order6` (cost: 86.55% of profiles) and the largest-flank condition in
  `flank_clear_of_no_tiny`. Both removed. Genuinely required, and kept:
  `shadow_needs_full_denom`'s `0 < p < q`, and `profile_clear_one`'s `b ≤ 9`.
- **The first tower greedy was wrong.** It demanded a full window run of length `w(b)`, needing
  `\|I\| ≈ 7b/4` where the construction supplies `≈ 3b/4`, and failed 82,599 of 200,000 towers.
  The longest surviving piece works; the exhaustive check caught the error.
- **The step-interval form's 44.82% is not a regression** against `T = L(b*)`'s 59.84% — both
  are percentages of **25,000 sampled Branch B divisor-closed profiles** (`step_interval_v1.py`,
  `branchB_rule_v1.py`). The interval form excludes, by construction, the profiles that clear
  *by* wrapping a modulus.
- **A first correction to the declaration count was itself wrong.** v3 said "54 declarations"
  against a file holding 79; the first fix, in **v4**, said "73 over 73", counting only the axiom-reporting
  lines and dropping the 6 that depend on no axioms at all.

## 8. What is not claimed

Existence at order 8 is **open**. Nothing in this arc closes a door. None of the above is
existence.

Across v4 and v5 the arc bought **11 Lean modules** (`Openings`, `LastClass`, `MinusSeven`,
`FirstLap`, `CoverCount`, `DivisorOrder6`, `SmallModuli`, `CanonicalCandidate`,
`WindowGeometry`, `Derestricted`, `ReducedOpen`) carrying **57 proved declarations**; **21 rows**
of §1 (8 added in v4, 13 in v5); **7 added rows** in §2 of which **3 are exhaustive**; **8 added rows** in §5; and **9
corrections** in §7.

The change that matters most in v5 is not on that list. Removing two hypotheses that were mine
rather than the category's **reduced the open set**: the middle band is closed, and the mixed
divisor-closed class is now the single explicit obligation `ReducedOpen.ReducedWitness`, with the
small moduli discharged as pure non-divisibility and the difficulty located entirely at the
moduli `≥ 10`.
