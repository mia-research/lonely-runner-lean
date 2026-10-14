# v7 revision list — running, for later review

Started 2026-09-14. **Append only. The manuscript is frozen; nothing here is applied.**
Each item says what to change, where, and why, with the evidence that settles it.

---

## 1. §7.1 — the procedure carries a window the framework does not require  `[SETTLED]`

**Change:** drop the window condition `d ≤ a·m ≤ 7d` and the restriction of `d` to the
runner's own differences. The candidates are `t = a/(8D)`, `a ≡ 1 (mod 8)`, `D` a free
positive integer — the resolution at which the seed is framed.

**Why:** verified counterexample, `WHY_THE_LAST_MILE_RESISTS_v1.md` §1. Speeds
`(1, 31, 75, 97, 128, 160, 176, 225)`, the runner at speed 1: nothing clears in its first
window, and it is lonely at `t = 9/40 = 9/(8·5)` — resolution `D = 5`, lap 6.

**Owner:** *"I never thought the first window/cycle was a requirement and think it keeps
getting introduced from context loss and revert to training data."* Provenance confirmed:
§1.3 introduces it and flags it as a choice; §7.1 bakes it in; §7.4 makes it the claim.

## 2. §7.4 — the Claim is false as written  `[SETTLED]`

**Change:** restate over the relaxed form — a runner is cleared at **some** resolution, with
no bound on the lap. The instant stays exactly named.

**Why:** same counterexample. `[PROVED — exact, exhibited]`

## 3. §1.3 — its justification for the window does not survive checking  `[SETTLED]`

§1.3 keeps the first-window form because the relaxed form *"would leave the lap `k`
unsupplied"*. In the `(a, D)` form it is not unsupplied: `t = a/(8D)` names the instant
outright and the lap is `⌊d_min·t⌋`. Checked: `d_min = 30`, `t = 9/40` → lap 6;
`d_min = 1974`, `t = 3/64` → lap 92. **The closed expression survives the relaxation.** Only
a bound on the lap is lost, and the framework never claimed one.

## 4. §7.2 — Proposition 7.1 is scoped to the window  `[OPEN — needs restating]`

The proposition (*the candidates are exactly the openings*) is **true and machine-checked**
as `exists_clear_candidate`, but it is stated about one window. Under item 1 it should be
restated per resolution: within any lap, the clear set is closed, so its components have
least elements, and those are openings. The Lean core is resolution-agnostic already and
should carry over unchanged.

## 5. §7.3 — soundness, phrasing  `[OPEN]`

Still correct: a returned instant is correct. Should be phrased on `(a, D)` rather than on a
window. Matches the deferred Lean item below.

## 6. Lean — `procedure_sound` naming  `[OPEN, deferred at owner's direction]`

True as stated, but phrased on the window and named for "the procedure". Restate on `(a, D)`
and rename. Not a reproof.

## 7. §8 — no row for the cascade family  `[OPEN]`

The cascade's clearing test **is** `coord_iff`, so it is machine-checked, but §8's table does
not say so.

## 8. §9 — the `2σ` containment threshold  `[OPEN]`

`two_sigma_zone_inside` needs `3 < n`; at `n = 3` the two ends coincide. §9 lists the other
thresholds (`n > 4` for the exclusion, `n > 2` for the clear interval) and should list this.

## 9. Restorations still outstanding from `LOST_FUNCTIONS_v1`  `[OPEN]`

Not yet in any manuscript version: **H1** (same-side runners within `1/4` of a lap line), the
**wrap gap / global start / gap migration**, the **relay anatomy** (231,294 blocked instances,
0 chains reaching the window's end), and **Part II's perturbation mechanisms**. §6.2 still
refutes the relay without stating the rule the relay runs on.

## 10. §1.1 — the per-runner reading is never distinguished from the stationary frame  `[SETTLED]`

`PROOF_CANDIDATE_v3` Step 3 carries a clause v7 does not:

> *On frames.* Reading `v_j − v_i` is what "`i` is lonely" **means**; it is not a WLOG
> privileging `i`. Steps 3–5 are performed identically and independently for each of the eight.

v7 §1.1 keeps *"performed identically and separately for each of the eight, and no runner is
held stationary"* but drops the clause that says **why** the per-runner subtraction is not the
banned stationary frame. Without it, §7A's own firewall row — "No stationary frame" — reads as
a ban on the framework's engine. One clause fixes it, and it already exists in v3.

**Found by:** the owner's review of `PROOF_REQUIREMENTS_v1`, item 2, which hit the same gap in
that document. Corrected there in v2.

## 11. §1.1 and §2.2 state exactness unconditionally; it holds only for commensurable arrangements  `[SETTLED]`

§1.1: *"Every quantity is exact. Positions, lap counts and phases are **rationals** computed
from the speeds."* §2.2: *"Both conditions are on `ℕ`. There is **no real division, no floor,
and no fractional part** in the statement."*

For the runner at speed `1 + √2/100` in §7d's own example: `d_min = √2/100` is irrational, the
produced time `3/(8·d_min) = 26.5165…` is irrational, the readings `1, 140.42…, 211.13…` are
irrational. **Proposition 2.1's test does not apply** — there is no `mod 8D` for an irrational
difference, and the test there is the band condition on the reals.

The runner is lonely at that time and the construction delivers; what fails is the *stated
method*. §7d already separates the three regimes and treats the irrational one differently, so
the unconditional wording contradicts §7d.

**Fix:** qualify both sections — the arithmetic is exact and integral for commensurable
arrangements; for incommensurable ones the test is the band condition on the reals.

## 12. §7.1 / §7.4 — the cascade, in the owner's words; items 1 and 3 cite the wrong time  `[SETTLED]`

Added 2026-09-14 (review session). **Owner:**

> *"So the basis of this is that any speed is determined/can be found with reference AP and or
> Grid with Dmin and Dmax. So at AP gap or 1, the speed set of 1,2,3.2335,4,5,6,7,8, each
> runners isolation can be found and Dmin gives a proportionate out come one resolution. So the
> more decimal points the more cycles till the isolation time. The issue is sometime speed
> arrangemts don't quite work to AP times of just 1. So that is were the cascade happens to give
> you the appropriate ap scale to use."*

And on item 1's proposal: *"I don't know what free integer is I suspect it was an attempt to use
it to prove a lemma."* **"`D` a free positive integer" is therefore not the framework's object**,
and the several operational forms in the scripts (`D = k·d_min`, lap-by-lap readings, integer
`(D, a)`) are applications simplified for particular tests, not the cascade's definition.

**The arrangement of item 1 is not a counterexample to the framework.** v7 stops the cascade at
lap 0 (`p ≤ 7`). Read past lap 0, the `d_min` lattice itself isolates both hard runners on file —
spine instants `u = k + r/8`: `[VERIFIED — exact, lonely at every distance]`

| arrangement | `d_min` | from the `d_min` lattice | lap | cited in items 1, 3 / v7 |
|---|---|---|---|---|
| `(1, 31, 75, 97, 128, 160, 176, 225)`, runner at 1 | 30 | `t = 43/240`, `u = 5 + 3/8` | 5 | `9/40` at `D = 5` |
| `(1, 1975, 5265, 6910, 8737, 9589, 11845, 15135)`, runner at 1 | 1974 | `t = 17/15792`, `u = 2 + 1/8` | 2 | `3/64` at `D = 8` |

`9/40` and `3/64` are lonely times, but neither is on the runner's `d_min` lattice, so neither is
the cascade's output. `WHY_THE_LAST_MILE_RESISTS_v1`'s headline ("§7.4 is false … why every
route died") carries the framing this item corrects.

## 13. §1.1, §2.2, §7, §8 — commensurate and incommensurate times  `[SETTLED — Lean, outside both trees]`

**Owner:** the computations have been a *representation* of the method (e.g. `r3 = π` to seven
digits gives a rational time with a proportionate cycle), **but the method works for irrational
speeds and returns an irrational isolation time.** The documentation does not say so; item 11
records the symptom.

**How the Lean development handles it.** Checked 2026-09-14.

| over `ℝ` — irrational speeds admitted as they stand | integer / commensurate only |
|---|---|
| `lonely_iff_flanks` (4.1), `gaps_all_eq` (4.2), `grid_of_pairwise` (4.3), `nearest_below/above`, `before_floor`, `window_iff`, `reading_clear_iff`, `lap_and_phase`, `ratio_condition` (4.8), `wide_gap_*` (4.9), `no_solo_closure`; in `ConstructionN`: `procedure_sound` (`t = u/dmin`, `dmin : ℝ`), `returns_at_spine`, `band_identity`, `exists_clear_candidate` | `coord_iff` (Prop 2.1, `ℕ`), the reference and survival statements 4.5–4.7 (whole-eighth displacements), `commensurable` (global isolation forces commensurable speeds), the 2(b) derivation in `Instants.lean` |

So the framework's per-runner machinery is already real-valued; only the integer **test** and the
**reference** are commensurate objects, and the reference is commensurate necessarily
(`commensurable`). `procedure_sound` carries `u < 1`, the first-window restriction — see item 6.

**Machine-checked instance.** `experiments/n8/IrrationalDemo_v1.lean` (SHA-256 `f9913c85…`),
compiled against the frozen `Construction8`, using `ratio_condition` unchanged. Every declaration
depends on `[propext, Classical.choice, Quot.sound]`.

| speeds | runners at `π`/`3.141593` and at `4` | the other six |
|---|---|---|
| `(1, 2, π, 4, …, 8)` | `d_min = 4 − π`, lonely at `t = 1/(8(4 − π))` — **irrational** (`time_irrational`) | `d_min = 1`, `t = 1/8` |
| `(1, 2, 3.141593, 4, …, 8)` | lonely at `t = 125000/858407` — rational (`time_rational`) | `t = 1/8` |

`all_lonely` uses only `3 < π < 3.15`: no rational approximation of `π` enters. The two times
differ by `5.9 × 10⁻⁸`, and in this arrangement both fall in the slowest runner's first cycle —
Theorem 4.8 settles both runners, so the digit count moves the time proportionately without
adding cycles. Runners that need the cascade have not been tested on this point.

**Change when unfreezing:** state the method over real speeds; present `coord_iff` as the exact
integer representation for commensurate arrangements; keep the reference (4.5–4.7) as the
commensurate object it provably is.

## 14. v7 defects raised in review, not yet reviewed by the owner  `[OPEN]`

Each checked in exact arithmetic, 2026-09-14.

- **§7.2** — "the moment, whenever the procedure returns, is always an opening" predates the
  second family. v7's own first witness returns `3/64`, an opening of none of that runner's
  differences.
- **§7.4 nesting** — "every grid satisfies it" (the residue test) is false: the grid rows settle
  runners at `1/(8g)`, not `u = 1/8`. Runner 1 of `(1,3,5,7,10,12,14,16)` fails the residue test
  and all four `u = r/8`, and is lonely at `1/8`. Over grids with differences `≤ 24`: 8,740 of
  17,488 grid runners fail the residue test, 920 fail row 2. `PROOF_REQUIREMENTS_v2` §5 row 1's
  "general form" makes the same conflation.
- **§1.2** — "the decision on an open cell is settled by its two ends" is false: at speeds
  `(0,12,14,16,30,35,38,53)`, the runner at 53, the cell `(7/424, 9/424)` has both ends clear and
  is the open zone of difference 53. Decide a cell by an interior point.
- **§1.3 vs §7.1** — "confines its evaluation to that first window" vs "the second family is not
  confined to that window".
- **Abstract** — "every result asserted as proved is formally verified" vs §8 (Thm 7.2 partial,
  Prop 7.1 outside the digest) and §10 (§6 not formalised).
- **§11 / abstract** — the gate "fails if the open claim of §7.4 is stated in Lean at all"; check
  [4] greps declaration names only.
- **§7.1 ceiling prose** — "for `D ≤ 7m` the residue is `mp`" should read `8D > mp`
  (`210 mod 80 = 50`). Conclusion unaffected.
- **§5 understates** — 2(b) is derived axiom-clean in `ConstructionN/Instants.lean`, and the AP's
  four points follow from Theorem 4.3 alone (the eight points `jt` are pairwise `≥ 1/8`).
- **Minor** — "parts 1–7" never defined in v7; §6.1 "the subject" should be the end runner; §9
  places the ratio bounds in §3 (they are §6.2) and leaves "descent" undefined; `Reference.lean`'s
  docstring still says the 6(c) converse is not done.

## 15. §7.1 / §7d — an incommensurate arrangement needing the cascade, every runner, in Lean  `[SETTLED — Lean, outside both trees]`

Added 2026-09-14. `experiments/n8/IrrationalCascade_v1.lean` (SHA-256 `2520f2dc…`), compiled
against the frozen `Construction8`; every theorem depends on `[propext, Classical.choice,
Quot.sound]`, no `sorry`. Speeds `(1, 1+δ, 3, 4, 5, 6, 7, 8)`, `δ = √2/100` — §7d's own case.
`√2` enters only through `√2·√2 = 2` and `1.41421 < √2 < 1.41422`.

| runner | Lean | time |
|---|---|---|
| r2, speed `1+δ` | `r2_not_ratio`: `d_max > 7·d_min`, so Thm 4.8 does not reach it. `r2_blocked_at_first_spine`: at `u = 1/8` the runner at 6 is in the way. `r2_lonely`: clear at the grid tier's spine `r = 3`, `D = d_min = δ` | `t = 3/(8δ) = 75√2/4`, **irrational** (`r2_time_irrational`) |
| r1, speed 1 | `r1_lonely`: the integer pack; at difference 7 the distance is exactly `1/8`, admitted by the closed test | `t = 71/8` |
| r3 … r8 | `others_lonely`: Theorem 4.8 via `ratio_condition` unchanged | `t = 1/8` |

What Lean does here: it **checks** a time the cascade names — the tier, the spine `r` and each
runner's integer lap were supplied, then verified. r1's and r2's times (`≈ 8.9` and `≈ 26.5`
cycles of the slowest runner) sit far out because `d_min = δ` is small, the proportionate effect
of item 12's owner statement; r1's time is rational although its `d_min` is irrational.

## 16. §4.3–§4.4, §7.1 — the cascade is a deviation from an ideal; the scale comes from spread and periodicity  `[OPEN — the scale's formula is the owner's to state]`

Added 2026-09-14. **Owner:**

> *"every speed arrangement is individual deviation from an ideal, those ideals we represent as
> either AP or Grid with dmin finding any AP deviation. The ap gap is coded as 1 e.g. (1...8) it can
> alway represent the speed, that that's because AP is gap not a number the cascade is the way deal
> with it."*
>
> *"you want to know how to change the AP scale that is determined by the speed spread and
> periocity. You test that, take the flase counter example, that AP scale is 1200"*

**In Lean** — `experiments/n8/CascadeRule_v1.lean`, outside both trees, every declaration on
`[propext, Classical.choice, Quot.sound]`, real speeds, no runner pinned, every lap:

| declaration | says |
|---|---|
| `reading`, `reading_dev_bounds` | every arrangement is an ideal AP of **any** real gap plus deviations in `[0, gap)` |
| `gap_is_a_scale` | coding the gap as `1` changes no distance |
| `position_in_eighths`, `clear_iff` | at the ideal's AP instant `t = r/(8·gap)` each runner sits `index·r` eighths from the subject plus `deviation·r/gap`; clear iff that is `≥ 1` eighth from every multiple of 8 |
| `on_ideal_clear` | a runner with no deviation is clear at every `r` coprime to 8 unless its index is a multiple of 8 |
| `nearest_on_ideal_above/below` | at gap `d_min`, the nearest runner is on the ideal |
| `lonely_of_reading` | every runner landing clear ⟹ the subject is lonely at `t = r/(8·gap)` |
| `deviation_sets_the_lap`, `r1_lonely` | `(1, 1+√2/100, 3, …, 8)`, runner 1, ideal of gap 1: the one deviating runner lands `r·δ` eighths away, `69δ < 1 ≤ 71δ`, so the time is `71/8` |

The theorem 4.5–4.7 statements in `Construction8` already carry the gap as a real scale
(`displacement`); what they lacked was the per-runner reading without whole-eighth displacements.

**Scale 1200 on `(1, 31, 75, 97, 128, 160, 176, 225)`.** `[VERIFIED — exact]` On the time AP of step
`1/1200`, **every runner** has lonely instants in one period: 148, 194, 200, 154, 208, 166, 162,
196 (odd numerators alone: 74, 92, 112, 78, 102, 86, 76, 114). The runner at speed 1's first is
`29/600`. The scales 40 and 240 also carry lonely instants for every runner, and the least step
`1/N` serving all eight is `N = 23`. So 1200 works, and it is not singled out by this test alone:
**how spread and periodicity give 1200 is the piece still to be written down.**

## 17. When and why the AP scale has to change  `[PARTLY PROVED — scale 1 and scale 2 exactly; larger scales open]`

Added 2026-09-14. Integer speeds, `g` = gcd of the speed differences, the AP gap coded as `g`; at
scale `s` the AP times are `t = r/(8sg)`, `r` odd, repeating every `8s` values of `r` (one period).
Scripts: `experiments/n8/ap_scaling_survey_v1.py`, `experiments/n8/ap_scale2_rule_v1.py`.

**When — scale 1.** `[PROVED]` At scale 1 each difference `e` sits `(e/g)·r` eighths from the
subject, a whole number of eighths: in the way at **every** AP time if `8g | e`, at **none**
otherwise. So a runner needs the scale changed **exactly when it shares an AP slot** — some speed
differs from it by a multiple of `8g`. This is `on_ideal_clear`'s exception
(`experiments/n8/CascadeRule_v1.lean`). On `(1,31,75,97,128,160,176,225)` the shared slots are
`1|97|225` and `128|160|176`; those six runners need scaling and `31`, `75` do not.

**The first scale to try.** `[PROVED]` A scale `s` is dead for a runner when a slot-mate differs
from it by a multiple of `8sg`: every AP time at that scale puts the two together. The first live
scale is **the least whole number dividing none of the slot multiples `e/(8g)`**.

**Why the first live scale can still fail.** No single runner is in the way throughout; different
runners take different AP times. At scale 2 this is exact: `[PROVED]` an even difference (not a
multiple of 16) is never in the way; an odd difference is in the way at exactly two of the eight
times, `r ≡ ±e⁻¹ (mod 16)`; inversion permutes the four pairs `{±1}, {±3}, {±5}, {±7}`. So
**scale 2 fails exactly when the odd differences occupy all four pairs mod 16**. Checked on every
runner whose first live scale is 2 — 380,751, from all 8-subsets of `[1,20]` and 5,000 random sets
to 2,000 — with no disagreement. Example: `(1,2,3,4,5,6,8,9)`, runner 1 — slot-mate at 9, first
live scale 2, odd differences `1, 3, 5, 7`, one in each pair; it works at scale 5.

**How often the first live scale is the one.** Among runners needing scaling: 421,652 of 519,260 in
all 8-subsets of `[1,20]`; 81–86% in random speeds to 100, 1,000 and 10,000. Where it is not, the
working scale is 1–7 steps further.

**Open:** the same exact description at scales 3, 4, 5, … — which differences take which AP times
at scale `s` — and from it, the factor as a formula. Owner's 1200 on the arrangement above: all
eight runners work at scale 150; the least scale serving all eight is 9; per runner the least are
`5, 1, 1, 7, 5, 3, 4, 3`.

**Credit, added the same day:** item 17's "when" and "first scale to try" are the **dead lattice of
`SKETCH_v7` §7c** (`Dead` = divisors of `{e/8 : 8 | e}`, `L₀` the first live step), re-derived here
before the owner pointed it out. What item 17 adds beyond §7c is the all-laps reading (§7c counted
`p ∈ {1,3,5,7}` only, giving 78.6%) and the exact scale-2 reason the first live step can fail.

## 18. The dead lattice is proved in Lean and absent from the manuscript  `[SETTLED]`

Owner, 2026-09-14: *"That right the dead lattice, I thought we had already established this its
unfortunate it did[n't] get translated in to our proof."*

It is in the frozen artefact itself — `Construction8/LemmaPass.lean`, covered by the digest
`578022e0…`:

| declaration | says |
|---|---|
| `dead_iff` | step `D` is dead for difference `d` iff `d = 8k` with `D ∣ k` — only differences divisible by 8 kill a step, and they kill the divisors of `d/8` |
| `dead_downward` | a divisor of a dead step is dead |
| `exists_live` | a live step always exists, so `L₀` is well defined |

v7 contains neither "dead" nor `L₀`; §8's table does not list these three; `gate.sh` does not
axiom-check them. **Change when unfreezing:** state the dead lattice in §7 as the cascade's
mechanism for changing the AP scale — when (a shared AP slot, item 17), which scale is first live
(`L₀`), and why `L₀` can still fail (item 17, scale 2) — and add the three declarations to §8 and to
the gate's headline list.

## 19. The AP-scale mechanism at every scale, and a correction to item 17  `[PROVED — elementary; checked]`

Added 2026-09-14. Scripts: `experiments/n8/ap_scale_gaps_varied_v1.py`,
`experiments/n8/ap_scale_mechanism_v1.py`.

**Correction to item 17.** Its 380,751 scale-2 runners were almost all at gcd gap 1 (380,560 at
`g = 1`, 187 at `g = 2`, 4 at `g = 3`), so that count did not test other gap sizes. Tested now: four
arrangements (including the false counterexample) rebuilt at `g = 1, 2, 3, 5, 7, 12, 30, 1974` give
identical slot multiples, first live scale, least working scale and scale-2 verdict for every
runner; 6,066 scale-2 runners at random gaps `2…500`, no disagreement. The gcd gap is a pure scale,
as `gap_is_a_scale` proves.

**The mechanism, derived.** Differences `e` in units of `g`. At scale `s` the AP times are
`t = r/(8sg)`, `r` odd. Put `h = gcd(e, 8s)`, `m = 8s/h`. Runner `e` sits at `h·((e/h)·r mod m)` in
units of `1/(8sg)`, and is in the way exactly when that residue is within `m/8` of `0 (mod m)`:

| `m` | runner `e` at scale `s` |
|---|---|
| `1` (`8s ∣ e`) | on the subject at **every** AP time — the dead lattice |
| even, `≤ 8` | **never** in the way |
| even, `> 8` | in the way where `(e/h)·r` is an odd residue within `m/8` of 0 |
| odd, `> 1` | in the way where `(e/h)·r` is within `m/8` of 0 — always including `r ≡ 0 (mod m)` |

Checked against direct computation for `e ≤ 399`, `s ≤ 40`: 15,960 cases, no disagreement. Scale 2
(item 17) is the case `8s = 16`.

**The false counterexample, runner at speed 1** (differences `30, 74, 96, 127, 159, 175, 224`):

- **Scales 1–4 fail** because two runners share its AP slot — `97` (`96 = 8·12`) and `225`
  (`224 = 8·28`) — and `12` is divisible by `1, 2, 3, 4`: at each of those scales `97` is on the
  subject at every AP time (`225` too at `1, 2, 4`). Nothing else is involved.
- **Scale 5 works** because `5` divides neither `12` nor `28`. Of its 20 AP times: `97` and `225`
  both take `r = 5, 15, 25, 35`; `31` and `176` never are in the way (differences `30`, `175` sit on
  the scale-5 ideal); `75`, `128`, `160` take 4 each. Sixteen taken, `r = 9, 19, 21, 31` free — so
  `t = 9/40` is the first scale-5 AP time.
- **The runner at 97 fails at live scale 5**: its slot-mates take `r ≡ 0 (mod 5)` and its other five
  take 4 each — 28 claims on 20 times, all 20 taken. Scale 6 is dead (`6 ∣ 12`). At scale 7, `160`
  (difference `63 = 9·7`) sits on the ideal and 8 times are free.

## 20. The AP scale is one scale for the whole arrangement  `[OPEN — the factor's formula]`

Owner, 2026-09-14: *"the scale to the ap gap needs to work for all runners."* One scale for the
arrangement; each runner still takes its own AP time at that scale (its own `r`), so this is not a
global clock. Script: `experiments/n8/ap_common_scale_v1.py`.

**Dead for the arrangement:** every divisor of every sharing pair's slot multiple. On
`(1,31,75,97,128,160,176,225)` the multiples are `2, 4, 6, 12, 16, 28`, so scales
`1, 2, 3, 4, 6, 7, 8, 12, 14, 16, 28` are dead.

| scale | status | per runner (speed: first free AP time) |
|---|---|---|
| 5 | first common live — **fails** | `97` has no free time (item 19); the other seven do |
| 9 | next live — **works for all eight** | `1: 11/72`, `31: 1/8`, `75: 7/72`, `97: 17/72`, `128: 1/72`, `160: 1/24`, `176: 17/72`, `225: 7/72` |
| 150 (owner's 1200) | live — works for all eight | `1: 71/1200`, `31: 1/240`, `75: 7/1200`, `97: 7/1200`, `128: 1/240`, `160: 11/1200`, `176: 19/1200`, `225: 7/1200` |

**How far the working scale sits past the first common live one** (steps, dead scales included):
all 12,869 8-subsets of `[1,16]` with gcd 1 — 0 steps in 1,377, up to 13; random speeds to 200 —
0 steps in 723 of 2,000; to 5,000 — 395 of 1,000. Every step past it is a live scale where some
runner has all its AP times taken (item 19's mechanism).

**Open:** from item 19's table, which live scales leave every runner a free time — that is the
factor.

## 21. The spread determines the AP; its relation to Theorem 4.9  `[PARTLY PROVED]`

Owner, 2026-09-14: *"AP variations can only handle up to the next AP location, that is, so the
spread of the speeds determins the ap to use."* Script: `experiments/n8/ap_spread_scale_v1.py`.

**What the spread settles — proved.** An AP of gap `D` has eight locations. A runner further than
the next location wraps onto another runner's location: two speeds differ by a multiple of `8D`,
the dead lattice. Every dead scale divides a slot multiple, and every slot multiple is at most
`spread/(8g)`. So **at any gap with `8D > spread` no runner shares a location — the scale is live
for every runner.** On `(1,31,75,97,128,160,176,225)`: spread 224, so from scale 29 on; the
progressive run found scale 28 (the largest slot multiple, `224/8`) the last failure, and every
scale from 29 to 50, and 96, 150, 240, worked for all eight.

**What the spread does not settle — measured.** Live is not the same as every runner having a
free AP time (item 19: the runner at 97 at live scale 5). At the spread-determined scale, some
runner has every AP time taken in:

| family | `8sg > spread` | `7sg ≥ spread` |
|---|---|---|
| all 8-subsets of `[1,20]`, gcd 1 (125,925) | 97,769 | 95,114 |
| random speeds to 300 (3,000) | 12 | 8 |
| random speeds to 3,000 (1,000) | 0 | 0 |
| rebuilt at gaps 2–40 from sets in `[1,60]` (1,500) | 542 | 488 |

Exact example: `(1,2,3,4,5,6,7,9)`, spread 8, scale 2 (`t = r/16`) — the runner at 2 has no lonely
AP time; its odd differences `1, 1, 3, 5, 7` occupy all four pairs mod 16 (item 17).

**Theorem 4.9 uses the same number.** Its threshold is the average speed gap `S/7`, and a gap
`D ≥ S/7` is exactly the `7D ≥ spread` reading above (on the counterexample, `S/7 = 32`, the scale at
which the runner at 1 reaches its earliest time `11/256`). What 4.9 proves is narrower: a runner
whose **own** flanking gaps are both at least `S/7` (one, for an end runner) has `7·d_min ≥ spread ≥
d_max`, so Theorem 4.8 gives it `u = 1/8` at its own `d_min`. On the counterexample that is only the
runner at 225 (gap 49); Theorem 4.8 itself reaches 31, 75, 97, 128, 225. 4.9 is the case where a
runner's own `d_min` already reaches the spread-determined gap; it says nothing about an AP of gap
`S/7` for runners whose `d_min` is smaller.

**Addendum to item 21 — which times a scale keeps.** `[PROVED]` The AP times of scale `s'` are AP
times of scale `s` exactly when `s` is an **odd** multiple of `s'`: `r/(8s') = (r·s/s')/(8s)`, and
`r·s/s'` is odd iff `s/s'` is odd. Even multiples lose them. On `(1,2,3,4,5,6,7,9)`: the runner at 2
is isolated at `1/8` by Theorem 4.8 (scale 1), keeps a time at scales 1, 3, 5, 7 and has none at
2, 4, 6; the runners at 1 and 9 share an AP location at scale 1 (`9 − 1 = 8`). The first scale giving
all eight runners a time is 5, then 8. Theorem 4.9 reaches only the runner at 9 here.

## 22. The function, reconstructed from the record — and items 17–21 used the wrong frame  `[SETTLED — sources quoted]`

Added 2026-09-14, after the owner's account: *"Initially we … could find the isolation speed of
every runner deviation from AP up to colliding with the next neighbours AP location … until a speed
at 9, to solve that we used mod n referred to a grid … At some point we were using a mix of dmin of
ap/or grid dmin. Ultimately we found that for weird speed spread neither would work, until we
increase the AP from 1 to 2. Then we found we didn't need to search for the right scale we derive
it or more correct the speeds determined it."*

The record, in that order:

| stage | document | what it established |
|---|---|---|
| AP deviation up to the next location | `UNIFIED_MOD_N_RULE_v1` §3–4 | AP ± ε; only r1 and r8 reach 7, one from the band edge |
| mod n, the grid as reference | `COMPLETE_PREDICTOR_v1` (T4, T7, T8) | `d_min = 1`: blocked iff a difference `≡ 0 (mod 8)`; grids of gcd `g`: every moment `1/(8g)` |
| mixed AP / grid `d_min` | `SKETCH_v7` §7b | the four instants at each runner's own `d_min` |
| **AP 1 → 2, the scale determined** | **`RESIDUE_BAND_v1`** — *"Arrived at from the owner's suggestion: for `(1,3,5,9,12,14,16,18)`, use AP 2."* | **the AP scale for a runner is its own `d_min`, set by its two neighbours.** Blocked ⟺ a difference lies within `d_min` of a multiple of `8·d_min`, on `ℝ/(8·d_min)ℤ` — proved for all real speeds. `d_min = 1` is the grid rule; `d_min = 2` is "AP 2" |
| the lattice on top of `d_min` | `WHY_IT_PREDICTS_v1` §2 | lattice `L` (`u = p/(8L)`) is dead ⟺ some reading `≡ 0 (mod 8L)`; **first live lattice `≤ ⌊s_max/8⌋ + 1`**, `s_max = d_max/d_min` — the runner's own spread — proved |
| the base determined, not searched | `C1_MIXED_CONSTRUCTION_v2` | base `u = p/8` or `u = (2k+1)/(2·s_max)`, where the farthest runner (always an end runner) is diametrically opposite — spread `s_max`, recurring with period `1/s_max` in `u`; then move to clear the blocked. 162,694 runner-instances, 0 failures; the fit and a bound on `k` unproved. (Its header is dated 2026-09-15; the file dates from 2026-09-13.) |

**Correction to items 17–21.** They measured the AP scale on the **gcd lattice** — gap `g` for the
whole arrangement, scales `s·g`, and the arrangement's total spread. `RESIDUE_BAND_v1` §4 already
records that frame as wrong: *"the grid frame lives on the gcd lattice while the event is at the
`d_min` scale — **wrong** — the frame moves to `d_min`"*, and on making the AP bigger, *"the fix is not
a coarser lattice, it is a wider band at the same scale."* The arithmetic in items 17–21 stands
(dead lattice, the mechanism table, odd multiples keeping times), but it is stated in a frame the
framework left behind. Restated in the framework's frame, the dead lattice is `WHY_IT_PREDICTS_v1`
§2 and the spread bound is per runner, `⌊d_max/(8·d_min)⌋ + 1`.

## 23. §7A — the "no global clock" row needs two qualifications  `[SETTLED]`

Owner, 2026-09-14: *"Global clock no but the slowest speed defines a cycle"* and *"Phi (n) law for AP
on LRC proves global isolation for arithmetic progress."* v7 §7A's row reads *"No global clock — The
procedure yields up to eight different times for the eight runners. No single global isolation
event is needed."* **Change:** keep the ban on *needing* a shared isolation event, and state beside it
that (a) the reference ideal, the AP, **is** globally isolated — the φ(n) law, §5 and Theorems 4.5–4.7
— and deviations from it are then read runner by runner; and (b) the slowest runner's lap is the
framework's cycle, the unit in which times are counted (`SKETCH_v7` §5, §7d). Without these the row
reads as excluding the framework's own reference.

## 24. Fitting the arrangement between the AP locations  `[OPEN — how the fit feeds each runner's reading]`

Owner, 2026-09-14: *"Its about fitting them in between the spaces they can be, so for ap r1 can be 0
to <2, r2 can be [1] to <3, their is overlap between them."* Script: `experiments/n8/ap_fit_spread_v1.py`.

**Stated exactly.** Against an AP of gap `D`, runner `k` may sit anywhere strictly between its
neighbours' AP locations, `(A_k − D, A_k + D)`; adjacent bands overlap by one gap. An arrangement
**fits** when every runner is inside its band. Anchoring the AP at the slowest and fastest speeds
makes the gap `S/7` — the spread determines it, and it need not be a whole number.

| arrangement | gap `S/7` | deviations from the fitted AP | fits |
|---|---|---|---|
| `(1,31,75,97,128,160,176,225)` | 32 | `0, −2, 10, 0, −1, −1, −17, 0` | yes |
| `(1,2,3,4,5,6,7,9)` | `8/7` | `0, −1/7, …, −6/7, 0` | yes |
| `(1,3,5,9,12,14,16,18)` (the AP-2 case) | `17/7` | `0, −3/7, −6/7, 5/7, 9/7, 6/7, 3/7, 0` | yes |
| `(1,2,3,4,5,6,7,100)` | `99/7` | `0, −92/7, …, −552/7, 0` | no |

**What the fit does not do by itself** `[VERIFIED — exact]`: give every runner a time on the fitted
AP's own instants `t = r/(8D)`. In all 8-subsets of `[1,20]`, 45,568 fit and 34,462 of those have a
time for every runner there; 80,357 do not fit and 58,800 of those still do. Random speeds to 300:
581 of 582 fits, and all 2,418 non-fits; to 3,000: all. On the counterexample the fitted instants
`r/256` do give every runner a time, and runner 1's earliest, `11/256`. But `(1,2,3,4,5,6,7,9)` fits,
and the runner at 2 has no time on `7r/64` — while its own `d_min = 1` reading isolates it at `1/8`
(Theorem 4.8). So the fitted AP is the ideal; the runner's time is read at its own `d_min`
(`RESIDUE_BAND_v1`). How the fit decides which runners then need the cascade is the step to write
down.

## 25. What the Lean already has for finding a time — and §8 understates it  `[SETTLED]`

Owner, 2026-09-14: *"look to see if the search function that is already in the lean can be useful."*
All in the frozen `Construction8/LemmaPass.lean` (digest `578022e0…`), general `n`:

| declarations | what they give |
|---|---|
| `opening`, `clear_on_left`, `opening_le`, `reading_complete` | **completeness over openings, every lap, real speeds**: lonely at any `t` ⟹ lonely at an opening `(⌊d·t⌋ + 1/n)/d` of one of its own differences, no later than `t` |
| `localisation_free` | integral readings: lonely anywhere ⟹ lonely inside the first window |
| `spine_all_or_nothing` | integral reading `s` at a unit `p`: clear iff `n ∤ s`, the same for every `p` |
| `step_ceiling` | clear at `a/(nD)` forces `D ≤ a·d_min`, with `a` free |
| `dead_iff`, `dead_downward`, `exists_live` | the dead lattice (item 18) |
| `blocked_lands_on_threshold`, `unblocked_stays_clear` | a **determined move**: integral readings, one blocked reading `Sb` (`n ∣ Sb`) which is the largest; at `u = p/n + 1/(n·Sb)` the blocked runner sits exactly on the threshold and every unblocked runner with `1 ≤ s·p mod n ≤ n−2` stays clear |

**§8 understates it.** v7 §8 says Proposition 7.1 is machine-checked only outside the digest, as
`exists_clear_candidate`, and revision item 4 asks for Prop 7.1 to be restated per lap.
`reading_complete` is **inside** the digest and already is the all-laps statement, over the reals.

**Reach of the determined move** (`experiments/n8/lean_c1_integer_reach_v1.py`, all 8-subsets of
`[1,20]`, every runner, exact): applies to 48,936 runners, and every instant it produces is lonely
(0 failures, as the two lemmas guarantee). Not applicable: 413,016 with non-integral readings;
309,458 unblocked (the spine already works); 224,890 integral-blocked outside the hypotheses (more
than one blocked reading, or the blocked one not the largest); 11,100 with one largest blocked
reading but no unit `p` fitting. Example: `(1,2,3,4,5,6,7,9)`, runner 1 — the runner at the next AP
location — `u = 1/8 + 1/64 = 9/64`, matching `procedure_laps_v1`'s control. The composition of the two
lemmas into one theorem is not stated in Lean.

## 26. Buffer against room — the move is proved; the scale is not read off the ratio  `[PARTLY PROVED]`

Proposed 2026-09-14 (relayed by the owner): compute the buffer the worst deviation needs against the
room the clear gaps allow, and when it does not fit, calculate the scale multiplier directly.
Owner: *"We should be able to figure this out from the existing lean information."*

**Proved in Lean** — `experiments/n8/BufferRoom_v1.lean`, outside both trees, axioms
`[propext, Classical.choice, Quot.sound]`, real readings. From a base `u₀`, a runner at phase
`φ = fract(s·u₀)` needs `(1/8 − φ)/s` if blocked low, `(9/8 − φ)/s` if blocked high, nothing if clear;
its room is `(7/8 − φ)/s`, or `(15/8 − φ)/s` if blocked high. `clear_after_move`: requirement `≤ ε ≤`
room ⟹ clear at `u₀ + ε`. So the move by the largest requirement is **computed**, and sound whenever it
fits the smallest room. This generalises `blocked_lands_on_threshold` / `unblocked_stays_clear` from
integral readings to real ones. Instance `runner160_lonely`: the counterexample's runner at 160 (readings
`159/16, 129/16, …`, not integral), base `1/8`, the runner at 31 (difference 129) blocked low at phase `1/128`, `ε = 5/344`,
lonely at `t = 3/344` — its earliest isolation instant.

**Measured** (`experiments/n8/buffer_room_scale_v1.py`, 12,000 runners, speeds to 400, bases `p/(8L)` in
the first window): the move fits at `L = 1` for 11,147. Where it does not, the least lattice that fits
is 2, 3 or 4 **independently of the requirement-to-room ratio** (ratio 2 → `L` 2 or 3; ratio 14 → 3 or 4;
ratio 20 → 2). **The multiplier is not the ratio.**

**A limit of any first-window move.** The counterexample's runner at speed 1 has no lonely instant in its
first window at all (item 12), so no first-window base fits at any `L ≤ 12` — and `C1_MIXED_CONSTRUCTION_v2`,
which confines itself to `[1/8, 7/8]`, cannot reach it. The move has to be allowed on later laps (item 1).

## 27. The moment iteration is the framework's "search", and it is deterministic — now in Lean  `[PROVED-LEAN, partial]`

Added 2026-09-14. **Replication:** `COMPLETE_PREDICTOR_v1` §1 exactly as documented — from
`t = 1/(8·d_min)`, move to the largest next opening `(8k+1)/(8d)` of the runners in the way, re-test —
equals the BSM first isolation time for **207,464 of 207,464** runners (one mover step 0.01; two
movers; every runner moved; push-out and spread families to 200; all 8-subsets of `[1,16]`; random
integers to 1,000). Most moves observed: 24. `experiments/n8/complete_predictor_replication_v1.py`.
The slot-sharing displacement `1/(8·d_min) + 1/(8·Δ)` is a single step of this move; the dead-lattice
"scale jump" is where the move takes several steps.

**Lean** — `experiments/n8/MomentIteration_v1.lean`, outside both trees, real speeds, axioms
`[propext, Classical.choice, Quot.sound]`, no `sorry`:
`inWay_until_opening`, `lt_nextOpening`, `nextOpening_le_of_lonely`, `move_le_of_lonely` (no move
overshoots a lonely time), `lonely_of_fixed` (a fixed point is lonely), `iterate_le_of_lonely`,
`bound_le_of_lonely`, and **`first_isolation_of_fixed`: if an iterate of the move from the bound is
fixed, it is lonely and no positive lonely time precedes it.**

**Not stated:** that some iterate is fixed. For v8: this replaces §7.1's two families and §7.4's Claim —
the open statement becomes "the orbit of the bound under `move` reaches a fixed point".

## 28. The flank at the first isolation time, and who sets each move  `[PROVED-LEAN; VERIFIED]`

Added 2026-09-14. **Lean** — `experiments/n8/MomentIteration_v2.lean` (v1 unchanged), no `sorry`,
axioms `[propext, Classical.choice, Quot.sound]`:
`circDist_at_nextOpening`, `move_eq_self_or_opening`, `iterate_has_threshold_runner` (every iterate
from the bound has a runner at exactly `1/8`), `flank_of_threshold` (a runner at exactly `1/8` from a
lonely subject is the nearest ahead or the nearest behind), and **`flank_at_first_isolation`**: over
signed speed differences, if an iterate `T` of the move from the bound is fixed, the subject is lonely at
`T`, no positive lonely time precedes it, and some runner is a flank at exactly one eighth.

**Who sets the moves** (`experiments/n8/move_setters_v1.py`, same iteration). In every multi-move case
(1,036; 1,210; 17,112; 1,041 across one mover, every runner moved, `[1,16]`, random integers to 1,000)
the setter changes at every move — no runner sets two consecutive moves. The last setter is always the
flank at `1/8` (forced). In integer arrangements the first setter is the slot-sharer (31,680 of 33,264
in `[1,16]`; the rest the `r1/r8` wrap) — forced by the band identity. Later setters are spread over AP
index distances 2–4, speed-neighbours and slot-sharers: no single class determines the handover.

## 29. The cascade function, stated: a recursion on the AP scale  `[DERIVED; VERIFIED 124,488 of 124,488]`

Added 2026-09-14. Every move of the moment iteration is a change of AP scale: the bound
`1/(8·d_min)` is the `u = 1/8` spine point of the AP of gap `d_min`, and a move to an opening
`(8N+1)/(8·d_l)` is the spine point of the AP of gap `d_l/(8N+1)`. At scale `D`, runner `l` reads
`s_l = d_l/D` and is in the way iff `|s_l − 8N_l| < 1` (the band identity). Hence

    D_0 = d_min,    D_{n+1} = D_n · min{ s_l / (8N_l + 1) : |s_l − 8N_l| < 1 },    time = 1/(8·D_final),

stopping when no reading is within 1 of a multiple of 8. **The next runner is the one whose reading is
proportionally furthest short of its opening multiple `8N+1`.** At the final scale the last runner reads
exactly `8k+1` — one slot away, at exactly one eighth, the nearest runner of that AP — and every other
reading is at least 1 from `8ℤ`: the final event is an AP isolation at scale `D_final`.

`experiments/n8/scale_cascade_recursion_v1.py`: recursion time = BSM first isolation time for 12,736 +
4,800 + 102,952 + 4,000 runners (one mover; every runner moved; `[1,16]`; random integers to 1,000).
Final readings observed: `1, 9, 17, 25, 33, 41, 49` only. The last runner is rarely the subject's speed
neighbour (72/1,974; 96/2,429; 556/33,264; 176/2,170) — mostly 3–4 speed ranks away.

Each step evaluates seven readings at one scale; the whole chain of scales is not yet known without
stepping. This recursion is the "d_min/cascade function" for the Lean upgrade: `move` from
`MomentIteration_v2.lean` restated on the scale.

## 30. The chain read from the runners' lap completions; the drift lines; the scale bridge in Lean  `[VERIFIED; PROVED-LEAN]`

Added 2026-09-14. Script `experiments/n8/chain_from_laps_v1.py`; 29,320 runners (one mover step 0.05;
every runner moved; `[1,14]`; random integers to 300).

**The chain is the run of lap-completion zones.** Runner `l` completes relative lap `N` at `N/d_l` — its
distance from zero comes round — and is in the way on the open zone of half-width `1/(8d_l)` about it.
Sorting every zone by its left end and taking one pass from the bound `1/(8·d_min)` gives the first
isolation time: **29,320 of 29,320** equal to BSM. The cascade's setters appear in increasing order of
their lap-completion time: **4,684 of 4,684** chains of two or more moves. (The single pass is the
boundary set read in time order; what it adds is that the chain is fixed by the sorted list of `N/d_l`.)

**Drift lines in the AP-deviation frame.** With `d_l = (a_l + e_l)·d_min`, at the subject's AP instant
`n/8` (`n = 8K + r` odd) runner `l` sits at `r·a_l + n·e_l` eighths (mod 8): its AP slot plus its
deviation accumulated over `n` eighths. It is in the way while the line `n·s_l` is within 1 of `8ℤ`, i.e.
on the explicit intervals `((8M−1)/s_l, (8M+1)/s_l)`. The first lonely AP instant computed from these
intervals (one merged pass per residue, no instant evaluated) equals direct evaluation: **29,320 of 29,320**.

**Refuted (proposal relayed by the owner):** `D_final = d_min / ∏(8N_i + 1)`. At `(1,…,6,8,9)`,
runner 1, the chain is `(8, N=1), (7, N=1)` and `D_final = 7/9 = d_last/(8k+1)`; the product gives `1/81`.
Each step resets to `D' = d_l/(8N+1)`; the factors do not accumulate. A wrap-integer factorisation cannot
be the general mechanism either: multi-move chains occur with real-valued deviations, where there is no
integer `q`.

**Lean** — `experiments/n8/MomentIteration_v3.lean` (v2 unchanged), no `sorry`, standard axioms:
`inWay_at_scale_iff` — at `t = 1/(8D)` a runner is in the way iff its reading `d/D` is within 1 of a
multiple of 8; `nextOpening_at_scale` — its next opening is `1/(8·(d/(8N+1)))`, the first spine point of
the AP of gap `d/(8N+1)`. Together with `move_eq_self_or_opening` this is the scale recursion of item 29.

## 31. The first isolation time as the end of the run of lap-completion zones — in Lean  `[PROVED-LEAN]`

Added 2026-09-14. `experiments/n8/MomentIteration_v4.lean` (v1–v3 unchanged), no `sorry`, standard axioms.

- `zoneLo d N`, `zoneHi d N` — the open zone `((N − 1/8)/d, (N + 1/8)/d)` about runner `d`'s lap-`N` completion.
- `inWay_iff_zone` — in the way at `t` iff `t` lies in one of the runner's lap zones.
- `Run ds b L T` — a list of lap zones from `b`, each containing the end of the one before; `T` the last right end.
- `Run.covers` — every time from `b` up to `T` lies in some runner's zone.
- **`first_isolation_of_run`** — a run from the bound `1/(8·d_min)` ending at a lonely time `T`: no positive lonely
  time precedes `T`. Proved from the zones alone; `move` does not appear.
- `run_of_iterate` — every iterate of the move is the end of a run (each move adds its setter's zone).
- `run_end_eq_fixed_point` — a run from the bound ending at a lonely time ends at the iteration's fixed point.
- **`first_isolation_as_zone_run`** — if the iteration reaches a fixed point `F`: `F` is the end of a run of lap zones
  from the bound, lonely, first, and every run from the bound ending at a lonely time ends at `F`.

**For v8:** the first isolation time is stated as the end of the run of lap-completion zones `N/d` that starts at
the nearest runner's bound. The open statement becomes: **for every arrangement and runner, the run of lap zones
from the bound ends** (a run from the bound ending at a lonely time exists).

## 32. Finiteness and the drift lines — in Lean  `[PROVED-LEAN]`

Added 2026-09-14. `experiments/n8/MomentIteration_v5.lean` (v1–v4 unchanged): 22 headline declarations, no
`sorry`, every one on `[propext, Classical.choice, Quot.sound]`.

**Finiteness.**
- `iterate_mem_openings` — below a lonely time `s`, every iterate from a positive start is the start or an opening
  `(k + 1/8)/d` with `d ∈ ds`, `0 ≤ k ≤ ⌈d·s⌉`: a finite set.
- `exists_fixed_of_lonely` — a positive lonely time forces the iteration from the bound to reach a fixed point
  (a non-stopping iteration is strictly increasing and cannot stay in a finite set).
- **`lonely_iff_run_ends`** — for every subject: lonely at some positive time ⟺ the iteration from the bound
  reaches a fixed point ⟺ a run of lap zones from the bound ends at a lonely time.

**Drift lines** (subject's nearest difference `m`, runner reading `a + e`, AP index `a ∈ ℤ`, deviation `e`):
- `drift_position` — at the AP instant `n = 8K + r` the runner sits at `(r·a + n·e)/8` plus `K·a` whole laps:
  AP slot plus accumulated deviation.
- `inWay_at_ap_instant_iff_drift` — in the way there iff `r·a + n·e` is within 1 of a multiple of 8.
- `drift_blocked_iff_interval` — iff `n ∈ ((8M − 1)/(a + e), (8M + 1)/(a + e))` for some `M`.
- `zone_at_ap_instant_iff` — those intervals are the runner's lap zones read at AP instants.

**Status of the open statement.** With `lonely_iff_run_ends`, "the run of lap zones from the bound ends" is
**equivalent** to "the subject is lonely at some positive time" — proved, per runner, for real speeds. The
framework's open statement and LRC(8) for that runner are now one statement in Lean; what the framework adds is
that the time, when it exists, is the end of that run, computed by the cascade.

## 33. Slot-sharers and the own AP: what removes every own-AP instant  `[PROVED-LEAN; VERIFIED; one hypothesis refuted]`

Added 2026-09-14.

**Lean** — `experiments/n8/MomentIteration_v6.lean` (v1–v5 unchanged), no `sorry`, standard axioms:
`sharer_inWay_at_ap_instant` — a runner at difference `8b·m` is in the way at every AP instant `n/(8m)`;
`not_lonely_at_ap_instant_of_sharer` — with such a runner present the subject is lonely at no own-AP instant.

**The converse fails.** `experiments/n8/drift_sharer_dichotomy_v1.py`, `drift_denominator_v1.py`: runners with
no exact slot-sharer and still no lonely own-AP instant exist (44; 10; 396 in `[1,16]`; 51 random to 300). Every
runner moved from the AP by `k/q`, 2,400 runners per `q`: such runners number 32, 71, 93, 66, 91, 58, 40, 31, 21, 11
for `q = 2 … 25`, and **0** for `q = 50, 97, 211, 1000`. Sharer present with a lonely own-AP instant: 0 at every `q`.
`[VERIFIED — scoped: AP base, deviations ≤ 0.45, 300 arrangements per q]`

**Their structure** (`experiments/n8/finer_scale_sharing_v1.py`, 1,079 such runners, reading denominators 2–20):
- `q = 2`: the odd doubled readings take all four slot-pairs `{±1},{±3},{±5},{±7}` mod 16 — 370 of 370. This is the
  scale-2 pair rule (item 17) read at the subject's own AP instants, so it is exact rather than evidence.
- **Refuted:** "every such runner has a sharer at a finer scale" (some runner with `L·s ∈ 8ℤ`, `L | q`): 633 of 1,079.
- A runner landing exactly on the subject at some (not all) own-AP instants: 491 of 1,079.
- Least lonely lattice on the own `d_min`: `L = 2` (864), 3 (139), 4 (59), 7 (13), 5 (3), 6 (1); `L | q` in 505.

**Open:** the exact rule for `q ≥ 3`, derived as the `q = 2` pair rule was — at own-AP instants a runner of reading
`c/q` sits at `n·c/q` (mod 8), a residue question mod `8q`.

## 34. The own-AP residue rule at every reading denominator  `[DERIVED; VERIFIED 40,000 of 40,000]`

Added 2026-09-14. Generalises item 17's scale-2 pair rule and item 33's `q = 2` pattern.

**Derivation.** Subject's readings `s_l = c_l/q` (in AP-deviation terms `c_l = q·a_l + p_l`, `e_l = p_l/q`). At own-AP
instant `n` (odd) runner `l` sits at `n·c_l/q` (mod 8), in the way iff `n·c_l mod 8q` is strictly within `q` of 0. Put
`h_l = gcd(c_l, 8q)`, `m'_l = 8q/h_l`, `u_l = c_l/h_l` (a unit mod `m'_l`); then `n·c_l mod 8q = h_l·(n·u_l mod m'_l)`,
so `l` is in the way iff `n·u_l mod m'_l` is strictly within `m'_l/8` of 0, i.e. `n ≡ u_l⁻¹·ρ (mod m'_l)` for `|ρ| < m'_l/8`:

| `m'_l` | runner at own-AP instants |
|---|---|
| 1 | exact slot-sharer — in the way at every `n` (Lean: `sharer_inWay_at_ap_instant`) |
| even, ≤ 8 | never in the way (`n·u_l` odd; the band holds only 0) |
| even, > 8 | in the way at `n ≡ ±u_l⁻¹·ρ`, `ρ` odd, `0 < ρ < m'_l/8` |
| odd, > 1 | in the way at `n ≡ u_l⁻¹·ρ`, `|ρ| < m'_l/8`, including `n ≡ 0 (mod m'_l)` |

**Rule.** Own-AP instant `n` is lonely iff `n·u_l mod m'_l` is at least `m'_l/8` from 0 for every runner. The lonely own-AP
instants are the odd `n` mod `8q` outside every runner's residue classes; the first is the least of them. At `q = 2` this
is `n ≢ ±c⁻¹ (mod 16)` for odd `c` — item 17.

**Verified** (`experiments/n8/residue_rule_q_v1.py`): every runner moved from the AP by `k/q` for `q = 3 … 25` (400
arrangements each) plus 600 random integer sets to 200 — 40,000 runners, reading denominators 1–30+. The rule's set of
lonely own-AP instants equals direct evaluation for **40,000 of 40,000**, including all 5,090 with none; the first lonely
instant agrees for all 40,000.

## 35. Depth and time against the spread — no ceiling of 24; the time ratio stays near 12, hardest just above S = 7  `[VERIFIED / EMPIRICAL]`

Added 2026-09-14. Scripts `experiments/n8/depth_growth_v1.py`, `depth_adversary_v1.py`, `ratio_vs_spread_v1.py`.
`R = t/(1/(8·d_min)) = d_min/D_final` (time in units of the nearest runner's bound), `S = d_max/d_min`, depth = number of
AP scales in the cascade.

- **Correction:** near the wrap `(1,…,7, 9 ± δ)`, runner 1's **first isolation time** stays at `9/64` (2 scales) for
  `δ` down to `10⁻⁶`. The `1/(8δ)` lap law applies to its first lonely **own-AP instant**, not to its first isolation
  time.
- **Depth has no ceiling at 24.** Sweeps: max 17–18 (`[1,24]`, random to `10⁵`), 25 (push-out families to `x = 5000`).
  A short adversarial climb over speeds ≤ 400 reached **29** at `(27,70,107,137,159,188,344,393)` r8.
- **The time ratio R.** Adversarial maxima by spread band, speeds ≤ 400 / ≤ 3000: `S ∈ [7,8)` 11.55 / 10.86;
  `[8,10)` 10.85 / 11.13; `[10,15)` 6.84 / 6.55; `[15,30)` 6.25 / 6.50; `[30,100)` 5.56 / 6.45. Largest found overall
  **11.79** at `(96,136,189,227,266,308,331,398)` r1, `S = 7.55`. R did not grow from speeds 400 to 3000 in any band.
- **Counting link** `[PROVED — arithmetic]`: each move lands on an opening below `t`, so depth ≤ `(7/8)·S·R + 7`.

**What a depth bound would be.** By `lonely_iff_run_ends`, "depth ≤ B for every arrangement" is equivalent to existence
for that runner — not a smaller problem. The observed structure suggests the concrete bounded form is on `R`: every
first isolation time found has `R < 12`, i.e. `u = d_min·t < 3/2`. A statement "`R < 16` always" (lonely before the
nearest runner's second relative lap ends) would imply existence and depth ≤ `14·S + 7`. It is **not established**; it
is a lap bound of the kind item 1 warns about, one lap later than v7's false first-window claim, and the hardest
arrangements sit in the same band just above `S = 7` where that claim failed.

## 36. One round of adversarial search for R ≥ 16 in S ∈ [7,10] — none; the maxima converge to R ≈ 11.96 at S ≈ 7.44  `[EMPIRICAL — one round]`

Added 2026-09-14. `experiments/n8/r16_search_v2.py` (annealing, 44 runs, 232 s; integer grids to 400 / 3,000 /
20,000, rational grids with denominators 10 and 100, restarts seeded from earlier maxima). Every top arrangement
re-checked: cascade time = BSM.

- **No arrangement with R ≥ 16.**
- **Independent runs on unrelated grids converge on the same value:** `R = 11.9628` (speeds to 20,000), `11.9607`
  (to 2,330), `11.9603` (denominator 100), `11.9592`, `11.9581`, `11.9563`, `11.9540` — all at `S ≈ 7.44`.
- Deepest cascade found: 30 scales, at `(410, 618, 788, 1252, 1452, 2298, 2416, 2747)` r4, `R = 11.91`, `S = 7.475`.

**Reading.** The largest time ratio found looks like a limit approached from below, near `R = 12` (`u = d_min·t = 3/2`),
at spreads just above the Theorem 4.8 threshold. Not established: whether 12 is the supremum, whether it is attained,
or what arrangement realises it. One round only; nothing here bounds `R` below all arrangements.

## 37. The moment iteration holds at every threshold `1/n`; at `n = 3` it stops within one move — in Lean  `[PROVED-LEAN, outside both trees; one derived-on-paper step now formal]`

Added 2026-09-14.

**General `n`.** `experiments/n8/MomentIterationN_v1.lean` is all of `MomentIteration_v6` with the constant `8`
replaced by a parameter `n ≥ 2` (`[Fact (2 ≤ n)]`). Compiles, no `sorry`, 24 of 24 axiom lines
`[propext, Classical.choice, Quot.sound]`; two examples check that `n = 8` recovers v6. The proofs used only
`0 < n`, `n⁻¹ ≤ 1/2` and `n·n⁻¹ = 1`; the runner set was already an arbitrary finite set of positive differences.
Soundness, first-ness, completeness given termination, finiteness (`lonely_iff_run_ends`), the flank lemma, the scale
bridge (reading within 1 of a multiple of `n`), drift lines and slot-sharers therefore hold at every `n`.
Not carried: the residue rule for `q ≥ 3` (item 34, derived at 8 only), the `R ≈ 12` behaviour (items 35–36),
`Construction8`, `BufferRoom`.

**n = 3.** `experiments/n8/MomentIterationN_v2.lean`, section `TerminationThree` (compiles, no `sorry`, axioms as above;
imports only `ConstructionN`, which does not reach `SmallN`):
- `three_stops_within_one_move` — at most two positive differences, nearest `m`: the first iterate of the move from
  `1/(3m)` is fixed.
- `three_first_isolation` — the subject is lonely at that iterate and at no earlier positive time.
- Mechanism (`nearest_clear_after_move`): if the other runner `b` is in the way at the bound, `|b/m − 3N| < 1` with
  `N ≥ 1`; the move goes to scale `b/(3N+1)`, where `b` reads `3N+1` (on the threshold) and `m` reads
  `(3N+1)·m/b ∈ (1, 2]`, clear.

**Chain lengths by `n`** (`experiments/small_n/chain_depth_by_n_v1.py`, exact rationals, random and near-AP sets; sample
maxima, not bounds): n=3: 1, n=4: 3, n=5: 7, n=6: 9, n=7: 8, n=8: 11. Large counts sit at the maximum for n=4 (10,747 at
3), n=6 (2,833 at 9), n=8 (1,524 at 11) — not yet examined.

**For v8.** The framework's termination is proved at `n = 3` by its own objects (setter, scale, readings). `n = 4` is
the first order with a multi-move chain and is the next target; the route through `lonely_iff_run_ends` plus an
existing existence proof is available in Lean and is not the route, since it says nothing about why the chain stops.

## 38. n = 4: the iteration stops within three moves, before the nearest runner reads 3 — in Lean; the return lemma at every `n`  `[PROVED-LEAN, outside both trees]`

Added 2026-09-14. `experiments/n8/MomentIterationN_v3.lean`, section `TerminationFour` (compiles, no errors or warnings,
no `sorry`, 29 of 29 axiom lines `[propext, Classical.choice, Quot.sound]`; imports only `ConstructionN`).

- `return_lemma` (every `n ≥ 2`) — runner `x` at its lap-`P` opening; the next move is set by `y` at lap `Q`; if `x` is in
  the way again at the new iterate, then `Q·(n − 2) < 2P + 1`. At `n = 4`: `Q ≤ P`; at `n = 8`: `6Q < 2P + 1`.
- `four_stops_within_three_moves` — at most three positive differences, nearest `a`: the third iterate of the move from
  `1/(4a)` is fixed, and `a·T < 3/4` (the nearest runner reads below 3).
- `four_first_isolation` — the subject is lonely there and at no earlier positive time.
- Supporting: `step_cases` (a move lands on the opening of a runner in the way), `not_inWay_at_own_opening`,
  `clear_in_window`, `mem_three`.

**The chain, with `τ = a·t`.** Move 1 (setter `x₁`, lap `k₁ ≥ 1`): `τ < 5/12`. Move 2 (setter `x₂ ≠ x₁`, lap `k₂ ≥ 1`):
`3t₂ < 5t₁`, `τ < 25/36`. The nearest runner is clear at both, so a third setter is `x₁`; the return lemma gives
`k₂ ≤ k₁`, returning gives `k₃ ≥ k₁ + 1`, and `3k₃ ≤ 5k₁ + 1` gives `4k₃ + 1 ≤ 12k₁ − 3`, so `τ < 3/4`. A fourth setter
would be `x₂`, and the return lemma would give `k₃ ≤ k₂ ≤ k₁ < k₃`.

**Checks before the Lean** (`experiments/small_n/return_lemma_check_v1.py`): the return lemma held at every returning
setter tested (n=4: 32,127; n=5: 226; n=6: 3,987; n=7: 197; n=8: 2,178); at n=4, 240,000 subjects, no violation of the
`τ` bounds, the three-move limit, or the nearest runner's clearance. `n4_chain_map_v1.py`: setter patterns at n=4 are
only `b, c, bc, cb, cbc` (305,000 arrangements).

**What n = 3 and n = 4 used, and where n = 8 differs.**
1. *The nearest runner stays in its first clear window (reading ≤ n − 1).* Held at n = 3 (≤ 2) and n = 4 (< 3), and in
   every random sample for n = 5…8 (`nearest_window_by_n_v1.py`). It fails at n = 8 on item 36's arrangement
   `(410, 618, 788, 1252, 1452, 2298, 2416, 2747)` r4: at iterate 19 the nearest runner reads 7.33, is in the way, and
   sets the move to reading 9; the chain ends at iterate 29, reading 11.91. Not searched adversarially at n = 5, 6, 7.
2. *Setters alternate between two runners.* Forced at n = 4 (the nearest runner is clear and only two others exist).
   At n = 8 runners return many times (in the same trace `1495` sets moves at laps 1, 2, 4, 6, 11).
3. *The return lemma.* Holds at every `n`, but constrains only a return at the very next iterate; at n = 4 alternation
   made every return immediate.

The n = 8 argument needs what replaces 1 and 2: a statement about returns after several intervening moves, and about
the chain passing through the nearest runner's zones.

## 39. n = 5: no fixed chain length; termination reduced to a cap on the time — cap open  `[PROVED-LEAN (reduction, growth lemmas); EMPIRICAL (cap)]`

Added 2026-09-14.

**Why the n = 3, 4 method does not carry.** `experiments/small_n/n5_chain_map_v1.py`: chains reach 137 moves; 115
distinct setter patterns; length grows with the ratios (`n5_extremes_v1.py`: longest 7 / 12 / 28 as the largest ratio
goes from units to hundreds). A proof by a fixed number of cases, as at n = 4, is not available.

**What holds in the data.** (random, grid, near-AP and annealed; see the two scripts)
- The nearest runner is never in the way at any iterate.
- The largest final nearest reading found is `3.4444` (≈ `31/9`), at ratios `(2.2450, 3.3462, 9.000001)`: moves
  d2, c1, b1, d5, c2, d6, the last landing at `(6 + 1/5)/9`. Found by search; not shown to be the supremum.
- The product form of the return condition held on all 59,536 returns tested.
- Returns do not always come at the next lap (386 of 4,018 skip one or more; in the extremal chain d goes from lap 2
  to lap 5).

**Proved, every `n`** (`experiments/n8/MomentIterationN_v4.lean`, section `ChainBounds`; compiles, no `sorry`, axioms
`[propext, Classical.choice, Quot.sound]`):
- `exists_fixed_of_capped` — if every iterate from a positive start stays at or below `U`, some iterate is fixed.
- `move_growth` — a move set at lap `Q ≥ 1` from `t` lands before `(Q + 1/n)/(Q − 1/n) · t`.
- `return_growth` — a runner that left at its lap-`P` opening `t` is in the way at `t' > t` only if
  `t' > (P + 1 − 1/n)/(P + 1/n) · t`.
Together they give the multi-move return condition: `∏ (nQⱼ + 1)/(nQⱼ − 1) > (nP + n − 1)/(nP + 1)` over the intervening
setters; `P = 0` (the nearest runner) needs the product to exceed `n − 1`.

**Open at n = 5.** The cap: every iterate from `1/(5a)` stays below `4/(5a)` (the nearest runner reads below 4). With
`exists_fixed_of_capped` and `first_isolation_of_fixed`, the cap gives termination and the first isolation time.

**In the cascade's quantity.** The cap is `R = d_min/D_final < 4` at threshold `1/5` (the quantity of items 35–36).
Items 37–38 prove termination at orders 3 and 4 from setters, laps and readings; no such proof of the order-5 cap exists
yet.

## 40. n = 5, route 1 (chain accounting): word rules proved; long chains are resonances that barely move the time  `[PROVED-LEAN (W1, W2); VERIFIED / EMPIRICAL (structure)]`

Added 2026-09-14. Owner chose route 1 (setters, laps, growth budget only).

**Proved, every `n ≥ 4`** (`experiments/n8/MomentIterationN_v5.lean`, section `WordRules`; compiles, no `sorry`, axioms
`[propext, Classical.choice, Quot.sound]`):
- `no_return_after_faster` (W1) — a runner is not in the way straight after a move set by a runner at least as fast.
  So `x y x` needs `y` slower than `x`.
- `no_four_alternation` (W2) — no four consecutive moves `y z y z`.

**n = 5 structure** (nearest runner clear; others `b < c < d` by speed). W1 forbids `bcb`, `bdb`, `cdc`; W2 forbids
alternation. Checked on 158,681 arrangements (`experiments/small_n/n5_word_rules_v1.py`), no violation:
- gaps between `b`'s settings: `cd`, `dc`, `dcd` (each has exactly one `c`, so `b` and `c` settings alternate);
- gaps for `c`: `b`, `bd`, `db`, `dbd`; for `d`: `b`, `c`, `bc`, `cb`, `cbc`;
- chains without `b`: at most 3 moves (largest nearest reading 2.23).

**Long chains** (`n5_cycles_v1.py`, near-rational speed ratios): they are resonances. Example: 300 moves at
`c/b = 1.0022`, `d/b = 2.0021`, repeating `b(P) d(2P+1) c(P+1) d(2P+2)`; each cycle grows the time by ≈ `1 + 1/P`;
the chain ends with the nearest runner reading 1.38.

**Where the nearest reading gets large** (`n5_reading_vs_length_v1.py`, 159,801 arrangements): largest final
reading by chain length — 0–4 moves: 3.18; 5–9: 3.30; 10–14: 1.37; 15–29: ≤ 1.41; 30+: 1.51. By the largest lap any
setter used — laps ≤ 6: up to 3.30; 7–10: ≤ 2.36; 11–20: 2.09; 21–50: 1.78; > 50: 1.51.

**Proof shape suggested by the data (not yet derived).**
(A) *Resonance window.* A handoff at laps `(P, Q)` pins the reading of the next setter at the previous opening's scale
to `(5Q − 1, 5Q + 1)`; a handoff repeated with lap offset `c = Q − mP` fixes `ρ_y/ρ_x − m` to order `1/P`, so it can
repeat only while `P` stays within a bounded factor — bounding the growth a resonance can deliver at large laps.
(B) *Small laps.* The chains that approach the cap use laps ≤ 6 and fewer than 10 moves; a finite analysis of the
word rules with bounded laps.

## 41. The resonance window stated and tested; the setter pigeonhole and the nearest-reading recurrence in Lean, every `n`  `[PROVED-LEAN; VERIFIED; one hoped-for separation not found]`

Added 2026-09-14.

**Resonance window, exact** (`h = 1/n`, `r = ρ_y/ρ_x`; a handoff `x → y` at laps `(P, Q)` means `x`'s lap-`P` opening lies
in `y`'s lap-`Q` zone):
- A1 — handoff iff `Q − rP ∈ (h(r − 1), h(r + 1))`.
- A2 — a run of `k` handoffs with constant lap step `(p, q)` and `ε = r − q/p` has `(k − 1)·p·|ε| < 2h`.
- A3 — its growth `(P_k + h)/(P₁ + h) < 1 + 2h/(|ε|(P₁ + h))`.
- A4 — with `D = pQ₁ − qP₁`, unbounded growth needs `D ∈ [h(q − p), h(q + p)]` (the exact ratio `q/p` admits the handoff).

Test (`experiments/small_n/n5_resonance_products_v1.py`, 148,894 arrangements at n = 5): A1 on 89,737 handoffs, A2 and
A3 on 3,134 runs, no violation. **A4 does not separate:** admissible and non-admissible runs both reach growth 1.83,
because A3's bound is small only at large `P₁`. The resonance window bounds growth at large laps only.

**Recon for the product route** (same script):
- (D) Laps are not bounded by position: `Q_j/Q_1` reaches 34 within the first 10 moves (a slow runner sets at lap 1,
  a fast one later at lap 34); from position 10 on, `Q_j/Q_1 ≤ 1.6`. Laps follow speeds, not the index.
- (C) The setter-lap product `∏ (5Q + 1)/(5Q − 1)` reaches ≥ 4 in 733 chains (max 5.04: three lap-1 and two lap-2 moves)
  while every actual nearest reading stays below 4. The product uses only the lower end of each handoff interval; the
  cap needs the consistency of the speed ratios across different handoffs, not arithmetic on the product.

**Proved, every `n`** (`experiments/n8/MomentIterationN_v6.lean`, section `NearestState`; compiles, no errors or warnings,
no `sorry`, 38 of 38 axiom lines `[propext, Classical.choice, Quot.sound]`):
- `setter_repeat` — `k + 1` setters from a set of size `≤ k` include two equal ones at positions `i < j`.
- `nearest_clear_general` — while `1/n ≤ m·t ≤ 1 − 1/n` the nearest runner is clear.
- `repeat_within` — `card ds ≤ n − 1`, nearest clear at `n − 1` consecutive moving iterates: some other runner sets two
  of those moves.
- `nearest_reading_recurrence` — along the iteration from `1/(n·m)`: `m·t_N ≤ (1/n)·∏_{j<N} (Q_j + 1/n)/(Q_j − 1/n)`, each
  `Q_j ≥ 1` the lap of the setter of move `j` (or the move stays).
- `nearest_return_needs_product` — if the nearest runner is in the way at iterate `N`, that product exceeds `n − 1`.

## 42. Where the nearest runner leaves its first window; termination for two and three differences at every threshold `1/n` — in Lean  `[PROVED-LEAN; VERIFIED (n = 6 case by BSM); EMPIRICAL (searches)]`

Added 2026-09-14 (autonomous run; owner away).

**The nearest runner's first clear window across `n`** (`experiments/small_n/nearest_window_anneal_v1.py`, `_v2.py`,
40 annealing runs per `n`, plus `n6_nearest_leaves_v1.py`):
- n = 3, 4: never leaves (proved, items 37–38). n = 5: never leaves in any search (largest reading 3.3591 here;
  3.4444 in item 39).
- **n = 6: it leaves.** Speeds `1, 59733/25000, 299191/100000, 392283/100000, 516561/100000`: at iterate 9 the nearest
  runner reads 5.44, is in the way, and sets the move to reading 7; the chain ends at reading 8.3559. BSM (all zone
  endpoints, boundary points evaluated separately) gives the same first isolation time `1250000/897573`. 400,000 random
  arrangements at n = 6 found no such case; annealing found it.
- n = 6, 7, 8, 9: leaves in 2, 6, 3, 1 of 40 runs; largest readings 8.60, 9.04, 11.66, 10.66 — all below the second
  window's edge `2n − 1` in these searches.
So the first-window cap is a statement for n ≤ 5 only; from n = 6 a cap needs a later window.

**Chains for `k` differences at threshold `1/n`** (`chain_length_k_by_n_v1.py`, random + near-rational + annealing on
length; longest found): k = 2: 1 move at every n = 3…8; k = 3: ≤ 3 at every n = 4…11; k = 4: 7 (n=5), 5, 6, 5, 5, 4, 5, 4,
4, 5 (n=6…14); k = 5: 11 (n=6) falling to 4–5 by n = 16, 17. The nearest runner was never in the way when `k ≤ n − 2`.

**Proved** (`experiments/n8/MomentIterationN_v7.lean`, section `FewDifferences`; compiles, no errors or warnings, no
`sorry`, 41 of 41 axiom lines `[propext, Classical.choice, Quot.sound]`):
- `nearest_clear_first_moves` (every `n`) — each move multiplies the nearest reading by at most `(n + 1)/(n − 1)`, so
  the nearest runner is not in the way at iterate `j` whenever `((n + 1)/(n − 1))^j ≤ n − 1`.
- `two_diffs_stop_within_one_move` (every `n ≥ 3`) — at most two differences: the first iterate is fixed. (Generalises
  item 37; the nearest runner's reading after the move lies in `(1, n − 1]`, `nearest_clear_after_move_n`.)
- `three_diffs_stop_within_three_moves` (every `n ≥ 4`) — at most three differences: the third iterate is fixed.
  (n = 4 from item 38; n ≥ 5 from `three_diffs_stop_ge_five`: the nearest runner is clear at iterates 0–3 because
  `(3/2)³ ≤ n − 1`, setters alternate, and two return lemmas give `k₃ ≤ …` against `k₃ ≥ k₁ + 1`.)

## 43. The slowest-setter recursion: `k` differences stop within `2^(k−1) − 1` moves at every `n ≥ max(9, 2^(k−1))` — in Lean  `[PROVED-LEAN]`

Added 2026-09-15; replaces the item first written here on 2026-09-14 (a zone-width count, excised at the owner's
direction — see item 51 and `OBJECTION_LEDGER_v1.md` Part 7).

`experiments/n8/MomentIterationN_v14.lean`, section `SlowestRecursion` (compiles, no errors or warnings, no `sorry`, 63 of
63 axiom lines `[propext, Classical.choice, Quot.sound]`):
- `run_length_le` — a run of consecutive moves whose setters lie in a set of `r` runners has at most `2^r − 1` moves,
  whenever `2^r ≤ n`. Proof, by induction on `r`: the run's slowest setter `v` sets at most once in it — between two of
  its settings the moves are set by the other `≤ r − 1` runners, all faster than `v`, so that gap is a run of at most
  `2^(r−1) − 1` moves, and `word_no_slow_return_g` (from `no_return_after_few_faster`: a runner that left at lap `P` is
  not in the way after `≤ g` moves at laps `≥ P + 1` when `n ≥ 2g + 2`) excludes `v`'s return; so the run is two runs over
  `r − 1` runners and one setting of `v`.
- `factor_pow_le_exp_two` — `((n + 1)/(n − 1))^(n − 1) ≤ n − 1` for `n ≥ 9`, so the nearest runner is clear for the first
  `n − 1` moves (`nearest_clear_first_moves`).
- `stops_slowest_recursion` — at most `k` differences, `n ≥ 9`, `2^(k−1) ≤ n`: the iterate after `2^(k−1) − 1` moves from
  the bound is fixed. (`VersionB.slowest_recursion`: that iterate is lonely and first.)

Every step uses who sets each move, at which lap, and the return growth a lap-`P` return needs. It reaches no owner order
(`2^(n−2) ≤ n` fails for `n ≥ 5`).

## 44. n = 5: the relaxed chain as a linear program — supremum 31/9, and the boundary treatment is load-bearing  `[VERIFIED-COMPUTATION (bounded laps and length); CONJECTURE (supremum for all chains)]`

Added 2026-09-14 (autonomous run). `experiments/small_n/n5_relaxed_lp_v1.py`.

**Formulation.** Fix a setter word over `b, c, d` and its laps. With periods `u_x = 1/ρ_x` (nearest period 1,
`u_b ≥ u_c ≥ u_d`), every iterate is `t_j = (Q_j + 1/5)·u_{w_j}`, every handoff is `(Q_j − 1/5)·u_{w_j} < t_{j−1} < t_j`, and
the nearest runner is clear while `t_j ≤ 4/5`: all linear in `u`. So the largest reachable time for a word is an LP.
The relaxation allows any runner in the way to set the move (not only the latest opening). The true chain satisfies
every constraint of its own word, so for the words searched the LP value is at least the true chain's nearest reading.

**Boundary.** With the inequalities closed, the supremum is 4.125 (`dcbc`, laps 1, 1, 1, 2, ratios 16/9, 8/3, 4) — but
every handoff there sits exactly on a zone boundary, where BSM counts the runner clear (checked exactly). With strict
margins (`EPS = 1e-7`) the value falls to the true one. The closed chain is not a limit of strict chains.

**Result (strict).** Laps ≤ 8, length ≤ 9: 37,465 LPs; laps ≤ 12, length ≤ 11: 202,381 LPs. Both give supremum
**`t = 31/45`, nearest reading `31/9 ≈ 3.4444`**, at `dcbdcd`, laps `(2, 1, 1, 5, 2, 6)`, periods `(4/9, 8/27, 1/9)`
(ratios `9/4, 27/8, 9`) — the arrangement annealing found (item 39). Next values: 3.375 (`dcb`, laps 1,1,1), 3.3611.
By largest lap used: 3.375, 3.361, 3.259, 3.039, 3.361, 3.444, 3.143, 2.75, 2.959, 2.862, 2.947, 2.868 (laps 1…12) — not
decreasing: a fast runner at a large lap can ride on slow runners at lap 1. By length: 1.5, 2.25, 3.375, 2.889, 3.361,
3.444, 2.947, 2.333, 2.333, 1.933, 1.895 (1…11 moves).

**What a proof of the n = 5 cap needs beyond this.** A finite LP check covers bounded laps and length. The remainder
is the scale-separated case (some runner much faster than the others): its moves contribute little growth, but they
reset the word rules between the slower runners. A lemma bounding that contribution, plus the finite check, would
give the cap; neither is written.

## 45. No return across a few faster moves (every `n`), and the relaxed-chain supremum at n = 6  `[PROVED-LEAN; VERIFIED-COMPUTATION (bounded)]`

Added 2026-09-15 (autonomous run).

**Proved** (`experiments/n8/MomentIterationN_v9.lean`, section `FasterMoves`; compiles, no errors or warnings, no
`sorry`, 48 of 48 axiom lines `[propext, Classical.choice, Quot.sound]`):
- `faster_lap_ge` — after `x`'s lap-`P` opening, a runner at least as fast as `x` is in the way only at laps `≥ P + 1`.
- `lap_factor_antitone` — `(Q + 1/n)/(Q − 1/n)` decreases in `Q ≥ 1`.
- `bernoulli_upper` — `(1 + y)^g (1 − g·y) ≤ 1` for `y ≥ 0`, `g·y ≤ 1`.
- `factor_pow_le_return` — `((P + 1 + 1/n)/(P + 1 − 1/n))^g ≤ (P + 1 − 1/n)/(P + 1/n)` whenever `n ≥ 2g + 2`.
- `no_return_after_few_faster` — a runner that left at its lap-`P` opening is not in the way after `m ≤ g` further
  moves set at laps `≥ P + 1`, whenever `n ≥ 2g + 2`.
Use: at four differences the slowest runner's settings are separated by at most three faster moves (item 40's word
rules), so at `n = 8` it sets at most once. (Assembled in item 46.)

**Relaxed chains at general `n`** (`experiments/small_n/relaxed_lp_general_v1.py`, `_par_v1.py`: the nearest runner is
also allowed to set moves). Checks: n = 4 gives supremum reading 3 (`cbc`, laps 1, 1, 2; the proved bound of item 38);
n = 5 gives 31/9 (item 44), with the nearest runner never setting a move. **n = 6** (laps ≤ 6, length ≤ 14; 425,520
LPs): supremum reading **8.63636 ≈ 95/11**, at `edcbdecdbabdc`, laps `(1,1,1,1,2,3,2,3,2,1,3,5,4)` — the nearest runner
sets move 10 at lap 1 — above annealing's 8.6016 (item 42) and below the second window's edge 11. Bounded search only.

## 46. Four differences at every `n ≥ 8`: the iteration stops within seven moves — in Lean  `[PROVED-LEAN]`

Added 2026-09-15 (autonomous run). `experiments/n8/MomentIterationN_v10.lean`, section `FourDifferences` (compiles, no
errors or warnings, no `sorry`, 51 of 51 axiom lines `[propext, Classical.choice, Quot.sound]`).

- `word_no_alternation` — W2 stated on a word of iterates (`t`, setters `s`, laps `q`).
- `word_no_slow_return` — for `n ≥ 8`, a setter slowest among the setters between its two settings cannot return across
  at most three moves (from `no_return_after_few_faster` and `faster_lap_ge'`).
- `four_diffs_stop_ge_eight` — at most four differences, every `n ≥ 8`: the seventh iterate from `1/(n·a)` is fixed.
  Proof: the nearest runner is clear at iterates 0–7 (`((n + 1)/(n − 1))^7 ≤ (9/7)^7 ≤ n − 1`); an eighth move would make
  eight setters from three runners with adjacent setters distinct; the slowest of them, `v`, sets at most once (a gap of
  `≤ 3` moves is excluded by `word_no_slow_return`, a gap of `≥ 4` contains four moves by the other two runners, which
  alternate, excluded by `word_no_alternation`); so four consecutive setters avoid `v`, excluded again.

**The (differences, order) table after items 42, 46.** Proved termination: 2 differences at every `n ≥ 3`; 3 at every
`n ≥ 4`; 4 at every `n ≥ 8`. Open in the row `k = 4`: `n = 5, 6, 7`. The owner's orders (`k = n − 1`, `n ≥ 5`) are all
open.

## 47. Four differences at every `n ≥ 6`: the iteration stops within seven moves — in Lean  `[PROVED-LEAN]`

Added 2026-09-15 (autonomous run). `experiments/n8/MomentIterationN_v11.lean` (section `FourSixAlgebra`) and
`MomentIterationN_v12.lean` (section `FourDifferencesSix`); v12 compiles with no errors or warnings, no `sorry`, 58 of 58
axiom lines `[propext, Classical.choice, Quot.sound]`.

**Algebra (v11).**
- `three_move_bound` — for `n ≥ 6`, `P ≥ 0`, `2A ≥ (P + 1)(n − 2)`: `F(A)·F(P + 1)·F(A + 1) ≤ (P + 1 − 1/n)/(P + 1/n)`.
  Proof: reduce to `A = (P + 1)(n − 2)/2`; with `x = n − 6` the cleared difference times 4 is a polynomial of 27 monomials
  in `x, P`, every coefficient a positive integer (`three_move_poly`).
- `sorted_lap_prod` — `m` distinct laps `≥ 1` give a lap-factor product `≤ g(m) = ∏_{r=1}^{m} F(r)`.
- `g_balance` — `a + b ≤ 2m → g(a)·g(b) ≤ g(m)²`.

**Words (v12).**
- `word_no_slow_return_g` — the slowest setter does not return across `≤ g` moves when `n ≥ 2g + 2`.
- `word_no_slow_return_three` — for `n ≥ 6`, three moves `y z y` cannot carry the slowest setter back: `y` returns across
  `z`, so the return lemma gives `2·lap(y) ≥ (P + 1)(n − 2)`, and `three_move_bound` caps the growth below what `v`'s
  return needs.
- `g_count_bound` — `g(1)·g(3)² ≤ n − 1` for `n ≥ 6` (≤ 7/5 · (1729/935)² ≈ 4.787 ≤ 5).

**`four_diffs_stop_ge_six`.** At most four differences, every `n ≥ 6`: the seventh iterate from `1/(n·a)` is fixed.
1. On any prefix of the chain whose setters avoid the nearest runner, the slowest setter sets at most once (gaps of 2–3
   moves: `g = 2`; gap of 4: the three-move bound; gaps ≥ 5: four moves by two runners alternate, W2).
2. The nearest runner is clear at iterates 0–7 (strong induction): `a·t_j ≤ (1/n)∏ F(lap)`; split the product by runner
   (`prod_fiberwise`), bound each runner by `g(its count)` (sorted laps), the slowest runner's count is ≤ 1 and the other
   two counts sum to ≤ 6, so the product is ≤ `g(1)·g(3)² ≤ n − 1`.
3. Eight moves would put the slowest setter at most once among eight positions, leaving four consecutive setters that
   alternate — W2.

**The table now.** Proved termination: 2 differences at every `n ≥ 3`; 3 at every `n ≥ 4`; **4 at every `n ≥ 6`**; `k` at
every `n ≥ max(9, 2^(k−1))` (item 43). In the row `k = 4` only `n = 5` is open — the owner's order 5 and the cap of items
39, 44.

## 48. Version B stated for the proved cases — in Lean  `[PROVED-LEAN]`

Added 2026-09-15 (autonomous run). `experiments/n8/MomentIterationN_v13.lean`, section `VersionB` (compiles, no errors or
warnings, no `sorry`, all axiom lines `[propext, Classical.choice, Quot.sound]`). Each theorem says: for every arrangement
in the class, an explicit iterate of the move from the bound `1/(n·m)` is lonely and no positive lonely time precedes it
("terminates with the correct answer"):
- `two_diffs` (every `n ≥ 3`, iterate 1), `three_diffs` (every `n ≥ 4`, iterate 3), `four_diffs` (every `n ≥ 6`,
  iterate 7), `slowest_recursion` (every `n ≥ max(9, 2^(k−1))`, iterate `2^(k−1) − 1`; in v14), `order_three` (n = 3),
  `order_four` (n = 4, with `a·T < 3/4`).
Consolidated status: `docs/n8/SMALL_N_TERMINATION_STATUS_v5.md`.

## 49. Corrections to items 44–48 and the status document, from an independent audit  `[CORRECTION]`

Added 2026-09-15. A memory-drafting audit read the status document, items 37–48, `MomentIterationN_v13.lean` and its
output, and recompiled the file (exit 0, 64 axiom lines identical to the checked-in output; all 51 theorem names cited in
the documents exist). It found no claim the Lean file contradicts, and four defects in the prose:
1. Items 44–45 and status v2 §3 describe the relaxed-chain LP results as if exact. The LPs are floating-point
   (`scipy linprog`, HiGHS) with `EPS = 1e-7`; `31/9` and `95/11` are rationals recognised from float optima over bounded
   searches (item 45's "≈ 95/11" is the accurate form).
2. The module docstring of `MomentIterationN_v13.lean` (inherited from v6) still speaks of `1/8` and says termination is
   not stated. The file is left unchanged (its SHA-256 is recorded in the project memory); the documents now say to read
   the theorem statements.
3. Item 48 pointed to status v1; the current document is `docs/n8/SMALL_N_TERMINATION_STATUS_v5.md`.
4. Status v2 §4 asserted, without an artifact, a common cause for the two n = 5 failures. That assertion used a
   zone-width count and has been excised (item 51).

## 50. Drift audit of items 37–49; the n = 5 cap is `R < 4`  `[AUDIT]`

Added 2026-09-15 at the owner's request. Verdicts piece by piece in `OBJECTION_LEDGER_v1.md` Part 7. Framework: the
iteration, zones, setters, laps, return lemma, W1/W2, nearest reading, resonance window, Version B. Imports found:
four; all excised and replaced (item 51). Current status document: `docs/n8/SMALL_N_TERMINATION_STATUS_v5.md`. The cap in the cascade's quantity: `R = d_min/D_final < 4` at threshold `1/5`.

## 51. Imports excised and replaced  `[EXCISION]`

Added 2026-09-15. Owner: *"Not just noted they need to be excised and replaced."* Each import found in item 50's audit has
been removed from the current work and replaced by a statement in the framework's objects:

| import | excised from | replaced by |
|---|---|---|
| zone-width count (`AdvanceBudget`: "any `k` at every `n > 2k`") | `MomentIterationN_v14.lean` (section and `VersionB.budget` removed); item 43 rewritten; items 46–48 tables; status v5 | `SlowestRecursion.stops_slowest_recursion`: `k` differences stop within `2^(k−1) − 1` moves at every `n ≥ max(9, 2^(k−1))`, proved from setters, laps and the return growth (item 43) |
| a zone-width "hypothesis" for the n = 5 failures | status document §4; item 49 | the handoffs themselves (which runner sets, at which lap, the reading it hands on) named as what has to be analysed |
| the four-speed relabel of order 5 | item 39 | the cap as `R = d_min/D_final < 4` |
| covering justification of the LP bound | item 44 | the true chain satisfies its word's constraints, so the LP value bounds its reading from above for the words searched |

Earlier files that still contain the excised material, kept as the version history (not current): `MomentIterationN_v8`–
`v13.lean`, `SMALL_N_TERMINATION_STATUS_v1`–`v4.md`. The owner decides whether to delete them.

## 52. Why `R` stays below 4 at order 5 — the cascade, the own-AP instants and the isolation positions  `[DERIVED (1–3); VERIFIED (4–7); OPEN (the bound)]`

Added 2026-09-15 at the owner's request. Subject with nearest difference `m = d_min`; the other readings at scale `m` are
`s = a + e` (AP index `a`, deviation `e`, `|e| ≤ 1/2`). The cascade: `R_0 = 1`; at scale `D_j = m/R_j` the readings are
`s·R_j`; a runner is in the way iff `s·R_j` is within 1 of `5N`; `R_{j+1}` is the largest `(5N + 1)/s` over those runners;
`R = R_final = d_min/D_final`. The nearest runner's own reading is `R`, so the cap is `R < 4`.
Scripts: `experiments/small_n/n5_cascade_R_v1.py`, `n5_ap_instants_v1.py`, `n5_instant_runners_v1.py`,
`n5_isolation_positions_v1.py`, `n5_exact_ap_v1.py`, `n5_resonant_search_v1.py`.

**1. `R` is a product of step factors (derived).** If step `j` is set at lap `N_j` by a runner whose reading exceeds the
zone entry `5N_j − 1` by `δ_j ∈ (0, 2)`, then `R_{j+1}/R_j = (5N_j + 1)/(5N_j − 1 + δ_j)`, so
`R = ∏_j (5N_j + 1)/(5N_j − 1 + δ_j)`. Each factor is below `(5N + 1)/(5N − 1)`: `3/2` at lap 1, `11/9` at lap 2, `8/7` at
lap 3. (In Lean: `ChainBounds.move_growth`, `NearestState.nearest_reading_recurrence`.)

**2. The lap-1 ladder (derived).** Each runner's reading passes `5` once, so each runner sets at most one lap-1 step. A
cascade made only of lap-1 steps has `R < (3/2)³ = 27/8`. The limit is approached by readings `4, 8/3, 16/9` (AP slots 4,
3, 2 with deviations `0, −1/3, −2/9`): each runner in turn reads just above 4, and `R` goes `1 → 3/2 → 9/4 → 27/8`
(instance `(1.7799, 2.6686, 4.0012)`: `R = 3.37098`). Passing `27/8` needs steps at laps `≥ 2`, whose factors are at most
`11/9`, and whose entries are fixed by the reading ratios the earlier handoffs set: `s_y/s_x = (5N_y − 1 + δ_y)/(5N_x + 1)`.
The largest found, `31/9`, is `d` at laps 2, 5, 6, `c` at 1, 2, `b` at 1, with readings `≈ (2.24, 3.28, 9)`: AP slots 2, 3,
and 4 at the next grid point (index 9), slot 4 exact.

**3. Exact AP: only slot-sharers move the cascade (derived; checked).** With `e = 0` every reading is an integer `a`. At
`R = 1` a runner with `a ≢ 0 (mod 5)` sits at least one fifth from the subject, so it is not in the way. Hence **with exact
AP readings and no slot-sharer, `R = 1`** — the AP reference is isolated at its own bound (all 9,139 index triples in
`2…40`). With a slot-sharer (`a ≡ 0`), `R ≤ 11/5` on the same triples. Everything above that comes from deviations.

**4. The own-AP instants (derived from the residue rule; verified).** To reach `R = 4` the cascade must pass the own-AP
instants `R = 2` and `R = 3`, each with some runner in the way. By the drift line, at instant `n'` a runner sits at
`n'a + n'e` (mod 5), in the way iff that is within 1 of a multiple of 5. With `|e| ≤ 1/2` this allows exactly:
- at `R = 2`: slot 0 with `|2e| < 1`; slot 3 with `e < 0`; slot 2 with `e > 0`;
- at `R = 3`: slot 0 with `|3e| < 1`; slot 2 with `e < 0`; slot 3 with `e > 0`; slot 4 with `e < −1/3`; slot 1 with `e > 1/3`.
On 13,592 annealed arrangements with `R > 3`, every in-way runner at those instants falls in these classes (slot 1 does
not occur). Only 63 of 200,000 uniform arrangements pass both instants.

**5. A tempting pigeonhole fails, and why (verified).** "A different runner in the way at each of `R = 1, 2, 3`" fails in
1,606 of the 13,592: a slot-sharer with small deviation is in the way at every own-AP instant it passes (in 1,810
arrangements one runner is in the way at all three). This is the framework's slot-sharer lemma
(`MomentIterationN.not_lonely_at_ap_instant_of_sharer`) with a deviation.

**6. Where the predictor isolates (verified).** At `R_final`, in all 13,592 arrangements with `R > 3`: exactly one other
runner is at `+1/5` (the last setter, exactly at its opening), the other two are strictly inside `[1, 4]` fifths, none is
at `−1/5`, and the nearest runner is at `R_final` fifths.

**7. Large AP gaps (verified, search).** At gap `K` with indices `(1, 1, 2)` and tuned deviations: `R ≈ 1.54` (`K ≈ 100`,
60 moves), `≈ 1.50` (`K ≈ 1000`, 565 moves). Long cascades at large gaps barely raise `R`.

**What is not shown.** A bound `R < 4` for every arrangement. Items 1–4 reduce it to the stretches between own-AP instants:
how the in-way runner at `R = 2` (resp. `3`) can hand on across `(2, 3)` and `(3, 4)` given its slot, the sign of its
deviation and the step factors of item 1 — and the large-gap regime of item 7.

**For order 8.** (a) Item 3's argument carries over (a non-zero residue sits at least one eighth away), and it was run at
order 8: with exact AP readings and no index `≡ 0 (mod 8)`, `R = 1` on 7,950 random seven-reading arrangements from
`2…60`; with a slot-sharer, `R ≤ 5/2` on 12,050 (`experiments/small_n/n8_exact_ap_v1.py`). (b) Item 5's
failure will recur: slot-sharers with small deviation cross several own-AP instants, so an order-8 argument cannot count
instants against runners. (c) The lap-1 ladder at order 8 gives `(9/7)^7 ≈ 5.81 < 7` for lap-1-only cascades, but the
largest `R` found at order 8 is `≈ 11.96`, so order 8 needs later-lap steps and nearest-runner steps far more than order
5 does; item 1's product form is where to measure them.

---

## 53. Applied in v8 — `MANUSCRIPT_v8_2.md`  `[APPLIED; nothing removed from this list]`

Added 2026-09-15. v7 unfrozen per `V8_PLAN_v2` and rulings Q1–Q4. Drafts `MANUSCRIPT_v8.md` → `_v8_1.md` → `_v8_2.md`
(v7 untouched). What each item became is in v8_2 Appendix B; the items stay here as the record.

- **Structure.** Three outcomes in the framework's objects: Construction `[PROVED]`, Localisation `[PROVED]`, Existence
  `[OPEN]` (§6.4–6.7). The conjecture is named once, in §9: *"If Existence held for every runner, the conjecture at eight
  runners would follow."* v7 §9 "is the Lonely Runner Conjecture itself" removed. v7 §6 → Appendix A; ledger → Appendix C.
- **Items applied:** 1–3 (no window; §1.3 states the cascade), 8 (§8.1 fixes), 10–13 (frames, exactness), 14 (interior-point
  cells; grid row; gate check [4] names only), 17–23 (dead lattice, spread-live scale, 4.9 relation, firewall
  qualifications), 24 (stated open, §2.3), 25–36 (cascade, openings, setters, recursion, drift, residue rule, `R`, depth 29),
  37–49 and 52 (§8.2, order 5 open, order 8 exact AP), 51 (no excised import cited). `LOST_FUNCTIONS_v1` §§A–I restored.
- **Checks.** Every cited Lean declaration exists and matches its v8 statement; 26 declarations outside the gates checked by
  `experiments/n8/v8_axiom_check_v1.lean` (`.out`, all within the three standard axioms). Compile-diff run twice: 25 losses
  and 8 grade/caveat defects in v8 → all 33 resolved in v8_1; four residual defects (v7 regime clause, seven ledger figures,
  a mis-labelled mapping row, a declaration count) fixed in v8_2.
- **Corrections found while writing** (now in v8_2): cascade depth found is 29 (not 30); n = 6 nearest reading 8.3559; the
  24,310 exhaustive count is for 4.9's contrapositive; the pinned-frame caveat is kept, not reversed; Proposition 3.3's
  conclusion keeps the baseline alternative once the window is gone; W1 is a statement about the earliest lonely instant only.
- **Open, carried:** Existence at order 8; the gap-frame obligation (§4.6); item 24's fit step; order-5 cap `R < 4`;
  `k = 5` at `n = 6…15`. **Owner decisions pending:** whether v8_2 is promoted as the manuscript of record; deletion of history
  files (v8–v13 Lean experiments, status v1–v4).

**Addendum to item 53 (2026-09-15).** Owner decision on history files: archive, never delete. Moved with `git mv` to
`archive/n8_history/` with original paths kept: `experiments/n8/MomentIterationN_v8.lean` … `_v13.lean` and
`docs/n8/SMALL_N_TERMINATION_STATUS_v1.md` … `_v4.md`. References above use the original paths. Further work is tracked in
`V8_REVISION_LIST_v1.md`.
