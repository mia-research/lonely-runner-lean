# Order 8 (n = 8 Lonely Runner): standalone transfer summary

**T. Palelei.** v1, 2026-11-11. Written for a reader with no access to the working corpus (931 documents, an 18,668-line running log E1 to E847, 3,203 Lean files in one tree and several hundred in another). Read this first, then `N8_LEAN_KERNEL_AND_GAPS_v1.md`. Documents not included are listed in `N8_APPENDIX_ON_REQUEST_v1.md`.

Grades: **[L]** Lean, standard axioms only; **[T n/N]** exact machine test on a stated finite population; **[P]** hand proof; **[OBS]** observation; **[OWED]** not proved. Exact fractions are facts; decimals are steering only.

**Status in one paragraph.** The conjecture at eight runners is not proved. Orders 3 to 7 are proved in Lean for all real speeds in this framework. For order 8 there is one Lean theorem, `filterAssembly`, that derives the conjecture from named hypotheses. Behind those hypotheses sits a large exact computation that sorts every arrangement whose readings are at most 17 into 74,613 integer boxes and settles each (0 left open), and certifies readings up to 95 by dyadic boxes. What is missing is (a) the passage from those computations to statements over the reals in Lean, and (b) a proof for readings beyond the computed range (the tail). Item (b) is open mathematics; item (a) is partly routine and partly needs one covering lemma.

---

## 1. The problem and the author's framework

Eight runners on a unit circle with distinct constant positive speeds. Claim: every runner is at some time at circular distance at least `1/8` from all the others.

The framework treats **one runner at a time** (the subject). No runner is held at speed 0; only the differences of speed from the subject enter.

| object | meaning |
|---|---|
| **disparity** `d_j` | `|v_j − v_subject|`, seven of them |
| **`d_min`** | the least disparity (a speed-neighbour) |
| **reading** `ρ_j = d_j/d_min ≥ 1` | one reading is 1; sorted `ρ₁ = 1 ≤ ρ₂ ≤ … ≤ ρ₇` |
| **in the way / clear** at `t` | runner within strictly less than `1/8` of the subject / not |
| **bound** | `t₀ = 1/(8·d_min)`, the earliest possible isolation |
| **`R`** | time in units of the bound, `t = R/(8·d_min)`; the bound is `R = 1` |
| **zone** of reading `ρ`, lap `j` | the open interval `R ∈ ((8j−1)/ρ, (8j+1)/ρ)` where `ρ` is in the way |
| **window** `W_j = [8j+1, 8j+7]` | where the reading 1 is clear; `W₀ = [1,7]`, `W₁ = [9,15]` |
| **opening** | an instant at which a runner is exactly `1/8` past a lap line |
| **move** | go to the **largest** next opening among the runners in the way; stay if none |
| **cascade** | the sequence of moves from the bound; deterministic, no search |
| **landing** | the cascade's fixed point; **setter/opener**: the runner whose opening it is |
| **AP** | the arithmetic progression of speeds; **grid**: speeds `v₀ + idx_j·D` with the `idx_j` a complete residue system mod 8 |

**Proved about the cascade [L].** A fixed point is lonely and is the *first* lonely instant. Every lonely instant is at or after every cascade step. So the cascade lands if and only if the subject has an isolation. On millions of arrangements the cascade has never failed to land; it is treated as an oracle, and the work is to explain why it must land.

**Existence at the reference [L].** An AP, and any grid, is globally isolated (all eight runners at once) at the instants `a/(8D)`, `a` coprime to 8: four instants per period, the `φ(8)` law.

**The author's thesis (the direction to carry forward).** In the owner's words (log E270, E282, E293, E768, E804):

> "We are trying to prove n=8 by showing there are only finite amounts of arrangements and those arrangements can be view in terms of ap/grid ... all arrangements achieve individual isolation by moving the isolation points depending on the arrangement of the speeds."
>
> "while there are continuous ability of speeds to change there are only a finite set of arrangements of runners ... runner 2's speed can not increase more than runner 3's speed without becoming runner 3. The scale invariance ... and then the fact grid goes on forever."
>
> "existence is already proven by the phi(n) law/grid global isolation ... Move the speed and you move the isolation point from the global ideal to a local isolation event."
>
> "The structure that contradicts it is two runners at the same speed."
>
> "We have a filter of arbitrary arrangements that sorts them into one of 14 types, there are no exceptions. Once every tested arrangement is one of 14 you can then look to why that is true for all."

So the programme has two halves: (i) the cascade sorts arbitrary arrangements into a finite list of types; (ii) each type's isolation is easy. Half (ii) is in good shape. Half (i), **arbitrary to finite**, is the hard part and is where section 4 concentrates.

**Working rules the owner enforces** (they shaped what was and was not tried):
- State results in the framework's objects. Density, measure, covering-as-existence, move budgets, uniform caps and "first lap" bounds are regarded as imports from other frameworks. Counting and covering are allowed as *tools* inside a proof if tagged provisional.
- The cascade has no exceptions. An exception found is an exception to *our description*; each must be understood (what sets it apart, what forces it, same mechanism or not) before moving on.
- Exact arithmetic only. Lower orders may be used only in their re-proved framework form.
- Do not label steps hard or easy; report what was verified.

---

## 2. What is settled

**Orders 3 to 7, all real speeds [L]**, in the nested repository (`LRC/Spec/`): `existenceAtN_seven` and predecessors, with a shared integer-to-real transfer. Consequence at order 8: a subject with at most six distinct disparities is done.

**Order 8, special classes [L unless marked]:**
- All disparities within `[d_min, 7·d_min]`: lands at the bound (`ratio_lands`). Spread in `(7, 9]`: 105 lap-assignment cones, each lonely at a named instant (`BandCover.band_lonely`).
- Whole-number readings with none divisible by 8: lonely at `1/8` (`IntegerGridN.lonely8_of_no_multiple_of_eight`). Exactly one multiple of 8, not divisible by 32: lonely (`lonely_of_not_dvd32`).
- The AP with **one** runner moved to any speed, every subject (`s1_all_landing`); **two** movers, subject fixed (37 frozen sets); three movers above the least frozen reading; every arrangement within relative radius `1/6` of the AP (`ap_nbhd_lands_12`), via a chamber complex cut by walls `ρ_b/ρ_a = (8k±1)/(8m±1)`.
- 63 six-reading "cores" with any real seventh reading.
- The **view lemmas**: every arrangement at every scale has exactly one grid index and one deviation in `[−½, ½)` per reading (`every_arrangement_viewed`); the subject is lonely at `t` iff every reading's status is ok in the view at scale `1/(8t)` (residue 2 to 6: ok; residue 1 with deviation `≥ 0`; residue 7 with deviation `≤ 0`; residue 0 never) (`lonelyAt_iff_view`); each cascade move is a change of view to a smaller scale (`move_view`); the landing is the least class-1 instant at which every reading is good (`isFirst_iff_least_goodM`).

**The outcome catalogue (E325, E369, E802).** Every cascade outcome observed carries one of 14 labels: no move; opener of rank 2 to 7 with landing in `W₀`; opener of rank 1 to 7 with landing in `W₁`. Twelve are realised; two are empty by proof. Checked on 52,000 sampled arrangements, 271,361 members of an exhaustive tree, and every later population. **[L]**: the 14 labels are complete *exactly when* every arrangement lands with `R < 17`. So "14 types" and "lands below 17" are one statement, and that statement contains existence; it is order 8 with a stated place, not a reduction of it.

---

## 3. The current route: the filter assembly

**Sorting method (E802).** Scale by the least reading. If the six other readings' zones do not cover `W₀ = [1,7]`, the landing is the left end of the first clear piece of `W₀`. If they do cover it (a **carve**), look at `W₁ = [9,15]`. The claim is that `W₀` and `W₁` are never both carved.

**In Lean [L]:** exhibit any `s ∈ [1,7] ∪ [9,15]` clear for all readings, and the cascade lands below 17; and `filterAssembly` assembles three regions by the largest reading `ρ₇`.

**Inside, `ρ₇ ≤ 17`.** Round the six non-least readings to nearest integers: 74,613 sorted tuples ("boxes"). Exact computation, 0 open:

| class | boxes | how it is settled |
|---|---|---|
| fixed clear point | 62,000 | one rational `R₀ ∈ [1,7]` clear on the whole box; closed form: no rounded reading in `{7,8,9,15,16,17}` gives `R₀ = 1` (8,008 boxes, [L]), plus 36 gap-edge forms |
| subdivision tree | 12,540 | no carve anywhere on the box; leaf certificates from a closed 90-type envelope; one fixpoint algorithm replaces 10,211 trees; 2,329 held by trees only |
| one-sided chain boxes | 68 | a carve of `W₀` is possible; then no chain can cover `W₁` |
| two-sided chain boxes | 5 | both chains exist separately; every pair conflicts, [T 2,522,259/0] |

The five two-sided boxes are `(1,2,3,4,5,6,7)` (the AP's own box), `(1,2,3,4,5,6,8)`, `(1,3,4,4,5,6,7)`, `(1,3,4,5,5,6,8)`, `(1,3,4,5,6,7,8)`. Largest landing found anywhere: `26433/2209 ≈ 11.97` (the owner had long suspected `R = 12` is the maximum).

**Band and tail, `ρ₇ > 17`.** No carve of `[1,7]` for `ρ₇ ∈ [17,23) ∪ [25,95)`, by dyadic-box certificates. For `ρ₇ ∈ (23,25)` carves exist ("X24") and all land in `W₁`. Beyond 95: nothing computed; this is the tail.

**The mechanism that recurs at every scale.** A carve is a chain of zones; consecutive zones `(p, j_p) → (q, j_q)` overlap strictly iff `ρ_q/ρ_p > (8j_q − 1)/(8j_p + 1)`. Chains are therefore systems of ratio bounds with numerators `≡ ±1 (mod 8)`, and a system is infeasible exactly when some cycle of bounds has product `≥ 1`. The two-sided box conflicts, the tie planes of the band, and the death of every near-carve chain type in the tail are all this one fact.

**Cross-order check.** The same instrument at threshold `1/k`: no chain boxes for `k ≤ 5`; 8 at `k = 6`; 24 at `k = 7`; 73 at `k = 8`; 186 at `k = 9`. Two-sided boxes occur only at `k = 8`.

The exact remaining statement, the defects found in the hypotheses as currently written, and the gap list G1 to G6 are in `N8_LEAN_KERNEL_AND_GAPS_v1.md` sections 4 and 5.

---

## 4. Arbitrary to finite: what has been tried, and where it stands

This is the half the owner regards as the heart. Stated as a problem: *give a finite set of types, defined from the speeds alone, such that every arrangement has a type and each type names its isolation.* The log's own verdict at several points (E434, E444, E472) is that the finite set had not yet been identified. What follows is every notion of "type" tried, in the order the evidence came.

**Notions whose count grows without bound (do not retry as stated).**
- Cascade paths, rank words, status words, setter words, link words, chain types: every encoding grows with the height of the readings (for example rank words 18, 48, 120, 355, 608, 853 for heights 10 to 20; link words 206, 474, 2,241 at heights 16, 20, 24).
- Polyhedral cells of the cascade tree: 19,679 / 293,333 / 1,878,060 regions for `ρ₇ ≤ 9 / 17 / 25`.
- Residue-and-sign keys: (residue mod 8, sign of deviation) decides loneliness at `R = 1` exactly [L], but does not determine the path; the missing coordinate is the size of the deviation.
- Lap labels: the opener's lap is not uniformly bounded (largest lap 2, 13, 67 at spreads 8, 50, 400) while `R` stays small. **The uniform quantity is `R`, not the lap or the move count.**
- Classes with a free real unit: equivalent to isolation itself [L], so not types.
- Lists of whole-number cores: the list lengthens with the search height.

**From the first month (E1 to E170), results that still stand.**
- Exhaustive exact box enumerations: every subject with `d_max ≤ 24·d_min` has its isolation at some `R ≤ 15` (E49 to E66, slabs up to `S ∈ [23,24]`, not in Lean). This is the earliest form of "lands below 17" and agrees with the later 74,613-box result.
- Spread `(7,9]` by 105 lap-assignment cones with Farkas certificates (E124), later in Lean. Strips `[9,10]` to `[16,17]` need 131, 168, 255, 308, 337, 399, 754, 762 cones: the count grows with the spread, so strip-by-strip cones cannot close unbounded spread.
- Exactly three tight arrangements up to scale (lonely only at isolated instants): readings `{1,…,7}`, `{1,2,3,4,5,7,12}`, `{1,4,5,6,7,11,13}` (exhaustive to height 40).
- `EndRunnerN.lonelyRunnerAt8_of_slowest` [L]: for whole-number arrangements only the slowest runner remains. The off-lattice rule [L]: a set with a reading that is not a multiple of the gcd of the others reduces to order 7.
- The cascade's chain has exactly three move types (sweep step, bridge up, bridge down), forced by ordering (`SweepBridgeN`) [L].
- Complete grids, the AP and the doubled-slot family each have a proved neighbourhood in which every runner's instant is named.
- A single spread-free covering statement `Cover8 M` (the bound, or a grid class through a reading with step at least `d_min/M`): `lonelyRunnerAt8_of_cover8` [L], `Cover8 M` owed; `Cover8 2` leaves none uncovered on every population tested. With a uniform `M` it carries a cap; without one it restates loneliness (E215, E217).
- Type counts by landing: 57,802 at readings `≤ 24`, 93,126 at `≤ 28`. "Every arrangement has a type" was recorded then as the conjecture itself, with types up to relocation not yet defined operationally.

**Notions that are finite and survive.**
- **The 14 outcome labels** (opener rank, window). Finite by construction; complete iff landing below 17.
- **The neighbour pair at the isolation**: at most 42 per subject (which runner sits on the `1/8` edge, which is the other neighbour). All 42 are realised. An isolation only constrains the two neighbours; the other five lie anywhere in the remaining `6/8` (the owner's point, E289).
- **Twelve link kinds**: every link of every cascade walk is one of at most twelve kinds at any height [P].
- **63 wall kinds**: every wall across which a cascade path changes is `ρ_b/ρ_a = (8k∓1)/(8m±1)`, 21 pairs times 3 edge types. The path is constant between walls [OBS exact on a grid; P on two lines].
- **The nearest-integer box with `ρ₇ ≤ 17`**: 74,613, with four certificate classes. This is the first finite set for which *every* member has been settled.

**What makes arbitrary finite, on the evidence.** Three reductions are proved: order (speeds cannot cross), scale (`dev_scale`: a common factor changes nothing), and translation (only differences from the subject enter). What remains unbounded is the top readings. The data say the middle readings of any carve are confined to a fixed box (`ρ₂ … ρ₆` below about `4.82, 5.28, 6.21, 7.10, 8.15`, [OBS]) and only the top reading runs off; and a carve needs the last reading to satisfy `7ρ < 8j+1` and the first to straddle 1. So the conjectured finiteness statement, in the framework's terms, is:

> **For six sorted readings with `ρ₇ ≥ 25`, the zones do not cover `[1,7]`.**

With it, every arrangement either has `ρ₇ < 25` (a bounded region, already computed exhaustively, 14 labels) or lands in `W₀`. This is the precise form of the owner's "`1…7, 10¹⁰` is not a new arrangement from `1…7, 17`" (E270): a far runner's zones are too thin to complete a carve that the near runners leave open. It is gap G5.

**Routes to that statement, with their state.**
1. *Strip classes.* `ρ₇` must lie in a strip `(8k−1, 8k+1)` to cover `R = 1`. Strips `k = 2, 3` carve, with exact tops `511/31` and `86989/3565`. Strips `k ≥ 4` are excluded computationally to 95. Owed: a product cap below `(8k−1)/7` for every `k ≥ 4`, which needs the middle-reading bound proved.
2. *One-dimensional lemma.* Reading 7's zones have width `2/ρ₇`, so it can only close components of the clear set of readings 2 to 6 that are shorter than that. Owed: a lower bound on the longest clear component of five readings inside `[1,7]`.
3. *Block gap.* The longest stretch with no joint clear instant for `m` readings, in units of the slowest: proved `≤ 2m/(b₁(4−m))` for `m ≤ 3`; open for `m = 4, 5, 6`.
4. *Deformation from the AP/grid* (the owner's preferred picture). Proved to relative radius `1/6`; the chamber count grows with radius (3 leaves at `1/64` to 201 at `1/6`, 1,130 at `1/4`), and "every arrangement is within `d/8` of a grid" is false as stated [L] (true exactly when no two speeds agree mod 8, on the sample). The owner's reply (E774) is that larger deformations are restatements at another scale; a proof of that restatement is owed and would be the direct form of the thesis.
5. *Displacement at a pinned pair.* When a moving reading closes the landing, the next landing is the first isolation that is not the same wall [L]. Owed: that the relocation is bounded; by E772 this is equivalent to isolation of the limit arrangement, and the owner's argument for it is that unbounded relocation would force two runners to one speed.

**Older reductions on record** (each real, none assembled with the others):
- To whole-number sets failing 22 arithmetic rules (`EightResidual`; `lonelyRunnerAt8_iff_residual` [L] both directions; no member has been found by search, only constructed controls).
- The one-multiple-of-8 branch (residual: the multiple divisible by 32).
- A block skeleton with five owed premises (fast blocks of size 3 to 6 separated by a factor 9, and the unseparated case); a path route owing `WindowBound`.
- The real-to-whole-number transfer and the residual chain in `Fresh/` [L modulo the owed end]: `ResidualRest6 → 5 → 4 → 3 → 2 → ResidualRest → ResidualLonely8 → NatLonely8 → ExistenceAtN 8 → Isolation`. Each arrow removes a proved class (residue cases, gate chain, 368 fixed instants `R = 8a/b`, window chain, 53 cores, flank band). The whole-number sets left after all classes numbered 0, 1, 5, 11, 19 at heights 28, 32, 36, 40, 44, and each stage's classes were fitted to the previous left-over, so these counts are not evidence of finiteness.
- The partition theorems (`typesProvedUp_or_admissible`, `shapeUp_or_admissible`) [L]: every ordered arrangement is in a proved class or in a named remainder. Nothing is proved about the remainder being empty or finite.
- A general landing law near any baseline (`landing_cert`, `LDC`) [L, covering provisional]: within a radius of a baseline arrangement the first isolation is the largest exit of the baseline's first surviving lonely component. The radius depends on the baseline; no uniform radius is known.
- The two-block template (`twoBlock_iff`, nine regions) and gap-edge cells for six families. Several equivalences were proved that turned out to restate the conjecture (`Compat`, transversal, `LeftClosed`, bounded relocation, `Cover8` without a bound). They are useful as dictionaries and are not progress by themselves.

---

## 5. Suggested order of attack for a fresh reader

1. Rebuild the instrument (section 6) and reproduce the calibrators. Half a day.
2. Fix the three hypothesis-shape defects (kernel document, section 4) so that the Lean statement carries the box data and admits the X24 family.
3. Prove the **exact cover criterion** in Lean (a compact interval covered by open zones has a strictly overlapping chain). It is the one lemma that unlocks G3 and the Lean form of every chain argument.
4. Attack the tail statement above. Everything else is finite.
5. Decide whether to keep "below 17" for the tail or relax it (G6).

---

## 6. Ingredients to rebuild (no scripts are needed from the corpus)

All in exact rationals (`fractions.Fraction`).

- **Clear test.** `ρ` is clear at `R` iff `ρR mod 8 ∈ [1,7]`.
- **Cascade.** Start `R = 1`. At `R`, for each reading in the way compute its zone's exit `(8j+1)/ρ` with `j = round(ρR/8)`; move to the largest; stop when none is in the way. Cap at about 150 moves and count caps.
- **Greedy chain over `[1,7]`.** List all zones meeting `[1,7]`; start with the zone containing 1 that exits latest; repeatedly take, among zones entering at or before the current exit, the one exiting latest; a carve is a chain reaching past 7 with no gap.
- **Cycle test.** Links `p → q` with weight `(8j_q−1)/(8j_p+1)`, plus order edges of weight 1; a simple cycle with product `≥ 1` kills the type.
- **Box certificate.** For a box of readings and a rational `R₀`, check `R₀·[lo_i, hi_i] ⊆ [8j+1, 8j+7]` for some `j`, per reading. Subdivide when no `R₀` works.
- **Farkas check.** For a chain type with a gap, maximise the gap-closing slack `t` over the type's cone (any LP solver to find the basis), then verify the dual exactly.

**Calibrators (must come out exactly).**
- AP readings `1…7`: no move, landing `R = 1`.
- `ρ = (1, 2767/1000, 749/200, 957/200, 123/20, 683/100, 11889/500)`: carves `[1,7]` with a 21-zone chain; cascade lands at `R = 6500/683` after 24 moves.
- Lap-2 frontier: `ρ₆ = 7`, `ρ₇ = 511/31`. Lap-3: `ρ₃ = 119/31`, `ρ₂ = 2023/713`, `ρ₇ = 86989/3565`.
- Box `(1,2,3,4,5,6,8)`: demand `ρ₂/ρ₆ < 25/63` against cap `ρ₆/ρ₂ ≤ 17/7`.
- Near-carve pair: `143ρ₆ − 25ρ₇ ≥ t`, `31ρ₇ − 177ρ₆ ≥ t` give `t ≤ −ρ₆/7`; product `4433/4425`.
- Box count: sorted 6-tuples in `[1,17]` number `C(22,6) = 74,613`; those avoiding `{7,8,9,15,16,17}` number `C(16,6) = 8,008`.
- Largest landing: `89·(9/47)·(33/47) = 26433/2209`.

---

## 7. Provenance and limits of this summary

Compiled 2026-11-11 from: the rules file; the three most recent handovers and the self-contained start-up document of 2026-11-09; the framework cheat sheet and glossary; the memory notes on the Lean trees; ten section-by-section digests of the running log, each produced by a sub-reader that read its slice in full (E1 to E847, all ten complete; the log has no entries E167 to E169, and a second series E36b to E48b after E105); and a direct reading and recompilation of the sixteen kernel Lean files. I read each digest's finite-set, retraction and owner-message sections, not every findings line, so a result that appears only in a findings line may be missing here; the digests carry them. The manuscripts (`MANUSCRIPT_v21` of record, `v25_3` latest) were not re-read for this summary. The digests are in `digests/` for reference.
