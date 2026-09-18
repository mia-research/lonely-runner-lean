# The n = 8 Framework — Glossary and Notation

**T. Palelei.** Documentation file, v1, 2026-09-18. Companion to `N8_PROOF_v9_3_DOC_v1.md`,
`N8_LEAN_KERNEL_v1.md`, `N8_WHY_OTHER_ROUTES_FAIL_v1.md` and `N8_PROOF_ARGUMENTS_v1.md`.

**Why this file exists.** The framework uses about forty terms with meanings specific to it, and
several of them are ordinary English words. `OBJECT_REGISTER_v3.md` item 21 records the sharpest
case: the word **gap** was attached to two different objects across many exchanges, and every
question asked about "whether a gap clears" read as a question about loneliness and was not one.
The register calls that the most dangerous kind of error, because it survives any audit that
greps for foreign vocabulary — the word being imported is the framework's own. §5 below lists
every such collision found so far.

Nothing here is a new claim. Definitions follow `MANUSCRIPT_v9_3.md` and the Lean source.

---

## 1. The setting

| term | meaning |
|---|---|
| **Arrangement** | eight distinct real speeds. Formally `v : Fin 8 → ℝ`, injective. **Not** a set: the indexing is part of the object |
| **Subject** | the runner currently being considered. The construction is run separately and identically for each of the eight; no runner is privileged and none is held stationary |
| **Circle distance** `‖x‖` | distance from `x` to the nearest integer; the separation on a circle of circumference 1. In Lean, `circDist` |
| **Threshold** | `1/n`, so `1/8` at eight runners |
| **Lonely** (at `t`) | the subject is at circle distance at least `1/8` from every other runner at `t`. The threshold case counts as lonely |
| **In the way** (at `t`) | a runner is within **strictly** less than `1/8` of the subject. The negation of clear |
| **Clear** | not in the way. Exactly on the threshold is clear |
| **Order** `n` | the number of runners. Most statements are proved at general `n` and instantiated at `n = 8` |

---

## 2. The subject's own data

| term | meaning |
|---|---|
| **Disparity** `d_j` | `\|v_j − v_i\|`, the speed difference between the subject `i` and runner `j`. Seven of them. Also called a **difference** in older files |
| `Δ_i` | the set of the subject's seven disparities |
| `d_min`, `m` | the smallest disparity, attained at a **speed-neighbour**. For an extremal runner it is one-sided |
| `d_max` | the largest disparity |
| **Speed-neighbour** | the runner adjacent to the subject in **speed** order. Distinct from a track neighbour (§5) |
| **Reading** `s_j` | `d_j / d_min ≥ 1`. Equality is possible. All seven are evaluated, including the `d_min` reading itself and the second speed-neighbour's |
| `S` | `d_max / d_min`, the subject's **ratio**. Never the spread |
| `W` | `v_8 − v_1`, the **spread** of the speeds. A difference, not a ratio |
| `μ` | the smallest speed gap anywhere in the arrangement (used in §4.6 of the proof document) |
| `R` | `d_min / D_final`, the cascade's instant measured in units of the bound. Largest found at order 8: ≈ 11.96 |
| **Lap coordinate** `u` | `u = d_min · t`. One unit of `u` is one relative lap of the nearest runner |
| **Phase** | `s·u mod 1`. A reading is clear exactly when its phase lies in `[1/8, 7/8]` |

---

## 3. The geometry of one reading

| term | meaning |
|---|---|
| **Zone** (lap zone, in-the-way zone) | the **open** interval `((8k − 1)/(8s), (8k + 1)/(8s))` in `u` on which one reading is in the way; one per lap. Width `1/(4s)` |
| **Lap-completion zone** | the same object named by the lap it surrounds: runner `d` completes relative lap `N` at `N/d` and is in the way on `((N − 1/8)/d, (N + 1/8)/d)` |
| **Clear interval** | the **closed** interval between consecutive zones of one reading. Width `3/(4s)` |
| **Cell** | a maximal interval of the boundary-set decomposition. **Decided by an interior point, never by its two ends** — both ends of a cell can be clear while the cell is an in-the-way zone |
| **Boundary set** / **BSM** | the finite, named set of instants at which some runner sits exactly on the threshold. Isolation is decided on it. Open cells and boundary points are evaluated separately, and touching zones are never merged |
| **Run** | a list of lap-completion zones, each containing the end of the one before, starting with one containing the bound. Its **end** is the right end of the last zone |

**Boundary discipline is load-bearing, not pedantry.** Closing the zones would put `u = 1/8` in the
way for `s = 7` and the arithmetic progression's spine would vanish.

---

## 4. The ideal, the scale, and the cascade

| term | meaning |
|---|---|
| **The ideal** | the arithmetic progression. Every arrangement reads as an ideal of some gap `D` plus deviations in `[0, D)` |
| **Gap** `D` (of the ideal) | **a scale, a positive real — not an integer, and not a track gap.** See §5 |
| **Deviation** `ε_j` | runner `j`'s departure from its ideal location, in gap units, in `[0, 1)` |
| **Slot** `a_j` | runner `j`'s whole index difference from the subject against the ideal. The framework's unit is an **eighth**; "slot" names which eighth |
| **Spine** (of scale `D`) | the instants `r/(8D)` with `r` odd. `r = 1` is the **first spine point** |
| **Bound** | `1/(8·d_min)`, the first spine point of the progression of gap `d_min`. Where the cascade starts. Earliest possible lonely instant |
| **Band identity** | at `1/(8D)` a runner of reading `s = d/D` is in the way **iff** `s` is within 1 of a multiple of 8. Stated over the reals for every `D > 0` |
| **Opening** (of a disparity `d`) | an instant `(k + 1/8)/d`, `k = 0, 1, …`: one eighth past a lap line of `d`. The `k = 0` opening of `d_min` is the bound |
| **Next opening** (after `t`, for `d`) | the least opening of `d` at or after `t` |
| **Move** | sends `t` to the **largest** next opening among the runners in the way at `t`; leaves `t` fixed if none is |
| **Cascade**, **determinator** | the sequence of moves from the bound. Fixed by the speeds — there is no candidate set and nothing is searched, sampled or picked |
| **Setter** | the runner whose next opening the move lands on. It changes at nearly every move |
| **Fixed point** | an instant the move leaves alone: no reading within 1 of a multiple of 8 at that scale |
| **Dilation** | one cascade step, which multiplies every reading by the same factor `λ = (8N + 1)/s_x > 1` |
| **Slot-sharer** (at scale `D`) | a runner with `d/D ∈ 8ℤ`; it sits on the subject at **every** spine instant of that scale |
| **Near-sharer** | a reading within 1 of a multiple of 8 — slot `≡ 0`, or slot `≡ 7` with positive deviation |
| **Live / dead** (scale or lattice) | dead for the subject when some reading is a whole multiple of `8L`; live otherwise. **Live is not the same as lonely** |
| **Own AP instant** | `ν/(8·d_min)`, `ν = 1, 2, …` — the subject's own progression's instants, as opposed to the cascade's |

---

## 5. Collisions — words that name two different objects

Each of these has caused a recorded error. This is the section to read before writing anything.

| word | the framework's object | the thing it gets confused with | record |
|---|---|---|---|
| **gap** | one of the **eight cyclic gaps between runners on the track**, summing to 1. Theorem 4.1 is the only gap condition the framework has | the ideal's **scale** `D`. "Does this gap clear" is then a question about loneliness that was never asked | register item 21 — "the sharpest entry on this list" |
| **slot** | which eighth a runner occupies against the ideal | used as a synonym for "an eighth" | register item 13 |
| **neighbour** | **speed**-neighbour, adjacent in speed order | **track** neighbour, adjacent on the circle. Cyclic adjacency is a property of the track, not of the speed ordering | §2.1, §4.1 |
| **spread** | `W = v_8 − v_1`, a difference | the ratio `S = d_max/d_min`. A script and its first output printed "spread" for the ratio; both were corrected and the certificate re-run | §8.2, order-5 certificate |
| **candidate** | **nothing, in the present framework.** The cascade has no candidate set | an instant `p/(8D)` in the 2026-09-14 rule-based construction, which had `4D` of them per gap | register items 22–24 |
| **first** | nothing is required to be first. First-ness is a *proved property* of the cascade's output (Thm 6.2(b)) | a demand placed on the construction | register item 24; firewall row 4 |
| **window** | **nothing.** There is no evaluation window | v7's confinement to `u ∈ [1/8, 7/8]`. Every coverage figure quoted from v7 — 81.9%, 66.0%, 86.8% — is a statement about that window, not about reach | register item 15 |
| **7/4** | a union bound on blocked **time**: seven arcs of width `2/8` | a statement about the eight track gaps. Ruled the wrong object to quote beside a gaps discussion, 2026-09-18 | commit `919b944`, correction 1 |
| **predictor** | **nothing.** The construction determines; it does not predict | several script and document names predate the present terminology (`predictor`, `WHY_IT_PREDICTS`) | §10 |

---

## 6. Flanks

| term | meaning |
|---|---|
| **Flank** | one of the subject's own disparities, considered as the host of openings. By Proposition 6.1 every lonely instant is matched by a lonely opening of one of them |
| **Flank opening** | `(k + 1/8)/e` for flank `e`. In Lean, `flankOpening n e k` |
| **Ratio** `ρ_j` | `d_j / e`. At a flank's `k`-th opening **only the ratios enter**: runner `j` sits at `ρ_j·(k + 1/8)` laps |
| **Live flank** | no ratio to it is a multiple of 8 |
| **Shadowed flank** | every one of its openings has a runner in the way |
| **Shadowing value** | a value of a free disparity that shadows the flank. These form a **finite** set — that finiteness is what the flank calculus buys |
| **Lattice** (`c`-lattice, `P`-lattice) | the ratios whose fractional part has denominator dividing `c`. A lattice runner's verdict repeats with its denominator, so it is clear on a whole residue class of openings |

---

## 7. Verification vocabulary

| term | meaning |
|---|---|
| **Version B** | for a class already proved, the **explicit** iterate of the move that is lonely and first — not merely an existence statement |
| **Census** | the shadowing-set enumeration: 4,413 pinned families plus 62 with one free disparity. Each is the *same* criterion instantiated, discharged by `decide`. **Not 4,476 distinct results** |
| **Pinned frame** | an enumeration fixing `v_1 = 0`. **Not the framework's frame.** What carries such counts across is that a common shift of every speed leaves every disparity, and so every reading, unchanged |
| **Gate** | a done-check script. Cascade gate: builds every module by explicit target, inventories `sorry`, scans for `native_decide`/`unsafe`/`admit`, runs `#print axioms` on every theorem, and checks that the open statement is not stated |
| **Native / nativeness** | a claim about what a declaration **cites** — whether its proof stays inside the framework's own objects. A per-version pass over that version's additions. **Not** a claim that the artefact imports nothing |
| **Structural vs generated** | 276 structural theorems carry the mathematics; 4,476 generated census instances are one statement instantiated. The gate prints the split on every run |

---

## 8. The three outcomes, and the doors

| term | meaning | status |
|---|---|---|
| **Construction** | a fixed point of the cascade is lonely, is the **first** lonely instant, ends the run of lap-completion zones from the bound, and has a flank at exactly one eighth | `[PROVED]` |
| **Localisation** | every lonely instant is at or after every cascade step and is matched by a lonely opening no later than it | `[PROVED]` |
| **Existence** | the cascade reaches a fixed point at all | **`[OPEN]`** at order 8 |
| **Door** | an equivalent form of the obligation for one subject. Closing any one closes the target | see below |

| door | statement | relation to the obligation |
|---|---|---|
| `DoorFlank` | some disparity hosts a lonely opening | **equivalent** |
| `DoorArrives` | the cascade from the subject's first reading reaches a fixed point | **equivalent** |
| `DoorCapped` | the cascade's instants are bounded above | **equivalent** |
| `DoorFAM` | each other runner is in the subject's way at only finitely many steps | **equivalent** |
| `DoorFirstLap` | every cascade iterate stays at or below `1/e`, one lap of the nearest runner | **sufficient, not equivalent.** The cap is not proved |
| `DoorThreeLargest` | the flank can be taken among the three largest disparities | **sufficient, not equivalent** — a strengthening |
| `DoorLargestFlank` | the flank can be taken as the **largest** disparity | **refuted** by `(2, 3, 5, 7, 8, 13, 16)` |

---

## 9. Lean identifiers most often met

| identifier | meaning |
|---|---|
| `circDist` | circle distance to the nearest integer |
| `inWay n d t` | the runner at disparity `d` is within `1/n` of the subject at `t` |
| `nextOpening n d t` | the least `(k + 1/n)/d` at or after `t` |
| `move n ds t` | the largest `nextOpening` over the runners in the way; `t` if none |
| `Lonely n ds t` | every disparity in `ds` is clear at `t` |
| `LonelyAt v k t` | subject `k` of arrangement `v` is lonely at `t` |
| `diffSet v k` | subject `k`'s disparities, as a `Finset ℝ` |
| `flankOpening n e k` | `(k + 1/n)/e` |
| `LonelyRunnerAt8` | **the target**: the conjecture at eight runners on an injective `v : Fin 8 → ℝ` |
| `ExistenceOnArrangements` | `Iff.rfl` to the target |
| `ExistenceAt8` | the difference-set form. Retained, proved **sufficient**, **no longer the target** |
| `CascadeCapped` | the cascade's instants are uniformly capped. Equivalent to `ExistenceAt8`, both directions proved |
| `FiniteActiveMembership` | each disparity is in the way at only finitely many cascade steps. Equivalent, both directions proved |

---

## 10. Grades

| tag | meaning |
|---|---|
| `[PROVED]` | a proof exists; where a Lean declaration is named, it is machine-checked |
| `[DERIVED]` | follows by stated arithmetic from a `[PROVED]` result, not separately formalised |
| `[VERIFIED — scope]` | exhaustive or exact computation over a stated finite range. **Not** a substitute for a proof |
| `[EMPIRICAL]` | sampled computation; a measurement, not a bound |
| `[OPEN]` | stated, not proved |
| `[WITHDRAWN]` | previously asserted, retracted, reason recorded |
| `[CARRIED]` | a figure restored from an earlier version rather than recomputed |

---

## 11. A note on dated vocabulary

`OBJECT_REGISTER_v3.md` §0 lists "the framework's own objects" as of **2026-09-14**, when the
construction was a rule-based procedure over lattice instants `p/(8D)` with integer scales
`D = k·d_min`, and the cascade was `SKETCH_v7` §7c's three tiers. Several entries there —
**candidates**, the **ceiling** `D ≤ 7·d_min`, the **enlarged tier**, the **output pair `(D, a)`** —
describe that procedure and not the present cascade, whose scales are real, `d/(8N + 1)`, and
decrease from `d_min`. The register is append-only and is not edited; read its §0 as a snapshot.
The present objects are §§2–4 above.
