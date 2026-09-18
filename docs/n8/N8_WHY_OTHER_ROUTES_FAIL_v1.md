# Why Other Routes Fail — the register, the objections, and the dead ends

**T. Palelei.** Documentation file, v1, 2026-09-18. Companion to `N8_PROOF_v9_3_DOC_v1.md`.

**What this collects.** Three separate bodies of work, inlined here so each answer stands alone:

- `OBJECT_REGISTER_v3.md` (28 items, append-only; §0a is the supersession table) — constructs imported against the framework,
  each classified and refused with a reason;
- `OBJECTION_LEDGER_v1.md` (append-only) — objections raised against the construction, each
  **tested rather than argued**, plus the false blockers that were raised and refuted;
- `MANUSCRIPT_v9_3.md` Appendix A — four routes that look natural and do not work, with exact
  counterexamples.

**What this is not.** None of it argues that the conjecture is hard, and none of it is a reason to
prefer this framework over another. Every entry is a specific construct meeting a specific object,
with the mismatch named.

---

## 0. The positive list — what the framework actually has

A register of imports is unreadable without the list it is measured against. Everything in §§1–3
is an outside thing laid over one of these, or over nothing at all.

| object | what it is |
|---|---|
| **Gaps** | the eight cyclic gaps between runners **on the track**, summing to 1. Theorem 4.1: a runner is lonely ⟺ both its flanking gaps are `≥ 1/8` |
| **`d_min`** | the nearest speed disparity, from the two speed-neighbours |
| **Laps** | `u = d_min·t`; readings `s_j = d_j/d_min`; phase `s_j·u mod 1` |
| **The seven readings** | `d_min` comes from the nearer neighbour; the second neighbour is read like everyone else |
| **The clearing test** | at `t = a/(nD)`, disparity `e` is clear ⟺ `D ≤ (a·e mod nD) ≤ (n−1)D`. An integer comparison (`coord_iff`) |
| **The band identity** | at `1/(8D)` a runner of reading `s` is in the way ⟺ `s` is within 1 of a multiple of 8. The real-valued form |
| **The move** | to the largest next opening among the runners in the way — one step, fixed by the speeds |
| **The cascade** | the sequence of moves from the bound `1/(8·d_min)`. Real scales, decreasing |
| **The output** | an instant |
| **All-or-nothing** | if `D` divides every disparity, every spine instant at that scale gives the same verdict |

**The check that catches an import:** name the object before naming the problem. If the object is
not on this list, the problem belongs to the reader's model, not to the construction.

---

## 1. The three classifications

| tag | meaning | the repair |
|---|---|---|
| **NOT APPLICABLE** | the framework poses no question here at all; there is no object under the import | **deletion** — nothing takes its place |
| **MISPLACED** | the framework *has* an object here, and the import is the wrong name, shape or scope for it | **substitution** — name the framework's object instead |
| **REFUTED BY THE FRAMEWORK'S OWN CASE** | the import contradicts a worked example already on file | **withdrawal**, citing the case |

**Misplacement is the more dangerous of the two.** It survives every audit that checks whether a
foreign *word* appears, because the word is the framework's own.

---

## 2. The register — imported constructs, and why each is out

### 2.1 The original fourteen

| # | import | why it is out | class |
|---|---|---|---|
| 1 | **"For any six reals `s ≥ 1` there is a `u` …"** | it is the conjecture at eight runners restated. The construction's objects are gaps and laps, not a list of six reals | NOT APPLICABLE |
| 2 | **Blocking** | there is no walk, so nothing blocks. The object that exists is whether a disparity clears — a residue comparison | MISPLACED |
| 3 | **The jump chain**, its handover and cycling | the procedure reads one window and never takes a minimal step; the obstruction was an artefact of the walk | NOT APPLICABLE |
| 4 | **Covering** | covering forms a complement; the construction forms none. Proofs must be pointwise | NOT APPLICABLE |
| 5 | **Measure / zero-measure branch** | the construction measures nothing. The progression's lonely set is four points of length zero, and the framework still names `t = 1/8` there | NOT APPLICABLE |
| 6 | **Witness** | a point is **computed**, not witnessed | MISPLACED |
| 7 | **Carrier** ("which constraint is tight") | the procedure never asks which one was last to clear | NOT APPLICABLE |
| 8 | **Set emptiness** | good-set language in a new coat | NOT APPLICABLE |
| 9 | **Weyl equidistribution** | a real result, but an outside debt — and unnecessary: irrational disparities are read directly, `√2/100` exactly | NOT APPLICABLE |
| 10 | **LRC(7) / induction on `n`** | excluded from the candidate proof | NOT APPLICABLE |
| 11 | **`p` and primes** | Rosenfeld's method is a prime search; this is not. The index object is `r`, the units mod 8 | MISPLACED, with downstream damage (item 16) |
| 12 | **A stationary first runner** | standing ban: never pin any runner at 0 | NOT APPLICABLE |
| 13 | **Slots** as a word for an eighth | the object is an eighth | MISPLACED |
| 14 | **A cited Proposition 4.1** | it is a proof sketch in its source, and it is a measure statement — item 5 arriving under a citation | NOT APPLICABLE |

### 2.2 The imported restrictions — the recurring shape

These are the ones that did real damage, because each narrowed the construction and then the
narrowing was read back as a limit.

| # | restriction imposed | the framework's object |
|---|---|---|
| 15 | the first window `u ∈ [1/8, 7/8]` | **no restriction on when.** Consequence: every coverage figure quoted — 81.9%, 66.0%, 86.8% — is a statement about that window, not about reach |
| 16 | `p ∈ {1, 3, 5, 7}` carried onto the enlarged tier | the numerator is free. The ceiling argument binds at the AP tier only; §7c's own exhibited failure clears at `D = 5`, `a = 9` |
| 17 | `a ≡ 1 (mod 8)` | any odd numerator. **Refuted by the framework's own case**: §7d's worked instant is `t = 71/8`, and `71 ≡ 7 (mod 8)` |
| 18 | `D ∈ ℤ` | the gap is a **scale**. Integer-`D` produced 82 false failures on irrational configurations; with the framework's own scales, 0 |
| 19 | the lap as part of the output | the instant is the output |
| 24 | "return the first candidate that passes" | the first-instant demand in control-flow costume, re-importing item 15 |

### 2.3 The rest

| # | import | why it is out | class |
|---|---|---|---|
| 20 | **The interior / no-interior split** | it classifies arrangements by whether a **density** argument applies. The framework produced in 472 of 472 empty-interior cases | NOT APPLICABLE |
| 21 | **"Gap" used for the lattice step** | in the framework gaps are the **eight cyclic gaps on the track**. Every question asked about "whether a gap clears" read as a question about loneliness and was not one | MISPLACED — **the sharpest entry** |
| 22 | **A loop over the gap index** | by `D = p/(8t)`, searching for the gap is re-asking the construction's output as its input | NOT APPLICABLE |
| 23 | **A loop over the numerator** | same root as 22 | NOT APPLICABLE |
| 25 | **Termination** raised as a blocker | nothing runs. Each step is finite. It is a property of the imported loop, not of the cascade | NOT APPLICABLE |
| 26 | **Rule coverage read as reach** | rule-firing rates measure *explanation*; the object is *production* | MISPLACED |
| 27 | **Union bounds over the candidates** | item 4 by a new route. A bound reaching 86.8% produced no instant | NOT APPLICABLE |
| 28 | **The global clock / simultaneity** | demonstrated dead: `(3, 7, 12, 20, 29, 31, 44, 50)` gives eight runners, five distinct instants, and **zero** instants at which all eight are lonely together | NOT APPLICABLE |

### 2.4 Misplacements inside the framework's own objects

Nothing foreign entered; one of the framework's own objects was used at the wrong scope.

| error | correction |
|---|---|
| **Five readings instead of six** | the second speed-neighbour is read like everyone else. At `(4, 12, 29, 37, 101, 121, 176, 196)`, runner 37: five-only returns `1/8`, the truth is `9/64`. Differs in **3,276 of 48,000** |
| **Grid and AP conflated** | Grid ⊋ AP. `(1, 2, 3, 4, 5, 6, 15, 16)` is a grid and not a progression |
| **Octant labelling at exactly `1/8`** | `7/8` is *allowed* — the distance is exactly `1/8`. **16.7% of positions sit exactly on the boundary.** Evaluate boundary points separately; never merge touching zones |
| **Measure-zero read as a difficulty** | a reading that is four isolated points is a progression. In `(8, 9, 10, 11, 15, 16, 17, 18)` two runners have disparities `1…7`: pure progressions. They are the *easy* cases |

### 2.5 The generator, stated once

Twenty-eight entries, and one move behind almost all of them:

> **An absence in the reader's own model of the construction is converted into a requirement on the
> construction.**

The pattern in full: not seeing what named a step, one builds a loop; the loop then needs a bound,
a termination proof and a coverage figure; each of those becomes an objection to the framework.
None of the three was about the framework.

---

## 3. Objections tested

Each was tested rather than argued. Figures are for the construction as it stood when tested
(2026-09-14, a rule-based construction over lattice instants), except where noted.

### 3.1 Objections that do not apply

| objection | outcome |
|---|---|
| **Incommensurable speeds break it** | 0 failures over 3,200 runner-instances with every disparity irrational. Now also **proved in Lean** on instances: `(1, 2, π, 4, …, 8)` with every runner lonely, the `π` and `4` runners at the irrational `1/(8(4 − π))`, using only `3 < π < 3.15` — no rational approximation |
| **Ties among the disparities break it** | 8,122 instances with repeated disparities, 0 failures |
| **It is an `n = 8` construction** | rules fired for 76.7–87.0% at `n = 5, 6, 7, 8, 9, 11, 12, 13`, and every instant produced was genuine, 23,703 of 23,703 |
| **It needs a global clock** | demonstrated dead — see register item 28 |
| **It needs the real-to-integer reduction** | the test reads irrational disparities directly via the band identity; `√2` is never approximated |
| **Measure or density is required** | inapplicable: the quantity such an argument bounds is **zero** for the progression, where the framework names `t = 1/8` |
| **Covering, or counting the candidates** | inapplicable **by type**: both conclude that some point survives; the construction names which. A bound reaching 86.8% produced no instant |
| **The test might not mean what it says** | `D ≤ (a·e mod nD) ≤ (n−1)D` ⟺ distance at least `1/n`: proved (Prop 2.1), and checked on 28,000 cases at `n = 5…13`, 0 disagreements |
| **Producing an instant is not what is asked** | an instant at which a runner is lonely is Existence for that runner (Corollary 6.4) |

**An imported restriction this exposed.** The first objection *appeared* to bite — 82 of 2,400
failures — until the scale `D` was found to be ranging over **integers**. With the framework's own
scales the failures went to zero. That was the fifth such restriction found, after the first window,
`p ∈ {1,3,5,7}`, the lap in the contract, and `a ≡ 1 (mod 8)`.

### 3.2 False blockers — objections raised and found to be false

| the claim | why it was false |
|---|---|
| **"The construction is not proved to always produce"**, from rule shares of 81.9% and 66.0% | those are **rule coverage**, not reach. The construction produced for **12,000 of 12,000** random runners and for every runner of every hard case on file |
| **"The stepping is not proved to terminate"** | nothing runs forever. Each step is one move, fixed by the runners in the way; no search is performed. What remains open is stated as Existence |
| **"The gcd rule does not survive incommensurability"** | the `d_min`-scaled construction produced for **1,600 of 1,600** all-irrational runners **without** that rule. Its absence costs nothing |
| **"§7.4 has a counterexample"**, from `(1, 31, 75, …, 225)` | it refutes v7's **wording**, which stopped the cascade at lap 0. Read past lap 0 the runner is isolated, at `t = 43/240` |
| **"Theorem 4.7 is an imported global obligation"** | global isolation of the progression is the framework's **reference ideal**, derived in Lean from its own objects. What held of the point is narrower: where the reference instant does not survive, the per-runner reading of deviations gives the instants |

### 3.3 The test for the next one

> If an objection is about **how long a search takes**, **how much of the space is covered**, or
> **when the instant falls**, it is a false blocker. The construction computes an instant; those
> three questions are about a search that is not there.

### 3.4 An objection that is not a false blocker

**Exactness was claimed unconditionally and holds only for commensurate arrangements.** It passes
the test above: it is not about search length, coverage or timing. For the runner at `1 + √2/100`,
`d_min`, the instant and the readings are all irrational and the test is a real inequality. **The
construction still delivers** — that runner is lonely at the instant produced. What failed was a
claim *about the method*, not the method. Corrected: the method is real-valued throughout; the
integer test is its **commensurate representation**.

### 3.5 A drift audit of the small-order line

Run 2026-09-15, on the author's instruction, reading each piece for what it actually uses.

| piece | verdict |
|---|---|
| moment iteration, lap zones, boundary set, the bound | **framework** |
| setters, laps, return lemma, word rules, return growth, the nearest reading as chain state | **framework** |
| large-lap searches over progression references with deviations | **framework** |
| **Advance budget** — sums each runner's zone width over the time it spans | **import — a density count in chain form.** It never used a handoff, a setter's identity or a reading. **Excised**, and replaced by the slowest-setter recursion |
| **"Zones' combined width exceeds 1 explains the failures"** | the same density count. **Excised** |
| **"n = 5 is the four-speed case"** | someone else's problem statement placed next to the framework's. **Excised**, replaced by the cap `R < 4` |
| a uniform "clear point within Λ laps" lemma; compactness; almost-periodicity; meeting-time candidates from published proofs | **import.** Dropped before anything was built on them |

---

## 4. Routes that cannot close this

Four routes that look natural and do not work, each with the exact fact that kills it.

### 4.1 Comparing zone lengths with the lap cannot name an instant

In the progression the first runner's lonely instants are the isolated points
`≡ 1/8, 3/8, 5/8, 7/8 (mod 1)`. **The set on which such a comparison would have to find room has
length zero in exactly the case that matters.** Any argument must name an instant.

### 4.2 A chain of overlapping zones has no ratio to accumulate

A route that follows a chain of overlapping zones and bounds the spread of readings it can pass
through fails on four exact facts:

1. `u = 7/8` can be in the way of a reading well above `9/7`: at `s = 11/5` on its second lap,
   `‖(11/5)(7/8)‖ = 3/40`.
2. The overlap bound `s/s′ < 9/7` holds for **first** zones only. Lap `k` of `s` meets lap `k′` of
   `s′` when `s/s′ < (8k + 1)/(8k′ − 1)`, giving `17/7` and `25/7` later.
3. **A run is built from zones, not runners.** A reading `s` has `s` zones per lap of the nearest
   runner; an observed run went 11 steps with readings recurring. `N` runners do not give `N − 1`
   steps.
4. A single reading can be in the way at both `u = 1/8` and `u = 7/8`: `s = 8`. The descent through
   consecutive integers breaks at `s = 4`.

*Data on runs.* Over every arrangement `0 = v_1 < … < v_8 ≤ 20` whose short gap has left the wrap:
231,294 runner-instances with a reading in the way at the bound; runs of mean 2.38 zones, 99th
percentile 8, maximum 19. Those are small integer arrangements; runs elsewhere end much later.

### 4.3 Counting readings against clear intervals fails

Over one lap of `u` a reading `s = 8` has 8 zones and 8 closed clear intervals. The v7 inference
that five other readings cannot be in the way on six intervals **assumed one reading per interval**;
readings share an interval, and one reading has zones in several. Over 300,000 draws of five
readings, the most closed was three of six — neither none nor all.

**And no count can repair it.** With `σ` the smallest reading other than the baseline, the
lap-`(2k+1)` zone of `s = 2σ` lies inside the closed clear interval
`[(8k+1)/(8σ), (8k+7)/(8σ)]` of `σ` **for every** `k` (`two_sigma_zone_inside`, needs `n > 3`).
`[PROVED]` So Proposition 3.3's "at least two readings acting together" cannot be combined with a
count of how many intervals each reading reaches.

### 4.4 Runners in the way together (H1) — a direction, not a result

If two runners sit at `x`, `y` relative to the subject with `‖x‖, ‖y‖ < 1/8`, then
`‖x − y‖ ≤ ‖x‖ + ‖y‖ < 1/4`; and if both lie on the same side, `|x − y| < 1/8`. So their
connecting disparity is within `1/4` of a lap line, and within `1/8` on the same side.
`[PROVED — Together.connecting_difference_near_lap, _same_side; the circle-metric triangle
inequality circDist_sub_le is proved there too]`

The development record combines H1 with the overlap bound of §4.2 to argue that a long run forces
near-divisibility conditions on the arrangement's gaps. **That step is stated there, not derived**,
and is recorded as a direction in the framework's objects, not as a result. The next test it names:
trace the steps of the longest run (19 zones) and locate the arithmetic that ends it.

---

## 5. What the framework's own bans exclude

The firewall, restated because it is the compact form of everything above.

| ban | content |
|---|---|
| **No stationary frame** | no runner pinned to zero |
| **No window, no bound on when** | no result requires a bound on when an instant falls |
| **No search** | the cascade is fixed by the speeds; nothing is picked or predicted |
| **No first-instant demand** | first-ness is a *proved property* of the output, not a requirement |
| **No global clock** | each runner receives its own instant |
| **No measure or density** | exact arithmetic and lap-zone geometry only |
| **No covering or emptiness language** | no complement is formed and no set is shown empty |
| **Boundary discipline is mandatory** | open cells and boundary points evaluated separately; a cell decided by an interior point |

**Three were violated in earlier drafts**, all recorded rather than repaired quietly: the
first-instant demand (v7 §7.1–7.2, now resolved); the pinned frame (v7 §7.4 evidence, a standing
caveat); and no covering or emptiness language, found 2026-09-17 and the cause of the withdrawal of
Propositions 6.10–6.11 in v9.3.

**The test, stated once.** The bound lives in the **argument**, not in the shape of the statement.
Every result kept concludes with an unbounded `∃` in Lean, and that is not the defect; their
witnesses carry an index bound. Read the proof, not the `∃`.

---

## 6. What the framework does not exclude

Stated because the list above is long and reads as a wall.

- **Pigeonhole and residue counts are admissible as tools** (author's ruling, 2026-09-15, still
  standing). `exists_fixed_of_lonely` uses pigeonhole and is native. The test that withdrew
  Propositions 6.10–6.11 was not the tool but the **index bound**: they concluded that a lonely
  opening exists without bounding where it is.
- **Irrational speeds are not an exception anywhere.** The cascade is real-valued throughout;
  `class_killer_int` covers rational and irrational ratios in one case with no rationality input.
- **The `n > 2k` proof is kept**, although it arrives at the covering threshold, because it gets
  there by a route that uses no covering — a potential, producing an explicit cap. What was refuted
  is the *framing* of `n > 2k` as the obstruction to beat, not its proof.
