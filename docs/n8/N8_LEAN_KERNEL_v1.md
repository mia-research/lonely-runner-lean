# The n = 8 Lean Kernel — Modules, Gates, Axioms

**T. Palelei.** Documentation file, v1, 2026-09-18. Companion to `N8_PROOF_v9_3_DOC_v1.md`.

**Every figure in this file was recomputed from the tree on 2026-09-18**, not quoted from a
manuscript. Cascade figures move faster than the manuscript, so a quoted number goes stale; the
commands that produce each figure are given in §6 so any of them can be re-derived.

**What the kernel does not contain.** Existence at order 8 is **not proved** and is **not stated**
in the cascade artefact. It is not a `sorry` — there are none — it is a `Prop` in the specification
(`LRC/Spec/Target.lean`), and cascade gate check [4] fails if a declaration naming it appears inside
the artefact.

---

## 1. The trees

The Lean development sits in `LonelyRunner/`, a **nested git repository** inside the `Math Ex`
repository. It must be committed separately: `git add LonelyRunner` in the outer repository records
only the submodule pointer and silently leaves Lean work uncommitted.

| tree | role | modules | theorems | gate |
|---|---|---|---|---|
| `LonelyRunner/LRC/Construction8/` | v7's artefact, **frozen** | 11 | 85 | `scripts/n8/gate.sh` |
| `LonelyRunner/LRC/Cascade/` | the cascade artefact | 20 | 4,752 (**276 structural**, 4,476 generated) | `scripts/cascade/gate.sh` |
| `LonelyRunner/LRC/Spec/` | the target, the reduction, the doors | 2 | 38 | **neither gate** — see §4 |
| `LonelyRunner/LRC/ConstructionN/` | the general-`n` line (`φ(n)` law, general forms) | — | — | `scripts/nN/gate.sh` |

**Plain `lake build` is not a gate.** `LonelyRunner.lean` imports only `LonelyRunner.Basic`, so the
default target never enters `LRC/` and reports success without compiling the n = 8 work at all. Each
gate builds its modules by explicit target.

**Toolchain.** `leanprover/lean4:v4.29.1`; mathlib `5e932f97dd25535344f80f9dd8da3aab83df0fe6`
(tag `v4.29.1`); batteries `756e3321fd3b02a85ffda19fef789916223e578c`; aesop
`7152850e7b216a0d409701617721b6e469d34bf6`; Qq `707efb56d0696634e9e965523a1bbe9ac6ce141d`;
proofwidgets `4dd0959c44d1af0462bd604d0f87c5781307d709`.

**Digests** (`shasum -a 256 *.lean | sort -k2 | shasum -a 256`, run in the directory), as of
2026-09-18:

| tree | digest | last commit touching it |
|---|---|---|
| `LRC/Construction8/` | `578022e0296ce565ec601655747d1e5cdc614a9efa2cced6540162e698f43b9d` | `f356459` (2026-09-13) |
| `LRC/Cascade/` | `56696dd9669ec0aeb663e27c4010b71dcfdc40c4314e80f5691a2c857eb6ea50` | `919b944` (2026-09-18) — **see §5.4: the tree moved during this session** |

---

## 2. Module map — `LRC/Cascade/`

Theorem counts are per module, comment-stripped, 2026-09-18.

### 2.1 Structural modules (276 theorems)

| module | thms | what it carries |
|---|---|---|
| `Iteration.lean` | 57 | **the cascade itself**, at threshold `1/n`: `inWay`, `nextOpening`, `move`. Soundness and first-ness of a fixed point (`lonely_of_fixed`, `first_isolation_of_fixed`); the flank at the first isolation; the move as a change of AP scale (`inWay_at_scale_iff`, `nextOpening_at_scale`); the first isolation as the end of the run of lap-completion zones (`first_isolation_as_zone_run`); finiteness (`lonely_iff_run_ends`); drift lines at own-AP instants; slot-sharers |
| `Flanks.lean` | 55 | **flanks**: `flankOpening`, `lonely_iff_exists_flank`, `position_at_flank`, `integer_ratio_clear_iff`, `fractional_ratio_circDist`, `exists_clear_step`, the lattice/free pair results, `class_killer_int`, `lonely_of_flank_unkillable` |
| `SmallOrders.lean` | 32 | `n = 3` and `n = 4`; move and return growth; the capped-chain lemma; word rules; the nearest runner's reading as chain state; two and three disparities at every threshold |
| `FourDifferences.lean` | 29 | no return across a few faster moves; four disparities at every `n ≥ 6`; `k` disparities at `n ≥ max(9, 2^(k−1))` |
| `Arrangement.lean` | 27 | the framework's objects **on an arrangement** rather than a disparity set (v9.6; see §5) |
| `Irrational.lean` | 18 | worked irrational instances: `(1, 2, π, 4, …, 8)`, `(1, 1 + √2/100, 3, …, 8)`. **The only module importing mathlib's irrationality results, deliberately** |
| `ManyDifferences.lean` | 17 | `k` disparities at every `n > 2k`, by a potential: `potential_step`, `time_le_potential`, `exists_fixed_of_capped` |
| `Reading.lean` | 11 | every arrangement as an ideal AP of real gap `D` plus deviations (Proposition 2.2) |
| `Certificate.lean` | 9 | the three finiteness bounds that make the order-5 word enumeration legitimate, and what a setting is worth |
| `EighthFamily.lean` | 8 | the one-parameter family `{1, 3, 4, 5, 7, x, 8}` that shadows the largest flank, lonely at an opening of the `7/8` flank |
| `VersionB.lean` | 6 | for each proved class, an **explicit** iterate of the move that is lonely and first |
| `NearAP.lean` | 4 | the critical family `{2, 3, 4, 5, 6, 7, 16m}`, proved lonely at an explicit instant |
| `Together.lean` | 3 | runners in the way together (Appendix A item 4, H1) and the circle-metric triangle inequality `circDist_sub_le` |

`All.lean` (0 theorems) is the import aggregator.

### 2.2 Generated census (4,476 theorems, 94% of the count)

| module | thms |
|---|---|
| `PinnedBatch1.lean` | 1,200 |
| `PinnedBatch2.lean` | 1,200 |
| `PinnedBatch3.lean` | 1,200 |
| `PinnedBatch4.lean` | 813 |
| `CensusBatch.lean` | 62 |
| `CensusFamilies.lean` | 1 |

**These are not 4,476 distinct results.** Each is the *same* one-line application of
`lonely_of_band_list` to a different seven-element list, discharged by `norm_num` and `decide`. They
are a machine-checked enumeration. Across the whole census only **169 distinct `(e, k)` pairs** are
used and a greedy cover needs **78**. The cascade gate prints the structural/generated split on every
run so the headline count cannot be read as independent facts.

The emitters are `gen_pinned_batch_v1.py` and `gen_census_batch_v1.py`; the checkers
`pinned_batch_verify_v1.py` (30,891 clearance checks, 0 failures) and `census_batch_verify_v1.py`
(15,354 values of the free disparity, 0 failures) test against the **definition**, not against the
arithmetic that chose the witnesses.

---

## 3. Module map — `LRC/Construction8/` (frozen)

Eleven modules, 85 theorems, unchanged since v7: `Parts`, `LemmaPass`, `Coords`, `Reference`,
`Gaps`, `Sorted`, `Grid`, `Integrality`, `Flank`, `Window`, `Bounds`.

Of the 85: **59 are stated at general `n`**, 20 involve no runner count (statements about reals), and
6 carry `n = 8` — all of them the zone geometry, whose general forms are formalised separately in the
general-`n` line.

That the tree digests today to the value v9.2 recorded (`578022e0…`) is the evidence that it is in
fact frozen.

---

## 4. `LRC/Spec/` — the target, the reduction, the doors

**Deliberately outside both artefacts**, so that cascade gate check [4] — that nothing in the
artefact names the open statement — keeps its meaning. **Neither gate builds it and neither runs
`#print axioms` on it.** Its axiom check is a separate deposited artefact.

### 4.1 `Target.lean` (396 lines, 15 theorems; commit `e525758`)

**THE TARGET, as of 2026-09-18:**

```
def LonelyRunnerAt8 : Prop   -- every injective v : Fin 8 → ℝ, every subject, some t > 0 lonely
```

This is the conjecture at eight runners, untransformed. `ExistenceOnArrangements` is `Iff.rfl` to it
(`lonelyRunnerAt8_iff_existenceOnArrangements`).

**`ExistenceAt8` is retained but is no longer the target.** It quantifies over a
`ds : Finset ℝ` with `card ds ≤ 7`. It is still proved **sufficient**
(`lonelyRunnerAt8_of_existence`), and everything in §6 of the proof document applies to it verbatim,
but it is not the same statement: `Finset ℝ` forces decidable equality, collapses duplicates and so
destroys the indexing, admits disparity sets no arrangement produces, and discards the arrangement —
gaps, the AP structure, the coupling across the eight subjects.

Equivalent forms of `ExistenceAt8`, all machine-checked:

| declaration | says |
|---|---|
| `target_forms_agree` | the difference-set form ↔ the cascade form (`ExistenceAt8_cascade`) |
| `target_flank_agrees` | the flank form gives it |
| `existence_of_capped` / `capped_of_existence` | **both directions** against `CascadeCapped` — the obligation restated, not weakened |
| `cascade_of_FAM` / `FAM_of_existence` / `FAM_iff_existence` | **both directions** against Finite Active Membership |
| `congruence_of_existence` / `exists_lonely_of_congruence` | against `ExistenceAt8_congruence` — no time: a runner, a lap, and a congruence |
| `exists_lonely_of_threeLargest` | `ThreeLargestFlanks` ⇒ Existence on whole-number disparities (**one direction only** — a strengthening) |
| `exists_lonely_of_card_le_three` | Existence holds **outright** for at most three disparities |

### 4.2 `Doors.lean` (346 lines, 23 theorems; commit `919b944`, 2026-09-18)

`Target.lean` states the doors on a **disparity set**. `Doors.lean` states them on the
**arrangement**, per subject, and proves each **equivalent** to the obligation for that subject.

| door | statement |
|---|---|
| `DoorFlank` | some disparity of the subject hosts a lonely opening |
| `DoorArrives` | the cascade from the subject's first reading reaches a fixed point |
| `DoorCapped` | the cascade's instants are bounded above |
| `DoorFAM` | each other runner is in the subject's way at only finitely many steps |
| `DoorThreeLargest` | the flank can be taken among the three largest disparities — **not proved equivalent**; it is a strengthening, stated so that what it adds is visible |
| `DoorFirstLap` | **the cap, named**: every cascade iterate stays at or below `1/e`, one lap of the nearest runner. `doorCapped_of_doorFirstLap` shows it is a cap and `lonelyRunnerAt8_of_doorFirstLap` that it closes the conjecture. **Nothing proves the cap holds** (commit `919b944`) |
| `DoorLargestFlank` | the flank can be taken as the **largest** disparity — **refuted** by `(2, 3, 5, 7, 8, 13, 16)`, which needs flank 13. `doorThreeLargest_of_doorLargestFlank` keeps the two apart so the refutation touches only this strengthening (commit `919b944`) |

`doors_agree` proves the first four mutually equivalent to `LonelyForSubject`, and
`lonelyRunnerAt8_of_doorFlank` / `_doorArrives` / `_doorCapped` / `_doorFAM` carry each to the target.
Equivalence is the point: none of these is a weaker thing to aim at, and closing any one closes the
target. **Nothing in the module proves the target.**

The module also carries the block-degree view: `lonelyAt_iff_blockDegree_zero`,
`blockDegree_symm_pairs`, `sum_blockDegree`, `existenceOnArrangements_iff_isolated`.

### 4.3 Axiom witnesses for `Spec/`

Since neither gate covers this directory, the axiom checks are deposited separately:

| file | covers | result |
|---|---|---|
| `experiments/n8/v9_6_spec_axioms_v1.out` | `Target.lean`, **15 theorems — every one in the module as it now stands** | all `[propext, Classical.choice, Quot.sound]` |
| `experiments/n8/v9_6_doors_axioms_v1.out` | `Doors.lean`, **20 theorems** | all `[propext, Classical.choice, Quot.sound]` — but the module now carries **23**, so three are **uncovered** (§5.4) |
| `experiments/n8/v9_6_door_dependency_audit_v1.out` | the doors are not `ExistenceAt8` relabelled | see the file |

The earlier `v9_2_spec_axioms_v1.out` / `v9_3_spec_axioms_v1.out` covered only **four** declarations
and no longer described the file once the target was amended; v9.6 replaced them.

---

## 5. The gates

### 5.1 Cascade gate — `scripts/cascade/gate.sh`

**What PASS means:** every module of the cascade artefact builds, contains no `sorry`,
`native_decide`, `unsafe` or `admit`, and **every theorem in it** depends on
`[propext, Classical.choice, Quot.sound]` only.

**What PASS does not mean:** Existence at order 8 is proved. It is open, and check [4] fails the gate
if a declaration naming it appears.

| check | what it does |
|---|---|
| **[0]** | purges dataless (cloud-evicted) `.olean` files — the project sits under iCloud, and an evicted `.olean` reads as `invalid header` while lake's traces still call it up to date |
| **[1]** | builds every module **by explicit target**, with the module list **derived from disk**, not hardcoded |
| **[2]** | `sorry` inventory |
| **[2b]** | hygiene scan: `native_decide`, `unsafe`, `admit` |
| **[3]** | `#print axioms` on **every theorem**, plus a **coverage assertion**: the extractor's count must equal an independent, deliberately **broader** count on disk, so a declaration written in a form the extractor cannot name fails the gate rather than being skipped |
| **[4]** | the open statement must not be stated — a **name tripwire**, not a proof of absence |
| **[5]** | irrational-ratio coverage pinned by name, so it cannot lapse silently |
| **[6]** | the manuscript's recorded figures (theorem count, structural split, both digests, commit, module count) must match this tree |

The gate also fingerprints the tree at start and end, because it is not atomic against edits: a run
that straddles a commit reports a state that never existed.

**Three defects this gate was hardened against, each found in production:**

1. **A hardcoded module list went stale** (2026-09-17), missing nine modules on disk while still
   claiming to build every one. The list is now derived from disk at both sites.
2. **A doc comment was counted as a declaration** (2026-09-18). A `/-- -/` comment in `Flanks.lean`
   wrapped so a continuation line began with the word `theorem`. The extractor counted it *and* the
   coverage assertion agreed — both read raw lines — and the manuscript's figure went to 4,749 when
   4,748 declarations existed. Only Lean caught it, as `Unknown constant Flanks.on`. A
   `strip_comments` pass now guards both sites. **This is the counting-a-proxy failure**: the check
   measured lines, not declarations.
3. **One digest in four slots** (v9.3, repeated in v9.4). Check [6] grepped for the *presence* of the
   `Cascade` digest, which one correct slot satisfies. It now also requires the `Construction8`
   digest and requires the two to differ.

The gate has been tested to fail on a planted `sorry` in a new module and on a planted declaration
naming the open claim.

**Cost.** Step [3] is ~94% of the run and scales with the theorem count; the measured warm baseline
is roughly 12–14 minutes. No cold-build figure is quoted because none has been measured.

### 5.2 Construction8 gate — `scripts/n8/gate.sh`

Same shape, narrower: checks [0], [1], [2], [2b], and [3] on **23 headline declarations** rather than
every theorem, plus [4] "part 7 must not be stated". The all-theorem axiom check for this tree is a
separate deposited artefact, `experiments/n8/v9_construction8_all_axioms_v1.lean` / `.out`: 82 of the
85 depend on exactly the three axioms and 3 on a subset.

### 5.3 Deposited gate runs

| file | theorems | structural | digest | verdict |
|---|---|---|---|---|
| `experiments/n8/cascade_gate_v9_3_v1.out` | 4,698 | 222 | `1af2c9f2` | PASS |
| `experiments/n8/cascade_gate_v9_4_v1.out` | — | — | — | PASS |
| `experiments/n8/cascade_gate_v9_5_v1.out` | — | — | — | PASS |
| `experiments/n8/cascade_gate_v9_6_v1.out` | 4,748 | 272 | `d8ceb5ad` | PASS |
| `experiments/n8/cascade_gate_919b944_v1.out` | 4,752 | 276 | `56696dd9` | **FAIL — check [6] only** (§5.4) |

### 5.4 The run made for this document — 2026-09-18

Deposited at **`experiments/n8/cascade_gate_919b944_v1.out`**. Tree state: commit `919b944`, digest
`56696dd9…`, 20 modules. Total 802s, of which step [3] was 794s.

**Verdict: GATE FAIL — on check [6] alone.** Checks [0] through [5] all passed:

| check | result |
|---|---|
| [0] build-artefact integrity | clean |
| [1] build every module by explicit target | 20 modules, 3,363 jobs, success |
| [2] `sorry` inventory | **none** |
| [2b] hygiene (`native_decide`, `unsafe`, `admit`) | clean |
| [3] `#print axioms`, every theorem | **4,752 of 4,752 clean** — 276 structural, 4,476 generated census (94%) |
| [4] the open statement must not be stated | clean (unstated, as intended) |
| [5] irrational-ratio coverage by name | clean, 5 declarations present |
| **[6]** | **STALE** in `MANUSCRIPT_v9_6.md`: theorems(4,752), structural(276), digest(`56696dd9…`), commit(`919b944`) |

**What the failure is, and what it is not.** Check [6] compares the manuscript's recorded figures
with the tree. `MANUSCRIPT_v9_6.md` records 4,748 theorems, 272 structural, digest `d8ceb5ad…` at
commit `58ba790`; commit `919b944` then added four theorems to `Cascade/Arrangement.lean`. So the
failure is **documentation drift, not a defect in the Lean**: every theorem in the artefact is
axiom-clean, there is no `sorry`, and the open statement is still unstated. The manuscript's figures
need updating, or the manuscript needs to say which commit it describes.

**The run is a valid witness.** The gate fingerprints the tree at start and at end and reports a
mismatch, because a run that straddles an edit describes a state that never existed. This run
reported **no** mismatch, so all figures above describe one state of the tree.

**A caveat on scope.** This gate covers `LRC/Cascade/` only. `LRC/Spec/` is outside both gates by
design (§4), and three of `Doors.lean`'s 23 theorems are currently outside any deposited axiom
witness (§4.3). `LRC/Construction8/` has its own gate and was not re-run for this document; its
all-theorem axiom witness (`v9_construction8_all_axioms_v1.out`) stands at 82 of 85 on exactly the
three axioms and 3 on a subset.

---

## 6. Reproducing every figure in this file

Run from `LonelyRunner/`. `strip_comments` is the gate's own comment-stripping pass, without which
a doc comment can be counted as a declaration (§5.1, defect 2):

```bash
strip_comments() { awk 'BEGIN{d=0}{l=$0; if(d==0) print l; else print ""; n=gsub(/\/-/,"&",l); m=gsub(/-\//,"&",l); d+=n-m; if(d<0)d=0}' "$@"; }
```

| figure | command |
|---|---|
| Cascade theorem count | `strip_comments LonelyRunner/LRC/Cascade/*.lean \| grep -cE '^theorem \|^lemma '` |
| generated census count | the same over `PinnedBatch*.lean CensusBatch.lean CensusFamilies.lean` |
| structural count | total minus generated |
| a tree's digest | `cd <dir> && shasum -a 256 *.lean \| sort -k2 \| shasum -a 256` |
| last commit touching a tree | `git log -1 --format=%h -- <dir>` |
| the full done-check | `bash scripts/cascade/gate.sh <logfile>` |
| `Construction8` done-check | `bash scripts/n8/gate.sh <logfile>` |

Do **not** pipe a gate through `tail`: `tail` holds the whole stream until exit, so the output reads
empty for the full run whether the gate is healthy, hung or dead. Redirect to a file and read the
tail of the file.

---

## 7. Standing hazards

1. **iCloud eviction.** The project sits under `~/Desktop`, which is iCloud-synced, so build
   artefacts get evicted. A dataless `.olean` reads as `invalid header` while lake's traces still
   call it up to date. Gate step [0] handles it; expect recurrence.
2. **`LonelyRunner/` is a nested repository.** Commit it separately, or Lean work is silently left
   out of the outer repository's history.
3. **Figures drift.** The cascade artefact grows faster than the manuscript is revised. Recompute;
   never quote. Check [6] now fails on drift, which is the only reason the drift stops being silent.
4. **Counts are proxies until the object is named.** Every number here names what it counts —
   comment-stripped lines beginning `theorem` or `lemma` — and the coverage assertion in check [3]
   exists because that is a proxy for a declaration and was once wrong.
5. **A name tripwire is not a proof of absence.** Check [4] catches a declaration *named* for the
   open statement. It would not catch one proved under an unrelated name.
