# Where the framework stops being a proof on its own terms — an audit for self-imposed blocks

2026-09-15, version 2: states the basis of the reading in §0; nothing else changed. Owner's question: *where are the boundaries of the framework that stop it becoming proof on its own terms, not
imported requirements, and have we blocked ourselves by defaulting to someone else's machinery?* Each entry below gives the
block as it stands in the record, where it came from, whether it is the framework's or an import, and the framework's own form.
Sources are named; grades follow `CLAIM_GRADES_v1.md`.

---

## 0. The framework's own proof shape, stated first

From the owner's statements (v7 list item 12, 2026-09-14) and the proved objects:

- **Every arrangement is an AP ideal relocated.** At a gap `D`, read from the subject's own speed as base, runner `j` has an
  integer slot `a_j` (negative for slower runners) and a deviation `ε_j ∈ [0, 1)` in gap units. The subject itself has slot 0
  and deviation 0 (`CascadeRule.reading` with `base = v_i`; `reading_dev_bounds`; `position_in_eighths` uses
  `idx_j − idx_i` and `dev_j − dev_i`, which on this basis are `a_j` and `ε_j·D`). This holds for every real arrangement,
  commensurate or not.
- **The ideal is globally isolated.** At spine instant `r` (in eighths of the gap), the ideal puts runner `j` at `a_j·r`
  eighths. Every runner is clear at every `r` coprime to 8 unless `a_j ≡ 0 (mod 8)`, a slot-sharer (φ(n) law, §5;
  `on_ideal_clear`).
- **Relocation is drift.** The deviation moves runner `j` by `ε_j·r` eighths (`position_in_eighths`). Runner `j` is in the way
  at spine `r` exactly when `r·(a_j + ε_j)` is within 1 of a multiple of 8 (`drift_blocked_iff_interval`, real-valued).
- **The cascade chooses the scale.** When the drift puts some runner in the way at the spine instant, the next scale is
  `d/(8N + 1)` and the readings are re-read as new slots and deviations. *"The cascade happens to give you the appropriate AP
  scale to use."*
- **Any lonely instant settles the runner** (Corollary 6.4). The framework names an instant. It does not need the first one,
  and it does not need a bound on when.

So the framework's proof of Existence has this shape: **for every ideal and every relocation, some scale and some spine instant
at that scale are clear.** Each block below is checked against that shape.

---

## 1. Blocks found

### B1. The target became "bound `R`", a statement about *when*  `[IMPORTED PROOF SHAPE — self-imposed]`

**Where:** `TARGETS_v1–v3` §1 ("Existence ⟺ `R_N` bounded"), T1 (`R < 4`), T3 (`R ≤ 2n − 1`), T2 (a growth potential), the
return-lemma and word-rule programme (items 37–52).
**Origin:** the colleague's "Version B" proposal (*prove the framework terminates*) and the termination programme built on it:
algorithm termination via growth bounds, potentials, and case analysis of the iteration's words.
**Why it blocks:** the equivalence is true, but it recasts Existence as a dynamics problem about an iteration. The framework's
statement is about naming a scale. Objection ledger Part 4's own test applies: *an objection about how long the search takes,
how much is covered, or when the time falls is a false blocker.* A uniform cap on `R` is a "when".
**The framework's form:** Existence = for every ideal and relocation, some scale and spine instant clear (§0). The cascade is
one way to find it; Localisation means any way will do.
**Standing:** T2 (`ManyDifferences`) is correct mathematics in the framework's objects, but its machinery (a potential bounding
growth) is not the framework's. T1 and T3 are targets of this imported shape.

### B2. The order-5 target `R < 4` is the first window again  `[IMPORTED REQUIREMENT — self-imposed]`

`R = n·d_min·t < n − 1` says the runner is lonely within its nearest neighbour's first relative lap. That is the first-window
restriction the owner rejected (v7 list item 1: *"I never thought the first window/cycle was a requirement"*). It came back
as the n = 5 "cap" in status v4–v6, item 50 ("the n = 5 cap is `R < 4`"), and `TARGETS` T1. `R ≤ 2n − 1` is the second window.
As proof devices these are legitimate if true, but they are stronger than Existence, and making them *the* target reinstates
the window as the thing to prove.

### B3. "The lattice route needs rational readings"  `[IMPORTED MACHINERY — withdrawn]`

**Where:** `TARGETS_v3` §4A ("the route is for rational readings; incommensurate speeds need … a separate argument").
**Origin:** I decided lattice instants by periodicity in `p` and residue classes. That is residue-class / periodic machinery,
which needs rational readings.
**The framework's form:** slot plus drift is real-valued (§0). Loneliness at a lattice instant is decided by the drift intervals
for any real reading.
**Checked** (`experiments/n8/lattice_witness_irrational_v1.py`, readings `a + b√2`, decided exactly by integer square roots,
no floating point, no periodicity):

| | runners | gap 0 | 1 | 2 | none found |
|---|---|---|---|---|---|
| order 5 | 777 | 775 | 1 | 1 | 0 |
| order 8 | 377 | 377 | 0 | 0 | 0 |

Irrational readings behave like rational ones on the lattice route. Only exact slot-sharers make a lattice dead, and an
irrational reading never does. Lean already proves an irrational instance exactly (`IrrationalCascade.r2_lonely`, spine `r = 3`
at scale `δ`).

### B4. "The dead lattice is about integer scales"  `[ARTEFACT OF A LEAN STATEMENT — withdrawn]`

**Where:** `TARGETS_v1–v3` §4, objection 1.
**Origin:** `dead_iff`, `dead_downward` and `exists_live` are stated over `ℕ`, and I read the concept off the statement.
**The framework's form:** a slot-sharer at scale `D` is a difference that is a whole multiple of `8D`. That makes sense for real
`d`, `D` (`sharer_inWay_at_ap_instant` is real-valued). Objection 1 is withdrawn. Objection 2 (the cascade's scales decrease
while the spread-live region is at large `D`) concerns the cascade trajectory only. Objection 3 (live is not lonely) is the
open content of T4.

### B5. The residue rule (Prop 6.7) requires `s = c/q`  `[MACHINERY CHOICE — the framework's own form exists]`

Prop 6.7 is derived for rational readings, giving finite classes of `n` mod `m′`. The framework's own rule is the drift-interval
rule (Prop 6.5, `drift_blocked_iff_interval`), valid for real readings. Prop 6.7 is its rational special case. Any T4 argument
should be stated on the drift intervals.

### B6. "A count of classes cannot succeed"  `[DENSITY REASONING USED TO RULE OUT — reframe]`

`TARGETS_v3` §5.4: *"seven classes of about a quarter each exceed the whole, so a count cannot succeed."* The conclusion that
counting fails is right, but the reason given is a density comparison, the imported frame. The framework's reason is
structural: the ideal is fully clear (φ law), so any obstruction is carried entirely by drift `ε_j·r`, and the question is how
drifts of different runners line up. That is a statement about slots and deviations, not about shares of `p`.

### B7. The per-word certificate (T1a) parametrised by the cascade's words  `[COORDINATE CHOICE — restate]`

**What T1a is, plainly.**
- At order 5 with spread at most `s₀`, the slots `a_j` are integers from 1 to `s₀`: finitely many ideals.
- Each ideal has a box of relocations `ε ∈ [0, 1)³`.
- The cascade's path — which runner is in the way at each scale, and at which lap — stays the same on each cell of that box.
  The cells are cut out by the drift-interval endpoints. On each cell `R` is an explicit function.
- T1a checks, cell by cell and exactly, that `R < 4`.
- I described the cells as "words" (setter, lap sequences) and the check as linear programs over lap periods. In the
  framework's coordinates it is **every ideal with bounded slots, every relocation**.

**Why I asked whether it fits, stated properly.** There were two separate questions. I explained neither:
1. It is a proof by finite exhaustive case check, computer-verified in exact arithmetic. It is a proof, but of the
   enumeration kind. Whether that counts as "on the framework's own terms" is the owner's call.
2. **Its target is `R < 4`, which is B2**, the first window. That is the stronger problem. Re-aimed at the framework's statement
   — for every ideal and relocation, some scale and spine instant are clear — the same cell structure applies, with a weaker
   and more natural target.

**Recommendation:** re-aim T1a at the §0 statement, and state it in slot–deviation coordinates.

### B8. "Lap bookkeeping cannot reach the diagonal"  `[A LIMIT OF A METHOD — scope it]`

`TARGETS` §3.2 is correct, but it is a limit of the growth-potential method (B1's machinery), not of the framework. It says
nothing about the slot–drift form.

### B9. The first-exceedance mechanism  `[NEUTRAL, but aimed at B2]`

"The first step where `R ≥ 4`" is a device for bounding `R`. It inherits B1 and B2. The native analogue is "the first scale at
which no spine instant clears". It says the same finite thing about slots and deviations, without a time bound.

---

## 2. What is not an import (checked, kept)

- **Boundary discipline** (open zones, boundary points evaluated separately): the framework's own rule (§1.2).
- **Localisation and Construction** (Theorems 6.2–6.3): stated in the framework's objects; Lean.
- **The dead-lattice criterion and the first-live bound `⌊s_max/n⌋ + 1`** (`WHY_IT_PREDICTS_v1` §2): the framework's own.
  Stated there for integer readings; the concept is real-valued (B4).
- **The φ(n) reference and drift lines**: the framework's own; real-valued.
- **"Existence" as the name of the open outcome** (ruling Q2): kept. B1 is about the route taken to it, not its statement.

---

## 3. Where the actual boundary is

With B1–B9 removed, the framework's open content is one statement in its own objects:

> **For every ideal (slots `a_j`) and every relocation (deviations `ε_j ∈ [0, 1)`), there are a scale and a spine instant `r` at
> that scale at which no runner's drifted slot `r·(a_j + ε_j)` is within 1 of a multiple of 8.**

What the framework already provides toward it:

| piece | status |
|---|---|
| the ideal is clear at every `r` coprime to 8 except for slot-sharers | PROVED (φ law, `on_ideal_clear`) |
| exact drift intervals per runner, real readings | PROVED (`drift_blocked_iff_interval`) |
| a live scale exists within `⌊s_max/8⌋ + 1` lattices | PROVED (dead-lattice criterion; real-valued form to be written) |
| from the first live scale, a clear spine instant within `c` further lattices | OPEN (T4); observed `c ≤ 3` rational, `≤ 2` irrational |
| how the cascade re-reads slots and deviations at the next scale | DERIVED (item 29); **the owner's scale formula** (items 16, 20, 24) is open |

**The boundary is the scale rule for relocations.** Given `(a_j mod 8, ε_j)`, which scale clears is still unstated. The owner's
items 16, 20 and 24 have been open since 2026-09-14 and are all "the step still to be written down". The termination programme
(B1) went around that step instead of through it.

**A concrete native first question.** At a single scale, which relocations block every spine instant `r = 1, 3, 5, 7`?
- At `r = 1` the blockers are exactly the slot-sharers and the runners in slot 7 with any positive deviation.
- At `r = 3`, `5`, `7` each slot residue blocks an explicit sub-interval of `ε`, with endpoints multiples of `1/r`.

The set of relocations that block all four spine instants is therefore an explicit union of boxes in `ε`-space, one for each
assignment of blocking runners. Characterising it exactly, and showing that the next scale leaves it, is the framework's own
version of both T1a and T4, for irrational deviations too.

---

## 4. Actions

| # | action | status |
|---|---|---|
| A1 | Withdraw "rational readings only" (B3) and objection 1 of §4 (B4) in the targets document | this audit; `TARGETS_v4` |
| A2 | Re-aim T1a from `R < 4` to §3's statement, in slot–deviation coordinates (B2, B7) | owner to confirm |
| A3 | Record T2 (`ManyDifferences`) as correct but of imported proof shape (B1); no further work on growth-potential routes unless the owner asks | owner to confirm |
| A4 | First native computation: at one scale, the exact set of relocations blocking `r = 1, 3, 5, 7`, by slot residues (§3) | proposed |
| A5 | State the dead-lattice criterion and first-live bound for real readings, in Lean | proposed |
| A6 | Items 16, 20, 24 — the owner's scale rule for relocations — are the boundary; bring them forward | owner |
