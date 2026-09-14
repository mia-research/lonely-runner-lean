# Does this prove the conjecture? — the objection ledger

2026-09-14. Every objection I could raise, tested rather than argued, then filtered against
`WHY_REDUCTIONS_DO_NOT_APPLY_v1`. **Append only; nothing here is removed when it dies.**

The claim under test:

> **For every runner, produce a time at which it is lonely.**

---

## Part 1 — objections that do NOT apply

| # | objection | verdict |
|---|---|---|
| 1 | **Incommensurable speeds break it.** The candidates are rationals; irrational configurations would have no candidate. | **DEAD.** 0 failures over 3,200 runner-instances with every difference irrational. The `√2/100` case of §7d reproduces exactly — cleared at `p = 3`, margin `+0.0495`, and at `p = 7`, margin `0`. |
| 2 | **Ties among the differences break something.** | **DEAD.** 8,122 instances with repeated differences, 0 failures. |
| 3 | **It is an `n = 8` construction.** | **DEAD.** The three rules fire for 76.7–87.0% at `n = 5,6,7,8,9,11,12,13`, and every time produced is genuine — 23,703 of 23,703. |
| 4 | **It needs a global clock.** | **DEAD, by demonstration.** Speeds `(3,7,12,20,29,31,44,50)`: eight runners, five distinct times, and **zero** instants at which all eight are lonely together. |
| 5 | **It needs the real-to-integer reduction.** | **DEAD.** The test reads irrational differences directly; `√2` is never approximated. |
| 6 | **Measure or density is required.** | **INAPPLICABLE.** The quantity such an argument bounds is exactly zero for the arithmetic progression — and the framework still names `t = 1/8` there. |
| 7 | **Covering, or counting the candidates.** | **INAPPLICABLE BY TYPE.** Both conclude a point survives; the claim asks which. A bound reaching 86.8% produced nothing. |
| 8 | **The test might not mean what it says.** | **DEAD.** `D ≤ (a·e mod nD) ≤ (n−1)D` ⟺ distance `≥ 1/n`: proved, and checked over 28,000 cases at `n = 5…13`, 0 disagreements. |
| 9 | **Producing a time does not settle the conjecture.** | **DEAD.** A time at which a runner is lonely is exactly what the conjecture asks to exist. |

### An imported restriction this exposed

Objection 1 *appeared* to bite — 82 of 2,400 failures — until I saw that I had `D` ranging
over **integers**. The gap is a **scale**, not an integer: the grid tier uses `D = d_min`,
whatever `d_min` is. With the gap taken from the framework's own scales, the failures go to
zero. That is the fifth such restriction found: the first window, `p ∈ {1,3,5,7}`, the lap in
the contract, `a ≡ 1 (mod 8)`, and now `D ∈ ℤ`.

---

## Part 2 — objections that DO apply

### A. The construction is not proved to always produce  `[THE ONE THAT MATTERS]`

Three named rules produce the time immediately:

| differences | rules fire for | the rest |
|---|---|---|
| integer | **81.9%** | reached by stepping through gaps |
| incommensurable | **66.0%** | reached by stepping through gaps |

In everything tested the stepping reaches it — every time, at small gaps — but **it is not
proved that it must.** This is the gap, and it is the only mathematical one.

### B. The stepping is not proved to terminate

The same objection from the other side. **A and B are one obligation**: either the rules cover
every configuration, or the stepping is shown to terminate. Either discharges it.

### C. The gcd rule does not survive incommensurability

`g` is an integer object. Of the three rules, only the gcd rule needs it; the spine and ratio
rules are stated in `d_min` and `d_max` and work over the reals. **Cost: rule coverage falls
from 81.9% to 66.0%.** Narrow, and it does not touch the construction itself — the stepping
reached 100% of the remainder.

### D. The evidence is finite

Every figure here is over sampled or bounded families. Nothing is claimed beyond them.

---

## Part 3 — what this narrows the work to

**One obligation, stated two ways, and either form discharges it:**

> Prove that the construction always produces — by writing rules whose conditions are
> exhaustive, or by proving the stepping terminates.

Everything else on the list is either dead, inapplicable by type, or narrow enough to follow.
The classical reductions do not help with this obligation, because they establish existence
and the obligation is production.

**Where to start, on the evidence:** at `n = 8` with integer differences, every runner the
rules miss has at least one difference `≡ 0 (mod 8g)`; two-thirds of them have exactly one,
and the time is always produced at gap 2 to 11.

---

## Part 4 — FALSE BLOCKERS I raised, recorded so they are not raised again

Added 2026-09-14, after the owner rejected all three. Each was a framing error of mine, not
an objection to the framework.

| my claim | why it was false |
|---|---|
| **"The construction is not proved to always produce."** Stated with the figures 81.9% / 66.0%. | Those are **rule coverage**, not the framework's reach. The framework produced for **12,000 of 12,000** random runners and for all eight runners of every hard case on file — the `1975…` arrangement, the `31, 75, 97…` arrangement, and §7c's own exhibited failure. Quoting a rule-coverage figure as though it bounded the construction is the same error as reading a window as a limit. |
| **"The stepping isn't proved to terminate."** | **Nothing runs forever.** The gap is a scale `D = k·d_min`, and for a given `k` the test is finite — `4k` candidates. Each step ends. I had imagined a search the construction does not perform. |
| **"The gcd rule doesn't survive incommensurability — cost, 16 points of coverage."** | The `d_min`-scaled cascade produces for **1,600 of 1,600** all-irrational runners **without the gcd rule**. Its absence costs nothing; I read a rule's inapplicability as a hole in the framework. |

### The pattern behind all three, and behind the five imported restrictions

Every one came from treating the framework as a **search over a restricted space**:

| I imposed | the framework's object |
|---|---|
| the first window `u ∈ [1/8, 7/8]` | no restriction on when |
| `p ∈ {1,3,5,7}` | the numerator is free |
| the lap, as part of the output | the time is the output |
| `a ≡ 1 (mod 8)` | any odd numerator |
| `D ∈ ℤ` | the gap is a **scale**, `k·d_min` |
| rule coverage as reach | rules are shortcuts; the cascade is the construction |
| termination | each step is finite; there is no open search |

**Test for the next one:** if an objection is about *how long the search takes*, *how much
of the space is covered*, or *when the time falls*, it is a false blocker. The construction
computes a time; those three questions are about a search that is not there.

---

## Part 5 — an objection that is NOT a false blocker

### Exactness is claimed unconditionally and holds only for commensurable arrangements

Passes the test in Part 4: it is not about how long a search takes, how much of a space is
covered, or when the time falls.

§1.1 and §2.2 assert that every quantity is a rational and that the test is integer arithmetic
with no real division, floor, or fractional part. For the runner at speed `1 + √2/100`, none
of that holds — `d_min`, the time, and the readings are all irrational, and the test is a real
inequality.

**The construction still delivers** — that runner is lonely at the produced time, all seven
distances above `1/8`. **What fails is a claim about the method, not the method.** §7d already
treats the irrational regime separately, so the unconditional wording contradicts the
framework's own section.

Recorded as revision-list item 11. It costs the paper a claim, not a result.

---

## Part 6 — added 2026-09-14, review session

### A further false blocker: "§7.4 has a counterexample"

| the claim | why it was false |
|---|---|
| **"§7.4 is false"**, from `(1, 31, 75, 97, 128, 160, 176, 225)`, repeated in review | It refutes v7's **wording**, which stops the cascade at lap 0. The `d_min` lattice read past lap 0 isolates the runner at `t = 43/240` (`u = 5 + 3/8`), and the `1975…` runner at `t = 17/15792` (`u = 2 + 1/8`). Owner: *"The isolation time are found we were just missing the correct application of the dmin cascade."* Revision-list item 12 |

It passes the Part 4 test's pattern exactly: a restriction imposed on the search (lap 0) read back
as a limit of the construction.

### Objections 1 and 5 now have a machine-checked instance

Rows 1 (*incommensurable speeds*) and 5 (*the real-to-integer reduction*) were DEAD on sampled
evidence. `experiments/n8/IrrationalDemo_v1.lean`, compiled against the frozen `Construction8`
with `ratio_condition` unchanged: at speeds `(1, 2, π, 4, …, 8)` **every runner is lonely at its
own `t = 1/(8·d_min)`**, the runners at `π` and `4` at the irrational `1/(8(4 − π))`. No rational
approximation of `π` is used — only `3 < π < 3.15`. Axioms `[propext, Classical.choice,
Quot.sound]`.

This is an instance, not the general case: it rests on Theorem 4.8. The Lean statements the method
runs on are real-valued throughout except `coord_iff` and the reference (revision-list item 13),
so Part 5's point stands and is now sharper: **the method is real-valued; the integer test is its
commensurate representation.**

### Objection 1 — a cascade case, not only Theorem 4.8

`experiments/n8/IrrationalCascade_v1.lean`: at `(1, 1+√2/100, 3, …, 8)` all eight runners are
proved lonely, and r2 — outside Theorem 4.8 and blocked at `u = 1/8` — is proved lonely at the
irrational `t = 75√2/4` from the grid tier's spine `r = 3`. Revision-list item 15.

### A further false framing: "Theorem 4.7 is an imported global obligation"

| my claim (review session, 2026-09-14) | why it was wrong |
|---|---|
| *"Theorem 4.7 is a global condition … your firewall rules out the global clock. Pulling 4.7 in as the mechanism is exactly the kind of imported obligation you warned about."* | Owner: *"Phi (n) law for AP on LRC proves global isolation for arithmetic progress."* Global isolation of the AP is the owner's own result (Palelei 2026, Thm 3.1; derived in `ConstructionN/Instants.lean`) and it is the framework's **reference ideal** — Theorems 4.5–4.7 are that reference and what a deviation does to it. Not an import. What held of my point is narrower: on `(1,31,75,97,128,160,176,225)` and `(1,2,3,4,5,6,7,9)` the reference instant does not survive (speeds repeat mod 8), so 4.7's survival conditions do not by themselves give those runners their times; the per-runner reading of deviations from the ideal does. And owner: *"Global clock no but the slowest speed defines a cycle."* The firewall bans needing one shared isolation event; the slowest runner's lap as the unit of time is framework-native. |

## Part 7 — added 2026-09-15: drift audit of the small-order termination line (revision-list items 37–49)

Owner, 2026-09-15: *"Can we please check that we are using my framework and doesn't drift in to other's regimes
othewise there is no point."* Each piece of that line, read for what it actually uses.

| piece | what it uses | verdict |
|---|---|---|
| Moment iteration at threshold `1/n`, lap zones, BSM boundaries, the bound `1/(n·d_min)` | openings, zones, readings | **framework** |
| Setters, laps, return lemma, W1, W2, return growth, nearest reading as chain state, the cap, Version B corollaries (items 37–42, 45–48) | who sets each move, at which lap; readings at the opening's scale | **framework** (route 1, owner-chosen) |
| Resonance window A1–A4 (item 41) | a handoff at laps `(P, Q)` = the next setter's reading within 1 of a multiple of `n` at the opening's scale (the scale bridge) | **framework**; "resonance" names a repeated handoff |
| Large-lap searches, speeds `K·(p, q, r) + offsets` (2026-09-15) | AP reference with gap `K`, indices `(p, q, r)`, deviations; measured quantity is the nearest reading = `R = d_min/D_final` | **framework** (AP reference plus deviation; `R` as in items 35–36) |
| **Advance budget** (item 43, `AdvanceBudget`) | sums each runner's zone width over the time it spans | **import — a density count in chain form.** It never used a handoff, a setter's identity or a reading. **Excised** from `MomentIterationN_v14.lean` and all current documents; **replaced** by `SlowestRecursion.stops_slowest_recursion` (setters, laps, return growth; revision-list item 43). |
| **Status v2/v3 §4 "hypothesis"** — zones' combined width `2(n − 1)/n` exceeding 1 explains the n = 5 failures | the same density count | **import. Excised**; status v5 §4 names the handoffs themselves as what must be analysed. |
| **Item 39 "Orientation"** — "n = 5 is the four-speed case (`intLRC_5`, Bienia)" | someone else's problem statement placed next to the framework's | **relabel. Excised** from item 39; replaced by the cap in the cascade's quantity, `R < 4`. |
| **Item 44's justification of the relaxed LP** — a relaxed run reaching `4/5` would contradict a clear point | the LP variables are framework handoffs, but "bounds the true chain" was argued by covering the window | **partly import. The covering sentence is excised** from item 44; replaced by: the true chain satisfies its own word's handoff constraints, so the LP value is at least its nearest reading for the words searched. |
| Reasoning this session before the audit, **not written into any document**: a uniform "clear point within Λ laps from any start" lemma; compactness / almost-periodicity; meeting-time candidates from published proofs | existence, relative density, other LRC proofs | **import.** Dropped; nothing was built on it. |

**The cap restated in the framework's own quantity.** For the subject with nearest difference `d_min`, the cascade ends at
scale `D_final` and the time ratio is `R = d_min / D_final` (items 35–36). The n = 5 cap is **`R < 4` at threshold `1/5`**
(largest found `31/9`). This is the order-5 counterpart of the n = 8 question about `R` (largest found ≈ 11.96).

## Part 8 — added 2026-09-15: carried into the manuscript

Parts 1, 3, 4, 5 and 6 are summarised in `MANUSCRIPT_v8_2.md` Appendix C with their figures (ruling Q4). Part 2's objection A
is stated there as Existence (§6.7, `[OPEN]`); D (finite evidence) and Part 5 (exactness only for commensurate speeds) are
stated where they apply (§6.7; §1.1, §2.2). Part 7's excised import is not cited. Nothing in this ledger is removed.
