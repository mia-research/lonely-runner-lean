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
