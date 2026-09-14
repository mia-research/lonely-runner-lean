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
