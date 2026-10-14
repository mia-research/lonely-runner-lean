# Does the joint/marginal reading reframe Existence

*Version 1, 2026-09-20. Answers the question directly: it reframes, it does not close, and it does
not sidestep. What it supplies is a reason why §13's integer-reading branch is the whole problem
rather than one branch among several. Companion to `PROGRESS_ACCOUNTING_LIMIT_v1.md`.*

---

## 1. The reframe, stated exactly

Fix a subject with disparities `d_1, …, d_7 > 0`. Loneliness at `t` is `‖d_i·t‖ ≥ 1/8` for every `i`,
where `‖·‖` is distance to the nearest integer. The map `t ↦ (d_1 t, …, d_7 t) mod 1` is a
one-parameter subgroup of the 7-torus; the closure of its forward orbit is a closed connected
subgroup `H`, and

> **the subject is lonely at some positive instant iff `H` meets the cube `C = [1/8, 7/8]^7`.**

`H` is determined by the **relation lattice** `Λ = { m ∈ ℤ^7 : Σ m_i d_i = 0 }`: it is `Λ`'s
annihilator, of dimension `7 − rank Λ`. Dropping relations enlarges `H`, so the family is monotone in
rank.

This is the view-obstruction reading of the conjecture. It is **standard, not novel**, and it is a
restatement of the definition rather than an imported technique — but it is an import in the sense
§6A cares about only if something is built on machinery from outside. Nothing is, below.

## 2. What it settles, and what it does not

| rank `Λ` | `H` | status |
|---|---|---|
| `0` (disparities rationally independent) | the whole 7-torus | **closes outright**: `H` contains `(1/2, …, 1/2)`, so the subject is lonely near any `t` with every reading near a half-lap |
| `1 … 5` | a torus of dimension `6 … 2` | **not settled here.** `H` only shrinks as rank rises, so these sit between the two extremes; nothing below decides them |
| `6` (all disparities commensurable) | a circle | **is the conjecture.** Rescale to coprime integers `a_1, …, a_7`; the statement is integer LRC at eight runners, with no slack left |

So Existence is **not** sidestepped. At rank 6 the joint condition is the target itself, and there is
no weaker joint statement there to aim at that is not again an equivalence.

## 3. Why rank 6 carries everything — the independence account

`PROGRESS_ACCOUNTING_LIMIT_v1.md` shows runner-additive accounting is pinned at `7/4`. In this
picture that number is the **union bound**: each event "runner `i` is in the way" occupies a quarter
of `H` — every coordinate map `H → T` is onto, since `d_i ≠ 0` — and seven quarters total `7/4 > 1`,
so the bound is vacuous on **every** stratum. Passing to a larger `H` does not soften it.

What differs by stratum is not the bound but the **overlap**:

- At rank 0 the seven events are independent, so the union is `1 − (3/4)^7 = 0.8665 < 1` and the
  clear set has measure `(3/4)^7 ≈ 0.1335`. Independence, not the union bound, is what closes it.
- At rank 6 the seven events are functions of a single circle parameter and the dependence is total.
  The union bound is all that survives, and it says nothing.

> **The obstruction is the failure of independence between the seven in-the-way events, and the
> relation lattice is what measures that failure.**

This is why every additive route returns the same `7/4`: additive accounting is exactly the union
bound, and the union bound is stratum-independent. It is also why depth needs fine denominators
(`CAP_DEFECT_v1.md` §2) — index in the relation lattice is the quantity that varies.

## 4. Where this lands: §13, already

At rank 6 the question is finite and arithmetic, not measure-theoretic. With coprime integers
`a_1, …, a_7`, the clear set on the circle is a set of residues, and its Haar measure is a count over
a modulus. That is **exactly** `MANUSCRIPT_v17.md` §13's integer-reading branch — *"a statement about
two integers: for every profile `S`, is there `s ∈ S` and `A ≡ 1 (mod 8)` with `s ≤ A ≤ 7s` such that
`s'A mod 8s ∈ [s, 7s]` for every `s' ∈ S`"* — which §9 records as **not closed**, with no bound
supplied.

So the reframe does not open new ground. Its contribution is to say **why that ground is the only
ground**: every stratum shares the same vacuous union bound, rank 0 escapes through independence
alone, and rank 6 has no independence to spend. §13's branch is not one case among several; it is the
place where all the dependence is concentrated.

## 5. The rule decision this forces

The order-1 count is capped. The next order is pairwise: the overlap of the events for `a_i` and
`a_j` inside `H`, governed by `gcd(a_i, a_j)` and by `Λ`. Any argument that beats `7/4` has to use
overlaps, and that is a counting argument.

`MANUSCRIPT_v17.md` §6A row six bans measure and density outright. Two things already on the record
bear on whether that row forecloses the route:

- the author's ruling of **2026-09-15**, that such counts are admissible **as tools**, which §9
  records as untouched and still standing; and
- §6A's own test — *"the bound lives in the argument, not in the shape of the statement … A reader
  checking this table should read the proof, not the `∃`"* — which is what Propositions 6.10–6.11
  failed, by concluding a lonely opening exists **without naming or bounding one**.

On that reading, a pairwise count that returns a **named** instant is inside the rules, and one that
concludes `∃` without naming is not. At rank 6 the count is over residues to a finite modulus, so
naming the witness is available in principle.

**This is a decision for the author, not a finding.** Nothing here proposes running such an argument,
and nothing here is evidence that one would work.

## 6. What this does not do

It closes nothing. It supplies no bound. It leaves ranks 1–5 untouched, and it leaves rank 6 exactly
where §13 left it. What it removes is the expectation that reformulating Existence — as a cap, as a
door, as a joint condition — could close it, since every such reformulation has landed on an
equivalence, and the one that was not an equivalence was `DoorFirstLap`, now `[REFUTED]`.
