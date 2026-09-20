# Does the joint/marginal reading reframe Existence

*Version 2, 2026-09-20. Supersedes v1. **§5 of v1 was wrong and is withdrawn here**: it proposed
pairwise overlap as the next order of argument, which Appendix A routes 6–9 and 10–14 had already
closed with measurements. v1 is kept as the record of what was claimed. Everything else is unchanged.
Companion to `PROGRESS_ACCOUNTING_LIMIT_v1.md`.*

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

## 5. WITHDRAWN — the pairwise route was already closed

**v1 §5 said** that beating `7/4` requires overlaps, that overlaps are a counting argument, and that
§6A's ban therefore had to be weighed against the 2026-09-15 tools ruling. **That was wrong, and the
error was mine: the route had already been tried and closed, with measurements, in Appendix A.**

- **Hunter–Kounias on the overlaps** (routes 6–9, closed v12). *"The obvious non-counting route."*
  Forcing a gap needs a spanning-tree sum above `4.5` over six edges. Measured exactly
  (`experiments/n8/overlap_tree_v1.py`, 400 profiles from `[2,200]`): best tree `3.1023`, so the
  bound lands at `7.3977` where `6` is needed — *"short by 1.40, and not close."*
- **Counting, in every form** (routes 10–14, closed v13). The joint density of the solution set sits
  **below** the product of the pairwise conditionals, ratio as low as `0.716`, violated in 2,594 of
  3,000 chain profiles (`experiments/n8/telescope_v1.py`). *"The constraints reinforce one another's
  badness, so no independence-flavoured argument and no bound assembled from pairwise conditionals
  can close this."*

So the dependence does not merely fail to help — it runs the wrong way. §4's account of rank 6 as the
stratum with no independence to spend stands; what does not stand is v1's inference that the next
order of the same accounting could recover it.

**No rule decision is forced.** The tension v1 raised between §6A's ban and the 2026-09-15 tools
ruling does not arise, because the route the tension was about is closed on its own merits. §6A's
ban is also not merely stylistic — see §5A.

## 5A. Why the density ban is earned, not a preference

Measured exactly on `(0, 2]` (`experiments/n8/clear_set_measure_v1.{py,out}`):

| difference set | measure of the clear set |
|---|---|
| **AP `1,…,7`** | **`0`** — the clear set is exactly the eight points `1/8, 3/8, 5/8, 7/8, 9/8, 11/8, 13/8, 15/8` |
| `(2,6,8,9,11,14,15)` | `29/240` |
| `(2,3,5,7,8,13,16)` | `41/280` |
| `{49,205,234,256,286,323,366}` | `51907461343/196705850880 ≈ 0.2639` |

In the extremal case the object being sought is a **finite set of isolated points**. No measure,
density or "there is room" argument can locate a measure-zero target, whatever constant it achieves.
That is Appendix A route 1, stated there as *"the set on which such a comparison would have to find
room has length zero in the case that matters. Any argument must name an instant."*

This is the load-bearing point for §6A rows six and seven, and for the exhibit requirement: **naming
the witness is forced by the AP, not imposed by preference.** `[VERIFIED — exact rational
arithmetic]`

## 6. What this does not do

It closes nothing. It supplies no bound. It leaves ranks 1–5 untouched, and it leaves rank 6 exactly
where §13 left it. What it removes is the expectation that reformulating Existence — as a cap, as a
door, as a joint condition — could close it, since every such reformulation has landed on an
equivalence, and the one that was not an equivalence was `DoorFirstLap`, now `[REFUTED]`.
