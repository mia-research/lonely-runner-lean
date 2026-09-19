# How the proofs fit together, and exactly what is left

Lean added here: `experiments/n8/CardSix_v1.lean` (2 theorems, axiom-clean, built **on
`intLRC_seven`** — so the whole chain through our own order-7 proof is clean).
Scripts: `card_six_v2.py`, `blocker_five_v1.py`, `subdensity_check_v1.py`.

---

## 1. The target does not require the candidate machinery

Existence at a subject is: a **real** `t` with `circDist(dᵢ·t) ≥ 1/8` for the seven differences.
The candidate/opening apparatus (`ArithForm`, `finite_check`, `edge_witness`) is a **normal form
for the witness**, not a requirement. That matters, because it means in-house LRC theorems at
lower order apply directly, with no lattice conversion, whenever the constraint count is low
enough.

## 2. Six constraints are already covered — **[PROVED]**

`intLRC_seven` (ours, axiom-clean, zero `sorry`) gives six distinct positive speeds a real `t`
with `circDist ≥ 1/7`. And `1/7 > 1/8`.

**[PROVED — `CardSix.lonely_at_eight_of_six`]** any subject whose differences collapse to at most
six distinct values is lonely at order 8. **[PROVED — `CardSix.margin_to_spare`]** with
`1/7 − 1/8 = 1/56` to spare at every speed.

Since `circDist(d·t) = circDist(−d·t)`, the collapse happens exactly when the subject is the
**midpoint** of two other runners. **[VERIFIED]** 600/600 distinct-speed sets of size ≤ 6 reach
margin ≥ 1/7. Frequency of midpoint subjects: 43.2% at range ±10, falling to 2.55% at ±200 — a
real class, shrinking with spread.

## 3. At a candidate, only **five** readings can block — an order-**6** count

`BlockerCount.self_never_blocks` frees the generating reading `s_k` at its own candidates;
`BlockerCount.unit_never_blocks` frees the unit reading throughout band 0. That leaves `n−3 = 5`.

**[VERIFIED — 8,337,943 band-0 candidates]** the generating reading and the unit reading block
**0** times, and the maximum active blocker count observed is exactly **5**.

Five speeds is an **order-6** question, and `intLRC_six` is ours and axiom-clean: margin `1/6`,
against the `1/8` needed. **The margin is already there.** What is not automatic is that the
order-6 witness is a *candidate* rather than an arbitrary real.

## 4. So the whole remaining gap is one conversion

| step | status |
|---|---|
| reduce to candidates | **proved** (`finite_check`, `ArithForm.near_iff_int`, `witness_normalised`) |
| at most 5 active blockers per candidate | **proved** (`BlockerCount`, `n−3`) |
| 5 speeds have a real witness at margin `1/6` | **proved** (`intLRC_six`, in-house) |
| turn that real witness into a candidate | **proved for moduli `≥ 10`** (`DivisorOrder6.clear_of_order6`) |
| … at moduli `≤ 9` | **OPEN** — and there, clearing is pure non-divisibility (`ReducedOpen.small_clear_iff`) |

Everything but the last line is proved. The open frontiers are that one line.

**And there are seven independent attempts.** Each generating reading `s_k` gives its own order-6
problem. **[VERIFIED — 4,000 profiles]** the number of generating readings admitting a clear
candidate is **minimum 3, median 6, maximum 7**, and **never 0**.

## 5. Why the three closing mechanisms fail exactly where they do

Every class that is closed is closed by one of three mechanisms, and each open frontier is where
all three fail:

| mechanism | closes | fails on the frontiers because |
|---|---|---|
| **orbit** — the spine clears all four unit points at once | Branch A (`8 ∤ s` throughout) | a collider pins the residue to `0` and kills every spine point, and with it the whole `m`-lattice (`CanonicalCandidate.collider_kills_lattice`; `L(m)`, `⌈m/4⌉`, `⌈3m/8⌉` each clear **0.00%**) |
| **count drop** — fewer constraints, lower order, bigger margin | ≤ 6 distinct differences (order 7); divisor-closed, two readings free (order 6) | the count drops to 5 *at a candidate*, but converting the order-6 real witness to a candidate costs margin, and at moduli `≤ 9` the cost exceeds the slack |
| **explicit candidate** | ratio-7 windows (`FirstLap`); every quotient `≤ 9` (`q = 1`) | no explicit candidate reaches **mixed scales** — `q = 1` fails from `b = 10` (`clear_one_fails`), and the ratio-7 window cannot span both ends |

## 6. What will not close it

**[REFUTED]** Sub-density. "Mean active blockers `≈ 1.2–1.5`, well below 6, so blockade is
impossible" does not follow: on the extremal shadowed set, flank `e = 3` has mean blocker count
**exactly 1.0000** with every opening blocked, and the one *clear* flank has the **highest** mean.
This is the counting route already on the do-not-re-attempt list.

**[REFUTED]** Integrality forcing. `GapRule`'s `N ≥ 1` branch is sound, but `N ≤ 0` is the overlap
case and overlap *is* blockade — **551 of 756** zone pairs on those flanks have `N ≤ 0`. The rule
bounds gaps that exist; it does not make them exist.

**Structural limit of the toolkit.** `finite_check` makes the question decidable,
`near_iff_int` restates it exactly, `GapRule` bounds existing gaps, and `edge_witness_both` is
conditional on the clear set already being non-empty. **None can establish non-emptiness** — and
that is what is needed. Every closed class was closed by something that *produces* a witness.

## 7. The single remaining target, stated exactly

> Fix a generating reading `s_k`. Order 6 supplies a real `t` with margin `1/6` against the five
> active blockers. Round it to a candidate `A = 8q+1`. The rounding is proved to preserve
> clearing at every modulus `≥ 10`. **Show it can be chosen to also satisfy the non-divisibility
> conditions at the moduli `≤ 9`** — `b ∤ q`, and `b ∤ (q+1)` for `b ∈ {8,9}`.

For `b = 2` this needs the parity of `q` forced, which costs a margin `> 1/4` that no order-6
bound supplies — so the answer must come from *where* the rounding lands, not from how much
margin it has. Seven generating readings give seven attempts at it.

That is one statement, it serves both open frontiers, and everything around it is proved.

Existence at order 8 remains open.
