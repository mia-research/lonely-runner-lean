# The attack surface: five equivalent doors to Existence at order 8

2026-09-18. Companion to `THE_OBLIGATION_v1.md`, which pins the obligation and tabulates the routes
that have failed. This file is the other half: **where to push**, with what each door would require.

All five are proved equivalent in the tree. **Any one of them closes the problem.** Pick by shape,
not by apparent difficulty — they are the same difficulty.

---

## 0. What closing any door buys

`existence_of_capped : CascadeCapped → ExistenceAt8`, proved, axiom-clean. And `ExistenceAt8` **is**
LRC at order 8 — derived from the conjecture in `EXISTENCE_FRAME_CHECK_v1` by evenness and
duplicate-collapse and nothing else, and checked against a direct simulation of the conjecture on
3,200 (configuration, runner) pairs with **0 disagreements**.

So a term of any of these types is the theorem. There is no further obligation behind it.

## 1. The five doors

| # | door | statement | Lean |
|---|---|---|---|
| 1 | **uniform cap** | `∃U, ∀N, move^[N] b ≤ U` | `CascadeCapped` |
| 2 | **arrival** | `∃N, move^[N] b` is a fixed point | `ExistenceAt8_cascade` |
| 3 | **bare existence** | `∃s > 0, Lonely 8 ds s` | `ExistenceAt8` |
| 4 | **flank form** | `∃e ∈ ds, ∃k, Lonely 8 ds (flankOpening 8 e k)` | `ExistenceAt8_flank` |
| 5 | **finite activity** | each `d ∈ ds` is in the way at only finitely many steps | `FiniteActiveMembership` |

Equivalences: `target_forms_agree` (1↔2↔3), `target_flank_agrees` (4→3), `existence_of_capped` and
`capped_of_existence` (1↔3), `cascade_of_FAM` and `FAM_of_existence` (5↔3). All axiom-clean.

## 2. What each door would require

**Door 1 — uniform cap.** A quantity bounded above that the cascade increases. *Do not attack via
`nearest_reading_recurrence`.* It gives `m·t_N ≤ (1/8)·∏(Q_j+1/8)/(Q_j−1/8)`, and that product
**necessarily diverges** for an infinite cascade: `τ = m·t` rises by at most `2h/ρ ≤ 1/4` per move, so
`τ` is at most linear in `N`, so `Q_j` is at most linear, so `Σ1/Q_j ~ log N`. The bound goes vacuous
exactly where it is needed. Measured: already 2× loose after 28 moves on the §6.7 climb, with actual
`τ` growth at 5.7% of even that linear ceiling.

**Door 2 — arrival.** A terminating measure. Every counting measure tried dies at `2k < n`; note
that `TerminationThree` and `TerminationFour` both live *outside* that regime and work anyway, so the
wall belongs to the method.

**Door 3 — bare existence.** The classical statement. Least structure to work with; carried mainly
because it is what an outside reader recognises. **It imposes no extra obligation**: all five doors
carry no integrality hypothesis, so the real case is settled by any of them. Only the *residue tools*
(`lonely_iff_bounded_search`, `lonely_iff_emod_search`, `clear_at_int_flank_iff_emod_b`) carry
`hint`, and using them is what would owe a real-to-integer lift. See `DOOR3_v1` §4.

**Door 4 — flank form. This is the one I would attack.**  *(Worked extensively since: see
`DOOR4_v1` and `RULE_TABLE_v1`.  Two named instants are now proved and cover 94%; the residue always
has a named instant with observed `c ≤ 17` but no proved bound.  `DOOR4_v1` §13 rules §§5, 8, 11, 12
of that file imported density rather than native.)* The residue work made it pure arithmetic
with no trajectory in it. Over whole numbers, `lonely_iff_emod_search` reads:

> `∃ b ∈ ds, ∃ k < b, ∀ a ∈ ds:  b ≤ a·(8k+1) mod 8b ≤ 7b`

Equivalently: **seven Bohr sets in `ℤ/8bℤ` cannot cover the progression `u ≡ 1 (mod 8)`.** Each
runner blocks `2b−1` of the `8b` residues; the flank blocks none at its own openings, so it is six
blockers against `b` candidate openings, and `6 × 1/4 = 1.5 > 1` — counting alone will not do it. The
content has to come from the arithmetic of the interval `[b, 7b]`, which is where CRT fails and where
the structure lives. Known obstruction: intervals do not factor under CRT, so splitting `8b` into
prime parts does not split the condition.

**Door 5 — finite activity.** Per-runner and combinatorial rather than a global bound. Mechanism in
hand: `nextOpening_le_move` (below) gives that a runner's lap strictly increases between successive
activities, so its active set is finite exactly when its lap is bounded.

## 3. The FAM proposal, adjudicated

A route was put forward: prove **Finite Active Membership** — each fixed difference is active only
finitely often — and Existence follows. Three parts, assessed separately.

**Part 1, simultaneous exhaustion — TRUE, and it was missing.** `move` folds `max` over `ds`, so it
reaches `nextOpening n d t` for *every* `d` in the way at `t`, not merely the setter attaining the
maximum. Verified 0 violations in 3,853 active-runner observations. The tree had only
`le_move : t ≤ move t`; the stronger fact was **not** stated. Now added:

    MomentIterationN.nextOpening_le_move : d ∈ ds → inWay n d t → nextOpening n d t ≤ move n ds t

`[PROVED]`, axiom-clean. **A genuine contribution from the proposal.** Its corollary — a runner's lap
strictly increases between successive activities — was also verified, 0 violations.

**Part 3, FAM ⟹ Existence — VALID.** Seven finite sets have a finite union; a non-terminating cascade
has someone in the way at every step, so `ℕ` would embed in that union. Formalised as
`LRC.Spec.cascade_of_FAM`, `[PROVED]`, axiom-clean.

**Part 2, FAM itself — equivalent to the target, not weaker.** This is the point on which the
proposal turns, and it does not hold. `LRC.Spec.FAM_of_existence` proves the converse: if the cascade
arrives at step `N`, the iterates are constant thereafter and nothing is in the way, so every active
set sits inside `range N`. So **FAM ⟺ Existence**, and "prove FAM" is a restatement of the
obligation, not a reduction of it.

The mechanism makes it concrete: by part 1, each activity of `d` strictly increases its lap, so
`|S_d| < ∞` ⟺ `d`'s lap is bounded ⟺ the cascade is capped. Door 5 is a door, not a shortcut.

### 3a. Audit of that equivalence

Because `FAM_of_existence` is what denies the proposal its reduction, it was audited for the ways it
could be manufactured rather than true.

| check | result |
|---|---|
| `sorry` anywhere in `Spec/` or `Cascade/` | none |
| axioms of `cascade_of_FAM`, `FAM_of_existence`, `FAM_iff_existence` | `[propext, Classical.choice, Quot.sound]` |
| **is FAM proved outright?** | **no** — it occurs only as a hypothesis of `cascade_of_FAM` and a conclusion of `FAM_of_existence`. Were it provable, `cascade_of_FAM` would already have closed Existence, and the gate reports Existence unstated |
| is FAM vacuous (the active sets always empty)? | no — 3,853 active-runner observations across 3,002 cascades |
| is the equivalence prose or machine-checked? | machine-checked: `FAM_iff_existence : FiniteActiveMembership ↔ ExistenceAt8` |
| does the proof lean on anything unsound? | `iterate_stable`, `lonely_of_fixed`, `target_forms_agree` — all pre-existing and axiom-clean |

**Faithfulness of the definition**, which no build can check. The proposal sets
`S_d = { j ∈ ℕ : d ∈ I(C_j) }` with `C_0 = 1/d_min`, and FAM is `|S_d| < ∞` for every `d`. The Lean
definition is `{j : ℕ | inWay 8 d ((move 8 ds)^[j] (1/(8·m)))}.Finite` for every `d ∈ ds`, with `m`
the minimum. `I(C_j)` is the set in the way at step `j`, which is `inWay`; and the proposal's `C` is
`8t` in its own normalisation, so its `C_0 = 1/d_min` is this `t_0 = 1/(8·d_min)` — the same instant.
No hypothesis was added and none dropped.

**What this does and does not say about the proposal.** It denies it the status of a *reduction*.
It does not touch parts 1 and 3, which are sound and are adopted, one of them supplying a theorem the
tree did not have.

**On the ratifications.** The proposal cites a tool that "ratified TRUE" both the simultaneous
exhaustion and FAM. The same tool asserted `K ≤ 15` for every difference set; the §6.7 climb takes
**K = 28** and the §6.9 row **K = 23**, both arrangements from this manuscript. Those ratifications
therefore carry no evidential weight here. Parts 1 and 3 stand anyway, on their own mathematics,
which is why they are adopted above.

## 4. What is new in the tree from this

| declaration | what it says |
|---|---|
| `MomentIterationN.nextOpening_le_move` | one move clears every runner in the way, not only the setter |
| `LRC.Spec.FiniteActiveMembership` | the fifth wording |
| `LRC.Spec.cascade_of_FAM` | FAM gives the target |
| `LRC.Spec.FAM_of_existence` | the target gives FAM — so it is not weaker |

Build 2547 jobs, all axiom-clean `[propext, Classical.choice, Quot.sound]`.

## 5. The standing rule, restated

A proposal that reduces Existence to a new statement should be checked **in both directions** before
it is adopted as a reduction. If the converse holds, it is a fifth door, not a bridge. Doors are
useful — they offer different shapes to attack — but they do not shorten the work.
