# Door 3: it is door 4 plus a reduction, not an alternative to it

2026-09-18. Lean: `Flanks.exists_lonely_of_smul`, axiom-clean, build 2443 jobs. Artefacts:
`experiments/n8/door3_v1/`. Door 3 is `ExistenceAt8` — see `ATTACK_SURFACE_v1`.

---

## 1. What door 3 uniquely has

Doors 1, 2 and 4 reach door 3 by `iff`s, so none of them loses anything — **except that door 4's
residue form needs whole-number differences.** Door 3 is stated over `Finset ℝ`. Its distinctive
content is therefore the **real** case, and there is **no real-to-integer reduction anywhere in the
tree**: `Irrational.lean` supplies specific irrational witnesses (`1/(8(4−π))`, `3/(8δ)`), not a
reduction.

The structure the real case has, and the residue form cannot see: the closure of the orbit
`{(d₁t, …, d₇t) mod 1 : t ∈ ℝ}` is a closed connected subgroup of the 7-torus, determined by the
rational linear relations among the `dᵢ`.

## 2. Where the difficulty actually sits  `[VERIFIED — numerical, 1e-6 grid]`

| case | attainable `max_t min_i ‖dᵢt‖` |
|---|---|
| `ℚ`-linearly independent (generic reals) | **0.39 – 0.46**, 60/60 sets, none below `1/8` |
| six integers + one irrational | worst **0.200** over 40 sets |
| fully commensurable — the three tight sets | **exactly 0.125** |

Threshold is `0.125`. **All of the difficulty is in the fully rationally dependent case**, which after
scaling is the integer case — that is, door 4. Any genuine irrational freedom leaves a margin of
1.6× to 3.7×.

The reason is visible in the first row: with `ℚ`-independent speeds the orbit is dense in the torus,
so some `t` puts *every* runner near `1/2`. Loneliness is then not marginal, it is comfortable.

## 3. The two halves of the reduction

**Commensurable half — done.** `lonely_smul` makes loneliness scale-free, so a difference set whose
members are all `c` times a whole number inherits Existence from the whole-number set:

    Flanks.exists_lonely_of_smul : 0 < c → (∃ s > 0, Lonely n ds s)
                                         → ∃ s > 0, Lonely n (ds.image (c * ·)) s

`[PROVED]`, axiom-clean.

**Incommensurable half — not done, and it has a cost.** It needs a dense-orbit theorem on the
`k`-torus (Kronecker). **mathlib does not carry one**: `Mathlib/Dynamics/Ergodic/AddCircle.lean` is
one-dimensional, and a search for a multi-dimensional Kronecker or Weyl equidistribution statement
returns nothing usable. Building it is real work, and it is work on a standard classical theorem
rather than on this framework's objects.

Partial machinery does exist for the mixed case: `off_lattice_of_irrational_ratio`,
`lonely_opening_of_free_off_lattice` and `lonely_of_flank_unkillable` already settle a flank at which
one runner is off the lattice and the rest are on it — which is the `[C]` row of §2.

## 4. Verdict — corrected

**An earlier draft of this file said the real case is "a separate, later obligation". That is wrong,
and the correction matters.**

Checked against the hypotheses rather than assumed:

| statement | integrality hypothesis? |
|---|---|
| `ExistenceAt8`, `ExistenceAt8_cascade`, `ExistenceAt8_flank`, `CascadeCapped`, `FiniteActiveMembership` | **none — all five are over `ℝ`** |
| `lonely_iff_exists_flank`, `lonely_iff_run_ends` | **none — over `ℝ`** |
| `lonely_iff_bounded_search`, `lonely_iff_emod_search` | `hint : ∀ d ∈ ds, ∃ a : ℤ, d = a` |

So **the incommensurable case is not an outstanding obligation of the problem.** Every door, and the
flank form `ExistenceAt8_flank` itself, is stated and reduced over the reals. A proof arriving through
the cascade (doors 1, 2, 5) or through the flank form as stated settles the real case with no
reduction at all.

**What the Kronecker step actually costs is the use of one tool.** The residue reformulation —
`lonely_iff_bounded_search`, `lonely_iff_emod_search`, `clear_at_int_flank_iff_emod_b` — carries
`hint`, so it speaks only about whole-number differences. Choosing to work in it is what would incur
the lift. That is a property of the tool, not of the target.

**The real trade-off**, stated plainly:

- Work in the residue form: strong arithmetic (progressions mod `b`, intervals of relative length
  `3/4`, six conditions not seven) — and you owe the commensurable-to-real lift, whose remaining half
  needs a `k`-torus dense-orbit theorem mathlib lacks.
- Work over `ℝ` directly, in `ExistenceAt8_flank` or the cascade: no lift is ever owed — and you give
  up the residue arithmetic.

**Neither is a gap.** §2's measurement stands and is the useful part: all the difficulty is in the
fully commensurable case, and any irrational freedom leaves 1.6× to 3.7× of margin. That says the
incommensurable case is mathematically comfortable however it is reached — which is exactly why
treating it as an outstanding obligation was a mistake.

**Ordering unchanged:** close door 4. If it closes in the residue form, the lift is then owed and its
mathematics is easy; if it closes in the flank form over `ℝ`, nothing is owed.
