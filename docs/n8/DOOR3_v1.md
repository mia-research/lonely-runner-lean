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

## 4. Verdict

**Door 3 is not an alternative attack surface. It is door 4 plus a reduction.** Its extra content is
exactly the incommensurable case, and that case is the *easy* one mathematically — margins of 1.6× to
3.7× — while being the expensive one to formalise, because the tool is missing from mathlib.

So the ordering is: **close door 4 first.** The real case is then a separate, later obligation whose
mathematics is comfortable and whose cost is library-building, not discovery. Recorded here so that
door 3 is not mistaken for a shortcut, and so that the missing Kronecker step is not rediscovered as
a surprise at the end.
