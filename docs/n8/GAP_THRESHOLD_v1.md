# Auditing the stated gap, and closing the route it suggested

Lean: `experiments/n8/GapThreshold_v1.lean` (4 theorems, axiom-clean; two need only
`[propext, Quot.sound]`). Scripts: `allowed_class_v1.py`, `failing_moduli_v1.py`.

---

## 1. The audit: the requirement was mine

`ISOLATED_WITNESS_v1` §3 named the gap as *"whether the order-6 margin argument transfers to the
`u`-problem"*. **That is not a requirement of the problem.** The substitution `q = 2u+1` was my
change of variable, introduced to handle `b = 2`. The genuine requirement is only:

> find a candidate in the order-6 band satisfying the residue exclusions.

Nothing obliges that to be done in `u`. The direct alternative is to round `t` not to the nearest
integer but to the nearest integer **in an allowed residue class**.

## 2. The direct alternative is strictly worse — **[PROVED]**

Let `G` be the largest gap in the allowed class, so `|q − t| ≤ G/2`. The order-6 margin then
gives the band `2b − 6G ≤ 12r ≤ 10b + 6G`.

**[PROVED — `GapThreshold.window_of_bandG`]** that band implies the window at every modulus

```
    b ≥ 12G + 3 .
```

**[PROVED — `GapThreshold.threshold_mono`]** the threshold is monotone in `G`, so a larger
allowed-class gap can only **enlarge** the exceptional set, never shrink it.

The allowed classes, by which of `{2,3,8,9}` the profile carries:

| exclusions enforced | allowed residues | largest gap `G` | exceptional moduli |
|---|---|---|---|
| none (plain rounding) | — | **1** | **4** — `{2,3,8,9}` |
| one of them | e.g. `2/3` | 2 | 14 |
| two | e.g. `14/24` | 3 | 26 |
| two (with `b=2`) | e.g. `2/6` | 4 | 38 |
| three | `35/72` | 5 | 50 |
| three (with `b=2`) | `6/24` | 6 | 62 |
| **all four** | **`15/72`** | **10** | **110**, largest `120` |

So enforcing the four exclusions by moving the candidate trades **4** exceptional moduli for
**110**. `window_of_band_one` and `window_of_band_ten` record the two ends: thresholds `15` and
`123`.

**Route closed, with the reason.** Satisfying the residue conditions *by rounding into an allowed
class* is provably counterproductive — not a guess, a monotonicity theorem. The exclusions must
be **coordinated with the band**, not rounded into.

## 3. What is now known about the shape of the problem

**[PROVED]** For **every** rounding error the exceptional set is finite and bounded by `12G + 3`.
The problem never has an infinite tail of bad moduli — only a finite, explicitly computable list,
and for the case that matters that list is the four moduli `{2,3,8,9}`.

That is worth stating as the structural fact it is: *the difficulty of Existence at order 8 is
concentrated, for any attack of this shape, in a bounded set of small moduli.*

## 4. Two errors caught in the course of this

**The cyclic gap of a singleton.** My first gap computation returned `0` for an allowed set with
one residue, instead of the modulus `P`. It made `(2,)` — the commonest case — look free. Fixed;
the corrected value is `G = 2`, threshold `27`, 14 exceptional moduli.

**"Threshold" was the wrong shape.** I first reported the least `b` at which band ⟹ window holds,
as though the property were monotone in `b`. It is not: at `G = 1` it holds at `b = 4..7`, fails
at `8, 9`, and holds from `10`. Reporting a threshold hid the exceptional set, which is the whole
content. `FourResidues` had already established this and I restated it wrongly.

## 5. Where the gap actually is

Unchanged, and now stated without the `u` detour:

> **`[OPEN]`** For every commensurable profile there is a generating reading whose order-6 band
> contains a candidate `q` with `q ≢ 0 (mod 2)`, `q ≢ 0 (mod 3)`, `q ≢ 7 (mod 8)` and
> `q ≢ 8 (mod 9)`, for whichever of those moduli occur.

§2 closes the obvious attack on it. The `u`-substitution of `ODD_SUBLATTICE_v1` remains available
and makes `b = 2, 4, 6` vacuous, but it is a reformulation, not a requirement — and §2 shows the
same is true of any scheme that buys residue conditions with rounding error.

Existence at order 8 remains open.
