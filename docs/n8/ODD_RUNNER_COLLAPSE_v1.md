# The odd-runner collapse — `a ≥ 4` attacked through the Klein/cyclic mismatch

2026-09-10. Follows `TILING_AND_BLOCKS_v1.md`, which closed `a ≤ 3` and named the
obstruction at `a ≥ 4`. Scripts `experiments/n8/ok_collapse_v1.py`,
`ok_combined_reach_v1.py`. Exact `Fraction`; nothing here uses `LRC(8)`, Rosenfeld, or any
`n ≠ 8`.

---

## 1. The mismatch, made into a lever  `[PROVED]`

In `F₂²` coordinates `(χ₁, χ₃)` the odd residue an odd runner blocks is

    g_e = ρ_e + bits(q_e),   q_e = ⌊4et⌋ mod 4,   bits(q) = (q mod 2, ⌊q/2⌋),

and the binary carry gives

> **`bits(q+1) = bits(q) + (1, q mod 2)`** — the increment **depends on `q`**.

That is exactly the statement that `ν : q ↦ 2q+1` is not a homomorphism `ℤ/4 → (ℤ/8)^*`:
in multiplicative form, advancing `q` by one multiplies `g_e` by **3 when `q` is even and by
7 when `q` is odd**. The Klein/cyclic mismatch is not an obstacle here — it is the
mechanism, because a *uniform* motion in `t` produces a *non-uniform* motion in `V`.

## 2. The collapse  `[PROVED for the two named cases]`

For `t < 1/(2e⁽¹⁾)` (`e⁽¹⁾ >` … `> e⁽ᵃ⁾` the odd speeds) every `q_e ∈ {0,1}`, with `q_e = 1`
exactly when `t > 1/(4e)`. So as `t` rises from `0` the set `S(t) = {e : q_e = 1}` runs
through the **top segments** of the odd speeds, and the odd runners block

    f(S) = {3ρ_e : e ∈ S} ∪ {ρ_e : e ∉ S}      (product in (ℤ/8)^*).

**Not Unit-Complete.** On `(0, 1/(4e⁽¹⁾))` every `q_e = 0`, so `f(∅) = {ρ_e}`, which misses
an absent class. ∎

**`a = 4`, Unit-Complete.** On `(1/(4e⁽¹⁾), min(1/(4e⁽²⁾), 1/(2e⁽¹⁾)))` — nonempty, and
explicit — only the largest odd runner has `q = 1`, so

    f(S₁) = {3ρ⁽¹⁾} ∪ ({1,3,5,7} \ {ρ⁽¹⁾}),

and since `3ρ⁽¹⁾ ≠ ρ⁽¹⁾` this **misses `ρ⁽¹⁾`**. ∎

The hypothesis that makes the case hard — all four unit classes present — is what supplies
the colliding partner. That is the whole content.

## 3. How far the top-segment argument goes  `[PROVED — exhaustive, and it has a boundary]`

Over **every** residue sequence (ordered by decreasing speed):

| `a` | Unit-Complete sequences | some top segment non-covering | deepest segment needed |
|---|---|---|---|
| 4 | 24 | **24 — all** | `r = 1` |
| 5 | 240 | **240 — all** | `r = 4` |
| 6 | 1 560 | 1 480 | `r = 5` |

**At `a = 6` it fails on 80 of 1 560**, e.g. `(1,3,1,5,7,5)`, `(1,3,1,7,5,7)`,
`(1,3,5,1,7,5)`. So the argument is a theorem at `a = 4` and `a = 5` and **not** at `a = 6`;
that is stated as a boundary, not hidden. (`a = 5` needs depth up to 4, which is available
only when the odd speeds lie within a factor 2 of the largest — `q_e ∈ {0,1}` requires
`t < 1/(2e⁽¹⁾)`. Deeper windows, where `q` reaches 2 and 3, are untested and are the
obvious next move at `a = 6`.)

## 4. Reach  `[EMPIRICAL — exhaustive or sampled in the stated box]`

End-to-end: take the collapse window, confirm the odd runners really leave a residue free
on it, then ask whether the `v₂ ≥ 1` runners miss it too — which is an actual witness,
checked against all seven speeds.

| | `a ≥ 4` tuples, box `[1..18]` |
|---|---|
| odd runners collapse on a near-0 window | 490 / 500 (**98%**) |
| …and `v₂ ≥ 1` runners miss it → **witness** | 413 / 500 (**82%**) |

Combined with the block criterion of `TILING_AND_BLOCKS_v1` §1, over a 925-tuple sample of
Case 2 in `[1..18]`:

| criterion | reach |
|---|---|
| block criterion (`a ≤ 3` only) | 503 (54%) |
| odd-runner collapse (all `a`) | 869 (**93%**) |
| **union — explicit witness, no measure estimate anywhere** | **906 (97%)** |
| residue | 19 (**2%**) |

Both criteria hand back a `t` and it is verified exactly; neither estimates anything.

## 5. What this does not do

`n = 8` is **not proved.** Three things are owed and none is glossed:

1. The `a = 6` gap — 80 residue sequences where no top segment collapses. Deeper windows
   (`q` reaching 2, 3) are the untested continuation.
2. The `a = 5` depth-4 segments need the odd speeds within a factor 2 of `e⁽¹⁾`; outside
   that the segment is not realised in the window.
3. The residual 2–3%. The known extremum `(2,6,7,8,10,13,14)` collapses on the odd side at
   once (`ρ = {5,7}`, missing 1 and 3) but its four `v₂ = 1` runners cover the gap, so it is
   **in the residue** — as it must be, since it is where `|G|` is smallest.

The reach figures are one-sided and box-bound as always. What has changed: `a ≥ 4` was
0% reachable in `TILING_AND_BLOCKS_v1` and is now 82%, and the mechanism doing it is the
Klein/cyclic mismatch used as a lever rather than treated as the obstruction.

## 6. Grades

§1 identity and §2 both collapse cases: **PROVED** (two lines each).
§3 table: **PROVED — exhaustive** over the finite residue data, including the `a = 6`
counterexamples.
§4: **EMPIRICAL** — exhaustive over `a ≥ 4` in the stated box, sampled for the union;
every reported witness verified exactly against all seven speeds.
