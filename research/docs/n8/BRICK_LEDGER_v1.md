# The brick ledger — what is laid, what it carries, where the wall is

2026-09-13. n = 8, individual isolation, threshold 1/8. Speeds distinct positive reals,
translation-invariant so WLOG sorted `v_1 < … < v_8`. Differences `d_j = |v_i − v_j|` for the
runner `i` under consideration; `d_min` its smallest.

This file is a **ledger, not an argument**. Each brick is stated with the grade it actually
earns and the load it actually bears. Nothing here is promoted by adjacency to something proved.

---

## The bricks

### B1 — loneliness is a two-neighbour condition  `[PROVED]`

Runner `i` is lonely at `t` iff **both** its cyclic-adjacent gaps on the circle at time `t`
are `≥ 1/8`.

*Proof.* The nearest other runner to `i` on the circle is one of its two cyclic neighbours in
the induced order at time `t`. So `min_j ‖(v_i − v_j)t‖` is realised by a neighbour, and the
seven constraints collapse to two. ∎

**Load:** reduces the per-runner condition from 7 constraints to 2. Local.

### B2 — the φ(n) law  `[PROVED — prior work]`

A grid is globally isolated at exactly `φ(n)` instants `t = p/(ng)`, `gcd(p,n) = 1`. All eight
runners at once, all-or-nothing.

**Load:** supplies the one arrangement class whose behaviour is completely known. It is the
reference frame, not a step in the n = 8 argument.

### B3 — equidistance is the grid's property; the AP is its simplest form  `[PROVED — B2]`

The AP `(1,…,8)` is the grid with all deviations zero. Every dilation `(k,2k,…,8k)` and every
block grid with `d_min = g` throughout has the same isolation structure. "AP" is not privileged;
"grid" is.

**Load:** stops the argument from being an argument about arithmetic progressions.

### B4 — the floor  `[PROVED — arithmetic]`

    t*  ≥  1 / (8 · d_min)

*Proof.* For `t < 1/(8·d_min)` we have `d_min·t < 1/8`, so `‖d_min·t‖ = d_min·t < 1/8` and the
runner is not lonely. Nothing precedes the bound. ∎

**Load:** a per-runner lower bound, exact, computed from one number. `SCALE_RULE_v1.md` §1.

### B5 — the band identity  `[PROVED — arithmetic]`

With `m = d_min`, a difference `d` blocks the floor iff `d mod 8m` lies within `m` of 0 —
i.e. `(d mod 8m) ∈ {0,…,m−1} ∪ {7m+1,…,8m−1}`, `2m−1` forbidden residues out of `8m`.

**Load:** turns "is the floor attained" into a residue test at modulus `8·d_min`. Reaches all
real speeds; `RESIDUE_BAND_v1.md` §4 records the correction that the modulus is `8·d_min` and
**not** `8g` — `g` does not reach off-grid.

### B6 — the grid theorem  `[PROVED — B5]`

Let `V` be a grid with gcd `g`, and suppose `d_min = g` for all eight runners. Then no runner
is blocked and every runner's first isolation is exactly `1/(8g)`.

*Proof.* `g │ d` so `s = d/g ∈ ℤ⁺`; by B5, blocked ⟺ `s ≡ 0 mod 8` ⟺ the two runners share a
residue mod 8. A grid has all eight residues distinct. ∎  (485/485.)

**Load:** the grid measure `g` is exactly the condition under which the eight numbers `d_min`
collapse to one — which is why grid isolation is simultaneous.

### B7 — the lattice of moments  `[PROVED, CONDITIONAL ON EXISTENCE]`

If runner `i` is ever lonely, then its first such instant satisfies

    t*  =  p / (8d),      p ≡ ±1 (mod 8),      d one of that runner's differences.

*Proof.* Each `{t : ‖d_j t‖ ≥ 1/8}` is closed, so the good set `G_i` is closed; by B4 it is
bounded below by `1/(8d_min) > 0`, so if nonempty its infimum `t*` is attained. Just below `t*`
the runner is not lonely, so some constraint is violated there; that constraint is continuous
and `≥ 1/8` at `t*`, hence exactly `1/8` at `t*`. So `‖d t*‖ = 1/8` for that `d`, i.e.
`8dt* ∈ ℤ` and `8dt* ≡ ±1 (mod 8)`. ∎

Measured: 2432/2432 single-deviation runner-instances, zero exceptions, `p ≡ ±1 mod 8` always.
Of these, `d = d_min` with `p = 1` in **2072 (85.2%)**; in the other 360 the carrying gap is
never `d_min` (ranks 1–6) and `p ∈ {7,9,15,17,25,33,41,49,55,63,105}`, dominantly 9.

**Load:** the AP's instant set `p/8` never leaves. Deviation rescales it by a gap and steps it
along the `±1 mod 8` ladder. This is a **localisation** statement.

---

## The wall

B7 is conditional on existence — it says *where* a moment is, given that one exists. It cannot
prove n = 8, and nothing built out of B1–B7 alone can, because none of them produces a moment.

This is the mirror of the failure already on record for the other direction
(`project_n8_unitcomplete_theorem`: *LRC(7) does not help — existence ≠ localisation*). We now
hold localisation without existence. **The missing brick is the join**: a reason why some rung
`p/(8d)` on some gap's ladder must clear all seven constraints.

What is known about the join, and is not enough:

- **Density is circular.** `DYADIC_DEPTH_RESULT_v1.md` §4 `[PROVED]`: if the max of
  `g(t) = min_v ‖vt‖` exceeds `1/8` then `g > 1/8` on an open interval and a witness exists by
  density alone. That derives existence *from* LRC(8), which is the thing being proved. Do not
  re-enter this route; it was closed 2026-09-07 and rebuilt once in error.
- **Clearing one blocker hands the block to another.** Three candidate closed forms for the
  blocked case each landed at ≈46%, because in 3234/3234 cases the difference that blocks after
  a repair is a *different* one. The blocked case has no local closed form.
- **Measure and covering are dead at n = 8.** The AP's good set has measure zero inside a
  revolution (four isolated points); the union bound fails by 3/2. `8 × 2 × 1/16 = 1` exactly —
  the circle is exactly filled, with nothing spare.

## Grades used

`[PROVED]` — argument given here or cited to a file that gives one, all real speeds.
`[PROVED, CONDITIONAL ON X]` — proof is complete given X; X is not supplied by this ledger.
`[PROVED — prior work]` — established elsewhere in the programme, cited not re-derived.

No brick in this file is graded above what its own argument earns. B7's conditionality is the
load-bearing caveat and is stated in its grade slot, not in a footnote.
