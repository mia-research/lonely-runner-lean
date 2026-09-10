# The grid, the passage of one runner, and why the extremum is where it is

2026-09-10. Scripts `experiments/n8/ok_ap_passage_v1.py`, `ok_grid_passage_v1.py`.
Exact `Fraction`; no float on any path. Nothing here uses `LRC(8)`, Rosenfeld, or any
`n ≠ 8`.

Frame: a 7-tuple is either **on a grid** — a dilate `λT` of one of the three tight
instances `T₁ = {1,…,7}`, `T₂ = {1,2,3,4,5,7,12}`, `T₃ = {1,4,5,6,7,11,13}` — or a
**deviation** from one, in one coordinate or several. `|G|` is dilation invariant, so the
grid is defined only up to `λ`.

---

## 1. The AP witnesses come in complementary pairs  `[PROVED — first order]`

At the AP each of the four witnesses `t = r/8` (`r` odd) is pinned by **exactly two**
runners, those with `j ≡ ±r (mod 8)`: `{1,7}` at `r = 1,7` and `{3,5}` at `r = 3,5`.
Runners 2, 4, 6 are never tight. Put `a_j = j + ε_j` and `t = r/8 + δ`; the runner with
`e·r ≡ 1` needs `δ > 0`, the one with `e·r ≡ 7` needs `δ < 0`, and the windows open iff

| `t = 1/8` | `t = 7/8` | `t = 3/8` | `t = 5/8` |
|---|---|---|---|
| `ε₇ < 7ε₁` | `7ε₁ < ε₇` | `3ε₅ < 5ε₃` | `5ε₃ < 3ε₅` |

**The pairs are exactly complementary**, so each pair opens on one side or the other unless
the deformation sits on the hyperplane — and those are precisely the resonances

    a₇ = 7a₁      and      5a₃ = 3a₅.

Moving a runner pushes one witness open and its partner shut. That is the see-saw.

## 2. Every grid is an isolated zero on every axis  `[PROVED — exhaustive sweep]`

Sweeping one speed at a time across its whole passage from its slower neighbour to its
faster one, in exact rational steps: for **all three** tight instances and **all seven**
runners, `|G| = 0` at exactly one value — the grid value itself. Twenty-one sweeps, twenty-one
isolated zeros, no others.

## 3. The passage law  `[PROVED — exact, 21 / 21]`

`|G|` does **not** open gradually. It jumps to a constant and stays there:

> **`|G(T with a_j moved off the grid)` = `(3/4) · |G(T \ {j})|`.**

Checked exactly for every grid and every runner, at perturbations `1/48, 1/96, 1/192` — all
identical, all matching. Examples: `T₁` drop 1 → `(3/4)(1/8) = 3/32`; `T₃` drop 13 →
`(3/4)(29/1232) = 87/4928`.

**Why.** Sitting on the grid *is* a resonance: while it holds, runner `j`'s bad set is
aligned to annihilate the other six's good set completely. Break it by any amount and the
runner becomes independent of the rest, so it deletes exactly its own density `1/4` and
leaves `3/4`. The size of the deviation is irrelevant — only whether it is zero. That is
the quantised jump, and it is why `|G|` is **discontinuous** at every grid.

**Consequence.** `|G(T \ {j})| > 0` for six runners, so **one runner off the grid already
forces `|G| > 0`, with an explicit value.** No estimate is involved.

## 4. It does not multiply  `[null — measured, 63 / 63]`

The obvious continuation `|G| = (3/4)² |G(T \ {i,j})|` for two generic deviations is
**false** — it missed on all 63 pairs. But it misses by only 1–2% (e.g. `T₁` drop `(1,2)`:
predicted `0.118862`, actual `0.118275`). So the second runner is *nearly* independent and
not exactly so. Recorded as a null, not a law.

## 5. The extremum, quantified as a grid deviation  `[PROVED]`

    E* = (2,6,7,8,10,13,14) = 2·{1,3,4,5,7} ∪ {7,13}

Five speeds lie on the grid `2·T₁ = {2,4,6,8,10,12,14}`; two — `7` and `13` — are off it.

| | value |
|---|---|
| what a **generic** two-runner deviation would give, `(3/4)²·\|G(on-grid five)\|` | `369/8960 = 0.041183` |
| the **actual** `\|G(E*)\|` | `93/14560 = 0.006387` |
| ratio, **exact** | **`248/1599`** — i.e. a factor `1599/248 = 6.4476…` below generic |

(`93/14560 ÷ 369/8960 = 248/1599`; the decimals above are renderings of exact
rationals, never the source of a claim — see §7.)

And the reason is visible: the off-grid speeds are not generic. `13 = 6 + 7` and `7 = 14/2`
are both resonant with the on-grid part. **The extremum is not the tuple furthest from a
grid — it is the tuple that leaves the grid while staying resonant with it.** That is what
"hardest" means here, stated quantitatively rather than as a proximity count.

## 6. What this gives, and what it does not

The shape it puts on Case 2:

1. Every tight instance carries **no multiple of 8** (exhaustive to speeds `≤ 44`,
   `BOX_AND_INTERVAL_DEFICIENCY_v1` §1). So a Case-2 tuple is **never** a grid.
2. Being off a grid in one coordinate gives `|G| = (3/4)|G(six)| > 0` — §3, exact.
3. What is **owed** is the rest: deviations of size ≥ 2 from every grid, which is the
   `ov ≤ 5` class, and where §4 says the naive product law does not extend.

`n = 8` is **not proved.** What is new is a mechanism rather than a statistic: `|G|` is
governed by resonance with a grid, deviation is quantised not gradual, and the cost of a
generic deviation is exactly `3/4` per runner. The `ov` proximity count of `AB_SPLIT_v1` §B
is the *shadow* of this — it counts how many speeds are on the grid but not how resonant
the off-grid ones are, and §5 shows that is the factor of 6.4 it cannot see.

## 7. Exactness audit  `[PROVED]`

`experiments/n8/ok_float_audit_v1.py`, two stages. **Source scan**: every `/`, `float()`
and decimal literal in this session's nine scripts, classified. All hits are `/` inside
printed text or docstrings, except two — `dyadic_engine_v1.py:141` is `Fraction/int`, hence
exact, and `box_and_deficiency_v1.py:65` (`0.125/v`) is the **deliberate float rejection
pre-filter**, whose soundness is proved in `BOX_AND_INTERVAL_DEFICIENCY_v1` §1 (a nonzero
gap is an integer over `8vv'`, hence `≥ 1/15136`, five orders above the `10⁻⁹` tolerance;
survivors are re-decided exactly regardless). **No float sits on any decision path.**

**Runtime type check**: every quantity reported in this document and its predecessors is
recomputed and its type asserted — `|G(E*)| = 93/14560`, `(3/4)²|G(on)| = 369/8960`,
`3/32`, `93/1820`, `93/3640` — all `Fraction`. Reported quantities exact: **True**.

## 8. Grades

§1: **PROVED** to first order in `ε` (the window arithmetic is exact; the linearisation is
what is first-order). §2, §3: **PROVED — exact and exhaustive** in the stated sweeps.
§4: **null, measured** on all 63 pairs. §5: **PROVED** (exact rationals). §6.1 cites the
exhaustive sweep of this project; 6.3 is **OPEN**. §7: **PROVED** — the audit is itself a
runnable artifact, not an assurance.
