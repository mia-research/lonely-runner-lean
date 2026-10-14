# A union bound on the odd-collapse set — and a complementary pair of certificates

2026-09-11. Follows `QUARTER_DICHOTOMY_v1.md`. Scripts
`experiments/n8/ok_collapse_deficiency_v1.py`, `ok_collapse_union_v1.py`, `ok_pair_v1.py`.
Exact `Fraction`, no float. Every criterion here is a **certificate** — a derivation or an
inequality — not a window search, so its reach figures are meaningful.

---

## 1. The window route is dead, for a reason  `[PROVED]`

Composing the collapse, the quarter dichotomy and the interval-deficiency lemma gives a
closed-form criterion on the collapse window `W`. **It fires on 0 of 617 tuples**, and the
cause is structural, not incidental:

> `|W| = (e⁽¹⁾−e⁽²⁾)/(4e⁽¹⁾e⁽²⁾)` is `O(1/e²)`, while each obstacle's components have
> length `1/(4e)`, which is `O(1/e)`. **The window is an order of magnitude shorter than a
> single obstacle**, so a deficiency argument on it can never fire.

Recorded so it is not retried.

## 2. The right object is the whole odd-collapse set

By the quarter dichotomy the failure set is `1/4`-periodic, so no near-zero window is
special. Take instead

    C   = { t : the ODD runners leave some odd residue free }
    v*(t) = min of those free residues
    B*_e = { t ∈ C : runner e blocks v*(t) },   e ranging over the v₂ ≥ 1 runners.

A `t ∈ C` fails only if **some** `e` blocks `v*(t)`, so the failure set lies inside
`⋃_e B*_e`. Hence

> **`|C| > Σ_e |B*_e|` ⟹ a witness exists.**  `[PROVED — union bound]`

No independence, no search. The converse is false — it fails on 127 of 308 tuples — so it
is **not forced**.

**A soundness fix, recorded because the first version was wrong.** The first implementation
put `t` in `B_e` when `e` blocked **all** free residues. That is unsound: a failure needs
only that *different* runners block *different* free residues. Designating a single `v*`
repairs it. The cost is real — the criterion's reach fell from 94% to 58% overall — and the
inflated figure was never reported.

## 3. Reach  `[EMPIRICAL — exact inputs, stated box]`

308 Case-2 tuples from `[1..16]`, by `a = #odd speeds`:

| `a` | 1 | 2 | 3 | **4** | **5** | **6** |
|---|---|---|---|---|---|---|
| union bound fires | 0/10 | 0/53 | 55/118 | **101/102** | **19/19** | **6/6** |

**`a ≥ 4`: 126 of 127.** That is precisely the class the block criterion provably cannot
reach (only two blocks per parity), and `a ≤ 3` is precisely the class it does. The two are
complementary.

## 4. The pair  `[EMPIRICAL — 364 tuples]`

`a ≤ 3`: block criterion `a < 2·max(u_O,u_E)` (structural, `TILING_AND_BLOCKS_v1` §1).
`a ≥ 4`: the union bound of §2.

| `a` | 1 | 2 | 3 | 4 | 5 | 6 | total |
|---|---|---|---|---|---|---|---|
| tuples | 7 | 57 | 143 | 122 | 30 | 5 | 364 |
| settled | 7 | **40** | 143 | **120** | 30 | 5 | **345 (94%)** |

**Complete at `a = 1, 3, 5, 6`.** The residue is 19 — seventeen at `a = 2`, two at `a = 4`.
Both certificates are sound, non-circular and search-free, so unlike the retracted figures
of `COLLAPSE_v2_NULL_v1` these percentages carry evidential weight.

## 5. Ledger

`[PROVED]` §1 the `O(1/e²)` vs `O(1/e)` obstruction; §2 the union bound and its soundness
under the `v*` designation.
`[EMPIRICAL — exact, stated box]` §3, §4 reach tables, with the control that the union
bound fails on 127/308 and the pair on 19/364, so neither is forced.
`[CORRECTED]` the first `B_e` definition, unsound; 94% → 58% on the union bound alone.

`n = 8` is **not proved.** What is new: a sound measure certificate that covers `a ≥ 4`,
which no earlier method did, and a complementary pairing that leaves `a = 2` as the single
identified weak class.
