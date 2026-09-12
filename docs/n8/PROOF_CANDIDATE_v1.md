# n = 8 — proof candidate from the reference / deviation / transit / resolution architecture

2026-09-12. **Individual isolation throughout** (global isolation is not LRC).
Assembles: `WHICH_GRIDS_ISOLATE_v1`, `FRAME_FREE_RESTATEMENT_v1`,
`WN_parity_lemma_2026_09_12`, `WN_transit_periodicity_2026_09_12`,
`WN_resolution_law_2026_09_12`, `WN_reference_collapse_2026_09_12`.

## 0. The architecture

Four ingredients, each established separately:

1. **A reference that isolates.** AP/grid — any complete residue system mod 8 — is globally
   isolated at exactly `φ(8) = 4` instants.
2. **Coordinates in which every arrangement is a deviation from it.** `u_i = π(i) + 8 q_i`.
3. **A deterministic transit law**: how sliding one speed changes isolation.
4. **A deterministic resolution law**: how the measure of a runner's good set responds.

The candidate runs them as a case split on each runner separately.

## 1. Steps and their status

Let `V` be 8 distinct integer speeds, translated so the runner under test sits at 0 and
divided by `g = gcd`. Runner `i` has constraint set `D` (its 7 differences),
`G_D = { t : ‖d t‖ ≥ 1/8 ∀ d ∈ D }`. Runner `i` is lonely iff `G_D ≠ ∅`.

| step | statement | status |
|---|---|---|
| **S1** reference | `π` a complete residue system ⟹ globally isolated at `t = p/8`, `φ(8)=4` times; in particular every runner individually lonely | `[PROVED]` `WHICH_GRIDS_ISOLATE_v1` §1 |
| **S2** partial reference | for any `m ≤ 8`, residue of `i` unique mod `m` ⟹ lonely at `t = a/m` | `[PROVED]` |
| **S3** parity | `i`'s parity class has ≥ 5 members and `16 ∤ d` for all `d` ⟹ lonely at `t = a/16`. A `π`-condition: parity of `u_i` = parity of `π(i)` since `8q_i` is even, so it survives every deviation | `[PROVED]` `WN_parity_lemma` §3 |
| **S4** transit | fixing seven speeds and sliding the eighth, loneliness at `t = a/m` depends on the slider only through `e mod m` — hence periodic, hence a covering-congruence question, finite over one period | `[PROVED]` `WN_transit_periodicity` §1 |
| **S5** resolution | `|G(e)| ≥ (3/4)|G_F| − N_F/(2e)`, where `F` = the six fixed differences, `N_F` = components of `G_F` | `[PROVED]` `WN_resolution_law` §3 |
| **S6** branch | `e > E0 := 2N_F/(3|G_F|)` ⟹ `|G(e)| > 0` ⟹ `G ≠ ∅` ⟹ lonely | `[PROVED]`, given `|G_F| > 0` |
| **S7** thinness | `|G_D| = 0` ⟹ `G_D = {p/8 : p odd}` — a thin good set can only be the reference's own isolation times | `[VERIFIED]` 1,180,572 sets, `[1..28]`; not proved |

## 2. Where the assembly stands

Coverage of the union S2 ∪ S3 ∪ S6, over all 349,920 runner-instances of primitive 8-sets
in `[1..18]`:

| branch | fires on |
|---|---|
| S2 residue uniqueness, some `m ≤ 8` | 89.31% |
| S3 `m = 16` parity | 36.90% |
| S6 resolution, with the proved constant `N_F/2` | 0.38% |
| **uncovered by all three** | **5.87%** |

With the sharper constant `C = 3/2` in place of `N_F/2` (measured `C` runs 0.59–1.12 across
the fixed parts tested, so `3/2` is plausible but **not proved**):

| `C` | still uncovered |
|---|---|
| `3/2` | **3.49%** |
| `2` | 5.19% |
| `3` | 5.88% |

**The architecture does not close.** 3.49% of runner-instances fall in no proved branch.

## 3. What the uncovered cases are

They are **not** failures. Direct BSM evaluation of all 12,208 uncovered runner-instances at
`C = 3/2`: `G_D` empty in **0** of them. Every one is lonely; the branches are simply not
sharp enough to decide it. Smallest examples:

    V=(1,2,3,4,5,6,7,10) runner 8   D=[3,4,5,6,7,8,9]
    V=(1,2,3,4,5,6,7,12) runner 8   D=[5,6,7,8,9,10,11]
    V=(1,2,3,4,5,6,8,9)  runner 8   D=[1,3,4,5,6,7,8]

These are near-reference: a consecutive run of differences, i.e. a runner sitting just off the
AP. The branches that fail are exactly the ones nearest the reference, where S2's residues
collide and `e` is too small for S6.

## 4. The two gaps, named

**G1 — the constant.** S5's error term uses `N_F/2`, obtained by counting centres `k/e` in
each component. Measurement says the truth is near `1` regardless of `N_F`. A proof of
`|G(e)| ≥ (3/4)|G_F| − C/e` with absolute `C` would move S6 from 0.38% to ~2.4% coverage and
cut the hole to 3.49%. It would not close it.

**G2 — the small-`e` region.** S6 is a large-`e` branch by construction. The residue left is
`{ runners with no unique residue at any m ≤ 8, not in a majority parity class, and with
small e }` — precisely the near-reference band in §3. No proved statement covers it.
S4's covering certificates settle individual cases (E* runner 1 closes with moduli
`{14,15,16,23}` over period 38,640) but no uniform version exists.

**Not a gap:** applicability. Every arrangement has the coordinates (S1/S2), a transit (S4)
and a resolution (S5) — that much is unconditional. What is missing is not reach but
sharpness: the branches apply everywhere and decide 96.5%.

## 5. Status

No grade moves. n = 8 is **not proved**. §1 rows marked `[PROVED]` are proved; S7 is verified
on a range; §2's coverage figures are exhaustive over `[1..18]`; the `C = 3/2` row is
conditional on an unproved constant and is reported as such.
