# Working note — measure-zero individual good sets collapse onto the reference

2026-09-12. n=8 only. **Individual isolation throughout** — global isolation is not LRC.
Frame: `WHICH_GRIDS_ISOLATE_v1` §2 and §4 (coordinates `u_i = π(i) + 8 q_i`; `π` decides
global isolation, `q` is where individual isolation lives).

## 1. The hypothesis being tested

Every arrangement is a permutation/deviation off the AP/grid reference. The reference
achieves **equidistant** isolation: by the φ(n) law a complete residue system is globally
isolated at exactly `φ(8) = 4` instants `t = p/8`, `gcd(p,8)=1`. So at the reference each
runner's individual good set is a set of **points**, not intervals — measure zero is what
"exact" means there, not a defect.

The hypothesis asks whether permuting away from the reference can destroy individual
isolation. This note tests the sharp form: **can an individual good set be thin anywhere
other than at the reference?**

## 2. Result  [VERIFIED — exhaustive over the stated range]

Enumerate every primitive 7-element constraint set `D` — one runner's view, no global
condition imposed. `G_D = { t : ‖d t‖ ≥ 1/8 for all d ∈ D }`. Run at two ranges:

| | `[1..20]` | `[1..28]` |
|---|---|---|
| primitive constraint sets | 77,400 | 1,180,572 |
| `G_D` **empty** (runner never lonely) | **0** | **0** |
| `|G_D| = 0` with `G_D` nonempty | **3** | **3** |

The wider range is 15x the search space and finds **the same three** — the tight set does
not grow with the box.

The three, identical at both ranges:

| `D` | `G_D` |
|---|---|
| `(1,2,3,4,5,6,7)` | `{1/8, 3/8, 5/8, 7/8}` |
| `(1,2,3,4,5,7,12)` | `{1/8, 3/8, 5/8, 7/8}` |
| `(1,4,5,6,7,11,13)` | `{1/8, 3/8, 5/8, 7/8}` |

All three have the **same** good set, and it is exactly the φ(8) points. So on both ranges

> `|G_D| = 0`  ⟹  `G_D = { p/8 : p odd }`.

A thin individual good set can only be the reference's own isolation times. There is no
configuration that is thin somewhere else.

## 3. Reading it in the hypothesis

Two branches, no third:

- **On the reference** — `G_D` is the four points `p/8`. Nonempty by the φ(8) law.
- **Off the reference** — `G_D` has positive measure, bounded below by the resolution law
  `|G(e)| ≥ (3/4)|G_F| − N_F/(2e)` (`WN_resolution_law_2026_09_12` §3).

Measured on the AP transit: moving `r8` off its AP point by one takes the measure from `0`
to `0.0563` and it never returns to zero — `0.0736, 0.0792, 0.0818, 0.0833, …` out to
`r8 = 40`. Moving `r1` down gives `0.0938, 0.1319, 0.1438`. The reference is the floor.

Component count is not the invariant: AP runner 1 has 4 components, but `(0,2,3,4,5,6,7,8)`
runner 1 has 2 — with measure `0.0938`. Components can be traded for measure; the pair does
not bottom out together.

## 4. Why the two lemmas proved today belong here

Both are conditions on `π` alone, so they survive **every** deviation `q`:

- `m ≤ 8` uniqueness: runner's residue mod 8 unique. Reads `π`; `q` invisible. 88.6%.
- `m = 16` parity (`WN_parity_lemma_2026_09_12`): runner's parity class has ≥ 5 members.
  Parity of `u_i` equals parity of `π(i)` because `8q_i` is even — so this too is a
  `π`-condition, and its sufficient form holds for all `q`. 40.75% of the remainder.

That is the hypothesis's shape: properties read off the reference that no permutation or
deviation can break.

## 5. Status

- §2 is exhaustive over primitive `D ⊂ [1..28]`, 1,180,572 sets (and over `[1..20]`,
  77,400 sets). It is a verification on those ranges, not a proof for all `D`. That the
  tight set is unchanged from 77,400 to 1,180,572 sets is evidence it is finite, not proof.
- The φ(8) law for the reference is proved (`WHICH_GRIDS_ISOLATE_v1` §1).
- Not proved: that `|G_D| = 0 ⟹ G_D = {p/8}` holds beyond the range, and that `G_D` is
  never empty beyond it. Those are the two statements §2 supports and does not settle.
