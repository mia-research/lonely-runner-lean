# Does deformation away from AP/grid move the isolation's neighbours predictably?

**Question (owner, 2026-09-18).** *"So does the variation away from ap/grid change the neighbour
of the isolation in a predictable way?"*

**Answer.** It splits cleanly in two, and the split is sharp.

| | is the neighbour predictable from the residues? | |
|---|---|---|
| at a **grid instant** `t = p/(n·g)` | **completely**, and proved | `[PROVED]` Lean + `[EMPIRICAL]` 16,000/16,000 |
| at the **cascade's own instant** | **no** — 10.4%, against a 1.9% null | `[EMPIRICAL]` 16,000 pairs |

Grade discipline: the Lean half is `[PROVED]`; every percentage below is `[EMPIRICAL]`, bound to
the stated sampler and sample size.

---

## 1. The decomposition that makes the question answerable

Reduce a commensurable arrangement by `g = gcd` of the pairwise differences, so the speeds are
integers `w`. Every such arrangement is

```
w i  =  π i  +  n · q i           π i = residue mod n,   q i = whole laps
```

A grid is exactly the case where `π` is a bijection. An AP of gap `g` is the case `π = id`,
`q = 0`. So **"variation away from AP/grid" is variation in `π` and variation in `q`, and these
are independent.** Asking whether the neighbour moves predictably is two questions, not one.

---

## 2. At a grid instant: the `q` part is invisible, the `π` part obeys a closed form

### 2.1 Whole laps move nothing `[PROVED]`

`experiments/n8/GridNeighbour_v1.lean`, four theorems, `#print axioms` =
`[propext, Classical.choice, Quot.sound]` on all four, zero `sorry`:

```
gridPos n p d               := Int.fract (d · p / n)      -- j's place relative to i at t = p/n
gridPos_eq                  : gridPos n p d = ((d·p) % n) / n
gridPos_congr               : d ≡ d' (mod n)  →  gridPos n p d = gridPos n p d'
laps_invisible              : gridPos n p ((π j + n·q j) − (π i + n·q i))
                            = gridPos n p ((π j + n·q' j) − (π i + n·q' i))
neighbour_laps_invisible    : the two arrangements hand the subject the SAME function j ↦ gridPos
```

The last one is the point. Two arrangements sharing `π` do not merely put the neighbour in the
same place — they present the subject with the identical position function, so *every* selection
rule stated in that function (nearest ahead, nearest behind, the entire cyclic order of the pack)
returns the identical answer. Whole-lap deformation is not "approximately" invisible. It is
invisible.

Reproduce:

```bash
cd LonelyRunner && lake env lean ../experiments/n8/GridNeighbour_v1.lean
```

### 2.2 Residues move it by a closed form `[EMPIRICAL 12,800/12,800]`

At `t = p/(n·g)` runner `j` sits at `(π j − π i)·p / n` relative to the subject, so it is the
**neighbour ahead exactly when `(π j − π i)·p ≡ 1 (mod n)`**, i.e. `π j − π i ≡ p⁻¹`. At `n = 8`
the unit group `(ℤ/8)ˣ` is the Klein four-group, so **`p⁻¹ = p`** and the rule reads:

> **At instant `p/8` the subject's neighbours are the runners at residue offset `±p (mod 8)`.**

Checked on 400 grids × 8 subjects × 4 instants: **12,800 of 12,800**
(`experiments/n8/neighbour_rule_v1.py`).

For the AP (`π = id`) this collapses to the table measured earlier — each subject has exactly two
neighbour pairs, and `p = 7`/`p = 5` are `p = 1`/`p = 3` with ahead and behind swapped:

```
 subject    p=1      p=3      p=5      p=7
       1  (2,8)    (4,6)    (6,4)    (8,2)
       2  (3,1)    (5,7)    (7,5)    (1,3)
       4  (5,3)    (7,1)    (1,7)    (3,5)
```

So at grid instants the answer to the owner's question is **yes, and exhaustively**: the map from
deformation to neighbour is `π ↦ (±p mod 8)`, and the `q` coordinate does not appear in it.

---

## 3. At the cascade's instant: no

The cascade does not use the grid instants. It starts at `t = 1/(8·d_min)` and `1/(8g) ≥
1/(8·d_min)` because `g | d_min`, so the grid instants lie at or after the cascade's start; on a
sample of 24,000 subjects **63.8%** were already clear at the very first instant, before any grid
instant is reached (`neighbour_rule_v1.py` §2).

Running the §2.1 invariance test at the cascade's own stopping instant instead:

```
                              grid instant    cascade instant
  MATCHED (same residues)     1.0000          0.1042
  NULL    (unrelated)         0.1912          0.0194
  n = 16,000 subject-pairs each
```

(`experiments/n8/neighbour_rule_v5.py`.) The matched figure is **5.4× the null**, so the residues
are not irrelevant to the cascade's neighbour — they carry real information. They do not come
close to determining it.

A second, coarser statistic points the same way. Over 20,000 subject-instances the binding
neighbour is the *nearest runner in speed*:

```
  ahead   0.3409      behind  0.3540      either  0.6789
```

so a third of the time neither binding neighbour is a speed-neighbour at all.

### 3.1 A worked ladder

Subject `1` in the AP `(1,…,8)`, perturbing runner `8 → 8 + ε`:

```
   ε      cascade t   ahead  behind   flank
   0        1/8         2      8     [2, 8]      p = 1, the speed-neighbours
  1/20      3/8         4      6     [4, 6]      p = 1 dies → p = 3, the PAIR CHANGES
  1/4       3/8         4      6     [4, 6]
  1/2      17/60       17/2    4     [17/2]      the perturbed runner becomes the neighbour
   1        9/64        9      7     [9]
   2        1/8         2      7     [2, 10]     back to p = 1
```

Rows 2–3 are the predictable regime: an ideal instant dies, the subject is handed to the next
surviving one, and the `±p` rule delivers the new pair. Rows 4–5 are the regime §3 measures — the
instant is no longer of the form `p/8` at all, and the perturbing runner itself becomes the
binding neighbour.

---

## 4. What this does and does not give

**Does.** It names the coordinate that matters. A deformation's `q` component cannot move a grid
neighbour — that is now a Lean theorem, not a statistic — so any search over deformations at grid
instants is a search over `π` alone, which is finite (`8^8` before symmetry, and only the `φ(8)=4`
instants matter). It also explains the AP table's structure without computation.

**Does not.** It says nothing about Existence at order 8, and must not be read as progress on it.
Existence is a statement about arrangements where *no* grid instant works — precisely the regime
§3 shows is not residue-predictable. The clean half of this result lives exactly where the problem
is already solved, and the open half is exactly §2.3's open item ("how the fit decides which
runners then need the cascade"). That is a boundary this note locates; it does not cross it.

**No measure or density language is used, and none is needed** — §6A firewall intact. The
percentages in §3 are sampler frequencies over an explicitly named finite sample, not densities of
anything.

---

## 5. Errors made reaching this

Recorded per `OBJECT_REGISTER` practice: the mistake, not just the fix.

1. **`neighbour_rule_v2.py` and `_v3.py` both reported 6% where the truth is 100%** — twice, the
   same fault. I took residues in the units I had constructed, but `_frame.speeds()` **sorts**, so
   index `k` in `v` no longer corresponded to `π k`. `v3` "fixed" it by forcing `g = 1`, which was
   a real but different defect and left the sorting bug untouched. Only carrying runner identity
   through the sort by tag (`v4`) gave the exact answer. **A near-miss for a false null**: 6% looks
   like a perfectly publishable negative result, and I would have written it up as one.
2. **I nearly called 10.4% "below chance"** on the reasoning that a blind guess is `1/7 ≈ 14%`.
   The statistic is a *pair* of offsets; the matched null is **1.9%**. The figure is 5× the null,
   not below it. The null was not measured until after the sentence was drafted.

Both are instances of the same thing: a number was interpreted before the thing it was compared
against was computed.
