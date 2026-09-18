# Deformation, the binding runners, and depth

Supersedes `NEIGHBOUR_DEFORMATION_v1.md`, which is retained. **v1 §4 was wrong in its framing**
and is corrected in §7 here: it said the result "does not bear on Existence" and stopped. It does
bear on *which runners can be among the binding disparities, and how far any arrangement may move*
— a different claim, which v1 did not test because I had already deflated it.

---

## 1. The question and the shape of the answer

**Owner, 2026-09-18.** *"Does the variation away from AP/grid change the neighbour of the isolation
in a predictable way?"* — and then: *"what it does bear on is what runners are among the
discrepancies and limits how they may be arranged for any arrangement. So we may get more
understanding about how and why any depth occurs."*

| | result | grade |
|---|---|---|
| §2 whole laps move a grid neighbour | **never** | `[PROVED]` |
| §2 residues move it | by a closed form, `±p mod 8` | `[PROVED]` algebra, `[EMPIRICAL]` 12,800/12,800 |
| §3 which runners can ever bind | a **gcd cage**; at `n=8`, 3 of 7 are barred | `[PROVED]` |
| §4 how far an arrangement may move | exact integer budget per offset | `[PROVED]` + `[EMPIRICAL]` |
| §5 neighbour at the *cascade's* instant | **not** residue-determined | `[EMPIRICAL]` 10.4% vs 1.9% null |
| §6 cascade **depth** | **not** determined by residues *or* by laps | `[EMPIRICAL]`, on the forced floor |

Lean: `experiments/n8/GridNeighbour_v1.lean`, **8 theorems, zero `sorry`, all axiom-clean**
(`[propext, Classical.choice, Quot.sound]`; `slot_gcd` does not even need choice).

```bash
cd LonelyRunner && lake env lean ../experiments/n8/GridNeighbour_v1.lean
```

---

## 2. The decomposition, and the grid instants

Reduce by `g = gcd` of the pairwise differences, so speeds are integers `w`. Then

```
w i  =  π i  +  n · q i           π i = residue mod n,   q i = whole laps
```

A grid is `π` bijective; an AP of gap `g` is `π = id`, `q = 0`. "Variation away from AP/grid" is
variation in `π` and in `q`, and they are independent.

**`q` is invisible at grid instants** (`laps_invisible`, `neighbour_laps_invisible`). Two
arrangements sharing `π` do not merely put the neighbour in the same place — they hand the subject
the *identical* position function, so nearest-ahead, nearest-behind and the whole cyclic order
agree. 16,000 of 16,000 in `neighbour_rule_v4.py`.

**`π` moves it by a closed form.** At `t = p/8` runner `j` is the neighbour ahead iff
`(π j − π i)·p ≡ 1`, and `(ℤ/8)ˣ` is Klein so `p⁻¹ = p`:

> the neighbours at instant `p/8` are the runners at residue offset **`±p (mod 8)`**.

12,800 of 12,800 (`neighbour_rule_v1.py`). For the AP this is the measured table, with `p=7`/`p=5`
being `p=1`/`p=3` with ahead and behind swapped.

---

## 3. Which runners can ever bind: a gcd cage

As the instant `p` runs over the **units** mod `n`, a runner at offset `d` visits the slots `d·p`
— the orbit of `d` under `(ℤ/n)ˣ`. That orbit is pinned by `gcd(d, n)`:

```
slot_gcd     :  gcd((d·p) mod n, n) = gcd(d, n)            for p a unit
slot_ge      :  gcd(d,n) ≤ (d·p) mod n  ≤  n − gcd(d,n)    when the slot is nonzero
gridPos_caged:  gcd(d,n)/n ≤ position ≤ 1 − gcd(d,n)/n
```

**A runner whose residue offset shares a factor with `n` can never approach the subject.** At
`n = 8` the orbits are `{0}`, `{1,3,5,7}`, `{2,6}`, `{4}` — indexed by the **2-adic valuation** —
and the closest a runner at offset `d` ever comes, over all four instants, is exactly `2^ν₂(d)/8`:

```
  d  ν₂  slots over p = 1,3,5,7   closest approach
  0  ∞   0 0 0 0                  0        (blocks always — this is the residue partition)
  1  0   1 3 5 7                  1/8      threshold
  2  1   2 6 2 6                  1/4
  3  0   3 1 7 5                  1/8      threshold
  4  2   4 4 4 4                  1/2      ANTIPODAL at every instant
  5  0   5 7 1 3                  1/8      threshold
  6  1   6 2 6 2                  1/4
  7  0   7 5 3 1                  1/8      threshold
```

Exhaustive, not sampled (`offset_valuation_v1.py`). `even_offset_caged` is the `n = 8` case in
Lean.

**So in any grid, 3 of the subject's 7 disparities — offsets 2, 4 and 6 — are structurally barred
from ever being the binding constraint at a grid instant.** The tightness is carried by four
runners, never seven. The grid-instant problem is a 4-runner problem.

This is the same object Barajas–Serra run the `n = 7` argument on, one prime down: there `ν` is the
7-adic valuation of a position; here `n = 8 = 2³` and it is the 2-adic valuation of a residue
offset. `[OBSERVATION]` — the structural parallel is stated, not exploited, and BS's argument does
not transfer (CLAUDE.md §11).

---

## 4. How far an arrangement may move

The cage read as a perturbation budget. Moving a runner's speed by `δ` moves it by `δ·t`; the
subject stays clear while the runner stays at distance `≥ 1/8`. At `t = p/8`:

```
  offset  ν₂   budget at p=1   p=3    p=5    p=7    MIN over the four
    1     0        0           2/3    2/5     0       0
    2     1        1           1/3    1/5    1/7      1/7
    3     0        2            0      0     2/7      0
    4     2        3            1     3/5    3/7      3/7
    5     0        2            0      0     2/7      0
    6     1        1           1/3    1/5    1/7      1/7
    7     0        0           2/3    2/5     0       0
```

At the AP-referenced instant `p = 1` the budget is exactly `min(d, 8−d) − 1`, in reduced units —
**`0, 1, 2, 3, 2, 1, 0`**. Confirmed by direct simulation on 300 grids × 8 subjects × 7 runners
(`offset_slack_v1.py`), which reproduces that row exactly.

The reading the owner asked for: **an arrangement's rigidity at a grid instant is carried entirely
by the two residue-adjacent runners** (offsets 1 and 7, budget 0). The residue-antipodal runner
(offset 4) may have its speed moved by 3 in either direction with no effect at all. So "how they
may be arranged" is not uniformly constrained — the constraint is concentrated on two of the
seven, and it is exact.

---

## 5. At the cascade's instant, the neighbour is not residue-determined

The cascade does not visit the grid instants. It starts at `1/(8·d_min)`, and `g | d_min` so the
grid instants lie at or after that; 63.8% of subjects are already clear at the first instant,
before any grid instant is reached. Running the §2 invariance test at the cascade's own stopping
instant:

```
                            grid instant    cascade instant
  MATCHED (same residues)     1.0000          0.1042
  NULL    (unrelated)         0.1912          0.0194       n = 16,000 pairs each
```

5.4× the null — real information, nowhere near determination (`neighbour_rule_v5.py`).

---

## 6. Depth: a negative, and it is a clean one

The owner's hope was that this would illuminate *why depth occurs*. Tested directly, on the same
matched-pair design, holding each coordinate fixed in turn:

```
  depth agreement between two arrangements, by what is held fixed:
     matched π  (q varies)    0.4017
     matched q  (π varies)    0.4148
     matched neither          0.3805
     FORCED FLOOR             0.3758     (collision rate of the depth marginal alone)
     n ≈ 20,000 subject-pairs per arm
```

(`depth_residue_v3.py`; the floor is the probability two independent draws from the observed depth
distribution agree, which is what any statistic must beat.) Both arms sit essentially on the floor.
The blocker sets behave the same way: 0.3466 matched against 0.3185 null.

**Neither coordinate determines depth, and neither does much better than chance.** Depth is a joint
phenomenon of `π` and `q` together, not separable in the decomposition that explains the grid
instants completely. That is worth knowing precisely because the decomposition is otherwise so
clean: whatever explains depth, it is not this.

`[EMPIRICAL — conditional negative]`: bound to this sampler (residues uniform on ℤ/8, laps uniform
on 0..6, reduced units, `n ≈ 20,000` subject-pairs per arm) and to depth-as-move-count. It does not
say depth is unstructured; it says these two coordinates do not carry it.

---

## 7. What this does and does not give — correcting v1

**v1 §4 said this "does not bear on Existence" and stopped there. That was a deflation, not a
finding**, and it skipped the test. The corrected position:

**It does constrain the arrangement space.** §3 and §4 are hard limits that hold for *every*
arrangement, not statistics: which offsets can carry tightness (only the units), how close the
others can ever come (`2^ν₂/8`), and exactly how far each may move (`min(d,8−d)−1` at `p=1`). That
is a reduction of the grid-instant problem from seven runners to four, with the residue-antipodal
runner provably irrelevant to it.

**It does not reach Existence, and §6 says why the obvious bridge fails.** The hoped-for route was
cage → which runners block → depth. The cage is proved and the depth link is measured absent. The
open regime is exactly where §5 and §6 land: off the grid instants, where `q` and `π` interact and
neither alone predicts anything. That is the same boundary as §2.3's open item ("how the fit
decides which runners then need the cascade"). This note sharpens where the boundary is; it does
not cross it.

**No measure or density language is used** — §6A firewall intact. The percentages are sampler
frequencies over explicitly named finite samples.

---

## 8. Errors made reaching this

1. **`neighbour_rule_v2.py` and `_v3.py` both reported 6% where the truth is 100%** — twice, the
   same fault: `_frame.speeds()` **sorts**, so the residue index stopped tracking the runner. `v3`
   "fixed" it by forcing `g = 1`, a real but different defect, leaving the sorting bug untouched.
   Only carrying identity through the sort by tag (`v4`) gave the exact answer. **A near-miss for a
   publishable false null**: 6% reads as a perfectly good negative result.
2. **10.4% was nearly called "below chance"** against a `1/7 ≈ 14%` baseline. The statistic is a
   *pair* of offsets; the matched null is **1.9%**. Five times the null, not below it. The null was
   not computed until after the sentence was drafted.
3. **v1 §4 deflated the result before testing it** (this section's subject). The owner had to point
   out that "bears on Existence" and "constrains which runners can bind" are different claims. §3
   and §4 exist only because of that push-back, and they are the strongest part of the note.
4. **The 0.40 depth figure was nearly reported as a weak positive** before the forced floor was
   computed. The floor is 0.3758. Same fault as (2), one measurement later.

All four are the same failure: **a number interpreted before the thing it must be compared against
was computed.** (2) and (4) are that fault in successive experiments in the same session.
