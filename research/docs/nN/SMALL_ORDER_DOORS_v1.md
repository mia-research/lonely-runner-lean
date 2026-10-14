# The cascade framework at orders 5, 6 and 7 — what transfers and what does not

2026-09-20, version 1. Question put by the owner: can the `n = 8` framework of
`PROOF_SPINE_v1.md` / `MANUSCRIPT_v17.md` be applied at `n = 5, 6, 7` "to this same level"?

Artefacts: `LonelyRunner/LRC/Spec/DoorsN.lean` (new, builds),
`experiments/n8/doorsN_check_v1.lean` / `.out` (axiom checks),
scratch arithmetic for §3 reproduced inline.

**RING-FENCE.** `LRC/Construction8/` and `LRC/Spec/Doors.lean` are untouched. `DoorsN.lean`
is additive and imports `Doors.lean`; it redefines nothing in `LRC.Spec`.

---

## 1. The answer in one line

The door equivalence transfers **completely and for free** — it never depended on eight. The
*termination* results do not transfer, and the missing case at each of `n = 5, 6, 7` is the
same shape as the missing case at `n = 8`.

---

## 2. `doors_agree` holds at every order  `[PROVED]`

`LRC/Spec/DoorsN.lean` carries the arrangement layer and the four doors to a variable `n`
under `[Fact (2 ≤ n)]`:

```lean
theorem LRC.SpecN.doors_agree {n : ℕ} [Fact (2 ≤ n)] {v : Fin n → ℝ}
    (hv : Function.Injective v) (k : Fin n) :
    (DoorFlank v k ↔ LonelyForSubject v k) ∧ (DoorArrives v k ↔ LonelyForSubject v k) ∧
    (DoorCapped v k ↔ LonelyForSubject v k) ∧ (DoorFAM v k ↔ LonelyForSubject v k)
```

Axioms `[propext, Classical.choice, Quot.sound]`, no `sorry`, instantiated and axiom-checked
at `n = 5, 6, 7` (`doors_agree_five`, `_six`, `_seven` in `experiments/n8/doorsN_check_v1.out`).

**Why it was free.** Every step of the `n = 8` door proofs already supplies `8` as an
*argument* to a lemma stated for a variable `n`: `lonely_iff_run_ends (n := 8)`,
`ChainBounds.exists_fixed_of_capped (n := 8)`, `FourDifferences.iterate_stable (n := 8)`,
`MomentIterationN.move_eq_self_or_opening (n := 8)`, `Flanks.lonely_iff_exists_flank (n := 8)`.
`MomentIterationN` and `Flanks` are stated under `variable {n : ℕ} [Fact (2 ≤ n)]` throughout.
The literal `8` entered only at `LRC/Spec`, through `Fin 8`, `(8 : ℝ)⁻¹` and
`instance : Fact (2 ≤ 8)`. The port is a substitution; it compiled on the first attempt.

One generic proof obligation did have to be supplied: `others_nonempty` was `by simp` at a
literal `Fin 8` and needs `Fact.out : 2 ≤ n` at a variable `n`. Nothing else changed.

**What this means.** The four doors — a flank hosts a lonely opening; the cascade arrives;
the cascade is capped; each runner is in the way finitely often — are equivalent to the
subject being lonely **at every order `n ≥ 2`**, both directions, unconditionally. The
equivalence is a property of the cascade construction, not of eight runners.

---

## 3. Termination is where the orders differ  `[PROVED — the table; the gap is a gap in the record, not a refutation]`

A subject in an `n`-runner arrangement has at most `n − 1` distinct positive differences
(at most, not exactly: `|v i − v k|` collapses when two runners are equidistant in speed,
e.g. `v = (0,1,2)`, `k = 1` gives the single difference `1`).

The cascade-native termination results in the tree, all for a variable `n`:

| differences `k` | arrives within | holds for | declaration |
|---|---|---|---|
| `≤ 2` | 1 move | `n ≥ 3` | `FewDifferences.two_diffs_stop_within_one_move` |
| `≤ 3` | 3 moves | `n ≥ 4` | `FewDifferences.three_diffs_stop_within_three_moves` |
| `≤ 4` | 7 moves | `n ≥ 6` | `FourDifferences.four_diffs_stop_ge_six` |
| `≤ k` | `2^(k−1) − 1` moves | `n ≥ max(9, 2^(k−1))` | `FourDifferences.stops_slowest_recursion` |

To close order `n` inside the framework one needs the **diagonal** `k = n − 1` at that `n`:

| order | needs | available | |
|---|---|---|---|
| `n = 3` | 2 diffs at `n = 3` | `n ≥ 3` | **closed** |
| `n = 4` | 3 diffs at `n = 4` | `n ≥ 4` | **closed** |
| `n = 5` | 4 diffs at `n = 5` | `n ≥ 6` | **open** |
| `n = 6` | 5 diffs at `n = 6` | `n ≥ 16` | **open** |
| `n = 7` | 6 diffs at `n = 7` | `n ≥ 32` | **open** |
| `n = 8` | 7 diffs at `n = 8` | `n ≥ 64` | **open** |

The diagonal is closed at 3 and 4 and breaks at 5. `stops_slowest_recursion` requires
`2^(k−1) ≤ n`, so at `k = n − 1` it requires `2^(n−2) ≤ n`, which fails for every `n ≥ 5`.
It is a few-differences result and never reaches the diagonal.

**So the framework does not self-close at 5, 6 or 7 any more than at 8.** The n=8 frontier
is not an artefact of eight being large; it is the diagonal, and it is open from 5 upward.

### 3.1 Why `n = 5` is not a near miss

`four_diffs_stop_ge_six` rests on a counting bound, `FourDifferences.g_count_bound`:

> `g n 1 · (g n 3)² ≤ n − 1`,  where `g n m = ∏_{j=1}^{m} (j + 1/n)/(j − 1/n)`

Evaluated exactly (`fractions.Fraction`):

| `n` | `g n 1 · (g n 3)²` | `n − 1` | holds |
|---|---|---|---|
| 4 | 10.68899 | 3 | no |
| 5 | 6.58503 | 4 | no |
| 6 | 4.78735 | 5 | **yes** |
| 7 | 3.81854 | 6 | yes |
| 8 | 3.22532 | 7 | yes |

The `6 ≤ n` hypothesis is exactly where this bound turns over, and `n = 6` is tight
(4.787 against 5). At `n = 5` the bound fails by a factor of about 1.6, so relaxing the
argument will not reach it — four differences at `n = 5` needs a different argument, not a
sharper constant.

---

## 4. What `n = 5, 6, 7` have that `n = 8` does not

At those orders the conjecture is **a theorem in this repository**:
`intLRC_five`, `intLRC_six`, `intLRC_seven`, each axiom-clean with no `sorry`
(`LRC/SmallN/IntLRC_5.lean`, `IntLRC_6.lean`, `IntLRC_7.lean`).

By §2's equivalence, a proof of loneliness **is** a proof that the cascade arrives. So at
`n = 5, 6, 7` the framework's Existence statement can be discharged **unconditionally**,
from a theorem already held, rather than left equivalent to an open conjecture. That is a
thing `n = 8` cannot have, and it is the sense in which the framework can be taken to the
same level at 5, 6 and 7 — and past it.

**This bridge does not exist yet.** A grep of `Cascade/`, `Spec/` and `ConstructionN/` finds
no use of `intLRC` anywhere. Building it is real work, and it has three obstacles, all
stateable:

1. **Shape.** `intLRC n` takes `speeds : Fin (n−1) → ℕ` with `StrictMono`, positivity and
   `Finset.gcd univ speeds = 1`. The framework has a `Finset ℝ`, unordered, of size `≤ n − 1`.
   Sorting and the `gcd = 1` normalisation (scale by `g`, and `t ↦ t/g` carries the witness
   back) are both needed.
2. **Collapse.** `diffSet` can have **fewer** than `n − 1` elements, so the arrangement can
   present `intLRC n` with too few speeds. Padding to `n − 1` distinct positive integers
   keeps `gcd = 1` and the witness restricts, but the padding has to be constructed.
3. **Real speeds.** `intLRC` is integer-speed. The reduction to real speeds,
   `Theorem121_Main.theorem121_LRC_real`, is **`sorry`** in this tree (a standard argument,
   Bienia et al. 1998, stated without proof at line 337). So without it this route closes
   Existence at `n = 5, 6, 7` for **integer arrangements only**.

Obstacle 3 is the one that decides how much the bridge delivers. Obstacles 1 and 2 are
bookkeeping; 3 is a real piece of missing mathematics, though a standard one.

---

## 5. The two routes, stated plainly

**Route A — native.** Prove the diagonal `k = n − 1` at `n = 5` (four differences at five),
then 5 at 6, then 6 at 7. Closes each order inside the framework, for real speeds, with no
import. The `n = 5` case is a single bounded target and the existing counting argument does
not reach it (§3.1). Whether the statement is even true at `(k=4, n=5)` is being checked
empirically — pre-registration at `docs/n8/PREREG_N5_FOUR_DIFF_v1.md`.

**Route B — bridge.** Build `intLRC n → LonelyForSubject` and compose with §2. Delivers
unconditional Existence at 5, 6, 7 immediately for integer arrangements, and for real
arrangements once `theorem121_LRC_real` is discharged. Imports someone else's machinery,
which the framework-boundary audits have flagged before
(`docs/n8/FRAMEWORK_BOUNDARY_AUDIT_v3.md`), so it validates the equivalence rather than the
framework's self-sufficiency.

They are not exclusive and they answer different questions. Route A asks whether the cascade
closes small orders on its own terms; Route B asks whether the door equivalence is
load-bearing enough to carry a known theorem into the framework's objects.

---

## 6. Grades

| claim | grade |
|---|---|
| `doors_agree` at every `n ≥ 2`, four doors, both directions | `[PROVED — LRC.SpecN.doors_agree, axiom-clean]` |
| instantiations at `n = 5, 6, 7` | `[PROVED — doorsN_check_v1.out]` |
| termination table of §3 | `[PROVED — the four cited declarations]` |
| the diagonal is open for every `n ≥ 5` | `[PROVED — arithmetic on the cited hypotheses: 2^(n−2) ≤ n fails for n ≥ 5]` |
| `g_count_bound` fails at `n ≤ 5` | `[VERIFIED — exact rational evaluation, §3.1]` |
| no `intLRC` bridge exists in the tree | `[VERIFIED — grep of Cascade/, Spec/, ConstructionN/]` |
| `theorem121_LRC_real` is `sorry` | `[VERIFIED — Theorem121_Main.lean:346]` |
| the cascade arrives for 4 differences at `n = 5` | **untested** — pre-registered, not yet run |
