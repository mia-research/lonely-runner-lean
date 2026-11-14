# Order 8 (n = 8 Lonely Runner): the Lean kernel and the gap register

**T. Palelei.** Transfer package, v1, 2026-11-11. Companion to `N8_TRANSFER_SUMMARY_v1.md` (read that first for the framework and the history) and `N8_APPENDIX_ON_REQUEST_v1.md`.

This file is for a reader who has **only this folder**. It states what the Lean kernel in `lean_kernel/` proves, what it leaves as hypotheses, and what each hypothesis needs. Grades: **[L]** compiled in Lean with `#print axioms` giving only `propext`, `Classical.choice`, `Quot.sound`; **[T n/N]** exact machine test over a stated finite population; **[P]** hand proof; **[OBS]** observation; **[OWED]** stated, not proved.

---

## 1. What is in `lean_kernel/` and how to check it

Sixteen Lean files, 9,676 lines, copied from the working tree `LonelyRunnerFresh/Fresh/` (3,203 files). They are the import closure of the top theorem, with one cut: `FilterSkeleton.lean` has its "shape bridge" fragment removed, because that fragment pulled in about 660 further modules and the top theorem does not use it. Nothing else is changed. `KernelProbe.lean` is new (section 4).

| file | lines | role |
|---|---|---|
| `Framework.lean` | 165 | the objects: arrangement, disparity set, `d_min`, isolation, the move, the cascade; the target `LonelyRunnerEight` |
| `Cascade.lean` | 476 | the cascade's proved properties: a fixed point is the first lonely instant; `cascadeFixes_iff_isolation`; `CascadeForm ↔ LonelyRunnerEight` |
| `KTaxonomy.lean` | 1,231 | the landing (`StabilizesAtMin`), openers, the 14 outcome labels as predicates, `distInt_ge_eighth_iff` |
| `Localisation.lean`, `OneMoverA.lean`, `CascadeLanding.lean` | 2,925 | support; only `OneMover.inWay_of_window` is used by the kernel |
| `FrontierFamilyCap.lean` | 204 | `CarvesOneSeven`; "first landing is at or before every lonely instant"; the frontier cap `511/31` |
| `FilterSkeleton.lean` (trimmed) | 306 | windows `W₀ = [1,7]`, `W₁ = [9,15]`; `CascadeLandsBelow17`; `lonelyRunnerEight_of_allLandBelow17` |
| `CarveExclusionCerts.lean` | 556 | certificate schemas: fixed clear point, window type, plane split, dyadic-box totality |
| `PinchCert.lean` | 461 | fourth schema: the pinch point on a tangency plane |
| `FilterAssembly.lean` | 1,326 | **the top theorem `filterAssembly`** and its six hypotheses |
| `SpineSound.lean`, `SpineTotalData.lean` | 953 | the conflict engine for the 73 "chain" boxes; three no-go lemmas |
| `BandNoCarve.lean`, `BandPinchData.lean` | 743 | the band `(17, 49]`: `BandCertData → OutsideBelow17`; the seven pinch windows |
| `KernelProbe.lean` | 25 | two facts about the hypotheses' shape (section 4) |

**Check recorded 2026-11-11** (`lean_kernel/check_kernel_2026_11_11.out`): all 16 files compile with exit 0; 256 `#print axioms` reports, every one a subset of `[propext, Classical.choice, Quot.sound]`; `sorry`, `native_decide` and `axiom` counts are 0 in every file. Lean `v4.29.1`, Mathlib revision `5e932f97dd25535344f80f9dd8da3aab83df0fe6`. To re-run: `lake update && lake exe cache get && lake build` with the `lakefile.toml` supplied, or `./check_kernel.sh` with `LEAN_PATH` pointing at a built Mathlib.

A caution that has cost time before: a `def … : Prop` is type-checked, never proved. A false `Prop` used only as a hypothesis passes every axiom and `sorry` scan. Two such statements in this kernel are false or vacuous as written (section 4). Every `Prop` in the tree carries a `-- STANDING: DEFINITION` or `-- STANDING: OWED` tag; read the tag, not the build status.

---

## 2. The objects, in plain mathematics and in Lean

Eight runners with distinct positive real speeds `v : Fin 8 → ℝ`. Fix one runner `k`, the **subject**. Its **disparities** are `|v_i − v_k|` for the other seven; `d_min = m` is the least. A **reading** is `ρ = d/m ≥ 1`; one reading equals 1. No runner is ever stationary: the subject has positive speed, and readings are differences from it.

`distInt x` is the distance from `x` to the nearest integer. The subject is **isolated** (lonely) at `t` when `distInt(d·t) ≥ 1/8` for every disparity `d` (closed condition: exactly `1/8` counts).

```lean
def IsArrangement (v : Fin 8 → ℝ) : Prop := (∀ i, 0 < v i) ∧ Function.Injective v
noncomputable def disparitySet (v : Fin 8 → ℝ) (k : Fin 8) : Finset ℝ :=
  (Finset.univ.erase k).image (fun i => |v i - v k|)
def IsDmin (v : Fin 8 → ℝ) (k : Fin 8) (m : ℝ) : Prop := IsLeast (disparitySet v k : Set ℝ) m
def IsolatedAt (v : Fin 8 → ℝ) (k : Fin 8) (t : ℝ) : Prop :=
  ∀ i, i ≠ k → (1 / 8 : ℝ) ≤ distInt ((v i - v k) * t)
def Isolation (v : Fin 8 → ℝ) (k : Fin 8) : Prop := ∃ t : ℝ, 0 < t ∧ IsolatedAt v k t
def LonelyRunnerEight : Prop := ∀ v : Fin 8 → ℝ, IsArrangement v → ∀ k, Isolation v k
```

Note the target asks for an isolation of **every** runner, which is the usual statement of the conjecture (any runner can be taken as the subject).

**The cascade.** A runner at disparity `d` is **in the way** at `t` when `distInt(d·t) < 1/8`. Its **next opening** after `t` is the instant it next stands exactly `1/8` past a lap line. One **move** goes to the largest next opening among the runners in the way, and stays put if none is in the way. The cascade is the sequence of moves from the **bound** `t₀ = 1/(8·d_min)`.

```lean
def InWay (d t : ℝ) : Prop := distInt (d * t) < 1 / 8
noncomputable def nextOpening (d t : ℝ) : ℝ := (((⌈d * t - 1 / 8⌉ : ℤ) : ℝ) + 1 / 8) / d
def IsMove (ds : Finset ℝ) (t t' : ℝ) : Prop :=
  ((∀ d ∈ ds, ¬ InWay d t) ∧ t' = t) ∨
  (∃ d ∈ ds, InWay d t ∧ t' = nextOpening d t ∧ ∀ d' ∈ ds, InWay d' t → nextOpening d' t ≤ t')
```

**The `R` coordinate.** Normalise so the least reading is 1 and write an instant as `t = R/(8·d_min)`. Then the cascade starts at `R = 1`, and reading `ρ` is in the way at `R` exactly when `ρR ∈ (8j−1, 8j+1)` for some integer `j` (the **zone** of lap `j`), and clear exactly when `ρR ∈ [8j+1, 8j+7]`. The reading 1 itself is clear exactly on the **windows** `W_j = [8j+1, 8j+7]`: `W₀ = [1,7]`, `W₁ = [9,15]`, and so on.

**A carve.** The readings **carve `[1,7]`** when every `R ∈ [1,7]` has some reading in the way, that is, when the open zones of the readings cover `W₀`:

```lean
def CarvesOneSeven (rs : Finset ℝ) : Prop :=
  ∀ R : ℝ, 1 ≤ R → R ≤ 7 → ∃ ρ ∈ rs, ∃ j : ℤ,
    ((j : ℝ)) * 8 - 1 < ρ * R ∧ ρ * R < ((j : ℝ)) * 8 + 1
def NoCarve (g : Fin 7 → ℝ) : Prop := ¬ CarvesOneSeven (Finset.image g Finset.univ)
```

**Lands below 17.** The cascade reaches a fixed point after `N` strict moves, and that landing has `R ∈ W₀ ∪ W₁`:

```lean
def StabilizesAtMin (ds : Finset ℝ) (t₀ : ℝ) (N : ℕ) : Prop :=
  cascadeSeq ds t₀ (N + 1) = cascadeSeq ds t₀ N ∧ ∀ n < N, cascadeSeq ds t₀ n < cascadeSeq ds t₀ (n + 1)
def InWindow01 (m T : ℝ) : Prop :=
  ∃ j : ℤ, 0 ≤ j ∧ j ≤ 1 ∧ 8 * m * T ∈ Set.Icc (((8 * j : ℤ) : ℝ) + 1) (((8 * j : ℤ) : ℝ) + 7)
def CascadeLandsBelow17 (ds : Finset ℝ) (m : ℝ) : Prop :=
  ∃ N, StabilizesAtMin ds (1 / (8 * m)) N ∧ InWindow01 m (cascadeSeq ds (1 / (8 * m)) N)
def AllArrangementsLandBelow17 : Prop :=
  ∀ v : Fin 8 → ℝ, IsArrangement v → ∀ (k : Fin 8) (m : ℝ), IsDmin v k m →
    CascadeLandsBelow17 (disparitySet v k) m
```

---

## 3. What the kernel proves [L]

All names below are in the check output with the standard axioms only.

**The cascade is sound and exact.**
- `Fresh.Cascade.fixed_is_first_isolation`: a fixed point of the cascade from the bound is the first lonely instant.
- `Fresh.Cascade.cascadeFixes_iff_isolation`: for an arrangement and its `d_min`, the cascade reaches a fixed point **if and only if** the subject has an isolation. So "the cascade lands" is not weaker or stronger than the conjecture for that subject; it is the same statement (`cascadeForm_iff : CascadeForm ↔ LonelyRunnerEight`).
- `Fresh.FrontierFamilyCap.first_landing_le_lonely`: the landing is at or before every positive lonely instant. Hence: **exhibit any one lonely instant `s`, and the cascade lands at or before it.**

**The window law.**
- `dmin_clear_iff_window`: the reading 1 is clear at `t` iff `R` lies in some `W_j`. `landing_window`: every landing is in a window. `window_avoids_gap`: no landing in `(7,9)`. `noMove_R_one`: a cascade with no move lands at `R = 1`. `dmin_cannot_open_W0`.
- `outcomeLabelComplete_iff`, `allLabelled_iff_allLandBelow17`: the 14 outcome labels (no move; opener rank 2 to 7 in `W₀`; opener rank 1 to 7 in `W₁`) are complete exactly when every arrangement lands below 17.

**The core bridge** (`FilterAssembly.cascadeLandsBelow17_of_clearPoint`): if some `s ∈ [1,7] ∪ [9,15]` has every normalised reading clear at `R = s`, the cascade lands below 17. Together with `notCarve_witness` (`NoCarve g` iff there is a lonely instant with `R ∈ [1,7]`) this turns the whole problem into exhibiting a clear point.

**The reduction to the target.** `lonelyRunnerEight_of_allLandBelow17 : AllArrangementsLandBelow17 → LonelyRunnerEight`.

**The arrangement-to-box map.** `coverTuple`: an arrangement whose readings are all at most 17 gives a reading vector `g : Fin 7 → ℝ` (padded with 1) and the nearest-integer tuple `n i = ⌊g i + 1/2⌋ ∈ [1,17]`, with `g i` in the face `[max(n−½, 1), n+½]`. `bandTuple` is the same with bound 49.

**Certificate soundness.** Each is an implication over a closed box of readings:
- `fixedClear_noCarve` (a rational `R₀ ∈ [1,7]` whose scaled faces sit in closed gaps), with the integer form `fixedClearCert_of_dyadic_int`;
- `windowCert_noCarve` (a clear window `[X, Y] ⊆ [1,7]` whose ends are functions of the readings);
- `noCarve_split` (a box cut by a plane, each side certified);
- `Pinch.tangentPlane_noCarve`, `pinchIntCert_of_dyadic` (on a tangency plane `(8b+1)ρ₇ = (8a+1)ρ₅` the point `R* = (8b+1)/ρ₅` is clear);
- `clearPointOfCert`, `noCarveOfM1`, `existsGapJ`, `faceClear` (an integer box certificate `ZoneClearCert` gives a clear point for every real reading vector in the box);
- `cL_one`, `m1Cond_of_cL`: **if no reading's nearest integer is in `{7, 8, 9, 15, 16, 17}`, then `R = 1` is clear for the whole box** (the closed form C_L);
- `box_totality`, `refine_cover` (dyadic boxes cover; children cover the parent).

**The chain-box engine.** `SpineSound.joinEdge_conflict`, `famRefutes`: a "word" demand `ρ_x/ρ_y < A/B` and a chain cap `ρ_y/ρ_x ≤ C/D` with `A·C ≤ B·D` cannot both hold. `refute_box_*` for the five two-sided boxes with their integer data.

**The band.** `BandNoCarve.outsideBelow17_of_bandData : BandCertData → OutsideBelow17`; `outsideBelow17_of_avoidsAtOne` (the sub-band whose every reading is clear at `R = 1`). `BandPinchData.pinchWindow_2645 … 2727`: the seven window theorems for the pinch family.

**Three no-go lemmas [L]** (`SpineTotalData`): `capDerivedDemand_unsat`, `intervalForcedDemand_capUnsat`, `intervalForcedPair_invalid`. Face-interval arithmetic alone cannot discharge the chain-box totality: any such proof is vacuous.

**The top theorem.**

```lean
theorem filterAssembly (hCover : CoverData) (hCP : ClearPointOfCert) (hOneS : OneSidedSound)
    (hPair : PairwiseSound) (hOutside : OutsideBelow17) (hTail : TailBelow17) :
    Fresh.LonelyRunnerEight
```

`ClearPointOfCert` is proved (`clearPointOfCert`). `OutsideBelow17` is proved from `BandCertData`. The other hypotheses are open. Their definitions:

```lean
def InRange17 (n : Fin 7 → ℤ) : Prop := ∀ i, 1 ≤ n i ∧ n i ≤ 17
def M1Cond (n : Fin 7 → ℤ) : Prop := ∃ r base : ℤ, ZoneClearCond n r base 0
def M4Cond (n : Fin 7 → ℤ) : Prop := ∃ r base : ℤ, ZoneClearCond n r base 0
def JoinFam (n : Fin 7 → ℤ) (fam : Finset JoinEdge) : Prop :=
  ∀ e : {e // e ∈ fam}, 0 < e.1.B ∧ 0 < e.1.D ∧ e.1.A * e.1.C ≤ e.1.B * e.1.D ∧
      (e.1.A % 8 = 1 ∨ e.1.A % 8 = 7) ∧ (e.1.C % 8 = 1 ∨ e.1.C % 8 = 7)
def OneSidedCond (n : Fin 7 → ℤ) : Prop := ∃ fam : Finset JoinEdge, JoinFam n fam
def PairwiseCond (n : Fin 7 → ℤ) : Prop := ∃ fam : Finset JoinEdge, JoinFam n fam
def CoverData : Prop :=
  ∀ n : Fin 7 → ℤ, InRange17 n → M1Cond n ∨ M4Cond n ∨ OneSidedCond n ∨ PairwiseCond n
def OneSidedSound : Prop :=
  ∀ (n : Fin 7 → ℤ) (fam : Finset JoinEdge), InRange17 n → JoinFam n fam →
    ∀ (g : Fin 7 → ℝ), (∀ i, FaceLo n i ≤ g i ∧ g i ≤ FaceHi n i) →
      CarvesOneSeven (Finset.image g Finset.univ) →
      ∃ s, 9 ≤ s ∧ s ≤ 15 ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (g i * (s / 8))
def PairwiseSound : Prop :=
  ∀ (n : Fin 7 → ℤ) (fam : Finset JoinEdge), InRange17 n → JoinFam n fam →
    ∀ (g : Fin 7 → ℝ), (∀ i, FaceLo n i ≤ g i ∧ g i ≤ FaceHi n i) →
      Fresh.Certs.NoCarve g ∨ (∃ s, 9 ≤ s ∧ s ≤ 15 ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (g i * (s / 8)))
def OutsideBelow17 : Prop :=
  ∀ v, IsArrangement v → ∀ (k : Fin 8) (m : ℝ), IsDmin v k m →
    (∃ d ∈ disparitySet v k, 17 * m < d) → (∀ d ∈ disparitySet v k, d ≤ 49 * m) →
      CascadeLandsBelow17 (disparitySet v k) m
def TailBelow17 : Prop :=
  ∀ v, IsArrangement v → ∀ (k : Fin 8) (m : ℝ), IsDmin v k m →
    (∃ d ∈ disparitySet v k, 49 * m < d) → CascadeLandsBelow17 (disparitySet v k) m
def BandCertData : Prop :=
  ∀ g : Fin 7 → ℝ, BandRange g → BandFixedR0 g ∨ BandWindowType g ∨ BandSeamPlane g ∨ BandPinch g
```

---

## 4. Three defects in the shape of the hypotheses

These were found while preparing this package. The first two are checked in Lean (`KernelProbe.lean`); the third follows from two theorems already in the working tree. None affects the truth of any proved theorem. They affect what the remaining work **is**, so they come before the gap list.

**D1. `CoverData` is provable as stated and carries no data [L, `probe_coverData`].** `OneSidedCond n` asks only that *some* family satisfies `JoinFam`, and the empty family does. So `CoverData` holds for every tuple by its third disjunct, and the 74,613-box enumeration is nowhere in the Lean statement.

**D2. `PairwiseSound` and `OneSidedSound` quantify over every family, including the empty one [L, `probe_pairwise`].** As written, `PairwiseSound` asserts, for every box in range and every reading vector in it, "no carve of `[1,7]`, or a clear point in `[9,15]`". That is the whole inside statement, not a statement about five boxes. `OneSidedSound` likewise asserts "a carve of `[1,7]` implies a clear point in `[9,15]`" for every box. Under D1 and D2 the first four hypotheses collapse to one:

> **(Inside)** For every reading vector with all readings in `[1, 17.5]` and least reading 1: `[1,7]` is not carved, or some `s ∈ [9,15]` is clear for every reading.

**D3. `BandCertData` is false as stated.** Each of its four disjuncts implies `NoCarve g` (`clearPoint_of_fixedR0`, `clearPoint_of_windowType`, `noCarve_of_seamPlane`, `noCarve_of_pinch`; the first two give a clear point in `[1,7]`). The working tree has `Fresh.FrontierCarveCapFalse.carve_ce` [L]: the readings `1, 2767/1000, 749/200, 957/200, 123/20, 683/100, 11889/500` carve `[1,7]`, and the largest, `23.778`, is in the band. So no disjunct can hold for that vector. The exact cascade lands it at `R = 6500/683 ≈ 9.52` in `W₁`, so `OutsideBelow17` itself is not contradicted; the data hypothesis is missing a fifth disjunct for a `W₁` clear point. This is the "X24" family (carves with `ρ₇ ∈ (23, 25)`), which the module's own docstring lists as needing separate data. I have stated this from the two existing theorems; I did not compile the one-line combination.

**D4 (a shape mismatch, to be checked).** `M4Cond` is defined with the same shape as `M1Cond`: one rational clear point `r/base` valid for the whole integer box. The M4 computation is a search tree over sub-boxes (median 34 leaves per box, up to hundreds), which shows "no reading vector in the box carves `[1,7]`" leaf by leaf. A box that needed a tree most likely has no single box-wide clear point, so the 12,540 M4 verdicts probably cannot be instantiated as `M4Cond`. The Lean form that matches the computation is a leaf-level statement: every `g` in the box lies in a sub-box carrying its own certificate (the `InDyadicBox` / `refine_cover` machinery already in `CarveExclusionCerts.lean`).

**What the target reduces to, stated without the defective wrappers.** Write `Z(ρ) = ⋃_j ((8j−1)/ρ, (8j+1)/ρ)` for the open set of `R` where reading `ρ` is in the way.

> **(S)** For every set of at most seven reals `ρ ≥ 1` containing 1, some `s ∈ [1,7] ∪ [9,15]` lies outside `Z(ρ)` for every `ρ` in the set.

`(S)` implies `LonelyRunnerEight` through theorems already proved in the kernel (`cascadeLandsBelow17_of_clearPoint`, `lonelyRunnerEight_of_allLandBelow17`). `(S)` is stronger than the conjecture: it places an isolation of every runner within `15/(8·d_min)`, inside the first two windows of that runner's nearest speed-neighbour. No counterexample to `(S)` has been found in any search (section 5). If `(S)` should fail in the tail, the conjecture needs only `Isolation`, and the tail hypothesis can be restated with a larger bound or with none; the kernel's `isolation_of_cascadeLandsBelow17` is the only place the number 17 enters the final step.

`(S)` splits by the largest reading `ρ_max`: **inside** (`ρ_max ≤ 17`), **band** (`17 < ρ_max ≤ 49`), **tail** (`ρ_max > 49`). The 49 is a bookkeeping choice; computations run to 95.

---

## 5. The gap register

Each gap states the mathematical content, what the computation has established, what is in Lean, and what is missing.

### G1. Inside, boxes with a fixed clear point (62,000 of 74,613 boxes)

*Content.* The six non-least readings, each rounded to its nearest integer in `[1,17]` and sorted, give one of `C(22,6) = 74,613` tuples (the least reading is pinned at 1). For 62,000 of them one rational `R₀ ∈ [1,7]` is clear for every reading vector in the box.

*Computed.* [T 62,000] by a closed form: C_L (no nearest integer in `{7,8,9,15,16,17}`, so `R₀ = 1`; `C(16,6) = 8,008` tuples) plus 36 "gap-edge" forms, each a specific rational `R₀` at an interior zone edge.

*In Lean.* C_L in full (`cL_one`, `m1Cond_of_cL`), and the soundness chain to the landing.

*Missing.* The 36 gap-edge forms as theorems, and the decidable check that C_L plus the 36 forms cover the 62,000. Both are finite integer checks of the kind `decide` or `omega` handles; the 36 forms would need to be re-derived (a short script: for each tuple, search rationals `R₀ = (8j±1)/(2n±1)`-type edge points).

### G2. Inside, boxes needing a subdivision tree (12,540 boxes)

*Content.* No reading vector in the box carves `[1,7]`, but the clear point moves with the readings.

*Computed.* [T 12,540] by a depth-first subdivision with exact leaf certificates (two stragglers needed a 400,000-node budget). The leaf certificates come from a closed set: every leaf's kill is one of three schemas (frontier-ceiling `p·B ≤ 7A`, entry-block, advance-block) keyed by (rank, exit numerator `8j+1`); 40 types observed inside a 90-type envelope; exit numerators `9, 17, …, 97`. A single fixpoint algorithm "C₃" (states keyed by last rank and exit numerator, merged componentwise) replaces 10,211 of the 12,540 trees. **2,329 boxes are not reached by C₃** and are held only by their trees; why C₃ fails on them is recorded as not understood (they are deep: 1,756 of 2,329 have depth at least 15; median 385 leaves against 34).

*In Lean.* The schemas' soundness (`fixedClear_noCarve`, `windowCert_noCarve`, `refine_cover`). No M4 data. See D4.

*Missing.* A Lean form of the tree or of C₃, and the 2,329.

### G3. Inside, the 73 chain boxes

*Content.* These are the boxes where a carve of `[1,7]` is possible. For them the claim is that `W₀` and `W₁` are never both carved: a carve of `[1,7]` forces a clear point in `[9,15]`.

*Computed.* 68 boxes are "one-sided": no chain of zones can cover `[9,15]` on the box at all once the `W₀` chain's seam inequalities are added. 5 boxes are "two-sided": `(1,2,3,4,5,6,7)` (the arithmetic progression's own box), `(1,2,3,4,5,6,8)`, `(1,3,4,4,5,6,7)`, `(1,3,4,5,5,6,8)`, `(1,3,4,5,6,7,8)`. On these, both chains exist separately, and every pair (a `W₁` covering word, a `W₀` chain) contains a raw demand contradicting a chain cap, `d·d̄ ≤ 1`: [T 2,522,259 pairs / 0 exceptions]. Example: box `(1,2,3,4,5,6,8)` needs `ρ₂/ρ₆ < 25/63` from the `W₁` word and `ρ₆/ρ₂ ≤ 17/7` from the `W₀` chain, and `25·17 = 425 ≤ 441 = 63·7`. The largest landing over these boxes is `26433/2209 ≈ 11.97`.

*In Lean.* The conflict engine and the five boxes' top conflicts (`refute_box_*`). The family data for the five (`spineFamData_*`).

*Missing (the true lift, both directions).* (a) A carve of `[1,7]` by a real reading vector **realises** one of the enumerated `W₀` chains, with its caps holding on that vector. (b) Absence of a clear point in `[9,15]` realises one of the enumerated `W₁` words. Both are finite covering statements over the reals: a compact interval covered by finitely many open zones has a finite subcover that can be ordered into a chain with strictly overlapping consecutive zones (the "exact cover criterion", [P] by hand, not in Lean). The three no-go lemmas show this cannot be bypassed with interval arithmetic on the box faces. Per-box family dumps for the 68 one-sided boxes also need regenerating (the stored file aggregates across boxes).

### G4. The band `17 < ρ_max ≤ 49`

*Content.* No carve of `[1,7]`, except in the X24 family `ρ_max ∈ (23, 25)` where carves exist and the landing is in `W₁`.

*Computed.* No carve for `ρ₇ ∈ [17,23) ∪ [25,95)`, by dyadic boxes `ρ_i ∈ [n_i/D, (n_i+1)/D]` each certified by one of: a fixed `R₀` (the bulk), a window type, a plane split (`h₁ = ρ₇ − 7ρ₅`, `h₂ = 3ρ₆ − 5ρ₄`, and in `[49,51)` `7ρ₅ − 9ρ₄`, `ρ₇ − 7ρ₆`), or the pinch on `h₃ = 25ρ₇ − 89ρ₅` (509 boxes in `[17,23)`). Depths to `D = 512`. For X24: 96 exact carves found, all landing in `W₁` with `R < 26433/2209`; the record's earlier exhaustive tree for `ρ₇ ≤ 25` (2,094,794 nodes, float linear programming with exact spot checks) gives the same supremum.

*In Lean.* `BandCertData → OutsideBelow17`; the `R = 1` sub-band; the seven pinch windows and one worked box.

*Missing.* (i) A corrected `BandCertData` with a `W₁` disjunct (D3), and a certificate for X24 in exact arithmetic (the existing tree is float-based). (ii) The off-plane sides of the 509 pinch boxes need a fifth schema: 0 of their 1,018 side certificates extend to axis-aligned boxes, so "box plus one linear inequality plus window data" is required. (iii) The per-box data itself: about `10⁹` nodes were searched; window types compress the leaves of `[29,41)` to 17 types (327,661 boxes) but do not compress the fixed-`R₀` bulk of `[25,29)` (1,961 types for 125,246 roots). A Lean discharge by enumeration is not practical; this gap needs either the tail argument of G5 pushed down to 25, or a structural reason for the fixed-`R₀` bulk.

### G5. The tail `ρ_max > 49` (the open mathematics)

*Content.* For six sorted readings with `ρ₇ ≥ 25` the open zones do not cover `[1,7]`. (With the X24 exception below 25, this subsumes G4.)

*Computed.* 0 uncertified boxes for `ρ₇ < 95`. Random and annealed searches to `ρ₇ = 80` find no carve above 25.

*Understood so far [P unless marked].*
- **Chain type.** A carve gives a greedy chain of zones `(reading, lap)` across `[1,7]`. Consecutive zones `(p, j_p) → (q, j_q)` must overlap strictly: `ρ_q/ρ_p > (8j_q − 1)/(8j_p + 1)`, a linear inequality. The first zone covers `R = 1`, the last covers `R = 7` (so the last reading satisfies `7ρ < 8j+1`).
- **Cycle-product law.** Take the digraph of a chain type's links with weights `(8j_q−1)/(8j_p+1)`, plus order edges `ρ_p ≤ ρ_{p+1}` of weight 1. If any cycle has product `≥ 1` the type is infeasible (product exactly 1 is a tangency: equality only, and open zones cannot cover a compact interval at equality).
- **Tops as products.** The largest `ρ₇` of a feasible type is a product of link ratios from the pin `ρ₆ = 7`: `511/31 = (73/31)·7` for the lap-2 strip (`15 < ρ₇ < 17`), `86989/3565 = 7·(17/31)(17/23)(129/15)` for the lap-3 strip (`23 < ρ₇ < 25`).
- **Census near the frontier** [T 1,096/1,096 types]: 1,052 dead by cycle product, 17 tangent, 27 feasible but leaving gaps; of the 27, 25 have every gap locked by an exact Farkas certificate and 2 re-route once and then die with cycle product `124775/123369 > 1`.
- **A one-dimensional lemma** (E387): every component of the clear set of readings 2 to 6 inside `[1,7]` must be shorter than `2/ρ₇`.
- **Ladder law** [T 1,420/1,420]: between two appearances of the same reading at laps `j < j'` in a strict chain, the intervening zones' laps `k` satisfy `∏(8k+1)/(8k−1) > (8j'−1)/(8j+1)`.

*Missing.* (a) Re-route completeness: continuations were tested at one point per open facet, not over the facet. (b) The **strip-class cap**: for every strip `k ≥ 4` (`ρ₇ ∈ (8k−1, 8k+1)`) the product cap is below `(8k−1)/7`. This needs a bound on the middle readings of a carve; observed [OBS, float] `ρ₂…ρ₆ ≲ 4.82, 5.28, 6.21, 7.10, 8.15` in every tree run, only the top reading grows. A relaxation with free middle readings was refuted as sufficient (witness walk with value `2064884481/117649`). (c) A block-gap lemma: the longest stretch with no joint clear instant for `m` readings is bounded in units of the slowest, proved for `m ≤ 3` only (`2m/(b₁(4−m))`); `m = 4, 5, 6` open, and it is not known whether the supremum is finite for `m = 5, 6`.

### G6. Whether "below 17" is the right target for the tail

A choice of target, not a gap in a proof. `(S)` restricts the clear point to `[1,7] ∪ [9,15]`. The data support it to `ρ₇ < 95`. For the conjecture alone, any isolation suffices. A reader attacking the tail may prefer to prove "no carve of `[1,7]` for `ρ₇ ≥ 25`" (which gives a `W₀` landing) or a weaker statement with a larger window; the assembly accepts either with a one-line change.

---

## 6. Statements that looked right and are false (do not rebuild these)

| statement | status | evidence |
|---|---|---|
| A carve of `[1,7]` with `47/7 < ρ₆ < 7`, `15 < ρ₇` forces the seam `31/ρ₆ ≤ 73/ρ₇` (`FrontierCarveCap`) | false [L] | `carve_ce`, `not_frontierCarveCap` |
| "A landing in `W₁` forces `ρ₇ ≤ 511/31`" | false | the X24 family; `511/31` bounds only the lap-2 strip class |
| The plane `h₃ = 25ρ₇ − 89ρ₅` is a seam cycle | false [T 0] | `2225 = 5²·89` has no divisor `≡ 7 (mod 8)`; it is an exit-exit tangency |
| The chain-box totality follows from the box faces | vacuous [L] | the three no-go lemmas |
| The cascade's instants stay within one lap of the nearest runner (`DoorFirstLap`, `d_min·t ≤ 1`) | false | the 28-move case `τ = 2401/1872` |
| The flank can always be taken as the largest disparity | false | `(2, 3, 5, 7, 8, 13, 16)` |
| A fixed modulus-128 residue method settles the one-multiple branch | false | base `{1,2,33,34,35,61}` plus `32` |
| "Every six-reading core plus any real seventh reading" is a smaller problem | it is order eight itself | E644 |
| A class with a free real unit `g` and instant `1/(q·g)` is an arrangement type | it is equivalent to isolation [L] | `NearMultiples.isolation_imp_nearMultiples` |
| Rank words, status words, link words or path types give a finite list | counts grow with height in every encoding tried | E434, E450, E690 |

---

## 7. What else exists in Lean and is not in this kernel

Available on request (see the appendix). None of it is needed to continue from `filterAssembly`.

- **Orders 3 to 7 for all real speeds**, proved in the framework's own terms (nested repository `LonelyRunner/`, `LRC/Spec/`): `lonely_seven_nat`, `existenceAtN_seven`, and the shared integer-to-real transfer `RealTransferN.existenceAtN_of_nat`. Order 7 uses kernel-checked certificates (120 + 10 + 20 parts). These give, for order 8: any subject with at most six distinct disparities is settled.
- **The older order-8 reductions** (not assembled with each other or with this kernel): `OrderEightCasesN.lonely_eight_or_residual` (a whole-number set is lonely at `1/8` or is an `EightResidual` member, 22 arithmetic fields); the one-multiple branch `lonely_or_dvd32`; the block skeleton `lonelyRunnerAt8_of_arrangement_holes` with five owed premises; `lonelyRunnerAt8_of_window` with `WindowBound` owed.
- **Deformation families from the arithmetic progression** (`Fresh/`): one runner moved to any speed, every subject (`s1_all_landing`); two movers with the subject fixed (37 frozen sets); three movers above the least frozen reading; neighbourhoods of the progression to relative radius `1/6` (`ap_nbhd_lands_12`); the ratio condition (`ratio_lands`: all disparities within `[m, 7m]` gives landing at the bound).
- **The view lemmas**: `every_arrangement_viewed`, `lonelyAt_iff_view` (every arrangement at every scale has one grid index and one deviation per reading; lonely at `t` iff every reading's status is ok in the view at scale `1/(8t)`); `isFirst_iff_least_goodM` (the landing is the least class-1 instant at which every reading is good).
- **53 + 10 six-reading cores** with any real seventh reading (`ScaledCoreChain.real_all`, `real_core_*`).
