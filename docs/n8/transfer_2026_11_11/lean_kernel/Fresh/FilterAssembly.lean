import Mathlib
import Fresh.Framework
import Fresh.Cascade
import Fresh.KTaxonomy
import Fresh.FilterSkeleton
import Fresh.CarveExclusionCerts
import Fresh.FrontierFamilyCap

/-!
# The four-branch filter assembly for the n=8 Lonely Runner reduction (E834 skeleton)

Written 2026-11-07.  New file; nothing existing is edited.  This is the assembly skeleton of
the E834 campaign: the four box classes of the J2 admission cover
(`experiments/n8/j2_admit_cover_v1.out`: M1 62,000 / M4 12,540 / CHAIN 73 / OPEN 0 over all
74,613 nearest-integer tuples), the per-class bridge to the landing, the totality-and-split
theorem, and the full composition `CoverData + outside + tail -> LonelyRunnerEight`.

Everything is composed through the EXISTING soundness layer: `Fresh.Certs`
(`fixedClearCert_of_dyadic_int`, `fixedClear_noCarve`, `box_totality`),
`Fresh.FrontierFamilyCap` (`first_landing_le_lonely`, `CarvesOneSeven`,
`lonely_witness_of_not_carved`) and `Fresh.FilterSkeleton` (`CascadeLandsBelow17`,
`InWindow01`, `isolation_of_cascadeLandsBelow17`, `lonelyRunnerEight_of_allLandBelow17`).

Coordinates (E832 convention, as in `Fresh.Certs`): readings normalised by `d_min`, the least
reading is `1`; an instant is `t = R/8` in the `R`-coordinate; reading `ρ` is in the way at
`R` iff `ρR ∈ (8j-1, 8j+1)` for some `j`, and clear iff `ρR ∈ [8j+1, 8j+7]` for some `j`
(`Fresh.KTaxonomy.distInt_ge_eighth_iff`).  Windows: `W₀ = [1,7]`, `W₁ = [9,15]`; "lands
below 17" is `Fresh.FilterSkeleton.InWindow01`, i.e. the landing coordinate `8·m·T` in
`W₀ ∪ W₁`.

The J2 box form.  An arrangement's normalised disparity set
`dsn = (disparitySet v k).image (·/m)` is a Finset of `1 ≤ card ≤ 7` values containing `1`;
its sorted enumeration `L = dsn.sort (· ≤ ·)` gives `g i = L[i]` (padded with `1`, which lies
in its own face) and the tuple `n i = ⌊g i + 1/2⌋`.  The per-coordinate face is
`[max(2·n i − 1, 2)/2, (2·n i + 1)/2]` — exactly the raw box ranges of `j2_admit_mech_v1.py`
(`max(n − 1/2, 1) ≤ ρ ≤ n + 1/2`), plus the least reading's own `n = 1` face.  `CoverData` is
stated over ALL 7-tuples in `[1,17]`; the artifact's 74,613 verdicts are over the sorted
6-tuples of the six non-least readings (least reading pinned at `1`), so the data-side
discharge drops the `n = 1` coordinate: the remaining six faces are the artifact faces
verbatim, and the least reading's extra face `[1, 3/2]` is cleared at `x = 1` by the same C_L
arithmetic (`cL_one` below).  Divergences from the artifacts, recorded:
(i) `Fresh.Certs.fixedClearCert_of_dyadic_int` builds single dyadic cells `[k/D, (k+1)/D]`
while the nearest-integer boxes are width-1 (two cells at `D = 2`); the `W₀` no-carve plug
below therefore passes the reading's own cell `k i = min(⌊2·g i⌋, 2·n i)`, which lies inside
the face — `fixedClearCert_of_dyadic_int` and `fixedClear_noCarve` are used verbatim.
`Fresh.Certs.box_totality` is the fixed-depth form of the same covering (`InDyadicBox 2
⌊2·g⌋ g`); the min-clamp here is its content for the wider boxes (closed boxes tile with face
overlaps, cf. `Fresh.Certs.refine_cover`'s remark).
(ii) `M1Cond`/`M4Cond` share the avoidance shape `ZoneClearCert n 0` because their SOUNDNESS
direction is the same (a box clear point in `W₀`); they differ at the data level (which
artifact mechanism produces the certificate), and the data lemmas are separate.
(iii) `OneSidedCond`/`PairwiseCond` share the raw-edge family shape `JoinFam` because both
kill through E's raw-edge law (`j2_cycle_v12`); they differ in the soundness obligation
(the one-sided kill is conditional on a `W₀` chain, the pairwise kill is not) and in the
data (68 one-sided chain boxes vs the 5 two-sided boxes).

The four classes and their status:
* `M1Cond n` — a `ZoneClearCert n 0`: an exact rational clear point `r/base ∈ [1,7]` over the
  faces, as integer inequalities over the finite zone range `j ∈ [0,33]`.  Fully defined; the
  C_L closed form `cL_one` (no reading in `{7,8,9,15,16,17}` ⟹ `x = 1` clear) is PROVED
  below; the 36 interior gap-edge forms and the 62,000-tuple check are data-side (OWED inside
  `CoverData`).
* `M4Cond n` — the same shape; the 12,540 DFS certificates of
  `j2_admit_cert2_checkpoint.jsonl` must each yield such a certificate (data-side, OWED
  inside `CoverData`).
* `OneSidedCond n` — a `JoinFam` raw-edge conflict family; for the 68 one-sided chain boxes
  the artifact kill is CONDITIONAL on a `W₀` chain (`j2_cycle_v6/v10.out`: IF a `W₀` chain
  exists THEN box+join kills every `W₁` word), so its soundness hypothesis `OneSidedSound`
  is OWED and the bridge splits on whether the arrangement carves `[1,7]`.
* `PairwiseCond n` — the same family shape for the 5 two-sided boxes (E's corrected
  RAW-EDGE LAW, `j2_cycle_v12.py/.out`, superseding v11 Part A: every surviving (W₁ word,
  W₀ chain) pair has a raw word edge conflicting with a chain cap, `d·d̄ ≤ 1`,
  [T 2,522,259 pairs / 0 exceptions]; seamE/seamM forms over `8m±1` numerators with explicit
  intervals).  Its soundness `PairwiseSound` is OWED; the bridge consumes the disjunction
  (no carve, or a `W₁` clear point) it provides.

The bridge chain: box certificate ⟹ per-reading clear point (`FaceClear`, via the gap
selection `ExistsGapJ`) ⟹ lonely instant of the normalised set (the `W₀` no-carve route
plugs through `Fresh.Certs.fixedClearCert_of_dyadic_int` + `Fresh.Certs.fixedClear_noCarve`)
⟹ the cascade lands at or before it (`cascadeSeq_norm` scaling +
`Fresh.FrontierFamilyCap.first_landing_le_lonely`) ⟹ the landing coordinate is in a window
(`Fresh.FilterSkeleton.landing_window`) capped by 15 ⟹ `InWindow01` ⟹
`CascadeLandsBelow17` ⟹ `Isolation`.  PROVED here: the scaling lemmas
(`nextOpening_scale`/`isMove_scale`/`cascadeSeq_norm`/`stabilizes_norm`), the core bridge
`cascadeLandsBelow17_of_clearPoint`, the arrangement-to-tuple construction `coverTuple`, the
C_L closed form `cL_one` (with `m1Cond_of_cL`), the witness transport `notCarve_witness`/
`clear_of_image`, and BOTH composition theorems `allLandBelow17_of_coverData` (the
totality-and-split) and `filterAssembly`.  OWED (hypothesis-carrying, named): `ExistsGapJ`,
`FaceClear`, `ClearPointOfCert`, `NoCarveOfM1` (the per-certificate soundness directions —
each elementary, proofs drafted and iterated but not closed in Lean within this session),
`OneSidedSound`, `PairwiseSound`, `OutsideBelow17` (the `[17,23) ∪ (23,25) X24 ∪ [25,49)`
certificates — four schema classes: fixed-R₀, window-type, seam-cycle-plane, pinch; the
first two already have Lean soundness in `Fresh.Certs`, the pinch is
`Fresh/PinchCert.lean`, in progress), and `TailBelow17` (`[49,∞)`, open), plus `CoverData`
itself (the 74,613-tuple decidable integer check, via the four data lemmas).

Completion note (2026-11-08, closing session): the four M1-branch per-certificate soundness
directions are CLOSED as theorems below (the Props remain as named definitions, unchanged):
`existsGapJ` — the gap selection `J = ⌊(s·FaceLo i − 1)/8⌋` (`s = r/base`), via both floor
bounds plus the avoidance at zone `J+1`, with `J ≥ 0` from `s·FaceLo ≥ 1` and `J ≤ 32` from
`s·FaceLo < 265` (`s ≤ 15` when `w ≤ 1`; `FaceLo ≤ 35/2` when `n i ≤ 17`); `faceClear` — the
selected window gives `distInt ≥ 1/8` via `Fresh.KTaxonomy.distInt_ge_eighth_iff`;
`clearPointOfCert` — the point `s = r/base` with the `w = 0 / w = 1` split; and `noCarveOfM1`
— the `fixedClearCert_of_dyadic_int` plug at depth `D = 2` with the reading's own cell
`k i = min(⌊2·g i⌋, 2·n i)` (in the face: `max(2n−1,2) ≤ k i` needs `n i ≥ 1`; `k i + 1 ≤
2n+1`; the cell contains `g i` by the floor bounds) composed with `fixedClear_noCarve`.
New helpers, all `#print axioms`-clean: `faceLo_ge_one`, `certPoint_bounds`, `div_mul_eight`,
`mul_div_div`, `zoneAvoid_real` (the avoidance's real form, with the zone range `j < 34` as a
hypothesis).  All four closings depend only on `[propext, Classical.choice, Quot.sound]`.
The remaining OWED props (`OneSidedSound`, `PairwiseSound`, `OutsideBelow17`, `TailBelow17`,
`CoverData`) are unchanged; the raw-edge engine direction of the former two is
`Fresh/SpineSound.lean` (2026-11-08, sibling session).
-/

open Classical

namespace Fresh.FilterAssembly

open Fresh Fresh.Cascade Fresh.KTaxonomy Fresh.Certs Fresh.FilterSkeleton
open Fresh.FrontierFamilyCap

/-! ## Coordinate helpers -/

/-- `distInt` is invariant under integer shifts (both ways via `distInt_le`, as `distInt_neg`). -/
theorem distInt_add_int (x : ℝ) (k : ℤ) : distInt (x + k) = distInt x := by
  refine le_antisymm ?_ ?_
  · have h := distInt_le (x + k) ((round x : ℤ) + k)
    have he2 : (((round x : ℤ) + k : ℤ) : ℝ) = (round x : ℝ) + (k : ℝ) := by
      push_cast
      ring
    rw [he2] at h
    have he3 : x + k - ((round x : ℝ) + (k : ℝ)) = x - (round x : ℝ) := by ring
    rw [he3] at h
    rwa [show distInt x = |x - (round x : ℝ)| from rfl]
  · have h := distInt_le x ((round (x + k) : ℤ) - k)
    have he2 : (((round (x + k) : ℤ) - k : ℤ) : ℝ) = (round (x + k) : ℝ) - (k : ℝ) := by
      push_cast
      ring
    rw [he2] at h
    have he3 : x - ((round (x + k) : ℝ) - (k : ℝ)) = x + k - (round (x + k) : ℝ) := by ring
    rw [he3] at h
    rwa [show distInt (x + k) = |x + k - (round (x + k) : ℝ)| from rfl]

#print axioms distInt_add_int

/-- In the way at `R/8` iff the phase `ρR` lies in a zone `(8j-1, 8j+1)` — the `R`-coordinate
form of the way condition, bridging `Fresh.Certs.CarvesOneSeven` and `Fresh.InWay`. -/
theorem inWay_zone_iff {ρ R : ℝ} :
    Fresh.InWay ρ (R / 8) ↔
      ∃ j : ℤ, (j : ℝ) * 8 - 1 < ρ * R ∧ ρ * R < (j : ℝ) * 8 + 1 := by
  constructor
  · intro h
    have hdef : distInt (ρ * (R / 8)) = |ρ * (R / 8) - (round (ρ * (R / 8)) : ℝ)| := rfl
    have hab : |ρ * (R / 8) - (round (ρ * (R / 8)) : ℝ)| < 1 / 8 := by
      rw [← hdef]
      exact h
    have habs := abs_lt.mp hab
    have hmul : ρ * R = 8 * (ρ * (R / 8)) := by ring
    refine ⟨round (ρ * (R / 8)), ?_, ?_⟩
    · have e1 : ((round (ρ * (R / 8)) : ℝ)) * 8 - 1
          = 8 * ((round (ρ * (R / 8)) : ℝ) - 1 / 8) := by
        have hc : ((round (ρ * (R / 8)) : ℤ) : ℝ) = (round (ρ * (R / 8)) : ℝ) := rfl
        rw [hc]
        push_cast
        ring
      have hmul2 : (round (ρ * (R / 8)) : ℝ) * 8 = ρ * R - 8 * (ρ * (R / 8) - (round (ρ * (R / 8)) : ℝ)) := by
        have : ρ * R = 8 * (ρ * (R / 8)) := hmul
        linarith
      push_cast at habs ⊢
      linarith [habs.2, hmul2]
    · have e2 : ((round (ρ * (R / 8)) : ℝ)) * 8 + 1
          = 8 * ((round (ρ * (R / 8)) : ℝ) + 1 / 8) := by
        have hc : ((round (ρ * (R / 8)) : ℤ) : ℝ) = (round (ρ * (R / 8)) : ℝ) := rfl
        rw [hc]
        push_cast
        ring
      have hmul2 : (round (ρ * (R / 8)) : ℝ) * 8 = ρ * R - 8 * (ρ * (R / 8) - (round (ρ * (R / 8)) : ℝ)) := by
        have : ρ * R = 8 * (ρ * (R / 8)) := hmul
        linarith
      push_cast at habs ⊢
      linarith [habs.1, hmul2]
  · rintro ⟨j, h1, h2⟩
    have e1 : ((8 * j - 1 : ℤ) : ℝ) = (j : ℝ) * 8 - 1 := by push_cast; ring
    have e2 : ((8 * j + 1 : ℤ) : ℝ) = (j : ℝ) * 8 + 1 := by push_cast; ring
    refine Fresh.Certs.inWay_of_zone (ρ := ρ) (R := R) (j := j) ?_ ?_
    · rw [e1]; exact h1
    · rw [e2]; exact h2

#print axioms inWay_zone_iff

/-- `NoCarve` in the witness form the reduction consumes: no carve of `[1,7]` iff there is a
lonely instant of the readings in `t ∈ [1/8, 7/8]` (the `R`-coordinate witness in `[1,7]`).
Forward: the carve-form's negation is `Fresh.FrontierFamilyCap.lonely_witness_of_not_carved`'s
input via `inWay_zone_iff`; backward: the witness contradicts the carve at the witness point. -/
theorem notCarve_witness (g : Fin 7 → ℝ) :
    Fresh.Certs.NoCarve g ↔
      ∃ t, 1 / 8 ≤ t ∧ t ≤ 7 / 8 ∧
        Fresh.Cascade.LonelyAt (Finset.image g Finset.univ) t := by
  constructor
  · intro h
    refine lonely_witness_of_not_carved ?_
    intro hcarve
    refine h (fun R hR1 hR2 => ?_)
    obtain ⟨ρ, hρmem, hway⟩ := hcarve (R / 8) (by linarith) (by linarith)
    rw [inWay_zone_iff] at hway
    obtain ⟨j, h1, h2⟩ := hway
    exact ⟨ρ, hρmem, j, h1, h2⟩
  · intro hww hcarve
    obtain ⟨t, ht1, ht2, hclear⟩ := hww
    obtain ⟨ρ, hρmem, j, h1, h2⟩ := hcarve (8 * t) (by linarith) (by linarith)
    have he1 : ((8 * j - 1 : ℤ) : ℝ) = (j : ℝ) * 8 - 1 := by push_cast; ring
    have he2 : ((8 * j + 1 : ℤ) : ℝ) = (j : ℝ) * 8 + 1 := by push_cast; ring
    have hway' : Fresh.InWay ρ ((8 * t) / 8) :=
      Fresh.Certs.inWay_of_zone (ρ := ρ) (R := 8 * t) (j := j)
        (by rw [he1]; exact h1) (by rw [he2]; exact h2)
    have he8 : (8 * t) / 8 = t := by field_simp
    rw [he8] at hway'
    have hclearρ : (1 / 8 : ℝ) ≤ distInt (ρ * t) := hclear ρ hρmem
    have hway'' : distInt (ρ * t) < 1 / 8 := hway'
    linarith

#print axioms notCarve_witness

/-! ## The integer avoidance certificate (the shared decidable shape) -/

/-- The per-coordinate raw-box face's lower end: `max(2n-1, 2)/2` — the nearest-integer box
`ρ ∈ [n - 1/2, n + 1/2]` cut at `1` (readings are at least the least reading `1`). -/
-- STANDING: DEFINITION
noncomputable def FaceLo (n : Fin 7 → ℤ) (i : Fin 7) : ℝ := ((max (2 * n i - 1) 2 : ℤ) : ℝ) / 2

/-- The per-coordinate raw-box face's upper end: `(2n+1)/2`. -/
-- STANDING: DEFINITION
noncomputable def FaceHi (n : Fin 7 → ℤ) (i : Fin 7) : ℝ := ((2 * n i + 1 : ℤ) : ℝ) / 2

/-- The zone-avoidance certificate for the tuple `n` at the rational clear point `r/base` in
window `w` (`w = 0`: `W₀ = [1,7]`; `w = 1`: `W₁ = [9,15]`).  All fields are integer
inequalities over the finite zone range `j ∈ [0,33]` (out-of-range `j` is automatic given
`n ≤ 17` and the window range: `r·(2n+1) ≤ 15·base·35 < 2·(8·34-1)·base`), so the check is a
decidable integer check — the Lean form of the M1/M4 interval certificates.  This is the
exact integer form of `j2_admit_mech_v1.py` mechanism (b): for every coordinate and every
zone, `r/base · (2n+1)/2 ≤ 8j-1` or `8j+1 ≤ r/base · max(2n-1,2)/2`, i.e. the face interval
does not meet the way-zone. -/
-- STANDING: DEFINITION
structure ZoneClearCert (n : Fin 7 → ℤ) (w : ℕ) where
  r : ℤ
  base : ℤ
  hbase : 0 < base
  hlo : (8 * w + 1) * base ≤ r
  hhi : r ≤ (8 * w + 7) * base
  hn17 : ∀ i, n i ≤ 17
  havoid : ∀ (i : Fin 7) (j : Fin 34),
    r * (2 * n i + 1) ≤ 2 * (8 * ((j : ℕ) : ℤ) - 1) * base ∨
      2 * (8 * ((j : ℕ) : ℤ) + 1) * base ≤ r * max (2 * n i - 1) 2

/-- The certificate's condition, as a PROP with the data supplied (`r`, `base`): the same
content as the `ZoneClearCert` structure, in decidable form — the per-instance integer check
of the mission's "decidable predicates" (the existential over `r`, `base` lives in
`CoverData`). -/
-- STANDING: DEFINITION
def ZoneClearCond (n : Fin 7 → ℤ) (r base : ℤ) (w : ℕ) : Prop :=
  0 < base ∧ (8 * w + 1) * base ≤ r ∧ r ≤ (8 * w + 7) * base ∧ (∀ i, n i ≤ 17) ∧
    ∀ (i : Fin 7) (j : Fin 34),
      r * (2 * n i + 1) ≤ 2 * (8 * ((j : ℕ) : ℤ) - 1) * base ∨
        2 * (8 * ((j : ℕ) : ℤ) + 1) * base ≤ r * max (2 * n i - 1) 2

instance (n : Fin 7 → ℤ) (r base : ℤ) (w : ℕ) : Decidable (ZoneClearCond n r base w) := by
  unfold ZoneClearCond
  infer_instance

/-- The data carrier and the decidable condition carry the same content. -/
theorem ZoneClearCond_of_cert {n : Fin 7 → ℤ} {w : ℕ} (c : ZoneClearCert n w) :
    ZoneClearCond n c.r c.base w :=
  ⟨c.hbase, c.hlo, c.hhi, c.hn17, c.havoid⟩

#print axioms ZoneClearCond_of_cert

/-- The condition builds the data carrier. -/
noncomputable def certOfCond (n : Fin 7 → ℤ) (r base : ℤ) (w : ℕ) (hc : ZoneClearCond n r base w) :
    ZoneClearCert n w :=
  ⟨r, base, hc.1, hc.2.1, hc.2.2.1, hc.2.2.2.1, hc.2.2.2.2⟩

/-! ### The per-certificate soundness machinery (added 2026-11-08) -/

/-- Every face's lower end is at least `1` (the raw box cut at the least reading `1`). -/
theorem faceLo_ge_one (n : Fin 7 → ℤ) (i : Fin 7) : (1 : ℝ) ≤ FaceLo n i := by
  unfold FaceLo
  have h3 : (2 : ℝ) ≤ ((max (2 * n i - 1) 2 : ℤ) : ℝ) := by
    exact_mod_cast (le_max_right (2 * n i - 1) 2)
  calc (1 : ℝ) = 2 / 2 := by norm_num
    _ ≤ ((max (2 * n i - 1) 2 : ℤ) : ℝ) / 2 :=
        (div_le_div_iff₀ (by norm_num : (0 : ℝ) < 2) (by norm_num : (0 : ℝ) < 2)).mpr
          (mul_le_mul_of_nonneg_right h3 (by norm_num : (0 : ℝ) ≤ 2))

#print axioms faceLo_ge_one

/-- The certificate's clear point `r/base` lies in the scaled window `[8w+1, 8w+7]`. -/
theorem certPoint_bounds (n : Fin 7 → ℤ) (w : ℕ) (c : ZoneClearCert n w) :
    (8 * w + 1 : ℝ) ≤ (c.r : ℝ) / c.base ∧ (c.r : ℝ) / c.base ≤ (8 * w + 7 : ℝ) := by
  have hb : (0 : ℝ) < c.base := by exact_mod_cast c.hbase
  constructor
  · exact (le_div_iff₀ hb).mpr (by exact_mod_cast c.hlo)
  · exact (div_le_iff₀ hb).mpr (by exact_mod_cast c.hhi)

#print axioms certPoint_bounds

/-- Division reassociation: `r / (b * 8) = r / b / 8`. -/
theorem div_mul_eight {r b : ℝ} (hb : b ≠ 0) : r / (b * 8) = r / b / 8 := by
  field_simp

#print axioms div_mul_eight

/-- Product-of-quotients reassociation: `r / b * (x / 2) = r * x / (2 * b)`. -/
theorem mul_div_div {r b x : ℝ} (hb : b ≠ 0) : r / b * (x / 2) = r * x / (2 * b) := by
  field_simp

#print axioms mul_div_div

/-- The integer avoidance of a `ZoneClearCert` in real form: for every in-range zone `j < 34`
the scaled face interval misses the open zone `(8j-1, 8j+1)` — its top is at most the zone's
lower edge, or the zone's upper edge is at most its bottom. -/
theorem zoneAvoid_real {n : Fin 7 → ℤ} {w : ℕ} (c : ZoneClearCert n w) (i : Fin 7) (j : ℕ)
    (hj : j < 34) :
    (c.r : ℝ) / c.base * FaceHi n i ≤ 8 * (((j : ℕ) : ℤ) : ℝ) - 1 ∨
      8 * (((j : ℕ) : ℤ) : ℝ) + 1 ≤ (c.r : ℝ) / c.base * FaceLo n i := by
  have hb : (0 : ℝ) < c.base := by exact_mod_cast c.hbase
  have hbne : (c.base : ℝ) ≠ 0 := hb.ne'
  have h2b : (0 : ℝ) < 2 * c.base := by positivity
  have hne : ((2 : ℝ) * c.base) ≠ 0 := ne_of_gt h2b
  have hval : ((⟨j, hj⟩ : Fin 34) : ℕ) = j := rfl
  rcases c.havoid i ⟨j, hj⟩ with h | h
  · rw [hval] at h
    refine Or.inl ?_
    have h1 : (c.r : ℝ) * ((2 * n i + 1 : ℤ) : ℝ)
        ≤ 2 * (8 * (((j : ℕ) : ℤ) : ℝ) - 1) * (c.base : ℝ) := by exact_mod_cast h
    have e : (c.r : ℝ) / (c.base : ℝ) * FaceHi n i
        = (c.r : ℝ) * ((2 * n i + 1 : ℤ) : ℝ) / ((2 : ℝ) * (c.base : ℝ)) := by
      simp only [FaceHi]
      exact mul_div_div hbne
    rw [e]
    calc (c.r : ℝ) * ((2 * n i + 1 : ℤ) : ℝ) / ((2 : ℝ) * (c.base : ℝ))
        ≤ (2 * (8 * (((j : ℕ) : ℤ) : ℝ) - 1) * (c.base : ℝ)) / ((2 : ℝ) * (c.base : ℝ)) :=
          (div_le_div_iff₀ h2b h2b).mpr (mul_le_mul_of_nonneg_right h1 h2b.le)
      _ = 8 * (((j : ℕ) : ℤ) : ℝ) - 1 := by field_simp
  · rw [hval] at h
    refine Or.inr ?_
    have h1 : 2 * (8 * (((j : ℕ) : ℤ) : ℝ) + 1) * (c.base : ℝ)
        ≤ (c.r : ℝ) * ((max (2 * n i - 1) 2 : ℤ) : ℝ) := by exact_mod_cast h
    have e : (c.r : ℝ) / (c.base : ℝ) * FaceLo n i
        = (c.r : ℝ) * ((max (2 * n i - 1) 2 : ℤ) : ℝ) / ((2 : ℝ) * (c.base : ℝ)) := by
      simp only [FaceLo]
      exact mul_div_div hbne
    rw [e]
    have e2 : 8 * (((j : ℕ) : ℤ) : ℝ) + 1
        = (2 * (8 * (((j : ℕ) : ℤ) : ℝ) + 1) * (c.base : ℝ)) / ((2 : ℝ) * (c.base : ℝ)) := by
      field_simp
    rw [e2]
    exact (div_le_div_iff₀ h2b h2b).mpr (mul_le_mul_of_nonneg_right h1 h2b.le)

#print axioms zoneAvoid_real

/-- **The gap selection** (PROVED below as `existsGapJ`): the face interval
`[FaceLo i, FaceHi i]` scaled by `r/base` lies in ONE closed window `[8J+1, 8J+7]` with
`0 ≤ J ≤ 32` (so `J` and `J+1` are inside the certificate's zone range).  This is the
per-reading form of the artifact's exact sweep (`j2_admit_mech_v1.py` `gaps_b`) and the
per-reading `hgap` of a `Fresh.Certs.FixedClearCert`. -/
-- STANDING: DEFINITION
def ExistsGapJ : Prop :=
  ∀ (n : Fin 7 → ℤ) (w : ℕ) (c : ZoneClearCert n w) (i : Fin 7), w ≤ 1 →
    ∃ J : ℤ, 0 ≤ J ∧ J ≤ 32 ∧
      8 * (J : ℝ) + 1 ≤ (c.r : ℝ) / c.base * FaceLo n i ∧
      (c.r : ℝ) / c.base * FaceHi n i ≤ 8 * (J : ℝ) + 7

/-- **The gap selection, PROVED** (2026-11-08): the selection is `J = ⌊(s·FaceLo i − 1)/8⌋`
with `s = r/base`.  The floor gives `8J+1 ≤ s·FaceLo < 8J+9`; `J ≥ 0` since `s·FaceLo ≥ 1`;
`J ≤ 32` since `s·FaceLo < 265` (`s ≤ 15` from `w ≤ 1`, `FaceLo ≤ 35/2` from `n i ≤ 17`); and
if the scaled face top passed `8J+7`, the avoidance at zone `J+1` (in range since `J ≤ 32`)
would be violated on both sides. -/
theorem existsGapJ : ExistsGapJ := by
  intro n w c i hw
  have hb : (0 : ℝ) < c.base := by exact_mod_cast c.hbase
  have hs1 : (1 : ℝ) ≤ (c.r : ℝ) / c.base := by
    obtain ⟨hslo, -⟩ := certPoint_bounds n w c
    have hw0 : (0 : ℝ) ≤ ((w : ℕ) : ℝ) := by exact_mod_cast (Nat.zero_le w)
    linarith
  have hs15 : (c.r : ℝ) / c.base ≤ 15 := by
    obtain ⟨-, hshi⟩ := certPoint_bounds n w c
    have hw1 : ((w : ℕ) : ℝ) ≤ 1 := by exact_mod_cast hw
    linarith
  have hLlo : (1 : ℝ) ≤ FaceLo n i := faceLo_ge_one n i
  have hLpos : (0 : ℝ) ≤ FaceLo n i := le_trans (by norm_num : (0 : ℝ) ≤ 1) hLlo
  have hLub : FaceLo n i ≤ 35 / 2 := by
    have hni := c.hn17 i
    unfold FaceLo
    have hmax : max (2 * n i - 1) 2 ≤ 35 := max_le (by omega) (by omega)
    calc ((max (2 * n i - 1) 2 : ℤ) : ℝ) / 2 ≤ ((35 : ℤ) : ℝ) / 2 :=
        (div_le_div_iff₀ (by norm_num : (0 : ℝ) < 2) (by norm_num : (0 : ℝ) < 2)).mpr
          (mul_le_mul_of_nonneg_right (by exact_mod_cast hmax) (by norm_num : (0 : ℝ) ≤ 2))
      _ = 35 / 2 := by norm_num
  have hAnn : (0 : ℝ) ≤ (c.r : ℝ) / c.base * FaceLo n i - 1 := by
    have hstep : (1 : ℝ) * FaceLo n i ≤ (c.r : ℝ) / c.base * FaceLo n i :=
      mul_le_mul_of_nonneg_right hs1 hLpos
    rw [one_mul] at hstep
    linarith
  obtain ⟨J, hJfloor⟩ : ∃ J : ℤ, J = Int.floor (((c.r : ℝ) / c.base * FaceLo n i - 1) / 8) :=
    ⟨_, rfl⟩
  have hJ0 : 0 ≤ J := by
    rw [hJfloor]
    exact Int.floor_nonneg.mpr (div_nonneg hAnn (by norm_num : (0 : ℝ) ≤ 8))
  have hJ1 : ((J : ℝ)) ≤ ((c.r : ℝ) / c.base * FaceLo n i - 1) / 8 := by
    rw [hJfloor]
    exact Int.floor_le _
  have hJ2 : ((c.r : ℝ) / c.base * FaceLo n i - 1) / 8 < ((J : ℝ)) + 1 := by
    rw [hJfloor]
    exact Int.lt_floor_add_one _
  have hJ1m : (J : ℝ) * 8 ≤ (c.r : ℝ) / c.base * FaceLo n i - 1 :=
    (le_div_iff₀ (by norm_num : (0 : ℝ) < 8)).mp hJ1
  have hJ2m : (c.r : ℝ) / c.base * FaceLo n i - 1 < ((J : ℝ) + 1) * 8 :=
    (div_lt_iff₀ (by norm_num : (0 : ℝ) < 8)).mp hJ2
  have hJlo : 8 * (J : ℝ) + 1 ≤ (c.r : ℝ) / c.base * FaceLo n i := by linarith
  have hJalt : (c.r : ℝ) / c.base * FaceLo n i < 8 * (J : ℝ) + 9 := by linarith
  have hAub : (c.r : ℝ) / c.base * FaceLo n i < 265 := by
    have hstep : (c.r : ℝ) / c.base * FaceLo n i ≤ 15 * FaceLo n i :=
      mul_le_mul_of_nonneg_right hs15 hLpos
    have h3 : (15 : ℝ) * FaceLo n i ≤ (15 : ℝ) * (35 / 2 : ℝ) :=
      mul_le_mul_of_nonneg_left hLub (by norm_num : (0 : ℝ) ≤ 15)
    have h4 : (15 : ℝ) * (35 / 2 : ℝ) = 262.5 := by norm_num
    linarith
  have hJ32 : J ≤ 32 := by
    have h8 : (8 : ℝ) * (J : ℝ) < 264 := by linarith
    have h9 : ((8 * J : ℤ) : ℝ) < ((264 : ℤ) : ℝ) := by
      calc ((8 * J : ℤ) : ℝ) = 8 * (J : ℝ) := by push_cast; rfl
        _ < 264 := h8
        _ = ((264 : ℤ) : ℝ) := by norm_num
    have h10 : (8 * J : ℤ) < 264 := Int.cast_lt.mp h9
    omega
  refine ⟨J, hJ0, hJ32, hJlo, ?_⟩
  by_contra hcon
  push_neg at hcon
  have hJ1nn : (0 : ℤ) ≤ J + 1 := by omega
  have hJ1val : (((J + 1).toNat : ℕ) : ℤ) = J + 1 := Int.toNat_of_nonneg hJ1nn
  have hJ1lt : (J + 1).toNat < 34 := by
    have h2 : (((J + 1).toNat : ℕ) : ℤ) < ((34 : ℕ) : ℤ) := by rw [hJ1val]; omega
    exact_mod_cast h2
  obtain hd1 | hd2 := zoneAvoid_real c i (J + 1).toNat hJ1lt
  · rw [hJ1val] at hd1
    push_cast at hd1
    linarith
  · rw [hJ1val] at hd2
    push_cast at hd2
    linarith

#print axioms existsGapJ

/-- **The per-reading soundness of the avoidance certificate** (PROVED below as `faceClear`):
every real reading `y` in the coordinate's face is clear at the instant `R/8`, `R = r/base`.
(Via the gap selection: the phase `y·R` lies in the selected closed window, so
`distInt ≥ 1/8`.) -/
-- STANDING: DEFINITION
def FaceClear : Prop :=
  ∀ (n : Fin 7 → ℤ) (w : ℕ) (c : ZoneClearCert n w) (i : Fin 7) (y : ℝ), w ≤ 1 →
    FaceLo n i ≤ y → y ≤ FaceHi n i →
      (1 / 8 : ℝ) ≤ distInt (y * ((c.r : ℝ) / (c.base * 8)))

/-- **The per-reading soundness, PROVED** (2026-11-08): by `existsGapJ` the scaled face lies in
`[8J+1, 8J+7]`, so the phase `y·R/8 = y·s/8` lies in `[J+1/8, J+7/8]` and
`distInt ≥ 1/8` (`distInt_ge_eighth_iff`). -/
theorem faceClear : FaceClear := by
  intro n w c i y hw hlo hhi
  obtain ⟨J, hJ0, hJ32, hJlo, hJhi⟩ := existsGapJ n w c i hw
  have hb : (0 : ℝ) < c.base := by exact_mod_cast c.hbase
  have hs0 : (0 : ℝ) ≤ (c.r : ℝ) / c.base := by
    obtain ⟨hslo, -⟩ := certPoint_bounds n w c
    have hw0 : (0 : ℝ) ≤ ((w : ℕ) : ℝ) := by exact_mod_cast (Nat.zero_le w)
    linarith
  have hsy1 : (c.r : ℝ) / c.base * FaceLo n i ≤ (c.r : ℝ) / c.base * y :=
    mul_le_mul_of_nonneg_left hlo hs0
  have hsy2 : (c.r : ℝ) / c.base * y ≤ (c.r : ℝ) / c.base * FaceHi n i :=
    mul_le_mul_of_nonneg_left hhi hs0
  have hcomm : (c.r : ℝ) / c.base * y = y * ((c.r : ℝ) / c.base) := mul_comm _ _
  have hylow : 8 * (J : ℝ) + 1 ≤ y * ((c.r : ℝ) / c.base) := by linarith [hJlo, hsy1, hcomm]
  have hyhigh : y * ((c.r : ℝ) / c.base) ≤ 8 * (J : ℝ) + 7 := by linarith [hJhi, hsy2, hcomm]
  rw [div_mul_eight hb.ne']
  have e1 : ((J : ℝ)) + 1 / 8 ≤ y * ((c.r : ℝ) / c.base / 8) := by
    have h8 : y * ((c.r : ℝ) / c.base / 8) = (1 / 8 : ℝ) * (y * ((c.r : ℝ) / c.base)) := by ring
    rw [h8]
    linarith
  have e2 : y * ((c.r : ℝ) / c.base / 8) ≤ ((J : ℝ)) + 7 / 8 := by
    have h8 : y * ((c.r : ℝ) / c.base / 8) = (1 / 8 : ℝ) * (y * ((c.r : ℝ) / c.base)) := by ring
    rw [h8]
    linarith
  exact (distInt_ge_eighth_iff (y * ((c.r : ℝ) / c.base / 8))).mpr ⟨J, Set.mem_Icc.mpr ⟨e1, e2⟩⟩

#print axioms faceClear

/-- **The bridge certificate-to-clear-point** (PROVED below as `clearPointOfCert`): a tuple
certificate gives a clear point `s = r/base ∈ [1,15]` with `s ≤ 7` or `9 ≤ s`, clear for every
real reading vector in the tuple's faces. -/
-- STANDING: DEFINITION
def ClearPointOfCert : Prop :=
  ∀ (n : Fin 7 → ℤ) (w : ℕ) (c : ZoneClearCert n w), w ≤ 1 →
    ∀ (g : Fin 7 → ℝ), (∀ i, FaceLo n i ≤ g i ∧ g i ≤ FaceHi n i) →
      ∃ s : ℝ, 1 ≤ s ∧ s ≤ 15 ∧ (s ≤ 7 ∨ 9 ≤ s) ∧
        ∀ i, (1 / 8 : ℝ) ≤ distInt (g i * (s / 8))

/-- **The bridge, PROVED** (2026-11-08): the clear point is `s = r/base`; the bounds
`8w+1 ≤ s ≤ 8w+7` give `1 ≤ s ≤ 15`, the split is `w = 0` (`s ≤ 7`) or `w = 1` (`9 ≤ s`), and
the per-coordinate clearance is `faceClear`. -/
theorem clearPointOfCert : ClearPointOfCert := by
  intro n w c hw g hface
  have hb : (0 : ℝ) < c.base := by exact_mod_cast c.hbase
  refine ⟨(c.r : ℝ) / c.base, ?_, ?_, ?_, ?_⟩
  · obtain ⟨hslo, -⟩ := certPoint_bounds n w c
    have hw0 : (0 : ℝ) ≤ ((w : ℕ) : ℝ) := by exact_mod_cast (Nat.zero_le w)
    linarith
  · obtain ⟨-, hshi⟩ := certPoint_bounds n w c
    have hw1 : ((w : ℕ) : ℝ) ≤ 1 := by exact_mod_cast hw
    linarith
  · rcases Nat.eq_zero_or_pos w with hw0 | hw0
    · subst hw0
      refine Or.inl ?_
      have h := c.hhi
      norm_num at h
      exact (div_le_iff₀ hb).mpr (by exact_mod_cast h)
    · have hw1 : w = 1 := by omega
      subst hw1
      refine Or.inr ?_
      have h := c.hlo
      norm_num at h
      exact (le_div_iff₀ hb).mpr (by exact_mod_cast h)
  · intro i
    rw [← div_mul_eight hb.ne']
    exact faceClear n w c i (g i) hw (hface i).1 (hface i).2

#print axioms clearPointOfCert

/-- **The `W₀` no-carve plug through `Fresh.Certs`** (PROVED below as `noCarveOfM1`): a `W₀`
tuple certificate gives `Fresh.Certs.NoCarve g` — via `fixedClearCert_of_dyadic_int` (the
reading's own cell `min(⌊2·g i⌋, 2·n i)`, which lies in the face) and `fixedClear_noCarve`. -/
-- STANDING: DEFINITION
def NoCarveOfM1 : Prop :=
  ∀ (n : Fin 7 → ℤ) (c : ZoneClearCert n 0) (g : Fin 7 → ℝ),
    (∀ i, FaceLo n i ≤ g i ∧ g i ≤ FaceHi n i) → (∀ i, 1 ≤ n i) →
      Fresh.Certs.NoCarve g

/-- **The `W₀` no-carve plug, PROVED** (2026-11-08): per coordinate, `existsGapJ` selects the
gap index `jf i` with the scaled face in `[8·jf i + 1, 8·jf i + 7]`; the reading's own dyadic
cell `k i = min(⌊2·g i⌋, 2·n i)` satisfies `max(2n−1, 2) ≤ k i` (from `g i ≥ FaceLo i` and
`n i ≥ 1`) and `k i + 1 ≤ 2n + 1`, so the cell lies in the face inside the window — the
`FixedClearIntCond` of `fixedClearCert_of_dyadic_int` at depth `D = 2`; the cell contains
`g i` by the floor bounds, so `fixedClear_noCarve` applies. -/
theorem noCarveOfM1 : NoCarveOfM1 := by
  intro n c g hface hn1
  have hw : (0 : ℕ) ≤ 1 := by omega
  have hgw : ∀ i : Fin 7, ∃ J : ℤ, 0 ≤ J ∧ J ≤ 32 ∧
      8 * (J : ℝ) + 1 ≤ (c.r : ℝ) / c.base * FaceLo n i ∧
      (c.r : ℝ) / c.base * FaceHi n i ≤ 8 * (J : ℝ) + 7 :=
    fun i => existsGapJ n 0 c i hw
  choose jf hjf using hgw
  have hb : (0 : ℝ) < c.base := by exact_mod_cast c.hbase
  have hbne : (c.base : ℝ) ≠ 0 := hb.ne'
  have hs0 : (0 : ℝ) ≤ (c.r : ℝ) / c.base := by
    obtain ⟨hslo, -⟩ := certPoint_bounds n 0 c
    linarith
  have hR1 : (1 : ℤ) * c.base ≤ c.r := by simpa using c.hlo
  have hR7 : c.r ≤ (7 : ℤ) * c.base := by simpa using c.hhi
  have hint : Fresh.Certs.FixedClearIntCond 2 c.base
      (fun i => min (Int.floor (2 * g i)) (2 * n i)) jf c.r := by
    intro i
    obtain ⟨-, -, hJlo, hJhi⟩ := hjf i
    obtain ⟨hflo, hfhi⟩ := hface i
    have hni := hn1 i
    have hF1 : (2 * n i - 1 : ℤ) ≤ Int.floor (2 * g i) := by
      rw [Int.le_floor (a := 2 * g i)]
      have hkey : ((2 * n i - 1 : ℤ) : ℝ) / 2 ≤ g i := by
        calc ((2 * n i - 1 : ℤ) : ℝ) / 2 ≤ ((max (2 * n i - 1) 2 : ℤ) : ℝ) / 2 :=
            (div_le_div_iff₀ (by norm_num : (0 : ℝ) < 2) (by norm_num : (0 : ℝ) < 2)).mpr
              (mul_le_mul_of_nonneg_right (by exact_mod_cast (le_max_left _ _))
                (by norm_num : (0 : ℝ) ≤ 2))
          _ = FaceLo n i := rfl
          _ ≤ g i := hflo
      linarith [(div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mp hkey]
    have hF2 : (2 : ℤ) ≤ Int.floor (2 * g i) := by
      rw [Int.le_floor (a := 2 * g i)]
      have h1 : (1 : ℝ) ≤ g i := le_trans (faceLo_ge_one n i) hflo
      have h2 : (2 : ℝ) ≤ 2 * g i := by linarith
      exact_mod_cast h2
    have hklo : max (2 * n i - 1) 2 ≤ min (Int.floor (2 * g i)) (2 * n i) :=
      max_le (le_min hF1 (by omega)) (le_min hF2 (by omega))
    have hkhi : min (Int.floor (2 * g i)) (2 * n i) + 1 ≤ 2 * n i + 1 := by
      have hminle := min_le_right (Int.floor (2 * g i)) (2 * n i)
      omega
    have h2b : (0 : ℝ) < 2 * c.base := by positivity
    constructor
    · -- (8 * jf i + 1) * c.base * 2 ≤ c.r * k i
      have hFL2 : FaceLo n i ≤ ((min (Int.floor (2 * g i)) (2 * n i) : ℤ) : ℝ) / 2 := by
        calc FaceLo n i = ((max (2 * n i - 1) 2 : ℤ) : ℝ) / 2 := rfl
          _ ≤ ((min (Int.floor (2 * g i)) (2 * n i) : ℤ) : ℝ) / 2 :=
              (div_le_div_iff₀ (by norm_num : (0 : ℝ) < 2) (by norm_num : (0 : ℝ) < 2)).mpr
                (mul_le_mul_of_nonneg_right (by exact_mod_cast hklo)
                  (by norm_num : (0 : ℝ) ≤ 2))
      have hstep : (c.r : ℝ) / c.base * (((min (Int.floor (2 * g i)) (2 * n i) : ℤ) : ℝ) / 2)
          = (c.r : ℝ) * ((min (Int.floor (2 * g i)) (2 * n i) : ℤ) : ℝ) / (2 * c.base) :=
        mul_div_div hbne
      have hchain : 8 * ((jf i : ℝ)) + 1
          ≤ (c.r : ℝ) * ((min (Int.floor (2 * g i)) (2 * n i) : ℤ) : ℝ) / (2 * c.base) := by
        calc 8 * ((jf i : ℝ)) + 1 ≤ (c.r : ℝ) / c.base * FaceLo n i := hJlo
          _ ≤ (c.r : ℝ) / c.base * (((min (Int.floor (2 * g i)) (2 * n i) : ℤ) : ℝ) / 2) :=
              mul_le_mul_of_nonneg_left hFL2 hs0
          _ = (c.r : ℝ) * ((min (Int.floor (2 * g i)) (2 * n i) : ℤ) : ℝ) / (2 * c.base) := hstep
      have hfinal : (((8 * jf i + 1) * c.base * 2 : ℤ) : ℝ)
          ≤ ((c.r * (min (Int.floor (2 * g i)) (2 * n i)) : ℤ) : ℝ) := by
        have eL : (((8 * jf i + 1) * c.base * 2 : ℤ) : ℝ)
            = (8 * ((jf i : ℝ)) + 1) * ((2 : ℝ) * (c.base : ℝ)) := by
          push_cast; ring
        have eR : ((c.r * (min (Int.floor (2 * g i)) (2 * n i)) : ℤ) : ℝ)
            = (c.r : ℝ) * ((min (Int.floor (2 * g i)) (2 * n i) : ℤ) : ℝ) := by
          rw [Int.cast_mul]
        rw [eL, eR]
        exact (le_div_iff₀ h2b).mp hchain
      exact Int.cast_le.mp hfinal
    · -- c.r * (k i + 1) ≤ (8 * jf i + 7) * c.base * 2
      have hFL2' : ((((min (Int.floor (2 * g i)) (2 * n i) : ℤ) + 1 : ℤ) : ℝ)) / 2
          ≤ FaceHi n i := by
        calc (((min (Int.floor (2 * g i)) (2 * n i) : ℤ) + 1 : ℤ) : ℝ) / 2
            ≤ ((2 * n i + 1 : ℤ) : ℝ) / 2 :=
              (div_le_div_iff₀ (by norm_num : (0 : ℝ) < 2) (by norm_num : (0 : ℝ) < 2)).mpr
                (mul_le_mul_of_nonneg_right (by exact_mod_cast hkhi)
                  (by norm_num : (0 : ℝ) ≤ 2))
          _ = FaceHi n i := rfl
      have hstep : (c.r : ℝ) / c.base
              * ((((min (Int.floor (2 * g i)) (2 * n i) : ℤ) + 1 : ℤ) : ℝ) / 2)
          = (c.r : ℝ) * (((min (Int.floor (2 * g i)) (2 * n i) : ℤ) + 1 : ℤ) : ℝ) / (2 * c.base) :=
        mul_div_div hbne
      have hchain : (c.r : ℝ) * (((min (Int.floor (2 * g i)) (2 * n i) : ℤ) + 1 : ℤ) : ℝ)
              / (2 * c.base) ≤ 8 * ((jf i : ℝ)) + 7 := by
        calc (c.r : ℝ) * (((min (Int.floor (2 * g i)) (2 * n i) : ℤ) + 1 : ℤ) : ℝ) / (2 * c.base)
            = (c.r : ℝ) / c.base
                * ((((min (Int.floor (2 * g i)) (2 * n i) : ℤ) + 1 : ℤ) : ℝ) / 2) := hstep.symm
          _ ≤ (c.r : ℝ) / c.base * FaceHi n i := mul_le_mul_of_nonneg_left hFL2' hs0
          _ ≤ 8 * ((jf i : ℝ)) + 7 := hJhi
      have hfinal : ((c.r * (min (Int.floor (2 * g i)) (2 * n i) + 1) : ℤ) : ℝ)
          ≤ (((8 * jf i + 7) * c.base * 2 : ℤ) : ℝ) := by
        have eL : ((c.r * (min (Int.floor (2 * g i)) (2 * n i) + 1) : ℤ) : ℝ)
            = (c.r : ℝ) * (((min (Int.floor (2 * g i)) (2 * n i) : ℤ) + 1 : ℤ) : ℝ) := by
          rw [Int.cast_mul]
        have eR : (((8 * jf i + 7) * c.base * 2 : ℤ) : ℝ)
            = (8 * ((jf i : ℝ)) + 7) * ((2 : ℝ) * (c.base : ℝ)) := by
          push_cast; ring
        rw [eL, eR]
        exact (div_le_iff₀ h2b).mp hchain
      exact Int.cast_le.mp hfinal
  have hbox : ∀ i, ((min (Int.floor (2 * g i)) (2 * n i) : ℤ) : ℝ) / 2 ≤ g i
      ∧ g i ≤ (((min (Int.floor (2 * g i)) (2 * n i) : ℤ) + 1 : ℤ) : ℝ) / 2 := by
    intro i
    obtain ⟨hflo, hfhi⟩ := hface i
    rcases le_total (Int.floor (2 * g i)) (2 * n i) with hle | hle
    · have hmin : min (Int.floor (2 * g i)) (2 * n i) = Int.floor (2 * g i) :=
        min_eq_left hle
      rw [hmin]
      refine ⟨?_, ?_⟩
      · refine (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr ?_
        have h1 : ((Int.floor (2 * g i) : ℤ) : ℝ) ≤ 2 * g i := Int.floor_le _
        linarith
      · refine (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr ?_
        have h1 : (2 : ℝ) * g i < ((Int.floor (2 * g i) : ℤ) : ℝ) + 1 := Int.lt_floor_add_one _
        have h3 : (((Int.floor (2 * g i) : ℤ) + 1 : ℤ) : ℝ)
            = ((Int.floor (2 * g i) : ℤ) : ℝ) + 1 := by
          rw [Int.cast_add, Int.cast_one]
        rw [h3]
        linarith
    · have hmin : min (Int.floor (2 * g i)) (2 * n i) = 2 * n i := min_eq_right hle
      rw [hmin]
      refine ⟨?_, ?_⟩
      · refine (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr ?_
        have h1 : ((2 * n i : ℤ) : ℝ) ≤ ((Int.floor (2 * g i) : ℤ) : ℝ) := by
          exact_mod_cast hle
        have h2 : ((Int.floor (2 * g i) : ℤ) : ℝ) ≤ 2 * g i := Int.floor_le _
        linarith
      · exact hfhi
  exact fixedClear_noCarve
    (fixedClearCert_of_dyadic_int (by norm_num : (0 : ℤ) < 2) c.hbase
      (fun i => min (Int.floor (2 * g i)) (2 * n i)) jf hR1 hR7 hint) g hbox

#print axioms noCarveOfM1

/-! ## The cascade scaling (readings scaled by c, times scaled by c) -/

/-- The next-opening scales: a reading `d/c` at time `c·t` opens where `d` at `t` does,
times `c`. -/
theorem nextOpening_scale (c : ℝ) {d t : ℝ} :
    Fresh.nextOpening (d / c) (c * t) = c * Fresh.nextOpening d t := by
  by_cases h0 : d = 0
  · subst h0
    unfold Fresh.nextOpening
    norm_num
  · by_cases hc0 : c = 0
    · subst hc0
      unfold Fresh.nextOpening
      norm_num
    · unfold Fresh.nextOpening
      have he : (d / c) * (c * t) = d * t := by field_simp
      rw [he]
      field_simp

#print axioms nextOpening_scale

/-- A cascade move transports under scaling readings by `c` and times by `c`. -/
theorem isMove_scale {dsv dsn : Finset ℝ} {c : ℝ} (hc : 0 < c)
    (himg : dsn = Finset.image (fun d => d / c) dsv) :
    ∀ t t', Fresh.IsMove dsv t t' → Fresh.IsMove dsn (c * t) (c * t') := by
  intro t t' hmv
  unfold Fresh.IsMove at hmv ⊢
  rcases hmv with ⟨hw, rfl⟩ | ⟨d, hd, hway, ht', hmax⟩
  · refine Or.inl ⟨?_, rfl⟩
    intro d' hd' hway'
    rw [himg, Finset.mem_image] at hd'
    obtain ⟨d2, hd2, rfl⟩ := hd'
    unfold Fresh.InWay at hway'
    have he : (d2 / c) * (c * t') = d2 * t' := by field_simp
    rw [he] at hway'
    exact hw d2 hd2 hway'
  · refine Or.inr ⟨d / c, ?_, ?_, ?_, ?_⟩
    · rw [himg]
      exact Finset.mem_image.mpr ⟨d, hd, rfl⟩
    · unfold Fresh.InWay at hway ⊢
      have he : (d / c) * (c * t) = d * t := by field_simp
      rw [he]
      exact hway
    · rw [nextOpening_scale c, ht']
    · intro d2 hd2 hway2
      rw [himg, Finset.mem_image] at hd2
      obtain ⟨d3, hd3, rfl⟩ := hd2
      have hway3 : Fresh.InWay d3 t := by
        unfold Fresh.InWay at hway2
        have he : (d3 / c) * (c * t) = d3 * t := by field_simp
        rwa [he] at hway2
      have h := hmax d3 hd3 hway3
      rw [nextOpening_scale c, mul_comm c (nextOpening d3 t), mul_comm c t']
      exact mul_le_mul_of_nonneg_right h hc.le

#print axioms isMove_scale

/-- The cascade scales: the cascade of the scaled readings from the scaled start is the
scaled cascade.  (For the reduction: the cascade of the normalised readings from `1/8` is
`m` times the cascade of the arrangement's disparities from `1/(8·m)`.) -/
theorem cascadeSeq_norm {dsv dsn : Finset ℝ} {c : ℝ} (hc : 0 < c)
    (himg : dsn = Finset.image (fun d => d / c) dsv) (t₀ : ℝ) (n : ℕ) :
    cascadeSeq dsn (c * t₀) n = c * cascadeSeq dsv t₀ n := by
  have hmv : ∀ m : ℕ, Fresh.IsMove dsn (c * cascadeSeq dsv t₀ m)
      (c * cascadeSeq dsv t₀ (m + 1)) := fun m =>
    isMove_scale hc himg _ _ (cascadeSeq_isMove dsv t₀ m)
  have hseq := seq_eq_cascadeSeq (ds := dsn)
    (seq := fun m => c * cascadeSeq dsv t₀ m) hmv n
  rw [hseq, cascadeSeq_zero dsv t₀]

#print axioms cascadeSeq_norm

/-- Stabilization transports along the scaling. -/
theorem stabilizes_norm {dsv dsn : Finset ℝ} {c : ℝ} (hc : 0 < c)
    (himg : dsn = Finset.image (fun d => d / c) dsv) {t₀ : ℝ} {N : ℕ}
    (hS : Fresh.KTaxonomy.StabilizesAtMin dsv t₀ N) :
    Fresh.KTaxonomy.StabilizesAtMin dsn (c * t₀) N := by
  unfold Fresh.KTaxonomy.StabilizesAtMin at hS ⊢
  refine ⟨?_, ?_⟩
  · rw [cascadeSeq_norm hc himg t₀ (N + 1), hS.1, cascadeSeq_norm hc himg t₀ N]
  · intro n hn
    rw [cascadeSeq_norm hc himg t₀ n, cascadeSeq_norm hc himg t₀ (n + 1)]
    exact mul_lt_mul_of_pos_left (hS.2 n hn) hc

#print axioms stabilizes_norm

/-! ## The core bridge: a clear point caps the landing below 17 -/

/-- **The core bridge**: if the normalised readings of the arrangement are all clear at the
`R`-coordinate `s ∈ [1,15]` with `s ≤ 7` or `9 ≤ s`, then the cascade from the bound lands in
`W₀ ∪ W₁` (below 17).  Chain: the clear point is a lonely instant of the normalised set; the
first landing is at or before every lonely instant (`first_landing_le_lonely`); the landing
lies in a window (`landing_window`) and is capped by `s ≤ 15`, so the window is `W₀` or `W₁`. -/
theorem cascadeLandsBelow17_of_clearPoint {v : Fin 8 → ℝ} {k : Fin 8} {m : ℝ}
    (hv : Fresh.IsArrangement v) (hm : Fresh.IsDmin v k m)
    (s : ℝ) (hs₁ : 1 ≤ s) (hs₂ : s ≤ 15) (hsw : s ≤ 7 ∨ 9 ≤ s)
    (hclear : ∀ d ∈ disparitySet v k, (1 / 8 : ℝ) ≤ distInt ((d / m) * (s / 8))) :
    Fresh.FilterSkeleton.CascadeLandsBelow17 (disparitySet v k) m := by
  have hpos : ∀ d ∈ disparitySet v k, 0 < d := disparitySet_pos hv k
  have hm0 : 0 < m := hpos m hm.1
  have hs0 : (0 : ℝ) < s := lt_of_lt_of_le zero_lt_one hs₁
  set dsn : Finset ℝ := Finset.image (fun d => d / m) (disparitySet v k) with hdsn
  have hmdsn : (1 : ℝ) ∈ dsn := by
    rw [hdsn]
    exact Finset.mem_image.mpr ⟨m, hm.1, div_self (ne_of_gt hm0)⟩
  have hposn : ∀ d ∈ dsn, 0 < d := by
    intro d hd
    rw [hdsn, Finset.mem_image] at hd
    obtain ⟨d2, hd2, rfl⟩ := hd
    exact div_pos (hpos d2 hd2) hm0
  -- the clear point is lonely for the normalised set
  have hlonely : Fresh.Cascade.LonelyAt dsn (s / 8) := by
    intro d hd
    rw [hdsn, Finset.mem_image] at hd
    obtain ⟨d2, hd2, rfl⟩ := hd
    exact hclear d2 hd2
  -- the arrangement is isolated at t* = s/(8m)
  have hist : Fresh.Isolation v k := by
    refine ⟨s / (8 * m), div_pos hs0 (mul_pos (by norm_num) hm0), ?_⟩
    intro i hi
    have hread : |v i - v k| ∈ disparitySet v k := by
      refine Finset.mem_image.mpr ⟨i, ?_, rfl⟩
      exact Finset.mem_erase.mpr ⟨hi, Finset.mem_univ i⟩
    have hge := hclear _ hread
    have hmne : (8 : ℝ) * m ≠ 0 := mul_ne_zero (by norm_num) (ne_of_gt hm0)
    rcases abs_cases (v i - v k) with he | he
    · have hneg : (v i - v k) = |v i - v k| := he.1.symm
      have he2 : (v i - v k) * (s / (8 * m)) = (|v i - v k| / m) * (s / 8) := by
        rw [hneg]
        field_simp
        rw [abs_abs]
      rw [he2]
      exact hge
    · have hneg : (v i - v k) = -|v i - v k| := by
        rw [he.1, neg_neg]
      have he2 : (v i - v k) * (s / (8 * m)) = (-(|v i - v k| / m)) * (s / 8) := by
        rw [hneg]
        field_simp
        rw [abs_neg, abs_abs]
      rw [he2, neg_mul, distInt_neg]
      exact hge
  -- cascade fixes, stabilizes; scale to the normalised set
  have hfix : Fresh.CascadeFixes (disparitySet v k) (1 / (8 * m)) :=
    (Fresh.Cascade.cascadeFixes_iff_isolation hv hm).mp hist
  obtain ⟨N, hS⟩ := Fresh.KTaxonomy.exists_stabilizesAtMin_of_cascadeFixes hpos hfix
  have hSn : Fresh.KTaxonomy.StabilizesAtMin dsn (1 / 8) N := by
    have hst := stabilizes_norm (c := m) hm0 hdsn hS
    rwa [show m * (1 / (8 * m)) = 1 / 8 from by field_simp] at hst
  -- landing ≤ s/8, ≥ 1/8, in a window
  have hfirst : cascadeSeq dsn (1 / 8) N ≤ s / 8 :=
    first_landing_le_lonely hposn hmdsn hSn (div_pos hs0 (by norm_num)) hlonely
  have hmono : cascadeSeq dsn (1 / 8) 0 ≤ cascadeSeq dsn (1 / 8) N :=
    cascadeSeq_mono hposn 0 N (Nat.zero_le N)
  have h0eq : cascadeSeq dsn (1 / 8) 0 = 1 / 8 := cascadeSeq_zero dsn (1 / 8)
  obtain ⟨j, hj⟩ := Fresh.FilterSkeleton.landing_window hposn hmdsn hSn
  rw [Set.mem_Icc] at hj
  obtain ⟨hw1, hw2⟩ := hj
  have hw1' : ((8 * j + 1 : ℤ) : ℝ) ≤ 8 * cascadeSeq dsn (1 / 8) N := by
    simpa using hw1
  have hw2' : 8 * cascadeSeq dsn (1 / 8) N ≤ ((8 * j + 7 : ℤ) : ℝ) := by
    simpa using hw2
  push_cast at hw1' hw2'
  have hLge : (1 : ℝ) ≤ 8 * cascadeSeq dsn (1 / 8) N := by linarith [h0eq, hmono]
  have hLle : 8 * cascadeSeq dsn (1 / 8) N ≤ s := by linarith [hfirst]
  have hj1 : (0 : ℤ) ≤ j := by
    by_contra hc
    push_neg at hc
    have hz : (8 * j + 7 : ℤ) ≤ -1 := by omega
    have hzr : ((8 * j + 7 : ℤ) : ℝ) ≤ (((-1 : ℤ)) : ℝ) := Int.cast_le.mpr hz
    push_cast at hzr
    linarith [hw2', hzr, hLge]
  have hj2 : j ≤ 1 := by
    by_contra hc
    have hc2 : (2 : ℤ) ≤ j := by omega
    have hc3 : (2 : ℝ) ≤ (j : ℝ) := Int.cast_le.mpr hc2
    have h1 : ((8 * j + 1 : ℤ) : ℝ) = 8 * (j : ℝ) + 1 := by push_cast; ring
    have h2 : 17 ≤ ((8 * j + 1 : ℤ) : ℝ) := by
      have h3 : (17 : ℝ) = 8 * 2 + 1 := by norm_num
      linarith
    linarith [hw1', h2, hLle, hs₂]
  refine ⟨N, hS, j, hj1, hj2, ?_⟩
  have hnorm : cascadeSeq dsn (1 / 8) N
      = m * cascadeSeq (disparitySet v k) (1 / (8 * m)) N := by
    have hst := cascadeSeq_norm (c := m) hm0 hdsn (1 / (8 * m)) N
    rwa [show m * (1 / (8 * m)) = 1 / 8 from by field_simp] at hst
  rw [Set.mem_Icc, mul_assoc, ← hnorm]
  push_cast
  exact ⟨hw1', hw2'⟩

#print axioms cascadeLandsBelow17_of_clearPoint

/-! ## The arrangement-to-tuple construction -/

/-- The tuple range of the J2 enumeration: every coordinate in `[1,17]`. -/
-- STANDING: DEFINITION
def InRange17 (n : Fin 7 → ℤ) : Prop := ∀ i, 1 ≤ n i ∧ n i ≤ 17

instance (n : Fin 7 → ℤ) : Decidable (InRange17 n) := Fintype.decidableForallFintype

/-- The arrangement-to-tuple construction: the sorted normalised readings, the nearest-
integer tuple, the faces, and the identification `image g = dsn` that transports loneliness.
(The sorted list needs no order property here, only its length `= card dsn ≤ 7` and its
membership `↔ dsn`.) -/
theorem coverTuple {v : Fin 8 → ℝ} {k : Fin 8} {m : ℝ} (hv : Fresh.IsArrangement v)
    (hm : Fresh.IsDmin v k m) (hmax : ∀ d ∈ disparitySet v k, d ≤ 17 * m) :
    ∃ g : Fin 7 → ℝ, ∃ n : Fin 7 → ℤ,
      InRange17 n ∧
      (∀ i, FaceLo n i ≤ g i ∧ g i ≤ FaceHi n i) ∧
      (Finset.image g Finset.univ = Finset.image (fun d => d / m) (disparitySet v k)) := by
  have hpos : ∀ d ∈ disparitySet v k, 0 < d := disparitySet_pos hv k
  have hm0 : 0 < m := hpos m hm.1
  have hge : ∀ d ∈ disparitySet v k, m ≤ d := fun d hd => hm.2 hd
  set dsn : Finset ℝ := Finset.image (fun d => d / m) (disparitySet v k) with hdsneq
  have h1in : (1 : ℝ) ∈ dsn := by
    rw [hdsneq]
    exact Finset.mem_image.mpr ⟨m, hm.1, div_self (ne_of_gt hm0)⟩
  have hge1 : ∀ d ∈ dsn, 1 ≤ d := by
    intro d hd
    rw [hdsneq, Finset.mem_image] at hd
    obtain ⟨d2, hd2, rfl⟩ := hd
    have h1 : (m : ℝ) ≤ d2 := by exact_mod_cast (hge d2 hd2)
    have h3 : (1 : ℝ) = m / m := by rw [div_self (ne_of_gt hm0)]
    calc (1 : ℝ) = m / m := h3
      _ ≤ d2 / m := by
          rw [← h3, le_div_iff₀ hm0]
          linarith
  have hle17 : ∀ d ∈ dsn, d ≤ 17 := by
    intro d hd
    rw [hdsneq, Finset.mem_image] at hd
    obtain ⟨d2, hd2, rfl⟩ := hd
    have h1 : (d2 : ℝ) ≤ 17 * m := by exact_mod_cast (hmax d2 hd2)
    have h2 : d2 / m ≤ 17 := (div_le_iff₀ hm0).mpr h1
    exact h2
  have hcard : dsn.card ≤ 7 := by
    rw [hdsneq]
    have h1 := Finset.card_image_le (f := fun d => d / m) (s := disparitySet v k)
    have h2c : (disparitySet v k).card
        = (Finset.image (fun i => |v i - v k|) (Finset.univ.erase k)).card := rfl
    have h2 := Finset.card_image_le (f := fun i => |v i - v k|) (s := Finset.univ.erase k)
    have h4 : (Finset.univ.erase k).card = 7 := by
      have h3 : (Finset.univ (α := Fin 8)).card = 8 := by simp
      rw [Finset.card_erase_of_mem (Finset.mem_univ k), h3]
    omega
  set L : List ℝ := dsn.sort (· ≤ ·) with hLdef
  have hLlen : L.length = dsn.card := Finset.length_sort (· ≤ ·)
  have hLmem : ∀ x ∈ L, x ∈ dsn := fun x hx => (Finset.mem_sort (· ≤ ·)).mp hx
  set g : Fin 7 → ℝ := fun i => if h : (i : ℕ) < L.length then L[i] else 1 with hgdef
  set n : Fin 7 → ℤ := fun i => Int.floor (g i + 1 / 2) with hndef
  have hgin : ∀ i, g i ∈ dsn := by
    intro i
    simp only [hgdef]
    by_cases h : (i : ℕ) < L.length
    · rw [dif_pos h]
      exact hLmem _ (List.mem_iff_getElem.mpr ⟨i, h, rfl⟩)
    · rw [dif_neg h]
      exact h1in
  refine ⟨g, n, ?_, ?_, ?_⟩
  · intro i
    have hgi1 : (1 : ℝ) ≤ g i := hge1 _ (hgin i)
    have hgi2 : g i ≤ 17 := hle17 _ (hgin i)
    constructor
    · have h1 : (1 : ℝ) ≤ g i + 1 / 2 := by linarith
      have hn : n i = Int.floor (g i + 1 / 2) := by simp only [hndef]
      rw [hn, Int.le_floor (a := g i + 1 / 2), Int.cast_one]
      exact h1
    · have h1 : g i + 1 / 2 < 18 := by linarith
      have h2 : Int.floor (g i + 1 / 2) < 18 := Int.floor_lt.mpr h1
      show Int.floor (g i + 1 / 2) ≤ 17
      omega
  · intro i
    have hf1 : (n i : ℝ) ≤ g i + 1 / 2 := Int.floor_le _
    have hf2 : g i + 1 / 2 < (n i : ℝ) + 1 := Int.lt_floor_add_one _
    have hgi1 : (1 : ℝ) ≤ g i := hge1 _ (hgin i)
    constructor
    · unfold FaceLo
      rcases le_total ((2 * n i - 1 : ℤ) : ℝ) 2 with hc | hc
      · have hz : (2 * n i - 1 : ℤ) ≤ 2 := by exact_mod_cast hc
        have h1 : max (2 * n i - 1) 2 = 2 := max_eq_right hz
        rw [h1]
        push_cast
        linarith
      · have hz : (2 : ℤ) ≤ 2 * n i - 1 := by exact_mod_cast hc
        have h1 : max (2 * n i - 1) 2 = 2 * n i - 1 := max_eq_left hz
        rw [h1]
        push_cast
        linarith
    · unfold FaceHi
      have he : ((2 * n i + 1 : ℤ) : ℝ) / 2 = (n i : ℝ) + 1 / 2 := by
        push_cast
        ring
      rw [he]
      linarith
  · refine Finset.ext fun d => ⟨fun hd => ?_, fun hd => ?_⟩
    · rw [Finset.mem_image] at hd
      obtain ⟨i, -, rfl⟩ := hd
      exact hgin i
    · have hdL : d ∈ L := Finset.mem_sort (· ≤ ·) |>.mpr hd
      obtain ⟨j, hj, hjeq⟩ := List.mem_iff_getElem.mp hdL
      rw [Finset.mem_image]
      refine ⟨⟨j, ?_⟩, Finset.mem_univ _, ?_⟩
      · have h7 : L.length ≤ 7 := by rw [hLlen]; exact hcard
        omega
      · simp only [hgdef]
        rw [dif_pos hj]
        show L[(j : ℕ)] = d
        exact hjeq

#print axioms coverTuple

/-! ## The four box classes, the covering hypothesis, and the OWED soundness lemmas -/

/-- **Class (i) M1**: the M1 closed-form interval certificate — a `ZoneClearCert n 0`
(a `W₀` clear point over the raw faces, as a decidable integer check).  The C_L closed form
(`cL_one` below) is proved; the 62,000-tuple check and the 36 interior gap-edge forms are
data-side (they produce instances of this predicate). -/
-- STANDING: DEFINITION
def M1Cond (n : Fin 7 → ℤ) : Prop := ∃ r base : ℤ, ZoneClearCond n r base 0

/-- **Class (ii) M4**: the M4 certificate-DFS verdict.  The DFS
(`j2_admit_cert2_checkpoint.jsonl`, 12,540 boxes, 14,829/15,622-leaf forms) concludes the
same avoidance as M1 — no `W₀` chain for any real readings in the box, hence a `W₀` clear
point — so the Lean soundness shape is the same `ZoneClearCert n 0`; the data lemma (each M4
certificate yields such an instance) is data-side, separate from M1's. -/
-- STANDING: DEFINITION
def M4Cond (n : Fin 7 → ℤ) : Prop := ∃ r base : ℤ, ZoneClearCond n r base 0

/-- A raw-edge conflict datum: the word edge on readings `(y, x)` with box demand `A/B`
(numerators `8m±1`, denominators from the box faces `2n±1`), against the chain cap `C/D` on
`ρ_y/ρ_x`.  The conflict is `A·C ≤ B·D` (`d·d̄ ≤ 1`, E's corrected raw-edge law,
`j2_cycle_v12.py/.out`). -/
-- STANDING: DEFINITION
structure JoinEdge where
  x : Fin 7
  y : Fin 7
  A : ℤ
  B : ℤ
  C : ℤ
  D : ℤ
deriving DecidableEq

/-- The raw-edge conflict family: every edge in the family has positive denominators, the
conflict inequality `A·C ≤ B·D`, and the `8m±1` numerator form.  (The VALIDITY of the family
— that `A/B` bounds the actual word edge over the box and `C/D` the chain's coverage — is
the OWED soundness direction, `OneSidedSound`/`PairwiseSound`.) -/
-- STANDING: DEFINITION
def JoinFam (n : Fin 7 → ℤ) (fam : Finset JoinEdge) : Prop :=
  ∀ e : {e // e ∈ fam},
    0 < e.1.B ∧ 0 < e.1.D ∧ e.1.A * e.1.C ≤ e.1.B * e.1.D ∧
      (e.1.A % 8 = 1 ∨ e.1.A % 8 = 7) ∧ (e.1.C % 8 = 1 ∨ e.1.C % 8 = 7)

instance (n : Fin 7 → ℤ) (fam : Finset JoinEdge) : Decidable (JoinFam n fam) :=
  Fintype.decidableForallFintype

/-- **Class (iii) OneSided**: a raw-edge conflict family; for the 68 one-sided chain boxes
the artifact kill is conditional on a `W₀` chain (`j2_cycle_v6/v10.out`), so the soundness
hypothesis `OneSidedSound` carries the condition and the bridge splits on the carve. -/
-- STANDING: DEFINITION
def OneSidedCond (n : Fin 7 → ℤ) : Prop := ∃ fam : Finset JoinEdge, JoinFam n fam

/-- **Class (iv) Pairwise**: the same family shape for the 5 two-sided boxes, killed
pairwise — every surviving (W₁ word, W₀ chain) pair has a conflicting raw edge. -/
-- STANDING: DEFINITION
def PairwiseCond (n : Fin 7 → ℤ) : Prop := ∃ fam : Finset JoinEdge, JoinFam n fam

/-- **OWED — the one-sided soundness** (`j2_cycle_v6/v10.out`): for a one-sided box, IF the
arrangement's readings carve `[1,7]` (the `W₀` chain) THEN the box+join kill gives a `W₁`
clear point over the faces. -/
-- STANDING: OWED
def OneSidedSound : Prop :=
  ∀ (n : Fin 7 → ℤ) (fam : Finset JoinEdge), InRange17 n → JoinFam n fam →
    ∀ (g : Fin 7 → ℝ), (∀ i, FaceLo n i ≤ g i ∧ g i ≤ FaceHi n i) →
      Fresh.FrontierFamilyCap.CarvesOneSeven (Finset.image g Finset.univ) →
      ∃ s, 9 ≤ s ∧ s ≤ 15 ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (g i * (s / 8))

/-- **OWED — the pairwise soundness** (E's raw-edge law, `j2_cycle_v12`): for a two-sided
box, the conflict family gives: no carve of `[1,7]`, OR a `W₁` clear point over the faces. -/
-- STANDING: OWED
def PairwiseSound : Prop :=
  ∀ (n : Fin 7 → ℤ) (fam : Finset JoinEdge), InRange17 n → JoinFam n fam →
    ∀ (g : Fin 7 → ℝ), (∀ i, FaceLo n i ≤ g i ∧ g i ≤ FaceHi n i) →
      Fresh.Certs.NoCarve g ∨
        (∃ s, 9 ≤ s ∧ s ≤ 15 ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (g i * (s / 8)))

/-- **The covering hypothesis (the decidable integer check)**: every 7-tuple in `[1,17]` (the
J2 range; see the module docstring for the reduction to the artifact's 74,613 sorted
6-tuples) is killed by one of the four classes.  The data lemmas discharging it: the C_L
x=1 form is `cL_one` (PROVED); the 62,000 M1 verdicts, the 12,540 M4 verdicts, the 68
one-sided chain boxes and the 5 two-sided boxes each yield their class's certificate
(data-side, per `j2_admit_cover_v1.out` / `j2_admit_cert2_checkpoint.jsonl` /
`j2_cycle_v6/v10.out` / `j2_cycle_v12.out`). -/
-- STANDING: DEFINITION
def CoverData : Prop :=
  ∀ n : Fin 7 → ℤ, InRange17 n →
    M1Cond n ∨ M4Cond n ∨ OneSidedCond n ∨ PairwiseCond n

/-- **OWED — the outside branch** (`[17,23) ∪ (23,25) X24 ∪ [25,49)`): arrangements whose
normalised readings exceed 17 but stay at or below 49 land below 17.  The four schema classes
supplying it (per box, over the enumerated ranges): fixed-R₀ (`Fresh.Certs.FixedClearCert`),
window-type (`Fresh.Certs.WindowCert`), seam-cycle-plane (`Fresh.Certs.noCarve_split` with
the `planeH1`/`planeH2` tie planes), and pinch (the `h₃ = 25ρ₇ − 89ρ₅` exit-exit tangency,
`Fresh.Certs.PinchCert`-shaped, `Fresh/PinchCert.lean` in progress) — the first two already
have Lean soundness in `Fresh.Certs`, and each gives either a `W₀` clear point (hence the
landing in `W₀` by the core bridge) or, for the X24 seam-cycle family, a `W₁` clear point. -/
-- STANDING: OWED
def OutsideBelow17 : Prop :=
  ∀ v : Fin 8 → ℝ, Fresh.IsArrangement v → ∀ (k : Fin 8) (m : ℝ), Fresh.IsDmin v k m →
    (∃ d ∈ disparitySet v k, 17 * m < d) → (∀ d ∈ disparitySet v k, d ≤ 49 * m) →
      Fresh.FilterSkeleton.CascadeLandsBelow17 (disparitySet v k) m

/-- **OWED — the tail** (`[49,∞)`, open in the campaign): arrangements with a normalised
reading past 49 land below 17. -/
-- STANDING: OWED
def TailBelow17 : Prop :=
  ∀ v : Fin 8 → ℝ, Fresh.IsArrangement v → ∀ (k : Fin 8) (m : ℝ), Fresh.IsDmin v k m →
    (∃ d ∈ disparitySet v k, 49 * m < d) →
      Fresh.FilterSkeleton.CascadeLandsBelow17 (disparitySet v k) m

/-! ## The C_L closed form (proved) -/

/-- The per-coordinate C_L arithmetic: a reading's nearest integer outside `{7,8,9,15,16,17}`
makes the coordinate's face clear at `x = 1` (`r = base = 1`): for `j = 0` the lower zone
edge is at most `1 ≤ max(2n-1,2)`; for `j = 1` the face lies below `7` (`n ≤ 6`) or above
`9` (`n ≥ 10`); for `j = 2` below `15` (`n ≤ 14`); for `j ≥ 3` the zone starts past `23`. -/
theorem cL_one_coord (n : ℤ) (j : Fin 34) (h1 : 1 ≤ n) (h17 : n ≤ 17)
    (h79 : n ∉ ({7, 8, 9} : Finset ℤ)) (h15 : n ∉ ({15, 16, 17} : Finset ℤ)) :
    (2 * n + 1 : ℤ) ≤ 2 * (8 * ((j : ℕ) : ℤ) - 1) ∨
      2 * (8 * ((j : ℕ) : ℤ) + 1) ≤ max (2 * n - 1) 2 := by
  have h79' : n ≤ 6 ∨ 10 ≤ n := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at h79
    omega
  have h15' : n ≤ 14 ∨ 18 ≤ n := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at h15
    omega
  rcases le_total (2 * n - 1) 2 with hm | hm
  · rw [max_eq_right hm]
    rcases Nat.lt_or_ge (j : ℕ) 1 with hj | hj
    · have h0 : (j : ℕ) = 0 := by omega
      rw [h0]
      exact Or.inr (by norm_num)
    · refine Or.inl ?_
      have hn1 : n ≤ 1 := by linarith
      have hj1 : 1 ≤ (j : ℕ) := hj
      have hn1r : (n : ℝ) ≤ 1 := by exact_mod_cast hn1
      have hjr : (1 : ℝ) ≤ ((j : ℕ) : ℝ) := by exact_mod_cast hj1
      push_cast
      linarith
  · rw [max_eq_left hm]
    rcases h79' with hn6 | hn10
    · rcases Nat.lt_or_ge (j : ℕ) 1 with hj | hj
      · have h0 : (j : ℕ) = 0 := by omega
        rw [h0]
        exact Or.inr hm
      · refine Or.inl ?_
        have hj1 : 1 ≤ (j : ℕ) := hj
        have hn6r : (n : ℝ) ≤ 6 := by exact_mod_cast hn6
        have hjr : (1 : ℝ) ≤ ((j : ℕ) : ℝ) := by exact_mod_cast hj1
        push_cast
        linarith
    · rcases Nat.lt_or_ge (j : ℕ) 2 with hj | hj
      · rcases Nat.lt_or_ge (j : ℕ) 1 with h0 | h1
        · have hz : (j : ℕ) = 0 := by omega
          rw [hz]
          exact Or.inr hm
        · have hon : (j : ℕ) = 1 := by omega
          rw [hon]
          refine Or.inr ?_
          have hn10r : (10 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn10
          push_cast
          linarith
      · refine Or.inl ?_
        have hn14 : n ≤ 14 := by
          rcases h15' with h | h
          · exact h
          · linarith
        have hj2 : 2 ≤ (j : ℕ) := hj
        have hn14r : (n : ℝ) ≤ 14 := by exact_mod_cast hn14
        have hjr : (2 : ℝ) ≤ ((j : ℕ) : ℝ) := by exact_mod_cast hj2
        push_cast
        linarith

#print axioms cL_one_coord

/-- **The C_L closed form** (the M1 x=1 case, fully proved): a tuple in range with NO
reading's nearest integer in `{7,8,9,15,16,17}` has `x = 1` clear over all its faces — the
point `R = 1` is covered by no way-zone, so the box admits a `W₀` clear point (`M1Cond`).
This is the integer port of `j2_admit_mech_v1.py` mechanism (b) at `x* = 1`: at `x = 1` a
face `[max(n-1/2,1), n+1/2]` meets a zone `(8j-1, 8j+1)` exactly for
`n ∈ {7,8,9,15,16,17}` (zone `(7,9)`: `j = 1`; zone `(15,17)`: `j = 2`). -/
theorem cL_one (n : Fin 7 → ℤ) (hrange : InRange17 n)
    (h : ∀ i, n i ∉ ({7, 8, 9, 15, 16, 17} : Finset ℤ)) : ZoneClearCond n 1 1 0 := by
  have hmem79 : ∀ i, n i ∉ ({7, 8, 9} : Finset ℤ) := by
    intro i hmem
    refine h i ?_
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem ⊢
    tauto
  have hmem1516 : ∀ i, n i ∉ ({15, 16, 17} : Finset ℤ) := by
    intro i hmem
    refine h i ?_
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem ⊢
    tauto
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩
  · intro i
    exact (hrange i).2
  · intro i j
    simpa using cL_one_coord (n i) j (hrange i).1 (hrange i).2 (hmem79 i) (hmem1516 i)

#print axioms cL_one

/-- The C_L instance of class (i): every no-straddle tuple in range is M1-killed. -/
theorem m1Cond_of_cL (n : Fin 7 → ℤ) (hrange : InRange17 n)
    (h : ∀ i, n i ∉ ({7, 8, 9, 15, 16, 17} : Finset ℤ)) : M1Cond n :=
  ⟨1, 1, cL_one n hrange h⟩

#print axioms m1Cond_of_cL

/-! ## The totality-and-split theorem -/

/-- The transport helper: a per-coordinate clear statement over `g` is a per-reading clear
statement over the normalised disparity set (via `image g = dsn`). -/
theorem clear_of_image {v : Fin 8 → ℝ} {k : Fin 8} {m : ℝ} {g : Fin 7 → ℝ}
    (himage : Finset.image g Finset.univ
      = Finset.image (fun d => d / m) (disparitySet v k))
    {s : ℝ} (hcl : ∀ i, (1 / 8 : ℝ) ≤ distInt (g i * (s / 8))) :
    ∀ d ∈ disparitySet v k, (1 / 8 : ℝ) ≤ distInt ((d / m) * (s / 8)) := by
  intro d hd
  have hmem : d / m ∈ Finset.image g Finset.univ := by
    rw [himage]
    exact Finset.mem_image.mpr ⟨d, hd, rfl⟩
  rw [Finset.mem_image] at hmem
  obtain ⟨i, -, he⟩ := hmem
  rw [← he]
  exact hcl i

#print axioms clear_of_image

/-- **(c) The totality-and-split theorem**: IF the four classes cover every J2 tuple
(`CoverData`), THEN every arrangement with `ρ₇ ≤ 17` (all normalised readings at most 17)
lands below 17.  Composed from the per-class certificates through the core bridge
`cascadeLandsBelow17_of_clearPoint`: classes (i)/(ii) via `ClearPointOfCert`, class (iii) via
`OneSidedSound` (splitting on whether the arrangement carves `[1,7]`), class (iv) via
`PairwiseSound`; the no-carve routes go through the `notCarve_witness` lonely point. -/
theorem allLandBelow17_of_coverData (hCover : CoverData) (hCP : ClearPointOfCert)
    (hOneS : OneSidedSound) (hPair : PairwiseSound) {v : Fin 8 → ℝ} (hv : Fresh.IsArrangement v)
    {k : Fin 8} {m : ℝ} (hm : Fresh.IsDmin v k m)
    (hmax : ∀ d ∈ disparitySet v k, d ≤ 17 * m) :
    Fresh.FilterSkeleton.CascadeLandsBelow17 (disparitySet v k) m := by
  obtain ⟨g, n, hrange, hface, himage⟩ := coverTuple hv hm hmax
  have hge1 : ∀ i, 1 ≤ n i := fun i => (hrange i).1
  rcases hCover n hrange with hM1 | hM4 | hOS | hPW
  · -- (i) M1: the W₀ clear-point route
    obtain ⟨r, base, hc⟩ := hM1
    obtain ⟨s, hs1, hs2, hsw, hcl⟩ :=
      hCP n 0 (certOfCond n r base 0 hc) (by omega) g hface
    exact cascadeLandsBelow17_of_clearPoint hv hm s hs1 hs2 hsw
      (clear_of_image himage hcl)
  · -- (ii) M4: the same soundness shape
    obtain ⟨r, base, hc⟩ := hM4
    obtain ⟨s, hs1, hs2, hsw, hcl⟩ :=
      hCP n 0 (certOfCond n r base 0 hc) (by omega) g hface
    exact cascadeLandsBelow17_of_clearPoint hv hm s hs1 hs2 hsw
      (clear_of_image himage hcl)
  · -- (iii) OneSided: split on whether the arrangement carves [1,7]
    obtain ⟨fam, hfam⟩ := hOS
    by_cases hcarve : Fresh.FrontierFamilyCap.CarvesOneSeven (Finset.image g Finset.univ)
    · obtain ⟨s, hs9, hs15, hcl⟩ := hOneS n fam hrange hfam g hface hcarve
      refine cascadeLandsBelow17_of_clearPoint hv hm s ?_ hs15 (Or.inr hs9) ?_
      · linarith
      · exact clear_of_image himage hcl
    · -- not carved: the witness route (a lonely point in [1/8, 7/8] caps the landing in W₀)
      have hnc : Fresh.Certs.NoCarve g := hcarve
      obtain ⟨t, ht1, ht2, hlon⟩ := (notCarve_witness g).mp hnc
      refine cascadeLandsBelow17_of_clearPoint hv hm (8 * t) ?_ ?_ (Or.inl ?_) ?_
      · linarith
      · linarith
      · linarith
      · intro d hd
        have hmem : d / m ∈ Finset.image g Finset.univ := by
          rw [himage]
          exact Finset.mem_image.mpr ⟨d, hd, rfl⟩
        rw [Finset.mem_image] at hmem
        obtain ⟨i, -, he⟩ := hmem
        rw [← he]
        have hdist := hlon (g i) (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)
        have he8 : (8 * t) / 8 = t := by field_simp
        rw [he8]
        exact hdist
  · -- (iv) Pairwise: the soundness gives the disjunction directly
    obtain ⟨fam, hfam⟩ := hPW
    rcases hPair n fam hrange hfam g hface with hnc | ⟨s, hs9, hs15, hcl⟩
    · obtain ⟨t, ht1, ht2, hlon⟩ := (notCarve_witness g).mp hnc
      refine cascadeLandsBelow17_of_clearPoint hv hm (8 * t) ?_ ?_ (Or.inl ?_) ?_
      · linarith
      · linarith
      · linarith
      · intro d hd
        have hmem : d / m ∈ Finset.image g Finset.univ := by
          rw [himage]
          exact Finset.mem_image.mpr ⟨d, hd, rfl⟩
        rw [Finset.mem_image] at hmem
        obtain ⟨i, -, he⟩ := hmem
        rw [← he]
        have hdist := hlon (g i) (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)
        have he8 : (8 * t) / 8 = t := by field_simp
        rw [he8]
        exact hdist
    · refine cascadeLandsBelow17_of_clearPoint hv hm s ?_ hs15 (Or.inr hs9) ?_
      · linarith
      · exact clear_of_image himage hcl

#print axioms allLandBelow17_of_coverData

/-- The arrangement-level assembly of the three regions (J2 inside, outside, tail). -/
theorem allLandBelow17_of_assembly (hCover : CoverData) (hCP : ClearPointOfCert)
    (hOneS : OneSidedSound) (hPair : PairwiseSound) (hOutside : OutsideBelow17)
    (hTail : TailBelow17) : Fresh.FilterSkeleton.AllArrangementsLandBelow17 := by
  intro v hv k m hm
  by_cases h17 : ∀ d ∈ disparitySet v k, d ≤ 17 * m
  · exact allLandBelow17_of_coverData hCover hCP hOneS hPair hv hm h17
  · push_neg at h17
    obtain ⟨d, hdmem, hd17⟩ := h17
    by_cases h49 : ∀ d' ∈ disparitySet v k, d' ≤ 49 * m
    · exact hOutside v hv k m hm ⟨d, hdmem, hd17⟩ h49
    · push_neg at h49
      obtain ⟨d', hd'mem, hd'49⟩ := h49
      exact hTail v hv k m hm ⟨d', hd'mem, hd'49⟩

#print axioms allLandBelow17_of_assembly

/-- **(d) The full assembly**: the four-branch J2 cover (`CoverData`), the certificate
soundness (`ClearPointOfCert`), the one-sided and pairwise soundness, the outside
certificates and the tail give the n=8 Lonely Runner conjecture, composed with
`Fresh.FilterSkeleton.lonelyRunnerEight_of_allLandBelow17`. -/
theorem filterAssembly (hCover : CoverData) (hCP : ClearPointOfCert) (hOneS : OneSidedSound)
    (hPair : PairwiseSound) (hOutside : OutsideBelow17) (hTail : TailBelow17) :
    Fresh.LonelyRunnerEight :=
  Fresh.FilterSkeleton.lonelyRunnerEight_of_allLandBelow17
    (allLandBelow17_of_assembly hCover hCP hOneS hPair hOutside hTail)

#print axioms filterAssembly

end Fresh.FilterAssembly
