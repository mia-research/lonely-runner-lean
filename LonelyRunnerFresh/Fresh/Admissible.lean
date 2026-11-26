import Mathlib
import Fresh.Framework
import Fresh.Localisation
import Fresh.Grid
import Fresh.SelfMoverCommon
import Fresh.RatioLanding
import Fresh.DminClear

/-!
# Admissible arrangements: the complement of the proved classes

Written 2026-10-24 (owner: move from arbitrary arrangements to admissible arrangements, then reduce admissible to a finite set; AP and residue speeds are proved and scale invariant).
Real speeds, ordered arrangements (`IsOrderedArrangement`: positive, strictly increasing).  Three proved classes, each carrying a first isolation:
* `GridClass v` (`IsGrid`): speeds `v₀ + idx j · d` with a complete residue system mod 8 (the AP is one); globally isolated at `a/(8d)`, `a` a unit mod 8 (`gridGlobalIsolation`).
* `RatioClass v k`: the subject's disparities lie in `[m, 7 m]`, `m = d_min` (`ratio_firstIso`): first isolation `1/(8 m)`.
* `Unblocked v k`: no disparity within one `d_min` of a positive multiple of `8 d_min`, i.e. every reading is clear at `1/(8 m)` (`dmin_firstIso_iff`): first isolation `1/(8 m)`.
`Proved v k := GridClass v ∨ RatioClass v k ∨ Unblocked v k`; `Admissible v k := IsOrderedArrangement v ∧ ¬ Proved v k`.
* `proved_isolation`: a proved class gives an isolation of the subject; `ratio_imp_unblocked`: the ratio class is inside the unblocked class.
* `proved_or_admissible`: every ordered arrangement and subject is proved or admissible.
* Scale invariance (`Proved_smul`, `Admissible_smul`) and translation invariance (`Proved_add`, `Admissible_add`): the classes depend on the ratios of the disparities only.
* `admissible_iff_blocked`: for an ordered arrangement, `Admissible v k` iff the arrangement is not a grid and the d_min instant is blocked by some reading (the class C of E602).
* `admissible_exists`: an explicit admissible arrangement (non-vacuity), with an irrational ratio so that it is not a grid.
Grades: [L].  Not claimed: that the admissible set is finite, or any statement about admissible arrangements (that is the owed content).
-/

open Classical

namespace Fresh.Admissible

open Fresh Fresh.OneMover

-- STANDING: DEFINITION
def GridClass (v : Fin 8 → ℝ) : Prop := IsGrid v

-- STANDING: DEFINITION
def RatioClass (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  ∃ m, IsDmin v k m ∧ ∀ i, i ≠ k → |v i - v k| ≤ 7 * m

-- STANDING: DEFINITION
def Unblocked (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  ∃ m, IsDmin v k m ∧ ∀ i, i ≠ k → (1 / 8 : ℝ) ≤ distInt (|v i - v k| * (1 / (8 * m)))

-- STANDING: DEFINITION
def Proved (v : Fin 8 → ℝ) (k : Fin 8) : Prop := GridClass v ∨ RatioClass v k ∨ Unblocked v k

-- STANDING: DEFINITION
def Admissible (v : Fin 8 → ℝ) (k : Fin 8) : Prop := IsOrderedArrangement v ∧ ¬ Proved v k

theorem dmin_facts {v : Fin 8 → ℝ} {k : Fin 8} {m : ℝ} (h : IsDmin v k m) (hinj : Function.Injective v) :
    0 < m ∧ (∃ i, i ≠ k ∧ |v i - v k| = m) ∧ ∀ i, i ≠ k → m ≤ |v i - v k| := by
  obtain ⟨hmem, hlb⟩ := h
  simp only [disparitySet, Finset.coe_image, Finset.coe_erase, Set.mem_image, Set.mem_diff, Finset.mem_coe,
    Finset.mem_univ, true_and, Set.mem_singleton_iff] at hmem
  obtain ⟨i, hik, hi⟩ := hmem
  have hmpos : 0 < m := by
    rw [← hi]; exact abs_pos.mpr (sub_ne_zero.mpr (fun h => hik (hinj h)))
  refine ⟨hmpos, ⟨i, hik, hi⟩, fun j hj => ?_⟩
  apply hlb
  simp only [disparitySet, Finset.coe_image, Finset.coe_erase, Set.mem_image, Set.mem_diff, Finset.mem_coe,
    Finset.mem_univ, true_and, Set.mem_singleton_iff]
  exact ⟨j, hj, rfl⟩

theorem exists_dmin {v : Fin 8 → ℝ} (hinj : Function.Injective v) (k : Fin 8) : ∃ m, IsDmin v k m := by
  have hne : (disparitySet v k).Nonempty := by
    obtain ⟨i, hi⟩ : ∃ i : Fin 8, i ≠ k := by
      by_cases hk : k = 0
      · exact ⟨1, by rw [hk]; decide⟩
      · exact ⟨0, fun h => hk h.symm⟩
    exact ⟨|v i - v k|, Finset.mem_image.2 ⟨i, Finset.mem_erase.2 ⟨hi, Finset.mem_univ _⟩, rfl⟩⟩
  exact ⟨(disparitySet v k).min' hne, Finset.min'_mem _ _, fun d hd => Finset.min'_le _ _ hd⟩

theorem dmin_unique {v : Fin 8 → ℝ} {k : Fin 8} {m m' : ℝ} (h : IsDmin v k m) (h' : IsDmin v k m') : m = m' :=
  h.unique h'

theorem ratio_imp_unblocked {v : Fin 8 → ℝ} (hinj : Function.Injective v) {k : Fin 8} (h : RatioClass v k) : Unblocked v k := by
  obtain ⟨m, hm, h7⟩ := h
  obtain ⟨hpos, hmem, hle⟩ := dmin_facts hm hinj
  refine ⟨m, hm, ?_⟩
  have := ratio_firstIso v k m hpos hmem (fun i hi => ⟨hle i hi, h7 i hi⟩)
  exact (dmin_firstIso_iff v k m hpos hmem hle).1 this

theorem proved_isolation {v : Fin 8 → ℝ} (hv : IsOrderedArrangement v) {k : Fin 8} (h : Proved v k) : Isolation v k := by
  have hinj : Function.Injective v := hv.2.injective
  rcases h with hg | hr | hu
  · obtain ⟨d, v₀, idx, hd, hres, hvv⟩ := hg
    have := gridGlobalIsolation v d v₀ idx hd hres hvv 1 isCoprime_one_left
    exact ⟨1 / (8 * d), by positivity, by simpa using this k⟩
  · obtain ⟨m, hm, h7⟩ := hr
    obtain ⟨hpos, hmem, hle⟩ := dmin_facts hm hinj
    exact ⟨1 / (8 * m), by positivity, (ratio_firstIso v k m hpos hmem (fun i hi => ⟨hle i hi, h7 i hi⟩)).1⟩
  · obtain ⟨m, hm, hc⟩ := hu
    obtain ⟨hpos, hmem, hle⟩ := dmin_facts hm hinj
    exact ⟨1 / (8 * m), by positivity, ((dmin_firstIso_iff v k m hpos hmem hle).2 hc).1⟩

theorem proved_or_admissible {v : Fin 8 → ℝ} (hv : IsOrderedArrangement v) (k : Fin 8) : Proved v k ∨ Admissible v k := by
  by_cases h : Proved v k
  · exact Or.inl h
  · exact Or.inr ⟨hv, h⟩

#print axioms dmin_facts
#print axioms proved_isolation
#print axioms proved_or_admissible

theorem isDmin_iff {v : Fin 8 → ℝ} {k : Fin 8} {m : ℝ} :
    IsDmin v k m ↔ (∃ i, i ≠ k ∧ |v i - v k| = m) ∧ ∀ i, i ≠ k → m ≤ |v i - v k| := by
  constructor
  · intro h
    obtain ⟨hmem, hlb⟩ := h
    simp only [disparitySet, Finset.coe_image, Finset.coe_erase, Set.mem_image, Set.mem_diff, Finset.mem_coe,
      Finset.mem_univ, true_and, Set.mem_singleton_iff] at hmem
    obtain ⟨i, hik, hi⟩ := hmem
    refine ⟨⟨i, hik, hi⟩, fun j hj => hlb ?_⟩
    simp only [disparitySet, Finset.coe_image, Finset.coe_erase, Set.mem_image, Set.mem_diff, Finset.mem_coe,
      Finset.mem_univ, true_and, Set.mem_singleton_iff]
    exact ⟨j, hj, rfl⟩
  · rintro ⟨⟨i, hik, hi⟩, hle⟩
    refine ⟨?_, ?_⟩
    · simp only [disparitySet, Finset.coe_image, Finset.coe_erase, Set.mem_image, Set.mem_diff, Finset.mem_coe,
        Finset.mem_univ, true_and, Set.mem_singleton_iff]
      exact ⟨i, hik, hi⟩
    · intro d hd
      simp only [disparitySet, Finset.coe_image, Finset.coe_erase, Set.mem_image, Set.mem_diff, Finset.mem_coe,
        Finset.mem_univ, true_and, Set.mem_singleton_iff] at hd
      obtain ⟨j, hj, rfl⟩ := hd
      exact hle j hj

/-! ## Scale and translation invariance -/

theorem isDmin_smul {c : ℝ} (hc : 0 < c) {v : Fin 8 → ℝ} {k : Fin 8} {m : ℝ} :
    IsDmin (fun j => c * v j) k (c * m) ↔ IsDmin v k m := by
  have habs : ∀ i, |c * v i - c * v k| = c * |v i - v k| := fun i => by
    rw [← mul_sub, abs_mul, abs_of_pos hc]
  rw [isDmin_iff, isDmin_iff]
  simp only [habs]
  constructor
  · rintro ⟨⟨i, hik, hi⟩, hle⟩
    exact ⟨⟨i, hik, mul_left_cancel₀ hc.ne' hi⟩, fun j hj => le_of_mul_le_mul_left (hle j hj) hc⟩
  · rintro ⟨⟨i, hik, hi⟩, hle⟩
    exact ⟨⟨i, hik, by rw [hi]⟩, fun j hj => mul_le_mul_of_nonneg_left (hle j hj) hc.le⟩

theorem isDmin_add {v : Fin 8 → ℝ} {k : Fin 8} {m s : ℝ} : IsDmin (fun j => v j + s) k m ↔ IsDmin v k m := by
  have habs : ∀ i, |v i + s - (v k + s)| = |v i - v k| := fun i => by ring_nf
  rw [isDmin_iff, isDmin_iff]
  simp only [habs]

theorem habs_smul {c : ℝ} (hc : 0 < c) (v : Fin 8 → ℝ) (i k : Fin 8) :
    |(fun j => c * v j) i - (fun j => c * v j) k| = c * |v i - v k| := by
  show |c * v i - c * v k| = c * |v i - v k|
  rw [← mul_sub, abs_mul, abs_of_pos hc]

theorem habs_add (s : ℝ) (v : Fin 8 → ℝ) (i k : Fin 8) :
    |(fun j => v j + s) i - (fun j => v j + s) k| = |v i - v k| := by
  show |v i + s - (v k + s)| = |v i - v k|
  ring_nf

theorem GridClass_smul {c : ℝ} (hc : 0 < c) (v : Fin 8 → ℝ) : GridClass (fun j => c * v j) ↔ GridClass v := by
  unfold GridClass IsGrid
  constructor
  · rintro ⟨d, v₀, idx, hd, hres, hvv⟩
    refine ⟨d / c, v₀ / c, idx, by positivity, hres, fun j => ?_⟩
    have h : c * v j = v₀ + (idx j : ℝ) * d := hvv j
    field_simp
    linarith
  · rintro ⟨d, v₀, idx, hd, hres, hvv⟩
    exact ⟨c * d, c * v₀, idx, by positivity, hres, fun j => by show c * v j = _; rw [hvv j]; ring⟩

theorem GridClass_add (s : ℝ) (v : Fin 8 → ℝ) : GridClass (fun j => v j + s) ↔ GridClass v := by
  unfold GridClass IsGrid
  constructor
  · rintro ⟨d, v₀, idx, hd, hres, hvv⟩
    exact ⟨d, v₀ - s, idx, hd, hres, fun j => by have h : v j + s = v₀ + (idx j : ℝ) * d := hvv j; linarith⟩
  · rintro ⟨d, v₀, idx, hd, hres, hvv⟩
    exact ⟨d, v₀ + s, idx, hd, hres, fun j => by show v j + s = _; rw [hvv j]; ring⟩

theorem RatioClass_smul {c : ℝ} (hc : 0 < c) (v : Fin 8 → ℝ) (k : Fin 8) :
    RatioClass (fun j => c * v j) k ↔ RatioClass v k := by
  unfold RatioClass
  constructor
  · rintro ⟨m, hm, h7⟩
    have hm' : IsDmin v k (m / c) := (isDmin_smul hc).1 (by rwa [mul_div_cancel₀ _ hc.ne'])
    refine ⟨m / c, hm', fun i hi => ?_⟩
    have h := h7 i hi
    rw [habs_smul hc] at h
    have h2 : |v i - v k| * c ≤ 7 * m := by rw [mul_comm]; exact h
    have h3 : 7 * (m / c) = 7 * m / c := by ring
    rw [h3, le_div_iff₀ hc]; exact h2
  · rintro ⟨m, hm, h7⟩
    exact ⟨c * m, (isDmin_smul hc).2 hm, fun i hi => by
      rw [habs_smul hc]; nlinarith [h7 i hi]⟩

theorem Unblocked_smul {c : ℝ} (hc : 0 < c) {v : Fin 8 → ℝ} (hinj : Function.Injective v) (k : Fin 8) :
    Unblocked (fun j => c * v j) k ↔ Unblocked v k := by
  unfold Unblocked
  constructor
  · rintro ⟨m, hm, hcl⟩
    have hm' : IsDmin v k (m / c) := (isDmin_smul hc).1 (by rwa [mul_div_cancel₀ _ hc.ne'])
    have hmpos : 0 < m / c := (dmin_facts hm' hinj).1
    refine ⟨m / c, hm', fun i hi => ?_⟩
    have h := hcl i hi
    rw [habs_smul hc] at h
    have key : c * |v i - v k| * (1 / (8 * m)) = |v i - v k| * (1 / (8 * (m / c))) := by
      have : m = c * (m / c) := by field_simp
      rw [this]; field_simp
    rw [key] at h
    have hm2 : m = c * (m / c) := by field_simp
    convert h using 3 <;> simp [hm2] <;> field_simp
  · rintro ⟨m, hm, hcl⟩
    have hmpos : 0 < m := (dmin_facts hm hinj).1
    refine ⟨c * m, (isDmin_smul hc).2 hm, fun i hi => ?_⟩
    rw [habs_smul hc]
    have key : c * |v i - v k| * (1 / (8 * (c * m))) = |v i - v k| * (1 / (8 * m)) := by
      field_simp
    rw [key]; exact hcl i hi

theorem Proved_smul {c : ℝ} (hc : 0 < c) {v : Fin 8 → ℝ} (hinj : Function.Injective v) (k : Fin 8) :
    Proved (fun j => c * v j) k ↔ Proved v k := by
  unfold Proved
  rw [GridClass_smul hc, RatioClass_smul hc, Unblocked_smul hc hinj]

theorem Proved_add (s : ℝ) (v : Fin 8 → ℝ) (hinj : Function.Injective v) (k : Fin 8) :
    Proved (fun j => v j + s) k ↔ Proved v k := by
  unfold Proved RatioClass Unblocked
  rw [GridClass_add]
  have hd : ∀ m, IsDmin (fun j => v j + s) k m ↔ IsDmin v k m := fun m => isDmin_add
  simp only [hd, habs_add]

theorem Admissible_smul {c : ℝ} (hc : 0 < c) {v : Fin 8 → ℝ} (hv : IsOrderedArrangement v) (k : Fin 8) :
    Admissible (fun j => c * v j) k ↔ Admissible v k := by
  unfold Admissible
  have ho : IsOrderedArrangement (fun j => c * v j) ↔ IsOrderedArrangement v := by
    constructor
    · rintro ⟨hp, hm⟩
      refine ⟨fun j => ?_, fun a b hab => ?_⟩
      · have h : 0 < c * v j := hp j
        exact (pos_iff_pos_of_mul_pos h).1 hc
      · have h : c * v a < c * v b := hm hab
        exact lt_of_mul_lt_mul_left h hc.le
    · rintro ⟨hp, hm⟩
      exact ⟨fun j => mul_pos hc (hp j), fun a b hab => mul_lt_mul_of_pos_left (hm hab) hc⟩
  rw [ho, Proved_smul hc hv.2.injective]

#print axioms Proved_smul
#print axioms Admissible_smul
#print axioms Proved_add

/-- **Admissible = not a grid, and the d_min instant is blocked by some reading (class C).** -/
theorem admissible_iff_blocked {v : Fin 8 → ℝ} (hv : IsOrderedArrangement v) (k : Fin 8) :
    Admissible v k ↔ ¬ GridClass v ∧ ∃ m, IsDmin v k m ∧ ∃ j, j ≠ k ∧ distInt (|v j - v k| * (1 / (8 * m))) < 1 / 8 := by
  have hinj : Function.Injective v := hv.2.injective
  unfold Admissible
  constructor
  · rintro ⟨_, hnp⟩
    unfold Proved at hnp
    push Not at hnp
    obtain ⟨hng, hnr, hnu⟩ := hnp
    refine ⟨hng, ?_⟩
    obtain ⟨m, hm⟩ := exists_dmin hinj k
    refine ⟨m, hm, ?_⟩
    by_contra hcon
    push Not at hcon
    exact hnu ⟨m, hm, fun i hi => hcon i hi⟩
  · rintro ⟨hng, m, hm, j, hjk, hblock⟩
    refine ⟨hv, ?_⟩
    unfold Proved
    push Not
    have hnu : ¬ Unblocked v k := by
      rintro ⟨m', hm', hcl⟩
      have : m' = m := dmin_unique hm' hm
      subst this
      have := hcl j hjk
      linarith
    exact ⟨hng, fun hr => hnu (ratio_imp_unblocked hinj hr), hnu⟩

#print axioms admissible_iff_blocked

/-! ## Non-vacuity: an admissible arrangement -/

/-- Speeds `1, 2, ..., 7, 8 + √2`: the last disparity of the runner at speed 1 is `7 + √2`, within one `d_min` of `8 d_min`, and the ratio `7 + √2` is irrational, so this is not a grid. -/
noncomputable def exV : Fin 8 → ℝ := fun j => ((j : ℕ) : ℝ) + 1 + (if (j : ℕ) = 7 then Real.sqrt 2 else 0)

theorem exV_ordered : IsOrderedArrangement exV := by
  have hs := Real.sqrt_nonneg 2
  have hs2 : 0 < Real.sqrt 2 := by positivity
  refine ⟨fun j => ?_, fun a b hab => ?_⟩
  · unfold exV; split_ifs <;> positivity
  · have hlt : (a : ℕ) < (b : ℕ) := hab
    have hb7 : (b : ℕ) ≤ 7 := by omega
    have ha6 : (a : ℕ) ≤ 6 := by omega
    have ha7 : (a : ℕ) ≠ 7 := by omega
    have hnat : ((a : ℕ) : ℝ) + 1 ≤ ((b : ℕ) : ℝ) := by exact_mod_cast hlt
    unfold exV
    rw [if_neg ha7]
    by_cases hb : (b : ℕ) = 7
    · rw [if_pos hb, hb]
      have : ((a : ℕ) : ℝ) ≤ 6 := by exact_mod_cast ha6
      push_cast; linarith
    · rw [if_neg hb]; linarith

theorem exV_dmin : IsDmin exV 0 1 := by
  rw [isDmin_iff]
  have hs := Real.sqrt_nonneg 2
  refine ⟨⟨1, by decide, ?_⟩, fun i hi => ?_⟩
  · unfold exV; norm_num
  · unfold exV
    have hi0 : 1 ≤ (i : ℕ) := by
      have : (i : ℕ) ≠ 0 := fun h => hi (Fin.ext h)
      omega
    have : (1 : ℝ) ≤ ((i : ℕ) : ℝ) := by exact_mod_cast hi0
    have e : (((i : ℕ) : ℝ) + 1 + (if (i : ℕ) = 7 then Real.sqrt 2 else 0)) - (((0 : Fin 8) : ℕ) + 1 + (if ((0 : Fin 8) : ℕ) = 7 then Real.sqrt 2 else 0))
        = ((i : ℕ) : ℝ) + (if (i : ℕ) = 7 then Real.sqrt 2 else 0) := by simp; ring
    rw [e, abs_of_nonneg (by split_ifs <;> linarith)]
    split_ifs <;> linarith

theorem exV_not_grid : ¬ GridClass exV := by
  rintro ⟨d, v₀, idx, hd, hres, hvv⟩
  have h0 := hvv 0
  have h1 := hvv 1
  have h7 := hvv 7
  simp only [exV] at h0 h1 h7
  norm_num at h0 h1 h7
  have ha : ((idx 1 : ℝ) - idx 0) * d = 1 := by linarith
  have hb : ((idx 7 : ℝ) - idx 0) * d = 7 + Real.sqrt 2 := by linarith
  have hane : ((idx 1 : ℝ) - idx 0) ≠ 0 := by
    intro h; rw [h] at ha; simp at ha
  apply irrational_sqrt_two
  refine ⟨((idx 7 - idx 0 : ℤ) : ℚ) / ((idx 1 - idx 0 : ℤ) : ℚ) - 7, ?_⟩
  push_cast
  have hd1 : d = 1 / ((idx 1 : ℝ) - idx 0) := by field_simp; linarith
  rw [hd1] at hb
  field_simp at hb ⊢
  linarith

theorem admissible_exists : Admissible exV 0 := by
  rw [admissible_iff_blocked exV_ordered]
  refine ⟨exV_not_grid, 1, exV_dmin, 7, by decide, ?_⟩
  have hs := Real.sqrt_nonneg 2
  have hs2 : Real.sqrt 2 < 2 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have hsq : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hs1 : 1 ≤ Real.sqrt 2 := by nlinarith
  have e : |exV 7 - exV 0| = 7 + Real.sqrt 2 := by
    unfold exV; norm_num; rw [abs_of_nonneg (by linarith)]; ring
  rw [e]
  have h := Fresh.Localisation.distInt_le ((7 + Real.sqrt 2) * (1 / (8 * 1))) 1
  have h2 : |(7 + Real.sqrt 2) * (1 / (8 * 1)) - ((1 : ℤ) : ℝ)| = (Real.sqrt 2 - 1) / 8 := by
    push_cast
    rw [show (7 + Real.sqrt 2) * (1 / (8 * 1)) - 1 = (Real.sqrt 2 - 1) / 8 by ring]
    rw [abs_of_nonneg (by linarith)]
  rw [h2] at h
  linarith

#print axioms admissible_exists

end Fresh.Admissible
