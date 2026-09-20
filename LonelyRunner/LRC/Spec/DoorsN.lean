import LonelyRunner.LRC.Spec.Doors

/-!
# Everything the `n = 8` Spec layer has, at every order `n ≥ 2`

An experiment (2026-09-20): the owner asked for the whole `n = 8` apparatus rebuilt at a
variable `n`, so that whatever fails to generalise is named rather than guessed at.

This file carries across, in order, every declaration of
`LRC/Cascade/Arrangement.lean`, `LRC/Spec/Target.lean` and `LRC/Spec/Doors.lean`, with
`Fin 8 → Fin n`, `(8 : ℝ)⁻¹ → (n : ℝ)⁻¹`, `ds.card ≤ 7 → ds.card ≤ n - 1`,
`(8 : ℤ) → (n : ℤ)` and `1/(8*m) → 1/(n*m)`.

Findings are recorded at the foot of the file and in `docs/nN/SMALL_ORDER_DOORS_v3.md`.
Nothing here is new mathematics; it is the same chain with `8` replaced by `n`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

namespace LRC.SpecN

open Flanks MomentIterationN

variable {n : ℕ} [Fact (2 ≤ n)]

/-! ## 1. the arrangement layer  (`Cascade/Arrangement.lean`) -/

def sep (v : Fin n → ℝ) (k i : Fin n) (t : ℝ) : ℝ := v i * t - v k * t

theorem sep_eq (v : Fin n → ℝ) (k i : Fin n) (t : ℝ) : sep v k i t = (v i - v k) * t := by
  unfold sep; ring

def InWay (v : Fin n → ℝ) (k i : Fin n) (t : ℝ) : Prop := circDist (sep v k i t) < (n : ℝ)⁻¹

def LonelyAt (v : Fin n → ℝ) (k : Fin n) (t : ℝ) : Prop :=
  ∀ i : Fin n, i ≠ k → (n : ℝ)⁻¹ ≤ circDist (sep v k i t)

theorem lonelyAt_iff_no_inWay {v : Fin n → ℝ} {k : Fin n} {t : ℝ} :
    LonelyAt v k t ↔ ∀ i : Fin n, i ≠ k → ¬ InWay v k i t := by
  unfold LonelyAt InWay
  exact forall_congr' fun i => forall_congr' fun _ => (not_lt).symm

theorem lonelyAt_iff_two_sided {v : Fin n → ℝ} {k : Fin n} {t : ℝ} :
    LonelyAt v k t ↔
      (∀ i : Fin n, i ≠ k → (n : ℝ)⁻¹ ≤ Int.fract (sep v k i t)) ∧
      (∀ i : Fin n, i ≠ k → Int.fract (sep v k i t) ≤ 1 - (n : ℝ)⁻¹) := by
  unfold LonelyAt circDist
  constructor
  · intro h
    refine ⟨fun i hi => le_trans (h i hi) (min_le_left _ _), fun i hi => ?_⟩
    have := le_trans (h i hi) (min_le_right _ _); linarith
  · rintro ⟨h1, h2⟩ i hi
    exact le_min (h1 i hi) (by have := h2 i hi; linarith)

theorem others_nonempty (k : Fin n) : (Finset.univ.erase k).Nonempty := by
  rw [← Finset.card_pos, Finset.card_erase_of_mem (Finset.mem_univ k)]
  have := (Fact.out : 2 ≤ n)
  simp only [Finset.card_univ, Fintype.card_fin]
  omega

theorem lonelyAt_iff_neighbours {v : Fin n → ℝ} {k : Fin n} {t : ℝ} :
    LonelyAt v k t ↔
      (n : ℝ)⁻¹ ≤ (Finset.univ.erase k).inf' (others_nonempty k)
          (fun i => Int.fract (sep v k i t)) ∧
      (Finset.univ.erase k).sup' (others_nonempty k)
          (fun i => Int.fract (sep v k i t)) ≤ 1 - (n : ℝ)⁻¹ := by
  rw [lonelyAt_iff_two_sided, Finset.le_inf'_iff, Finset.sup'_le_iff]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun i hi => h1 i (Finset.mem_erase.mp hi).1, fun i hi => h2 i (Finset.mem_erase.mp hi).1⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun i hi => h1 i (Finset.mem_erase.mpr ⟨hi, Finset.mem_univ i⟩),
           fun i hi => h2 i (Finset.mem_erase.mpr ⟨hi, Finset.mem_univ i⟩)⟩

def disp (v : Fin n → ℝ) (k i : Fin n) : ℝ := v i - v k

theorem sep_eq_disp_mul (v : Fin n → ℝ) (k i : Fin n) (t : ℝ) :
    sep v k i t = disp v k i * t := by unfold sep disp; ring

theorem disp_ne_zero {v : Fin n → ℝ} (hv : Function.Injective v) {k i : Fin n} (hi : i ≠ k) :
    disp v k i ≠ 0 := sub_ne_zero.mpr fun h => hi (hv h)

theorem inWay_comm {v : Fin n → ℝ} {k i : Fin n} {t : ℝ} :
    InWay v k i t ↔ InWay v i k t := by
  unfold InWay sep
  rw [show v k * t - v i * t = -(v i * t - v k * t) by ring, Flanks.circDist_neg]

theorem sep_add_const (v : Fin n → ℝ) (c : ℝ) (k i : Fin n) (t : ℝ) :
    sep (fun j => v j + c) k i t = sep v k i t := by unfold sep; ring

theorem lonelyAt_add_const {v : Fin n → ℝ} {c : ℝ} {k : Fin n} {t : ℝ} :
    LonelyAt (fun j => v j + c) k t ↔ LonelyAt v k t := by
  unfold LonelyAt; simp only [sep_add_const]

theorem sep_const_mul (v : Fin n → ℝ) (c : ℝ) (k i : Fin n) (t : ℝ) :
    sep (fun j => c * v j) k i t = sep v k i (c * t) := by unfold sep; ring

theorem lonelyAt_const_mul {v : Fin n → ℝ} {c : ℝ} {k : Fin n} {t : ℝ} :
    LonelyAt (fun j => c * v j) k t ↔ LonelyAt v k (c * t) := by
  unfold LonelyAt; simp only [sep_const_mul]

theorem circDist_abs_mul (x t : ℝ) : circDist (|x| * t) = circDist (x * t) := by
  rcases abs_choice x with h | h
  · rw [h]
  · rw [h, neg_mul, Flanks.circDist_neg]

open Classical in
noncomputable def diffSet (v : Fin n → ℝ) (k : Fin n) : Finset ℝ :=
  (Finset.univ.erase k).image (fun i => |v i - v k|)

open Classical in
theorem mem_diffSet {v : Fin n → ℝ} {k : Fin n} {d : ℝ} :
    d ∈ diffSet v k ↔ ∃ i : Fin n, i ≠ k ∧ |v i - v k| = d := by
  unfold diffSet; simp [Finset.mem_image, Finset.mem_erase]

open Classical in
theorem diffSet_pos {v : Fin n → ℝ} (hv : Function.Injective v) (k : Fin n) :
    ∀ d ∈ diffSet v k, 0 < d := by
  intro d hd
  obtain ⟨i, hi, rfl⟩ := mem_diffSet.mp hd
  exact abs_pos.mpr (sub_ne_zero.mpr fun h => hi (hv h))

open Classical in
theorem diffSet_nonempty (v : Fin n → ℝ) (k : Fin n) : (diffSet v k).Nonempty := by
  obtain ⟨i, hi⟩ := others_nonempty k
  exact ⟨|v i - v k|, mem_diffSet.mpr ⟨i, (Finset.mem_erase.mp hi).1, rfl⟩⟩

open Classical in
/-- **The subject's difference set has at most `n − 1` members.**  At `n = 8` this is `card ≤ 7`. -/
theorem diffSet_card_le {v : Fin n → ℝ} (k : Fin n) : (diffSet v k).card ≤ n - 1 := by
  refine le_trans Finset.card_image_le ?_
  simp [Finset.card_erase_of_mem]

open Classical in
theorem lonelyAt_iff_lonely_diffSet {v : Fin n → ℝ} {k : Fin n} {t : ℝ} :
    LonelyAt v k t ↔ Lonely n (diffSet v k) t := by
  unfold LonelyAt Lonely
  constructor
  · intro h d hd
    obtain ⟨i, hi, rfl⟩ := mem_diffSet.mp hd
    rw [circDist_abs_mul, ← sep_eq]
    exact h i hi
  · intro h i hi
    have hmem := h _ (mem_diffSet.mpr ⟨i, hi, rfl⟩)
    rwa [circDist_abs_mul, ← sep_eq] at hmem

/-! ### named instants on an arrangement -/

theorem lonelyAt_inv_of_not_dvd {v : Fin n → ℝ} {k : Fin n}
    (h : ∀ i : Fin n, i ≠ k → ∃ a : ℤ, v i - v k = (a : ℝ) ∧ ¬ ((n : ℤ) ∣ a)) :
    LonelyAt v k ((n : ℝ)⁻¹) := by
  intro i hi
  obtain ⟨a, ha, hdvd⟩ := h i hi
  rw [sep_eq, ha]
  have hn : 0 < n := by have := (Fact.out : 2 ≤ n); omega
  have hkey := ConstructionN.circDist_int_div (n := n) hn (c := a) hdvd
  rw [show (a : ℝ) * (n : ℝ)⁻¹ = (a : ℝ) / ((n : ℕ) : ℝ) by push_cast; ring]
  exact hkey

theorem exists_lonelyAt_of_not_dvd {v : Fin n → ℝ} {k : Fin n}
    (h : ∀ i : Fin n, i ≠ k → ∃ a : ℤ, v i - v k = (a : ℝ) ∧ ¬ ((n : ℤ) ∣ a)) :
    ∃ t : ℝ, 0 < t ∧ LonelyAt v k t :=
  ⟨(n : ℝ)⁻¹, inv_pos.mpr (n_pos (n := n)), lonelyAt_inv_of_not_dvd h⟩

theorem lonelyAt_named_instant {v : Fin n → ℝ} {k : Fin n} {c : ℤ} (hc : 0 < c) (j : ℕ)
    (h : ∀ i : Fin n, i ≠ k → ∃ a : ℤ, v i - v k = (a : ℝ) ∧
      c ≤ a * ((n : ℤ) * (j : ℤ) + 1) % ((n : ℤ) * c) ∧
      a * ((n : ℤ) * (j : ℤ) + 1) % ((n : ℤ) * c) ≤ (n : ℤ) * c - c) :
    LonelyAt v k (Flanks.flankOpening n (c : ℝ) j) := by
  intro i hi
  obtain ⟨a, ha, h1, h2⟩ := h i hi
  rw [sep_eq, ha]
  have hkey := (Flanks.clear_at_int_flank_iff_emod (n := n) hc j).mpr ⟨h1, h2⟩
  simpa using hkey

theorem exists_lonelyAt_of_named_instant {v : Fin n → ℝ} {k : Fin n} {c : ℤ} (hc : 0 < c) (j : ℕ)
    (h : ∀ i : Fin n, i ≠ k → ∃ a : ℤ, v i - v k = (a : ℝ) ∧
      c ≤ a * ((n : ℤ) * (j : ℤ) + 1) % ((n : ℤ) * c) ∧
      a * ((n : ℤ) * (j : ℤ) + 1) % ((n : ℤ) * c) ≤ (n : ℤ) * c - c) :
    ∃ t : ℝ, 0 < t ∧ LonelyAt v k t :=
  ⟨Flanks.flankOpening n (c : ℝ) j,
    Flanks.flankOpening_pos (by exact_mod_cast hc) j, lonelyAt_named_instant hc j h⟩

/-! ### the instants are read off the speeds -/

open Classical in
theorem exists_lonelyAt_iff_flank {v : Fin n → ℝ} (hv : Function.Injective v) (k : Fin n) :
    (∃ t : ℝ, 0 < t ∧ LonelyAt v k t) ↔
      ∃ e ∈ diffSet v k, ∃ j : ℕ, LonelyAt v k (Flanks.flankOpening n e j) := by
  have hiff := Flanks.lonely_iff_exists_flank (n := n) (diffSet_pos hv k) (diffSet_nonempty v k)
  constructor
  · rintro ⟨t, ht, hl⟩
    obtain ⟨e, he, j, hj⟩ := hiff.mp ⟨t, ht, lonelyAt_iff_lonely_diffSet.mp hl⟩
    exact ⟨e, he, j, lonelyAt_iff_lonely_diffSet.mpr hj⟩
  · rintro ⟨e, he, j, hj⟩
    obtain ⟨t, ht, hl⟩ := hiff.mpr ⟨e, he, j, lonelyAt_iff_lonely_diffSet.mp hj⟩
    exact ⟨t, ht, lonelyAt_iff_lonely_diffSet.mpr hl⟩

open Classical in
theorem exists_lonelyAt_iff_bounded {v : Fin n → ℝ} (hv : Function.Injective v) (k : Fin n)
    (hint : ∀ i : Fin n, i ≠ k → ∃ a : ℤ, |v i - v k| = (a : ℝ)) :
    (∃ t : ℝ, 0 < t ∧ LonelyAt v k t) ↔
      ∃ e ∈ diffSet v k, ∃ j : ℕ, (j : ℝ) < e ∧ LonelyAt v k (Flanks.flankOpening n e j) := by
  have hds : ∀ d ∈ diffSet v k, ∃ a : ℤ, d = (a : ℝ) := by
    intro d hd
    obtain ⟨i, hi, rfl⟩ := mem_diffSet.mp hd
    exact hint i hi
  have hiff := Flanks.lonely_iff_bounded_search (n := n) (diffSet_pos hv k)
    (diffSet_nonempty v k) hds
  constructor
  · rintro ⟨t, ht, hl⟩
    obtain ⟨e, he, j, hj, hlj⟩ := hiff.mp ⟨t, ht, lonelyAt_iff_lonely_diffSet.mp hl⟩
    exact ⟨e, he, j, hj, lonelyAt_iff_lonely_diffSet.mpr hlj⟩
  · rintro ⟨e, he, j, hj, hlj⟩
    obtain ⟨t, ht, hl⟩ := hiff.mpr ⟨e, he, j, hj, lonelyAt_iff_lonely_diffSet.mp hlj⟩
    exact ⟨t, ht, lonelyAt_iff_lonely_diffSet.mpr hl⟩

/-! ### the subject's two gaps

At `n = 8` the docstring reads "the eight runners cut the circle into eight gaps".  At order `n`
they cut it into `n`, the subject owns two, and the demand is `2/n` of a circle of `1`. -/

noncomputable def gapAhead (v : Fin n → ℝ) (k : Fin n) (t : ℝ) : ℝ :=
  (Finset.univ.erase k).inf' (others_nonempty k) (fun i => Int.fract (sep v k i t))

noncomputable def gapBehind (v : Fin n → ℝ) (k : Fin n) (t : ℝ) : ℝ :=
  1 - (Finset.univ.erase k).sup' (others_nonempty k) (fun i => Int.fract (sep v k i t))

theorem lonelyAt_iff_gaps {v : Fin n → ℝ} {k : Fin n} {t : ℝ} :
    LonelyAt v k t ↔ (n : ℝ)⁻¹ ≤ gapAhead v k t ∧ (n : ℝ)⁻¹ ≤ gapBehind v k t := by
  rw [lonelyAt_iff_neighbours]
  unfold gapAhead gapBehind
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, by linarith⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, by linarith⟩

theorem gapAhead_add_gapBehind_le_one (v : Fin n → ℝ) (k : Fin n) (t : ℝ) :
    gapAhead v k t + gapBehind v k t ≤ 1 := by
  unfold gapAhead gapBehind
  obtain ⟨i, hi⟩ := others_nonempty k
  have h : (Finset.univ.erase k).inf' (others_nonempty k) (fun i => Int.fract (sep v k i t))
      ≤ (Finset.univ.erase k).sup' (others_nonempty k) (fun i => Int.fract (sep v k i t)) :=
    le_trans (Finset.inf'_le (fun i => Int.fract (sep v k i t)) hi)
      (Finset.le_sup' (fun i => Int.fract (sep v k i t)) hi)
  linarith

theorem gapAhead_nonneg (v : Fin n → ℝ) (k : Fin n) (t : ℝ) : 0 ≤ gapAhead v k t := by
  unfold gapAhead; exact Finset.le_inf' _ _ (fun i _ => Int.fract_nonneg _)

theorem gapBehind_nonneg (v : Fin n → ℝ) (k : Fin n) (t : ℝ) : 0 ≤ gapBehind v k t := by
  unfold gapBehind
  have : (Finset.univ.erase k).sup' (others_nonempty k) (fun i => Int.fract (sep v k i t)) ≤ 1 :=
    Finset.sup'_le _ _ (fun i _ => le_of_lt (Int.fract_lt_one _))
  linarith

/-! ## 2. the target layer  (`Spec/Target.lean`) -/

def ExistenceAtN (n : ℕ) : Prop :=
  ∀ ds : Finset ℝ, (∀ d ∈ ds, 0 < d) → ds.card ≤ n - 1 → ∃ s : ℝ, 0 < s ∧ Lonely n ds s

def ExistenceAtN_cascade (n : ℕ) : Prop :=
  ∀ ds : Finset ℝ, (∀ d ∈ ds, 0 < d) → ds.card ≤ n - 1 → ds.Nonempty →
    ∀ m ∈ ds, (∀ d ∈ ds, m ≤ d) →
      ∃ N : ℕ, move n ds ((move n ds)^[N] (1 / (n * m))) = (move n ds)^[N] (1 / (n * m))

theorem target_forms_agree : ExistenceAtN n ↔ ExistenceAtN_cascade n := by
  constructor
  · intro h ds hpos hcard hne m hm hmin
    exact ((lonely_iff_run_ends (n := n) hpos hm).1).mp (h ds hpos hcard)
  · intro h ds hpos hcard
    rcases Finset.eq_empty_or_nonempty ds with rfl | hne
    · exact ⟨1, by norm_num, by intro d hd; simp at hd⟩
    · obtain ⟨m, hm, hmin⟩ := ds.exists_min_image id hne
      exact ((lonely_iff_run_ends (n := n) hpos hm).1).mpr
        (h ds hpos hcard hne m hm (fun d hd => hmin d hd))

def ExistenceAtN_flank (n : ℕ) : Prop :=
  ∀ ds : Finset ℝ, (∀ d ∈ ds, 0 < d) → ds.card ≤ n - 1 → ds.Nonempty →
    ∃ e ∈ ds, ∃ k : ℕ, Lonely n ds (flankOpening n e k)

theorem target_flank_agrees (h : ExistenceAtN_flank n) : ExistenceAtN n := by
  intro ds hpos hcard
  rcases Finset.eq_empty_or_nonempty ds with rfl | hne
  · exact ⟨1, by norm_num, by intro d hd; simp at hd⟩
  · obtain ⟨e, he, k, hk⟩ := h ds hpos hcard hne
    exact ⟨flankOpening n e k, flankOpening_pos (hpos e he) k, hk⟩

theorem target_flank_iff : ExistenceAtN n ↔ ExistenceAtN_flank n := by
  constructor
  · intro h ds hpos hcard hne
    exact (Flanks.lonely_iff_exists_flank (n := n) hpos hne).mp (h ds hpos hcard)
  · exact target_flank_agrees

def CascadeCapped (n : ℕ) : Prop :=
  ∀ ds : Finset ℝ, (∀ d ∈ ds, 0 < d) → ds.card ≤ n - 1 → ∀ m ∈ ds, (∀ d ∈ ds, m ≤ d) →
    ∃ U : ℝ, ∀ N : ℕ, (move n ds)^[N] (1 / (n * m)) ≤ U

theorem existence_of_capped (h : CascadeCapped n) : ExistenceAtN n := by
  rw [target_forms_agree]
  intro ds hpos hcard hne m hm hmin
  obtain ⟨U, hU⟩ := h ds hpos hcard m hm hmin
  have hn : (0 : ℝ) < n := n_pos (n := n)
  have hb : (0 : ℝ) < 1 / (n * m) := by have := hpos m hm; positivity
  exact ChainBounds.exists_fixed_of_capped (n := n) hpos hb hU

theorem capped_of_existence (h : ExistenceAtN n) : CascadeCapped n := by
  intro ds hpos hcard m hm hmin
  rw [target_forms_agree] at h
  obtain ⟨N, hfix⟩ := h ds hpos hcard ⟨m, hm⟩ m hm hmin
  refine ⟨(move n ds)^[N] (1 / (n * m)), fun K => ?_⟩
  rcases le_or_gt K N with hKN | hKN
  · have e : (move n ds)^[N] (1 / (n * m))
        = (move n ds)^[N - K] ((move n ds)^[K] (1 / (n * m))) := by
      rw [← Function.iterate_add_apply]; congr 1; omega
    rw [e]; exact iterate_ge (n := n) ds _ _
  · obtain ⟨i, rfl⟩ : ∃ i, K = N + i := ⟨K - N, by omega⟩
    exact le_of_eq (FourDifferences.iterate_stable (n := n) hfix i)

def FiniteActiveMembership (n : ℕ) : Prop :=
  ∀ ds : Finset ℝ, (∀ d ∈ ds, 0 < d) → ds.card ≤ n - 1 → ∀ m ∈ ds, (∀ d ∈ ds, m ≤ d) →
    ∀ d ∈ ds, {j : ℕ | inWay n d ((move n ds)^[j] (1 / (n * m)))}.Finite

theorem cascade_of_FAM (h : FiniteActiveMembership n) : ExistenceAtN_cascade n := by
  intro ds hpos hcard hne m hm hmin
  by_contra hno
  push Not at hno
  have hact : ∀ j : ℕ, ∃ d ∈ ds, inWay n d ((move n ds)^[j] (1 / (n * m))) := by
    intro j
    rcases move_eq_self_or_opening (n := n) ds ((move n ds)^[j] (1 / (n * m))) with hfix | ⟨x, hx, hw, -⟩
    · exact absurd hfix (hno j)
    · exact ⟨x, hx, hw⟩
  have hfin : (⋃ d ∈ ds, {j : ℕ | inWay n d ((move n ds)^[j] (1 / (n * m)))}).Finite :=
    Set.Finite.biUnion ds.finite_toSet (fun d hd => h ds hpos hcard m hm hmin d hd)
  have huniv : (Set.univ : Set ℕ) ⊆ ⋃ d ∈ ds, {j : ℕ | inWay n d ((move n ds)^[j] (1 / (n * m)))} := by
    intro j _
    obtain ⟨d, hd, hw⟩ := hact j
    exact Set.mem_biUnion hd hw
  exact Set.infinite_univ (hfin.subset huniv)

theorem FAM_of_existence (h : ExistenceAtN n) : FiniteActiveMembership n := by
  intro ds hpos hcard m hm hmin d hd
  rw [target_forms_agree] at h
  obtain ⟨N, hfix⟩ := h ds hpos hcard ⟨m, hm⟩ m hm hmin
  refine Set.Finite.subset (Set.finite_Iio N) ?_
  intro j hj
  by_contra hjN
  simp only [Set.mem_Iio, not_lt] at hjN
  obtain ⟨i, rfl⟩ : ∃ i, j = N + i := ⟨j - N, by omega⟩
  rw [Set.mem_setOf_eq, FourDifferences.iterate_stable (n := n) hfix i] at hj
  exact absurd (lonely_of_fixed hpos hfix d hd) (not_le.mpr hj)

theorem FAM_iff_existence : FiniteActiveMembership n ↔ ExistenceAtN n :=
  ⟨fun h => target_forms_agree.mpr (cascade_of_FAM h), FAM_of_existence⟩

open Classical in
def ThreeLargestFlanks (n : ℕ) : Prop :=
  ∀ ds : Finset ℝ, (∀ d ∈ ds, 0 < d) → ds.card ≤ n - 1 → ds.Nonempty →
    (∀ d ∈ ds, ∃ a : ℤ, d = (a : ℝ)) →
      ∃ e ∈ ds, (ds.filter (fun d => e < d)).card ≤ 2 ∧
        ∃ k : ℕ, Lonely n ds (flankOpening n e k)

open Classical in
theorem exists_lonely_of_threeLargest (h : ThreeLargestFlanks n) {ds : Finset ℝ}
    (hpos : ∀ d ∈ ds, 0 < d) (hcard : ds.card ≤ n - 1)
    (hint : ∀ d ∈ ds, ∃ a : ℤ, d = (a : ℝ)) :
    ∃ s, 0 < s ∧ Lonely n ds s := by
  rcases Finset.eq_empty_or_nonempty ds with rfl | hne
  · exact ⟨1, by norm_num, by intro d hd; simp at hd⟩
  · obtain ⟨e, he, -, k, hk⟩ := h ds hpos hcard hne hint
    exact ⟨flankOpening n e k, flankOpening_pos (hpos e he) k, hk⟩

def ExistenceAtN_congruence (n : ℕ) : Prop :=
  ∀ ds : Finset ℝ, (∀ d ∈ ds, 0 < d) → ds.card ≤ n - 1 → ds.Nonempty →
    (∀ d ∈ ds, ∃ a : ℤ, d = (a : ℝ)) →
      ∃ b : ℤ, 0 < b ∧ (b : ℝ) ∈ ds ∧ ∃ k : ℕ, (k : ℤ) < b ∧
        ∀ a : ℤ, (a : ℝ) ∈ ds →
          b ≤ a * ((n : ℤ) * (k : ℤ) + 1) % ((n : ℤ) * b)
          ∧ a * ((n : ℤ) * (k : ℤ) + 1) % ((n : ℤ) * b) ≤ (n : ℤ) * b - b

theorem congruence_of_existence (h : ExistenceAtN n) : ExistenceAtN_congruence n := by
  intro ds hpos hcard hne hint
  exact (Flanks.lonely_iff_emod_search (n := n) hpos hne hint).mp (h ds hpos hcard)

theorem exists_lonely_of_congruence (h : ExistenceAtN_congruence n) {ds : Finset ℝ}
    (hpos : ∀ d ∈ ds, 0 < d) (hcard : ds.card ≤ n - 1) (hne : ds.Nonempty)
    (hint : ∀ d ∈ ds, ∃ a : ℤ, d = (a : ℝ)) :
    ∃ s, 0 < s ∧ Lonely n ds s :=
  (Flanks.lonely_iff_emod_search (n := n) hpos hne hint).mpr (h ds hpos hcard hne hint)

/-! ### the conjecture itself -/

def LonelyRunnerAtN (n : ℕ) : Prop :=
  ∀ v : Fin n → ℝ, Function.Injective v → ∀ k : Fin n,
    ∃ t : ℝ, 0 < t ∧ ∀ i : Fin n, i ≠ k → (n : ℝ)⁻¹ ≤ circDist (v i * t - v k * t)

theorem lonelyRunnerAtN_of_existence (h : ExistenceAtN n) : LonelyRunnerAtN n := by
  intro v hinj k
  classical
  obtain ⟨s, hs, hl⟩ := h (diffSet v k) (diffSet_pos hinj k) (diffSet_card_le k)
  refine ⟨s, hs, fun i hik => ?_⟩
  have := hl _ (mem_diffSet.mpr ⟨i, hik, rfl⟩)
  rwa [circDist_abs_mul, ← sep_eq] at this

/-! ### the excess of the difference-set form over the conjecture

At `n = 8` the excess is `card ≤ 3` and `exists_lonely_of_card_le_three` settles it.  The
counting behind that number generalises: a value `d` occurs as `|v i − v k|` for at most two
runners, so a difference set realised by an arrangement has `2·card ≥ n − 1`.  The excess at
order `n` is therefore `card < ⌈(n−1)/2⌉`, which grows with `n` while the available
termination results do not.  See the findings block at the foot of this file. -/

theorem exists_lonely_of_card_le_three {ds : Finset ℝ} (hn4 : 4 ≤ n)
    (hpos : ∀ d ∈ ds, 0 < d) (hcard : ds.card ≤ 3) : ∃ s, 0 < s ∧ Lonely n ds s := by
  classical
  rcases Finset.eq_empty_or_nonempty ds with rfl | hne
  · exact ⟨1, by norm_num, by intro d hd; simp at hd⟩
  · obtain ⟨a, ha, hmin⟩ := ds.exists_min_image id hne
    have ha0 := hpos a ha
    have hn : (0 : ℝ) < n := n_pos (n := n)
    have hb : (0 : ℝ) < 1 / (n * a) := by positivity
    have hfix := FewDifferences.three_diffs_stop_within_three_moves (n := n) hn4
      hpos hcard ha (fun d hd => hmin d hd)
    exact ⟨(move n ds)^[3] (1 / (n * a)),
      lt_of_lt_of_le hb (iterate_ge (n := n) ds _ 3), lonely_of_fixed hpos hfix⟩

theorem exists_lonely_of_card_le_four {ds : Finset ℝ} (hn6 : 6 ≤ n)
    (hpos : ∀ d ∈ ds, 0 < d) (hcard : ds.card ≤ 4) : ∃ s, 0 < s ∧ Lonely n ds s := by
  classical
  rcases Finset.eq_empty_or_nonempty ds with rfl | hne
  · exact ⟨1, by norm_num, by intro d hd; simp at hd⟩
  · obtain ⟨a, ha, hmin⟩ := ds.exists_min_image id hne
    have ha0 := hpos a ha
    have hn : (0 : ℝ) < n := n_pos (n := n)
    have hb : (0 : ℝ) < 1 / (n * a) := by positivity
    have hfix := FourDifferencesSix.four_diffs_stop_ge_six (n := n) hn6
      hpos hcard ha (fun d hd => hmin d hd)
    exact ⟨(move n ds)^[7] (1 / (n * a)),
      lt_of_lt_of_le hb (iterate_ge (n := n) ds _ 7), lonely_of_fixed hpos hfix⟩

def ExistenceOnArrangements (n : ℕ) : Prop :=
  ∀ v : Fin n → ℝ, Function.Injective v → ∀ k : Fin n,
    ∃ t : ℝ, 0 < t ∧ LonelyAt v k t

theorem lonelyRunnerAtN_iff_arrangement :
    LonelyRunnerAtN n ↔
      ∀ v : Fin n → ℝ, Function.Injective v → ∀ k : Fin n,
        ∃ t : ℝ, 0 < t ∧ LonelyAt v k t := Iff.rfl

theorem lonelyRunnerAtN_iff_existenceOnArrangements :
    LonelyRunnerAtN n ↔ ExistenceOnArrangements n := Iff.rfl

theorem lonelyRunnerAtN_of_arrangement
    (H : ∀ v : Fin n → ℝ, Function.Injective v → ∀ k : Fin n,
      ∃ t : ℝ, 0 < t ∧ LonelyAt v k t) :
    LonelyRunnerAtN n := H

/-! ## 3. the door layer  (`Spec/Doors.lean`) -/

open Classical in
noncomputable def leastDisp (v : Fin n → ℝ) (k : Fin n) : ℝ :=
  (diffSet v k).min' (diffSet_nonempty v k)

open Classical in
theorem leastDisp_mem (v : Fin n → ℝ) (k : Fin n) : leastDisp v k ∈ diffSet v k :=
  (diffSet v k).min'_mem _

open Classical in
theorem leastDisp_le (v : Fin n → ℝ) (k : Fin n) : ∀ d ∈ diffSet v k, leastDisp v k ≤ d :=
  fun d hd => (diffSet v k).min'_le d hd

open Classical in
theorem leastDisp_pos {v : Fin n → ℝ} (hv : Function.Injective v) (k : Fin n) :
    0 < leastDisp v k := diffSet_pos hv k _ (leastDisp_mem v k)

open Classical in
noncomputable def firstReading (v : Fin n → ℝ) (k : Fin n) : ℝ := 1 / (n * leastDisp v k)

open Classical in
theorem firstReading_pos {v : Fin n → ℝ} (hv : Function.Injective v) (k : Fin n) :
    0 < firstReading v k := by
  unfold firstReading
  exact div_pos one_pos (mul_pos (n_pos (n := n)) (leastDisp_pos hv k))

def LonelyForSubject (v : Fin n → ℝ) (k : Fin n) : Prop := ∃ t : ℝ, 0 < t ∧ LonelyAt v k t

theorem existenceOnArrangements_iff_subjects :
    ExistenceOnArrangements n ↔ ∀ v : Fin n → ℝ, Function.Injective v → ∀ k : Fin n,
      LonelyForSubject v k := Iff.rfl

open Classical in
theorem lonelyForSubject_iff_diffSet {v : Fin n → ℝ} {k : Fin n} :
    LonelyForSubject v k ↔ ∃ t : ℝ, 0 < t ∧ Lonely n (diffSet v k) t := by
  unfold LonelyForSubject
  exact exists_congr fun t => and_congr_right fun _ => lonelyAt_iff_lonely_diffSet

open Classical in
def DoorFlank (v : Fin n → ℝ) (k : Fin n) : Prop :=
  ∃ i : Fin n, i ≠ k ∧ ∃ j : ℕ, LonelyAt v k (flankOpening n |v i - v k| j)

open Classical in
def DoorArrives (v : Fin n → ℝ) (k : Fin n) : Prop :=
  ∃ N : ℕ, move n (diffSet v k) ((move n (diffSet v k))^[N] (firstReading v k))
    = (move n (diffSet v k))^[N] (firstReading v k)

open Classical in
def DoorCapped (v : Fin n → ℝ) (k : Fin n) : Prop :=
  ∃ U : ℝ, ∀ N : ℕ, (move n (diffSet v k))^[N] (firstReading v k) ≤ U

open Classical in
def DoorFAM (v : Fin n → ℝ) (k : Fin n) : Prop :=
  ∀ i : Fin n, i ≠ k →
    {j : ℕ | inWay n |v i - v k| ((move n (diffSet v k))^[j] (firstReading v k))}.Finite

open Classical in
theorem doorFlank_iff {v : Fin n → ℝ} (hv : Function.Injective v) (k : Fin n) :
    DoorFlank v k ↔ LonelyForSubject v k := by
  constructor
  · rintro ⟨i, hi, j, hj⟩
    refine ⟨flankOpening n |v i - v k| j, flankOpening_pos ?_ j, hj⟩
    exact abs_pos.mpr (sub_ne_zero.mpr fun h => hi (hv h))
  · intro h
    obtain ⟨e, he, j, hj⟩ := (exists_lonelyAt_iff_flank hv k).mp h
    obtain ⟨i, hi, rfl⟩ := mem_diffSet.mp he
    exact ⟨i, hi, j, hj⟩

open Classical in
theorem doorArrives_iff {v : Fin n → ℝ} (hv : Function.Injective v) (k : Fin n) :
    DoorArrives v k ↔ LonelyForSubject v k := by
  rw [lonelyForSubject_iff_diffSet]
  exact ((lonely_iff_run_ends (n := n) (diffSet_pos hv k) (leastDisp_mem v k)).1).symm

open Classical in
theorem doorCapped_iff {v : Fin n → ℝ} (hv : Function.Injective v) (k : Fin n) :
    DoorCapped v k ↔ LonelyForSubject v k := by
  rw [← doorArrives_iff hv k]
  constructor
  · rintro ⟨U, hU⟩
    exact ChainBounds.exists_fixed_of_capped (n := n) (diffSet_pos hv k) (firstReading_pos hv k) hU
  · rintro ⟨N, hfix⟩
    refine ⟨(move n (diffSet v k))^[N] (firstReading v k), fun K => ?_⟩
    rcases le_or_gt K N with hKN | hKN
    · have e : (move n (diffSet v k))^[N] (firstReading v k)
          = (move n (diffSet v k))^[N - K] ((move n (diffSet v k))^[K] (firstReading v k)) := by
        rw [← Function.iterate_add_apply]; congr 1; omega
      rw [e]; exact iterate_ge (n := n) (diffSet v k) _ _
    · obtain ⟨i, rfl⟩ : ∃ i, K = N + i := ⟨K - N, by omega⟩
      exact le_of_eq (FourDifferences.iterate_stable (n := n) hfix i)

open Classical in
theorem doorFAM_iff {v : Fin n → ℝ} (hv : Function.Injective v) (k : Fin n) :
    DoorFAM v k ↔ LonelyForSubject v k := by
  classical
  rw [← doorArrives_iff hv k]
  constructor
  · intro h
    by_contra hno
    unfold DoorArrives at hno
    push Not at hno
    have hact : ∀ j : ℕ, ∃ d ∈ diffSet v k,
        inWay n d ((move n (diffSet v k))^[j] (firstReading v k)) := by
      intro j
      rcases move_eq_self_or_opening (n := n) (diffSet v k)
        ((move n (diffSet v k))^[j] (firstReading v k)) with hfix | ⟨x, hx, hw, -⟩
      · exact absurd hfix (hno j)
      · exact ⟨x, hx, hw⟩
    have hfin : (⋃ d ∈ diffSet v k,
        {j : ℕ | inWay n d ((move n (diffSet v k))^[j] (firstReading v k))}).Finite := by
      refine Set.Finite.biUnion (diffSet v k).finite_toSet (fun d hd => ?_)
      obtain ⟨i, hi, rfl⟩ := mem_diffSet.mp hd
      exact h i hi
    have huniv : (Set.univ : Set ℕ) ⊆ ⋃ d ∈ diffSet v k,
        {j : ℕ | inWay n d ((move n (diffSet v k))^[j] (firstReading v k))} := by
      intro j _
      obtain ⟨d, hd, hw⟩ := hact j
      exact Set.mem_biUnion hd hw
    exact Set.infinite_univ (hfin.subset huniv)
  · rintro ⟨N, hfix⟩ i hi
    refine Set.Finite.subset (Set.finite_Iio N) ?_
    intro j hj
    by_contra hjN
    simp only [Set.mem_Iio, not_lt] at hjN
    obtain ⟨c, rfl⟩ : ∃ c, j = N + c := ⟨j - N, by omega⟩
    rw [Set.mem_setOf_eq, FourDifferences.iterate_stable (n := n) hfix c] at hj
    have hmem : |v i - v k| ∈ diffSet v k := mem_diffSet.mpr ⟨i, hi, rfl⟩
    exact absurd (lonely_of_fixed (diffSet_pos hv k) hfix _ hmem) (not_le.mpr hj)

/-! ### door 5 -/

open Classical in
def DoorThreeLargest (v : Fin n → ℝ) (k : Fin n) : Prop :=
  ∃ i : Fin n, i ≠ k ∧
    ((diffSet v k).filter (fun d => |v i - v k| < d)).card ≤ 2 ∧
    ∃ j : ℕ, LonelyAt v k (flankOpening n |v i - v k| j)

open Classical in
theorem lonelyForSubject_of_threeLargest {v : Fin n → ℝ} (hv : Function.Injective v) (k : Fin n)
    (h : DoorThreeLargest v k) : LonelyForSubject v k := by
  obtain ⟨i, hi, -, j, hj⟩ := h
  exact (doorFlank_iff hv k).mp ⟨i, hi, j, hj⟩

/-! ### the doors together -/

open Classical in
theorem doors_agree {v : Fin n → ℝ} (hv : Function.Injective v) (k : Fin n) :
    (DoorFlank v k ↔ LonelyForSubject v k) ∧
    (DoorArrives v k ↔ LonelyForSubject v k) ∧
    (DoorCapped v k ↔ LonelyForSubject v k) ∧
    (DoorFAM v k ↔ LonelyForSubject v k) :=
  ⟨doorFlank_iff hv k, doorArrives_iff hv k, doorCapped_iff hv k, doorFAM_iff hv k⟩

open Classical in
theorem lonelyRunnerAtN_of_doorFlank
    (h : ∀ v : Fin n → ℝ, Function.Injective v → ∀ k : Fin n, DoorFlank v k) :
    LonelyRunnerAtN n := by
  intro v hv k
  obtain ⟨t, ht, hl⟩ := (doorFlank_iff hv k).mp (h v hv k)
  exact ⟨t, ht, fun i hi => hl i hi⟩

open Classical in
theorem lonelyRunnerAtN_of_doorArrives
    (h : ∀ v : Fin n → ℝ, Function.Injective v → ∀ k : Fin n, DoorArrives v k) :
    LonelyRunnerAtN n := by
  intro v hv k
  obtain ⟨t, ht, hl⟩ := (doorArrives_iff hv k).mp (h v hv k)
  exact ⟨t, ht, fun i hi => hl i hi⟩

open Classical in
theorem lonelyRunnerAtN_of_doorCapped
    (h : ∀ v : Fin n → ℝ, Function.Injective v → ∀ k : Fin n, DoorCapped v k) :
    LonelyRunnerAtN n := by
  intro v hv k
  obtain ⟨t, ht, hl⟩ := (doorCapped_iff hv k).mp (h v hv k)
  exact ⟨t, ht, fun i hi => hl i hi⟩

open Classical in
theorem lonelyRunnerAtN_of_doorFAM
    (h : ∀ v : Fin n → ℝ, Function.Injective v → ∀ k : Fin n, DoorFAM v k) :
    LonelyRunnerAtN n := by
  intro v hv k
  obtain ⟨t, ht, hl⟩ := (doorFAM_iff hv k).mp (h v hv k)
  exact ⟨t, ht, fun i hi => hl i hi⟩

/-! ### the coupling across subjects

At `n = 8` the docstring counts **28 pairs**.  At order `n` it is `n(n−1)/2`, and the handshake
identity below is stated so that no count appears in it at all. -/

open scoped Classical in
noncomputable def blockDegree (v : Fin n → ℝ) (t : ℝ) (k : Fin n) : ℕ :=
  (Finset.univ.filter (fun i : Fin n => i ≠ k ∧ InWay v k i t)).card

open scoped Classical in
theorem lonelyAt_iff_blockDegree_zero {v : Fin n → ℝ} {k : Fin n} {t : ℝ} :
    LonelyAt v k t ↔ blockDegree v t k = 0 := by
  rw [lonelyAt_iff_no_inWay, blockDegree, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  constructor
  · intro h i _ hc; exact h i hc.1 hc.2
  · intro h i hi hw; exact h (Finset.mem_univ i) ⟨hi, hw⟩

open scoped Classical in
theorem blockDegree_symm_pairs {v : Fin n → ℝ} {t : ℝ} {i k : Fin n} :
    (i ≠ k ∧ InWay v k i t) ↔ (k ≠ i ∧ InWay v i k t) :=
  ⟨fun ⟨h1, h2⟩ => ⟨h1.symm, inWay_comm.mp h2⟩, fun ⟨h1, h2⟩ => ⟨h1.symm, inWay_comm.mp h2⟩⟩

open scoped Classical in
theorem sum_blockDegree (v : Fin n → ℝ) (t : ℝ) :
    ∑ k : Fin n, blockDegree v t k
      = (Finset.univ.filter (fun p : Fin n × Fin n => p.2 ≠ p.1 ∧ InWay v p.1 p.2 t)).card := by
  simp only [blockDegree, Finset.card_filter]
  rw [Fintype.sum_prod_type]

open scoped Classical in
theorem existenceOnArrangements_iff_isolated :
    ExistenceOnArrangements n ↔
      ∀ v : Fin n → ℝ, Function.Injective v → ∀ k : Fin n,
        ∃ t : ℝ, 0 < t ∧ blockDegree v t k = 0 := by
  unfold ExistenceOnArrangements
  exact forall_congr' fun v => forall_congr' fun _ => forall_congr' fun k =>
    exists_congr fun t => and_congr_right fun _ => lonelyAt_iff_blockDegree_zero

/-! ### the two refuted doors, carried across

Both are `[REFUTED]` at `n = 8`.  They are ported because the two implications attached to them
are true and vacuous there, and the question is whether the implications survive at general `n` —
not whether the refutations do. -/

open Classical in
def DoorFirstLap (v : Fin n → ℝ) (k : Fin n) : Prop :=
  ∀ N : ℕ, (move n (diffSet v k))^[N] (firstReading v k) ≤ 1 / leastDisp v k

open Classical in
theorem doorCapped_of_doorFirstLap {v : Fin n → ℝ} {k : Fin n} (h : DoorFirstLap v k) :
    DoorCapped v k := ⟨1 / leastDisp v k, h⟩

open Classical in
theorem lonelyRunnerAtN_of_doorFirstLap
    (h : ∀ v : Fin n → ℝ, Function.Injective v → ∀ k : Fin n, DoorFirstLap v k) :
    LonelyRunnerAtN n :=
  lonelyRunnerAtN_of_doorCapped (fun v hv k => doorCapped_of_doorFirstLap (h v hv k))

open Classical in
def DoorLargestFlank (v : Fin n → ℝ) (k : Fin n) : Prop :=
  ∃ i : Fin n, i ≠ k ∧
    (∀ i' : Fin n, i' ≠ k → |v i' - v k| ≤ |v i - v k|) ∧
    ∃ j : ℕ, LonelyAt v k (flankOpening n |v i - v k| j)

open Classical in
theorem doorThreeLargest_of_doorLargestFlank {v : Fin n → ℝ} (hv : Function.Injective v)
    {k : Fin n} (h : DoorLargestFlank v k) : DoorThreeLargest v k := by
  classical
  obtain ⟨i, hi, hmax, j, hj⟩ := h
  refine ⟨i, hi, ?_, j, hj⟩
  have : ((diffSet v k).filter (fun d => |v i - v k| < d)) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro d hd
    obtain ⟨i', hi', rfl⟩ := mem_diffSet.mp hd
    exact not_lt.mpr (hmax i' hi')
  rw [this]; simp

end LRC.SpecN
