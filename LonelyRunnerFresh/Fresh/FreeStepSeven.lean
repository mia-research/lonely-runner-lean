import Mathlib
import Fresh.Framework
import Fresh.Localisation
import Fresh.Grid
import Fresh.PathLaws
import Fresh.RealCase
import Fresh.Admissible
import Fresh.AdmissibleFlank

/-!
# One free reading and the block split, on real speeds

Written 2026-10-25.  New file.  Real forms of the old `OneFreeEightN.lean` (`lonely_eight_of_one_free`) and `BlockSplitEightN.lean` (`lonely_eight_of_block_split`).
`exists_clear_step` (a step of fractional size cannot stay within 1/8 of an integer for every k) is proved here from `distInt` alone.
`SevenClear6` is order seven on real speeds in `distInt` form; it is proved in `Fresh.NativeOrders.sevenClear6_proved` (2026-10-25; first written as a hypothesis); it is the statement of `LRC.OrderSevenN.existenceAtN_seven` (nested repo
`LonelyRunner`, `Spec/RealSevenN.lean`, axioms `[propext, Classical.choice, Quot.sound]`, checked 2026-10-25; owner ruling 2026-09-25: orders 3 to 7 are native and may be used).
* `OneFreeClass`: a real unit `g > 0`, a disparity `x` that is not a whole multiple of `g`, every other disparity a natural multiple of `g`.  Isolation at `t7 + k/g`.
* `BlockSplitClass`: reals `0 < m`, `28 m ≤ g`; a nonempty core of disparities at most `m` (arbitrary reals), a nonempty block of disparities each a natural multiple of `g`.
Commensurability is required only inside the block (and, for one-free, among the six).  Grade [L] (the hypothesis `SevenClear6` is discharged by `NativeOrders`).
-/

open Classical

namespace Fresh.FreeStep

open Fresh Fresh.Admissible Fresh.AdmissibleFlank

/-- Order seven on real speeds: at most six positive reals have an instant at which each is `1/7`-clear. -/
-- STANDING: PROVED (`Fresh.NativeOrders.sevenClear6_proved`, from the ported `LRC.OrderSevenN.existenceAtN_seven`; tag changed from IMPORTED 2026-10-25)
def SevenClear6 : Prop :=
  ∀ ds : Finset ℝ, (∀ d ∈ ds, 0 < d) → ds.card ≤ 6 → ∃ τ : ℝ, 0 < τ ∧ ∀ d ∈ ds, (1 / 7 : ℝ) ≤ distInt (d * τ)

theorem distInt_pos_of_frac {f : ℝ} (h0 : 0 < f) (h1 : f < 1) : 0 < distInt f := by
  unfold distInt
  rw [abs_pos]
  intro h
  have hz : f = (round f : ℝ) := by linarith
  have a1 : (0 : ℝ) < (round f : ℝ) := by rw [← hz]; exact h0
  have a2 : (round f : ℝ) < 1 := by rw [← hz]; exact h1
  have b1 : 0 < round f := by exact_mod_cast a1
  have b2 : round f < 1 := by exact_mod_cast a2
  omega

theorem exists_far_multiple {f : ℝ} (h0 : 0 < f) (h1 : f < 1) : ∃ j : ℕ, (1 / 4 : ℝ) ≤ distInt ((j : ℝ) * f) := by
  have hε := distInt_pos_of_frac h0 h1
  set ε : ℝ := distInt f with hεdef
  by_cases hbig : (1 / 4 : ℝ) ≤ ε
  · exact ⟨1, by simpa using hbig⟩
  push_neg at hbig
  set j : ℕ := ⌈1 / (4 * ε)⌉₊ with hj
  have hj1 : 1 / (4 * ε) ≤ (j : ℝ) := Nat.le_ceil _
  have hj2 : (j : ℝ) < 1 / (4 * ε) + 1 := Nat.ceil_lt_add_one (by positivity)
  have hjε1 : (1 / 4 : ℝ) ≤ j * ε := by
    rw [div_le_iff₀ (by positivity)] at hj1
    nlinarith
  have hjε2 : (j : ℝ) * ε < 1 / 2 := by
    have : (j : ℝ) * ε < (1 / (4 * ε) + 1) * ε := mul_lt_mul_of_pos_right hj2 hε
    have e : (1 / (4 * ε) + 1) * ε = 1 / 4 + ε := by field_simp
    linarith
  refine ⟨j, ?_⟩
  set s : ℝ := f - round f with hs
  have hsabs : |s| = ε := rfl
  have hform : (j : ℝ) * f = (j : ℝ) * s + (((j : ℤ) * round f : ℤ) : ℝ) := by
    rw [hs]; push_cast; ring
  rw [hform, distInt_add_int]
  have habs : |(j : ℝ) * s| = j * ε := by rw [abs_mul, hsabs, abs_of_nonneg (by positivity)]
  rw [Fresh.RealCase.distInt_of_abs_le (by rw [habs]; linarith), habs]
  exact hjε1

theorem exists_clear_step {f c : ℝ} (h0 : 0 < f) (h1 : f < 1) : ∃ k : ℕ, (1 / 8 : ℝ) ≤ distInt (c + (k : ℝ) * f) := by
  by_contra hall
  push_neg at hall
  obtain ⟨j, hj⟩ := exists_far_multiple h0 h1
  have hA := hall 0
  have hB := hall j
  simp only [Nat.cast_zero, zero_mul, add_zero] at hA
  have hz := Fresh.Localisation.distInt_le ((j : ℝ) * f) (round (c + (j : ℝ) * f) - round c)
  have h2 : |(j : ℝ) * f - ((round (c + (j : ℝ) * f) - round c : ℤ) : ℝ)| ≤
      |c + (j : ℝ) * f - (round (c + (j : ℝ) * f) : ℝ)| + |c - (round c : ℝ)| := by
    have := abs_sub ((c + (j : ℝ) * f) - (round (c + (j : ℝ) * f) : ℝ)) (c - (round c : ℝ))
    have e : (j : ℝ) * f - ((round (c + (j : ℝ) * f) - round c : ℤ) : ℝ) =
        ((c + (j : ℝ) * f) - (round (c + (j : ℝ) * f) : ℝ)) - (c - (round c : ℝ)) := by push_cast; ring
    rw [e]; exact this
  have h3 : |c + (j : ℝ) * f - (round (c + (j : ℝ) * f) : ℝ)| = distInt (c + (j : ℝ) * f) := rfl
  have h4 : |c - (round c : ℝ)| = distInt c := rfl
  linarith

theorem disp_card_le_seven (v : Fin 8 → ℝ) (k : Fin 8) : (disparitySet v k).card ≤ 7 := by
  unfold disparitySet
  calc _ ≤ (Finset.univ.erase k).card := Finset.card_image_le
    _ = 7 := by simp

-- STANDING: DEFINITION
def OneFreeClass (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  ∃ g : ℝ, 0 < g ∧ ∃ x ∈ disparitySet v k, (∀ d ∈ disparitySet v k, d ≠ x → ∃ n : ℕ, d = (n : ℝ) * g) ∧
    ∀ z : ℤ, x ≠ (z : ℝ) * g

theorem oneFree_isolation (hSeven : SevenClear6) {v : Fin 8 → ℝ} (hinj : Function.Injective v) {k : Fin 8}
    (h : OneFreeClass v k) : Isolation v k := by
  obtain ⟨g, hg, x, hx, hmult, hnot⟩ := h
  set D' := (disparitySet v k).erase x with hD'
  have hcard : D'.card ≤ 6 := by
    have h1 : D'.card = (disparitySet v k).card - 1 := Finset.card_erase_of_mem hx
    have h2 := disp_card_le_seven v k
    omega
  obtain ⟨t7, ht7, hl7⟩ := hSeven D' (fun d hd => disp_pos hinj (Finset.mem_of_mem_erase hd)) hcard
  set f : ℝ := Int.fract (x / g) with hf
  have hf1 : f < 1 := Int.fract_lt_one _
  have hf0 : 0 < f := by
    rcases (Int.fract_nonneg (x / g)).lt_or_eq with h | h
    · exact h
    · exfalso
      have : x / g = (⌊x / g⌋ : ℝ) := by
        have := Int.floor_add_fract (x / g)
        rw [← hf] at this; linarith
      exact hnot ⌊x / g⌋ (by field_simp at this; linarith)
  obtain ⟨n, hn⟩ := exists_clear_step (c := x * t7) hf0 hf1
  have hxpos := disp_pos hinj hx
  refine ⟨t7 + (n : ℝ) / g, by positivity, ?_⟩
  rw [Fresh.Localisation.isolatedAt_iff]
  intro d hd
  by_cases hdx : d = x
  · subst hdx
    have e : d * (t7 + (n : ℝ) / g) = (d * t7 + (n : ℝ) * f) + (((n : ℤ) * ⌊d / g⌋ : ℤ) : ℝ) := by
      have : f = d / g - ⌊d / g⌋ := rfl
      rw [this]; push_cast; field_simp; ring
    rw [e, distInt_add_int]
    exact hn
  · obtain ⟨m, hm⟩ := hmult d hd hdx
    have e : d * (t7 + (n : ℝ) / g) = d * t7 + (((n : ℤ) * (m : ℤ) : ℤ) : ℝ) := by
      rw [hm]; push_cast; field_simp
    rw [e, distInt_add_int]
    have := hl7 d (Finset.mem_erase.2 ⟨hdx, hd⟩)
    linarith

-- STANDING: DEFINITION
def BlockSplitClass (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  ∃ g m : ℝ, 0 < m ∧ 28 * m ≤ g ∧ (∃ c ∈ disparitySet v k, c ≤ m) ∧ (∃ f ∈ disparitySet v k, m < f) ∧
    ∀ d ∈ disparitySet v k, d ≤ m ∨ ∃ n : ℕ, d = (n : ℝ) * g

theorem blockSplit_isolation (hSeven : SevenClear6) {v : Fin 8 → ℝ} (hinj : Function.Injective v) {k : Fin 8}
    (h : BlockSplitClass v k) : Isolation v k := by
  obtain ⟨g, m, hm, hgm, ⟨c0, hc0, hc0m⟩, ⟨f0, hf0, hf0m⟩, hsplit⟩ := h
  have hg : 0 < g := by linarith
  set D := disparitySet v k with hD
  set C : Finset ℝ := D.filter (fun d => d ≤ m) with hC
  set F : Finset ℝ := D.filter (fun d => ¬ d ≤ m) with hF
  have hCF : C.card + F.card = D.card := Finset.card_filter_add_card_filter_not _
  have hDc : D.card ≤ 7 := disp_card_le_seven v k
  have hCne : 1 ≤ C.card := Finset.card_pos.2 ⟨c0, Finset.mem_filter.2 ⟨hc0, hc0m⟩⟩
  have hFne : 1 ≤ F.card := Finset.card_pos.2 ⟨f0, Finset.mem_filter.2 ⟨hf0, by linarith⟩⟩
  have hCc : C.card ≤ 6 := by omega
  have hFc : F.card ≤ 6 := by omega
  have hCpos : ∀ d ∈ C, 0 < d := fun d hd => disp_pos hinj (Finset.mem_filter.1 hd).1
  obtain ⟨τ, hτ, hCl⟩ := hSeven C hCpos hCc
  set F' : Finset ℝ := F.image (fun f => f / g) with hF'
  have hF'pos : ∀ q ∈ F', 0 < q := by
    intro q hq
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.1 hq
    exact div_pos (disp_pos hinj (Finset.mem_filter.1 hf).1) hg
  obtain ⟨σ, hσ, hσl⟩ := hSeven F' hF'pos (le_trans Finset.card_image_le hFc)
  set δ : ℝ := 1 / (56 * m) with hδ
  have hτm : 1 / (7 * m) ≤ τ := by
    have h1 : (1 / 7 : ℝ) ≤ c0 * τ := by
      have := hCl c0 (Finset.mem_filter.2 ⟨hc0, hc0m⟩)
      have h2 := distInt_le_abs (c0 * τ)
      have hc0pos := disp_pos hinj hc0
      rw [abs_of_pos (by positivity)] at h2
      linarith
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hδτ : δ < τ := by
    have : δ < 1 / (7 * m) := by
      rw [hδ]; exact one_div_lt_one_div_of_lt (by positivity) (by linarith)
    linarith
  set j : ℤ := ⌈(τ - δ) * g - σ⌉ with hj
  set t : ℝ := (σ + j) / g with ht
  have hj1 : (τ - δ) * g - σ ≤ j := Int.le_ceil _
  have hj2 : (j : ℝ) < (τ - δ) * g - σ + 1 := Int.ceil_lt_add_one _
  have ht1 : τ - δ ≤ t := by rw [ht, le_div_iff₀ hg]; linarith
  have ht2 : t ≤ τ + δ := by
    have hper : 1 / g ≤ 2 * δ := by
      rw [hδ, div_le_iff₀ hg]
      have : 2 * (1 / (56 * m)) * g = g / (28 * m) := by field_simp; ring
      rw [this, le_div_iff₀ (by positivity)]
      linarith
    have : t < τ - δ + 1 / g := by
      rw [ht, div_lt_iff₀ hg]
      have : (τ - δ + 1 / g) * g = (τ - δ) * g + 1 := by field_simp
      linarith
    linarith
  refine ⟨t, by linarith, ?_⟩
  rw [Fresh.Localisation.isolatedAt_iff]
  intro d hd
  by_cases hdm : d ≤ m
  · have hdpos := disp_pos hinj hd
    have hts : |t - τ| ≤ δ := by rw [abs_le]; constructor <;> linarith
    have hdist : |d * t - d * τ| ≤ 1 / 56 := by
      rw [← mul_sub, abs_mul, abs_of_pos hdpos]
      calc d * |t - τ| ≤ m * δ := mul_le_mul hdm hts (abs_nonneg _) hm.le
        _ = 1 / 56 := by rw [hδ]; field_simp
    have hlip := Fresh.PathLaws.distInt_lipschitz (d * t) (d * τ)
    have h7 := hCl d (Finset.mem_filter.2 ⟨hd, hdm⟩)
    have := (abs_le.1 hlip).1
    have h2 := (abs_le.1 hdist).2
    have h3 := (abs_le.1 hdist).1
    linarith [(abs_le.1 hlip).2]
  · obtain ⟨n, hn⟩ := (hsplit d hd).resolve_left hdm
    have hmemF : d ∈ F := Finset.mem_filter.2 ⟨hd, hdm⟩
    have hq : (n : ℝ) ∈ F' := Finset.mem_image.2 ⟨d, hmemF, by rw [hn]; field_simp⟩
    have e : d * t = (n : ℝ) * σ + (((n : ℤ) * j : ℤ) : ℝ) := by
      rw [hn, ht]; push_cast; field_simp
    rw [e, distInt_add_int]
    have := hσl _ hq
    linarith

#print axioms exists_clear_step
#print axioms oneFree_isolation
#print axioms blockSplit_isolation

end Fresh.FreeStep
