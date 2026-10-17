import LonelyRunner.LRC.Spec.OrderSevenHalfUnitsN
import LonelyRunner.LRC.Spec.OrderSevenLevel2N
import LonelyRunner.LRC.Spec.OrderSevenDescentN

/-!
# Order seven on 7-adic grids: every set with no speed divisible by `343`

`grid_nu2_of`: given certificates A, B, C, every set of at most six positive integers with no element divisible by
`343` is in band at a unit instant `k / 7^a`.  Cases on the units `U`, the runners `M1` of valuation 1 and `M2` of
valuation 2:

* no multiple of 7: level 1;
* no multiple of 49: at most four units, level 2 (valuation 1 is automatic there); five units and one `7m`, C;
* `U` empty: divide every speed by 7 and go up one level;
* `1 ≤ |U| ≤ 3`: the descent (cofactors of `M1` at level 2, a free top digit for the units, `M2` automatic);
* `|U| ≥ 4`: A if `M1` is empty, otherwise B.

Everything here is proved; no `sorry`, no `native_decide`.
-/

namespace LRC.O7L3
open LRC.O7Grid

/-- Some unit instant of some level puts every speed in band. -/
def GridG (S : Finset ℕ) : Prop := ∃ a k, 1 ≤ a ∧ ¬ 7 ∣ k ∧ ∀ d ∈ S, GridOK a k d

theorem gridOK_succ_seven {a : ℕ} (ha : 1 ≤ a) (k d : ℕ) : GridOK (a + 1) k (7 * d) ↔ GridOK a k d := by
  unfold GridOK
  obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have e : 7 * d * k % 7 ^ (b + 1 + 1) = 7 * (d * k % 7 ^ (b + 1)) := by
    rw [show 7 * d * k = 7 * (d * k) by ring, pow_succ' 7 (b + 1), Nat.mul_mod_mul_left]
  rw [e]
  generalize d * k % 7 ^ (b + 1) = x
  rw [pow_succ' 7 b]
  constructor <;> intro h <;> omega

theorem grid_nu1_of (hC1 : chunkC1 = true) (hC2 : ∀ p, p < 15 → chunkC2 p = true) {S : Finset ℕ}
    (hS : S.card ≤ 6) (h49 : ∀ d ∈ S, ¬ 49 ∣ d) : GridG S := by
  set U := S.filter fun d => ¬ 7 ∣ d with hU
  set M := S.filter fun d => 7 ∣ d with hM
  have hcard : M.card + U.card = S.card := Finset.filter_card_add_filter_neg_card_eq_card _
  rcases M.eq_empty_or_nonempty with hM0 | ⟨d0, hd0⟩
  · refine ⟨1, 1, le_rfl, by norm_num, fun d hd => gridOK_one ?_ (by norm_num)⟩
    intro h7; have : d ∈ M := Finset.mem_filter.mpr ⟨hd, h7⟩; rw [hM0] at this; simp at this
  by_cases hU4 : U.card ≤ 4
  · obtain ⟨k, hk, hkU⟩ := units_level_two hU4 (fun u hu => (Finset.mem_filter.mp hu).2)
    refine ⟨2, k, by norm_num, hk, fun d hd => ?_⟩
    by_cases h7 : 7 ∣ d
    · obtain ⟨d', rfl⟩ := h7
      exact gridOK_two_val1 (by have := h49 _ hd; omega) hk
    · exact hkU d (Finset.mem_filter.mpr ⟨hd, h7⟩)
  · have hM1 : M.card = 1 := by have := Finset.card_pos.mpr ⟨d0, hd0⟩; omega
    obtain ⟨d1, hd1⟩ := Finset.card_eq_one.mp hM1
    have hd1M : d1 ∈ M := by rw [hd1]; exact Finset.mem_singleton_self d1
    obtain ⟨hd1S, m, hm⟩ := Finset.mem_filter.mp hd1M
    have hm7 : ¬ 7 ∣ m := by have := h49 _ hd1S; rw [hm] at this; omega
    have hUne : U.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨a, k, ha, hk, hkU, hkm⟩ :=
      units5_val1_of hC1 hC2 (by omega) hUne (fun u hu => (Finset.mem_filter.mp hu).2) hm7
    refine ⟨a, k, ha, hk, fun d hd => ?_⟩
    by_cases h7 : 7 ∣ d
    · have : d ∈ M := Finset.mem_filter.mpr ⟨hd, h7⟩
      rw [hd1, Finset.mem_singleton] at this; rw [this, hm]; exact hkm
    · exact hkU d (Finset.mem_filter.mpr ⟨hd, h7⟩)

theorem grid_nu2_of (hA : ∀ i2, i2 < 147 → chunkAH i2 i2 147 = true)
    (hB : ∀ i2, i2 < 147 → chunkBH i2 i2 147 = true) (hC1 : chunkC1 = true)
    (hC2 : ∀ p, p < 15 → chunkC2 p = true) {S : Finset ℕ} (hS : S.card ≤ 6) (h343 : ∀ d ∈ S, ¬ 343 ∣ d) :
    GridG S := by
  by_cases h49 : ∀ d ∈ S, ¬ 49 ∣ d
  · exact grid_nu1_of hC1 hC2 hS h49
  push_neg at h49
  obtain ⟨e0, he0S, he0⟩ := h49
  set U := S.filter fun d => ¬ 7 ∣ d with hU
  set M := S.filter fun d => 7 ∣ d with hM
  set M1 := M.filter fun d => ¬ 49 ∣ d with hM1
  set M2 := M.filter fun d => 49 ∣ d with hM2
  have c1 : M.card + U.card = S.card := Finset.filter_card_add_filter_neg_card_eq_card _
  have c2 : M2.card + M1.card = M.card := Finset.filter_card_add_filter_neg_card_eq_card _
  have he0M2 : e0 ∈ M2 := Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨he0S, by omega⟩, he0⟩
  have hM2pos : 1 ≤ M2.card := Finset.card_pos.mpr ⟨e0, he0M2⟩
  have v2 : ∀ k, ¬ 7 ∣ k → ∀ d ∈ S, 49 ∣ d → GridOK 3 k d := fun k hk d hd h => by
    obtain ⟨m, rfl⟩ := h
    exact gridOK_three_val2 (by have := h343 _ hd; omega) hk
  have uU : ∀ u ∈ U, ¬ 7 ∣ u := fun u hu => (Finset.mem_filter.mp hu).2
  rcases U.eq_empty_or_nonempty with hU0 | hUne
  · -- every speed is a multiple of 7: divide by 7, go up one level
    have h7all : ∀ d ∈ S, 7 ∣ d := fun d hd => by
      by_contra h; have : d ∈ U := Finset.mem_filter.mpr ⟨hd, h⟩; rw [hU0] at this; simp at this
    obtain ⟨a, k, ha, hk, hok⟩ := grid_nu1_of hC1 hC2 (S := S.image (· / 7))
      (le_trans Finset.card_image_le hS) (by
        intro d' hd'
        obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hd'
        obtain ⟨m, rfl⟩ := h7all d hd
        rw [Nat.mul_div_cancel_left m (by norm_num)]
        have := h343 _ hd; omega)
    refine ⟨a + 1, k, by omega, hk, fun d hd => ?_⟩
    obtain ⟨m, rfl⟩ := h7all d hd
    rw [gridOK_succ_seven ha]
    exact hok m (Finset.mem_image.mpr ⟨7 * m, hd, Nat.mul_div_cancel_left m (by norm_num)⟩)
  have hUpos := Finset.card_pos.mpr hUne
  by_cases hU3 : U.card ≤ 3
  · -- descent: cofactors of `M1` at level 2, then a free top digit for the units
    have hM1c : (M1.image (· / 7)).card ≤ 4 := le_trans Finset.card_image_le (by omega)
    have hM1u : ∀ x ∈ M1.image (· / 7), ¬ 7 ∣ x := by
      intro x hx
      obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨hdM, h49'⟩ := Finset.mem_filter.mp hd
      obtain ⟨-, m, rfl⟩ := Finset.mem_filter.mp hdM
      rw [Nat.mul_div_cancel_left m (by norm_num)]; omega
    obtain ⟨k1, hk1, hk1M⟩ := units_level_two hM1c hM1u
    have hk0 : ¬ 7 ∣ k1 % 49 := by omega
    obtain ⟨s, -, hsU⟩ := free_digit hU3 uU hk0 (Nat.mod_lt _ (by norm_num))
    have hk : ¬ 7 ∣ (k1 % 49 + 49 * s) := by omega
    refine ⟨3, k1 % 49 + 49 * s, by norm_num, hk, fun d hd => ?_⟩
    by_cases h7 : 7 ∣ d
    · by_cases h49' : 49 ∣ d
      · exact v2 _ hk d hd h49'
      · obtain ⟨m, rfl⟩ := h7
        rw [gridOK_three_val1]
        have := (gridOK_mod_k 2 k1 m).mp (hk1M m (Finset.mem_image.mpr ⟨7 * m,
          Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hd, ⟨m, rfl⟩⟩, h49'⟩, Nat.mul_div_cancel_left m (by norm_num)⟩))
        rwa [show (7 : ℕ) ^ 2 = 49 by norm_num] at this
    · exact hsU d (Finset.mem_filter.mpr ⟨hd, h7⟩)
  rcases M1.eq_empty_or_nonempty with hM10 | ⟨d1, hd1⟩
  · -- at most five units, the rest of valuation 2: certificate A
    obtain ⟨k, hk, hkU⟩ := units3_of hA (by omega) uU
    refine ⟨3, k, by norm_num, hk, fun d hd => ?_⟩
    by_cases h7 : 7 ∣ d
    · by_cases h49' : 49 ∣ d
      · exact v2 _ hk d hd h49'
      · have : d ∈ M1 := Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hd, h7⟩, h49'⟩
        rw [hM10] at this; simp at this
    · exact hkU d (Finset.mem_filter.mpr ⟨hd, h7⟩)
  · -- four units, one runner of valuation 1, one of valuation 2: certificate B
    have hM1c : M1.card = 1 := by have := Finset.card_pos.mpr ⟨d1, hd1⟩; omega
    obtain ⟨d2, hd2⟩ := Finset.card_eq_one.mp hM1c
    have hd2M : d2 ∈ M1 := by rw [hd2]; exact Finset.mem_singleton_self d2
    obtain ⟨hd2M', h49d2⟩ := Finset.mem_filter.mp hd2M
    obtain ⟨-, m, hm⟩ := Finset.mem_filter.mp hd2M'
    have hm7 : ¬ 7 ∣ m := by rw [hm] at h49d2; omega
    obtain ⟨k, hk, hkU, hkm⟩ := units3_val1_of hB (by omega) hUne uU hm7
    refine ⟨3, k, by norm_num, hk, fun d hd => ?_⟩
    by_cases h7 : 7 ∣ d
    · by_cases h49' : 49 ∣ d
      · exact v2 _ hk d hd h49'
      · have : d ∈ M1 := Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hd, h7⟩, h49'⟩
        rw [hd2, Finset.mem_singleton] at this; rw [this, hm]; exact hkm
    · exact hkU d (Finset.mem_filter.mpr ⟨hd, h7⟩)

/-- **Order seven, no speed divisible by 343** (from certificates A, B, C): some instant `k / 7^a` keeps every
speed at distance at least `1/7` from an integer. -/
theorem lonely_nu2_of (hA : ∀ i2, i2 < 147 → chunkAH i2 i2 147 = true)
    (hB : ∀ i2, i2 < 147 → chunkBH i2 i2 147 = true) (hC1 : chunkC1 = true)
    (hC2 : ∀ p, p < 15 → chunkC2 p = true) {S : Finset ℕ} (hS : S.card ≤ 6) (h343 : ∀ d ∈ S, ¬ 343 ∣ d) :
    ∃ t : ℝ, ∀ d ∈ S, (1 : ℝ) / 7 ≤ circDist ((d : ℝ) * t) := by
  obtain ⟨a, k, ha, -, hok⟩ := grid_nu2_of hA hB hC1 hC2 hS h343
  exact lonely_of_gridOK ha hok

end LRC.O7L3
