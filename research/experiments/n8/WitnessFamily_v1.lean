import LonelyRunner.LRC.Cascade.Flanks

/-!
# A witness map for the critical family, in the framework's own predicate

`docs/n8/WITNESS_MAP_v1.md`.  Exhaustively over all 18,564,316 primitive 7-subsets of `[1,40]`, the
only difference sets with a **single** supporting flank are `(2,3,4,5,6,7,16)` and `(2,3,4,5,6,7,32)`;
the family is `{2,…,7} ∪ {x}` with `16 ∣ x`, and its witness at the sole flank `x` is `k = x/16`.

`experiments/n8/FirstLap_v1.lean` proves the `x = 16` instance, but against its **own** `inWay` on
`ℤ` — it never reaches `Lonely`.  This file states the whole family against
`MomentIterationN.Lonely` and `Flanks.flankOpening`, so it connects to the target.

**It is a family lemma, not `witness_lonely`.**  `Spec/Target.lean`'s discharge criterion quantifies
over every injective `v : Fin 8 → ℝ` and every subject; this covers one base with one parameter.

Stated over `ℝ`: the other disparities need only lie in `[2,7]`, not be integers, which is strictly
more than the measured family.
-/

namespace WitnessFamily

open MomentIterationN Flanks ConstructionN

instance : Fact (2 ≤ 8) := ⟨by norm_num⟩

/-- **The window step.**  A reading parked in `[1/8, 7/8]` is at circle distance at least `1/8`. -/
theorem clear_of_window {y : ℝ} (h1 : (8 : ℝ)⁻¹ ≤ y) (h2 : y ≤ 1 - (8 : ℝ)⁻¹) :
    (8 : ℝ)⁻¹ ≤ circDist y := by
  have hf : Int.fract y = y := by
    rw [Int.fract_eq_self]; constructor <;> norm_num at h1 h2 ⊢ <;> linarith
  unfold circDist
  rw [hf]
  exact le_min h1 (by linarith)

/-- **The witness map for the critical family.**  For every `k ≥ 1`, a difference set whose members
each either lie in `[2,7]` or equal `16k` is lonely at the flank `16k`'s `k`-th opening.

The instant is `(k + 1/8)/(16k) = 1/16 + 1/(128k)`.  A disparity `d ∈ [2,7]` reads
`d/16 + d/(128k)`, which is at least `1/8` because `d ≥ 2`, and at most `7/8` because `d ≤ 7` and
`k ≥ 1`.  The flank reads `k + 1/8` exactly, so its circle distance is `1/8` — admissible because the
threshold is closed. -/
theorem lonely_witness_family {k : ℕ} (hk : 1 ≤ k) {ds : Finset ℝ}
    (h : ∀ d ∈ ds, (2 ≤ d ∧ d ≤ 7) ∨ d = 16 * (k : ℝ)) :
    Lonely 8 ds (flankOpening 8 (16 * (k : ℝ)) k) := by
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hkpos : (0 : ℝ) < (k : ℝ) := by linarith
  have h16 : (0 : ℝ) < 16 * (k : ℝ) := by linarith
  intro d hd
  have ht : flankOpening 8 (16 * (k : ℝ)) k = ((k : ℝ) + (8 : ℝ)⁻¹) / (16 * (k : ℝ)) := by
    unfold flankOpening; norm_num
  rcases h d hd with ⟨hlo, hhi⟩ | rfl
  · -- an ordinary disparity, parked in the window
    rw [ht]
    have hmul : d * (((k : ℝ) + (8 : ℝ)⁻¹) / (16 * (k : ℝ)))
        = (d * ((k : ℝ) + (8 : ℝ)⁻¹)) / (16 * (k : ℝ)) := by ring
    rw [hmul]
    refine clear_of_window ?_ ?_
    · rw [le_div_iff₀ h16]; nlinarith
    · rw [div_le_iff₀ h16]; nlinarith
  · -- the flank itself: it reads exactly `k + 1/8`
    rw [ht]
    have e : (16 * (k : ℝ)) * (((k : ℝ) + (8 : ℝ)⁻¹) / (16 * (k : ℝ)))
        = (8 : ℝ)⁻¹ + ((k : ℤ) : ℝ) := by
      field_simp; push_cast; ring
    rw [e, circDist_add_int]
    have hcd : circDist ((8 : ℝ)⁻¹) = (8 : ℝ)⁻¹ := by
      unfold circDist
      rw [Int.fract_eq_self.mpr (by norm_num)]
      norm_num
    rw [hcd]
    norm_num

/-- **The measured family is the integer case.**  `(2,3,4,5,6,7,16m)` is lonely at the opening
`k = m` of its sole flank — the closed form `(e,k) = (x, x/16)`. -/
theorem lonely_critical_set {m : ℕ} (hm : 1 ≤ m) :
    Lonely 8 ({2, 3, 4, 5, 6, 7, 16 * (m : ℝ)} : Finset ℝ)
      (flankOpening 8 (16 * (m : ℝ)) m) := by
  classical
  refine lonely_witness_family hm (fun d hd => ?_)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hd
  rcases hd with rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact Or.inl ⟨by norm_num, by norm_num⟩
  · exact Or.inl ⟨by norm_num, by norm_num⟩
  · exact Or.inl ⟨by norm_num, by norm_num⟩
  · exact Or.inl ⟨by norm_num, by norm_num⟩
  · exact Or.inl ⟨by norm_num, by norm_num⟩
  · exact Or.inl ⟨by norm_num, by norm_num⟩
  · exact Or.inr rfl

end WitnessFamily

#print axioms WitnessFamily.clear_of_window
#print axioms WitnessFamily.lonely_witness_family
#print axioms WitnessFamily.lonely_critical_set
