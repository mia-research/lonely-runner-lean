import LonelyRunner.LRC.Spec.WindowPinchN
import LonelyRunner.LRC.Spec.FastRunnerN

/-!
# Inserting one reading into an already clear core window

The core window is supplied, not assumed to exist for arbitrary inputs.
Either its left end works, the inserted reading exits inside it, or one open
capture zone contains the entire window. This is exact, including endpoints.
-/

namespace LRC.CoreWindowInsertion

open MomentIterationN

/-- Once a window's left end is captured on lap K, the forward exit belongs
to the window precisely when its right end reaches that exit. -/
theorem exit_in_window {V L U : ℝ} (hV : 0 < V) (K : ℤ)
    (hleft : V * L < (K : ℝ) + 1 / 8)
    (hright : (K : ℝ) + 1 / 8 ≤ V * U) :
    L < ((K : ℝ) + 1 / 8) / V ∧
    ((K : ℝ) + 1 / 8) / V ≤ U ∧
    (8 : ℝ)⁻¹ ≤ circDist (V * (((K : ℝ) + 1 / 8) / V)) := by
  refine ⟨(lt_div_iff₀ hV).mpr (by nlinarith),
    (div_le_iff₀ hV).mpr (by nlinarith), ?_⟩
  rw [mul_div_cancel₀ _ hV.ne']
  exact TwoPinner.clear_of_band le_rfl (by norm_num)

/-- A whole closed window is obstructed by one reading iff one of its open
capture zones contains both endpoints. No scan over intervening times. -/
theorem swallowed_iff {V L U : ℝ} (hV : 0 < V) (hLU : L ≤ U) :
    (∀ t, L ≤ t → t ≤ U → circDist (V * t) < (8 : ℝ)⁻¹) ↔
    ∃ K : ℤ, (K : ℝ) - 1 / 8 < V * L ∧ V * U < (K : ℝ) + 1 / 8 := by
  constructor
  · intro h
    obtain ⟨K, hK⟩ := ConstructionN.circDist_eq_abs_sub_some_int (V * L)
    have hb := h L le_rfl hLU
    rw [hK] at hb
    have hab : |V * L - (K : ℝ)| < 1 / 8 := by simpa using hb
    obtain ⟨hl, hr⟩ := abs_lt.mp hab
    refine ⟨K, by linarith, ?_⟩
    by_contra hn
    obtain ⟨heL, heU, heclear⟩ := exit_in_window (L := L) (U := U)
      hV K (by linarith) (le_of_not_gt hn)
    exact (not_lt_of_ge heclear) (h _ heL.le heU)
  · rintro ⟨K, hl, hu⟩ t hLt htU
    have hlo := mul_le_mul_of_nonneg_left hLt hV.le
    have hhi := mul_le_mul_of_nonneg_left htU hV.le
    have hab : |V * t - (K : ℝ)| < 1 / 8 := by
      rw [abs_lt]
      constructor <;> linarith
    exact lt_of_le_of_lt (ConstructionN.circDist_le_abs_sub_int _ K) (by simpa using hab)

/-- Exact forbidden intervals for the inserted speed, with the core held
fixed. Equalities are not forbidden: a threshold endpoint is clear. -/
theorem swallowed_speed_iff {V L U : ℝ} (hV : 0 < V)
    (hL : 0 < L) (hLU : L ≤ U) :
    (∀ t, L ≤ t → t ≤ U → circDist (V * t) < (8 : ℝ)⁻¹) ↔
    ∃ K : ℤ, ((K : ℝ) - 1 / 8) / L < V ∧
      V < ((K : ℝ) + 1 / 8) / U := by
  rw [swallowed_iff hV hLU]
  have hU : 0 < U := hL.trans_le hLU
  apply exists_congr
  intro K
  rw [div_lt_iff₀ hL, lt_div_iff₀ hU]

/-- Every entirely swallowed core window is strictly shorter than a capture
zone. A window of equal width already forces an isolation endpoint. -/
theorem swallowed_width {V L U : ℝ} (hV : 0 < V) (hLU : L ≤ U)
    (h : ∀ t, L ≤ t → t ≤ U → circDist (V * t) < (8 : ℝ)⁻¹) :
    V * (U - L) < 1 / 4 := by
  obtain ⟨K, hl, hu⟩ := (swallowed_iff hV hLU).mp h
  linarith

/-- Lift failure of insertion to a concrete necessary obstruction, carrying
ALL core readings through their known clear window. -/
theorem insertion_or_swallowed {ι : Type*} (S : Finset ι) (d : ι → ℝ)
    {V L U : ℝ} (hV : 0 < V) (hL : 0 < L) (hLU : L ≤ U)
    (hcore : ∀ t, L ≤ t → t ≤ U → ∀ i ∈ S, (8 : ℝ)⁻¹ ≤ circDist (d i * t)) :
    (∃ t, 0 < t ∧ L ≤ t ∧ t ≤ U ∧ (8 : ℝ)⁻¹ ≤ circDist (V * t) ∧
      ∀ i ∈ S, (8 : ℝ)⁻¹ ≤ circDist (d i * t)) ∨
    (∃ K : ℤ, (K : ℝ) - 1 / 8 < V * L ∧ V * U < (K : ℝ) + 1 / 8) := by
  by_cases h : ∃ t, L ≤ t ∧ t ≤ U ∧ (8 : ℝ)⁻¹ ≤ circDist (V * t)
  · obtain ⟨t, hl, hu, hc⟩ := h
    exact Or.inl ⟨t, hL.trans_le hl, hl, hu, hc, hcore t hl hu⟩
  · right
    apply (swallowed_iff hV hLU).mp
    intro t hl hu
    exact lt_of_not_ge (fun hc => h ⟨t, hl, hu, hc⟩)

/-- For a fixed positive-width core window, even the capture label of an
arbitrarily large inserted speed is bounded whenever insertion fails. The
bound is derived from the window itself, not imposed on the speed space. -/
theorem swallowed_label_bound {V L U : ℝ} (hV : 0 < V) (hL : 0 < L)
    (hLU : L < U) (K : ℤ)
    (hl : (K : ℝ) - 1 / 8 < V * L)
    (hu : V * U < (K : ℝ) + 1 / 8) :
    0 ≤ K ∧ (K : ℝ) < L / (4 * (U - L)) + 1 / 8 := by
  have hw : 0 < U - L := sub_pos.mpr hLU
  have hshort : V * (U - L) < 1 / 4 := by nlinarith
  have hK : (-1 : ℝ) < K := by nlinarith [mul_pos hV (hL.trans hLU)]
  have hKi : (-1 : ℤ) < K := by exact_mod_cast hK
  refine ⟨by omega, ?_⟩
  have h1 := mul_lt_mul_of_pos_right hl hw
  have h2 := mul_lt_mul_of_pos_left hshort hL
  have hdiv : (K : ℝ) - 1 / 8 < L / (4 * (U - L)) := by
    apply (lt_div_iff₀ (by positivity : 0 < 4 * (U - L))).mpr
    nlinarith
  linarith

/-- A fixed positive core window yields a FINITE list of all possible
obstruction laps, uniformly over every positive inserted speed. -/
theorem finite_obstruction_labels {L U : ℝ} (hL : 0 < L) (hLU : L < U) :
    ∃ N : ℕ, ∀ V : ℝ, 0 < V →
      ((∀ t, L ≤ t → t ≤ U → circDist (V * t) < (8 : ℝ)⁻¹) ↔
        ∃ K ∈ Finset.Icc (0 : ℤ) (N : ℤ),
          (K : ℝ) - 1 / 8 < V * L ∧ V * U < (K : ℝ) + 1 / 8) := by
  obtain ⟨N, hN⟩ := exists_nat_gt (L / (4 * (U - L)) + 1 / 8)
  refine ⟨N, fun V hV => ?_⟩
  rw [swallowed_iff hV hLU.le]
  constructor
  · rintro ⟨K, hl, hu⟩
    obtain ⟨hK0, hKb⟩ := swallowed_label_bound hV hL hLU K hl hu
    have hKN : (K : ℝ) ≤ ((N : ℤ) : ℝ) := by simpa using (hKb.trans hN).le
    have hKNi : K ≤ (N : ℤ) := by exact_mod_cast hKN
    exact ⟨K, Finset.mem_Icc.mpr ⟨hK0, hKNi⟩, hl, hu⟩
  · rintro ⟨K, _, hl, hu⟩
    exact ⟨K, hl, hu⟩

end LRC.CoreWindowInsertion
