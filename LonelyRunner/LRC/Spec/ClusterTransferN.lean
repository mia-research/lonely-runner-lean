import LonelyRunner.LRC.Spec.InertReadingN

/-!+# Cluster reduction with the admissible interval retained

Use ordinary time here. Under t = a + u/c, a cluster reading c*x
has phase a*c*x and slope x. Integer phase shifts do not change clearance.
The slow readings may be removed only where they are clear. These are exact
reductions; none asserts existence of a cluster stopping point or a finite
universal catalogue.
-/

namespace LRC.ClusterTransfer
open MomentIterationN

theorem reading_transform {c : ℝ} (hc : c ≠ 0) (a x u : ℝ) :
    (c*x)*(a+u/c) = a*c*x+x*u := by
  field_simp
  <;> ring

/-- The starting phase must be retained, up to an integer number of laps. -/
theorem phase_clear_iff {c a x u p : ℝ} {k : ℤ} (hc : c ≠ 0)
    (hp : a*c*x = p+(k : ℝ)) :
    (8 : ℝ)⁻¹ ≤ circDist ((c*x)*(a+u/c)) ↔
      (8 : ℝ)⁻¹ ≤ circDist (p+x*u) := by
  rw [reading_transform hc, hp]
  rw [show p+(k : ℝ)+x*u = (p+x*u)+(k : ℝ) by ring]
  rw [ConstructionN.circDist_add_int]

/-- The next exit on the cluster clock keeps the initial phase as well.
The ceiling, hence the lap selection, is unchanged by the coordinate change. -/
theorem nextOpening_transform {c x : ℝ} (hc : c ≠ 0) (hx : x ≠ 0)
    (a u : ℝ) :
    nextOpening 8 (c*x) (a+u/c) =
      a + ((((⌈a*c*x+x*u-(8 : ℝ)⁻¹⌉ : ℝ) + (8 : ℝ)⁻¹ - a*c*x) / x) / c) := by
  unfold nextOpening
  rw [reading_transform hc]
  field_simp
  <;> ring

/-- Every slow reading clear at this state contributes no cascade move.
This removes a whole slow set, not merely one inert reading. -/
theorem move_union_clear (S F : Finset ℝ) (t : ℝ)
    (hs : ∀ d ∈ S, (8 : ℝ)⁻¹ ≤ circDist (d*t)) :
    move 8 (S ∪ F) t = move 8 F t := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert d S hd ih =>
    rw [Finset.insert_union, LRC.InertReading.move_insert_clear _ (hs d (by simp))]
    exact ih (fun e he => hs e (by simp [he]))

/-- The full prefix is preserved if the discarded readings stay clear at
every cluster state. No claim about arbitrary deletion of path letters. -/
theorem iterate_union_clear (S F : Finset ℝ) (b : ℝ) (N : ℕ)
    (hs : ∀ j < N, ∀ d ∈ S,
      (8 : ℝ)⁻¹ ≤ circDist (d*((move 8 F)^[j] b))) :
    (move 8 (S ∪ F))^[N] b = (move 8 F)^[N] b := by
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
      ih (fun j hj => hs j (Nat.lt_succ_of_lt hj))]
    exact move_union_clear S F _ (hs N (Nat.lt_succ_self N))

/-- A clear slow window reduces existence exactly to the cluster on its
rescaled interval, with its initial phases. Both interval ends are included. -/
theorem window_transfer_iff (S F : Finset ℝ) {c A B : ℝ} (hc : 0 < c)
    (hs : ∀ t, A ≤ t → t ≤ B → ∀ d ∈ S,
      (8 : ℝ)⁻¹ ≤ circDist (d*t)) :
    (∃ t, A ≤ t ∧ t ≤ B ∧
      (∀ d ∈ S, (8 : ℝ)⁻¹ ≤ circDist (d*t)) ∧
      ∀ x ∈ F, (8 : ℝ)⁻¹ ≤ circDist ((c*x)*t)) ↔
    ∃ u, 0 ≤ u ∧ u ≤ c*(B-A) ∧
      ∀ x ∈ F, (8 : ℝ)⁻¹ ≤ circDist (A*c*x+x*u) := by
  constructor
  · rintro ⟨t, htA, htB, _, hf⟩
    refine ⟨c*(t-A), mul_nonneg hc.le (sub_nonneg.mpr htA), ?_, ?_⟩
    · nlinarith
    · intro x hx
      convert hf x hx using 2 <;> ring
  · rintro ⟨u, hu, hub, hf⟩
    have htA : A ≤ A+u/c := le_add_of_nonneg_right (div_nonneg hu hc.le)
    have htB : A+u/c ≤ B := by
      have h : u/c ≤ B-A := (div_le_iff₀ hc).mpr (by nlinarith [hub])
      linarith
    refine ⟨A+u/c, htA, htB, hs _ htA htB, ?_⟩
    intro x hx
    rw [reading_transform hc.ne']
    exact hf x hx

end LRC.ClusterTransfer
