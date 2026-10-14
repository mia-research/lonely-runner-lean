import LonelyRunner.LRC.Cascade.Arrangement
import Mathlib.Data.Finset.Sort

/-!
# Six-factor arrangement space, before any time or disparity bound

Sort the eight speeds, subtract the first, and divide by one seventh of the
total span. The result is 0=x0<x1<...<x6<x7=7. Only the six interior speeds
remain free. Equivalently the seven consecutive speed gaps are positive and
sum to seven. These are speed gaps, not the track gaps at a chosen time.

This removes labelling, common drift and scale exactly. It makes no claim
that finite reference-grid signatures determine every future cascade move.
-/

namespace LRC.ArrangementShape

structure Shape8 where
  speed : Fin 8 → ℝ
  increasing : StrictMono speed
  first : speed 0 = 0
  last : speed 7 = 7

/-- Relabelling preserves each subject's isolation, with its label transported. -/
theorem lonely_relabel (v : Fin 8 → ℝ) (π : Equiv.Perm (Fin 8)) (k : Fin 8) (t : ℝ) :
    Arrangement.LonelyAt (fun i => v (π i)) k t ↔ Arrangement.LonelyAt v (π k) t := by
  constructor
  · intro h i hi
    have hh := h (π.symm i) (by intro he; apply hi; simpa using congrArg π he)
    simpa [Arrangement.sep] using hh
  · intro h i hi
    exact h (π i) (fun he => hi (π.injective he))

/-- Sorting changes labels, not the set of speed arrangements. -/
theorem exists_sorted (v : Fin 8 → ℝ) (hv : Function.Injective v) :
    ∃ π : Equiv.Perm (Fin 8), StrictMono (fun i => v (π i)) := by
  classical
  let S := Finset.univ.image v
  have hc : S.card = 8 := by
    dsimp [S]
    rw [Finset.card_image_of_injective _ hv]
    simp
  let w := S.orderEmbOfFin hc
  have hmem : ∀ i, ∃ j, v j = w i := by
    intro i
    have hi := S.orderEmbOfFin_mem hc i
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hi
    exact ⟨j, hj⟩
  choose p hp using hmem
  have hinj : Function.Injective p := by
    intro i j hij
    apply w.injective
    rw [← hp i, ← hp j, hij]
  let π := Equiv.ofBijective p ((Finite.injective_iff_bijective).mp hinj)
  refine ⟨π, ?_⟩
  intro i j hij
  change v (p i) < v (p j)
  rw [hp i, hp j]
  exact w.strictMono hij

/-- Every arrangement is exactly an affine rescaling of one bounded ordered shape. -/
theorem exists_shape (v : Fin 8 → ℝ) (hv : Function.Injective v) :
    ∃ π : Equiv.Perm (Fin 8), ∃ A D : ℝ, 0 < D ∧ ∃ s : Shape8,
      ∀ i, v (π i) = A + D * s.speed i := by
  obtain ⟨π, hπ⟩ := exists_sorted v hv
  let A := v (π 0)
  let D := (v (π 7) - A) / 7
  have hspan : 0 < v (π 7) - A := sub_pos.mpr (hπ (by decide : (0 : Fin 8) < 7))
  have hD : 0 < D := div_pos hspan (by norm_num)
  let x : Fin 8 → ℝ := fun i => (v (π i) - A) / D
  have hx : StrictMono x := by
    intro i j hij
    exact (div_lt_div_iff_of_pos_right hD).mpr (sub_lt_sub_right (hπ hij) A)
  have h0 : x 0 = 0 := by simp [x, A]
  have h7 : x 7 = 7 := by
    dsimp [x, D]
    field_simp
  refine ⟨π, A, D, hD, ⟨x, hx, h0, h7⟩, ?_⟩
  intro i
  change v (π i) = A + D * ((v (π i) - A) / D)
  field_simp
  ring

/-- A normalized witness maps to physical time by division by the removed scale. -/
theorem lonely_affine (x : Fin 8 → ℝ) (A D τ : ℝ) (hD : D ≠ 0) (k : Fin 8) :
    Arrangement.LonelyAt (fun i => A + D * x i) k (τ / D) ↔
      Arrangement.LonelyAt x k τ := by
  have he : ∀ i, Arrangement.sep (fun j => A + D * x j) k i (τ / D) =
      Arrangement.sep x k i τ := by
    intro i
    unfold Arrangement.sep
    field_simp
    ring
  unfold Arrangement.LonelyAt
  simp only [he]

noncomputable def gap (s : Shape8) (i : Fin 7) : ℝ :=
  s.speed i.succ - s.speed i.castSucc

theorem gap_pos (s : Shape8) (i : Fin 7) : 0 < gap s i := by
  apply sub_pos.mpr
  exact s.increasing (by simp)

theorem gaps_sum (s : Shape8) : ∑ i : Fin 7, gap s i = 7 := by
  simp [gap, Fin.sum_univ_succ]
  linarith [s.first, s.last]

/-- Six interior values determine the entire normalized arrangement. -/
theorem speed_determined_by_six (s t : Shape8)
    (h : ∀ i : Fin 6, s.speed ⟨i.val + 1, by omega⟩ = t.speed ⟨i.val + 1, by omega⟩) :
    s.speed = t.speed := by
  funext i
  fin_cases i
  · change s.speed 0 = t.speed 0
    rw [s.first, t.first]
  · exact h 0
  · exact h 1
  · exact h 2
  · exact h 3
  · exact h 4
  · exact h 5
  · change s.speed 7 = t.speed 7
    rw [s.last, t.last]

theorem speed_bounds (s : Shape8) (i : Fin 8) : 0 ≤ s.speed i ∧ s.speed i ≤ 7 := by
  constructor
  · rw [← s.first]
    exact s.increasing.monotone (Fin.zero_le i)
  · rw [← s.last]
    exact s.increasing.monotone (by omega)

/-- At any reference class from one through seven, positive pair readings have
only fifty possible integer grid labels, regardless of the original speed scale. -/
theorem reference_floor_bounds (s : Shape8) {i j : Fin 8} (hij : i ≤ j)
    {c : ℕ} (hc : c ≤ 7) :
    0 ≤ ⌊(c : ℝ) * (s.speed j - s.speed i)⌋ ∧
      ⌊(c : ℝ) * (s.speed j - s.speed i)⌋ ≤ 49 := by
  have hdiff : 0 ≤ s.speed j - s.speed i := sub_nonneg.mpr (s.increasing.monotone hij)
  have hupper : s.speed j - s.speed i ≤ 7 := by
    have := speed_bounds s i
    have := speed_bounds s j
    linarith
  have hcR : (c : ℝ) ≤ 7 := by exact_mod_cast hc
  constructor
  · exact Int.floor_nonneg.mpr (mul_nonneg (Nat.cast_nonneg c) hdiff)
  · have hy : (c : ℝ) * (s.speed j - s.speed i) ≤ 49 := by
      nlinarith [Nat.cast_nonneg (α := ℝ) c]
    exact_mod_cast le_trans (Int.floor_le _) hy

/-- The original per-runner existence problem is equivalent to the bounded
six-factor shape problem. No finite time bound or grid-cover premise is added. -/
theorem reduction_iff :
    (∀ s : Shape8, ∀ k, ∃ τ : ℝ, 0 < τ ∧ Arrangement.LonelyAt s.speed k τ) ↔
    (∀ v : Fin 8 → ℝ, Function.Injective v → ∀ k,
      ∃ t : ℝ, 0 < t ∧ Arrangement.LonelyAt v k t) := by
  constructor
  · intro hall v hv k
    obtain ⟨π, A, D, hD, s, hs⟩ := exists_shape v hv
    obtain ⟨τ, hτ, hl⟩ := hall s (π.symm k)
    have hsorted : Arrangement.LonelyAt (fun i => v (π i)) (π.symm k) (τ / D) := by
      have he : (fun i => v (π i)) = (fun i => A + D * s.speed i) := funext hs
      rw [he]
      exact (lonely_affine s.speed A D τ hD.ne' (π.symm k)).mpr hl
    refine ⟨τ / D, div_pos hτ hD, ?_⟩
    simpa using (lonely_relabel v π (π.symm k) (τ / D)).mp hsorted
  · intro hall s k
    exact hall s.speed s.increasing.injective k

end LRC.ArrangementShape
