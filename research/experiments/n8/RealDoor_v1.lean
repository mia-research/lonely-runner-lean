import LonelyRunner.LRC.Spec.Doors

/-!
# A door-level result over `ℝ`, with no integer detour

`LonelyRunnerAt8` is stated over the reals, and so is every door: `flankOpening n e k =
(k + 1/n)/e` takes a real `e`, `sep v k i t = (v i - v k) * t`, and `circDist` is on `ℝ`. **The
obligation never mentions integers.** `intLRC 8`, the commensurable case split, the candidate
normal form and the real→integer bridge were all layers I added on top of it.

The first-lap window argument needs none of them. At the opening `t = (j + 1/8)/e` the separation
of runner `i` is `(v i - v k)·t`, and `circDist x ≥ 1/8` is simply `1/8 ≤ x ≤ 7/8` once `x` lies
in `[0,1)`. So the whole argument is an inequality over `ℝ`.

This gives `DoorFlank` outright — hence `LonelyForSubject` by `doorFlank_iff`, hence the target
for those arrangements by `lonelyRunnerAt8_of_doorFlank`.
-/

namespace RealDoor

open LRC.Spec Arrangement Flanks

/-- **`circDist` on the first lap.**  For `x` in `[1/8, 7/8]` the circular distance is at least
`1/8`, with no modular reduction. -/
theorem circDist_ge_of_mem {x : ℝ} (h0 : 1/8 ≤ |x|) (h1 : |x| ≤ 7/8) : (8:ℝ)⁻¹ ≤ circDist x := by
  rcases abs_cases x with ⟨he, _⟩ | ⟨he, hneg⟩
  · rw [he] at h0 h1
    have hf : Int.fract x = x := Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
    unfold circDist; rw [hf]; exact le_min (by linarith) (by linarith)
  · rw [he] at h0 h1
    have hf : Int.fract x = x + 1 := by
      have : Int.fract (x + 1) = Int.fract x := Int.fract_add_one x
      rw [← this]
      exact Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
    unfold circDist; rw [hf]; exact le_min (by linarith) (by linarith)

/-- **The subject is lonely at a window opening.**  If every other runner's separation at the
opening lands in `[1/8, 7/8]`, the subject is lonely there. -/
theorem lonelyAt_of_window {v : Fin 8 → ℝ} {k : Fin 8} {t : ℝ}
    (h : ∀ i : Fin 8, i ≠ k → 1/8 ≤ |(v i - v k) * t| ∧ |(v i - v k) * t| ≤ 7/8) :
    LonelyAt v k t := by
  intro i hi
  rw [sep_eq]
  exact circDist_ge_of_mem (h i hi).1 (h i hi).2

/-- **Door 1, over `ℝ`.**  If some runner's disparity `e = |v i₀ - v k|` has an opening at which
every separation lands in `[1/8, 7/8]`, then `DoorFlank` holds — and with it the obligation for
that subject.  No commensurability, no candidate lattice, no integer reduction. -/
theorem doorFlank_of_window {v : Fin 8 → ℝ} {k i₀ : Fin 8} (hi₀ : i₀ ≠ k) (j : ℕ)
    (h : ∀ i : Fin 8, i ≠ k →
      1/8 ≤ |(v i - v k) * flankOpening 8 |v i₀ - v k| j| ∧
      |(v i - v k) * flankOpening 8 |v i₀ - v k| j| ≤ 7/8) :
    DoorFlank v k :=
  ⟨i₀, hi₀, j, lonelyAt_of_window h⟩

/-- **And it closes the obligation for that subject.** -/
theorem lonelyForSubject_of_window {v : Fin 8 → ℝ} (hv : Function.Injective v)
    {k i₀ : Fin 8} (hi₀ : i₀ ≠ k) (j : ℕ)
    (h : ∀ i : Fin 8, i ≠ k →
      1/8 ≤ |(v i - v k) * flankOpening 8 |v i₀ - v k| j| ∧
      |(v i - v k) * flankOpening 8 |v i₀ - v k| j| ≤ 7/8) :
    LonelyForSubject v k :=
  (doorFlank_iff hv k).mp (doorFlank_of_window hi₀ j h)

/-- **The whole target, if the window can always be found.**  Stated so the remaining obligation
is visible in the tree's own objects, over `ℝ`. -/
theorem lonelyRunnerAt8_of_window
    (H : ∀ v : Fin 8 → ℝ, Function.Injective v → ∀ k : Fin 8,
      ∃ i₀ : Fin 8, i₀ ≠ k ∧ ∃ j : ℕ, ∀ i : Fin 8, i ≠ k →
        1/8 ≤ |(v i - v k) * flankOpening 8 |v i₀ - v k| j| ∧
        |(v i - v k) * flankOpening 8 |v i₀ - v k| j| ≤ 7/8) :
    LonelyRunnerAt8 := by
  refine lonelyRunnerAt8_of_doorFlank (fun v hv k => ?_)
  obtain ⟨i₀, hi₀, j, h⟩ := H v hv k
  exact doorFlank_of_window hi₀ j h

end RealDoor

#print axioms RealDoor.circDist_ge_of_mem
#print axioms RealDoor.lonelyAt_of_window
#print axioms RealDoor.doorFlank_of_window
#print axioms RealDoor.lonelyForSubject_of_window
#print axioms RealDoor.lonelyRunnerAt8_of_window
