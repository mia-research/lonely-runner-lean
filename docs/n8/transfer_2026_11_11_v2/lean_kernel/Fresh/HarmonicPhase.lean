import Fresh.HarmonicArcs
import Mathlib.Data.Fin.Tuple.Sort

namespace Fresh.Harmonic

open Fresh.Cascade

theorem phase_of_replay {p : Vector ℕ n} {ms : List ℕ} {x : Fin n → ℝ}
    (hp : ∀ i : Fin n, 0 < p[i.val])
    (hm : ∀ m ∈ ms, 0 < m ∧ m ≤ 5)
    (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1/(↑(p.get i) : ℝ))
    (hs : ∀ i j, i < j → p[i.val]=p[j.val] → x i ≤ x j)
    (checked : (replay p ms).isEmpty = true) :
    ∃ m ∈ ms, ∃ φ : ℝ, ∀ i, (13/100 : ℝ) < distInt ((↑(p.get i) : ℝ)*(φ+(m : ℝ)*x i)) := by
  by_contra! h
  have hr := root_sound hp hx hs
  obtain ⟨b,hb,-⟩ := replay_sound hr
    (fun m hmem => clauses_sound hp (hm m hmem) hx hr (h m hmem))
  have hz : replay p ms = [] := List.isEmpty_iff.mp checked
  simp [hz] at hb

theorem drift_of_replay {p : Vector ℕ n} {ms : List ℕ} (b : Fin n → ℝ) (t : ℝ)
    (hp : ∀ i : Fin n, 0 < p[i.val])
    (ordered : Monotone (fun i : Fin n => p[i.val]))
    (hm : ∀ m ∈ ms, 0 < m ∧ m ≤ 5) (checked : (replay p ms).isEmpty = true) :
    ∃ m ∈ ms, ∃ φ : ℝ, ∀ i, (13/100 : ℝ) < distInt ((↑(p.get i) : ℝ)*φ+b i*((m : ℝ)*t)) := by
  let x (i : Fin n) := Int.fract (b i*t)/(↑(p.get i) : ℝ)
  have hp' (i : Fin n) : (0 : ℝ) < (p.get i : ℝ) := by exact_mod_cast hp i
  have hx (i : Fin n) : 0 ≤ x i ∧ x i ≤ 1/(↑(p.get i) : ℝ) :=
    ⟨div_nonneg (Int.fract_nonneg _) (hp' i).le,
      div_le_div_of_nonneg_right (Int.fract_lt_one _).le (hp' i).le⟩
  let f (i : Fin n) := toLex (p[i.val], x i)
  let σ := Tuple.sort f
  have hsort : Monotone (f ∘ σ) := Tuple.monotone_sort f
  have hpmono : Monotone (fun i : Fin n => p[(σ i).val]) := by
    intro i j hij
    rcases Prod.Lex.le_iff.mp (hsort hij) with h | h
    · exact h.le
    · exact h.1.le
  have same (i : Fin n) : p.get (σ i) = p.get i := by
    have hh := Tuple.unique_monotone
      (f := fun j : Fin n => p[j.val]) (σ := σ) (τ := Equiv.refl _)
      hpmono ordered
    exact congrFun hh i
  have xs (i j : Fin n) (hij : i < j) (hij' : p[i.val]=p[j.val]) : x (σ i) ≤ x (σ j) := by
    rcases Prod.Lex.le_iff.mp (hsort hij.le) with h | h
    · change p.get (σ i) < p.get (σ j) at h
      have hEq : p.get i = p.get j := hij'
      rw [same i,same j,hEq] at h
      exact (lt_irrefl _ h).elim
    · exact h.2
  have hxx (i : Fin n) : 0 ≤ x (σ i) ∧ x (σ i) ≤ 1/(↑(p.get i) : ℝ) := by
    simpa only [same] using hx (σ i)
  obtain ⟨m,hm',φ,hφ⟩ := phase_of_replay hp hm hxx xs checked
  refine ⟨m,hm',φ,fun i => ?_⟩
  have h := hφ (σ.symm i)
  have hsame : p.get (σ.symm i) = p.get i := by simpa using (same (σ.symm i)).symm
  simp only [Equiv.apply_symm_apply] at h
  rw [hsame] at h
  have he : (↑(p.get i) : ℝ)*(φ+(m : ℝ)*x i) =
      ((↑(p.get i) : ℝ)*φ+b i*((m : ℝ)*t)) - (((m : ℤ)*⌊b i*t⌋ : ℤ) : ℝ) := by
    dsimp [x]
    rw [Int.fract]
    push_cast
    field_simp [ne_of_gt (hp' i)]
    ring
  rw [he, sub_eq_add_neg, ← Int.cast_neg, distInt_add_int] at h
  exact h

#print axioms drift_of_replay
end Fresh.Harmonic
