import LonelyRunner.LRC.Cascade.Flanks

/-!
# Two walkers: the run-length criterion

Development file (outside the artefact, so the gate's no-`sorry` rule is never at risk).

At a flank, a non-integer ratio `ρ` with fractional part `f` sits at `k·f + ρ/8` and is CLEAR when
that is at least `1/n` from every integer.  `exists_clear_step` settles ONE such walker.  Two is
open in general -- `ρ = 1/2` and `ρ = 3.5` block every opening between them (`two_walker_v1.py`,
reproducing the manuscript's §6.9 family).  But the obstruction needs a FAST walker:

* a walker is bad for at most `(2/n)/f` consecutive openings   (`bad_run_le`, below)
* and clear for a run of about `(1 − 2/n)/f`
so if the SLOWER walker's clear run outlasts the FASTER walker's bad run, some opening has both
clear.  Measured sound on 60,000 pairs, 0 violations; every shadowing configuration found
exhaustively to denominator 7 has max `min(f,1−f) ≥ 1/3`.
-/

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace TwoWalker

open ConstructionN

variable {n : ℕ} [Fact (2 ≤ n)]

/-- `x` is within `1/n` of an integer. -/
def Bad (n : ℕ) (x : ℝ) : Prop := circDist x < (n : ℝ)⁻¹

/-- **A walker cannot stay bad for long.**  If the walker `k ↦ k·f + c` is bad at every one of
`k, k+1, …, k+m`, then `m·f < 2/n`.  The step cannot carry it past one integer's bad interval
into the next, because that would need `f > 1 − 2/n`, and `f ≤ 1/2 ≤ 1 − 2/n` for `n ≥ 4`. -/
theorem bad_run_le (hn4 : 4 ≤ n) {f c : ℝ} (hf0 : 0 < f) (hfh : f ≤ 1/2) (k m : ℕ)
    (hbad : ∀ j ≤ m, Bad n (((k + j : ℕ) : ℝ) * f + c)) :
    (m : ℝ) * f < 2 * (n : ℝ)⁻¹ := by
  have hn4r : (4 : ℝ) ≤ n := by exact_mod_cast hn4
  have hn0 : (0 : ℝ) < n := by linarith
  have hh0 : (0 : ℝ) < (n : ℝ)⁻¹ := inv_pos.mpr hn0
  have hq : 4 * (n : ℝ)⁻¹ ≤ 1 := by rw [mul_inv_le_iff₀ hn0]; linarith
  set P : ℕ → ℝ := fun j => (((k + j : ℕ) : ℝ)) * f + c with hPdef
  have hpick : ∀ j : ℕ, ∃ N : ℤ, j ≤ m → |P j - (N : ℝ)| < (n : ℝ)⁻¹ := by
    intro j
    by_cases hj : j ≤ m
    · obtain ⟨N, hN⟩ := circDist_eq_abs_sub_some_int (P j)
      exact ⟨N, fun _ => by rw [← hN]; exact hbad j hj⟩
    · exact ⟨0, fun h => absurd h hj⟩
  choose N hN using hpick
  have hPstep : ∀ j : ℕ, P (j + 1) = P j + f := by
    intro j; simp only [hPdef]; push_cast; ring
  -- the nearest integer never advances: that would need f > 1 - 2/n, and f ≤ 1/2 ≤ 1 - 2/n
  have hstep : ∀ j : ℕ, j + 1 ≤ m → N (j + 1) = N j := by
    intro j hj
    have h1 := hN j (by omega)
    have h2 := hN (j + 1) hj
    rw [abs_lt] at h1 h2
    rw [hPstep j] at h2
    have hz : ((N (j+1) - N j : ℤ) : ℝ) = ((N (j+1) : ℝ)) - ((N j : ℝ)) := by push_cast; ring
    by_contra hne
    have h1' : (1 : ℝ) ≤ |((N (j+1) - N j : ℤ) : ℝ)| := by
      rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs (by omega)
    rw [hz, le_abs] at h1'
    rcases h1' with hge | hge
    · -- the integer ADVANCED: that forces f > 1 - 2/n, but f ≤ 1/2 ≤ 1 - 2/n for n ≥ 4
      nlinarith [h1.2, h2.1, hq, hfh, hh0]
    · -- the integer went BACK: that forces f < 0
      nlinarith [h1.1, h2.2, hq, hf0, hh0]
  have hall : ∀ j : ℕ, j ≤ m → N j = N 0 := by
    intro j
    induction j with
    | zero => intro _; rfl
    | succ i ih => intro hj; rw [hstep i hj]; exact ih (by omega)
  have hPm : P m = P 0 + (m : ℝ) * f := by simp only [hPdef]; push_cast; ring
  have e0 := hN 0 (by omega)
  have em := hN m (le_refl m)
  rw [hall m (le_refl m)] at em
  rw [hPm] at em
  rw [abs_lt] at e0 em
  have : |(m : ℝ) * f| < 2 * (n : ℝ)⁻¹ := by
    rw [abs_lt]; constructor <;> linarith [e0.1, e0.2, em.1, em.2]
  calc (m : ℝ) * f ≤ |(m : ℝ) * f| := le_abs_self _
    _ < 2 * (n : ℝ)⁻¹ := this

end TwoWalker
