import LonelyRunner.LRC.Cascade.Flanks
import LonelyRunner.LRC.ConstructionN.Window

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

open ConstructionN Flanks MomentIterationN

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

/-! ## the clear run: a walker enters the clear arc at its edge and traverses it -/

/-- **Crossing.**  A walker stepping up by `f` lands in `[1/n, 1/n + f)` above some integer:
it cannot jump the boundary, so the first step at or past `N + 1/n` overshoots by less than `f`. -/
theorem exists_crossing {f c : ℝ} (hf0 : 0 < f) :
    ∃ (k₀ : ℕ) (N : ℤ), (n : ℝ)⁻¹ ≤ (((k₀ : ℕ) : ℝ) * f + c) - (N : ℝ) ∧
      (((k₀ : ℕ) : ℝ) * f + c) - (N : ℝ) < (n : ℝ)⁻¹ + f := by
  classical
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Fact.out : 2 ≤ n)
  have hn0 : (0 : ℝ) < n := by linarith
  have ht : (0 : ℝ) < (n : ℝ)⁻¹ := inv_pos.mpr hn0
  have hceil : c ≤ ((⌈c⌉ : ℤ) : ℝ) := Int.le_ceil c
  have hex : ∃ k : ℕ, ((⌈c⌉ : ℤ) : ℝ) + (n : ℝ)⁻¹ ≤ ((k : ℕ) : ℝ) * f + c := by
    obtain ⟨k, hk⟩ := exists_nat_ge ((((⌈c⌉ : ℤ) : ℝ) + (n : ℝ)⁻¹ - c) / f)
    refine ⟨k, ?_⟩
    rw [div_le_iff₀ hf0] at hk; linarith
  have h0 : ¬ (((⌈c⌉ : ℤ) : ℝ) + (n : ℝ)⁻¹ ≤ (((0 : ℕ) : ℕ) : ℝ) * f + c) := by
    push_cast; linarith
  refine ⟨Nat.find hex, ⌈c⌉, ?_, ?_⟩
  · have hs := Nat.find_spec hex; linarith
  · have hpos : Nat.find hex ≠ 0 := by intro h; exact h0 (h ▸ Nat.find_spec hex)
    have hprev := Nat.find_min hex (m := Nat.find hex - 1) (by omega)
    push Not at hprev
    have h1 : (1 : ℕ) ≤ Nat.find hex := by omega
    have hstep : ((Nat.find hex : ℕ) : ℝ) = ((Nat.find hex - 1 : ℕ) : ℝ) + 1 := by
      push_cast [Nat.cast_sub h1]; ring
    rw [hstep]; nlinarith [hprev]

/-- **The clear run.**  From a crossing the walker stays clear while `j·f ≤ 1 − 2/n − f`: it entered
the clear arc at the bottom edge and has the whole arc of length `1 − 2/n` to cross. -/
theorem clear_run (hn4 : 4 ≤ n) {f c : ℝ} (hf0 : 0 < f) {k₀ : ℕ} {N : ℤ}
    (hlo : (n : ℝ)⁻¹ ≤ (((k₀ : ℕ) : ℝ) * f + c) - (N : ℝ))
    (hhi : (((k₀ : ℕ) : ℝ) * f + c) - (N : ℝ) < (n : ℝ)⁻¹ + f)
    (j : ℕ) (hj : (j : ℝ) * f ≤ 1 - 2 * (n : ℝ)⁻¹ - f) :
    (n : ℝ)⁻¹ ≤ circDist ((((k₀ + j : ℕ)) : ℝ) * f + c) := by
  have hn4r : (4 : ℝ) ≤ n := by exact_mod_cast hn4
  have hn0 : (0 : ℝ) < n := by linarith
  have ht : (0 : ℝ) < (n : ℝ)⁻¹ := inv_pos.mpr hn0
  have hq : 4 * (n : ℝ)⁻¹ ≤ 1 := by rw [mul_inv_le_iff₀ hn0]; linarith
  have hexp : (((k₀ + j : ℕ)) : ℝ) * f + c = ((((k₀ : ℕ) : ℝ) * f + c) - (N : ℝ)) + (j : ℝ) * f + (N : ℝ) := by
    push_cast; ring
  rw [hexp, circDist_add_int, window_iff (by nlinarith [mul_nonneg (Nat.cast_nonneg j : (0:ℝ) ≤ j) hf0.le])
      (by nlinarith [mul_nonneg (Nat.cast_nonneg j : (0:ℝ) ≤ j) hf0.le])]
  constructor
  · nlinarith [mul_nonneg (Nat.cast_nonneg j : (0:ℝ) ≤ j) hf0.le]
  · nlinarith

/-! ## the criterion -/

/-- **The run-length criterion for two walkers.**  If some `L` is short enough that the slower
walker stays clear across `k₀ … k₀+L` (`L·f₁ ≤ 1 − 2/n − f₁`), yet long enough that the faster
walker cannot stay bad across it (`2/n ≤ L·f₂`), then some opening has BOTH walkers clear.

No count, no density: the witness is the crossing index `k₀` plus an offset below `L`, so the
argument carries its own index bound.  Two walkers do NOT always clear -- `ρ = 1/2` and `ρ = 3.5`
shadow each other -- and this is exactly the region where they must. -/
theorem two_walkers (hn4 : 4 ≤ n) {f₁ c₁ f₂ c₂ : ℝ}
    (hf1 : 0 < f₁) (hf2 : 0 < f₂) (hf2h : f₂ ≤ 1/2)
    (L : ℕ) (hL1 : (L : ℝ) * f₁ ≤ 1 - 2 * (n : ℝ)⁻¹ - f₁)
    (hL2 : 2 * (n : ℝ)⁻¹ ≤ (L : ℝ) * f₂) :
    ∃ k : ℕ, (n : ℝ)⁻¹ ≤ circDist ((k : ℝ) * f₁ + c₁) ∧
             (n : ℝ)⁻¹ ≤ circDist ((k : ℝ) * f₂ + c₂) := by
  obtain ⟨k₀, N, hlo, hhi⟩ := exists_crossing (n := n) (c := c₁) hf1
  by_contra hcon
  push Not at hcon
  have hbad2 : ∀ j ≤ L, Bad n ((((k₀ + j : ℕ)) : ℝ) * f₂ + c₂) := by
    intro j hj
    have hjL : ((j : ℕ) : ℝ) ≤ ((L : ℕ) : ℝ) := by exact_mod_cast hj
    have hjf : ((j : ℕ) : ℝ) * f₁ ≤ 1 - 2 * (n : ℝ)⁻¹ - f₁ := by nlinarith
    have h1 := clear_run hn4 hf1 hlo hhi j hjf
    exact hcon (k₀ + j) h1
  have hbound := bad_run_le hn4 hf2 hf2h k₀ L hbad2
  linarith

/-! ## the case split, closed by what already exists plus the above -/

/-- **Off-lattice pairs cannot shadow.**  Contrapositive of `Flanks.shadowing_pair_cross_lattice`:
if one walker lies on the `P`-lattice and the other does NOT, some opening is clear for both.
Together with `two_walkers` this leaves only pairs on a COMMON lattice, where the verdict is
periodic in the opening index and a finite check decides it. -/
theorem not_shadow_of_off_lattice (hn4 : 4 ≤ n) {e y z : ℝ} (he0 : 0 < e) {P Q : ℕ}
    (hylat : Int.fract ((P : ℝ) * (y / e)) = 0)
    (hzlat : Int.fract ((Q : ℝ) * (z / e)) = 0)
    (hyclear : ∃ r : ℕ, (n : ℝ)⁻¹ ≤ circDist (y * flankOpening n e r))
    (hzclear : ∃ r : ℕ, (n : ℝ)⁻¹ ≤ circDist (z * flankOpening n e r))
    (hoff : Int.fract ((P : ℝ) * (z / e)) ≠ 0) :
    ∃ k : ℕ, ¬ inWay n y (flankOpening n e k) ∧ ¬ inWay n z (flankOpening n e k) := by
  by_contra hcon
  push Not at hcon
  have hshadow : ∀ k : ℕ, inWay n y (flankOpening n e k) ∨ inWay n z (flankOpening n e k) := by
    intro k
    by_cases h : inWay n y (flankOpening n e k)
    · exact Or.inl h
    · exact Or.inr (by have := hcon k h; exact this)
  exact hoff (shadowing_pair_cross_lattice hn4 he0 hylat hzlat hyclear hzclear hshadow).1

end TwoWalker
