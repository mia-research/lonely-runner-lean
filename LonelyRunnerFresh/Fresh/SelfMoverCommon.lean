import Mathlib
import Fresh.Framework
import Fresh.Localisation
import Fresh.Cascade
import Fresh.OneMoverA
import Fresh.OneMoverS1
import Fresh.CascadeLanding
import Fresh.CascadeLandingG

/-!
# The subject moving near another runner: shared lemmas

Written 2026-10-22.  New file.  The subject `k` of the AP `c + i` is at `x = c + i0 + s δ` (`s = ±1`, `δ > 0` small) and the other
seven runners stay at `c + i`.  Every other runner's signed disparity is `D_i = (i - i0) - s δ`.

Chain method (no covering search): the cascade's own path is a chain of zones.  Zone `j` is the set of instants where the reading
`d_j = |D_{i_j}|` is within `1/8` of the integer `M_j`.  If `lo_{j+1} < hi_j` (the next zone contains the previous zone's upper end)
and the first zone contains `1/(8δ)`, the union of the zones covers `[1/(8δ), hi_n)`, so no instant there is lonely;
`hi_n = (M_n + 1/8)/d_n` is lonely when every reading is clear there.  This file proves the three lemmas the chains use
(`zone_lo`, `zone_hi`, `clear_at_end`) and the link from `FirstIso` to the cascade (`selfland_of_first`).  Grades: [L].
-/

open Classical

namespace Fresh.OneMover

open Fresh

/-- The subject `k` at `c + i0 + s δ`, the others on the AP. -/
noncomputable def selfV (c : ℝ) (i0 : ℕ) (s δ : ℝ) (k : Fin 8) : Fin 8 → ℝ :=
  oneMover c (c + (i0 : ℝ) + s * δ) k

theorem selfV_diff (c : ℝ) (i0 : ℕ) (s δ : ℝ) (k i : Fin 8) (hik : i ≠ k) :
    selfV c i0 s δ k i - selfV c i0 s δ k k = ((i : ℕ) : ℝ) - (i0 : ℝ) - s * δ := by
  have h1 : selfV c i0 s δ k i = c + ((i : ℕ) : ℝ) := by simp [selfV, oneMover, hik]
  have h2 : selfV c i0 s δ k k = c + (i0 : ℝ) + s * δ := by simp [selfV, oneMover]
  rw [h1, h2]; ring

/-- The first isolation instant of `v` for the subject `k`. -/
-- STANDING: DEFINITION
def FirstIso (v : Fin 8 → ℝ) (k : Fin 8) (T : ℝ) : Prop :=
  IsolatedAt v k T ∧ ∀ s : ℝ, 0 < s → IsolatedAt v k s → T ≤ s

/-- A reading `D = ε d` (`ε = ±1`, `d > 0`) is in the way when `d s` is within `1/8` of the integer `M`. -/
theorem inway_signed {D d s ε : ℝ} (hD : D = ε * d) (hε : ε = 1 ∨ ε = -1) (M : ℤ)
    (h1 : (M : ℝ) - 1 / 8 < d * s) (h2 : d * s < (M : ℝ) + 1 / 8) : distInt (D * s) < 1 / 8 := by
  have h := inWay_of_window M h1 h2
  rcases hε with rfl | rfl
  · rw [hD]; simpa using h
  · rw [hD]
    have : (-1 * d) * s = -(d * s) := by ring
    rw [this, Fresh.Localisation.distInt_neg]; exact h

/-- The reading `D = ε d` is clear when `d s` lies in a clear window. -/
theorem clear_signed {D d s ε : ℝ} (hD : D = ε * d) (hε : ε = 1 ∨ ε = -1) (W : ℤ)
    (h1 : (W : ℝ) + 1 / 8 ≤ d * s) (h2 : d * s ≤ (W : ℝ) + 7 / 8) : (1 / 8 : ℝ) ≤ distInt (D * s) := by
  have h := Fresh.Localisation.clear_of_window W h1 h2
  rcases hε with rfl | rfl
  · rw [hD]; simpa using h
  · rw [hD]
    have : (-1 * d) * s = -(d * s) := by ring
    rw [this, Fresh.Localisation.distInt_neg]; exact h

/-- Lower end of the next zone: `s ≥ upper end of the previous zone` and the overlap inequality give `b < d' s`. -/
theorem zone_lo {d d' s a b : ℝ} (hd : 0 < d) (hd' : 0 < d') (hs : a ≤ d * s) (hab : d * b < d' * a) :
    b < d' * s := by
  by_contra h
  push Not at h
  have h1 : d * (d' * s) ≤ d * b := mul_le_mul_of_nonneg_left h hd.le
  have h2 : d' * a ≤ d' * (d * s) := mul_le_mul_of_nonneg_left hs hd'.le
  nlinarith

/-- Upper end: `s` below the zone's upper end `(M + 1/8)/d`. -/
theorem zone_hi {d s M : ℝ} (hd : 0 < d) (hs : s < (M + 1 / 8) / d) : d * s < M + 1 / 8 := by
  rw [lt_div_iff₀ hd] at hs
  linarith

theorem le_of_div {d s M : ℝ} (hd : 0 < d) (hs : (M + 1 / 8) / d ≤ s) : M + 1 / 8 ≤ d * s := by
  rw [div_le_iff₀ hd] at hs
  linarith

/-- The reading `d'` is clear at the upper end `(M + 1/8)/d` of a zone. -/
theorem clear_at_end {d d' M : ℝ} (hd : 0 < d) (W : ℤ) (h1 : ((W : ℝ) + 1 / 8) * d ≤ d' * (M + 1 / 8))
    (h2 : d' * (M + 1 / 8) ≤ ((W : ℝ) + 7 / 8) * d) : (1 / 8 : ℝ) ≤ distInt (d' * ((M + 1 / 8) / d)) := by
  have e : d' * ((M + 1 / 8) / d) = (d' * (M + 1 / 8)) / d := by ring
  rw [e]
  exact clear_div hd W h1 h2

/-- A reading in the way before `1/(8δ)`: for `0 < s < 1/(8δ)` the nearest runner's reading `δ s < 1/8` is in the way. -/
theorem inway_before {δ s : ℝ} (hδ : 0 < δ) (hs0 : 0 < s) (hs : s < 1 / (8 * δ)) : distInt (δ * s) < 1 / 8 := by
  apply inWay_of_window 0
  · push_cast; nlinarith
  · push_cast
    rw [lt_div_iff₀ (by positivity)] at hs
    nlinarith

theorem delta_small {δ τ0 : ℝ} {N0 N : ℕ} (hδ : δ * ((N0 : ℝ) + τ0) = 1 / 8) (hτ : 0 ≤ τ0)
    (hN : N ≤ N0) (hNpos : 0 < N) : δ ≤ 1 / (8 * (N : ℝ)) := by
  have hNr : (N : ℝ) ≤ N0 := by exact_mod_cast hN
  have hNp : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hδp : 0 < δ := by
    by_contra h
    push Not at h
    have : δ * ((N0 : ℝ) + τ0) ≤ 0 := by
      apply mul_nonpos_of_nonpos_of_nonneg h
      positivity
    linarith
  rw [le_div_iff₀ (by positivity)]
  nlinarith


theorem selfV_reading_ne (c : ℝ) (i0 : ℕ) (s δ : ℝ) (hs : s = 1 ∨ s = -1) (hδ : 0 < δ) (hδ1 : δ < 1)
    (k i : Fin 8) (hik : i ≠ k) : selfV c i0 s δ k i - selfV c i0 s δ k k ≠ 0 := by
  rw [selfV_diff c i0 s δ k i hik]
  intro h
  by_cases hii : (i : ℕ) = i0
  · rw [hii] at h
    have : s * δ = 0 := by linarith
    rcases hs with rfl | rfl <;> linarith
  · have hne : ((i : ℕ) : ℝ) ≠ (i0 : ℝ) := by exact_mod_cast hii
    have habs : (1 : ℝ) ≤ |((i : ℕ) : ℝ) - (i0 : ℝ)| := by
      rcases lt_or_gt_of_ne hii with hlt | hgt
      · have : ((i : ℕ) : ℝ) + 1 ≤ (i0 : ℝ) := by exact_mod_cast hlt
        rw [abs_of_neg (by linarith)]; linarith
      · have : (i0 : ℝ) + 1 ≤ ((i : ℕ) : ℝ) := by exact_mod_cast hgt
        rw [abs_of_pos (by linarith)]; linarith
    have h2 : ((i : ℕ) : ℝ) - (i0 : ℝ) = s * δ := by linarith
    rw [h2] at habs
    rcases hs with rfl | rfl <;> simp [abs_of_pos hδ] at habs <;> linarith

/-- From the first isolation instant to the cascade (start `1/(8δ)`, `δ` the nearest runner's reading). -/
theorem selfland_of_first (c : ℝ) (i0 : ℕ) (hi0 : i0 < 8) (s δ : ℝ) (hs : s = 1 ∨ s = -1) (k : Fin 8)
    (hk : (⟨i0, hi0⟩ : Fin 8) ≠ k) (hδ : 0 < δ) (hδ1 : δ < 1) (T : ℝ) (hT : 0 < T)
    (hF : FirstIso (selfV c i0 s δ k) k T) :
    (∃ seq : ℕ → ℝ, seq 0 = 1 / (8 * δ) ∧
      (∀ n, IsMove (disparitySet (selfV c i0 s δ k) k) (seq n) (seq (n + 1))) ∧ ∃ N, seq (N + 1) = seq N) ∧
    ∀ seq : ℕ → ℝ, seq 0 = 1 / (8 * δ) →
      (∀ n, IsMove (disparitySet (selfV c i0 s δ k) k) (seq n) (seq (n + 1))) → ∀ N, seq (N + 1) = seq N → seq N = T := by
  set v := selfV c i0 s δ k with hv
  have hpos : ∀ d ∈ disparitySet v k, 0 < d := by
    intro d hd
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hd
    have hik : i ≠ k := (Finset.mem_erase.mp hi).1
    exact abs_pos.mpr (selfV_reading_ne c i0 s δ hs hδ hδ1 k i hik)
  have ham : δ ∈ disparitySet v k := by
    refine Finset.mem_image.mpr ⟨⟨i0, hi0⟩, Finset.mem_erase.mpr ⟨hk, Finset.mem_univ _⟩, ?_⟩
    rw [hv, selfV_diff c i0 s δ k ⟨i0, hi0⟩ hk]
    simp only [sub_self, zero_sub]
    rcases hs with rfl | rfl <;> simp [abs_of_pos hδ]
  have hfirst : IsFirst (disparitySet v k) T :=
    ⟨(Fresh.Cascade.isolatedAt_iff_lonelyAt v k T).1 hF.1,
      fun s' hs' hl => hF.2 s' hs' ((Fresh.Cascade.isolatedAt_iff_lonelyAt v k s').2 hl)⟩
  exact cascade_landsG hpos ham hT hfirst

#print axioms selfland_of_first


theorem iso_iff_nat (c : ℝ) (i0 : ℕ) (s δ : ℝ) (k : Fin 8) (t : ℝ) :
    IsolatedAt (selfV c i0 s δ k) k t ↔
      ∀ i : ℕ, i < 8 → i ≠ (k : ℕ) → (1 / 8 : ℝ) ≤ distInt ((((i : ℕ) : ℝ) - (i0 : ℝ) - s * δ) * t) := by
  constructor
  · intro h i hi hik
    have hne : (⟨i, hi⟩ : Fin 8) ≠ k := fun e => hik (by simpa using congrArg Fin.val e)
    have := h ⟨i, hi⟩ hne
    rw [selfV_diff c i0 s δ k ⟨i, hi⟩ hne] at this
    simpa using this
  · intro h i hik
    have := h i i.isLt (fun e => hik (Fin.ext e))
    rw [selfV_diff c i0 s δ k i hik]
    exact this

theorem clear_of_abs {D d T ε : ℝ} (hD : D = ε * d) (hε : ε = 1 ∨ ε = -1) (h : (1 / 8 : ℝ) ≤ distInt (d * T)) :
    (1 / 8 : ℝ) ≤ distInt (D * T) := by
  rcases hε with rfl | rfl
  · rw [hD]; simpa using h
  · rw [hD]
    have : (-1 * d) * T = -(d * T) := by ring
    rw [this, Fresh.Localisation.distInt_neg]; exact h

#print axioms zone_lo
#print axioms clear_at_end
#print axioms inway_before

end Fresh.OneMover
