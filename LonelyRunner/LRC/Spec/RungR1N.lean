import LonelyRunner.LRC.Spec.MirrorCentreN

/-!
# Rung R1: a ladder rung plus the deviation forced by its multiples' own `d_min`

2026-09-26 (running log E88–E89).  Owner: *"any speed is just AP/grid and a deviation that is forced by `d_min`."*

At a ladder rung `t₀ = a/q` the readings divisible by `q` sit on whole laps (in the subject's slot) and every other
reading sits at a nonzero multiple of `1/q`.  Deviate by the multiples' own bound `1/(8m)`, `m` the least of them: the
multiples then sit exactly where they sit at their own first instant, a problem with fewer runners, and every other
reading rides from its rung position within its margin.

* `rung_r1_forward` / `rung_r1_backward`: the general form, at any instant `t₀` of any arrangement.  Readings on whole
  laps at `t₀` with `m ≤ w ≤ 7m` (R1 among the multiples), and every other reading at `K + ρ` with room
  `ρ + w/(8m) ≤ 7/8` (forward) or `ρ − w/(8m) ≥ 1/8` (backward), with `ρ ∈ [1/8, 7/8]`.
* `half_lap_r1`: whole-number readings; the evens within `[m, 7m]` (`m` the least even) and every odd reading at most
  `3m` give isolation at `1/2 + 1/(8m)`.
* `rung_r1_nat`: whole-number readings at any rung `a/q`, `2 ≤ q ≤ 8`.

In the exhaustive map (E88) the rung-R1 instants isolate 231,052 of the 231,062 reading sets up to 32 that the other
proved lemmas leave.  Everything here is proved; no `sorry`, no `native_decide`.
-/

namespace LRC.RungR1

open LRC.MirrorCentre

/-- **Rung R1, forward.** -/
theorem rung_r1_forward {ι : Type*} {s : Finset ι} {w : ι → ℝ} {t₀ m : ℝ} (hm : 0 < m)
    (h : ∀ j ∈ s, (∃ K : ℤ, w j * t₀ = K ∧ m ≤ w j ∧ w j ≤ 7 * m) ∨
      (∃ K : ℤ, ∃ ρ : ℝ, w j * t₀ = K + ρ ∧ 1 / 8 ≤ ρ ∧ 0 ≤ w j ∧ ρ + w j / (8 * m) ≤ 7 / 8)) :
    ∀ j ∈ s, (8 : ℝ)⁻¹ ≤ circDist (w j * (t₀ + 1 / (8 * m))) := by
  intro j hj
  rw [show (8 : ℝ)⁻¹ = 1 / 8 by norm_num]
  have hsplit : w j * (t₀ + 1 / (8 * m)) = w j * t₀ + w j / (8 * m) := by field_simp
  rcases h j hj with ⟨K, hK, h1, h2⟩ | ⟨K, ρ, hK, h1, h0, h2⟩
  · have a1 : 1 / 8 ≤ w j / (8 * m) := by rw [le_div_iff₀ (by positivity)]; linarith
    have a2 : w j / (8 * m) ≤ 7 / 8 := by rw [div_le_iff₀ (by positivity)]; linarith
    exact circDist_ge_of_window (m := K) (by rw [hsplit, hK]; linarith) (by rw [hsplit, hK]; linarith) (by norm_num)
  · have a0 : 0 ≤ w j / (8 * m) := by positivity
    exact circDist_ge_of_window (m := K) (by rw [hsplit, hK]; linarith) (by rw [hsplit, hK]; linarith) (by norm_num)

/-- **Rung R1, backward.** -/
theorem rung_r1_backward {ι : Type*} {s : Finset ι} {w : ι → ℝ} {t₀ m : ℝ} (hm : 0 < m)
    (h : ∀ j ∈ s, (∃ K : ℤ, w j * t₀ = K ∧ m ≤ w j ∧ w j ≤ 7 * m) ∨
      (∃ K : ℤ, ∃ ρ : ℝ, w j * t₀ = K + ρ ∧ ρ ≤ 7 / 8 ∧ 0 ≤ w j ∧ 1 / 8 ≤ ρ - w j / (8 * m))) :
    ∀ j ∈ s, (8 : ℝ)⁻¹ ≤ circDist (w j * (t₀ - 1 / (8 * m))) := by
  intro j hj
  rw [show (8 : ℝ)⁻¹ = 1 / 8 by norm_num]
  have hsplit : w j * (t₀ - 1 / (8 * m)) = w j * t₀ - w j / (8 * m) := by field_simp
  rcases h j hj with ⟨K, hK, h1, h2⟩ | ⟨K, ρ, hK, h1, h0, h2⟩
  · have a1 : 1 / 8 ≤ w j / (8 * m) := by rw [le_div_iff₀ (by positivity)]; linarith
    have a2 : w j / (8 * m) ≤ 7 / 8 := by rw [div_le_iff₀ (by positivity)]; linarith
    refine circDist_ge_of_window (m := K - 1) ?_ ?_ (by norm_num) <;> push_cast <;> rw [hsplit, hK] <;> linarith
  · have a0 : 0 ≤ w j / (8 * m) := by positivity
    exact circDist_ge_of_window (m := K) (by rw [hsplit, hK]; linarith) (by rw [hsplit, hK]; linarith) (by norm_num)

/-- **The half lap.**  Whole-number readings: if the evens lie in `[m, 7m]` for some `m > 0` and every odd reading is
at most `3m`, the subject is isolated at `1/2 + 1/(8m)`. -/
theorem half_lap_r1 {T : Finset ℕ} {m : ℕ} (hm0 : 0 < m)
    (hev : ∀ d ∈ T, 2 ∣ d → m ≤ d ∧ d ≤ 7 * m) (hodd : ∀ d ∈ T, ¬ 2 ∣ d → d ≤ 3 * m) :
    ∀ d ∈ T, (8 : ℝ)⁻¹ ≤ circDist ((d : ℝ) * (1 / 2 + 1 / (8 * (m : ℝ)))) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm0
  refine rung_r1_forward (s := T) (w := fun d => (d : ℝ)) (t₀ := 1 / 2) (m := (m : ℝ)) hmR ?_
  intro d hd
  by_cases h2 : 2 ∣ d
  · left
    obtain ⟨k, rfl⟩ := h2
    obtain ⟨h1, h7⟩ := hev _ hd ⟨k, rfl⟩
    refine ⟨k, by dsimp only; push_cast; ring, by dsimp only; exact_mod_cast h1, by dsimp only; exact_mod_cast h7⟩
  · right
    have hodd' : d % 2 = 1 := by omega
    refine ⟨((d / 2 : ℕ) : ℤ), 1 / 2, ?_, by norm_num, by positivity, ?_⟩
    · have : (d : ℝ) = 2 * ((d / 2 : ℕ) : ℝ) + 1 := by
        have := Nat.div_add_mod d 2; rw [hodd'] at this; exact_mod_cast this.symm
      dsimp only; rw [this]; simp only [Int.cast_natCast]; ring
    · have h3 : (d : ℝ) ≤ 3 * m := by exact_mod_cast hodd d hd h2
      dsimp only
      rw [show (1 : ℝ) / 2 + (d : ℝ) / (8 * m) = 1 / 2 + (d : ℝ) / (8 * m) from rfl]
      have : (d : ℝ) / (8 * m) ≤ 3 / 8 := by rw [div_le_iff₀ (by positivity)]; linarith
      linarith

/-- **Every rung.**  Whole-number readings at a rung `a/q`, `2 ≤ q ≤ 8`, `q ∤ a·u` for the non-multiples: the multiples
of `q` in `[m, 7m]` (`m` the least), and every other reading with `(a·u mod q)/q + u/(8m) ≤ 7/8`, give isolation at
`a/q + 1/(8m)`. -/
theorem rung_r1_nat {T : Finset ℕ} {q a m : ℕ} (hq2 : 2 ≤ q) (hq8 : q ≤ 8) (hm0 : 0 < m)
    (hmul : ∀ d ∈ T, q ∣ d → m ≤ d ∧ d ≤ 7 * m)
    (hoff : ∀ d ∈ T, ¬ q ∣ d → (a * d) % q ≠ 0 ∧
      (((a * d) % q : ℕ) : ℝ) / q + (d : ℝ) / (8 * m) ≤ 7 / 8) :
    ∀ d ∈ T, (8 : ℝ)⁻¹ ≤ circDist ((d : ℝ) * ((a : ℝ) / q + 1 / (8 * (m : ℝ)))) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm0
  have hqR : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  refine rung_r1_forward (s := T) (w := fun d => (d : ℝ)) (t₀ := (a : ℝ) / q) (m := (m : ℝ)) hmR ?_
  intro d hd
  by_cases hqd : q ∣ d
  · left
    obtain ⟨k, rfl⟩ := hqd
    obtain ⟨h1, h7⟩ := hmul _ hd ⟨k, rfl⟩
    refine ⟨((k * a : ℕ) : ℤ), ?_, by dsimp only; exact_mod_cast h1, by dsimp only; exact_mod_cast h7⟩
    dsimp only; push_cast; field_simp
  · right
    obtain ⟨hr0, hroom⟩ := hoff d hd hqd
    refine ⟨(((a * d) / q : ℕ) : ℤ), (((a * d) % q : ℕ) : ℝ) / q, ?_, ?_, by positivity, ?_⟩
    · have hdiv : ((a * d : ℕ) : ℝ) = q * (((a * d) / q : ℕ) : ℝ) + (((a * d) % q : ℕ) : ℝ) := by
        exact_mod_cast (Nat.div_add_mod (a * d) q).symm
      dsimp only
      have : (d : ℝ) * ((a : ℝ) / q) = ((a * d : ℕ) : ℝ) / q := by push_cast; field_simp
      rw [this, hdiv]; simp only [Int.cast_natCast]; field_simp
    · have hr1 : (1 : ℝ) ≤ (((a * d) % q : ℕ) : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hr0
      have hq8R : (q : ℝ) ≤ 8 := by exact_mod_cast hq8
      rw [le_div_iff₀ hqR]; nlinarith
    · exact hroom

end LRC.RungR1
