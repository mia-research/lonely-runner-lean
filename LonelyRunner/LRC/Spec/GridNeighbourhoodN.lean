import LonelyRunner.LRC.Spec.TwoPinnerN
import LonelyRunner.LRC.Cascade.Arrangement

/-!
# The neighbourhood of every complete grid: deviations relocate the isolation, and every instant is named

2026-09-27.  A **complete grid**: whole-number speeds `u₀, …, u₇` whose residues mod 8 are all different (an AP with
extra whole laps, §4.5).  At the class-1 grid instant `1/8` every runner is lonely, laps or not (the φ(8) law; whole laps
are invisible).  Deviate every speed by `|eᵢ| ≤ ρ`.

For runner `k`, its two class-1 circle neighbours are the runners `A`, `B` whose whole-number differences satisfy
`D_A ≡ 1`, `D_B ≡ 7 (mod 8)`.  Each sits exactly one eighth away at its own opening near `1/8`:
`t_A = D_A/(8 δ_A)`, `t_B = D_B/(8 δ_B)` (`δ` the actual differences).  Each neighbour is clear on one side of its
opening, which side fixed by its sign, so `gridT` takes the opening that keeps both clear (`max`, `min`, or one of
them), and when the class-1 window is empty the mirror class-7 instant `7·t_B` or `7·t_A`, where the roles swap.  Every
other runner keeps its residue `2 … 6` slot, moved by at most `c·|δ|·2ρ`.

**Theorem** (`grid_nbhd_exists`): if `2ρ(14W + 21) ≤ 1`, `W` a bound for the whole-number differences, every runner of
the deviated grid is lonely at a named positive instant.  For the AP (`W = 7`) this recovers E45's instants.  The radius
shrinks as the laps grow: each complete grid carries its own open neighbourhood.  No `sorry`, no `native_decide`.
Evidence: `experiments/nN/redo/reference_grid_v1.out` (E44).
-/

namespace LRC.GridNbhd

open Arrangement

/-- **The witness**: the class-1 neighbours' openings, or the mirror class-7 instant. -/
noncomputable def gridT (DA DB : ℤ) (a b : ℝ) : ℝ :=
  if 0 < DA then
    (if 0 < DB then
      (if (DA : ℝ) / (8 * a) ≤ (DB : ℝ) / (8 * b) then (DA : ℝ) / (8 * a) else 7 * ((DB : ℝ) / (8 * b)))
     else max ((DA : ℝ) / (8 * a)) ((DB : ℝ) / (8 * b)))
  else
    (if 0 < DB then min ((DA : ℝ) / (8 * a)) ((DB : ℝ) / (8 * b))
     else (if (DB : ℝ) / (8 * b) ≤ (DA : ℝ) / (8 * a) then (DB : ℝ) / (8 * b) else 7 * ((DA : ℝ) / (8 * a))))

/-- **A reading at a relocated grid instant** is its grid slot plus an error of at most one eighth. -/
theorem expand {x δ c η W : ℝ} {Dx Dj : ℤ} (hc0 : 0 ≤ c) (hc7 : c ≤ 7) (hη0 : 0 ≤ η)
    (hη : η * (14 * W + 21) ≤ 1) (hx : |x - Dx| ≤ η) (hDx : 1 ≤ |(Dx : ℝ)|)
    (hδ : |δ - Dj| ≤ η) (hDj : |(Dj : ℝ)| ≤ W) :
    ∃ E : ℝ, |E| ≤ 1 ∧ δ * (c * Dx / (8 * x)) = (c * Dj + E) / 8 := by
  have hW0 : 0 ≤ W := le_trans (abs_nonneg _) hDj
  have hη1 : η ≤ 1 / 21 := by nlinarith
  have hxabs : 1 / 2 ≤ |x| := by
    have h := abs_sub_abs_le_abs_sub (Dx : ℝ) x
    rw [abs_sub_comm] at h
    linarith
  have hxpos : 0 < |x| := by linarith
  have hx0 : x ≠ 0 := fun h => by rw [h, abs_zero] at hxpos; exact lt_irrefl _ hxpos
  have hk : |(Dx : ℝ) / x - 1| ≤ 2 * η := by
    have e1 : (Dx : ℝ) / x - 1 = ((Dx : ℝ) - x) / x := by field_simp
    rw [e1, abs_div, div_le_iff₀ hxpos]
    have : |(Dx : ℝ) - x| ≤ η := by rw [abs_sub_comm]; exact hx
    nlinarith
  have hδabs : |δ| ≤ W + η := by
    have h := abs_sub_abs_le_abs_sub δ Dj
    linarith
  refine ⟨c * (δ - Dj) + c * δ * ((Dx : ℝ) / x - 1), ?_, ?_⟩
  · have h1 : |c * (δ - Dj)| ≤ 7 * η := by
      rw [abs_mul, abs_of_nonneg hc0]
      exact mul_le_mul hc7 hδ (abs_nonneg _) (by norm_num)
    have h2 : |c * δ * ((Dx : ℝ) / x - 1)| ≤ 7 * ((W + η) * (2 * η)) := by
      rw [abs_mul, abs_mul, abs_of_nonneg hc0, mul_assoc]
      exact mul_le_mul hc7 (mul_le_mul hδabs hk (abs_nonneg _) (by linarith)) (by positivity) (by norm_num)
    calc |c * (δ - Dj) + c * δ * ((Dx : ℝ) / x - 1)|
        ≤ |c * (δ - Dj)| + |c * δ * ((Dx : ℝ) / x - 1)| := abs_add_le _ _
      _ ≤ 7 * η + 7 * ((W + η) * (2 * η)) := by linarith
      _ ≤ 1 := by nlinarith
  · field_simp
    ring

/-- One chosen flank `X` (at class `c`), the other neighbour `Y` held on its side by hypothesis, the rest by `expand`. -/
theorem config {δ : Fin 8 → ℝ} {D : Fin 8 → ℤ} {k X Y : Fin 8} {c η W : ℝ} {NX NY sX sY : ℤ}
    (hXk : X ≠ k) (hYk : Y ≠ k) (hXY : X ≠ Y) (hc0 : 0 ≤ c) (hc7 : c ≤ 7) (hη0 : 0 ≤ η)
    (hη : η * (14 * W + 21) ≤ 1) (hδ : ∀ j, |δ j - D j| ≤ η) (hW : ∀ j, |(D j : ℝ)| ≤ W)
    (hDX : 1 ≤ |(D X : ℝ)|) (hδX : δ X ≠ 0)
    (hX : c * D X = 8 * NX + sX) (hsX : sX = 1 ∨ sX = 7)
    (hY : c * D Y = 8 * NY + sY) (hsY : sY = 1 ∨ sY = 7)
    (hYhi : sY = 7 → δ Y * (c * D X / (8 * δ X)) ≤ NY + 7 / 8)
    (hYlo : sY = 1 → (NY : ℝ) + 1 / 8 ≤ δ Y * (c * D X / (8 * δ X)))
    (hrest : ∀ j, j ≠ k → j ≠ X → j ≠ Y → ∃ N r : ℤ, c * D j = 8 * N + r ∧ 2 ≤ r ∧ r ≤ 6) :
    ∀ j, j ≠ k → (8 : ℝ)⁻¹ ≤ circDist (δ j * (c * D X / (8 * δ X))) := by
  intro j hjk
  by_cases hjX : j = X
  · rw [hjX]
    have hy : δ X * (c * D X / (8 * δ X)) = c * D X / 8 := by field_simp
    rw [hy, hX]
    rcases hsX with h | h <;> subst h <;>
      apply LRC.TwoPinner.clear_of_band (N := NX) <;> push_cast <;> linarith
  by_cases hjY : j = Y
  · rw [hjY]
    obtain ⟨E, hE, hy⟩ := expand hc0 hc7 hη0 hη (hδ X) hDX (hδ Y) (hW Y)
    have hE' := abs_le.mp hE
    rcases hsY with h | h
    · have hlo := hYlo h
      subst h
      apply LRC.TwoPinner.clear_of_band (N := NY) hlo
      rw [hy, hY]; push_cast; linarith
    · have hhi := hYhi h
      subst h
      apply LRC.TwoPinner.clear_of_band (N := NY) _ hhi
      rw [hy, hY]; push_cast; linarith
  · obtain ⟨N, r, hr, hr2, hr6⟩ := hrest j hjk hjX hjY
    obtain ⟨E, hE, hy⟩ := expand hc0 hc7 hη0 hη (hδ X) hDX (hδ j) (hW j)
    have hE' := abs_le.mp hE
    have hr2' : (2 : ℝ) ≤ r := by exact_mod_cast hr2
    have hr6' : (r : ℝ) ≤ 6 := by exact_mod_cast hr6
    rw [hy, hr]
    apply LRC.TwoPinner.clear_of_band (N := N) <;> push_cast <;> linarith

/-- A deviated difference has the sign of its whole-number part. -/
theorem sign_of {x η : ℝ} {D : ℤ} (hη : η < 1) (hx : |x - D| ≤ η) (hD : 1 ≤ |(D : ℝ)|) :
    (0 < D → 0 < x) ∧ (D < 0 → x < 0) := by
  have h := abs_le.mp hx
  constructor
  · intro hD0
    have : (1 : ℝ) ≤ D := by exact_mod_cast hD0
    linarith
  · intro hD0
    have : (D : ℝ) ≤ -1 := by exact_mod_cast (show D ≤ -1 by omega)
    linarith

/-- **Every other runner is clear at the named instant**, in the runner's own readings. -/
theorem readings_clear {δ : Fin 8 → ℝ} {D : Fin 8 → ℤ} {k A B : Fin 8} {η W : ℝ}
    (hAk : A ≠ k) (hBk : B ≠ k) (hAB : A ≠ B) (hη0 : 0 ≤ η) (hη : η * (14 * W + 21) ≤ 1)
    (hδ : ∀ j, |δ j - D j| ≤ η) (hW : ∀ j, |(D j : ℝ)| ≤ W)
    (hA : D A % 8 = 1) (hB : D B % 8 = 7)
    (hrest : ∀ j, j ≠ k → j ≠ A → j ≠ B → 2 ≤ D j % 8 ∧ D j % 8 ≤ 6) :
    ∀ j, j ≠ k → (8 : ℝ)⁻¹ ≤ circDist (δ j * gridT (D A) (D B) (δ A) (δ B)) := by
  have hW0 : 0 ≤ W := le_trans (abs_nonneg _) (hW k)
  have hη1 : η < 1 := by nlinarith
  -- the neighbours' whole-number parts
  set MA := D A / 8
  set MB := D B / 8
  have hDA : D A = 8 * MA + 1 := by have := Int.emod_add_ediv (D A) 8; omega
  have hDB : D B = 8 * MB + 7 := by have := Int.emod_add_ediv (D B) 8; omega
  have hDA1 : 1 ≤ |(D A : ℝ)| := by
    have : D A ≠ 0 := by omega
    have h : (1 : ℤ) ≤ |D A| := Int.one_le_abs this
    exact_mod_cast h
  have hDB1 : 1 ≤ |(D B : ℝ)| := by
    have : D B ≠ 0 := by omega
    have h : (1 : ℤ) ≤ |D B| := Int.one_le_abs this
    exact_mod_cast h
  obtain ⟨sAp, sAn⟩ := sign_of hη1 (hδ A) hDA1
  obtain ⟨sBp, sBn⟩ := sign_of hη1 (hδ B) hDB1
  have hδA0 : δ A ≠ 0 := by
    rcases lt_trichotomy (D A) 0 with h | h | h
    · exact (sAn h).ne
    · omega
    · exact (sAp h).ne'
  have hδB0 : δ B ≠ 0 := by
    rcases lt_trichotomy (D B) 0 with h | h | h
    · exact (sBn h).ne
    · omega
    · exact (sBp h).ne'
  -- residues of the rest at class 1 and class 7
  have rest1 : ∀ j, j ≠ k → j ≠ A → j ≠ B →
      ∃ N r : ℤ, (1 : ℝ) * D j = 8 * N + r ∧ 2 ≤ r ∧ r ≤ 6 := by
    intro j h1 h2 h3
    obtain ⟨hr2, hr6⟩ := hrest j h1 h2 h3
    refine ⟨D j / 8, D j % 8, ?_, hr2, hr6⟩
    have := Int.emod_add_ediv (D j) 8
    rw [one_mul]; exact_mod_cast (by omega : D j = 8 * (D j / 8) + D j % 8)
  have rest7 : ∀ j, j ≠ k → j ≠ A → j ≠ B →
      ∃ N r : ℤ, (7 : ℝ) * D j = 8 * N + r ∧ 2 ≤ r ∧ r ≤ 6 := by
    intro j h1 h2 h3
    obtain ⟨hr2, hr6⟩ := hrest j h1 h2 h3
    refine ⟨7 * (D j / 8) + D j % 8 - 1, 8 - D j % 8, ?_, by omega, by omega⟩
    have := Int.emod_add_ediv (D j) 8
    exact_mod_cast (by omega : 7 * D j = 8 * (7 * (D j / 8) + D j % 8 - 1) + (8 - D j % 8))
  -- the two openings
  set tA := (D A : ℝ) / (8 * δ A) with htA
  set tB := (D B : ℝ) / (8 * δ B) with htB
  have eA : δ A * tA = D A / 8 := by rw [htA]; field_simp
  have eB : δ B * tB = D B / 8 := by rw [htB]; field_simp
  have rA : (D A : ℝ) = 8 * (MA : ℝ) + 1 := by
    have h := congrArg (fun z : ℤ => (z : ℝ)) hDA; push_cast at h; linarith
  have rB : (D B : ℝ) = 8 * (MB : ℝ) + 7 := by
    have h := congrArg (fun z : ℤ => (z : ℝ)) hDB; push_cast at h; linarith
  have cA1 : (1 : ℝ) * D A = 8 * ((MA : ℤ) : ℝ) + ((1 : ℤ) : ℝ) := by push_cast; rw [rA]; ring
  have cB1 : (1 : ℝ) * D B = 8 * ((MB : ℤ) : ℝ) + ((7 : ℤ) : ℝ) := by push_cast; rw [rB]; ring
  have cA7 : (7 : ℝ) * D A = 8 * ((7 * MA : ℤ) : ℝ) + ((7 : ℤ) : ℝ) := by
    push_cast; rw [rA]; ring
  have cB7 : (7 : ℝ) * D B = 8 * ((7 * MB + 6 : ℤ) : ℝ) + ((1 : ℤ) : ℝ) := by
    push_cast; rw [rB]; ring
  have t1A : tA = 1 * D A / (8 * δ A) := by rw [htA, one_mul]
  have t1B : tB = 1 * D B / (8 * δ B) := by rw [htB, one_mul]
  have t7A : 7 * tA = 7 * D A / (8 * δ A) := by rw [htA]; ring
  have t7B : 7 * tB = 7 * D B / (8 * δ B) := by rw [htB]; ring
  have hDAr : (D A : ℝ) / 8 = MA + 1 / 8 := by rw [rA]; ring
  have hDBr : (D B : ℝ) / 8 = MB + 7 / 8 := by rw [rB]; ring
  intro j hjk
  unfold gridT
  rw [← htA, ← htB]
  split_ifs with hA0 hB0 hle hB0' hle'
  -- (+,+), t_A ≤ t_B: flank A at class 1
  · rw [t1A]
    refine config hAk hBk hAB (by norm_num) (by norm_num) hη0 hη hδ hW hDA1 hδA0 cA1 (Or.inl rfl)
      cB1 (Or.inr rfl) (fun _ => ?_) (fun h => by norm_num at h) (fun j h1 h2 h3 => rest1 j h1 h2 h3) j hjk
    rw [← t1A]
    have := mul_le_mul_of_nonneg_left hle (sBp hB0).le
    rw [eB, hDBr] at this; exact this
  -- (+,+), t_B < t_A: flank B at class 7
  · rw [t7B]
    refine config hBk hAk (Ne.symm hAB) (by norm_num) (by norm_num) hη0 hη hδ hW hDB1 hδB0 cB7 (Or.inl rfl)
      cA7 (Or.inr rfl) (fun _ => ?_) (fun h => by norm_num at h) (fun j h1 h2 h3 => rest7 j h1 h3 h2) j hjk
    rw [← t7B]
    have hlt : tB ≤ tA := le_of_lt (not_le.mp hle)
    have := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlt (by norm_num : (0 : ℝ) ≤ 7)) (sAp hA0).le
    have e7 : δ A * (7 * tA) = 7 * (D A / 8) := by rw [← eA]; ring
    rw [e7, hDAr] at this; push_cast; linarith
  -- (+,−): max
  · rcases le_total tB tA with h | h
    · rw [max_eq_left h, t1A]
      refine config hAk hBk hAB (by norm_num) (by norm_num) hη0 hη hδ hW hDA1 hδA0 cA1 (Or.inl rfl)
        cB1 (Or.inr rfl) (fun _ => ?_) (fun h => by norm_num at h) (fun j h1 h2 h3 => rest1 j h1 h2 h3) j hjk
      rw [← t1A]
      have hBneg : δ B < 0 := sBn (by omega)
      have := mul_le_mul_of_nonpos_left h hBneg.le
      rw [eB, hDBr] at this; exact this
    · rw [max_eq_right h, t1B]
      refine config hBk hAk (Ne.symm hAB) (by norm_num) (by norm_num) hη0 hη hδ hW hDB1 hδB0 cB1 (Or.inr rfl)
        cA1 (Or.inl rfl) (fun h => by norm_num at h) (fun _ => ?_) (fun j h1 h2 h3 => rest1 j h1 h3 h2) j hjk
      rw [← t1B]
      have := mul_le_mul_of_nonneg_left h (sAp hA0).le
      rw [eA, hDAr] at this; exact this
  -- (−,+): min
  · rcases le_total tA tB with h | h
    · rw [min_eq_left h, t1A]
      refine config hAk hBk hAB (by norm_num) (by norm_num) hη0 hη hδ hW hDA1 hδA0 cA1 (Or.inl rfl)
        cB1 (Or.inr rfl) (fun _ => ?_) (fun h => by norm_num at h) (fun j h1 h2 h3 => rest1 j h1 h2 h3) j hjk
      rw [← t1A]
      have := mul_le_mul_of_nonneg_left h (sBp hB0').le
      rw [eB, hDBr] at this; exact this
    · rw [min_eq_right h, t1B]
      refine config hBk hAk (Ne.symm hAB) (by norm_num) (by norm_num) hη0 hη hδ hW hDB1 hδB0 cB1 (Or.inr rfl)
        cA1 (Or.inl rfl) (fun h => by norm_num at h) (fun _ => ?_) (fun j h1 h2 h3 => rest1 j h1 h3 h2) j hjk
      rw [← t1B]
      have hAneg : δ A < 0 := sAn (by omega)
      have := mul_le_mul_of_nonpos_left h hAneg.le
      rw [eA, hDAr] at this; exact this
  -- (−,−), t_B ≤ t_A: flank B at class 1
  · rw [t1B]
    refine config hBk hAk (Ne.symm hAB) (by norm_num) (by norm_num) hη0 hη hδ hW hDB1 hδB0 cB1 (Or.inr rfl)
      cA1 (Or.inl rfl) (fun h => by norm_num at h) (fun _ => ?_) (fun j h1 h2 h3 => rest1 j h1 h3 h2) j hjk
    rw [← t1B]
    have hAneg : δ A < 0 := sAn (by omega)
    have := mul_le_mul_of_nonpos_left hle' hAneg.le
    rw [eA, hDAr] at this; exact this
  -- (−,−), t_A < t_B: flank A at class 7
  · rw [t7A]
    refine config hAk hBk hAB (by norm_num) (by norm_num) hη0 hη hδ hW hDA1 hδA0 cA7 (Or.inr rfl)
      cB7 (Or.inl rfl) (fun h => by norm_num at h) (fun _ => ?_) (fun j h1 h2 h3 => rest7 j h1 h2 h3) j hjk
    rw [← t7A]
    have hlt : tA ≤ tB := le_of_lt (not_le.mp hle')
    have hBneg : δ B < 0 := sBn (by omega)
    have := mul_le_mul_of_nonpos_left (mul_le_mul_of_nonneg_left hlt (by norm_num : (0 : ℝ) ≤ 7)) hBneg.le
    have e7 : δ B * (7 * tB) = 7 * (D B / 8) := by rw [← eB]; ring
    rw [e7, hDBr] at this; push_cast; linarith

/-- **The two class-1 neighbours exist** in a complete grid: the residues of the eight differences are `0 … 7`. -/
theorem exists_nbrs (u : Fin 8 → ℤ) (hres : ∀ i j, u i % 8 = u j % 8 → i = j) (k : Fin 8) :
    ∃ A B : Fin 8, (u A - u k) % 8 = 1 ∧ (u B - u k) % 8 = 7 := by
  classical
  set g : Fin 8 → ℤ := fun j => (u j - u k) % 8
  have hinj : Function.Injective g := fun j j' h => hres j j' (by simp only [g] at h; omega)
  have hsub : Finset.univ.image g ⊆ Finset.Ico (0 : ℤ) 8 := by
    intro x hx
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hx
    simp only [Finset.mem_Ico, g]
    omega
  have hcard : (Finset.univ.image g).card = 8 := by
    rw [Finset.card_image_of_injective _ hinj]; simp
  have heq : Finset.univ.image g = Finset.Ico 0 8 :=
    Finset.eq_of_subset_of_card_le hsub (by rw [hcard]; simp)
  have h1 : (1 : ℤ) ∈ Finset.univ.image g := by rw [heq]; simp
  have h7 : (7 : ℤ) ∈ Finset.univ.image g := by rw [heq]; simp
  obtain ⟨A, -, hA⟩ := Finset.mem_image.mp h1
  obtain ⟨B, -, hB⟩ := Finset.mem_image.mp h7
  exact ⟨A, B, hA, hB⟩

/-- The deviated grid. -/
noncomputable def gridV (c0 : ℝ) (u : Fin 8 → ℤ) (e : Fin 8 → ℝ) (i : Fin 8) : ℝ := c0 + (u i : ℝ) + e i

/-- **Every runner of the deviated grid is lonely at the named instant**, its class-1 neighbours `A`, `B` given. -/
theorem grid_nbhd_lonely (c0 : ℝ) (u : Fin 8 → ℤ) (e : Fin 8 → ℝ) (ρ W : ℝ)
    (hres : ∀ i j, u i % 8 = u j % 8 → i = j) (hW : ∀ i j, |((u i - u j : ℤ) : ℝ)| ≤ W)
    (hρ0 : 0 ≤ ρ) (hρ : 2 * ρ * (14 * W + 21) ≤ 1) (he : ∀ i, |e i| ≤ ρ)
    (k A B : Fin 8) (hA : (u A - u k) % 8 = 1) (hB : (u B - u k) % 8 = 7) :
    LonelyAt (gridV c0 u e) k
      (gridT (u A - u k) (u B - u k) (gridV c0 u e A - gridV c0 u e k) (gridV c0 u e B - gridV c0 u e k)) := by
  have hAk : A ≠ k := by intro h; rw [h, sub_self] at hA; norm_num at hA
  have hBk : B ≠ k := by intro h; rw [h, sub_self] at hB; norm_num at hB
  have hAB : A ≠ B := by intro h; rw [h] at hA; omega
  have hδ : ∀ j, |(gridV c0 u e j - gridV c0 u e k) - ((u j - u k : ℤ) : ℝ)| ≤ 2 * ρ := by
    intro j
    have : (gridV c0 u e j - gridV c0 u e k) - ((u j - u k : ℤ) : ℝ) = e j - e k := by
      unfold gridV; push_cast; ring
    rw [this]
    have a1 := abs_le.mp (he j); have a2 := abs_le.mp (he k)
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hrest : ∀ j, j ≠ k → j ≠ A → j ≠ B → 2 ≤ (u j - u k) % 8 ∧ (u j - u k) % 8 ≤ 6 := by
    intro j h1 h2 h3
    have n1 : u j % 8 ≠ u k % 8 := fun h => h1 (hres _ _ h)
    have n2 : u j % 8 ≠ u A % 8 := fun h => h2 (hres _ _ h)
    have n3 : u j % 8 ≠ u B % 8 := fun h => h3 (hres _ _ h)
    omega
  intro j hjk
  rw [sep_eq]
  exact readings_clear (δ := fun j => gridV c0 u e j - gridV c0 u e k) (D := fun j => u j - u k)
    hAk hBk hAB (by linarith) (by linarith) hδ (fun j => hW j k) hA hB hrest j hjk

theorem gridT_pos {DA DB : ℤ} {a b : ℝ} (hA : (0 < DA ∧ 0 < a) ∨ (DA < 0 ∧ a < 0))
    (hB : (0 < DB ∧ 0 < b) ∨ (DB < 0 ∧ b < 0)) : 0 < gridT DA DB a b := by
  have tA : 0 < (DA : ℝ) / (8 * a) := by
    rcases hA with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact div_pos (by exact_mod_cast h1) (by linarith)
    · exact div_pos_of_neg_of_neg (by exact_mod_cast h1) (by linarith)
  have tB : 0 < (DB : ℝ) / (8 * b) := by
    rcases hB with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact div_pos (by exact_mod_cast h1) (by linarith)
    · exact div_pos_of_neg_of_neg (by exact_mod_cast h1) (by linarith)
  unfold gridT
  split_ifs
  all_goals first | exact tA | exact tB | linarith | exact lt_max_of_lt_left tA | exact lt_min tA tB

/-- **The complete grid's neighbourhood, as existence**: every runner has a positive lonely instant. -/
theorem grid_nbhd_exists (c0 : ℝ) (u : Fin 8 → ℤ) (e : Fin 8 → ℝ) (ρ W : ℝ)
    (hres : ∀ i j, u i % 8 = u j % 8 → i = j) (hW : ∀ i j, |((u i - u j : ℤ) : ℝ)| ≤ W)
    (hρ0 : 0 ≤ ρ) (hρ : 2 * ρ * (14 * W + 21) ≤ 1) (he : ∀ i, |e i| ≤ ρ) (k : Fin 8) :
    ∃ t : ℝ, 0 < t ∧ LonelyAt (gridV c0 u e) k t := by
  obtain ⟨A, B, hA, hB⟩ := exists_nbrs u hres k
  refine ⟨_, ?_, grid_nbhd_lonely c0 u e ρ W hres hW hρ0 hρ he k A B hA hB⟩
  have hW0 : 0 ≤ W := le_trans (abs_nonneg _) (hW k k)
  have hη1 : 2 * ρ < 1 := by nlinarith
  have sgn : ∀ X : Fin 8, (u X - u k) % 8 ≠ 0 →
      (0 < u X - u k ∧ 0 < gridV c0 u e X - gridV c0 u e k) ∨
        (u X - u k < 0 ∧ gridV c0 u e X - gridV c0 u e k < 0) := by
    intro X hX
    have hd : (gridV c0 u e X - gridV c0 u e k) - ((u X - u k : ℤ) : ℝ) = e X - e k := by
      unfold gridV; push_cast; ring
    have a1 := abs_le.mp (he X); have a2 := abs_le.mp (he k)
    have hb : -(2 * ρ) ≤ e X - e k ∧ e X - e k ≤ 2 * ρ := ⟨by linarith, by linarith⟩
    rcases lt_trichotomy (u X - u k) 0 with h | h | h
    · right; refine ⟨h, ?_⟩
      have : ((u X - u k : ℤ) : ℝ) ≤ -1 := by exact_mod_cast (show u X - u k ≤ -1 by omega)
      linarith
    · exact absurd (by rw [h]; rfl) hX
    · left; refine ⟨h, ?_⟩
      have : (1 : ℝ) ≤ ((u X - u k : ℤ) : ℝ) := by exact_mod_cast (show 1 ≤ u X - u k by omega)
      linarith
  exact gridT_pos (sgn A (by rw [hA]; norm_num)) (sgn B (by rw [hB]; norm_num))

end LRC.GridNbhd
