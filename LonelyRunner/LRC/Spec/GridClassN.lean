import LonelyRunner.LRC.Spec.GridNeighbourhoodN

/-!
# The grid rule at any class, and with one neighbour missing

2026-09-27.  `GridNeighbourhoodN.readings_clear` works at class 1 (mirror class 7).  A runner whose class-1 neighbour
slot is doubled needs class 3 (mirror 5); a runner next to an empty slot has only one neighbour at its class.  Both are
here, on one runner's readings, over the same `config` lemma.  Class `p` with mirror `q`: the neighbours are the runners
`A`, `B` with `p·D_A ≡ 1`, `p·D_B ≡ 7`, and `q·D_A ≡ 7`, `q·D_B ≡ 1 (mod 8)`; every other runner has `p·D`, `q·D` in
`2 … 6`.  Used by `DoubledNbhdN`.  No `sorry`, no `native_decide`.
-/

namespace LRC.GridClass

open LRC.GridNbhd

/-- The class-`p` rule, mirror class `q`. -/
noncomputable def gridTp (p q : ℝ) (DA DB : ℤ) (a b : ℝ) : ℝ :=
  if 0 < DA then
    (if 0 < DB then
      (if p * DA / (8 * a) ≤ p * DB / (8 * b) then p * DA / (8 * a) else q * DB / (8 * b))
     else max (p * DA / (8 * a)) (p * DB / (8 * b)))
  else
    (if 0 < DB then min (p * DA / (8 * a)) (p * DB / (8 * b))
     else (if p * DB / (8 * b) ≤ p * DA / (8 * a) then p * DB / (8 * b) else q * DA / (8 * a)))

/-- A residue statement in the form `config` consumes. -/
theorem split_res {c : ℤ} {D : ℤ} {s : ℤ} (h : (c * D) % 8 = s) :
    (c : ℝ) * D = 8 * (((c * D) / 8 : ℤ) : ℝ) + (s : ℝ) := by
  have := Int.emod_add_ediv (c * D) 8
  have h' : c * D = 8 * ((c * D) / 8) + s := by omega
  have := congrArg (fun z : ℤ => (z : ℝ)) h'
  push_cast at this ⊢
  linarith

theorem rest_res {c : ℤ} {D : ℤ} (h2 : 2 ≤ (c * D) % 8) (h6 : (c * D) % 8 ≤ 6) :
    ∃ N r : ℤ, (c : ℝ) * D = 8 * N + r ∧ 2 ≤ r ∧ r ≤ 6 :=
  ⟨(c * D) / 8, (c * D) % 8, split_res rfl, h2, h6⟩

/-- **Class `p`, both neighbours present.** -/
theorem readings_clear_p {δ : Fin 8 → ℝ} {D : Fin 8 → ℤ} {k A B : Fin 8} {η W : ℝ} {p q : ℤ}
    (hp : 0 < p) (hq : 0 < q) (hp7 : p ≤ 7) (hq7 : q ≤ 7)
    (hAk : A ≠ k) (hBk : B ≠ k) (hAB : A ≠ B) (hη0 : 0 ≤ η) (hη : η * (14 * W + 21) ≤ 1)
    (hδ : ∀ j, |δ j - D j| ≤ η) (hW : ∀ j, |(D j : ℝ)| ≤ W)
    (hpA : (p * D A) % 8 = 1) (hpB : (p * D B) % 8 = 7) (hqA : (q * D A) % 8 = 7) (hqB : (q * D B) % 8 = 1)
    (hrest : ∀ j, j ≠ k → j ≠ A → j ≠ B →
      (2 ≤ (p * D j) % 8 ∧ (p * D j) % 8 ≤ 6) ∧ (2 ≤ (q * D j) % 8 ∧ (q * D j) % 8 ≤ 6)) :
    ∀ j, j ≠ k → (8 : ℝ)⁻¹ ≤ circDist (δ j * gridTp p q (D A) (D B) (δ A) (δ B)) := by
  have hW0 : 0 ≤ W := le_trans (abs_nonneg _) (hW k)
  have hη1 : η < 1 := by nlinarith
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hDA0 : D A ≠ 0 := by intro h; rw [h, mul_zero] at hpA; norm_num at hpA
  have hDB0 : D B ≠ 0 := by intro h; rw [h, mul_zero] at hpB; norm_num at hpB
  have hDA1 : 1 ≤ |(D A : ℝ)| := by exact_mod_cast Int.one_le_abs hDA0
  have hDB1 : 1 ≤ |(D B : ℝ)| := by exact_mod_cast Int.one_le_abs hDB0
  obtain ⟨sAp, sAn⟩ := sign_of hη1 (hδ A) hDA1
  obtain ⟨sBp, sBn⟩ := sign_of hη1 (hδ B) hDB1
  have hδA0 : δ A ≠ 0 := by
    rcases lt_or_gt_of_ne hDA0 with h | h
    · exact (sAn h).ne
    · exact (sAp h).ne'
  have hδB0 : δ B ≠ 0 := by
    rcases lt_or_gt_of_ne hDB0 with h | h
    · exact (sBn h).ne
    · exact (sBp h).ne'
  have cpA := split_res hpA
  have cpB := split_res hpB
  have cqA := split_res hqA
  have cqB := split_res hqB
  have rp : ∀ j, j ≠ k → j ≠ A → j ≠ B → ∃ N r : ℤ, (p : ℝ) * D j = 8 * N + r ∧ 2 ≤ r ∧ r ≤ 6 :=
    fun j h1 h2 h3 => rest_res (hrest j h1 h2 h3).1.1 (hrest j h1 h2 h3).1.2
  have rq : ∀ j, j ≠ k → j ≠ A → j ≠ B → ∃ N r : ℤ, (q : ℝ) * D j = 8 * N + r ∧ 2 ≤ r ∧ r ≤ 6 :=
    fun j h1 h2 h3 => rest_res (hrest j h1 h2 h3).2.1 (hrest j h1 h2 h3).2.2
  set tA := (p : ℝ) * D A / (8 * δ A) with htA
  set tB := (p : ℝ) * D B / (8 * δ B) with htB
  -- positions at the openings
  have eA : δ A * tA = (p : ℝ) * D A / 8 := by rw [htA]; field_simp
  have eB : δ B * tB = (p : ℝ) * D B / 8 := by rw [htB]; field_simp
  have eAq : δ A * ((q : ℝ) * D A / (8 * δ A)) = (q : ℝ) * D A / 8 := by field_simp
  have eBq : δ B * ((q : ℝ) * D B / (8 * δ B)) = (q : ℝ) * D B / 8 := by field_simp
  -- the class-q instants in terms of the class-p ones
  have qA : (q : ℝ) * D A / (8 * δ A) = (q / p) * tA := by rw [htA]; field_simp
  have qB : (q : ℝ) * D B / (8 * δ B) = (q / p) * tB := by rw [htB]; field_simp
  have hqp' : (0 : ℝ) < q / p := div_pos hqR hpR
  intro j hjk
  unfold gridTp
  rw [← htA, ← htB]
  split_ifs with hA0 hB0 hle hB0' hle'
  · -- (+,+), tA ≤ tB: flank A, class p
    refine config hAk hBk hAB hpR.le (by exact_mod_cast hp7) hη0 hη hδ hW hDA1 hδA0 cpA (Or.inl rfl)
      cpB (Or.inr rfl) (fun _ => ?_) (fun h => by norm_num at h) (fun j h1 h2 h3 => rp j h1 h2 h3) j hjk
    rw [← htA]
    have := mul_le_mul_of_nonneg_left hle (sBp hB0).le
    rw [eB, cpB] at this; push_cast at this ⊢; linarith
  · -- (+,+), tB < tA: flank B, class q
    refine config hBk hAk (Ne.symm hAB) hqR.le (by exact_mod_cast hq7) hη0 hη hδ hW hDB1 hδB0 cqB (Or.inl rfl)
      cqA (Or.inr rfl) (fun _ => ?_) (fun h => by norm_num at h) (fun j h1 h2 h3 => rq j h1 h3 h2) j hjk
    have hlt : tB ≤ tA := le_of_lt (not_le.mp hle)
    rw [qB]
    have h1 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlt hqp'.le) (sAp hA0).le
    have h2 : δ A * ((q / p) * tA) = (q : ℝ) * D A / 8 := by rw [← qA, eAq]
    rw [h2, cqA] at h1; push_cast at h1 ⊢; linarith
  · rcases le_total tB tA with h | h
    · rw [max_eq_left h]
      refine config hAk hBk hAB hpR.le (by exact_mod_cast hp7) hη0 hη hδ hW hDA1 hδA0 cpA (Or.inl rfl)
        cpB (Or.inr rfl) (fun _ => ?_) (fun h => by norm_num at h) (fun j h1 h2 h3 => rp j h1 h2 h3) j hjk
      rw [← htA]
      have := mul_le_mul_of_nonpos_left h (sBn (by omega)).le
      rw [eB, cpB] at this; push_cast at this ⊢; linarith
    · rw [max_eq_right h]
      refine config hBk hAk (Ne.symm hAB) hpR.le (by exact_mod_cast hp7) hη0 hη hδ hW hDB1 hδB0 cpB (Or.inr rfl)
        cpA (Or.inl rfl) (fun h => by norm_num at h) (fun _ => ?_) (fun j h1 h2 h3 => rp j h1 h3 h2) j hjk
      rw [← htB]
      have := mul_le_mul_of_nonneg_left h (sAp hA0).le
      rw [eA, cpA] at this; push_cast at this ⊢; linarith
  · rcases le_total tA tB with h | h
    · rw [min_eq_left h]
      refine config hAk hBk hAB hpR.le (by exact_mod_cast hp7) hη0 hη hδ hW hDA1 hδA0 cpA (Or.inl rfl)
        cpB (Or.inr rfl) (fun _ => ?_) (fun h => by norm_num at h) (fun j h1 h2 h3 => rp j h1 h2 h3) j hjk
      rw [← htA]
      have := mul_le_mul_of_nonneg_left h (sBp hB0').le
      rw [eB, cpB] at this; push_cast at this ⊢; linarith
    · rw [min_eq_right h]
      refine config hBk hAk (Ne.symm hAB) hpR.le (by exact_mod_cast hp7) hη0 hη hδ hW hDB1 hδB0 cpB (Or.inr rfl)
        cpA (Or.inl rfl) (fun h => by norm_num at h) (fun _ => ?_) (fun j h1 h2 h3 => rp j h1 h3 h2) j hjk
      rw [← htB]
      have := mul_le_mul_of_nonpos_left h (sAn (by omega)).le
      rw [eA, cpA] at this; push_cast at this ⊢; linarith
  · -- (−,−), tB ≤ tA: flank B, class p
    refine config hBk hAk (Ne.symm hAB) hpR.le (by exact_mod_cast hp7) hη0 hη hδ hW hDB1 hδB0 cpB (Or.inr rfl)
      cpA (Or.inl rfl) (fun h => by norm_num at h) (fun _ => ?_) (fun j h1 h2 h3 => rp j h1 h3 h2) j hjk
    rw [← htB]
    have := mul_le_mul_of_nonpos_left hle' (sAn (by omega)).le
    rw [eA, cpA] at this; push_cast at this ⊢; linarith
  · -- (−,−), tA < tB: flank A, class q
    refine config hAk hBk hAB hqR.le (by exact_mod_cast hq7) hη0 hη hδ hW hDA1 hδA0 cqA (Or.inr rfl)
      cqB (Or.inl rfl) (fun h => by norm_num at h) (fun _ => ?_) (fun j h1 h2 h3 => rq j h1 h2 h3) j hjk
    have hlt : tA ≤ tB := le_of_lt (not_le.mp hle')
    rw [qA]
    have h1 := mul_le_mul_of_nonpos_left (mul_le_mul_of_nonneg_left hlt hqp'.le) (sBn (by omega)).le
    have h2 : δ B * ((q / p) * tB) = (q : ℝ) * D B / 8 := by rw [← qB, eBq]
    rw [h2, cqB] at h1; push_cast at h1 ⊢; linarith

/-- **One neighbour only** (the other neighbour slot empty): its class-`p` opening. -/
theorem readings_clear_single {δ : Fin 8 → ℝ} {D : Fin 8 → ℤ} {k X : Fin 8} {η W : ℝ} {p : ℤ} {sX : ℤ}
    (hp : 0 < p) (hp7 : p ≤ 7) (hXk : X ≠ k) (hη0 : 0 ≤ η) (hη : η * (14 * W + 21) ≤ 1)
    (hδ : ∀ j, |δ j - D j| ≤ η) (hW : ∀ j, |(D j : ℝ)| ≤ W)
    (hpX : (p * D X) % 8 = sX) (hsX : sX = 1 ∨ sX = 7)
    (hrest : ∀ j, j ≠ k → j ≠ X → 2 ≤ (p * D j) % 8 ∧ (p * D j) % 8 ≤ 6) :
    ∀ j, j ≠ k → (8 : ℝ)⁻¹ ≤ circDist (δ j * ((p : ℝ) * D X / (8 * δ X))) := by
  have hW0 : 0 ≤ W := le_trans (abs_nonneg _) (hW k)
  have hη1 : η < 1 := by nlinarith
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hDX0 : D X ≠ 0 := by
    intro h; rw [h, mul_zero] at hpX; rcases hsX with h' | h' <;> rw [← hpX] at h' <;> norm_num at h'
  have hDX1 : 1 ≤ |(D X : ℝ)| := by exact_mod_cast Int.one_le_abs hDX0
  obtain ⟨sXp, sXn⟩ := sign_of hη1 (hδ X) hDX1
  have hδX0 : δ X ≠ 0 := by
    rcases lt_or_gt_of_ne hDX0 with h | h
    · exact (sXn h).ne
    · exact (sXp h).ne'
  have cX := split_res hpX
  intro j hjk
  by_cases hjX : j = X
  · rw [hjX]
    have hy : δ X * ((p : ℝ) * D X / (8 * δ X)) = (p : ℝ) * D X / 8 := by field_simp
    rw [hy, cX]
    rcases hsX with h | h <;> subst h <;>
      apply LRC.TwoPinner.clear_of_band (N := (p * D X) / 8) <;> push_cast <;> linarith
  · obtain ⟨N, r, hr, hr2, hr6⟩ := rest_res (hrest j hjk hjX).1 (hrest j hjk hjX).2
    obtain ⟨E, hE, hy⟩ := expand hpR.le (by exact_mod_cast hp7) hη0 hη (hδ X) hDX1 (hδ j) (hW j)
    have hE' := abs_le.mp hE
    have hr2' : (2 : ℝ) ≤ r := by exact_mod_cast hr2
    have hr6' : (r : ℝ) ≤ 6 := by exact_mod_cast hr6
    rw [hy, hr]
    apply LRC.TwoPinner.clear_of_band (N := N) <;> push_cast <;> linarith

end LRC.GridClass
