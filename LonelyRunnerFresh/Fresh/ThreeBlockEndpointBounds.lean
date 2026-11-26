import Fresh.ThreeBlockPartitions

/-! Rules: 1–4, 8–18. Original endpoint-reading bounds for all positive
three-block lengths. Proof uses the three symbolic block cases, without
partition enumeration. Saved qualified singleton controls preceded this
lemma; guard-free singleton failures remain outside its statement.
-/
namespace Fresh.ThreeBlockEndpointBounds
open Fresh Fresh.ThreeBlockPartitions

theorem left_difference_bounds (c g h : ℝ) (p q : ℕ)
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hpq : p+q ≤ 7)
    (hg : 0<g) (hh : 0<h) (hsmall : g+h ≤ 2)
    (hguard : p=1→1 ≤ g) (i : Fin 8) (hi : i≠0) :
    1 ≤ speeds c g h p q i-speeds c g h p q 0 ∧
      speeds c g h p q i-speeds c g h p q 0 ≤ 7 := by
  let I : ℝ := ((i : ℕ) : ℝ)
  have hi1 : 1 ≤ (i : ℕ) := by have := Fin.val_ne_of_ne hi; simp at this; omega
  have hi7 : (i : ℕ) ≤ 7 := by have :=i.isLt;omega
  have hI1 : (1 : ℝ) ≤ I := by dsimp [I]; exact_mod_cast hi1
  have hI7 : I ≤ 7 := by dsimp [I]; exact_mod_cast hi7
  have hg2 : g ≤ 2 := by linarith
  have h0 : speeds c g h p q (0 : Fin 8)=c+1 := by
    have h0p : (0 : ℕ)<p := by omega
    simp [speeds,h0p]
  by_cases hip : (i : ℕ)<p
  · have hd : speeds c g h p q i-speeds c g h p q 0=I := by
      rw [h0]
      simp only [speeds,if_pos hip]
      dsimp [I]
      ring
    rw [hd]
    exact ⟨hI1,hI7⟩
  · by_cases hiq : (i : ℕ)<p+q
    · have hi6 : (i : ℕ) ≤ 6 := by omega
      have hI6 : I ≤ 6 := by dsimp [I]; exact_mod_cast hi6
      have hd : speeds c g h p q i-speeds c g h p q 0=g+I-1 := by
        rw [h0]
        simp only [speeds,if_neg hip,if_pos hiq]
        dsimp [I]
        ring
      rw [hd]
      constructor
      · by_cases hp1 : p=1
        · have := hguard hp1
          linarith
        · have hi2 : 2 ≤ (i : ℕ) := by omega
          have hI2 : (2 : ℝ) ≤ I := by dsimp [I]; exact_mod_cast hi2
          linarith
      · linarith
    · have hi2 : 2 ≤ (i : ℕ) := by omega
      have hI2 : (2 : ℝ) ≤ I := by dsimp [I]; exact_mod_cast hi2
      have hd : speeds c g h p q i-speeds c g h p q 0=g+h+I-2 := by
        rw [h0]
        simp only [speeds,if_neg hip,if_neg hiq]
        dsimp [I]
        ring
      rw [hd]
      constructor
      · by_cases hp1 : p=1
        · have := hguard hp1
          linarith
        · have hi3 : 3 ≤ (i : ℕ) := by omega
          have hI3 : (3 : ℝ) ≤ I := by dsimp [I]; exact_mod_cast hi3
          linarith
      · linarith

theorem right_difference_bounds (c g h : ℝ) (p q : ℕ)
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hpq : p+q ≤ 7)
    (hg : 0<g) (hh : 0<h) (hsmall : g+h ≤ 2)
    (hguard : p+q=7→1 ≤ h) (i : Fin 8) (hi : i≠7) :
    1 ≤ speeds c g h p q 7-speeds c g h p q i ∧
      speeds c g h p q 7-speeds c g h p q i ≤ 7 := by
  let I : ℝ := ((i : ℕ) : ℝ)
  have hi0 : (0 : ℝ) ≤ I := Nat.cast_nonneg _
  have hi6 : (i : ℕ) ≤ 6 := by have :=Fin.val_ne_of_ne hi;have :=i.isLt;omega
  have hI6 : I ≤ 6 := by dsimp [I]; exact_mod_cast hi6
  have hh2 : h ≤ 2 := by linarith
  have h7 : speeds c g h p q (7 : Fin 8)=c+g+h+6 := by
    have h7p : ¬(7 : ℕ)<p := by omega
    have h7pq : ¬(7 : ℕ)<p+q := by omega
    norm_num [speeds,h7p,h7pq]
    ring
  by_cases hip : (i : ℕ)<p
  · have hi5 : (i : ℕ) ≤ 5 := by omega
    have hI5 : I ≤ 5 := by dsimp [I]; exact_mod_cast hi5
    have hd : speeds c g h p q 7-speeds c g h p q i=g+h+5-I := by
      rw [h7]
      simp only [speeds,if_pos hip]
      dsimp [I]
      ring
    rw [hd]
    constructor
    · by_cases hs : p+q=7
      · have :=hguard hs
        linarith
      · have hi4 : (i : ℕ) ≤ 4 := by omega
        have hI4 : I ≤ 4 := by dsimp [I]; exact_mod_cast hi4
        linarith
    · linarith
  · by_cases hiq : (i : ℕ)<p+q
    · have hi1 : 1 ≤ (i : ℕ) := by omega
      have hI1 : (1 : ℝ) ≤ I := by dsimp [I]; exact_mod_cast hi1
      have hd : speeds c g h p q 7-speeds c g h p q i=h+6-I := by
        rw [h7]
        simp only [speeds,if_neg hip,if_pos hiq]
        dsimp [I]
        ring
      rw [hd]
      constructor
      · by_cases hs : p+q=7
        · have :=hguard hs
          linarith
        · have hi5 : (i : ℕ) ≤ 5 := by omega
          have hI5 : I ≤ 5 := by dsimp [I]; exact_mod_cast hi5
          linarith
      · linarith
    · have hd : speeds c g h p q 7-speeds c g h p q i=7-I := by
        rw [h7]
        simp only [speeds,if_neg hip,if_neg hiq]
        dsimp [I]
        ring
      rw [hd]
      constructor <;> linarith

/-- Left endpoint at the direct AP instant, with the singleton guard only. -/
theorem left_direct (c g h : ℝ) (p q : ℕ)
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hpq : p+q ≤ 7)
    (hg : 0<g) (hh : 0<h) (hsmall : g+h ≤ 2)
    (hguard : p=1→1 ≤ g) :
    IsolatedAt (speeds c g h p q) 0 (1/8) := by
  intro i hi
  obtain ⟨hlo,hhi⟩ := left_difference_bounds c g h p q hp hq hpq hg hh hsmall hguard i hi
  apply Fresh.Localisation.clear_of_window (0 : ℤ)
  all_goals norm_num
  all_goals linarith

/-- Right endpoint at the direct AP instant, with its singleton guard only. -/
theorem right_direct (c g h : ℝ) (p q : ℕ)
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hpq : p+q ≤ 7)
    (hg : 0<g) (hh : 0<h) (hsmall : g+h ≤ 2)
    (hguard : p+q=7→1 ≤ h) :
    IsolatedAt (speeds c g h p q) 7 (1/8) := by
  intro i hi
  obtain ⟨hlo,hhi⟩ := right_difference_bounds c g h p q hp hq hpq hg hh hsmall hguard i hi
  have hd : speeds c g h p q i-speeds c g h p q 7=
      -(speeds c g h p q 7-speeds c g h p q i) := by ring
  rw [hd,neg_mul,Fresh.Localisation.distInt_neg]
  apply Fresh.Localisation.clear_of_window (0 : ℤ)
  all_goals norm_num
  all_goals linarith

#print axioms left_difference_bounds
#print axioms right_difference_bounds
#print axioms left_direct
#print axioms right_direct
end Fresh.ThreeBlockEndpointBounds
