import Fresh.BandNoCarve
import Fresh.ExactCellRestoration

namespace Fresh.SymbolicWindow

open Fresh.Certs

def gapLo (j : ℤ) : ℤ := 8 * j + 1
def gapHi (j : ℤ) : ℤ := 8 * j + 7

/-- The earliest time in a prescribed joint gap, clipped at the window's left endpoint. -/
noncomputable def windowStart (a : ℝ) (g : Fin 7 → ℝ) (lap : Fin 7 → ℤ) : ℝ :=
  max a (Finset.univ.sup' Finset.univ_nonempty fun i => (gapLo (lap i) : ℝ) / g i)

theorem windowStart_clear {a b : ℝ} (hab : a ≤ b) (g : Fin 7 → ℝ) (lap : Fin 7 → ℤ)
    (hpos : ∀ i, 0 < g i)
    (hleft : ∀ i, (gapLo (lap i) : ℝ) ≤ b * g i)
    (hright : ∀ i, a * g i ≤ (gapHi (lap i) : ℝ))
    (hcross : ∀ i j, (gapLo (lap i) : ℝ) * g j ≤ (gapHi (lap j) : ℝ) * g i) :
    a ≤ windowStart a g lap ∧ windowStart a g lap ≤ b ∧
      ∀ i, (1 / 8 : ℝ) ≤ distInt (g i * (windowStart a g lap / 8)) := by
  unfold windowStart
  refine ⟨le_max_left _ _, max_le hab (Finset.sup'_le _ _ fun i _ =>
    (div_le_iff₀ (hpos i)).mpr (hleft i)), ?_⟩
  intro j
  rw [clearAt_R_iff]
  have hlo := (div_le_iff₀ (hpos j)).mp
    ((Finset.le_sup' (fun i => (gapLo (lap i) : ℝ) / g i) (Finset.mem_univ j)).trans
      (le_max_right a _))
  have hhi : max a (Finset.univ.sup' Finset.univ_nonempty
      fun i => (gapLo (lap i) : ℝ) / g i) * g j ≤ (gapHi (lap j) : ℝ) :=
    (le_div_iff₀ (hpos j)).mp
    (max_le ((le_div_iff₀ (hpos j)).mpr (hright j))
      (Finset.sup'_le _ _ fun i _ => (div_le_div_iff₀ (hpos i) (hpos j)).mpr (hcross i j)))
  refine ⟨lap j, ?_⟩
  exact ⟨by simpa [gapLo, mul_comm] using hlo, by simpa [gapHi, mul_comm] using hhi⟩

/-- Check the cross-gap inequalities using rectangle faces. Correlated rows
can be carried separately when the containing rectangle loses their information. -/
def HullCheck (D : ℤ) (lo hi lap : Fin 7 → ℤ) (extra : Finset (Fin 7 × Fin 7)) : Prop :=
  (∀ i, 0 < lo i ∧ 0 ≤ lap i ∧ gapLo (lap i) * D ≤ 7 * lo i ∧ hi i ≤ D * gapHi (lap i)) ∧
  ∀ i j, i ≠ j → (i, j) ∉ extra → gapLo (lap i) * hi j ≤ gapHi (lap j) * lo i

instance (D : ℤ) (lo hi lap : Fin 7 → ℤ) (extra : Finset (Fin 7 × Fin 7)) :
    Decidable (HullCheck D lo hi lap extra) := by
  unfold HullCheck
  infer_instance

theorem windowStart_of_hull {D : ℤ} (hD : 0 < D) {lo hi lap : Fin 7 → ℤ}
    {extra : Finset (Fin 7 × Fin 7)} (hcheck : HullCheck D lo hi lap extra)
    (g : Fin 7 → ℝ)
    (hfaces : ∀ i, (lo i : ℝ) ≤ (D : ℝ) * g i ∧ (D : ℝ) * g i ≤ (hi i : ℝ))
    (hrows : ∀ i j, (i, j) ∈ extra →
      (gapLo (lap i) : ℝ) * g j ≤ (gapHi (lap j) : ℝ) * g i) :
    1 ≤ windowStart 1 g lap ∧ windowStart 1 g lap ≤ 7 ∧
      ∀ i, (1 / 8 : ℝ) ≤ distInt (g i * (windowStart 1 g lap / 8)) := by
  have hd : 0 < (D : ℝ) := by exact_mod_cast hD
  have hp : ∀ i, 0 < g i := by
    intro i
    have hl : 0 < (lo i : ℝ) := by exact_mod_cast (hcheck.1 i).1
    exact pos_of_mul_pos_right (hl.trans_le (hfaces i).1) hd.le
  refine windowStart_clear (by norm_num) g lap hp ?_ ?_ ?_
  · intro i
    have hh : (gapLo (lap i) : ℝ) * (D : ℝ) ≤ 7 * (lo i : ℝ) := by
      exact_mod_cast (hcheck.1 i).2.2.1
    have h' := mul_le_mul_of_nonneg_left (hfaces i).1 (by norm_num : (0 : ℝ) ≤ 7)
    apply le_of_mul_le_mul_left _ hd
    linarith only [hh, h', show (D : ℝ) * (7 * g i) = 7 * ((D : ℝ) * g i) by ring,
      show (D : ℝ) * (gapLo (lap i) : ℝ) = (gapLo (lap i) : ℝ) * (D : ℝ) by ring]
  · intro i
    have hh : (hi i : ℝ) ≤ (D : ℝ) * (gapHi (lap i) : ℝ) := by
      exact_mod_cast (hcheck.1 i).2.2.2
    simpa only [one_mul] using le_of_mul_le_mul_left ((hfaces i).2.trans hh) hd
  · intro i j
    by_cases hij : i = j
    · subst j
      apply mul_le_mul_of_nonneg_right _ (hp i).le
      unfold gapLo gapHi
      push_cast
      linarith
    by_cases hmem : (i, j) ∈ extra
    · exact hrows i j hmem
    have hc : (gapLo (lap i) : ℝ) * (hi j : ℝ) ≤ (gapHi (lap j) : ℝ) * (lo i : ℝ) := by
      exact_mod_cast hcheck.2 i j hij hmem
    have hAi : (0 : ℝ) ≤ (gapLo (lap i) : ℝ) := by
      have h : 0 ≤ gapLo (lap i) := by unfold gapLo; have := (hcheck.1 i).2.1; omega
      exact_mod_cast h
    have hBj : (0 : ℝ) ≤ (gapHi (lap j) : ℝ) := by
      have h : 0 ≤ gapHi (lap j) := by unfold gapHi; have := (hcheck.1 j).2.1; omega
      exact_mod_cast h
    have h' := (mul_le_mul_of_nonneg_left (hfaces j).2 hAi).trans
      (hc.trans (mul_le_mul_of_nonneg_left (hfaces i).1 hBj))
    apply le_of_mul_le_mul_left _ hd
    simpa only [← mul_assoc, mul_comm (D : ℝ) (gapLo (lap i) : ℝ),
      mul_comm (D : ℝ) (gapHi (lap j) : ℝ)] using h'

/-- The moving reading has a clear point in the frozen cell whenever its face
misses every open parameter interval that would block the whole cell. -/
theorem oneMovingReading_clear (g : Fin 7 → ℝ) (i : Fin 7)
    {a b lo hi : ℝ} (ha : 0 < a) (hab : a ≤ b) (hg : 0 < g i)
    (hface : lo ≤ g i ∧ g i ≤ hi)
    (hothers : ∀ j, j ≠ i → ∀ R ∈ Set.Icc a b,
      (1 / 8 : ℝ) ≤ distInt (g j * (R / 8)))
    (hbad : ∀ j : ℤ, ¬ (((j : ℝ) * 8 - 1) / a < ((j : ℝ) * 8 + 1) / b ∧
      ((j : ℝ) * 8 - 1) / a < hi ∧ lo < ((j : ℝ) * 8 + 1) / b)) :
    ∃ R ∈ Set.Icc a b, ∀ j, (1 / 8 : ℝ) ≤ distInt (g j * (R / 8)) := by
  have hb : 0 < b := ha.trans_le hab
  have hrestore : LRC.ExactCellRestoration.Restores (g i) (a / 8) (b / 8) := by
    by_contra h
    obtain ⟨j, hl, hu⟩ :=
      (LRC.ExactCellRestoration.not_restores_iff hg (by linarith : a / 8 ≤ b / 8)).mp h
    have h1 : ((j : ℝ) * 8 - 1) / a < g i :=
      (div_lt_iff₀ ha).mpr (by linarith [show g i * a = g i * (a / 8) * 8 by ring])
    have h2 : g i < ((j : ℝ) * 8 + 1) / b :=
      (lt_div_iff₀ hb).mpr (by linarith [show g i * b = g i * (b / 8) * 8 by ring])
    exact hbad j ⟨h1.trans h2, h1.trans_le hface.2, hface.1.trans_lt h2⟩
  obtain ⟨t, hta, htb, j, hl, hu⟩ := hrestore
  have ht : 8 * t ∈ Set.Icc a b := ⟨by linarith, by linarith⟩
  refine ⟨8 * t, ht, fun k => ?_⟩
  by_cases hk : k = i
  · subst k
    rw [show 8 * t / 8 = t by ring]
    exact Fresh.Localisation.clear_of_window j hl hu
  · exact hothers k hk _ ht

def pinchLaps : Fin 7 → ℤ := ![0, 1, 1, 2, 3, 4, 11]
def pinchLo : Fin 7 → ℤ := ![512, 1202, 1576, 2027, 2645, 3615, 9419]
def pinchHi : Fin 7 → ℤ := ![512, 1244, 1625, 2090, 2728, 3726, 9712]
def pinchExtra : Finset (Fin 7 × Fin 7) := {(4, 2), (6, 2)}

/-- Across the whole pinch hull, only the two recorded exits can attain the maximum. -/
theorem pinchWindowStart_eq (g : Fin 7 → ℝ)
    (hfaces : ∀ i, (pinchLo i : ℝ) ≤ 512 * g i ∧ 512 * g i ≤ (pinchHi i : ℝ)) :
    windowStart 1 g pinchLaps = max (25 / g 4) (89 / g 6) := by
  have hlow : ∀ i, 0 < pinchLo i := by decide
  have hp : ∀ i, 0 < g i := by
    intro i
    have hl : 0 < (pinchLo i : ℝ) := by exact_mod_cast hlow i
    exact pos_of_mul_pos_right (hl.trans_le (hfaces i).1) (by norm_num)
  have hb : 1 ≤ 25 / g 4 := by
    apply (le_div_iff₀ (hp 4)).mpr
    have h := (hfaces (4 : Fin 7)).2
    have hh : pinchHi (4 : Fin 7) = 2728 := by decide
    rw [hh] at h
    norm_num at h
    linarith
  have hrow : ∀ i : Fin 7, i ≠ 4 → i ≠ 6 →
      gapLo (pinchLaps i) * pinchHi 4 ≤ 25 * pinchLo i := by decide
  unfold windowStart
  apply le_antisymm
  · refine max_le (hb.trans (le_max_left _ _)) (Finset.sup'_le _ _ ?_)
    intro i _
    by_cases h4 : i = 4
    · subst i
      simpa [pinchLaps, gapLo] using (le_max_left (25 / g 4) (89 / g 6))
    by_cases h6 : i = 6
    · subst i
      simpa [pinchLaps, gapLo] using (le_max_right (25 / g 4) (89 / g 6))
    apply le_trans _ (le_max_left _ _)
    apply (div_le_div_iff₀ (hp i) (hp 4)).mpr
    have hA : 0 ≤ (gapLo (pinchLaps i) : ℝ) := by
      have h : ∀ k : Fin 7, 0 ≤ gapLo (pinchLaps k) := by decide
      exact_mod_cast h i
    have h := mul_le_mul_of_nonneg_left (hfaces 4).2 hA
    have h' := mul_le_mul_of_nonneg_left (hfaces i).1 (by norm_num : (0 : ℝ) ≤ 25)
    have hr : (gapLo (pinchLaps i) : ℝ) * (pinchHi 4 : ℝ) ≤ 25 * (pinchLo i : ℝ) := by
      exact_mod_cast hrow i h4 h6
    apply le_of_mul_le_mul_left _ (by norm_num : (0 : ℝ) < 512)
    linarith only [h, h', hr, show 512 * ((gapLo (pinchLaps i) : ℝ) * g 4) =
      (gapLo (pinchLaps i) : ℝ) * (512 * g 4) by ring,
      show 512 * (25 * g i) = 25 * (512 * g i) by ring]
  · apply max_le
    · have h := Finset.le_sup' (fun i => (gapLo (pinchLaps i) : ℝ) / g i)
          (Finset.mem_univ (4 : Fin 7))
      simpa [pinchLaps, gapLo] using h.trans (le_max_right (1 : ℝ) _)
    · have h := Finset.le_sup' (fun i => (gapLo (pinchLaps i) : ℝ) / g i)
          (Finset.mem_univ (6 : Fin 7))
      simpa [pinchLaps, gapLo] using h.trans (le_max_right (1 : ℝ) _)

theorem pinchHull_clear (g : Fin 7 → ℝ)
    (hfaces : ∀ i, (pinchLo i : ℝ) ≤ 512 * g i ∧ 512 * g i ≤ (pinchHi i : ℝ))
    (h5 : 25 * g 2 ≤ 15 * g 4) (h7 : 89 * g 2 ≤ 15 * g 6) :
    1 ≤ windowStart 1 g pinchLaps ∧ windowStart 1 g pinchLaps ≤ 7 ∧
      ∀ i, (1 / 8 : ℝ) ≤ distInt (g i * (windowStart 1 g pinchLaps / 8)) := by
  refine windowStart_of_hull (D := 512) (extra := pinchExtra) (by decide)
    (show HullCheck 512 pinchLo pinchHi pinchLaps pinchExtra from by decide) g
    (by simpa using hfaces) ?_
  intro i j hij
  have hp : (i, j) = (4, 2) ∨ (i, j) = (6, 2) := by simpa [pinchExtra] using hij
  rcases hp with hp | hp
  · cases hp
    simpa [pinchLaps, gapLo, gapHi] using h5
  · cases hp
    simpa [pinchLaps, gapLo, gapHi] using h7

def pinchHulls : List ((Fin 7 → ℤ) × (Fin 7 → ℤ)) :=
  [(![512, 1202, 1576, 2027, 2645, 3615, 9419], ![512, 1218, 1577, 2029, 2648, 3617, 9427]),
   (![512, 1220, 1600, 2058, 2686, 3670, 9563], ![512, 1236, 1602, 2060, 2688, 3673, 9570]),
   (![512, 1239, 1624, 2089, 2726, 3725, 9707], ![512, 1244, 1625, 2090, 2728, 3726, 9712])]

private theorem pinchHulls_checked :
    ∀ p ∈ pinchHulls, HullCheck 512 p.1 p.2 pinchLaps ∅ := by
  intro p hp
  simp only [pinchHulls, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl | rfl <;> decide

theorem pinchThreeHulls_clear (g : Fin 7 → ℝ)
    (h : ∃ p ∈ pinchHulls, ∀ i, (p.1 i : ℝ) ≤ 512 * g i ∧ 512 * g i ≤ (p.2 i : ℝ)) :
    1 ≤ windowStart 1 g pinchLaps ∧ windowStart 1 g pinchLaps ≤ 7 ∧
      ∀ i, (1 / 8 : ℝ) ≤ distInt (g i * (windowStart 1 g pinchLaps / 8)) := by
  obtain ⟨p, hp, hg⟩ := h
  exact windowStart_of_hull (by decide) (pinchHulls_checked p hp) g (by simpa using hg)
    (by simp)

#print axioms windowStart_clear
#print axioms windowStart_of_hull
#print axioms oneMovingReading_clear
#print axioms pinchWindowStart_eq
#print axioms pinchHull_clear
#print axioms pinchThreeHulls_clear

end Fresh.SymbolicWindow
