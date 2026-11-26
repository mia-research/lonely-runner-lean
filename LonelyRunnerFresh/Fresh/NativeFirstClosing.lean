import Fresh.NativeRelativeCapture

/-! Original first-closing boundaries propagate one upper face to all
readings. The quarter face is automatic from one native capture width;
the sharp deficit face is retained separately and is not universally forced. -/
namespace Fresh.NativeFirstClosing
open Fresh Fresh.Cascade Fresh.Localisation

theorem propagate_upper (s c P : ℝ) (K C : ℤ) (hs : 0 ≤ s) (hc : 0 < c)
    (hanchor : c*P ≤ (C : ℝ)+7/8)
    (hfirst : s*((C : ℝ)+7/8) ≤ c*((K : ℝ)+7/8)) : s*P ≤ (K : ℝ)+7/8 := by
  have hscaled := mul_le_mul_of_nonneg_left hanchor hs
  nlinarith only [hscaled,hfirst,hc]

theorem quarter_implies_deficit (d s Q : ℝ) (N K : ℤ) (hs : 0 ≤ s)
    (hcap : (N : ℝ)-1/8 < d*Q)
    (hquarter : s/4 ≤ d*((K : ℝ)+7/8-s*Q)) :
    s*((N : ℝ)+1/8-d*Q) ≤ d*((K : ℝ)+7/8-s*Q) := by
  have hh := mul_nonneg hs (sub_nonneg.mpr hcap.le)
  nlinarith only [hh,hquarter]

theorem deficit_iff_upper (d s Q P : ℝ) (N K : ℤ) (hd : 0 < d)
    (hopen : d*P=(N : ℝ)+1/8) :
    s*((N : ℝ)+1/8-d*Q) ≤ d*((K : ℝ)+7/8-s*Q) ↔ s*P ≤ (K : ℝ)+7/8 := by
  have hscaled := congrArg (fun x : ℝ => s*x) hopen
  constructor
  · intro hh
    nlinarith only [hh,hscaled,hd]
  · intro hh
    have hmul := mul_le_mul_of_nonneg_left hh hd.le
    nlinarith only [hmul,hscaled]

theorem closing_at_opening (d s c Q P : ℝ) (N K C : ℤ) (hd : 0 < d) (hs : 0 ≤ s) (hc : 0 < c)
    (hopen : d*P=(N : ℝ)+1/8)
    (hface : c*((N : ℝ)+1/8-d*Q) ≤ d*((C : ℝ)+7/8-c*Q))
    (hfirst : s*((C : ℝ)+7/8) ≤ c*((K : ℝ)+7/8)) : s*P ≤ (K : ℝ)+7/8 := by
  exact propagate_upper s c P K C hs hc ((deficit_iff_upper d c Q P N C hd hopen).1 hface) hfirst

theorem exists_first_closing {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8) (L : Fin 8 → ℤ) :
    ∃ c : Fin 8, c≠k ∧ ∀ i : Fin 8, i≠k →
      |v i-v k| * ((L c : ℝ)+7/8) ≤ |v c-v k| * ((L i : ℝ)+7/8) := by
  let S : Finset (Fin 8) := Finset.univ.erase k
  have hne : S.Nonempty := by
    by_cases hk : k=0
    · exact ⟨1,Finset.mem_erase.mpr ⟨by subst k; decide,Finset.mem_univ _⟩⟩
    · exact ⟨0,Finset.mem_erase.mpr ⟨Ne.symm hk,Finset.mem_univ _⟩⟩
  obtain ⟨c,hc,hmin⟩ := Finset.exists_min_image S (fun i => ((L i : ℝ)+7/8)/|v i-v k|) hne
  have hck : c≠k := (Finset.mem_erase.mp hc).1
  refine ⟨c,hck,?_⟩
  intro i hi
  have hcpos : 0 < |v c-v k| := abs_pos.mpr (sub_ne_zero.mpr (fun he => hck (hv.2 he)))
  have hipos : 0 < |v i-v k| := abs_pos.mpr (sub_ne_zero.mpr (fun he => hi (hv.2 he)))
  have hh := hmin i (Finset.mem_erase.mpr ⟨hi,Finset.mem_univ _⟩)
  have hn := (div_le_div_iff₀ hcpos hipos).1 hh
  nlinarith only [hn]

#print axioms propagate_upper
#print axioms quarter_implies_deficit
#print axioms deficit_iff_upper
#print axioms closing_at_opening
#print axioms exists_first_closing
end Fresh.NativeFirstClosing
