import Fresh.CarveExclusionCerts

namespace Fresh.Certs

open Fresh Fresh.Cascade Set

/-- [PROVISIONAL: covering] One positive reading blocks a closed slow cell
exactly when a single strict zone contains both ends, including singleton cells. -/
theorem tailCell_blocked_iff {d a b : ℝ} (hd : 0 < d) (hab : a ≤ b) :
    (∀ R ∈ Icc a b, InWay d (R/8)) ↔
      ∃ j : ℤ, (8*(j:ℝ)-1) < d*a ∧ d*b < 8*(j:ℝ)+1 := by
  constructor
  · intro h
    obtain ⟨j,hj⟩ := exists_near_int (h a ⟨le_rfl,hab⟩)
    rw [abs_lt] at hj
    refine ⟨j,by linarith [hj.1],?_⟩
    by_contra! hjb
    let R := (8*(j:ℝ)+1)/d
    have hR : R ∈ Icc a b :=
      ⟨(le_div_iff₀ hd).mpr (by linarith [hj.2]),(div_le_iff₀ hd).mpr (by linarith)⟩
    have he : d*(R/8) = 1/8+(j:ℝ) := by dsimp [R]; field_simp; ring
    have hb := h R hR
    unfold InWay at hb
    rw [he,distInt_eighth_add_int] at hb
    exact (lt_irrefl _) hb
  · rintro ⟨j,ha,hb⟩ R hR
    apply inWay_of_zone (j := j) <;> push_cast
    · exact ha.trans_le (mul_le_mul_of_nonneg_left hR.1 hd.le)
    · exact (mul_le_mul_of_nonneg_left hR.2 hd.le).trans_lt hb

/-- [PROVISIONAL: covering] A closed cell of the slow core survives a
fast reading if the cell spans at least one full strict zone width. -/
theorem tailCell_survives_of_width {S : Finset ℝ} {d a b : ℝ}
    (hd : 0 < d) (hab : a ≤ b) (hw : 2 ≤ d*(b-a))
    (hslow : ∀ R ∈ Icc a b, LonelyAt S (R/8)) :
    ∃ R ∈ Icc a b, LonelyAt (insert d S) (R/8) := by
  have h : ∃ R ∈ Icc a b, ¬ InWay d (R/8) := by
    by_contra! h
    obtain ⟨j,h₁,h₂⟩ := (tailCell_blocked_iff hd hab).mp h
    linarith
  obtain ⟨R,hR,hfast⟩ := h
  refine ⟨R,hR,fun q hq => ?_⟩
  rcases Finset.mem_insert.mp hq with rfl | hq
  · exact not_inWay_iff.mp hfast
  · exact hslow R hR q hq

/-- [PROVISIONAL: covering] A retained slow cell and one fast lap give
a closed interval of fast rates that cannot carve the cell. The hypotheses
are the cross-multiplied rate interval, so they also include its endpoints. -/
theorem tailCell_survives_of_lap {S : Finset ℝ} {d a b : ℝ}
    (hd : 0 < d) (hab : a ≤ b) (j : ℤ)
    (hleft : d*a ≤ 8*(j:ℝ)+7) (hright : 8*(j:ℝ)+1 ≤ d*b)
    (hslow : ∀ R ∈ Icc a b, LonelyAt S (R/8)) :
    ∃ R ∈ Icc a b, LonelyAt (insert d S) (R/8) := by
  let e := (8*(j:ℝ)+1)/d
  let R := max a e
  have he : e ≤ b := (div_le_iff₀ hd).mpr (by linarith)
  have hR : R ∈ Icc a b := ⟨le_max_left _ _,max_le hab he⟩
  refine ⟨R,hR,fun q hq => ?_⟩
  rcases Finset.mem_insert.mp hq with rfl | hq
  · apply (clearAt_R_iff _ _).mpr
    refine ⟨j,?_⟩
    have hlo := (div_le_iff₀ hd).mp (le_max_right a e)
    have hhi : R ≤ (8*(j:ℝ)+7)/q := max_le
      ((le_div_iff₀ hd).mpr (by linarith))
      (div_le_div_of_nonneg_right (by linarith) hd.le)
    have hhi' := (le_div_iff₀ hd).mp hhi
    constructor <;> push_cast <;> linarith
  · exact hslow R hR q hq

/-- [PROVISIONAL: covering] The cap half restricts a putative carve to
ladder-feasible strip classes. Covering kills each remaining class by
producing a first-window clear point. -/
theorem noCarve_of_ladder_and_cover {ι : Type*} {g : Fin 7 → ℝ}
    (strip ladder : ι → Prop)
    (hclass : Fresh.FrontierFamilyCap.CarvesOneSeven (Finset.image g Finset.univ) →
      ∃ i, strip i ∧ ladder i)
    (hkill : ∀ i, strip i → ladder i →
      ∃ R : ℝ, 1 ≤ R ∧ R ≤ 7 ∧ ∀ q, (1/8:ℝ) ≤ distInt (g q*(R/8))) :
    NoCarve g := by
  intro h
  obtain ⟨i,hs,hl⟩ := hclass h
  obtain ⟨R,hR₁,hR₇,hclear⟩ := hkill i hs hl
  obtain ⟨d,hd,j,hj₁,hj₂⟩ := h R hR₁ hR₇
  obtain ⟨q,_,rfl⟩ := Finset.mem_image.mp hd
  exact (not_inWay_iff.mpr (hclear q)) (inWay_of_zone (j := j)
    (by push_cast; linarith) (by push_cast; linarith))

/-- [PROVISIONAL: covering] A strip class is excluded by a retained
slow cell whose certified fast-rate band contains the putative carver.
The cap and ladder classification is supplied by the caller. -/
theorem noCarve_of_ladder_and_lap_cover {ι : Type*} {g : Fin 7 → ℝ}
    {S : Finset ℝ} {d : ℝ} (hd : 0 < d)
    (himage : Finset.image g Finset.univ = insert d S)
    (strip ladder : ι → Prop)
    (hclass : Fresh.FrontierFamilyCap.CarvesOneSeven (Finset.image g Finset.univ) →
      ∃ i, strip i ∧ ladder i)
    (hcover : ∀ i, strip i → ladder i →
      ∃ (a b : ℝ) (j : ℤ), 1 ≤ a ∧ a ≤ b ∧ b ≤ 7 ∧
        d*a ≤ 8*(j:ℝ)+7 ∧ 8*(j:ℝ)+1 ≤ d*b ∧
        ∀ R ∈ Icc a b, LonelyAt S (R/8)) :
    NoCarve g := by
  apply noCarve_of_ladder_and_cover strip ladder hclass
  intro i hs hl
  obtain ⟨a,b,j,ha,hab,hb,hL,hU,hslow⟩ := hcover i hs hl
  obtain ⟨R,hR,hclear⟩ := tailCell_survives_of_lap hd hab j hL hU hslow
  refine ⟨R,ha.trans hR.1,hR.2.trans hb,fun q => hclear (g q) ?_⟩
  rw [← himage]
  exact Finset.mem_image.mpr ⟨q,Finset.mem_univ _,rfl⟩

#print axioms tailCell_blocked_iff
#print axioms tailCell_survives_of_width
#print axioms tailCell_survives_of_lap
#print axioms noCarve_of_ladder_and_cover
#print axioms noCarve_of_ladder_and_lap_cover

end Fresh.Certs
