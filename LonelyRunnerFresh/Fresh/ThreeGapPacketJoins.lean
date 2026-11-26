import Fresh.ThreeGapPacketBand

/-! Adding the native AP unit as the third generator embeds the two-gap
packet family. The D=4 edge becomes D=3 plus that unit. This records the
AP repetition explicitly rather than counting it as another family. -/
namespace Fresh.ThreeGapPacketJoins
open Fresh.TwoGapPacketBand Fresh.ThreeGapPacketBand

theorem two_into_three {V : Fin 8 → ℝ} {k : Fin 8}
    (h : TwoGapPacketClass V k) : ThreeGapPacketClass V k := by
  obtain ⟨hpos,hinj,u,g,h,m,a,b,hu,hgpos,hhpos,hm,hg,hh,hsum,hshape⟩ := h
  refine ⟨hpos,hinj,u,g,h,1,m,a,b,m,hu,hgpos,hhpos,by norm_num,hm,hg,hh,
    by norm_num,?_,?_⟩
  · nlinarith
  · intro i hik
    obtain ⟨D,e,f,hD,he,hf,hne,hdis⟩ := hshape i hik
    by_cases hD4 : D=4
    · subst D
      refine ⟨3,e,f,1,by norm_num,he,hf,by norm_num,by omega,?_⟩
      rw [hdis]
      ring
    · refine ⟨D,e,f,0,by omega,he,hf,by norm_num,by omega,?_⟩
      simpa using hdis

#print axioms two_into_three
end Fresh.ThreeGapPacketJoins
