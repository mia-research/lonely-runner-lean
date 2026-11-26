import Fresh.FourBlockNeighbour

/-! Unit-gap refinement identifies every earlier three-block internal family
inside the four-block family. Splitting a unit AP block adds no deformation.
This is a formal inclusion, not an additional disjoint arrangement count. -/
namespace Fresh.FourBlockNeighbourJoins
open Fresh Fresh.OneMover Fresh.FourBlockNeighbour

theorem three_indicator (c g h : ℝ) (p q : ℕ) (i : Fin 8) :
    ThreeBlockPartitions.speeds c g h p q i =
    c+1+(i : ℝ)+(if p ≤ (i : ℕ) then g-1 else 0)+
      (if p+q ≤ (i : ℕ) then h-1 else 0) := by
  by_cases hp : (i : ℕ)<p
  · have hpq : (i : ℕ)<p+q := by omega
    simp [ThreeBlockPartitions.speeds,hp,hpq,not_le.mpr hp,not_le.mpr hpq]
    ring
  · by_cases hpq : (i : ℕ)<p+q
    · simp [ThreeBlockPartitions.speeds,hp,hpq,le_of_not_gt hp,not_le.mpr hpq]
      ring
    · simp [ThreeBlockPartitions.speeds,hp,hpq,le_of_not_gt hp,le_of_not_gt hpq]
      ring

theorem refine_left (c g h : ℝ) (p q : ℕ) (hp : 2 ≤ p) :
    speeds c 1 g h 1 (p-1) q = ThreeBlockPartitions.speeds c g h p q := by
  funext i
  rw [three_indicator]
  have hc : 1+(p-1)=p := by omega
  simp [speeds,hc]

theorem refine_middle (c g h : ℝ) (p q : ℕ) (hq : 2 ≤ q) :
    speeds c g 1 h p 1 (q-1) = ThreeBlockPartitions.speeds c g h p q := by
  funext i
  rw [three_indicator]
  have hc : p+1+(q-1)=p+q := by omega
  simp [speeds,hc]

theorem refine_right (c g h : ℝ) (p q : ℕ) :
    speeds c g h 1 p q 1 = ThreeBlockPartitions.speeds c g h p q := by
  funext i
  rw [three_indicator]
  simp [speeds]

theorem three_into_four {V : Fin 8 → ℝ} {k : Fin 8}
    (hV : ThreeBlockNeighbour.ThreeBlockInternalClass V k) :
    FourBlockInternalClass V k := by
  obtain ⟨hpos,hinj,c,g,h,B,z,p,q,m,a,b,σ,hp,hq,hpq,hgpos,hhpos,hm,hg,hh,hsum,hk1,hk6,hz,hV⟩ := hV
  by_cases hp2 : 2 ≤ p
  · refine ⟨hpos,hinj,c,1,g,h,B,z,1,p-1,q,m,m,a,b,σ,
      by omega,by omega,hq,by omega,by norm_num,hgpos,hhpos,hm,
      by nlinarith,hg,hh,by nlinarith,hk1,hk6,hz,?_⟩
    simpa only [refine_left c g h p q hp2] using hV
  · by_cases hq2 : 2 ≤ q
    · refine ⟨hpos,hinj,c,g,1,h,B,z,p,1,q-1,m,a,m,b,σ,
        hp,by omega,by omega,by omega,hgpos,by norm_num,hhpos,hm,
        hg,by nlinarith,hh,by nlinarith,hk1,hk6,hz,?_⟩
      simpa only [refine_middle c g h p q hq2] using hV
    · refine ⟨hpos,hinj,c,g,h,1,B,z,p,q,1,m,a,b,m,σ,
        hp,hq,by omega,by omega,hgpos,hhpos,by norm_num,hm,
        hg,hh,by nlinarith,by nlinarith,hk1,hk6,hz,?_⟩
      simpa only [refine_right c g h p q] using hV

theorem pair_speeds (c g h j : ℝ) :
    speeds c g h j 2 2 2 = FourAPPairs.speeds c g h j := by
  funext i
  fin_cases i <;> norm_num [speeds,FourAPPairs.speeds] <;> ring

#print axioms three_indicator
#print axioms refine_left
#print axioms refine_middle
#print axioms refine_right
#print axioms three_into_four
#print axioms pair_speeds
end Fresh.FourBlockNeighbourJoins
