import Fresh.FourBlockEndpointCapture

/-! The far endpoint's unit AP partner is forced to enter after the first
native endpoint move. This is a retained-packet statement, not a claim that
later setters keep descending. Exact map has2160unit-opposite controls and
later return words; original comparison-reference provenance is retained. -/
namespace Fresh.FourBlockEndpointUnitPartner
open Fresh Fresh.Cascade Fresh.Localisation Fresh.FourBlockNeighbour Fresh.FourBlockEndpointCapture

theorem outer_opening_bounds (g h j : ℝ) (hg : 0 < g) (hh : 0 < h) (hj : 0 < j)
    (m a b e : ℤ) (hcap : (7/8 : ℝ) < remainder g h j m a b e)
    (hrem : remainder g h j m a b e ≤ 1) :
    (m : ℝ)+1/8 < outerOpening g h j m a b e ∧
    outerOpening g h j m a b e < (m : ℝ)+3/16 := by
  have hD : 4 < 4+g+h+j := by linarith
  have hDne : 4+g+h+j≠0 := ne_of_gt (by linarith)
  have hP : (4+g+h+j)*outerOpening g h j m a b e=(spanLap m a b e : ℝ)+9/8 := by
    dsimp [outerOpening]
    field_simp [hDne]
  have hT : (4+g+h+j)*((m : ℝ)+1/8)=
      (spanLap m a b e : ℝ)+remainder g h j m a b e := by
    dsimp [spanLap,remainder]
    push_cast
    ring
  have hdelta : (4+g+h+j)*(outerOpening g h j m a b e-((m : ℝ)+1/8))=
      9/8-remainder g h j m a b e := by nlinarith only [hP,hT]
  constructor <;> nlinarith

theorem unit_partner_capture (c g h j : ℝ) (p q r : ℕ)
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r) (hs : p+q+r ≤ 6)
    (hg : 0 < g) (hh : 0 < h) (hj : 0 < j) (m a b e : ℤ)
    (hcap : (7/8 : ℝ) < remainder g h j m a b e)
    (hrem : remainder g h j m a b e ≤ 1) :
    InWay |speeds c g h j p q r 6-speeds c g h j p q r 0| (outerOpening g h j m a b e) ∧
    nextOpening |speeds c g h j p q r 6-speeds c g h j p q r 0| (outerOpening g h j m a b e)=
      (((spanLap m a b e-m : ℤ) : ℝ)+9/8)/(3+g+h+j) := by
  have hD : 0 < 4+g+h+j := by linarith
  have hD6 : 0 < 3+g+h+j := by linarith
  have hspan := FourBlockEndpoints.speed_span c g h j p q r hp hq hr (by omega)
  have hstep := FourBlockEndpoints.adjacent_speed_gap c g h j p q r hq hr (6 : Fin 7)
  change speeds c g h j p q r 7-speeds c g h j p q r 6=
    (if (7 : ℕ)=p then g else if (7 : ℕ)=p+q then h else if (7 : ℕ)=p+q+r then j else 1) at hstep
  have hc1 : (7 : ℕ)≠p := by omega
  have hc2 : (7 : ℕ)≠p+q := by omega
  have hc3 : (7 : ℕ)≠p+q+r := by omega
  simp only [if_neg hc1,if_neg hc2,if_neg hc3] at hstep
  have hdiff : speeds c g h j p q r 6-speeds c g h j p q r 0=3+g+h+j := by linarith
  rw [hdiff,abs_of_pos hD6]
  obtain ⟨hlo,hhi⟩ := outer_opening_bounds g h j hg hh hj m a b e hcap hrem
  have hDne : 4+g+h+j≠0 := ne_of_gt hD
  have hP : (4+g+h+j)*outerOpening g h j m a b e=(spanLap m a b e : ℝ)+9/8 := by
    dsimp [outerOpening]
    field_simp [hDne]
  have hnear : |(3+g+h+j)*outerOpening g h j m a b e-((spanLap m a b e-m+1 : ℤ) : ℝ)| < 1/8 := by
    rw [abs_lt]
    push_cast
    constructor <;> nlinarith
  refine ⟨lt_of_le_of_lt (Fresh.Cascade.distInt_le _ (spanLap m a b e-m+1)) hnear,?_⟩
  rw [nextOpening_eq hnear]
  push_cast
  congr 1
  ring

#print axioms outer_opening_bounds
#print axioms unit_partner_capture
end Fresh.FourBlockEndpointUnitPartner
