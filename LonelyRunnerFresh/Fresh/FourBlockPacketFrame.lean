import Fresh.FourBlockLeftOpeningArrangement

/-! The actual four-reading packet faces determine their own lower
reference edge; no inherited five-reading lower face is required. -/
namespace Fresh.FourBlockPacketFrame
open Fresh Fresh.Cascade Fresh.Localisation Fresh.FourBlockNeighbour
  Fresh.FourBlockEndpointCapture Fresh.FourBlockLongTailBounds
  Fresh.FourBlockLongTailPhase Fresh.FourBlockOuterLapPhase Fresh.FourBlockOuterTailClear

theorem frame_upper (g h j : ℝ) (hg : 0 < g) (hh : 0 < h) (hj : 0 < j)
    (m a b e rho : ℤ)
    (hhi : 8*(rho : ℝ)-27 ≤ 7*(g+h+j)+8*remainder g h j m a b e) :
    outerLapOpening g h j m a b e rho ≤ (m : ℝ)+1 := by
  have hd := opening_delta g h j hg hh hj m a b e rho
  have hp : 0 < 4+g+h+j := by linarith
  nlinarith

theorem frame_lower (g h j : ℝ) (hg : 0 < g) (hh : 0 < h) (hj : 0 < j)
    (m : ℤ) (Q P : ℝ) (hQP : Q ≤ P)
    (hinner : (4+g+h+j)*(P-Q)+3*(1-(P-(m : ℝ))) ≤ 3/4) :
    (m : ℝ)+3/4 ≤ Q := by
  have hprod := mul_nonneg (by linarith : 0 ≤ 1+g+h+j) (sub_nonneg.mpr hQP)
  nlinarith only [hprod,hinner]

theorem packet_clear (c g h j : ℝ) (p q r : ℕ)
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r) (hs : p+q+r ≤ 4)
    (hg : 0 < g) (hh : 0 < h) (hj : 0 < j) (m a b e rho : ℤ) (P : ℝ)
    (hhi : 8*(rho : ℝ)-27 ≤ 7*(g+h+j)+8*remainder g h j m a b e)
    (hQP : outerLapOpening g h j m a b e rho ≤ P)
    (houter : (4+g+h+j)*(P-outerLapOpening g h j m a b e rho) ≤ 3/4)
    (hinner : (4+g+h+j)*(P-outerLapOpening g h j m a b e rho)+3*(1-(P-(m : ℝ))) ≤ 3/4)
    (i : Fin 8) (hi : 4 ≤ (i : ℕ)) :
    (1/8 : ℝ) ≤ distInt ((speeds c g h j p q r i-speeds c g h j p q r 0)*P) := by
  have hQhi := frame_upper g h j hg hh hj m a b e rho hhi
  have hf4 := tail_phase c g h j p q r hp hq hr hs hg hh hj m a b e rho (4 : Fin 8) (by norm_num)
  have hd4 := tail_reading c g h j p q r hp hq hr hs (4 : Fin 8) (by norm_num)
  norm_num at hf4 hd4
  have hshift4 := mul_nonneg (by linarith : 0 ≤ (1 : ℝ)+g+h+j) (sub_nonneg.mpr hQP)
  have hphase4 : ((1 : ℝ)+g+h+j)*P-
      ((wholeLap m a b e p q r 4-wholeLap m a b e p q r 0 : ℤ) : ℝ)=
      (rho : ℝ)+1/8-(3 : ℝ)*(P-(m : ℝ))+
        (4+g+h+j)*(P-outerLapOpening g h j m a b e rho) := by
    rw [hd4] at hf4
    push_cast at hf4 ⊢
    nlinarith only [hf4]
  have hc4 : (1/8 : ℝ) ≤ distInt ((speeds c g h j p q r 4-speeds c g h j p q r 0)*P) := by
    rw [hd4]
    apply clear_of_window (wholeLap m a b e p q r 4-wholeLap m a b e p q r 0+rho-3)
    all_goals rw [hd4] at hf4; push_cast at hf4 hphase4 ⊢
    · nlinarith only [hf4,hshift4,hQhi]
    · linarith only [hphase4,houter,hinner]
  have hf5 := tail_phase c g h j p q r hp hq hr hs hg hh hj m a b e rho (5 : Fin 8) (by norm_num)
  have hd5 := tail_reading c g h j p q r hp hq hr hs (5 : Fin 8) (by norm_num)
  norm_num at hf5 hd5
  have hshift5 := mul_nonneg (by linarith : 0 ≤ (2 : ℝ)+g+h+j) (sub_nonneg.mpr hQP)
  have hphase5 : ((2 : ℝ)+g+h+j)*P-
      ((wholeLap m a b e p q r 5-wholeLap m a b e p q r 0 : ℤ) : ℝ)=
      (rho : ℝ)+1/8-(2 : ℝ)*(P-(m : ℝ))+
        (4+g+h+j)*(P-outerLapOpening g h j m a b e rho) := by
    rw [hd5] at hf5
    push_cast at hf5 ⊢
    nlinarith only [hf5]
  have hc5 : (1/8 : ℝ) ≤ distInt ((speeds c g h j p q r 5-speeds c g h j p q r 0)*P) := by
    rw [hd5]
    apply clear_of_window (wholeLap m a b e p q r 5-wholeLap m a b e p q r 0+rho-2)
    all_goals rw [hd5] at hf5; push_cast at hf5 hphase5 ⊢
    · nlinarith only [hf5,hshift5,hQhi]
    · linarith only [hphase5,houter,hinner]
  have hf6 := tail_phase c g h j p q r hp hq hr hs hg hh hj m a b e rho (6 : Fin 8) (by norm_num)
  have hd6 := tail_reading c g h j p q r hp hq hr hs (6 : Fin 8) (by norm_num)
  norm_num at hf6 hd6
  have hshift6 := mul_nonneg (by linarith : 0 ≤ (3 : ℝ)+g+h+j) (sub_nonneg.mpr hQP)
  have hphase6 : ((3 : ℝ)+g+h+j)*P-
      ((wholeLap m a b e p q r 6-wholeLap m a b e p q r 0 : ℤ) : ℝ)=
      (rho : ℝ)+1/8-(1 : ℝ)*(P-(m : ℝ))+
        (4+g+h+j)*(P-outerLapOpening g h j m a b e rho) := by
    rw [hd6] at hf6
    push_cast at hf6 ⊢
    nlinarith only [hf6]
  have hc6 : (1/8 : ℝ) ≤ distInt ((speeds c g h j p q r 6-speeds c g h j p q r 0)*P) := by
    rw [hd6]
    apply clear_of_window (wholeLap m a b e p q r 6-wholeLap m a b e p q r 0+rho-1)
    all_goals rw [hd6] at hf6; push_cast at hf6 hphase6 ⊢
    · nlinarith only [hf6,hshift6,hQhi]
    · linarith only [hphase6,houter,hinner]
  have hf7 := tail_phase c g h j p q r hp hq hr hs hg hh hj m a b e rho (7 : Fin 8) (by norm_num)
  have hd7 := tail_reading c g h j p q r hp hq hr hs (7 : Fin 8) (by norm_num)
  norm_num at hf7 hd7
  have hshift7 := mul_nonneg (by linarith : 0 ≤ (4 : ℝ)+g+h+j) (sub_nonneg.mpr hQP)
  have hphase7 : ((4 : ℝ)+g+h+j)*P-
      ((wholeLap m a b e p q r 7-wholeLap m a b e p q r 0 : ℤ) : ℝ)=
      (rho : ℝ)+1/8-(0 : ℝ)*(P-(m : ℝ))+
        (4+g+h+j)*(P-outerLapOpening g h j m a b e rho) := by
    rw [hd7] at hf7
    push_cast at hf7 ⊢
    nlinarith only [hf7]
  have hc7 : (1/8 : ℝ) ≤ distInt ((speeds c g h j p q r 7-speeds c g h j p q r 0)*P) := by
    rw [hd7]
    apply clear_of_window (wholeLap m a b e p q r 7-wholeLap m a b e p q r 0+rho-0)
    all_goals rw [hd7] at hf7; push_cast at hf7 hphase7 ⊢
    · nlinarith only [hf7,hshift7,hQhi]
    · linarith only [hphase7,houter,hinner]
  fin_cases i
  · norm_num at hi
  · norm_num at hi
  · norm_num at hi
  · norm_num at hi
  · exact hc4
  · exact hc5
  · exact hc6
  · exact hc7

theorem time_bounds (g h j : ℝ) (hg : 0 < g) (hh : 0 < h) (hj : 0 < j)
    (m a b e rho : ℤ) (P : ℝ)
    (hhi : 8*(rho : ℝ)-27 ≤ 7*(g+h+j)+8*remainder g h j m a b e)
    (hQP : outerLapOpening g h j m a b e rho ≤ P)
    (houter : (4+g+h+j)*(P-outerLapOpening g h j m a b e rho) ≤ 3/4)
    (hinner : (4+g+h+j)*(P-outerLapOpening g h j m a b e rho)+3*(1-(P-(m : ℝ))) ≤ 3/4) :
    (m : ℝ)+3/4 ≤ P ∧ P ≤ (m : ℝ)+19/16 := by
  have hQhi := frame_upper g h j hg hh hj m a b e rho hhi
  have hQlo := frame_lower g h j hg hh hj m (outerLapOpening g h j m a b e rho) P hQP hinner
  have hprod := mul_nonneg (by linarith : 0 ≤ g+h+j) (sub_nonneg.mpr hQP)
  constructor <;> nlinarith

theorem return_roles (g h j : ℝ) (hgpos : 0 < g) (hhpos : 0 < h) (hjpos : 0 < j)
    (m a b e rho : ℤ) (P : ℝ) (hsmall : g+h+j ≤ 3)
    (hg : 8*(a : ℝ)+1 ≤ (8*(m : ℝ)+1)*g)
    (hh : 8*(b : ℝ)+1 ≤ (8*(m : ℝ)+1)*h)
    (hj : 8*(e : ℝ)+1 ≤ (8*(m : ℝ)+1)*j)
    (hsum : (8*(m : ℝ)+1)*(g+h+j) ≤ 8*((a : ℝ)+(b : ℝ)+(e : ℝ))+4)
    (hhi : 8*(rho : ℝ)-27 ≤ 7*(g+h+j)+8*remainder g h j m a b e)
    (hQP : outerLapOpening g h j m a b e rho ≤ P)
    (hinner : (4+g+h+j)*(P-outerLapOpening g h j m a b e rho)+3*(1-(P-(m : ℝ))) ≤ 3/4) :
    rho=4 ∨ rho=5 ∨ rho=6 := by
  obtain ⟨hRlo,hRhi⟩ := native_remainder_band g h j m a b e hg hh hj hsum
  have hQlo := frame_lower g h j hgpos hhpos hjpos m (outerLapOpening g h j m a b e rho) P hQP hinner
  have hd := opening_delta g h j hgpos hhpos hjpos m a b e rho
  have hpD : 0 < 4+g+h+j := by linarith
  have hprod := mul_nonneg hpD.le (sub_nonneg.mpr hQlo)
  have hweak : 5*(g+h+j)+8*remainder g h j m a b e ≤ 8*(rho : ℝ)-19 := by
    nlinarith only [hd,hprod]
  have hstrict := Fresh.FourBlockInnerCaptureBounds.strict_capture_face g h j m a b e hsmall hRhi
  have hspos : 0 < g+h+j := by positivity
  have hrloR : (3 : ℝ) < rho := by linarith
  have hrhiR : (rho : ℝ) < 7 := by linarith
  have hrlo : (3 : ℤ) < rho := by exact_mod_cast hrloR
  have hrhi : rho < (7 : ℤ) := by exact_mod_cast hrhiR
  omega

#print axioms frame_upper
#print axioms frame_lower
#print axioms packet_clear
#print axioms time_bounds
#print axioms return_roles
end Fresh.FourBlockPacketFrame
