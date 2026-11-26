import Fresh.FourBlockOuterLapClear

/-! Finite integer roles forced by the native opening and cut identities.
No bound on the number of cascade moves or on arbitrary arrangements is used. -/
namespace Fresh.FourBlockOuterLapRoles
open Fresh Fresh.FourBlockNeighbour Fresh.FourBlockEndpointCapture
  Fresh.FourBlockLongTailPhase Fresh.FourBlockOuterLapPhase Fresh.FourBlockOuterLapClear

theorem return_role (g h j : ℝ) (hgpos : 0 < g) (hhpos : 0 < h) (hjpos : 0 < j)
    (m a b e r : ℤ) (hsmall : g+h+j ≤ 3)
    (hg : 8*(a : ℝ)+1 ≤ (8*(m : ℝ)+1)*g)
    (hh : 8*(b : ℝ)+1 ≤ (8*(m : ℝ)+1)*h)
    (hj : 8*(e : ℝ)+1 ≤ (8*(m : ℝ)+1)*j)
    (hsum : (8*(m : ℝ)+1)*(g+h+j) ≤ 8*((a : ℝ)+(b : ℝ)+(e : ℝ))+4)
    (hlo : 11*(g+h+j)+16*remainder g h j m a b e ≤ 16*(r : ℝ)-42)
    (hhi : 8*(r : ℝ)-27 ≤ 7*(g+h+j)+8*remainder g h j m a b e) :
    r=4 ∨ r=5 ∨ r=6 := by
  obtain ⟨hRlo,hRhi⟩ := native_remainder_band g h j m a b e hg hh hj hsum
  have hstrict := Fresh.FourBlockInnerCaptureBounds.strict_capture_face g h j m a b e hsmall hRhi
  have hspos : 0 < g+h+j := by positivity
  have hrloR : (3 : ℝ) < r := by linarith
  have hrhiR : (r : ℝ) < 7 := by linarith
  have hrlo : (3 : ℤ) < r := by exact_mod_cast hrloR
  have hrhi : r < (7 : ℤ) := by exact_mod_cast hrhiR
  omega

theorem cut_roles (c g h j : ℝ) (hgpos : 0 < g) (hhpos : 0 < h) (hjpos : 0 < j)
    (m a b e r ell kappa : ℤ) (hsmall : g+h+j ≤ 3)
    (hg : 8*(a : ℝ)+1 ≤ (8*(m : ℝ)+1)*g)
    (hh : 8*(b : ℝ)+1 ≤ (8*(m : ℝ)+1)*h)
    (hj : 8*(e : ℝ)+1 ≤ (8*(m : ℝ)+1)*j)
    (hsum : (8*(m : ℝ)+1)*(g+h+j) ≤ 8*((a : ℝ)+(b : ℝ)+(e : ℝ))+4)
    (hlo : 11*(g+h+j)+16*remainder g h j m a b e ≤ 16*(r : ℝ)-42)
    (hhi : 8*(r : ℝ)-27 ≤ 7*(g+h+j)+8*remainder g h j m a b e)
    (hslo : (ell : ℝ)+1/8 ≤ g*outerLapOpening g h j m a b e r-(a : ℝ))
    (hshi : g*outerLapOpening g h j m a b e r-(a : ℝ) ≤ (ell : ℝ)+7/8)
    (hclo : (r : ℝ)-(kappa : ℝ)-3/4 ≤ j*outerLapOpening g h j m a b e r-(e : ℝ)+
      4*(outerLapOpening g h j m a b e r-(m : ℝ)))
    (hchi : j*outerLapOpening g h j m a b e r-(e : ℝ)+
      4*(outerLapOpening g h j m a b e r-(m : ℝ)) ≤ (r : ℝ)-(kappa : ℝ)) :
    0 ≤ ell ∧ ell ≤ kappa ∧ kappa ≤ 2 := by
  obtain ⟨hPlo,hPhi⟩ := opening_bounds g h j hgpos hhpos hjpos m a b e r hlo hhi
  have hdlo : 0 ≤ outerLapOpening g h j m a b e r-((m : ℝ)+1/8) := by linarith
  have hdhi : outerLapOpening g h j m a b e r-((m : ℝ)+1/8) ≤ 7/8 := by linarith
  have hgs := mul_nonneg hgpos.le hdlo
  have hhs := mul_nonneg hhpos.le hdlo
  have hgl : (1/8 : ℝ) ≤ g*outerLapOpening g h j m a b e r-(a : ℝ) := by nlinarith only [hg,hgs]
  have hhl : (1/8 : ℝ) ≤ h*outerLapOpening g h j m a b e r-(b : ℝ) := by nlinarith only [hh,hhs]
  have hjref : (1/8 : ℝ) ≤ j*((m : ℝ)+1/8)-(e : ℝ) := by nlinarith only [hj]
  have hprod := mul_nonneg (by linarith : 0 ≤ 3-(g+h)) hdlo
  have htwohi : (g+h)*outerLapOpening g h j m a b e r-(a : ℝ)-(b : ℝ) ≤ 3 := by
    nlinarith only [hprod,hdhi,hsum,hjref]
  have hf2 := cut_phase c g h j hgpos hhpos hjpos m a b e r
  norm_num [speeds,wholeLap] at hf2
  have hklo : (kappa : ℝ)+1/8 ≤ (g+h)*outerLapOpening g h j m a b e r-(a : ℝ)-(b : ℝ) := by
    nlinarith only [hf2,hchi]
  have hkhi : (g+h)*outerLapOpening g h j m a b e r-(a : ℝ)-(b : ℝ) ≤ (kappa : ℝ)+7/8 := by
    nlinarith only [hf2,hclo]
  have heR : (-1 : ℝ) < ell := by linarith
  have he : (-1 : ℤ) < ell := by exact_mod_cast heR
  have hekR : (ell : ℝ) < (kappa : ℝ)+1 := by nlinarith only [hslo,hkhi,hhl]
  have hek : ell < kappa+1 := by exact_mod_cast hekR
  have hkR : (kappa : ℝ) < 3 := by linarith
  have hk : kappa < (3 : ℤ) := by exact_mod_cast hkR
  omega

#print axioms return_role
#print axioms cut_roles
end Fresh.FourBlockOuterLapRoles
