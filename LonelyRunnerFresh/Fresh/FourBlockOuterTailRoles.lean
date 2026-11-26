import Fresh.FourBlockOuterTailClear

/-! The three original left labels are forced into a finite ordered set
by their native phase gaps and the supplied outer opening. -/
namespace Fresh.FourBlockOuterTailRoles
open Fresh Fresh.FourBlockNeighbour Fresh.FourBlockEndpointCapture
  Fresh.FourBlockLongTailBounds Fresh.FourBlockLongTailPhase
  Fresh.FourBlockOuterLapPhase Fresh.FourBlockOuterTailClear

theorem left_roles (c g h j : ℝ) (p q r : ℕ)
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r) (hs : p+q+r ≤ 4)
    (hgpos : 0 < g) (hhpos : 0 < h) (hjpos : 0 < j)
    (m a b e rho : ℤ) (L : Fin 3 → ℤ) (hsmall : g+h+j ≤ 3)
    (hg : 8*(a : ℝ)+1 ≤ (8*(m : ℝ)+1)*g)
    (hh : 8*(b : ℝ)+1 ≤ (8*(m : ℝ)+1)*h)
    (hj : 8*(e : ℝ)+1 ≤ (8*(m : ℝ)+1)*j)
    (hsum : (8*(m : ℝ)+1)*(g+h+j) ≤ 8*((a : ℝ)+(b : ℝ)+(e : ℝ))+4)
    (hlo : 11*(g+h+j)+16*remainder g h j m a b e ≤ 16*(rho : ℝ)-42)
    (hhi : 8*(rho : ℝ)-27 ≤ 7*(g+h+j)+8*remainder g h j m a b e)
    (hleft : LeftBands c g h j p q r m a b e rho L) :
    0 ≤ L 0 ∧ L 0 ≤ L 1 ∧ L 1 ≤ L 2 ∧ L 2 ≤ 3 := by
  let V := speeds c g h j p q r
  let N := wholeLap m a b e p q r
  let X := phase c g h j p q r m a b e
  let T : ℝ := (m : ℝ)+1/8
  let Q := outerLapOpening g h j m a b e rho
  let Y : Fin 8 → ℝ := fun i => (V i-V 0)*Q-((N i-N 0 : ℤ) : ℝ)
  obtain ⟨hPlo,hPhi⟩ := opening_bounds g h j hgpos hhpos hjpos m a b e rho hlo hhi
  have hdlo : 0 ≤ Q-T := by dsimp [Q,T]; linarith
  have hdhi : Q-T ≤ 7/8 := by dsimp [Q,T]; linarith
  have hgap := native_phase_gaps c g h j p q r hq hr m a b e hg hh hj
  have hmono := FourBlockEndpoints.speeds_monotone c g h j p q r hq hr hgpos hhpos hjpos
  have htransport (i : Fin 8) : Y i=X i-X 0+(V i-V 0)*(Q-T) := by
    have hi := phase_identity c g h j p q r m a b e i
    have h0 := phase_identity c g h j p q r m a b e 0
    change V i*T=X i+(N i : ℝ) at hi
    change V 0*T=X 0+(N 0 : ℝ) at h0
    dsimp [Y]
    push_cast
    nlinarith only [hi,h0]
  have hsep (i j : Fin 8) (hij : i < j) : (1/8 : ℝ) ≤ Y j-Y i := by
    have hx := Fresh.PhaseNeighbour.phase_separation X hgap i j hij
    have hm := mul_nonneg (sub_nonneg.mpr (hmono hij.le)) hdlo
    rw [htransport i,htransport j]
    nlinarith only [hx,hm]
  have hspan : X 7-X 0 ≤ 1 := by
    have hid := phase_span c g h j p q r hp hq hr (by omega) m a b e
    change X 7-X 0=_ at hid
    rw [hid]
    nlinarith only [hsum]
  have hX3 : X 3-X 0 ≤ 1/2 := by
    have h3 := hgap 3
    have h4 := hgap 4
    have h5 := hgap 5
    have h6 := hgap 6
    change (1/8 : ℝ) ≤ X 4-X 3 at h3
    change (1/8 : ℝ) ≤ X 5-X 4 at h4
    change (1/8 : ℝ) ≤ X 6-X 5 at h5
    change (1/8 : ℝ) ≤ X 7-X 6 at h6
    linarith
  have hV3 : V 3-V 0 ≤ 4 := by
    have hm := hmono (show (3 : Fin 8) ≤ 4 by decide)
    have h4 := tail_reading c g h j p q r hp hq hr hs (4 : Fin 8) (by norm_num)
    norm_num at h4
    change V 4-V 0=1+g+h+j at h4
    linarith
  have hprod := mul_nonneg (sub_nonneg.mpr hV3) hdlo
  have hY3 : Y 3 ≤ 4 := by
    rw [htransport 3]
    nlinarith only [hX3,hprod,hdhi]
  have hband (u : Fin 3) : (L u : ℝ)+1/8 ≤ Y (prefixIndex u) ∧
      Y (prefixIndex u) ≤ (L u : ℝ)+7/8 := by
    have hb := hleft u
    dsimp [Y,V,N,Q]
    push_cast at hb ⊢
    constructor <;> linarith [hb.1,hb.2]
  have h0 := hband 0
  have h1 := hband 1
  have h2 := hband 2
  change (L 0 : ℝ)+1/8 ≤ Y 1 ∧ Y 1 ≤ (L 0 : ℝ)+7/8 at h0
  change (L 1 : ℝ)+1/8 ≤ Y 2 ∧ Y 2 ≤ (L 1 : ℝ)+7/8 at h1
  change (L 2 : ℝ)+1/8 ≤ Y 3 ∧ Y 3 ≤ (L 2 : ℝ)+7/8 at h2
  have hy0 : Y 0=0 := by simp [Y]
  have hy1 := hsep 0 1 (by decide)
  have hy12 := hsep 1 2 (by decide)
  have hy23 := hsep 2 3 (by decide)
  have heR : (-1 : ℝ) < L 0 := by linarith
  have he : (-1 : ℤ) < L 0 := by exact_mod_cast heR
  have h01R : (L 0 : ℝ) < (L 1 : ℝ)+1 := by linarith
  have h01 : L 0 < L 1+1 := by exact_mod_cast h01R
  have h12R : (L 1 : ℝ) < (L 2 : ℝ)+1 := by linarith
  have h12 : L 1 < L 2+1 := by exact_mod_cast h12R
  have h2R : (L 2 : ℝ) < 4 := by linarith
  have h2Z : L 2 < (4 : ℤ) := by exact_mod_cast h2R
  omega

#print axioms left_roles
end Fresh.FourBlockOuterTailRoles
