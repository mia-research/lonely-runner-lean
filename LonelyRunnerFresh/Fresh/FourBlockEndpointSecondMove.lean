import Fresh.FourBlockEndpointUnitPartner
import Fresh.EndpointRetainedPacket

/-! The native first endpoint move forces its far unit AP partner to be the
next setter, retaining every other original reading. Later returns remain
separate; no descending-order or termination claim is inferred. -/
namespace Fresh.FourBlockEndpointSecondMove
open Fresh Fresh.Cascade Fresh.Localisation Fresh.FourBlockNeighbour
  Fresh.FourBlockEndpointCapture Fresh.FourBlockEndpointUnitPartner

theorem unit_partner_next_move (c g h j : ℝ) (p q r : ℕ)
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r) (hs : p+q+r ≤ 6)
    (hgpos : 0 < g) (hhpos : 0 < h) (hjpos : 0 < j) (m a b e : ℤ)
    (hg : 8*(a : ℝ)+1 ≤ (8*(m : ℝ)+1)*g)
    (hh : 8*(b : ℝ)+1 ≤ (8*(m : ℝ)+1)*h)
    (hj : 8*(e : ℝ)+1 ≤ (8*(m : ℝ)+1)*j)
    (hsum : (8*(m : ℝ)+1)*(g+h+j) ≤ 8*((a : ℝ)+(b : ℝ)+(e : ℝ))+4)
    (hcap : (7/8 : ℝ) < remainder g h j m a b e) :
    IsMove (disparitySet (speeds c g h j p q r) 0) (outerOpening g h j m a b e)
      ((((spanLap m a b e-m : ℤ) : ℝ)+9/8)/(3+g+h+j)) := by
  have hrem : remainder g h j m a b e ≤ 1 := by dsimp [remainder]; nlinarith
  obtain ⟨hTP,hPhi⟩ := outer_opening_bounds g h j hgpos hhpos hjpos m a b e hcap hrem
  obtain ⟨hw6,hop6⟩ := unit_partner_capture c g h j p q r hp hq hr hs hgpos hhpos hjpos m a b e hcap hrem
  have hmono := FourBlockEndpoints.speeds_monotone c g h j p q r hq hr hgpos hhpos hjpos
  have hu : (1/8 : ℝ) ≤ g*((m : ℝ)+1/8)-(a : ℝ) := by nlinarith
  have hv : (1/8 : ℝ) ≤ h*((m : ℝ)+1/8)-(b : ℝ) := by nlinarith
  have hw : (1/8 : ℝ) ≤ j*((m : ℝ)+1/8)-(e : ℝ) := by nlinarith
  have hgap : ∀i : Fin 7,(1/8 : ℝ) ≤
      phase c g h j p q r m a b e i.succ-phase c g h j p q r m a b e i.castSucc := by
    intro i
    rw [adjacent_phase_gap c g h j p q r hq hr m a b e i]
    split_ifs <;> linarith
  have hD : 0 < 4+g+h+j := by linarith
  have hDne : 4+g+h+j≠0 := ne_of_gt hD
  have hP : (4+g+h+j)*outerOpening g h j m a b e=(spanLap m a b e : ℝ)+9/8 := by
    dsimp [outerOpening]
    field_simp [hDne]
  have hspan := FourBlockEndpoints.speed_span c g h j p q r hp hq hr (by omega)
  have hstep := FourBlockEndpoints.adjacent_speed_gap c g h j p q r hq hr (6 : Fin 7)
  change speeds c g h j p q r 7-speeds c g h j p q r 6=
    (if (7 : ℕ)=p then g else if (7 : ℕ)=p+q then h else if (7 : ℕ)=p+q+r then j else 1) at hstep
  have hc1 : (7 : ℕ)≠p := by omega
  have hc2 : (7 : ℕ)≠p+q := by omega
  have hc3 : (7 : ℕ)≠p+q+r := by omega
  simp only [if_neg hc1,if_neg hc2,if_neg hc3] at hstep
  have hD6 : speeds c g h j p q r 6-speeds c g h j p q r 0=3+g+h+j := by linarith
  have hN6 : wholeLap m a b e p q r 6-wholeLap m a b e p q r 0=spanLap m a b e-m := by
    have h0p : ¬p ≤ 0 := by omega
    have h0q : ¬p+q ≤ 0 := by omega
    have h0r : ¬p+q+r ≤ 0 := by omega
    have h6p : p ≤ 6 := by omega
    have h6q : p+q ≤ 6 := by omega
    norm_num [wholeLap,spanLap,h0p,h0q,h0r,h6p,h6q,hs]
    ring
  have hpartner : (speeds c g h j p q r 6-speeds c g h j p q r 0)*outerOpening g h j m a b e-
      ((wholeLap m a b e p q r 6-wholeLap m a b e p q r 0 : ℤ) : ℝ) ≤ 1 := by
    rw [hD6,hN6]
    push_cast
    nlinarith only [hP,hTP]
  have hc7 : (1/8 : ℝ) ≤ distInt ((speeds c g h j p q r 7-speeds c g h j p q r 0)*outerOpening g h j m a b e) := by
    rw [hspan,hP]
    apply clear_of_window (spanLap m a b e+1) <;> push_cast <;> linarith
  refine Or.inr ⟨|speeds c g h j p q r 6-speeds c g h j p q r 0|,
    mem_disparitySet.mpr ⟨6,by decide,rfl⟩,hw6,hop6.symm,?_⟩
  intro d hd hwD
  obtain ⟨i,hi0,rfl⟩ := mem_disparitySet.mp hd
  by_cases hi6 : i=6
  · subst i
    exact hop6.le
  · by_cases hi7 : i=7
    · subst i
      change distInt (|speeds c g h j p q r 7-speeds c g h j p q r 0| * outerOpening g h j m a b e) < 1/8 at hwD
      rw [Fresh.Localisation.distInt_abs_mul] at hwD
      exact False.elim ((not_lt_of_ge hc7) hwD)
    · have hi0val : 0 < (i : ℕ) := by
        have := Fin.val_ne_of_ne hi0
        omega
      have hi6val : (i : ℕ) < 6 := by
        have := Fin.val_ne_of_ne hi6
        have := Fin.val_ne_of_ne hi7
        have := i.isLt
        omega
      have hci := Fresh.EndpointRetainedPacket.earlier_readings_clear
        (speeds c g h j p q r) (phase c g h j p q r m a b e) (wholeLap m a b e p q r)
        ((m : ℝ)+1/8) (outerOpening g h j m a b e)
        (phase_identity c g h j p q r m a b e) hgap hmono hTP.le hpartner i hi0val hi6val
      change distInt (|speeds c g h j p q r i-speeds c g h j p q r 0| * outerOpening g h j m a b e) < 1/8 at hwD
      rw [Fresh.Localisation.distInt_abs_mul] at hwD
      exact False.elim ((not_lt_of_ge hci) hwD)

#print axioms unit_partner_next_move
end Fresh.FourBlockEndpointSecondMove
