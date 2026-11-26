import Fresh.PhaseNeighbour

/-! Native retention before a named unit partner. A supplied phase lift and
physical order carry all earlier readings through an actual later opening.
No arbitrary phase representation or future isolated output is assumed. -/
namespace Fresh.EndpointRetainedSegment
open Fresh

theorem earlier_readings_clear (V X : Fin 8 → ℝ) (N : Fin 8 → ℤ) (T P : ℝ)
    (hphase : ∀i,V i*T=X i+(N i : ℝ))
    (hgap : ∀i : Fin 7,(1/8 : ℝ) ≤ X i.succ-X i.castSucc)
    (hmono : Monotone V) (hTP : T ≤ P)
    (k : Fin 8) (hpartner : (V k-V 0)*P-((N k-N 0 : ℤ) : ℝ) ≤ 1)
    (i : Fin 8) (hi0 : 0 < (i : ℕ)) (hi6 : i < k) :
    (1/8 : ℝ) ≤ distInt ((V i-V 0)*P) := by
  have h0i : (0 : Fin 8) < i := hi0
  have hi6' : i < k := hi6
  have hlo := Fresh.PhaseNeighbour.phase_separation X hgap 0 i h0i
  have hhi := Fresh.PhaseNeighbour.phase_separation X hgap i k hi6'
  have hDi : 0 ≤ V i-V 0 := sub_nonneg.mpr (hmono h0i.le)
  have hD6 : 0 ≤ V k-V i := sub_nonneg.mpr (hmono hi6'.le)
  have hΔ : 0 ≤ P-T := sub_nonneg.mpr hTP
  have hshift0 := mul_nonneg hDi hΔ
  have hshift6 := mul_nonneg hD6 hΔ
  have he0 : (V i-V 0)*P=((N i-N 0 : ℤ) : ℝ)+(X i-X 0)+(V i-V 0)*(P-T) := by
    have hi := hphase i
    have hz := hphase 0
    push_cast
    nlinarith only [hi,hz]
  have he6 : (V k-V 0)*P-((N k-N 0 : ℤ) : ℝ)-
      ((V i-V 0)*P-((N i-N 0 : ℤ) : ℝ))=
      X k-X i+(V k-V i)*(P-T) := by
    have hi := hphase i
    have hs := hphase k
    push_cast
    nlinarith only [hi,hs]
  apply Fresh.Localisation.clear_of_window (N i-N 0)
  all_goals push_cast at *
  all_goals linarith

#print axioms earlier_readings_clear
end Fresh.EndpointRetainedSegment
