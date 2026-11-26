import Fresh.Localisation

/-! One native AP-packet rule, independent of which physical runner opens
and which retained return lap it opens on. Physical speeds stay moving;
integer lap labels and exact unit-step differences are explicit inputs. -/
namespace Fresh.UnitAPPacketPhase
open Fresh

theorem phase_at_anchor (V : Fin 8 → ℝ) (N : Fin 8 → ℤ)
    (subject anchor i : Fin 8) (u P : ℝ) (m q : ℤ)
    (hstep : V i-V anchor=((i : ℝ)-(anchor : ℝ))*u)
    (hlap : N i-N anchor=(((i : ℕ) : ℤ)-((anchor : ℕ) : ℤ))*m)
    (hanchor : (V anchor-V subject)*P=(N anchor : ℝ)+(q : ℝ)+1/8) :
    (V i-V subject)*P-(N i : ℝ)=
      (q : ℝ)+1/8+((i : ℝ)-(anchor : ℝ))*(u*P-(m : ℝ)) := by
  have hlapR : (N i : ℝ)-(N anchor : ℝ)=((i : ℝ)-(anchor : ℝ))*(m : ℝ) := by
    have hc := congrArg (fun z : ℤ => (z : ℝ)) hlap
    push_cast at hc
    exact hc
  calc
    _ = (V anchor-V subject)*P-(N anchor : ℝ)+(V i-V anchor)*P-
        ((N i : ℝ)-(N anchor : ℝ)) := by ring
    _ = _ := by rw [hanchor,hstep,hlapR]; ring

#print axioms phase_at_anchor
end Fresh.UnitAPPacketPhase
