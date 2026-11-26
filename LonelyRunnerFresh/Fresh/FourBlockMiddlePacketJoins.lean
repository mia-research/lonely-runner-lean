import Fresh.FourBlockMiddlePacketArrangement

/-! Physical overlap reduction: a nonsingleton first block needs no displaced
endpoint witness. Only four middle-packet shapes remain outside that earlier
native all-subject family. This is a reduction of proved input families. -/
namespace Fresh.FourBlockMiddlePacketJoins
open Fresh Fresh.FourBlockMiddlePacket Fresh.FourBlockMiddlePacketArrangement

theorem nonsingleton_into_direct {V : Fin 8 → ℝ} {p q r : ℕ} {start : Fin 6} {u : Fin 7} {role : Fin 6}
    (hV : MiddlePacketClassAt V p q r start u role) (hp2 : 2 ≤ p) :
    Fresh.FourBlockArrangement.FourBlockClass V := by
  obtain ⟨hpos,hinj,c,g,h,j,B,z,m,a,b,e,rho,unitLap,window,L,σ,hp,hq,hr,hhost,hg,hh,hj,hm,hsmall,
    hga,hgb,hge,hsum,hP,hpacket,hcuts,hz,hrepr⟩ := hV
  have hs := hhost.1
  exact ⟨hpos,hinj,c,g,h,j,B,z,p,q,r,m,a,b,e,σ,hp,hq,hr,by omega,
    hg,hh,hj,hsmall,by intro hbad; omega,by intro hbad; omega,hm,hga,hgb,hge,hsum,hz,hrepr⟩

theorem nondirect_middle_shape {V : Fin 8 → ℝ} (hV : MiddlePacketClass V)
    (hnot : ¬ Fresh.FourBlockArrangement.FourBlockClass V) :
    ∃ (q r : ℕ) (start : Fin 6) (u : Fin 7) (role : Fin 6),
      ((q=4 ∧ r=1 ∧ start.val=1) ∨ (q=3 ∧ r=2 ∧ start.val=1) ∨
       (q=1 ∧ r=4 ∧ start.val=2) ∨ (q=2 ∧ r=3 ∧ start.val=3)) ∧
      MiddlePacketClassAt V 1 q r start u role := by
  obtain ⟨p,q,r,start,u,role,hAt⟩ := hV
  have hsave := hAt
  obtain ⟨_,_,c,g,h,j,B,z,m,a,b,e,rho,unitLap,window,L,σ,hp,hq,hr,hhost,_⟩ := hAt
  have hpeq : p=1 := by
    by_contra hn
    exact hnot (nonsingleton_into_direct hsave (by omega))
  subst p
  refine ⟨q,r,start,u,role,?_,hsave⟩
  have hc := host_cases 1 q r start (by omega) hq hr hhost
  omega

#print axioms nonsingleton_into_direct
#print axioms nondirect_middle_shape
end Fresh.FourBlockMiddlePacketJoins
