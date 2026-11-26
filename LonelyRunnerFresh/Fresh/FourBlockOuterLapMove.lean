import Fresh.FourBlockOuterLapArrangement

/-! Original runner6 can hand off to the outer endpoint on any retained
integer return lap. The exit is proved from native cuts, not assumed. -/
namespace Fresh.FourBlockOuterLapMove
open Fresh Fresh.Cascade Fresh.Localisation Fresh.FourBlockNeighbour
  Fresh.FourBlockEndpointCapture Fresh.FourBlockOuterLapPhase Fresh.FourBlockOuterLapClear

noncomputable def sixLapOpening (g h j : ℝ) (m a b e q : ℤ) : ℝ :=
  (((3*m+a+b+e : ℤ) : ℝ)+(q : ℝ)+1/8)/(3+g+h+j)

theorem six_identity (g h j : ℝ) (hg : 0 < g) (hh : 0 < h) (hj : 0 < j)
    (m a b e q : ℤ) :
    (3+g+h+j)*sixLapOpening g h j m a b e q=((3*m+a+b+e : ℤ) : ℝ)+(q : ℝ)+1/8 := by
  have hp : 0 < 3+g+h+j := by linarith
  dsimp [sixLapOpening]
  field_simp [ne_of_gt hp]

theorem six_packet_phase (c g h j : ℝ) (hg : 0 < g) (hh : 0 < h) (hj : 0 < j)
    (m a b e q : ℤ) (i : Fin 8) (hi : 3 ≤ (i : ℕ)) :
    (speeds c g h j 1 1 1 i-speeds c g h j 1 1 1 0)*sixLapOpening g h j m a b e q-
      ((wholeLap m a b e 1 1 1 i-wholeLap m a b e 1 1 1 0 : ℤ) : ℝ)=
      (q : ℝ)+1/8+((i : ℝ)-6)*(sixLapOpening g h j m a b e q-(m : ℝ)) := by
  let N : Fin 8 → ℤ := fun u=>wholeLap m a b e 1 1 1 u-wholeLap m a b e 1 1 1 0
  have h1 : (1 : ℕ) ≤ (i : ℕ) := by omega
  have h2 : (2 : ℕ) ≤ (i : ℕ) := by omega
  have hs : speeds c g h j 1 1 1 i-speeds c g h j 1 1 1 6=((i : ℝ)-6)*1 := by
    norm_num [speeds,h1,h2,hi]
  have hn : N i-N 6=(((i : ℕ) : ℤ)-((6 : Fin 8) : ℕ))*m := by
    dsimp [N]
    norm_num [wholeLap,h1,h2,hi]
    ring
  have ha : (speeds c g h j 1 1 1 6-speeds c g h j 1 1 1 0)*sixLapOpening g h j m a b e q=
      (N 6 : ℝ)+(q : ℝ)+1/8 := by
    have hid := six_identity g h j hg hh hj m a b e q
    norm_num [N,wholeLap,speeds] at *
    nlinarith only [hid]
  have hp := Fresh.UnitAPPacketPhase.phase_at_anchor (speeds c g h j 1 1 1) N 0 6 i 1
    (sixLapOpening g h j m a b e q) m q hs hn ha
  norm_num at hp
  exact hp

theorem outer_move_from (c g h j : ℝ) (hg : 0 < g) (hh : 0 < h) (hj : 0 < j)
    (m a b e r ell kappa : ℤ) (t : ℝ)
    (hlo : 11*(g+h+j)+16*remainder g h j m a b e ≤ 16*(r : ℝ)-42)
    (hhi : 8*(r : ℝ)-27 ≤ 7*(g+h+j)+8*remainder g h j m a b e)
    (hslo : (ell : ℝ)+1/8 ≤ g*outerLapOpening g h j m a b e r-(a : ℝ))
    (hshi : g*outerLapOpening g h j m a b e r-(a : ℝ) ≤ (ell : ℝ)+7/8)
    (hclo : (r : ℝ)-(kappa : ℝ)-3/4 ≤ j*outerLapOpening g h j m a b e r-(e : ℝ)+
      4*(outerLapOpening g h j m a b e r-(m : ℝ)))
    (hchi : j*outerLapOpening g h j m a b e r-(e : ℝ)+
      4*(outerLapOpening g h j m a b e r-(m : ℝ)) ≤ (r : ℝ)-(kappa : ℝ))
    (hcaplo : (r : ℝ)-1/8 < (4+g+h+j)*t-(spanLap m a b e : ℝ))
    (hcaphi : (4+g+h+j)*t-(spanLap m a b e : ℝ) < (r : ℝ)+1/8) :
    IsMove (disparitySet (speeds c g h j 1 1 1) 0) t (outerLapOpening g h j m a b e r) := by
  have hD7 : speeds c g h j 1 1 1 7-speeds c g h j 1 1 1 0=4+g+h+j := by
    norm_num [speeds]
    ring
  have hpos7 : 0 < speeds c g h j 1 1 1 7-speeds c g h j 1 1 1 0 := by rw [hD7]; positivity
  have hN7 : wholeLap m a b e 1 1 1 7-wholeLap m a b e 1 1 1 0=spanLap m a b e := by
    norm_num [wholeLap,spanLap]
    ring
  have hnear : |(speeds c g h j 1 1 1 7-speeds c g h j 1 1 1 0)*t-
      ((wholeLap m a b e 1 1 1 7-wholeLap m a b e 1 1 1 0+r : ℤ) : ℝ)| < 1/8 := by
    rw [abs_lt,hD7,hN7]
    push_cast
    constructor <;> linarith
  have hw7 : InWay |speeds c g h j 1 1 1 7-speeds c g h j 1 1 1 0| t := by
    rw [abs_of_pos hpos7]
    exact lt_of_le_of_lt (Fresh.Cascade.distInt_le _ (wholeLap m a b e 1 1 1 7-wholeLap m a b e 1 1 1 0+r)) hnear
  have hop7 : nextOpening |speeds c g h j 1 1 1 7-speeds c g h j 1 1 1 0| t=
      outerLapOpening g h j m a b e r := by
    rw [abs_of_pos hpos7,nextOpening_eq hnear,hD7,hN7]
    dsimp [outerLapOpening]
    push_cast
    rfl
  have hmem : |speeds c g h j 1 1 1 7-speeds c g h j 1 1 1 0| ∈
      disparitySet (speeds c g h j 1 1 1) 0 := mem_disparitySet.mpr ⟨7,by decide,rfl⟩
  have hpos : ∀ d ∈ disparitySet (speeds c g h j 1 1 1) 0, 0 < d := by
    intro d hd
    obtain ⟨i,hi0,rfl⟩ := mem_disparitySet.mp hd
    apply abs_pos.mpr
    have hstrict : StrictMono (speeds c g h j 1 1 1) := by
      apply Fin.strictMono_iff_lt_succ.mpr
      intro u
      have hd := FourBlockEndpoints.adjacent_speed_gap c g h j 1 1 1 (by norm_num) (by norm_num) u
      split_ifs at hd <;> linarith
    exact sub_ne_zero.mpr (fun heq => hi0 (hstrict.injective heq))
  have htime : t ≤ outerLapOpening g h j m a b e r := by
    rw [←hop7]
    exact (lt_nextOpening (by rw [abs_of_pos hpos7]; exact hpos7) hw7).le
  have hclear := outer_clear c g h j hg hh hj m a b e r ell kappa hlo hhi hslo hshi hclo hchi
  refine Or.inr ⟨_,hmem,hw7,hop7.symm,?_⟩
  intro d hd hwD
  exact nextOpening_le_of_lonely hpos hclear htime hd hwD

theorem six_handoff (c g h j : ℝ) (hg : 0 < g) (hh : 0 < h) (hj : 0 < j)
    (m a b e q ell kappa : ℤ)
    (hlo : 11*(g+h+j)+16*remainder g h j m a b e ≤ 16*((q+1 : ℤ) : ℝ)-42)
    (hhi : 8*((q+1 : ℤ) : ℝ)-27 ≤ 7*(g+h+j)+8*remainder g h j m a b e)
    (hslo : (ell : ℝ)+1/8 ≤ g*outerLapOpening g h j m a b e (q+1)-(a : ℝ))
    (hshi : g*outerLapOpening g h j m a b e (q+1)-(a : ℝ) ≤ (ell : ℝ)+7/8)
    (hclo : ((q+1 : ℤ) : ℝ)-(kappa : ℝ)-3/4 ≤ j*outerLapOpening g h j m a b e (q+1)-(e : ℝ)+
      4*(outerLapOpening g h j m a b e (q+1)-(m : ℝ)))
    (hchi : j*outerLapOpening g h j m a b e (q+1)-(e : ℝ)+
      4*(outerLapOpening g h j m a b e (q+1)-(m : ℝ)) ≤ ((q+1 : ℤ) : ℝ)-(kappa : ℝ))
    (htlo : (m : ℝ)+3/4 < sixLapOpening g h j m a b e q)
    (hthi : sixLapOpening g h j m a b e q < (m : ℝ)+1) :
    IsMove (disparitySet (speeds c g h j 1 1 1) 0)
      (sixLapOpening g h j m a b e q) (outerLapOpening g h j m a b e (q+1)) := by
  have hf7 := six_packet_phase c g h j hg hh hj m a b e q (7 : Fin 8) (by norm_num)
  norm_num [speeds,wholeLap,spanLap] at hf7
  apply outer_move_from c g h j hg hh hj m a b e (q+1) ell kappa
    (sixLapOpening g h j m a b e q) hlo hhi hslo hshi hclo hchi
  all_goals dsimp [spanLap]; push_cast at hf7 ⊢; nlinarith only [hf7,htlo,hthi]

#print axioms six_identity
#print axioms six_packet_phase
#print axioms outer_move_from
#print axioms six_handoff
end Fresh.FourBlockOuterLapMove
