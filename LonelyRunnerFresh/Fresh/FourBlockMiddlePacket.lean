import Fresh.FourBlockRecoveryHandoffs

/-! The same native three-reading AP charts in an original middle block.
Only the physical position and its retained integer phase lift change. -/
namespace Fresh.FourBlockMiddlePacket
set_option maxHeartbeats 2000000
open Fresh Fresh.Cascade Fresh.Localisation Fresh.FourBlockNeighbour Fresh.FourBlockShortOpening

def middleIndex (b : Fin 6) (i : Fin 3) : Fin 8 := ⟨b.val+i.val,by have := b.isLt; have := i.isLt; omega⟩

def MiddleHost (p q r : ℕ) (b : Fin 6) : Prop :=
  p+q+r=6 ∧ ((b.val=p ∧ 3≤q) ∨ (b.val=p+q ∧ 3≤r))

theorem host_cases (p q r : ℕ) (b : Fin 6) (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r)
    (hh : MiddleHost p q r b) :
    (p=1 ∧ q=4 ∧ r=1 ∧ b.val=1) ∨ (p=1 ∧ q=3 ∧ r=2 ∧ b.val=1) ∨
    (p=2 ∧ q=3 ∧ r=1 ∧ b.val=2) ∨ (p=1 ∧ q=1 ∧ r=4 ∧ b.val=2) ∨
    (p=1 ∧ q=2 ∧ r=3 ∧ b.val=3) ∨ (p=2 ∧ q=1 ∧ r=3 ∧ b.val=3) := by
  rcases hh with ⟨hs,hleft|hright⟩ <;> omega

theorem packet_steps (c g h j : ℝ) (p q r : ℕ) (b : Fin 6)
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r) (hh : MiddleHost p q r b)
    (m a d e : ℤ) (i : Fin 3) :
    speeds c g h j p q r (middleIndex b i)-speeds c g h j p q r (middleIndex b 0)=(i : ℝ) ∧
    wholeLap m a d e p q r (middleIndex b i)-wholeLap m a d e p q r (middleIndex b 0)=(i.val : ℤ)*m := by
  rcases host_cases p q r b hp hq hr hh with hs|hs|hs|hs|hs|hs
  all_goals obtain ⟨rfl,rfl,rfl,hb⟩ := hs
  all_goals fin_cases b <;> norm_num at hb
  all_goals fin_cases i <;> norm_num [middleIndex,speeds,wholeLap] <;> (try constructor) <;> ring

noncomputable def firstPhase (c g h j : ℝ) (p q r : ℕ) (b : Fin 6) (m a d e : ℤ) (P : ℝ) : ℝ :=
  (speeds c g h j p q r (middleIndex b 0)-speeds c g h j p q r 0)*P-
    ((wholeLap m a d e p q r (middleIndex b 0)-wholeLap m a d e p q r 0 : ℤ) : ℝ)

noncomputable def PacketBands (c g h j : ℝ) (p q r : ℕ) (b : Fin 6)
    (m a d e unitLap window : ℤ) (role : Fin 6) (P : ℝ) : Prop :=
  Fresh.UnitAPPacketThreeCharts.Chart role (firstPhase c g h j p q r b m a d e P-(window : ℝ)) (P-(m : ℝ)-(unitLap : ℝ))

def RemainingBands (c g h j : ℝ) (p q r : ℕ) (b : Fin 6) (m a d e : ℤ)
    (P : ℝ) (L : Fin 8 → ℤ) (u : Fin 7) : Prop :=
  ∀ i : Fin 8, i≠0 → i≠openingIndex u → (i.val < b.val ∨ b.val+3 ≤ i.val) →
    ((wholeLap m a d e p q r i-wholeLap m a d e p q r 0+L i : ℤ) : ℝ)+1/8 ≤
      (speeds c g h j p q r i-speeds c g h j p q r 0)*P ∧
    (speeds c g h j p q r i-speeds c g h j p q r 0)*P ≤
      ((wholeLap m a d e p q r i-wholeLap m a d e p q r 0+L i : ℤ) : ℝ)+7/8

theorem packet_phase (c g h j : ℝ) (p q r : ℕ) (b : Fin 6)
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r) (hh : MiddleHost p q r b)
    (m a d e : ℤ) (P : ℝ) (i : Fin 3) :
    (speeds c g h j p q r (middleIndex b i)-speeds c g h j p q r 0)*P-
      ((wholeLap m a d e p q r (middleIndex b i)-wholeLap m a d e p q r 0 : ℤ) : ℝ)=
      firstPhase c g h j p q r b m a d e P+(i : ℝ)*(P-(m : ℝ)) := by
  obtain ⟨hstep,hlap⟩ := packet_steps c g h j p q r b hp hq hr hh m a d e i
  have hn := congrArg (fun z : ℤ => (z : ℝ)) hlap
  push_cast at hn
  dsimp [firstPhase]
  push_cast
  have hscaled := congrArg (fun x : ℝ => x*P) hstep
  nlinarith only [hscaled,hn]

theorem packet_clear (c g h j : ℝ) (p q r : ℕ) (b : Fin 6)
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r) (hh : MiddleHost p q r b)
    (m a d e unitLap window : ℤ) (role : Fin 6) (P : ℝ)
    (hc : PacketBands c g h j p q r b m a d e unitLap window role P) (i : Fin 3) :
    (1/8 : ℝ) ≤ distInt ((speeds c g h j p q r (middleIndex b i)-speeds c g h j p q r 0)*P) := by
  have hwin := Fresh.UnitAPPacketThreeCharts.chart_windows role
    (firstPhase c g h j p q r b m a d e P-(window : ℝ)) (P-(m : ℝ)-(unitLap : ℝ)) hc i
  have hid := packet_phase c g h j p q r b hp hq hr hh m a d e P i
  apply clear_of_window (wholeLap m a d e p q r (middleIndex b i)-wholeLap m a d e p q r 0+
    window+(i.val : ℤ)*unitLap+Fresh.UnitAPPacketThreeCharts.carry role i)
  all_goals push_cast at hid ⊢; nlinarith only [hid,hwin.1,hwin.2]

theorem opening_clear (c g h j : ℝ) (p q r : ℕ) (b : Fin 6)
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r) (hhost : MiddleHost p q r b)
    (hg : 0 < g) (hh : 0 < h) (hj : 0 < j) (m a d e rho unitLap window : ℤ)
    (u : Fin 7) (role : Fin 6) (L : Fin 8 → ℤ)
    (hc : PacketBands c g h j p q r b m a d e unitLap window role (opening c g h j p q r m a d e rho u))
    (hb : RemainingBands c g h j p q r b m a d e (opening c g h j p q r m a d e rho u) L u) :
    LonelyAt (disparitySet (speeds c g h j p q r) 0) (opening c g h j p q r m a d e rho u) := by
  have hpacket := packet_clear c g h j p q r b hp hq hr hhost m a d e unitLap window role _ hc
  intro x hx
  obtain ⟨i,hi,rfl⟩ := mem_disparitySet.mp hx
  rw [Fresh.Localisation.distInt_abs_mul]
  by_cases hiu : i=openingIndex u
  · subst i
    have ho := Fresh.FourBlockShortOpening.opening_identity c g h j p q r hq hr hg hh hj m a d e rho u
    dsimp [reading] at ho
    apply clear_of_window (lap m a d e p q r u+rho)
    · exact ho.ge
    · linarith only [ho]
  by_cases hin : b.val ≤ i.val ∧ i.val < b.val+3
  · let v : Fin 3 := ⟨i.val-b.val,by omega⟩
    have he : middleIndex b v=i := by apply Fin.ext; dsimp [middleIndex,v]; omega
    have hh' := hpacket v
    rwa [he] at hh'
  · exact clear_of_window _ (hb i hi hiu (by omega)).1 (hb i hi hiu (by omega)).2

theorem opening_move (c g h j : ℝ) (p q r : ℕ) (b : Fin 6)
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r) (hhost : MiddleHost p q r b)
    (hg : 0 < g) (hh : 0 < h) (hj : 0 < j) (m a d e rho unitLap window : ℤ)
    (u : Fin 7) (role : Fin 6) (L : Fin 8 → ℤ)
    (hc : PacketBands c g h j p q r b m a d e unitLap window role (opening c g h j p q r m a d e rho u))
    (hb : RemainingBands c g h j p q r b m a d e (opening c g h j p q r m a d e rho u) L u) (Q : ℝ)
    (hlo : (rho : ℝ)-1/8 < reading c g h j p q r u*Q-(lap m a d e p q r u : ℝ))
    (hhi : reading c g h j p q r u*Q-(lap m a d e p q r u : ℝ) < (rho : ℝ)+1/8) :
    IsMove (disparitySet (speeds c g h j p q r) 0) Q (opening c g h j p q r m a d e rho u) := by
  obtain ⟨hw,hop,ht⟩ := Fresh.FourBlockShortOpeningMoves.capture_opening
    c g h j p q r hq hr hg hh hj m a d e u rho Q hlo hhi
  have hmem : |reading c g h j p q r u| ∈ disparitySet (speeds c g h j p q r) 0 := by
    refine mem_disparitySet.mpr ⟨openingIndex u,?_,rfl⟩
    intro he
    have hv := congrArg Fin.val he
    dsimp [openingIndex] at hv
    omega
  exact Fresh.FourBlockPacketFrameMoves.move_at_supplied_opening
    (Fresh.FourBlockPacketFrameMoves.native_readings_positive c g h j p q r hq hr hg hh hj) hmem hw hop
    (opening_clear c g h j p q r b hp hq hr hhost hg hh hj m a d e rho unitLap window u role L hc hb)

#print axioms opening_move
#print axioms host_cases
#print axioms packet_steps
#print axioms packet_phase
#print axioms packet_clear
#print axioms opening_clear
end Fresh.FourBlockMiddlePacket
