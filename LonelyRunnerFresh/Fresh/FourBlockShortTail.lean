import Fresh.UnitAPPacketThreeCharts
import Fresh.NativeBoundaryJoins

/-! Four native physical blocks whose final AP packet has at least three
readings. The six quartet-free packet charts retain original phase laps. -/
namespace Fresh.FourBlockShortTail
open Fresh Fresh.Cascade Fresh.Localisation Fresh.FourBlockNeighbour

def tailIndex (i : Fin 3) : Fin 8 := ⟨i.val+5,by omega⟩
def cutIndex (i : Fin 4) : Fin 8 := ⟨i.val+1,by omega⟩
noncomputable def cutReading (c g h j : ℝ) (p q r : ℕ) (i : Fin 4) : ℝ :=
  speeds c g h j p q r (cutIndex i)-speeds c g h j p q r 0
def cutLap (m a b e : ℤ) (p q r : ℕ) (i : Fin 4) : ℤ :=
  wholeLap m a b e p q r (cutIndex i)-wholeLap m a b e p q r 0
noncomputable def cutOpening (c g h j : ℝ) (p q r : ℕ) (m a b e : ℤ) (i : Fin 4) (z : ℤ) : ℝ :=
  (((cutLap m a b e p q r i+z : ℤ) : ℝ)+1/8)/cutReading c g h j p q r i
noncomputable def firstPhase (c g h j : ℝ) (p q r : ℕ) (m a b e : ℤ) (P : ℝ) : ℝ :=
  (speeds c g h j p q r 5-speeds c g h j p q r 0)*P-
    ((wholeLap m a b e p q r 5-wholeLap m a b e p q r 0 : ℤ) : ℝ)
noncomputable def PacketBands (c g h j : ℝ) (p q r : ℕ) (m a b e unitLap window : ℤ) (role : Fin 6) (P : ℝ) : Prop :=
  Fresh.UnitAPPacketThreeCharts.Chart role (firstPhase c g h j p q r m a b e P-(window : ℝ)) (P-(m : ℝ)-(unitLap : ℝ))
def OtherCutBands (c g h j : ℝ) (p q r : ℕ) (m a b e : ℤ) (P : ℝ) (L : Fin 4 → ℤ) (u : Fin 4) : Prop :=
  ∀ v : Fin 4, v≠u → ((cutLap m a b e p q r v+L v : ℤ) : ℝ)+1/8 ≤ cutReading c g h j p q r v*P ∧
    cutReading c g h j p q r v*P ≤ ((cutLap m a b e p q r v+L v : ℤ) : ℝ)+7/8

theorem tail_reading (c g h j : ℝ) (p q r : ℕ)
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r) (hs : p+q+r ≤ 5)
    (i : Fin 8) (hi : 5 ≤ (i : ℕ)) :
    speeds c g h j p q r i-speeds c g h j p q r 0=(i : ℝ)-3+g+h+j := by
  have hpi : p ≤ (i : ℕ) := by omega
  have hpqi : p+q ≤ (i : ℕ) := by omega
  have hpqri : p+q+r ≤ (i : ℕ) := by omega
  have h0p : ¬p ≤ 0 := by omega
  have h0q : ¬p+q ≤ 0 := by omega
  have h0r : ¬p+q+r ≤ 0 := by omega
  norm_num [speeds,hpi,hpqi,hpqri,h0p,h0q,h0r]
  ring

theorem tail_lap (p q r : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r)
    (hs : p+q+r ≤ 5) (m a b e : ℤ) (i : Fin 8) (hi : 5 ≤ (i : ℕ)) :
    wholeLap m a b e p q r i-wholeLap m a b e p q r 0=
      ((((i : ℕ) : ℤ)-3)*m+a+b+e) := by
  have hpi : p ≤ (i : ℕ) := by omega
  have hpqi : p+q ≤ (i : ℕ) := by omega
  have hpqri : p+q+r ≤ (i : ℕ) := by omega
  have h0p : ¬p ≤ 0 := by omega
  have h0q : ¬p+q ≤ 0 := by omega
  have h0r : ¬p+q+r ≤ 0 := by omega
  norm_num [wholeLap,hpi,hpqi,hpqri,h0p,h0q,h0r]
  ring

theorem reading_pos (c g h j : ℝ) (p q r : ℕ) (hq : 1 ≤ q) (hr : 1 ≤ r)
    (hg : 0 < g) (hh : 0 < h) (hj : 0 < j) (u : Fin 4) : 0 < cutReading c g h j p q r u := by
  have hstrict : StrictMono (speeds c g h j p q r) := by
    apply Fin.strictMono_iff_lt_succ.mpr
    intro idx
    have hd := Fresh.FourBlockEndpoints.adjacent_speed_gap c g h j p q r hq hr idx
    split_ifs at hd <;> linarith
  exact sub_pos.mpr (hstrict (show (0 : Fin 8)<cutIndex u by change 0<u.val+1; omega))

theorem opening_identity (c g h j : ℝ) (p q r : ℕ) (hq : 1 ≤ q) (hr : 1 ≤ r)
    (hg : 0 < g) (hh : 0 < h) (hj : 0 < j) (m a b e : ℤ) (u : Fin 4) (z : ℤ) :
    cutReading c g h j p q r u*cutOpening c g h j p q r m a b e u z=
      ((cutLap m a b e p q r u+z : ℤ) : ℝ)+1/8 := by
  have hp := reading_pos c g h j p q r hq hr hg hh hj u
  dsimp [cutOpening]
  field_simp [ne_of_gt hp]

theorem capture_opening (c g h j : ℝ) (p q r : ℕ) (hq : 1 ≤ q) (hr : 1 ≤ r)
    (hg : 0 < g) (hh : 0 < h) (hj : 0 < j) (m a b e : ℤ) (u : Fin 4) (z : ℤ) (Q : ℝ)
    (hlo : (z : ℝ)-1/8 < cutReading c g h j p q r u*Q-(cutLap m a b e p q r u : ℝ))
    (hhi : cutReading c g h j p q r u*Q-(cutLap m a b e p q r u : ℝ) < (z : ℝ)+1/8) :
    InWay |cutReading c g h j p q r u| Q ∧
    nextOpening |cutReading c g h j p q r u| Q=cutOpening c g h j p q r m a b e u z ∧
    Q < cutOpening c g h j p q r m a b e u z := by
  have hp := reading_pos c g h j p q r hq hr hg hh hj u
  have hnear : |cutReading c g h j p q r u*Q-((cutLap m a b e p q r u+z : ℤ) : ℝ)| < 1/8 := by
    rw [abs_lt]
    push_cast
    constructor <;> linarith
  have hw : InWay |cutReading c g h j p q r u| Q := by
    rw [abs_of_pos hp]
    exact lt_of_le_of_lt (Fresh.Cascade.distInt_le _ (cutLap m a b e p q r u+z)) hnear
  have hop : nextOpening |cutReading c g h j p q r u| Q=cutOpening c g h j p q r m a b e u z := by
    rw [abs_of_pos hp,nextOpening_eq hnear]
    rfl
  refine ⟨hw,hop,?_⟩
  rw [←hop]
  exact lt_nextOpening (abs_pos.mpr (ne_of_gt hp)) hw

theorem packet_phase (c g h j : ℝ) (p q r : ℕ)
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r) (hs : p+q+r ≤ 5)
    (m a b e : ℤ) (P : ℝ) (i : Fin 3) :
    (speeds c g h j p q r (tailIndex i)-speeds c g h j p q r 0)*P-
      ((wholeLap m a b e p q r (tailIndex i)-wholeLap m a b e p q r 0 : ℤ) : ℝ)=
      firstPhase c g h j p q r m a b e P+(i : ℝ)*(P-(m : ℝ)) := by
  dsimp [firstPhase]
  rw [tail_reading c g h j p q r hp hq hr hs _ (by dsimp [tailIndex]; omega),
    tail_reading c g h j p q r hp hq hr hs 5 (by norm_num),
    tail_lap p q r hp hq hr hs m a b e _ (by dsimp [tailIndex]; omega),
    tail_lap p q r hp hq hr hs m a b e 5 (by norm_num)]
  dsimp [tailIndex]
  push_cast
  norm_num
  ring

theorem packet_clear (c g h j : ℝ) (p q r : ℕ)
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r) (hs : p+q+r ≤ 5)
    (m a b e unitLap window : ℤ) (role : Fin 6) (P : ℝ)
    (hc : PacketBands c g h j p q r m a b e unitLap window role P) (i : Fin 3) :
    (1/8 : ℝ) ≤ distInt ((speeds c g h j p q r (tailIndex i)-speeds c g h j p q r 0)*P) := by
  have hwin := Fresh.UnitAPPacketThreeCharts.chart_windows role
    (firstPhase c g h j p q r m a b e P-(window : ℝ)) (P-(m : ℝ)-(unitLap : ℝ)) hc i
  have hid := packet_phase c g h j p q r hp hq hr hs m a b e P i
  apply clear_of_window (wholeLap m a b e p q r (tailIndex i)-wholeLap m a b e p q r 0+
    window+(i.val : ℤ)*unitLap+Fresh.UnitAPPacketThreeCharts.carry role i)
  all_goals push_cast at hid ⊢; nlinarith only [hid,hwin.1,hwin.2]

theorem cut_clear (c g h j : ℝ) (p q r : ℕ)
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r) (hs : p+q+r ≤ 5)
    (hg : 0 < g) (hh : 0 < h) (hj : 0 < j) (m a b e unitLap window : ℤ)
    (role : Fin 6) (u : Fin 4) (L : Fin 4 → ℤ)
    (hc : PacketBands c g h j p q r m a b e unitLap window role (cutOpening c g h j p q r m a b e u (L u)))
    (hcuts : OtherCutBands c g h j p q r m a b e (cutOpening c g h j p q r m a b e u (L u)) L u) :
    LonelyAt (disparitySet (speeds c g h j p q r) 0) (cutOpening c g h j p q r m a b e u (L u)) := by
  have hb (v : Fin 4) : (1/8 : ℝ) ≤ distInt (cutReading c g h j p q r v*cutOpening c g h j p q r m a b e u (L u)) := by
    by_cases hv : v=u
    · subst v
      have ho := opening_identity c g h j p q r hq hr hg hh hj m a b e u (L u)
      apply clear_of_window (cutLap m a b e p q r u+L u)
      · linarith only [ho]
      · linarith only [ho]
    · exact clear_of_window _ (hcuts v hv).1 (hcuts v hv).2
  have ht := packet_clear c g h j p q r hp hq hr hs m a b e unitLap window role
    (cutOpening c g h j p q r m a b e u (L u)) hc
  intro d hd
  obtain ⟨i,hi,rfl⟩ := mem_disparitySet.mp hd
  rw [Fresh.Localisation.distInt_abs_mul]
  fin_cases i
  · exact (hi rfl).elim
  · exact hb 0
  · exact hb 1
  · exact hb 2
  · exact hb 3
  · exact ht 0
  · exact ht 1
  · exact ht 2

theorem cut_move (c g h j : ℝ) (p q r : ℕ)
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r) (hs : p+q+r ≤ 5)
    (hg : 0 < g) (hh : 0 < h) (hj : 0 < j) (m a b e unitLap window : ℤ)
    (role : Fin 6) (u : Fin 4) (L : Fin 4 → ℤ)
    (hc : PacketBands c g h j p q r m a b e unitLap window role (cutOpening c g h j p q r m a b e u (L u)))
    (hcuts : OtherCutBands c g h j p q r m a b e (cutOpening c g h j p q r m a b e u (L u)) L u) (Q : ℝ)
    (hlo : (L u : ℝ)-1/8 < cutReading c g h j p q r u*Q-(cutLap m a b e p q r u : ℝ))
    (hhi : cutReading c g h j p q r u*Q-(cutLap m a b e p q r u : ℝ) < (L u : ℝ)+1/8) :
    IsMove (disparitySet (speeds c g h j p q r) 0) Q (cutOpening c g h j p q r m a b e u (L u)) := by
  obtain ⟨hw,hop,ht⟩ := capture_opening c g h j p q r hq hr hg hh hj m a b e u (L u) Q hlo hhi
  have hmem : |cutReading c g h j p q r u| ∈ disparitySet (speeds c g h j p q r) 0 := by
    refine mem_disparitySet.mpr ⟨cutIndex u,?_,rfl⟩
    intro he
    have hh := congrArg Fin.val he
    dsimp [cutIndex] at hh
    omega
  exact Fresh.FourBlockPacketFrameMoves.move_at_supplied_opening
    (Fresh.FourBlockPacketFrameMoves.native_readings_positive c g h j p q r hq hr hg hh hj) hmem hw hop
    (cut_clear c g h j p q r hp hq hr hs hg hh hj m a b e unitLap window role u L hc hcuts)

#print axioms capture_opening
#print axioms cut_move
#print axioms tail_reading
#print axioms tail_lap
#print axioms reading_pos
#print axioms opening_identity
#print axioms packet_phase
#print axioms packet_clear
#print axioms cut_clear
end Fresh.FourBlockShortTail
