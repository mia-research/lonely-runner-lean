import Fresh.FourBlockMiddlePacketJoins

/-! Two original singleton endpoints read one physical middle AP packet
in opposite orders. Separate original openings retain all integer labels. -/
namespace Fresh.FourBlockDoubleSingleton
set_option maxHeartbeats 2500000
open Fresh Fresh.Cascade Fresh.Localisation Fresh.FourBlockNeighbour

def endpoint (right : Bool) : Fin 8 := if right then 7 else 0

def openingIndex (right : Bool) (u : Fin 7) : Fin 8 :=
  if right then ⟨u.val,by omega⟩ else ⟨u.val+1,by omega⟩

def packetIndex (right : Bool) (b : Fin 6) (i : Fin 3) : Fin 8 :=
  if right then ⟨b.val+(2-i.val),by have := b.isLt; omega⟩
  else ⟨b.val+i.val,by have := b.isLt; have := i.isLt; omega⟩

def Host (q r : ℕ) (b : Fin 6) : Prop :=
  q+r=6 ∧ ((b.val=1 ∧ 3 ≤ q) ∨ (b.val=1+q ∧ 3 ≤ r))

theorem host_cases (q r : ℕ) (b : Fin 6) (hq : 1 ≤ q) (hr : 1 ≤ r) (hh : Host q r b) :
    (q=1 ∧ r=5 ∧ b.val=2) ∨ (q=2 ∧ r=4 ∧ b.val=3) ∨
    (q=3 ∧ r=3 ∧ b.val=1) ∨ (q=3 ∧ r=3 ∧ b.val=4) ∨
    (q=4 ∧ r=2 ∧ b.val=1) ∨ (q=5 ∧ r=1 ∧ b.val=1) := by
  rcases hh with ⟨hs,hleft|hright⟩ <;> omega

noncomputable def reading (c g h j : ℝ) (q r : ℕ) (right : Bool) (i : Fin 8) : ℝ :=
  if right then speeds c g h j 1 q r 7-speeds c g h j 1 q r i
  else speeds c g h j 1 q r i-speeds c g h j 1 q r 0

def lap (m a d e : ℤ) (q r : ℕ) (right : Bool) (i : Fin 8) : ℤ :=
  if right then wholeLap m a d e 1 q r 7-wholeLap m a d e 1 q r i
  else wholeLap m a d e 1 q r i-wholeLap m a d e 1 q r 0

theorem reading_abs (c g h j : ℝ) (q r : ℕ) (hq : 1 ≤ q) (hr : 1 ≤ r)
    (hg : 0 < g) (hh : 0 < h) (hj : 0 < j) (right : Bool) (i : Fin 8) :
    |speeds c g h j 1 q r i-speeds c g h j 1 q r (endpoint right)|=reading c g h j q r right i := by
  have hmono := Fresh.FourBlockEndpoints.speeds_monotone c g h j 1 q r hq hr hg hh hj
  cases right
  · exact abs_of_nonneg (sub_nonneg.mpr (hmono (Fin.zero_le i)))
  · exact (abs_of_nonpos (sub_nonpos.mpr (hmono (Fin.le_last i)))).trans (neg_sub _ _)

theorem opening_reading_pos (c g h j : ℝ) (q r : ℕ) (hq : 1 ≤ q) (hr : 1 ≤ r)
    (hg : 0 < g) (hh : 0 < h) (hj : 0 < j) (right : Bool) (u : Fin 7) :
    0 < reading c g h j q r right (openingIndex right u) := by
  have hstrict : StrictMono (speeds c g h j 1 q r) := by
    apply Fin.strictMono_iff_lt_succ.mpr
    intro idx
    have hd := Fresh.FourBlockEndpoints.adjacent_speed_gap c g h j 1 q r hq hr idx
    split_ifs at hd <;> linarith
  cases right
  · apply sub_pos.mpr
    apply hstrict
    change (0 : ℕ)<u.val+1
    omega
  · apply sub_pos.mpr
    apply hstrict
    change u.val<(7 : ℕ)
    exact u.isLt

theorem packet_steps (c g h j : ℝ) (q r : ℕ) (b : Fin 6)
    (hq : 1 ≤ q) (hr : 1 ≤ r) (hh : Host q r b)
    (m a d e : ℤ) (right : Bool) (i : Fin 3) :
    reading c g h j q r right (packetIndex right b i)-reading c g h j q r right (packetIndex right b 0)=(i : ℝ) ∧
    lap m a d e q r right (packetIndex right b i)-lap m a d e q r right (packetIndex right b 0)=(i.val : ℤ)*m := by
  rcases host_cases q r b hq hr hh with hs|hs|hs|hs|hs|hs
  all_goals obtain ⟨rfl,rfl,hb⟩ := hs
  all_goals fin_cases b <;> norm_num at hb
  all_goals cases right <;> fin_cases i <;> norm_num [packetIndex,reading,lap,speeds,wholeLap] <;> (try constructor) <;> ring

noncomputable def phase (c g h j : ℝ) (q r : ℕ) (right : Bool) (m a d e : ℤ) (i : Fin 8) (P : ℝ) : ℝ :=
  reading c g h j q r right i*P-(lap m a d e q r right i : ℝ)

noncomputable def opening (c g h j : ℝ) (q r : ℕ) (right : Bool) (m a d e rho : ℤ) (u : Fin 7) : ℝ :=
  ((lap m a d e q r right (openingIndex right u)+rho : ℤ)+1/8)/reading c g h j q r right (openingIndex right u)

noncomputable def PacketBands (c g h j : ℝ) (q r : ℕ) (b : Fin 6) (right : Bool)
    (m a d e unitLap window : ℤ) (role : Fin 6) (P : ℝ) : Prop :=
  Fresh.UnitAPPacketThreeCharts.Chart role (phase c g h j q r right m a d e (packetIndex right b 0) P-(window : ℝ))
    (P-(m : ℝ)-(unitLap : ℝ))

noncomputable def RemainingBands (c g h j : ℝ) (q r : ℕ) (b : Fin 6) (right : Bool)
    (m a d e : ℤ) (P : ℝ) (L : Fin 8 → ℤ) (u : Fin 7) : Prop :=
  ∀ i : Fin 8, i≠endpoint right → i≠openingIndex right u → (i.val < b.val ∨ b.val+3 ≤ i.val) →
    (L i : ℝ)+1/8 ≤ phase c g h j q r right m a d e i P ∧
    phase c g h j q r right m a d e i P ≤ (L i : ℝ)+7/8

theorem packet_phase (c g h j : ℝ) (q r : ℕ) (b : Fin 6) (hq : 1 ≤ q) (hr : 1 ≤ r) (hh : Host q r b)
    (m a d e : ℤ) (right : Bool) (P : ℝ) (i : Fin 3) :
    phase c g h j q r right m a d e (packetIndex right b i) P =
      phase c g h j q r right m a d e (packetIndex right b 0) P+(i : ℝ)*(P-(m : ℝ)) := by
  obtain ⟨hs,hn⟩ := packet_steps c g h j q r b hq hr hh m a d e right i
  have hscaled := congrArg (fun x : ℝ => x*P) hs
  have hlap := congrArg (fun x : ℤ => (x : ℝ)) hn
  push_cast at hlap
  dsimp [phase]
  nlinarith only [hscaled,hlap]

theorem endpoint_clear (c g h j : ℝ) (q r : ℕ) (b : Fin 6) (hq : 1 ≤ q) (hr : 1 ≤ r) (hhost : Host q r b)
    (hg : 0 < g) (hh : 0 < h) (hj : 0 < j) (right : Bool) (m a d e rho unitLap window : ℤ)
    (u : Fin 7) (role : Fin 6) (L : Fin 8 → ℤ)
    (hc : PacketBands c g h j q r b right m a d e unitLap window role (opening c g h j q r right m a d e rho u))
    (hb : RemainingBands c g h j q r b right m a d e (opening c g h j q r right m a d e rho u) L u) :
    IsolatedAt (speeds c g h j 1 q r) (endpoint right) (opening c g h j q r right m a d e rho u) := by
  let P := opening c g h j q r right m a d e rho u
  have hp := opening_reading_pos c g h j q r hq hr hg hh hj right u
  have ho : reading c g h j q r right (openingIndex right u)*P=
      ((lap m a d e q r right (openingIndex right u)+rho : ℤ) : ℝ)+1/8 := by
    dsimp [P,opening]
    field_simp
  intro i hi
  rw [←Fresh.Localisation.distInt_abs_mul,reading_abs c g h j q r hq hr hg hh hj]
  by_cases hiu : i=openingIndex right u
  · subst i
    apply clear_of_window (lap m a d e q r right (openingIndex right u)+rho)
    · exact ho.ge
    · linarith only [ho]
  by_cases hin : b.val ≤ i.val ∧ i.val < b.val+3
  · let v : Fin 3 := ⟨if right then b.val+2-i.val else i.val-b.val,by cases right <;> simp <;> omega⟩
    have he : packetIndex right b v=i := by
      apply Fin.ext
      cases right <;> dsimp [packetIndex,v] <;> omega
    have hw := Fresh.UnitAPPacketThreeCharts.chart_windows role
      (phase c g h j q r right m a d e (packetIndex right b 0) P-(window : ℝ)) (P-(m : ℝ)-(unitLap : ℝ)) hc v
    have hid := packet_phase c g h j q r b hq hr hhost m a d e right P v
    rw [he] at hid
    apply clear_of_window (lap m a d e q r right i+window+(v.val : ℤ)*unitLap+Fresh.UnitAPPacketThreeCharts.carry role v)
    all_goals dsimp [phase] at hid hw; push_cast; nlinarith only [hid,hw.1,hw.2]
  · have hw := hb i hi hiu (by omega)
    apply clear_of_window (lap m a d e q r right i+L i)
    all_goals dsimp [phase] at hw; push_cast; linarith only [hw.1,hw.2]

theorem opening_move (c g h j : ℝ) (q r : ℕ) (b : Fin 6) (hq : 1 ≤ q) (hr : 1 ≤ r) (hhost : Host q r b)
    (hg : 0 < g) (hh : 0 < h) (hj : 0 < j) (right : Bool) (m a d e rho unitLap window : ℤ)
    (u : Fin 7) (role : Fin 6) (L : Fin 8 → ℤ)
    (hc : PacketBands c g h j q r b right m a d e unitLap window role (opening c g h j q r right m a d e rho u))
    (hb : RemainingBands c g h j q r b right m a d e (opening c g h j q r right m a d e rho u) L u) (Q : ℝ)
    (hlo : (rho : ℝ)-1/8 < phase c g h j q r right m a d e (openingIndex right u) Q)
    (hhi : phase c g h j q r right m a d e (openingIndex right u) Q < (rho : ℝ)+1/8) :
    IsMove (disparitySet (speeds c g h j 1 q r) (endpoint right)) Q (opening c g h j q r right m a d e rho u) := by
  have hnear : |reading c g h j q r right (openingIndex right u)*Q-
      ((lap m a d e q r right (openingIndex right u)+rho : ℤ) : ℝ)| < 1/8 := by
    rw [abs_lt]
    dsimp [phase] at hlo hhi
    push_cast
    constructor <;> linarith
  have hw : InWay (reading c g h j q r right (openingIndex right u)) Q :=
    lt_of_le_of_lt (Fresh.Cascade.distInt_le _ (lap m a d e q r right (openingIndex right u)+rho)) hnear
  have hop : nextOpening (reading c g h j q r right (openingIndex right u)) Q=
      opening c g h j q r right m a d e rho u := by
    rw [nextOpening_eq hnear]
    rfl
  have hmem : reading c g h j q r right (openingIndex right u) ∈
      disparitySet (speeds c g h j 1 q r) (endpoint right) := by
    rw [←reading_abs c g h j q r hq hr hg hh hj]
    apply mem_disparitySet.mpr
    refine ⟨openingIndex right u,?_,rfl⟩
    intro he
    have hv := congrArg Fin.val he
    cases right <;> dsimp [openingIndex,endpoint] at hv <;> have := u.isLt <;> omega
  have hstrict : StrictMono (speeds c g h j 1 q r) := by
    apply Fin.strictMono_iff_lt_succ.mpr
    intro idx
    have hd := Fresh.FourBlockEndpoints.adjacent_speed_gap c g h j 1 q r hq hr idx
    split_ifs at hd <;> linarith
  have hpos : ∀ d ∈ disparitySet (speeds c g h j 1 q r) (endpoint right), 0 < d := by
    intro d hd
    obtain ⟨i,hi,rfl⟩ := mem_disparitySet.mp hd
    exact abs_pos.mpr (sub_ne_zero.mpr (fun he => hi (hstrict.injective he)))
  exact Fresh.FourBlockPacketFrameMoves.move_at_supplied_opening hpos hmem hw hop
    ((Fresh.Localisation.isolatedAt_iff _ _ _).1
      (endpoint_clear c g h j q r b hq hr hhost hg hh hj right m a d e rho unitLap window u role L hc hb))

#print axioms opening_move
#print axioms host_cases
#print axioms reading_abs
#print axioms opening_reading_pos
#print axioms packet_steps
#print axioms packet_phase
#print axioms endpoint_clear
end Fresh.FourBlockDoubleSingleton
