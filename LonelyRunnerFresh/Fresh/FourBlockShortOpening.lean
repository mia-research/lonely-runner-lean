import Fresh.FourBlockShortTailArrangement

/-! A common original opening for the short AP packet: any of the seven
other moving runners may set it. Its own cut boundary is derived exactly. -/
namespace Fresh.FourBlockShortOpening
open Fresh Fresh.Cascade Fresh.Localisation Fresh.FourBlockNeighbour Fresh.FourBlockShortTail

def openingIndex (u : Fin 7) : Fin 8 := ⟨u.val+1,by omega⟩
noncomputable def reading (c g h j : ℝ) (p q r : ℕ) (u : Fin 7) : ℝ :=
  speeds c g h j p q r (openingIndex u)-speeds c g h j p q r 0
def lap (m a b e : ℤ) (p q r : ℕ) (u : Fin 7) : ℤ :=
  wholeLap m a b e p q r (openingIndex u)-wholeLap m a b e p q r 0
noncomputable def opening (c g h j : ℝ) (p q r : ℕ) (m a b e rho : ℤ) (u : Fin 7) : ℝ :=
  (((lap m a b e p q r u+rho : ℤ) : ℝ)+1/8)/reading c g h j p q r u

def RemainingCutBands (c g h j : ℝ) (p q r : ℕ) (m a b e : ℤ)
    (P : ℝ) (L : Fin 4 → ℤ) (u : Fin 7) : Prop :=
  ∀ v : Fin 4, cutIndex v≠openingIndex u →
    ((cutLap m a b e p q r v+L v : ℤ) : ℝ)+1/8 ≤ cutReading c g h j p q r v*P ∧
    cutReading c g h j p q r v*P ≤ ((cutLap m a b e p q r v+L v : ℤ) : ℝ)+7/8

theorem reading_pos (c g h j : ℝ) (p q r : ℕ) (hq : 1 ≤ q) (hr : 1 ≤ r)
    (hg : 0 < g) (hh : 0 < h) (hj : 0 < j) (u : Fin 7) : 0 < reading c g h j p q r u := by
  have hstrict : StrictMono (speeds c g h j p q r) := by
    apply Fin.strictMono_iff_lt_succ.mpr
    intro idx
    have hd := Fresh.FourBlockEndpoints.adjacent_speed_gap c g h j p q r hq hr idx
    split_ifs at hd <;> linarith
  exact sub_pos.mpr (hstrict (show (0 : Fin 8)<openingIndex u by change 0<u.val+1; omega))

theorem opening_identity (c g h j : ℝ) (p q r : ℕ) (hq : 1 ≤ q) (hr : 1 ≤ r)
    (hg : 0 < g) (hh : 0 < h) (hj : 0 < j) (m a b e rho : ℤ) (u : Fin 7) :
    reading c g h j p q r u*opening c g h j p q r m a b e rho u=
      ((lap m a b e p q r u+rho : ℤ) : ℝ)+1/8 := by
  have hp := reading_pos c g h j p q r hq hr hg hh hj u
  dsimp [opening]
  field_simp [ne_of_gt hp]

theorem all_cut_clear (c g h j : ℝ) (p q r : ℕ) (hq : 1 ≤ q) (hr : 1 ≤ r)
    (hg : 0 < g) (hh : 0 < h) (hj : 0 < j) (m a b e rho : ℤ) (u : Fin 7) (L : Fin 4 → ℤ)
    (hb : RemainingCutBands c g h j p q r m a b e (opening c g h j p q r m a b e rho u) L u) :
    ∀ v : Fin 4, (1/8 : ℝ) ≤ distInt (cutReading c g h j p q r v*opening c g h j p q r m a b e rho u) := by
  intro v
  by_cases hv : cutIndex v=openingIndex u
  · have ho := opening_identity c g h j p q r hq hr hg hh hj m a b e rho u
    have hd : cutReading c g h j p q r v=reading c g h j p q r u := by dsimp [cutReading,reading]; rw [hv]
    rw [hd]
    apply clear_of_window (lap m a b e p q r u+rho)
    · linarith only [ho]
    · linarith only [ho]
  · exact clear_of_window _ (hb v hv).1 (hb v hv).2

theorem opening_clear (c g h j : ℝ) (p q r : ℕ)
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r) (hs : p+q+r ≤ 5)
    (hg : 0 < g) (hh : 0 < h) (hj : 0 < j) (m a b e rho unitLap window : ℤ)
    (u : Fin 7) (role : Fin 6) (L : Fin 4 → ℤ)
    (hc : PacketBands c g h j p q r m a b e unitLap window role (opening c g h j p q r m a b e rho u))
    (hb : RemainingCutBands c g h j p q r m a b e (opening c g h j p q r m a b e rho u) L u) :
    LonelyAt (disparitySet (speeds c g h j p q r) 0) (opening c g h j p q r m a b e rho u) := by
  have hcuts := all_cut_clear c g h j p q r hq hr hg hh hj m a b e rho u L hb
  have htail := packet_clear c g h j p q r hp hq hr hs m a b e unitLap window role
    (opening c g h j p q r m a b e rho u) hc
  intro d hd
  obtain ⟨i,hi,rfl⟩ := mem_disparitySet.mp hd
  rw [Fresh.Localisation.distInt_abs_mul]
  fin_cases i
  · exact (hi rfl).elim
  · exact hcuts 0
  · exact hcuts 1
  · exact hcuts 2
  · exact hcuts 3
  · exact htail 0
  · exact htail 1
  · exact htail 2

#print axioms reading_pos
#print axioms opening_identity
#print axioms all_cut_clear
#print axioms opening_clear
end Fresh.FourBlockShortOpening
