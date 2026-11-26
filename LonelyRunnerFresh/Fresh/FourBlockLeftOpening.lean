import Fresh.FourBlockOuterPacketRetention

/-! Native openings of the three original left readings. The captured
reading supplies its own boundary; only the other two left cuts are inputs. -/
namespace Fresh.FourBlockLeftOpening
open Fresh Fresh.Cascade Fresh.Localisation Fresh.FourBlockNeighbour
  Fresh.FourBlockEndpointCapture Fresh.FourBlockOuterLapPhase
  Fresh.FourBlockOuterTailClear Fresh.FourBlockOuterPacketRetention

noncomputable def leftReading (c g h j : ℝ) (p q r : ℕ) (u : Fin 3) : ℝ :=
  speeds c g h j p q r (prefixIndex u)-speeds c g h j p q r 0

def leftLap (m a b e : ℤ) (p q r : ℕ) (u : Fin 3) : ℤ :=
  wholeLap m a b e p q r (prefixIndex u)-wholeLap m a b e p q r 0

noncomputable def leftOpening (c g h j : ℝ) (p q r : ℕ) (m a b e : ℤ)
    (u : Fin 3) (z : ℤ) : ℝ :=
  (((leftLap m a b e p q r u+z : ℤ) : ℝ)+1/8)/leftReading c g h j p q r u

def LeftBandsAt (c g h j : ℝ) (p q r : ℕ) (m a b e : ℤ) (P : ℝ) (L : Fin 3 → ℤ) : Prop :=
  ∀ u : Fin 3, ((leftLap m a b e p q r u+L u : ℤ) : ℝ)+1/8 ≤ leftReading c g h j p q r u*P ∧
    leftReading c g h j p q r u*P ≤ ((leftLap m a b e p q r u+L u : ℤ) : ℝ)+7/8

def OtherLeftBandsAt (c g h j : ℝ) (p q r : ℕ) (m a b e : ℤ)
    (P : ℝ) (L : Fin 3 → ℤ) (k : Fin 3) : Prop :=
  ∀ u : Fin 3, u≠k → ((leftLap m a b e p q r u+L u : ℤ) : ℝ)+1/8 ≤ leftReading c g h j p q r u*P ∧
    leftReading c g h j p q r u*P ≤ ((leftLap m a b e p q r u+L u : ℤ) : ℝ)+7/8

theorem reading_pos (c g h j : ℝ) (p q r : ℕ) (hq : 1 ≤ q) (hr : 1 ≤ r)
    (hg : 0 < g) (hh : 0 < h) (hj : 0 < j) (u : Fin 3) : 0 < leftReading c g h j p q r u := by
  have hstrict : StrictMono (speeds c g h j p q r) := by
    apply Fin.strictMono_iff_lt_succ.mpr
    intro idx
    have hd := FourBlockEndpoints.adjacent_speed_gap c g h j p q r hq hr idx
    split_ifs at hd <;> linarith
  exact sub_pos.mpr (hstrict (show (0 : Fin 8)<prefixIndex u by change 0<u.val+1; omega))

theorem opening_identity (c g h j : ℝ) (p q r : ℕ) (hq : 1 ≤ q) (hr : 1 ≤ r)
    (hg : 0 < g) (hh : 0 < h) (hj : 0 < j) (m a b e : ℤ) (u : Fin 3) (z : ℤ) :
    leftReading c g h j p q r u*leftOpening c g h j p q r m a b e u z=
      ((leftLap m a b e p q r u+z : ℤ) : ℝ)+1/8 := by
  have hp := reading_pos c g h j p q r hq hr hg hh hj u
  dsimp [leftOpening]
  field_simp [ne_of_gt hp]

theorem capture_opening (c g h j : ℝ) (p q r : ℕ) (hq : 1 ≤ q) (hr : 1 ≤ r)
    (hg : 0 < g) (hh : 0 < h) (hj : 0 < j) (m a b e : ℤ) (u : Fin 3) (z : ℤ) (Q : ℝ)
    (hlo : (z : ℝ)-1/8 < leftReading c g h j p q r u*Q-(leftLap m a b e p q r u : ℝ))
    (hhi : leftReading c g h j p q r u*Q-(leftLap m a b e p q r u : ℝ) < (z : ℝ)+1/8) :
    InWay |leftReading c g h j p q r u| Q ∧
    nextOpening |leftReading c g h j p q r u| Q=leftOpening c g h j p q r m a b e u z ∧
    Q < leftOpening c g h j p q r m a b e u z := by
  have hp := reading_pos c g h j p q r hq hr hg hh hj u
  have hnear : |leftReading c g h j p q r u*Q-((leftLap m a b e p q r u+z : ℤ) : ℝ)| < 1/8 := by
    rw [abs_lt]
    push_cast
    constructor <;> linarith
  have hw : InWay |leftReading c g h j p q r u| Q := by
    rw [abs_of_pos hp]
    exact lt_of_le_of_lt (Fresh.Cascade.distInt_le _ (leftLap m a b e p q r u+z)) hnear
  have hop : nextOpening |leftReading c g h j p q r u| Q=leftOpening c g h j p q r m a b e u z := by
    rw [abs_of_pos hp,nextOpening_eq hnear]
    rfl
  refine ⟨hw,hop,?_⟩
  rw [←hop]
  exact lt_nextOpening (abs_pos.mpr (ne_of_gt hp)) hw

theorem bands_at_opening (c g h j : ℝ) (p q r : ℕ) (hq : 1 ≤ q) (hr : 1 ≤ r)
    (hg : 0 < g) (hh : 0 < h) (hj : 0 < j) (m a b e : ℤ) (k : Fin 3) (L : Fin 3 → ℤ)
    (hother : OtherLeftBandsAt c g h j p q r m a b e (leftOpening c g h j p q r m a b e k (L k)) L k) :
    LeftBandsAt c g h j p q r m a b e (leftOpening c g h j p q r m a b e k (L k)) L := by
  intro u
  by_cases huk : u=k
  · subst u
    have hid := opening_identity c g h j p q r hq hr hg hh hj m a b e k (L k)
    exact ⟨by linarith,by linarith⟩
  · exact hother u huk

theorem displaced_clear (c g h j : ℝ) (p q r : ℕ)
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r) (hs : p+q+r ≤ 4)
    (hg : 0 < g) (hh : 0 < h) (hj : 0 < j) (m a b e rho : ℤ) (P : ℝ) (L : Fin 3 → ℤ)
    (hlo : 11*(g+h+j)+16*remainder g h j m a b e ≤ 16*(rho : ℝ)-42)
    (hhi : 8*(rho : ℝ)-27 ≤ 7*(g+h+j)+8*remainder g h j m a b e)
    (hQP : outerLapOpening g h j m a b e rho ≤ P)
    (houter : (4+g+h+j)*(P-outerLapOpening g h j m a b e rho) ≤ 3/4)
    (hinner : (4+g+h+j)*(P-outerLapOpening g h j m a b e rho)+3*(1-(P-(m : ℝ))) ≤ 3/4)
    (hleft : LeftBandsAt c g h j p q r m a b e P L) :
    LonelyAt (disparitySet (speeds c g h j p q r) 0) P := by
  have hprefix (u : Fin 3) : (1/8 : ℝ) ≤ distInt (leftReading c g h j p q r u*P) :=
    clear_of_window _ (hleft u).1 (hleft u).2
  intro d hd
  obtain ⟨i,hi0,rfl⟩ := mem_disparitySet.mp hd
  rw [Fresh.Localisation.distInt_abs_mul]
  by_cases hi1 : i=1
  · subst i; simpa only [leftReading,prefixIndex] using hprefix 0
  by_cases hi2 : i=2
  · subst i; simpa only [leftReading,prefixIndex] using hprefix 1
  by_cases hi3 : i=3
  · subst i; simpa only [leftReading,prefixIndex] using hprefix 2
  have hiv := i.isLt
  have hn0 := Fin.val_ne_of_ne hi0
  have hn1 := Fin.val_ne_of_ne hi1
  have hn2 := Fin.val_ne_of_ne hi2
  have hn3 := Fin.val_ne_of_ne hi3
  exact packet_retained c g h j p q r hp hq hr hs hg hh hj m a b e rho P hlo hhi hQP houter hinner i (by omega)

theorem upper_capture_join (c g h j : ℝ) (p q r : ℕ) (hq : 1 ≤ q) (hr : 1 ≤ r)
    (hg : 0 < g) (hh : 0 < h) (hj : 0 < j) (m a b e : ℤ) (u : Fin 3) (z : ℤ) (Q : ℝ)
    (hface : leftReading c g h j p q r u*Q-(leftLap m a b e p q r u : ℝ)=(z : ℝ)+1/8) :
    leftOpening c g h j p q r m a b e u z=Q := by
  have hid := opening_identity c g h j p q r hq hr hg hh hj m a b e u z
  have hp := reading_pos c g h j p q r hq hr hg hh hj u
  push_cast at hid
  nlinarith only [hid,hface,hp]

theorem upper_join_clear (c g h j : ℝ) (p q r : ℕ)
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r) (hs : p+q+r ≤ 4)
    (hg : 0 < g) (hh : 0 < h) (hj : 0 < j) (m a b e rho : ℤ) (u : Fin 3) (L : Fin 3 → ℤ)
    (hlo : 11*(g+h+j)+16*remainder g h j m a b e ≤ 16*(rho : ℝ)-42)
    (hhi : 8*(rho : ℝ)-27 ≤ 7*(g+h+j)+8*remainder g h j m a b e)
    (hface : leftReading c g h j p q r u*outerLapOpening g h j m a b e rho-
      (leftLap m a b e p q r u : ℝ)=(L u : ℝ)+1/8)
    (hother : OtherLeftBandsAt c g h j p q r m a b e (leftOpening c g h j p q r m a b e u (L u)) L u) :
    LonelyAt (disparitySet (speeds c g h j p q r) 0) (outerLapOpening g h j m a b e rho) := by
  have hjoin := upper_capture_join c g h j p q r hq hr hg hh hj m a b e u (L u)
    (outerLapOpening g h j m a b e rho) hface
  have hb := bands_at_opening c g h j p q r hq hr hg hh hj m a b e u L hother
  rw [hjoin] at hb
  have hleft : LeftBands c g h j p q r m a b e rho L := by
    simpa only [LeftBandsAt,LeftBands,leftReading,leftLap] using hb
  exact Fresh.FourBlockOuterTailClear.outer_clear c g h j p q r hp hq hr hs hg hh hj m a b e rho L hlo hhi hleft

#print axioms upper_capture_join
#print axioms upper_join_clear
#print axioms reading_pos
#print axioms opening_identity
#print axioms capture_opening
#print axioms bands_at_opening
#print axioms displaced_clear
end Fresh.FourBlockLeftOpening
