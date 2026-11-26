import Fresh.FourBlockDisplacedLeftRoles

/-! A captured original left reading relocates the isolation while the
native AP packet stays clear. Other captured competitors are allowed. -/
namespace Fresh.FourBlockLeftExit
open Fresh Fresh.Cascade Fresh.Localisation Fresh.FourBlockNeighbour
  Fresh.FourBlockEndpointCapture Fresh.FourBlockOuterLapPhase
  Fresh.FourBlockOuterTailClear Fresh.FourBlockOuterPacketRetention Fresh.FourBlockLeftOpening

theorem left_lonely (c g h j : ℝ) (p q r : ℕ)
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r) (hs : p+q+r ≤ 4)
    (hg : 0 < g) (hh : 0 < h) (hj : 0 < j) (m a b e rho : ℤ) (u : Fin 3) (L : Fin 3 → ℤ)
    (hlo : 11*(g+h+j)+16*remainder g h j m a b e ≤ 16*(rho : ℝ)-42)
    (hhi : 8*(rho : ℝ)-27 ≤ 7*(g+h+j)+8*remainder g h j m a b e)
    (hcaplo : (L u : ℝ)-1/8 < leftReading c g h j p q r u*outerLapOpening g h j m a b e rho-(leftLap m a b e p q r u : ℝ))
    (hcaphi : leftReading c g h j p q r u*outerLapOpening g h j m a b e rho-(leftLap m a b e p q r u : ℝ) < (L u : ℝ)+1/8)
    (houter : (4+g+h+j)*(leftOpening c g h j p q r m a b e u (L u)-outerLapOpening g h j m a b e rho) ≤ 3/4)
    (hinner : (4+g+h+j)*(leftOpening c g h j p q r m a b e u (L u)-outerLapOpening g h j m a b e rho)+
      3*(1-(leftOpening c g h j p q r m a b e u (L u)-(m : ℝ))) ≤ 3/4)
    (hother : OtherLeftBandsAt c g h j p q r m a b e (leftOpening c g h j p q r m a b e u (L u)) L u) :
    LonelyAt (disparitySet (speeds c g h j p q r) 0) (leftOpening c g h j p q r m a b e u (L u)) := by
  obtain ⟨hw,hop,ht⟩ := capture_opening c g h j p q r hq hr hg hh hj m a b e u (L u)
    (outerLapOpening g h j m a b e rho) hcaplo hcaphi
  have hleft := bands_at_opening c g h j p q r hq hr hg hh hj m a b e u L hother
  exact displaced_clear c g h j p q r hp hq hr hs hg hh hj m a b e rho
    (leftOpening c g h j p q r m a b e u (L u)) L hlo hhi ht.le houter hinner hleft

theorem left_move (c g h j : ℝ) (p q r : ℕ)
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r) (hs : p+q+r ≤ 4)
    (hg : 0 < g) (hh : 0 < h) (hj : 0 < j) (m a b e rho : ℤ) (u : Fin 3) (L : Fin 3 → ℤ)
    (hlo : 11*(g+h+j)+16*remainder g h j m a b e ≤ 16*(rho : ℝ)-42)
    (hhi : 8*(rho : ℝ)-27 ≤ 7*(g+h+j)+8*remainder g h j m a b e)
    (hcaplo : (L u : ℝ)-1/8 < leftReading c g h j p q r u*outerLapOpening g h j m a b e rho-(leftLap m a b e p q r u : ℝ))
    (hcaphi : leftReading c g h j p q r u*outerLapOpening g h j m a b e rho-(leftLap m a b e p q r u : ℝ) < (L u : ℝ)+1/8)
    (houter : (4+g+h+j)*(leftOpening c g h j p q r m a b e u (L u)-outerLapOpening g h j m a b e rho) ≤ 3/4)
    (hinner : (4+g+h+j)*(leftOpening c g h j p q r m a b e u (L u)-outerLapOpening g h j m a b e rho)+
      3*(1-(leftOpening c g h j p q r m a b e u (L u)-(m : ℝ))) ≤ 3/4)
    (hother : OtherLeftBandsAt c g h j p q r m a b e (leftOpening c g h j p q r m a b e u (L u)) L u) :
    IsMove (disparitySet (speeds c g h j p q r) 0) (outerLapOpening g h j m a b e rho)
      (leftOpening c g h j p q r m a b e u (L u)) := by
  obtain ⟨hw,hop,ht⟩ := capture_opening c g h j p q r hq hr hg hh hj m a b e u (L u)
    (outerLapOpening g h j m a b e rho) hcaplo hcaphi
  have hclear := left_lonely c g h j p q r hp hq hr hs hg hh hj m a b e rho u L
    hlo hhi hcaplo hcaphi houter hinner hother
  have hmem : |leftReading c g h j p q r u| ∈ disparitySet (speeds c g h j p q r) 0 := by
    refine mem_disparitySet.mpr ⟨prefixIndex u,?_,rfl⟩
    intro heq
    have hc := congrArg Fin.val heq
    simp [prefixIndex] at hc
  have hpos : ∀ d ∈ disparitySet (speeds c g h j p q r) 0, 0 < d := by
    intro d hd
    obtain ⟨i,hi0,rfl⟩ := mem_disparitySet.mp hd
    apply abs_pos.mpr
    have hstrict : StrictMono (speeds c g h j p q r) := by
      apply Fin.strictMono_iff_lt_succ.mpr
      intro idx
      have hd := FourBlockEndpoints.adjacent_speed_gap c g h j p q r hq hr idx
      split_ifs at hd <;> linarith
    exact sub_ne_zero.mpr (fun heq => hi0 (hstrict.injective heq))
  refine Or.inr ⟨_,hmem,hw,hop.symm,?_⟩
  intro d hd hwD
  exact nextOpening_le_of_lonely hpos hclear ht.le hd hwD

#print axioms left_lonely
#print axioms left_move
end Fresh.FourBlockLeftExit
