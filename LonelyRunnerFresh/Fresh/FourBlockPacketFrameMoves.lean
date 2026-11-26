import Fresh.FourBlockPacketFrameArrangement

/-! Actual native moves into the broader packet frame, including captured
competitors. Each terminal clearance is derived from the frame's cut bands. -/
namespace Fresh.FourBlockPacketFrameMoves
open Fresh Fresh.Cascade Fresh.Localisation Fresh.FourBlockNeighbour
  Fresh.FourBlockEndpointCapture Fresh.FourBlockLongTailBounds Fresh.FourBlockOuterLapPhase
  Fresh.FourBlockOuterTailClear Fresh.FourBlockOuterLapMove Fresh.FourBlockLeftOpening
  Fresh.FourBlockPacketFrameArrangement

theorem native_readings_positive (c g h j : ℝ) (p q r : ℕ) (hq : 1 ≤ q) (hr : 1 ≤ r)
    (hg : 0 < g) (hh : 0 < h) (hj : 0 < j) :
    ∀ d ∈ disparitySet (speeds c g h j p q r) 0, 0 < d := by
  intro d hd
  obtain ⟨i,hi0,rfl⟩ := mem_disparitySet.mp hd
  apply abs_pos.mpr
  have hstrict : StrictMono (speeds c g h j p q r) := by
    apply Fin.strictMono_iff_lt_succ.mpr
    intro idx
    have hd := FourBlockEndpoints.adjacent_speed_gap c g h j p q r hq hr idx
    split_ifs at hd <;> linarith
  exact sub_ne_zero.mpr (fun heq => hi0 (hstrict.injective heq))

theorem move_at_supplied_opening {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d)
    {t P d : ℝ} (hd : d ∈ ds) (hw : InWay d t)
    (hop : nextOpening d t=P) (hclear : LonelyAt ds P) : IsMove ds t P := by
  have ht : t < P := by rw [←hop]; exact lt_nextOpening (hpos d hd) hw
  refine Or.inr ⟨d,hd,hw,hop.symm,?_⟩
  intro e he hwe
  exact nextOpening_le_of_lonely hpos hclear ht.le he hwe

theorem left_move (c g h j : ℝ) (p q r : ℕ)
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r) (hs : p+q+r ≤ 4)
    (hg : 0 < g) (hh : 0 < h) (hj : 0 < j) (m a b e rho : ℤ) (u : Fin 3) (L : Fin 3 → ℤ)
    (hhi : 8*(rho : ℝ)-27 ≤ 7*(g+h+j)+8*remainder g h j m a b e)
    (hb : FrameBands c g h j p q r m a b e rho (some u) L)
    (hcaplo : (L u : ℝ)-1/8 < leftReading c g h j p q r u*outerLapOpening g h j m a b e rho-(leftLap m a b e p q r u : ℝ))
    (hcaphi : leftReading c g h j p q r u*outerLapOpening g h j m a b e rho-(leftLap m a b e p q r u : ℝ) < (L u : ℝ)+1/8) :
    IsMove (disparitySet (speeds c g h j p q r) 0) (outerLapOpening g h j m a b e rho)
      (leftOpening c g h j p q r m a b e u (L u)) := by
  obtain ⟨hw,hop,ht⟩ := capture_opening c g h j p q r hq hr hg hh hj m a b e u (L u)
    (outerLapOpening g h j m a b e rho) hcaplo hcaphi
  have hclear := frame_clear c g h j p q r hp hq hr hs hg hh hj m a b e rho (some u) L hhi hb
  have hmem : |leftReading c g h j p q r u| ∈ disparitySet (speeds c g h j p q r) 0 := by
    refine mem_disparitySet.mpr ⟨prefixIndex u,?_,rfl⟩
    intro heq
    have hc := congrArg Fin.val heq
    simp [prefixIndex] at hc
  exact move_at_supplied_opening (native_readings_positive c g h j p q r hq hr hg hh hj) hmem hw hop hclear

theorem outer_move (c g h j : ℝ) (p q r : ℕ)
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r) (hs : p+q+r ≤ 4)
    (hg : 0 < g) (hh : 0 < h) (hj : 0 < j) (m a b e rho : ℤ) (L : Fin 3 → ℤ) (t : ℝ)
    (hhi : 8*(rho : ℝ)-27 ≤ 7*(g+h+j)+8*remainder g h j m a b e)
    (hb : FrameBands c g h j p q r m a b e rho none L)
    (hcaplo : (rho : ℝ)-1/8 < (4+g+h+j)*t-(spanLap m a b e : ℝ))
    (hcaphi : (4+g+h+j)*t-(spanLap m a b e : ℝ) < (rho : ℝ)+1/8) :
    IsMove (disparitySet (speeds c g h j p q r) 0) t (outerLapOpening g h j m a b e rho) := by
  have hD7 : speeds c g h j p q r 7-speeds c g h j p q r 0=4+g+h+j := by
    have hd := tail_reading c g h j p q r hp hq hr hs (7 : Fin 8) (by norm_num)
    norm_num at hd
    exact hd
  have hpos7 : 0 < speeds c g h j p q r 7-speeds c g h j p q r 0 := by rw [hD7]; positivity
  have hN7 : wholeLap m a b e p q r 7-wholeLap m a b e p q r 0=spanLap m a b e := by
    rw [tail_lap p q r hp hq hr hs m a b e (7 : Fin 8) (by norm_num)]
    norm_num [spanLap]
  have hnear : |(speeds c g h j p q r 7-speeds c g h j p q r 0)*t-
      ((wholeLap m a b e p q r 7-wholeLap m a b e p q r 0+rho : ℤ) : ℝ)| < 1/8 := by
    rw [abs_lt,hD7,hN7]
    push_cast
    constructor <;> linarith
  have hw7 : InWay |speeds c g h j p q r 7-speeds c g h j p q r 0| t := by
    rw [abs_of_pos hpos7]
    exact lt_of_le_of_lt (Fresh.Cascade.distInt_le _ (wholeLap m a b e p q r 7-wholeLap m a b e p q r 0+rho)) hnear
  have hop7 : nextOpening |speeds c g h j p q r 7-speeds c g h j p q r 0| t=
      outerLapOpening g h j m a b e rho := by
    rw [abs_of_pos hpos7,nextOpening_eq hnear,hD7,hN7]
    dsimp [outerLapOpening]
    push_cast
    rfl
  have hmem : |speeds c g h j p q r 7-speeds c g h j p q r 0| ∈
      disparitySet (speeds c g h j p q r) 0 := mem_disparitySet.mpr ⟨7,by decide,rfl⟩
  have hclear := frame_clear c g h j p q r hp hq hr hs hg hh hj m a b e rho none L hhi hb
  exact move_at_supplied_opening (native_readings_positive c g h j p q r hq hr hg hh hj) hmem hw7 hop7 hclear

theorem six_handoff (c g h j : ℝ) (p q r : ℕ)
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r) (hs : p+q+r ≤ 4)
    (hg : 0 < g) (hh : 0 < h) (hj : 0 < j) (m a b e z : ℤ) (L : Fin 3 → ℤ)
    (hhi : 8*((z+1 : ℤ) : ℝ)-27 ≤ 7*(g+h+j)+8*remainder g h j m a b e)
    (hb : FrameBands c g h j p q r m a b e (z+1) none L)
    (htlo : (m : ℝ)+3/4 < sixLapOpening g h j m a b e z)
    (hthi : sixLapOpening g h j m a b e z < (m : ℝ)+1) :
    IsMove (disparitySet (speeds c g h j p q r) 0)
      (sixLapOpening g h j m a b e z) (outerLapOpening g h j m a b e (z+1)) := by
  have hf7 := Fresh.FourBlockOuterTailMove.six_outer_phase c g h j p q r hp hq hr hs hg hh hj m a b e z
  rw [tail_reading c g h j p q r hp hq hr hs (7 : Fin 8) (by norm_num)] at hf7
  norm_num at hf7
  apply outer_move c g h j p q r hp hq hr hs hg hh hj m a b e (z+1) L
    (sixLapOpening g h j m a b e z) hhi hb
  all_goals dsimp [spanLap] at hf7 ⊢; push_cast at hf7 ⊢; nlinarith only [hf7,htlo,hthi]

#print axioms native_readings_positive
#print axioms move_at_supplied_opening
#print axioms left_move
#print axioms outer_move
#print axioms six_handoff
end Fresh.FourBlockPacketFrameMoves
