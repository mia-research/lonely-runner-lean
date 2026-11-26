import Fresh.FourBlockOuterTailArrangement

/-! One actual runner6→7 handoff rule for all four physical partitions,
with every original competitor retained. -/
namespace Fresh.FourBlockOuterTailMove
open Fresh Fresh.Cascade Fresh.Localisation Fresh.FourBlockNeighbour
  Fresh.FourBlockEndpointCapture Fresh.FourBlockLongTailBounds Fresh.FourBlockOuterLapPhase
  Fresh.FourBlockOuterLapMove Fresh.FourBlockOuterTailClear

theorem six_outer_phase (c g h j : ℝ) (u v w : ℕ)
    (hu : 1 ≤ u) (hv : 1 ≤ v) (hw : 1 ≤ w) (hs : u+v+w ≤ 4)
    (hg : 0 < g) (hh : 0 < h) (hj : 0 < j) (m a b e q : ℤ) :
    (speeds c g h j u v w 7-speeds c g h j u v w 0)*sixLapOpening g h j m a b e q-
      (spanLap m a b e : ℝ)=
      (q : ℝ)+1/8+(sixLapOpening g h j m a b e q-(m : ℝ)) := by
  rw [tail_reading c g h j u v w hu hv hw hs (7 : Fin 8) (by norm_num)]
  norm_num
  have hid := six_identity g h j hg hh hj m a b e q
  dsimp [spanLap]
  push_cast at hid ⊢
  nlinarith only [hid]

theorem outer_move_from (c g h j : ℝ) (u v w : ℕ)
    (hu : 1 ≤ u) (hv : 1 ≤ v) (hw : 1 ≤ w) (hsize : u+v+w ≤ 4)
    (hg : 0 < g) (hh : 0 < h) (hj : 0 < j)
    (m a b e r : ℤ) (L : Fin 3 → ℤ) (t : ℝ)
    (hlo : 11*(g+h+j)+16*remainder g h j m a b e ≤ 16*(r : ℝ)-42)
    (hhi : 8*(r : ℝ)-27 ≤ 7*(g+h+j)+8*remainder g h j m a b e)
    (hleft : LeftBands c g h j u v w m a b e r L)
    (hcaplo : (r : ℝ)-1/8 < (4+g+h+j)*t-(spanLap m a b e : ℝ))
    (hcaphi : (4+g+h+j)*t-(spanLap m a b e : ℝ) < (r : ℝ)+1/8) :
    IsMove (disparitySet (speeds c g h j u v w) 0) t (outerLapOpening g h j m a b e r) := by
  have hD7 : speeds c g h j u v w 7-speeds c g h j u v w 0=4+g+h+j := by
    have hd := tail_reading c g h j u v w hu hv hw hsize (7 : Fin 8) (by norm_num)
    norm_num at hd
    exact hd
  have hpos7 : 0 < speeds c g h j u v w 7-speeds c g h j u v w 0 := by rw [hD7]; positivity
  have hN7 : wholeLap m a b e u v w 7-wholeLap m a b e u v w 0=spanLap m a b e := by
    rw [tail_lap u v w hu hv hw hsize m a b e (7 : Fin 8) (by norm_num)]
    norm_num [spanLap]
  have hnear : |(speeds c g h j u v w 7-speeds c g h j u v w 0)*t-
      ((wholeLap m a b e u v w 7-wholeLap m a b e u v w 0+r : ℤ) : ℝ)| < 1/8 := by
    rw [abs_lt,hD7,hN7]
    push_cast
    constructor <;> linarith
  have hw7 : InWay |speeds c g h j u v w 7-speeds c g h j u v w 0| t := by
    rw [abs_of_pos hpos7]
    exact lt_of_le_of_lt (Fresh.Cascade.distInt_le _ (wholeLap m a b e u v w 7-wholeLap m a b e u v w 0+r)) hnear
  have hop7 : nextOpening |speeds c g h j u v w 7-speeds c g h j u v w 0| t=
      outerLapOpening g h j m a b e r := by
    rw [abs_of_pos hpos7,nextOpening_eq hnear,hD7,hN7]
    dsimp [outerLapOpening]
    push_cast
    rfl
  have hmem : |speeds c g h j u v w 7-speeds c g h j u v w 0| ∈
      disparitySet (speeds c g h j u v w) 0 := mem_disparitySet.mpr ⟨7,by decide,rfl⟩
  have hpos : ∀ d ∈ disparitySet (speeds c g h j u v w) 0, 0 < d := by
    intro d hd
    obtain ⟨i,hi0,rfl⟩ := mem_disparitySet.mp hd
    apply abs_pos.mpr
    have hstrict : StrictMono (speeds c g h j u v w) := by
      apply Fin.strictMono_iff_lt_succ.mpr
      intro idx
      have hd := FourBlockEndpoints.adjacent_speed_gap c g h j u v w hv hw idx
      split_ifs at hd <;> linarith
    exact sub_ne_zero.mpr (fun heq => hi0 (hstrict.injective heq))
  have htime : t ≤ outerLapOpening g h j m a b e r := by
    rw [←hop7]
    exact (lt_nextOpening (by rw [abs_of_pos hpos7]; exact hpos7) hw7).le
  have hclear := Fresh.FourBlockOuterTailClear.outer_clear c g h j u v w hu hv hw hsize hg hh hj m a b e r L hlo hhi hleft
  refine Or.inr ⟨_,hmem,hw7,hop7.symm,?_⟩
  intro d hd hwD
  exact nextOpening_le_of_lonely hpos hclear htime hd hwD

theorem six_handoff (c g h j : ℝ) (u v w : ℕ)
    (hu : 1 ≤ u) (hv : 1 ≤ v) (hw : 1 ≤ w) (hsize : u+v+w ≤ 4)
    (hg : 0 < g) (hh : 0 < h) (hj : 0 < j)
    (m a b e q : ℤ) (L : Fin 3 → ℤ)
    (hlo : 11*(g+h+j)+16*remainder g h j m a b e ≤ 16*((q+1 : ℤ) : ℝ)-42)
    (hhi : 8*((q+1 : ℤ) : ℝ)-27 ≤ 7*(g+h+j)+8*remainder g h j m a b e)
    (hleft : LeftBands c g h j u v w m a b e (q+1) L)
    (htlo : (m : ℝ)+3/4 < sixLapOpening g h j m a b e q)
    (hthi : sixLapOpening g h j m a b e q < (m : ℝ)+1) :
    IsMove (disparitySet (speeds c g h j u v w) 0)
      (sixLapOpening g h j m a b e q) (outerLapOpening g h j m a b e (q+1)) := by
  have hf7 := six_outer_phase c g h j u v w hu hv hw hsize hg hh hj m a b e q
  rw [tail_reading c g h j u v w hu hv hw hsize (7 : Fin 8) (by norm_num)] at hf7
  norm_num at hf7
  apply outer_move_from c g h j u v w hu hv hw hsize hg hh hj m a b e (q+1) L
    (sixLapOpening g h j m a b e q) hlo hhi hleft
  all_goals dsimp [spanLap] at hf7 ⊢; push_cast at hf7 ⊢; nlinarith only [hf7,htlo,hthi]

#print axioms six_outer_phase
#print axioms outer_move_from
#print axioms six_handoff
end Fresh.FourBlockOuterTailMove
