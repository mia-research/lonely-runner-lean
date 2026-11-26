import Fresh.FourBlockArrangementJoins

/-! Native endpoint frontier beyond the direct endpoint guards. At the
supplied reference only the opposite endpoint can be captured. This proves
the exact first continuation, not termination of its later returning packet.
Original full histories and reference continuations are recorded separately
in four_block_endpoint_resumption_map_v1.py/json; a reference may be skipped. -/
namespace Fresh.FourBlockEndpointCapture
open Fresh Fresh.Cascade Fresh.Localisation Fresh.FourBlockNeighbour

noncomputable def remainder (g h j : ℝ) (m a b e : ℤ) : ℝ :=
  1/2+(g+h+j)*((m : ℝ)+1/8)-((a : ℝ)+(b : ℝ)+(e : ℝ))

def spanLap (m a b e : ℤ) : ℤ := 4*m+a+b+e

noncomputable def outerOpening (g h j : ℝ) (m a b e : ℤ) : ℝ :=
  ((spanLap m a b e : ℝ)+9/8)/(4+g+h+j)

theorem reference_inner_clear (c g h j : ℝ) (p q r : ℕ)
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r) (hs : p+q+r ≤ 7) (m a b e : ℤ)
    (hg : 8*(a : ℝ)+1 ≤ (8*(m : ℝ)+1)*g)
    (hh : 8*(b : ℝ)+1 ≤ (8*(m : ℝ)+1)*h)
    (hj : 8*(e : ℝ)+1 ≤ (8*(m : ℝ)+1)*j)
    (hsum : (8*(m : ℝ)+1)*(g+h+j) ≤ 8*((a : ℝ)+(b : ℝ)+(e : ℝ))+4)
    (i : Fin 8) (hi0 : i≠0) (hi7 : i≠7) :
    (1/8 : ℝ) ≤ distInt ((speeds c g h j p q r i-speeds c g h j p q r 0)*((m : ℝ)+1/8)) ∧
    (1/8 : ℝ) ≤ distInt ((speeds c g h j p q r i-speeds c g h j p q r 7)*((m : ℝ)+1/8)) := by
  have hu : (1/8 : ℝ) ≤ g*((m : ℝ)+1/8)-(a : ℝ) := by nlinarith
  have hv : (1/8 : ℝ) ≤ h*((m : ℝ)+1/8)-(b : ℝ) := by nlinarith
  have hw : (1/8 : ℝ) ≤ j*((m : ℝ)+1/8)-(e : ℝ) := by nlinarith
  have hgap : ∀u : Fin 7,(1/8 : ℝ) ≤
      phase c g h j p q r m a b e u.succ-phase c g h j p q r m a b e u.castSucc := by
    intro u
    rw [adjacent_phase_gap c g h j p q r hq hr m a b e u]
    split_ifs  <;> linarith
  have hspan : phase c g h j p q r m a b e 7-phase c g h j p q r m a b e 0 ≤ 1 := by
    rw [phase_span c g h j p q r hp hq hr hs m a b e]
    nlinarith
  have hi0' : (0 : Fin 8) < i := by
    have := Fin.val_ne_of_ne hi0
    change (0 : ℕ) < (i : ℕ)
    omega
  have hi7' : i < (7 : Fin 8) := by
    have := Fin.val_ne_of_ne hi7
    have := i.isLt
    change (i : ℕ) < (7 : ℕ)
    omega
  have hl := Fresh.PhaseNeighbour.phase_separation _ hgap 0 i hi0'
  have hr' := Fresh.PhaseNeighbour.phase_separation _ hgap i 7 hi7'
  have he0 : (speeds c g h j p q r i-speeds c g h j p q r 0)*((m : ℝ)+1/8)=
      phase c g h j p q r m a b e i-phase c g h j p q r m a b e 0+
      ((wholeLap m a b e p q r i-wholeLap m a b e p q r 0 : ℤ) : ℝ) := by
    rw [sub_mul,phase_identity,phase_identity]
    push_cast
    ring
  have he7 : (speeds c g h j p q r i-speeds c g h j p q r 7)*((m : ℝ)+1/8)=
      phase c g h j p q r m a b e i-phase c g h j p q r m a b e 7+
      ((wholeLap m a b e p q r i-wholeLap m a b e p q r 7 : ℤ) : ℝ) := by
    rw [sub_mul,phase_identity,phase_identity]
    push_cast
    ring
  constructor
  · apply clear_of_window (wholeLap m a b e p q r i-wholeLap m a b e p q r 0)
    all_goals rw [he0]; push_cast; linarith
  · apply clear_of_window (wholeLap m a b e p q r i-wholeLap m a b e p q r 7-1)
    all_goals rw [he7]; push_cast; linarith

theorem left_captured_move (c g h j : ℝ) (p q r : ℕ)
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r) (hs : p+q+r ≤ 7)
    (hgpos : 0 < g) (hhpos : 0 < h) (hjpos : 0 < j) (m a b e : ℤ)
    (hg : 8*(a : ℝ)+1 ≤ (8*(m : ℝ)+1)*g)
    (hh : 8*(b : ℝ)+1 ≤ (8*(m : ℝ)+1)*h)
    (hj : 8*(e : ℝ)+1 ≤ (8*(m : ℝ)+1)*j)
    (hsum : (8*(m : ℝ)+1)*(g+h+j) ≤ 8*((a : ℝ)+(b : ℝ)+(e : ℝ))+4)
    (hcap : (7/8 : ℝ) < remainder g h j m a b e) :
    IsMove (disparitySet (speeds c g h j p q r) 0)
      ((m : ℝ)+1/8) (outerOpening g h j m a b e) := by
  have hD : 0 < 4+g+h+j := by linarith
  have hspan := FourBlockEndpoints.speed_span c g h j p q r hp hq hr hs
  have hrem : remainder g h j m a b e ≤ 1 := by dsimp [remainder]; nlinarith
  have hphase : (4+g+h+j)*((m : ℝ)+1/8)=
      (spanLap m a b e : ℝ)+remainder g h j m a b e := by
    dsimp [spanLap,remainder]
    push_cast
    ring
  have hnear : |(4+g+h+j)*((m : ℝ)+1/8)-((spanLap m a b e+1 : ℤ) : ℝ)| < 1/8 := by
    rw [abs_lt,hphase]
    push_cast
    constructor  <;> linarith
  have hwD : InWay (4+g+h+j) ((m : ℝ)+1/8) :=
    lt_of_le_of_lt (Fresh.Cascade.distInt_le _ (spanLap m a b e+1)) hnear
  have hopD : nextOpening (4+g+h+j) ((m : ℝ)+1/8)=outerOpening g h j m a b e := by
    rw [nextOpening_eq hnear]
    dsimp [outerOpening]
    push_cast
    congr 1
    ring
  have hDmem : 4+g+h+j ∈ disparitySet (speeds c g h j p q r) 0 := by
    apply mem_disparitySet.mpr
    refine ⟨7,by decide,?_⟩
    rw [hspan,abs_of_pos hD]
  refine Or.inr ⟨4+g+h+j,hDmem,hwD,hopD.symm,?_⟩
  intro d hd hw
  obtain ⟨i,hi0,rfl⟩ := mem_disparitySet.mp hd
  by_cases hi7 : i=7
  · subst i
    rw [hspan,abs_of_pos hD]
    exact hopD.le
  · have hc := (reference_inner_clear c g h j p q r hp hq hr hs m a b e hg hh hj hsum i hi0 hi7).1
    change distInt (|speeds c g h j p q r i-speeds c g h j p q r 0| * ((m : ℝ)+1/8)) < 1/8 at hw
    rw [Fresh.Localisation.distInt_abs_mul] at hw
    exact False.elim ((not_lt_of_ge hc) hw)

theorem left_reference_choice (c g h j : ℝ) (p q r : ℕ)
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r) (hs : p+q+r ≤ 7)
    (hgpos : 0 < g) (hhpos : 0 < h) (hjpos : 0 < j) (m a b e : ℤ)
    (hg : 8*(a : ℝ)+1 ≤ (8*(m : ℝ)+1)*g)
    (hh : 8*(b : ℝ)+1 ≤ (8*(m : ℝ)+1)*h)
    (hj : 8*(e : ℝ)+1 ≤ (8*(m : ℝ)+1)*j)
    (hsum : (8*(m : ℝ)+1)*(g+h+j) ≤ 8*((a : ℝ)+(b : ℝ)+(e : ℝ))+4) :
    (remainder g h j m a b e=7/8 ∧
      LonelyAt (disparitySet (speeds c g h j p q r) 0) ((m : ℝ)+1/8)) ∨
    ((7/8 : ℝ) < remainder g h j m a b e ∧
      IsMove (disparitySet (speeds c g h j p q r) 0)
        ((m : ℝ)+1/8) (outerOpening g h j m a b e)) := by
  have hremlo : (7/8 : ℝ) ≤ remainder g h j m a b e := by
    dsimp [remainder]
    nlinarith
  by_cases hedge : remainder g h j m a b e=7/8
  · refine Or.inl ⟨hedge,?_⟩
    intro d hd
    obtain ⟨i,hi0,rfl⟩ := mem_disparitySet.mp hd
    rw [Fresh.Localisation.distInt_abs_mul]
    by_cases hi7 : i=7
    · subst i
      have hspan := FourBlockEndpoints.speed_span c g h j p q r hp hq hr hs
      have hphase : (4+g+h+j)*((m : ℝ)+1/8)=
          (spanLap m a b e : ℝ)+remainder g h j m a b e := by
        dsimp [spanLap,remainder]
        push_cast
        ring
      rw [hspan,hphase,hedge]
      apply clear_of_window (spanLap m a b e) <;> linarith
    · exact (reference_inner_clear c g h j p q r hp hq hr hs m a b e hg hh hj hsum i hi0 hi7).1
  · have hcap : (7/8 : ℝ) < remainder g h j m a b e := lt_of_le_of_ne hremlo (Ne.symm hedge)
    exact Or.inr ⟨hcap,left_captured_move c g h j p q r hp hq hr hs hgpos hhpos hjpos m a b e hg hh hj hsum hcap⟩

#print axioms reference_inner_clear
#print axioms left_captured_move
#print axioms left_reference_choice
end Fresh.FourBlockEndpointCapture
