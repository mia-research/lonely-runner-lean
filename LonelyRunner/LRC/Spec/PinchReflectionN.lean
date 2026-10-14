import LonelyRunner.LRC.Spec.SymbolicWindowTransportN

/-!
# Period reflection selects replacement labels at a one-sided pinch

At an old clear time t, let P_i = (lambda+1)*d_i*t be integral. The reflected
labels are P_i-q_i-1. All old clear readings reflect to clear readings at
lambda*t. Every active pairwise slack reverses its deformation slope, with
factor -lambda. This includes simultaneous active constraints.

This is LOCAL transport. It does not bound successive reflections or rule out
accumulation of parameter boundaries. Exact common-period data are explicit;
the corresponding approximation argument for arbitrary real data is not here.
-/

namespace LRC.PinchReflection

variable {ι : Type*}

/-- A finite affine system extends to the right if its zero slacks have
nonnegative slopes. Positive slacks get an explicit finite minimum margin. -/
theorem affine_right (S : Finset ι) (hS : S.Nonempty) (C B : ι → ℝ)
    (hC : ∀ i ∈ S, 0 ≤ C i)
    (hB : ∀ i ∈ S, C i = 0 → 0 ≤ B i) :
    ∃ e : ℝ, 0 < e ∧ ∀ h : ℝ, 0 ≤ h → h ≤ e → ∀ i ∈ S, 0 ≤ C i + h * B i := by
  classical
  let r := fun i => if 0 < C i then C i / (|B i| + 1) else 1
  have hr : ∀ i ∈ S, 0 < r i := by
    intro i hi
    dsimp [r]
    split_ifs with hc
    · exact div_pos hc (by positivity)
    · norm_num
  refine ⟨S.inf' hS r, (Finset.lt_inf'_iff hS).mpr hr, ?_⟩
  intro h hh he i hi
  have her : h ≤ r i := he.trans (Finset.inf'_le r hi)
  by_cases hc : 0 < C i
  · have hb : h * (|B i| + 1) ≤ C i :=
      (le_div_iff₀ (by positivity : 0 < |B i| + 1)).mp (by simpa [r, hc] using her)
    have hm := mul_le_mul_of_nonneg_left (neg_abs_le (B i)) hh
    nlinarith
  · have hz : C i = 0 := le_antisymm (le_of_not_gt hc) (hC i hi)
    simpa [hz] using mul_nonneg hh (hB i hi hz)

/-- The reflected lap label is explicit, not supplied as a clearance witness. -/
theorem reflected_band {d t lam : ℝ} {q P : ℤ}
    (hP : (P : ℝ) = (lam + 1) * d * t)
    (hl : (q : ℝ) + 1/8 ≤ d*t) (hu : d*t ≤ q+7/8) :
    ((P-q-1 : ℤ) : ℝ) + 1/8 ≤ d*(lam*t) ∧
      d*(lam*t) ≤ ((P-q-1 : ℤ) : ℝ)+7/8 := by
  push_cast
  constructor <;> nlinarith

/-- At the pinch, the reflected slack of the reversed pair equals the old slack. -/
theorem reflected_slack {di dj t lam : ℝ} {qi qj Pi Pj : ℤ}
    (hPi : (Pi : ℝ) = (lam+1)*di*t)
    (hPj : (Pj : ℝ) = (lam+1)*dj*t) :
    (((Pi-qi-1 : ℤ) : ℝ)+7/8)*dj - (((Pj-qj-1 : ℤ) : ℝ)+1/8)*di =
      ((qj : ℝ)+7/8)*di - ((qi : ℝ)+1/8)*dj := by
  push_cast
  rw [hPi, hPj]
  ring

/-- A zero pairwise slack in an actual common band identifies both boundaries. -/
theorem active_boundaries {di dj t : ℝ} {qi qj : ℤ}
    (hi : 0 < di) (hj : 0 < dj)
    (hl : (qi : ℝ)+1/8 ≤ di*t) (hu : dj*t ≤ qj+7/8)
    (hz : ((qj : ℝ)+7/8)*di - ((qi : ℝ)+1/8)*dj = 0) :
    di*t = (qi : ℝ)+1/8 ∧ dj*t = (qj : ℝ)+7/8 := by
  have h1 := mul_le_mul_of_nonneg_left hl hj.le
  have h2 := mul_le_mul_of_nonneg_left hu hi.le
  constructor
  · apply mul_left_cancel₀ (ne_of_gt hj)
    nlinarith
  · apply mul_left_cancel₀ (ne_of_gt hi)
    nlinarith

/-- Every active derivative reverses sign, including tied/simultaneous pinches. -/
theorem active_slope_reversal {di dj vi vj t lam : ℝ} {qi qj Pi Pj : ℤ}
    (hPi : (Pi : ℝ) = (lam+1)*di*t)
    (hPj : (Pj : ℝ) = (lam+1)*dj*t)
    (hi : di*t = (qi : ℝ)+1/8) (hj : dj*t = (qj : ℝ)+7/8) :
    (((Pi-qi-1 : ℤ) : ℝ)+7/8)*vj - (((Pj-qj-1 : ℤ) : ℝ)+1/8)*vi =
      -lam * (((qj : ℝ)+7/8)*vi - ((qi : ℝ)+1/8)*vj) := by
  have hPi' : (Pi : ℝ) = (lam+1)*((qi : ℝ)+1/8) := by rw [← hi, hPi]; ring
  have hPj' : (Pj : ℝ) = (lam+1)*((qj : ℝ)+7/8) := by rw [← hj, hPj]; ring
  push_cast
  rw [hPi', hPj']
  ring

/-- Being feasible at a strictly earlier parameter determines the direction of
an active slack; this is not a hypothesis about future clearance. -/
theorem active_slope_nonpos {C B delta : ℝ} (hd : 0 < delta)
    (hz : C = 0) (hleft : 0 ≤ C - delta*B) : B ≤ 0 := by
  rw [hz] at hleft
  nlinarith

/-- A common period produces an actual right neighbourhood of feasible
replacement lap inequalities. No future-isolation assumption is present. -/
theorem reflected_right_inequalities (S : Finset ι) (hS : S.Nonempty)
    (d v : ι → ℝ) (q P : ι → ℤ) {t lam delta : ℝ}
    (hd : ∀ i ∈ S, 0 < d i) (hlam : 0 < lam) (hdelta : 0 < delta)
    (hP : ∀ i ∈ S, (P i : ℝ) = (lam+1)*d i*t)
    (hband : ∀ i ∈ S, (q i : ℝ)+1/8 ≤ d i*t ∧ d i*t ≤ q i+7/8)
    (hleft : ∀ i ∈ S, ∀ j ∈ S,
      ((q i : ℝ)+1/8)*(d j-delta*v j) ≤ ((q j : ℝ)+7/8)*(d i-delta*v i)) :
    ∃ e : ℝ, 0 < e ∧ ∀ h : ℝ, 0 ≤ h → h ≤ e → ∀ i ∈ S, ∀ j ∈ S,
      (((P i-q i-1 : ℤ) : ℝ)+1/8)*(d j+h*v j) ≤
        (((P j-q j-1 : ℤ) : ℝ)+7/8)*(d i+h*v i) := by
  let C := fun p : ι × ι =>
    (((P p.2-q p.2-1 : ℤ) : ℝ)+7/8)*d p.1 -
      (((P p.1-q p.1-1 : ℤ) : ℝ)+1/8)*d p.2
  let B := fun p : ι × ι =>
    (((P p.2-q p.2-1 : ℤ) : ℝ)+7/8)*v p.1 -
      (((P p.1-q p.1-1 : ℤ) : ℝ)+1/8)*v p.2
  have hC : ∀ p ∈ S ×ˢ S, 0 ≤ C p := by
    rintro ⟨i,j⟩ hp
    obtain ⟨hi,hj⟩ := Finset.mem_product.mp hp
    have he := reflected_slack (hP j hj) (hP i hi) (qi := q j) (qj := q i)
    dsimp [C]
    rw [he]
    have h1 := mul_le_mul_of_nonneg_left (hband j hj).1 (hd i hi).le
    have h2 := mul_le_mul_of_nonneg_left (hband i hi).2 (hd j hj).le
    nlinarith
  have hB : ∀ p ∈ S ×ˢ S, C p = 0 → 0 ≤ B p := by
    rintro ⟨i,j⟩ hp hz
    obtain ⟨hi,hj⟩ := Finset.mem_product.mp hp
    have he := reflected_slack (hP j hj) (hP i hi) (qi := q j) (qj := q i)
    have hold : ((q i : ℝ)+7/8)*d j - ((q j : ℝ)+1/8)*d i = 0 := by
      dsimp [C] at hz
      rwa [he] at hz
    obtain ⟨hl,hu⟩ := active_boundaries (hd j hj) (hd i hi)
      (hband j hj).1 (hband i hi).2 hold
    have hb : ((q i : ℝ)+7/8)*v j - ((q j : ℝ)+1/8)*v i ≤ 0 := by
      apply active_slope_nonpos hdelta hold
      nlinarith [hleft j hj i hi]
    dsimp [B]
    rw [active_slope_reversal (hP j hj) (hP i hi) hl hu]
    exact mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr hlam.le) hb
  obtain ⟨e, he, hw⟩ := affine_right (S ×ˢ S) (hS.product hS) C B hC hB
  refine ⟨e, he, ?_⟩
  intro h hh heh i hi j hj
  have hw' := hw h hh heh (i,j) (Finset.mem_product.mpr ⟨hi,hj⟩)
  dsimp [C, B] at hw'
  nlinarith

/-- The selected reflected labels give positive-time windows throughout a
right neighbourhood. Positivity of the perturbed disparities is derived too. -/
theorem reflected_right_windows (S : Finset ι) (hS : S.Nonempty)
    (d v : ι → ℝ) (q P : ι → ℤ) {t lam delta : ℝ}
    (hd : ∀ i ∈ S, 0 < d i) (ht : 0 < t) (hlam : 0 < lam) (hdelta : 0 < delta)
    (hP : ∀ i ∈ S, (P i : ℝ) = (lam+1)*d i*t)
    (hband : ∀ i ∈ S, (q i : ℝ)+1/8 ≤ d i*t ∧ d i*t ≤ q i+7/8)
    (hleft : ∀ i ∈ S, ∀ j ∈ S,
      ((q i : ℝ)+1/8)*(d j-delta*v j) ≤ ((q j : ℝ)+7/8)*(d i-delta*v i)) :
    ∃ e : ℝ, 0 < e ∧ ∀ h : ℝ, 0 ≤ h → h ≤ e →
      ∃ u : ℝ, 0 < u ∧ ∀ i ∈ S,
        ((P i-q i-1 : ℤ) : ℝ)+1/8 ≤ (d i+h*v i)*u ∧
          (d i+h*v i)*u ≤ ((P i-q i-1 : ℤ) : ℝ)+7/8 := by
  obtain ⟨e1, he1, hw⟩ := reflected_right_inequalities S hS d v q P hd hlam hdelta hP hband hleft
  obtain ⟨e2, he2, hp⟩ := affine_right S hS (fun i => d i/2) v
    (fun i hi => (div_pos (hd i hi) (by norm_num)).le)
    (fun i hi hz => by have := hd i hi; linarith)
  have hq : ∀ i ∈ S, (0 : ℝ) ≤ ((P i-q i-1 : ℤ) : ℝ) := by
    intro i hi
    have hr := (reflected_band (hP i hi) (hband i hi).1 (hband i hi).2).2
    have hpos := mul_pos (hd i hi) (mul_pos hlam ht)
    have hint : 0 ≤ P i-q i-1 := by
      by_contra h
      have hi' : P i-q i-1 ≤ -1 := by omega
      have hr' : ((P i-q i-1 : ℤ) : ℝ) ≤ -1 := by exact_mod_cast hi'
      linarith
    exact_mod_cast hint
  refine ⟨min e1 e2, lt_min he1 he2, ?_⟩
  intro h hh he
  have hd' : ∀ i ∈ S, 0 < d i+h*v i := by
    intro i hi
    have := hp h hh (he.trans (min_le_right _ _)) i hi
    have := hd i hi
    linarith
  have hlin : ∀ i ∈ S, ∀ j ∈ S,
      (8 * (((P i-q i-1 : ℤ) : ℝ))+1)*(d j+h*v j) ≤
        (8 * (((P j-q j-1 : ℤ) : ℝ))+7)*(d i+h*v i) := by
    intro i hi j hj
    have := hw h hh (he.trans (min_le_left _ _)) i hi j hj
    nlinarith
  obtain ⟨u, hu⟩ := (WindowPinch.lap_windows_iff S hS
    (fun i => d i+h*v i) (fun i => P i-q i-1) hd').mpr hlin
  obtain ⟨i, hi⟩ := hS
  have hl := (hu i hi).1
  have hqi := hq i hi
  have hprod : 0 < (d i+h*v i)*u := by linarith
  exact ⟨u, pos_of_mul_pos_right hprod (hd' i hi).le, hu⟩

/-- Finite rational readings have a common integer multiplier, constructed
by successively multiplying denominators. No isolation assumption is used. -/
theorem rational_common_multiplier (S : Finset ι) (r : ι → ℚ) :
    ∃ N : ℕ, 0 < N ∧ ∀ i ∈ S, ∃ P : ℤ, (P : ℚ) = (N : ℚ)*r i := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1, by norm_num, by simp⟩
  | @insert a S ha ih =>
    obtain ⟨N, hN, hP⟩ := ih
    refine ⟨(r a).den*N, Nat.mul_pos (r a).den_pos hN, ?_⟩
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · refine ⟨(r i).num*(N : ℤ), ?_⟩
      push_cast
      nlinarith [Rat.den_mul_eq_num (r i)]
    · obtain ⟨P, hP⟩ := hP i hi
      refine ⟨((r a).den : ℤ)*P, ?_⟩
      push_cast
      rw [hP]
      ring

/-- At rational data a positive reflection multiplier and all period labels
exist automatically. The exact-period hypothesis is discharged in this case. -/
theorem rational_reflection_data (S : Finset ι) (d : ι → ℚ) (t : ℚ) :
    ∃ lam : ℝ, 0 < lam ∧ ∃ P : ι → ℤ,
      ∀ i ∈ S, (P i : ℝ) = (lam+1)*(d i : ℝ)*(t : ℝ) := by
  classical
  obtain ⟨N, hN, hP⟩ := rational_common_multiplier S (fun i => 8*d i*t)
  let P := fun i => if hi : i ∈ S then Classical.choose (hP i hi) else 0
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  refine ⟨8*(N : ℝ)-1, by linarith, P, ?_⟩
  intro i hi
  have hp : (P i : ℚ) = (N : ℚ)*(8*d i*t) := by
    simpa [P, hi] using Classical.choose_spec (hP i hi)
  have hp' : (P i : ℝ) = (N : ℝ)*(8*(d i : ℝ)*(t : ℝ)) := by exact_mod_cast hp
  rw [hp']
  ring

/-- Successful replacement labels exist at every rational one-sided pinch,
for arbitrary real deformation directions. No replacement certificate, future
isolation, or bound on a cascade is assumed. This remains a local theorem. -/
theorem rational_pinch_transport (S : Finset ι) (hS : S.Nonempty)
    (d : ι → ℚ) (v : ι → ℝ) (q : ι → ℤ) (t : ℚ) {delta : ℝ}
    (hd : ∀ i ∈ S, 0 < (d i : ℝ)) (ht : 0 < (t : ℝ)) (hdelta : 0 < delta)
    (hband : ∀ i ∈ S, (q i : ℝ)+1/8 ≤ (d i : ℝ)*(t : ℝ) ∧
      (d i : ℝ)*(t : ℝ) ≤ q i+7/8)
    (hleft : ∀ i ∈ S, ∀ j ∈ S,
      ((q i : ℝ)+1/8)*((d j : ℝ)-delta*v j) ≤
        ((q j : ℝ)+7/8)*((d i : ℝ)-delta*v i)) :
    ∃ p : ι → ℤ, ∃ e : ℝ, 0 < e ∧ ∀ h : ℝ, 0 ≤ h → h ≤ e →
      ∃ u : ℝ, 0 < u ∧ ∀ i ∈ S,
        (p i : ℝ)+1/8 ≤ ((d i : ℝ)+h*v i)*u ∧
          ((d i : ℝ)+h*v i)*u ≤ p i+7/8 := by
  obtain ⟨lam, hlam, P, hP⟩ := rational_reflection_data S d t
  exact ⟨fun i => P i-q i-1,
    reflected_right_windows S hS (fun i => (d i : ℝ)) v q P
      hd ht hlam hdelta hP hband hleft⟩

end LRC.PinchReflection
