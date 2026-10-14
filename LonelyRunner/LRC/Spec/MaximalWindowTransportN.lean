import LonelyRunner.LRC.Spec.IncomingWindowN

/-!+# A dying rational affine window selects its own replacement

A natural lap vector is feasible at the initial point and at a positive
parameter r, but fails at the target. Its first loss occurs at a rational
parameter tau in [r,1). The old window is feasible there, and the incoming
reflection theorem constructs labels valid to its right. Ties are permitted.
No pinch location, rational witness time or future labels are supplied.
This still makes no assertion about an infinite sequence of replacements.
-/

namespace LRC.MaximalWindowTransport
variable {ι : Type*}

/-- The least decreasing root is rational and is after any known feasible
positive parameter. Initial zero slacks cause no exception to this statement. -/
theorem rational_first_loss (S : Finset ι) (A B : ι → ℚ) {r : ℝ}
    (hr : 0 < r) (hA : ∀ i ∈ S, 0 ≤ (A i : ℝ))
    (hR : ∀ i ∈ S, 0 ≤ (A i : ℝ)+r*(B i : ℝ))
    (hfail : ∃ i ∈ S, (A i : ℝ)+(B i : ℝ) < 0) :
    ∃ tau : ℚ, r ≤ (tau : ℝ) ∧ (tau : ℝ) < 1 ∧
      (∀ s : ℝ, 0 ≤ s → s ≤ (tau : ℝ) →
        ∀ i ∈ S, 0 ≤ (A i : ℝ)+s*(B i : ℝ)) ∧
      (∀ s : ℝ, (tau : ℝ) < s →
        ∃ i ∈ S, (A i : ℝ)+s*(B i : ℝ) < 0) := by
  have hdec : ∃ i ∈ S, (B i : ℝ) < 0 := by
    obtain ⟨i, hi, hf⟩ := hfail
    exact ⟨i, hi, by linarith [hA i hi]⟩
  obtain ⟨p, hp, hb, ht, hbefore, heq, hafter⟩ :=
    WindowPinch.exists_first_pinch S (fun i => (A i : ℝ)) (fun i => (B i : ℝ)) hA hdec
  let tau : ℚ := A p / (-B p)
  have htau : (tau : ℝ) = (A p : ℝ)/(-(B p : ℝ)) := by simp [tau]
  have hrt : r ≤ (tau : ℝ) := by
    rw [htau]
    exact (WindowPinch.decreasing_slack_iff hb).mp (hR p hp)
  have ht1 : (tau : ℝ) < 1 := by
    by_contra hn
    obtain ⟨i, hi, hf⟩ := hfail
    have hh := hbefore 1 (by norm_num) (by rw [← htau]; exact le_of_not_gt hn) i hi
    linarith
  refine ⟨tau, hrt, ht1, ?_, ?_⟩
  · simpa only [htau] using hbefore
  · intro s hs
    exact ⟨p, hp, hafter s (by simpa only [htau] using hs)⟩

/-- Automatic local replacement at the actual endpoint of an incoming
window along a rational affine deformation. No simple-pinch assumption. -/
theorem replacement_at_first_loss (S : Finset ι) (hS : S.Nonempty)
    (a b : ι → ℚ) (q : ι → ℕ) {r : ℝ}
    (ha : ∀ i ∈ S, 0 < (a i : ℝ)) (hb : ∀ i ∈ S, 0 < (b i : ℝ))
    (hr : 0 < r) (hr1 : r ≤ 1)
    (hstart : ∃ t : ℝ, ∀ i ∈ S,
      (q i : ℝ)+1/8 ≤ (a i : ℝ)*t ∧ (a i : ℝ)*t ≤ q i+7/8)
    (hin : ∃ t : ℝ, ∀ i ∈ S,
      (q i : ℝ)+1/8 ≤ ((a i : ℝ)+r*((b i : ℝ)-a i))*t ∧
        ((a i : ℝ)+r*((b i : ℝ)-a i))*t ≤ q i+7/8)
    (hfail : ¬ ∃ t : ℝ, ∀ i ∈ S,
      (q i : ℝ)+1/8 ≤ (b i : ℝ)*t ∧ (b i : ℝ)*t ≤ q i+7/8) :
    ∃ tau : ℚ, r ≤ (tau : ℝ) ∧ (tau : ℝ) < 1 ∧
      (∀ s : ℝ, 0 ≤ s → s ≤ (tau : ℝ) → ∃ t : ℝ, ∀ i ∈ S,
        (q i : ℝ)+1/8 ≤ ((a i : ℝ)+s*((b i : ℝ)-a i))*t ∧
          ((a i : ℝ)+s*((b i : ℝ)-a i))*t ≤ q i+7/8) ∧
      ∃ p : ι → ℤ, ∃ e : ℝ, 0 < e ∧ ∀ h : ℝ, 0 ≤ h → h ≤ e →
        ∃ t : ℝ, 0 < t ∧ ∀ i ∈ S,
          (p i : ℝ)+1/8 ≤ ((a i : ℝ)+((tau : ℝ)+h)*((b i : ℝ)-a i))*t ∧
            ((a i : ℝ)+((tau : ℝ)+h)*((b i : ℝ)-a i))*t ≤ p i+7/8 := by
  classical
  let A : ι × ι → ℚ := fun p => (8*(q p.2 : ℚ)+7)*a p.1-(8*(q p.1 : ℚ)+1)*a p.2
  let B : ι × ι → ℚ := fun p =>
    (8*(q p.2 : ℚ)+7)*(b p.1-a p.1)-(8*(q p.1 : ℚ)+1)*(b p.2-a p.2)
  have hpos : ∀ s : ℝ, 0 ≤ s → s ≤ 1 → ∀ i ∈ S,
      0 < (a i : ℝ)+s*((b i : ℝ)-a i) := by
    intro s hs hs1 i hi
    rw [show (a i : ℝ)+s*((b i : ℝ)-a i) = (1-s)*(a i : ℝ)+s*(b i : ℝ) by ring]
    by_cases hz : s = 0
    · simpa [hz] using ha i hi
    · exact add_pos_of_nonneg_of_pos (mul_nonneg (sub_nonneg.mpr hs1) (ha i hi).le)
        (mul_pos (lt_of_le_of_ne hs (Ne.symm hz)) (hb i hi))
  have hiff : ∀ s : ℝ, 0 ≤ s → s ≤ 1 →
      ((∃ t : ℝ, ∀ i ∈ S,
        (q i : ℝ)+1/8 ≤ ((a i : ℝ)+s*((b i : ℝ)-a i))*t ∧
          ((a i : ℝ)+s*((b i : ℝ)-a i))*t ≤ q i+7/8) ↔
      ∀ p ∈ S ×ˢ S, 0 ≤ (A p : ℝ)+s*(B p : ℝ)) := by
    intro s hs hs1
    have hw := WindowPinch.lap_windows_iff S hS
      (fun i => (a i : ℝ)+s*((b i : ℝ)-a i)) (fun i => (q i : ℤ)) (hpos s hs hs1)
    simp only [Int.cast_natCast] at hw
    rw [hw]
    constructor
    · intro h p hp
      obtain ⟨hi, hj⟩ := Finset.mem_product.mp hp
      have hh := h p.1 hi p.2 hj
      dsimp [A, B]
      push_cast
      nlinarith
    · intro h i hi j hj
      have hh := h (i,j) (Finset.mem_product.mpr ⟨hi,hj⟩)
      dsimp [A, B] at hh
      push_cast at hh
      nlinarith
  have hzero := (hiff 0 (by norm_num) (by norm_num)).mp (by simpa using hstart)
  have hR := (hiff r hr.le hr1).mp hin
  have hbad : ∃ p ∈ S ×ˢ S, (A p : ℝ)+(B p : ℝ) < 0 := by
    have hh : ¬ ∀ p ∈ S ×ˢ S, 0 ≤ (A p : ℝ)+(B p : ℝ) := by
      intro hh
      apply hfail
      have hw := (hiff 1 (by norm_num) (by norm_num)).mpr (by simpa using hh)
      simpa using hw
    push_neg at hh
    exact hh
  obtain ⟨tau, hrt, ht1, hbefore, _⟩ := rational_first_loss (S ×ˢ S) A B hr
    (by simpa using hzero) hR hbad
  have ht0 : 0 < (tau : ℝ) := hr.trans_le hrt
  have hold : ∀ s : ℝ, 0 ≤ s → s ≤ (tau : ℝ) → ∃ t : ℝ, ∀ i ∈ S,
      (q i : ℝ)+1/8 ≤ ((a i : ℝ)+s*((b i : ℝ)-a i))*t ∧
        ((a i : ℝ)+s*((b i : ℝ)-a i))*t ≤ q i+7/8 := by
    intro s hs hst
    exact (hiff s hs (hst.trans ht1.le)).mpr (hbefore s hs hst)
  let d : ι → ℚ := fun i => a i+tau*(b i-a i)
  have hd : ∀ i ∈ S, 0 < (d i : ℝ) := by
    intro i hi
    simpa [d] using hpos tau ht0.le ht1.le i hi
  have hearlier : ∀ i, (d i : ℝ)-(tau : ℝ)*((b i : ℝ)-a i) = a i := by
    intro i
    simp [d]
  obtain ⟨p, e, he, hw⟩ := IncomingWindow.replacement_of_incoming S hS d
    (fun i => (b i : ℝ)-a i) q hd ht0
    (by simpa only [hearlier] using ha)
    (by simpa only [hearlier] using hstart)
    (by simpa [d] using hold tau ht0.le le_rfl)
  refine ⟨tau, hrt, ht1, hold, p, e, he, ?_⟩
  intro h hh heh
  obtain ⟨t, ht, hw⟩ := hw h hh heh
  refine ⟨t, ht, ?_⟩
  intro i hi
  have hwi := hw i hi
  have heq : (d i : ℝ)+h*((b i : ℝ)-a i) =
      (a i : ℝ)+((tau : ℝ)+h)*((b i : ℝ)-a i) := by
    dsimp [d]
    push_cast
    ring
  rwa [heq] at hwi

end LRC.MaximalWindowTransport
