import LonelyRunner.LRC.Spec.MirrorN
import LonelyRunner.LRC.Spec.WindowTwoN

/-!
# Order six, BHK §8 (`v₃ ≤ 3 v₁`) inside the framework: windows and flank openings

2026-09-24.  BHK's §8 argues by contradiction: if no lonely time exists, certain gaps must lie
inside one runner's blocked zone, and the resulting inequalities are inconsistent.  In the
framework each such step is a **window and a flank opening** (Theorem 9):

* a window `[A, B]` on which four runners sit inside known clear laps (`clear_of_lap`);
* the fifth runner, the flank, either is clear somewhere in the window — at `A`, or at its own
  opening `(k + 1/6)/x` — and that instant is lonely, or the whole window sits inside one of
  its blocked zones `((k − 1/6)/x, (k + 1/6)/x)` (`window_or_inside`).

The second outcome is exactly BHK's inclusion, and it yields BHK's whole-number inequalities.  The
instants are named; nothing is assumed about there being none.

Everything here is proved; no `sorry`, no `native_decide`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

namespace LRC.OrderSixN

open MomentIterationN LRC.SpecN ConstructionN

theorem circDist_sixth_add_int (k : ℤ) : circDist ((k : ℝ) + 1 / 6) = 1 / 6 := by
  rw [add_comm, circDist_add_int]
  unfold circDist
  rw [Int.fract_eq_self.mpr ⟨by norm_num, by norm_num⟩]
  norm_num

/-- **A runner inside one clear lap.**  If `d·A ≥ m + 1/6` and `d·B ≤ m + 5/6`, the runner is clear
at `1/6` throughout `[A, B]`. -/
theorem clear_of_lap {d A B t : ℝ} (hd : 0 ≤ d) (m : ℤ) (hA : (m : ℝ) + 1 / 6 ≤ d * A)
    (hB : d * B ≤ (m : ℝ) + 5 / 6) (h1 : A ≤ t) (h2 : t ≤ B) : 1 / 6 ≤ circDist (d * t) := by
  have e1 : d * A ≤ d * t := mul_le_mul_of_nonneg_left h1 hd
  have e2 : d * t ≤ d * B := mul_le_mul_of_nonneg_left h2 hd
  have hfl : ⌊d * t⌋ = m := by
    rw [Int.floor_eq_iff]; constructor <;> linarith
  unfold circDist
  have hfr : Int.fract (d * t) = d * t - m := by rw [Int.fract, hfl]
  rw [hfr]
  refine le_min ?_ ?_ <;> linarith

/-- **Window or inside (the framework's reading of a BHK inclusion).**  Let a property `P` hold
throughout `[A, B]`, and let `x > 0` be a flank.  Either some instant of the window — `A`, or the
flank's opening `(k + 1/6)/x` — has `P` and the flank clear, or the whole window sits inside one
blocked zone of the flank. -/
theorem window_or_inside {x A B : ℝ} (hx : 0 < x) (hAB : A ≤ B) (P : ℝ → Prop)
    (hP : ∀ t, A ≤ t → t ≤ B → P t) :
    (∃ t, A ≤ t ∧ t ≤ B ∧ P t ∧ 1 / 6 ≤ circDist (x * t)) ∨
      ∃ k : ℤ, (k : ℝ) - 1 / 6 < x * A ∧ x * B < (k : ℝ) + 1 / 6 := by
  by_cases hA : 1 / 6 ≤ circDist (x * A)
  · exact Or.inl ⟨A, le_rfl, hAB, hP A le_rfl hAB, hA⟩
  push Not at hA
  obtain ⟨K, hK⟩ := circDist_eq_abs_sub_some_int (x * A)
  rw [hK] at hA
  have hK1 := abs_lt.mp hA
  by_cases hB : x * B < (K : ℝ) + 1 / 6
  · exact Or.inr ⟨K, by linarith [hK1.1], hB⟩
  push Not at hB
  -- the flank's opening lies in the window
  set t := ((K : ℝ) + 1 / 6) / x with ht
  have hxt : x * t = (K : ℝ) + 1 / 6 := by rw [ht]; field_simp
  have hAt : A ≤ t := by rw [ht, le_div_iff₀ hx]; linarith [hK1.2]
  have htB : t ≤ B := by rw [ht, div_le_iff₀ hx]; linarith
  refine Or.inl ⟨t, hAt, htB, hP t hAt htB, ?_⟩
  rw [hxt, circDist_sixth_add_int]

/-- Lonely at `1/6`, written out. -/
def Lonely6 (v1 v2 v3 v4 v5 : ℕ) (t : ℝ) : Prop :=
  1 / 6 ≤ circDist ((v1 : ℝ) * t) ∧ 1 / 6 ≤ circDist ((v2 : ℝ) * t) ∧
    1 / 6 ≤ circDist ((v3 : ℝ) * t) ∧ 1 / 6 ≤ circDist ((v4 : ℝ) * t) ∧
    1 / 6 ≤ circDist ((v5 : ℝ) * t)

/-! ## §8.2.1: `7 v₃ ≤ 5 v₄` and `5 v₁ < v₄` -/

/-- **§8.2.1.**  With `v₃ ≤ 3 v₁`, `7 v₃ ≤ 5 v₄`, `5 v₁ < v₄` and `v₄ < 2 v₃`: in the window
`[7/(6 v₄), 5/(6 v₃)]` runners 1–3 are in their first clear lap and runner 4 in its second, so the
flank `v₅` is clear there — at the window's start or at its own opening — and that instant is
lonely.  (BHK's inclusion would put the window inside one blocked zone of `v₅`, which the
whole-number kernel rules out.) -/
theorem lonely_8_2_1 {v1 v2 v3 v4 v5 : ℕ} (h0 : 0 < v1) (h12 : v1 < v2) (h23 : v2 < v3)
    (h34 : v3 < v4) (h45 : v4 < v5)
    (hlarge : v3 ≤ 3 * v1) (h82 : 7 * v3 ≤ 5 * v4) (h821 : 5 * v1 < v4) (h42 : v4 < 2 * v3) :
    ∃ t : ℝ, 0 < t ∧ Lonely6 v1 v2 v3 v4 v5 t := by
  have r0 : (0 : ℝ) < v1 := by exact_mod_cast h0
  have r12 : (v1 : ℝ) < v2 := by exact_mod_cast h12
  have r23 : (v2 : ℝ) < v3 := by exact_mod_cast h23
  have r34 : (v3 : ℝ) < v4 := by exact_mod_cast h34
  have r45 : (v4 : ℝ) < v5 := by exact_mod_cast h45
  have rl : (v3 : ℝ) ≤ 3 * v1 := by exact_mod_cast hlarge
  have r82 : 7 * (v3 : ℝ) ≤ 5 * v4 := by exact_mod_cast h82
  have r42 : (v4 : ℝ) < 2 * v3 := by exact_mod_cast h42
  have p3 : (0 : ℝ) < v3 := by linarith
  have p4 : (0 : ℝ) < v4 := by linarith
  have p5 : (0 : ℝ) < v5 := by linarith
  set A : ℝ := 7 / (6 * v4) with hA
  set B : ℝ := 5 / (6 * v3) with hB
  have hAB : A ≤ B := by rw [hA, hB, div_le_div_iff₀ (by positivity) (by positivity)]; linarith
  -- runners 1–3 in lap 0, runner 4 in lap 1
  have lap0 : ∀ d : ℝ, (v1 : ℝ) ≤ d → d ≤ v3 → ∀ t, A ≤ t → t ≤ B → 1 / 6 ≤ circDist (d * t) := by
    intro d hd1 hd3 t h1 h2
    refine clear_of_lap (by linarith) 0 ?_ ?_ h1 h2
    · rw [hA]; push_cast
      rw [zero_add, show d * (7 / (6 * (v4 : ℝ))) = 7 * d / (6 * v4) by ring,
        le_div_iff₀ (by positivity)]
      nlinarith
    · rw [hB]; push_cast
      rw [zero_add, show d * (5 / (6 * (v3 : ℝ))) = 5 * d / (6 * v3) by ring,
        div_le_iff₀ (by positivity)]
      nlinarith
  have lap4 : ∀ t, A ≤ t → t ≤ B → 1 / 6 ≤ circDist ((v4 : ℝ) * t) := by
    intro t h1 h2
    refine clear_of_lap (by linarith) 1 ?_ ?_ h1 h2
    · rw [hA]; push_cast
      rw [show (v4 : ℝ) * (7 / (6 * (v4 : ℝ))) = 7 / 6 by field_simp]; norm_num
    · rw [hB]; push_cast
      rw [show (v4 : ℝ) * (5 / (6 * (v3 : ℝ))) = 5 * v4 / (6 * v3) by ring,
        div_le_iff₀ (by positivity)]
      nlinarith
  rcases window_or_inside p5 hAB
      (fun t => 1 / 6 ≤ circDist ((v1 : ℝ) * t) ∧ 1 / 6 ≤ circDist ((v2 : ℝ) * t) ∧
        1 / 6 ≤ circDist ((v3 : ℝ) * t) ∧ 1 / 6 ≤ circDist ((v4 : ℝ) * t))
      (fun t h1 h2 => ⟨lap0 v1 le_rfl (by linarith) t h1 h2, lap0 v2 (by linarith) (by linarith) t h1 h2,
        lap0 v3 (by linarith) le_rfl t h1 h2, lap4 t h1 h2⟩) with
    ⟨t, h1, _, ⟨c1, c2, c3, c4⟩, c5⟩ | ⟨k, hkA, hkB⟩
  · have ht : 0 < t := lt_of_lt_of_le (by rw [hA]; positivity) h1
    exact ⟨t, ht, c1, c2, c3, c4, c5⟩
  · -- the window inside one blocked zone of `v₅`: BHK's `j`-conditions, and the kernel
    exfalso
    rw [hA, show (v5 : ℝ) * (7 / (6 * (v4 : ℝ))) = 7 * v5 / (6 * v4) by ring,
      lt_div_iff₀ (by positivity)] at hkA
    rw [hB, show (v5 : ℝ) * (5 / (6 * (v3 : ℝ))) = 5 * v5 / (6 * v3) by ring,
      div_lt_iff₀ (by positivity)] at hkB
    have hjL : (6 * k - 1) * (v4 : ℤ) < 7 * (v5 : ℤ) := by
      have : (6 * (k : ℝ) - 1) * v4 < 7 * v5 := by nlinarith
      exact_mod_cast this
    have hjR : 5 * (v5 : ℤ) < (6 * k + 1) * (v3 : ℤ) := by
      have : 5 * (v5 : ℝ) < (6 * (k : ℝ) + 1) * v3 := by nlinarith
      exact_mod_cast this
    have z1 : (v1 : ℤ) > 0 := by exact_mod_cast h0
    have zl : (v3 : ℤ) ≤ 3 * v1 := by exact_mod_cast hlarge
    have z82 : 7 * (v3 : ℤ) ≤ 5 * v4 := by exact_mod_cast h82
    have z821 : 5 * (v1 : ℤ) < v4 := by exact_mod_cast h821
    have z45 : (v4 : ℤ) < v5 := by exact_mod_cast h45
    have z3 : (0 : ℤ) < v3 := by exact_mod_cast (show 0 < v3 by omega)
    have hk2 : 2 ≤ k := by nlinarith
    have h6m : 0 < 6 * k - 1 := by linarith
    have h6p : 0 < 6 * k + 1 := by linarith
    have sA : (6 * k - 1) * (5 * (v1 : ℤ)) < (6 * k - 1) * v4 := mul_lt_mul_of_pos_left z821 h6m
    have sB : (6 * k + 1) * (v3 : ℤ) ≤ (6 * k + 1) * (3 * v1) :=
      mul_le_mul_of_nonneg_left zl h6p.le
    nlinarith

/-! ## Windows in whole-number form -/

/-- A whole-number runner `d` in clear lap `m` across the window `[p/(6a), q/(6b)]`. -/
theorem clear_window {d a b p q : ℕ} (ha : 0 < a) (hb : 0 < b) (m : ℤ)
    (h1 : (6 * m + 1) * (a : ℤ) ≤ (d : ℤ) * p) (h2 : (d : ℤ) * q ≤ (6 * m + 5) * (b : ℤ))
    {t : ℝ} (ht1 : (p : ℝ) / (6 * a) ≤ t) (ht2 : t ≤ (q : ℝ) / (6 * b)) :
    1 / 6 ≤ circDist ((d : ℝ) * t) := by
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  refine clear_of_lap (Nat.cast_nonneg d) m ?_ ?_ ht1 ht2
  · have h1' : (6 * (m : ℝ) + 1) * a ≤ d * p := by exact_mod_cast h1
    rw [show (d : ℝ) * (p / (6 * a)) = d * p / (6 * a) by ring, le_div_iff₀ (by positivity)]
    linarith
  · have h2' : (d : ℝ) * q ≤ (6 * (m : ℝ) + 5) * b := by exact_mod_cast h2
    rw [show (d : ℝ) * (q / (6 * b)) = d * q / (6 * b) by ring, div_le_iff₀ (by positivity)]
    linarith

/-- **Flank on a window, whole-number form.**  On `[p/(6a), q/(6b)]`, where `P` holds throughout,
either the flank `x` is clear at a named instant with `P`, or the window sits inside one blocked
zone of `x`: `(6k − 1)·a < x·p` and `x·q < (6k + 1)·b`. -/
theorem flank_window {x a b p q : ℕ} (hx : 0 < x) (ha : 0 < a) (hb : 0 < b)
    (hAB : (p : ℤ) * b ≤ (q : ℤ) * a) (P : ℝ → Prop)
    (hP : ∀ t, (p : ℝ) / (6 * a) ≤ t → t ≤ (q : ℝ) / (6 * b) → P t) :
    (∃ t, (p : ℝ) / (6 * a) ≤ t ∧ t ≤ (q : ℝ) / (6 * b) ∧ P t ∧ 1 / 6 ≤ circDist ((x : ℝ) * t)) ∨
      ∃ k : ℤ, (6 * k - 1) * (a : ℤ) < (x : ℤ) * p ∧ (x : ℤ) * q < (6 * k + 1) * (b : ℤ) := by
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  have hx' : (0 : ℝ) < x := by exact_mod_cast hx
  have hAB' : (p : ℝ) / (6 * a) ≤ (q : ℝ) / (6 * b) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : (p : ℝ) * b ≤ q * a := by exact_mod_cast hAB
    nlinarith
  rcases window_or_inside hx' hAB' P hP with h | ⟨k, hk1, hk2⟩
  · exact Or.inl h
  · refine Or.inr ⟨k, ?_, ?_⟩
    · rw [show (x : ℝ) * (p / (6 * a)) = x * p / (6 * a) by ring, lt_div_iff₀ (by positivity)] at hk1
      have : (6 * (k : ℝ) - 1) * a < x * p := by linarith
      exact_mod_cast this
    · rw [show (x : ℝ) * (q / (6 * b)) = x * q / (6 * b) by ring, div_lt_iff₀ (by positivity)] at hk2
      have : (x : ℝ) * q < (6 * (k : ℝ) + 1) * b := by linarith
      exact_mod_cast this

theorem window_pos {p a : ℕ} (hp : 0 < p) (ha : 0 < a) {t : ℝ} (h : (p : ℝ) / (6 * a) ≤ t) :
    0 < t := by
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  exact lt_of_lt_of_le (by positivity) h

/-! ## §8.2.2: `7 v₃ ≤ 5 v₄` and `v₄ ≤ 5 v₁` -/

set_option maxHeartbeats 2000000 in
/-- **§8.2.2.**  Four named instants: the 1234-window and the window `[7/(6v₄), 5/(6v₃)]` with
flank `v₅`, then the points `7/(6v₃)` and `21/(12v₃)` with flank `v₂`.  One of them is lonely:
otherwise the first two force `j = 2, k = 3`, and the points force `5v₃ < 7v₂` and `3v₂ < 2v₃`,
which cannot both hold. -/
theorem lonely_8_2_2 {v1 v2 v3 v4 v5 : ℕ} (h0 : 0 < v1) (h12 : v1 < v2) (h23 : v2 < v3)
    (h34 : v3 < v4) (h45 : v4 < v5)
    (hlarge : v3 ≤ 3 * v1) (h82 : 7 * v3 ≤ 5 * v4) (h822 : v4 ≤ 5 * v1) (h42 : v4 < 2 * v3) :
    ∃ t : ℝ, 0 < t ∧ Lonely6 v1 v2 v3 v4 v5 t := by
  have p1 : 0 < v1 := h0
  have p2 : 0 < v2 := by omega
  have p3 : 0 < v3 := by omega
  have p4 : 0 < v4 := by omega
  have p5 : 0 < v5 := by omega
  have z0 : (0 : ℤ) < v1 := by exact_mod_cast h0
  have z12 : (v1 : ℤ) < v2 := by exact_mod_cast h12
  have z23 : (v2 : ℤ) < v3 := by exact_mod_cast h23
  have z34 : (v3 : ℤ) < v4 := by exact_mod_cast h34
  have z45 : (v4 : ℤ) < v5 := by exact_mod_cast h45
  have zl : (v3 : ℤ) ≤ 3 * v1 := by exact_mod_cast hlarge
  have z82 : 7 * (v3 : ℤ) ≤ 5 * v4 := by exact_mod_cast h82
  have z822 : (v4 : ℤ) ≤ 5 * v1 := by exact_mod_cast h822
  have z42 : (v4 : ℤ) < 2 * v3 := by exact_mod_cast h42
  -- step L: the 1234-window `[1/(6v₁), 5/(6v₄)]`, flank `v₅`
  rcases flank_window (x := v5) (a := v1) (b := v4) (p := 1) (q := 5) p5 p1 p4 (by push_cast; linarith)
      (fun t => 1 / 6 ≤ circDist ((v1 : ℝ) * t) ∧ 1 / 6 ≤ circDist ((v2 : ℝ) * t) ∧
        1 / 6 ≤ circDist ((v3 : ℝ) * t) ∧ 1 / 6 ≤ circDist ((v4 : ℝ) * t))
      (fun t h1 h2 => ⟨clear_window p1 p4 0 (by push_cast; linarith) (by push_cast; linarith) h1 h2,
        clear_window p1 p4 0 (by push_cast; linarith) (by push_cast; linarith) h1 h2,
        clear_window p1 p4 0 (by push_cast; linarith) (by push_cast; linarith) h1 h2,
        clear_window p1 p4 0 (by push_cast; linarith) (by push_cast; linarith) h1 h2⟩) with
    ⟨t, h1, _, ⟨c1, c2, c3, c4⟩, c5⟩ | ⟨j, hjL, hjR⟩
  · exact ⟨t, window_pos one_pos p1 h1, c1, c2, c3, c4, c5⟩
  push_cast at hjL hjR
  -- step R: the window `[7/(6v₄), 5/(6v₃)]`, flank `v₅`
  rcases flank_window (x := v5) (a := v4) (b := v3) (p := 7) (q := 5) p5 p4 p3 (by push_cast; linarith)
      (fun t => 1 / 6 ≤ circDist ((v1 : ℝ) * t) ∧ 1 / 6 ≤ circDist ((v2 : ℝ) * t) ∧
        1 / 6 ≤ circDist ((v3 : ℝ) * t) ∧ 1 / 6 ≤ circDist ((v4 : ℝ) * t))
      (fun t h1 h2 => ⟨clear_window p4 p3 0 (by push_cast; linarith) (by push_cast; linarith) h1 h2,
        clear_window p4 p3 0 (by push_cast; linarith) (by push_cast; linarith) h1 h2,
        clear_window p4 p3 0 (by push_cast; linarith) (by push_cast; linarith) h1 h2,
        clear_window p4 p3 1 (by push_cast; linarith) (by push_cast; linarith) h1 h2⟩) with
    ⟨t, h1, _, ⟨c1, c2, c3, c4⟩, c5⟩ | ⟨k, hkL, hkR⟩
  · exact ⟨t, window_pos (by norm_num) p4 h1, c1, c2, c3, c4, c5⟩
  push_cast at hkL hkR
  -- the whole-number kernel forces `j = 2`, `k = 3`
  have hj1 : 1 ≤ j := by
    by_contra hc; push Not at hc
    have : (6 * j + 1) * (v4 : ℤ) ≤ 1 * v4 := mul_le_mul_of_nonneg_right (by omega) (by omega)
    nlinarith
  have hk1 : 1 ≤ k := by
    by_contra hc; push Not at hc
    have : (6 * k + 1) * (v3 : ℤ) ≤ 1 * v3 := mul_le_mul_of_nonneg_right (by omega) (by omega)
    nlinarith
  have hA : 30 * k < 42 * j + 12 := by
    by_contra hc; push Not at hc
    have : (42 * j + 12) * (v4 : ℤ) ≤ 30 * k * v4 := mul_le_mul_of_nonneg_right hc (by omega)
    nlinarith
  have hB : 15 * j < 9 * k + 4 := by
    have e : (6 * k + 1) * (v3 : ℤ) ≤ (6 * k + 1) * (3 * v1) :=
      mul_le_mul_of_nonneg_left zl (by omega)
    by_contra hc; push Not at hc
    have : (9 * k + 4) * (v1 : ℤ) ≤ 15 * j * v1 := mul_le_mul_of_nonneg_right hc (by omega)
    nlinarith
  have hj2 : j = 2 := by omega
  have hk3 : k = 3 := by omega
  subst hj2 hk3
  -- (75): `11v₁ < v₅`, `17v₄ < 7v₅`, `5v₅ < 19v₃`
  have e75a : 11 * (v1 : ℤ) < v5 := by linarith
  have e75c : 17 * (v4 : ℤ) < 7 * v5 := by linarith
  have e75d : 5 * (v5 : ℤ) < 19 * v3 := by linarith
  -- point a: `t = 7/(6v₃)`, flank `v₂`
  rcases flank_window (x := v2) (a := v3) (b := v3) (p := 7) (q := 7) p2 p3 p3 le_rfl
      (fun t => 1 / 6 ≤ circDist ((v1 : ℝ) * t) ∧ 1 / 6 ≤ circDist ((v3 : ℝ) * t) ∧
        1 / 6 ≤ circDist ((v4 : ℝ) * t) ∧ 1 / 6 ≤ circDist ((v5 : ℝ) * t))
      (fun t h1 h2 => ⟨clear_window p3 p3 0 (by push_cast; linarith) (by push_cast; linarith) h1 h2,
        clear_window p3 p3 1 (by push_cast; linarith) (by push_cast; linarith) h1 h2,
        clear_window p3 p3 1 (by push_cast; linarith) (by push_cast; linarith) h1 h2,
        clear_window p3 p3 4 (by push_cast; linarith) (by push_cast; linarith) h1 h2⟩) with
    ⟨t, h1, _, ⟨c1, c3, c4, c5⟩, c2⟩ | ⟨ka, hkaL, hkaR⟩
  · exact ⟨t, window_pos (by norm_num) p3 h1, c1, c2, c3, c4, c5⟩
  push_cast at hkaL hkaR
  have hka : ka = 1 := by
    rcases lt_trichotomy ka 1 with h | h | h
    · have : ka ≤ 0 := by omega
      nlinarith
    · exact h
    · have : 2 ≤ ka := by omega
      nlinarith
  subst hka
  -- point b: `t = 21/(12v₃) = 21/(6·(2v₃))`, flank `v₂`
  have p23 : 0 < 2 * v3 := by omega
  rcases flank_window (x := v2) (a := 2 * v3) (b := 2 * v3) (p := 21) (q := 21) p2 p23 p23 le_rfl
      (fun t => 1 / 6 ≤ circDist ((v1 : ℝ) * t) ∧ 1 / 6 ≤ circDist ((v3 : ℝ) * t) ∧
        1 / 6 ≤ circDist ((v4 : ℝ) * t) ∧ 1 / 6 ≤ circDist ((v5 : ℝ) * t))
      (fun t h1 h2 => ⟨clear_window p23 p23 0 (by push_cast; linarith) (by push_cast; linarith) h1 h2,
        clear_window p23 p23 1 (by push_cast; linarith) (by push_cast; linarith) h1 h2,
        clear_window p23 p23 2 (by push_cast; linarith) (by push_cast; linarith) h1 h2,
        clear_window p23 p23 6 (by push_cast; linarith) (by push_cast; linarith) h1 h2⟩) with
    ⟨t, h1, _, ⟨c1, c3, c4, c5⟩, c2⟩ | ⟨kb, hkbL, hkbR⟩
  · exact ⟨t, window_pos (by norm_num) p23 h1, c1, c2, c3, c4, c5⟩
  push_cast at hkbL hkbR
  -- kernel: `5v₃ < 7v₂` and `3v₂ < 2v₃` are incompatible
  exfalso
  rcases lt_trichotomy kb 1 with h | h | h
  · have : kb ≤ 0 := by omega
    nlinarith
  · subst h; linarith
  · have : 2 ≤ kb := by omega
    nlinarith

/-! ## The 123-window and the two-flank rule: `v₄ < 2 v₃` -/

/-- **The 123-window.**  With `v₃ ≤ 3 v₁`, runners 1–3 are in their first clear lap across
`[1/(6v₁), 5/(6v₃)]`.  If `2 v₃ ≤ v₄` the window is at least `2/(3v₄)` long, and the two-flank
window rule (`two_flank_window`, BHK Lemma 4) names a lonely instant in it.  Otherwise
`v₄ < 2 v₃`. -/
theorem lonely_or_v4_lt_2v3 {v1 v2 v3 v4 v5 : ℕ} (h0 : 0 < v1) (h12 : v1 < v2) (h23 : v2 < v3)
    (h34 : v3 < v4) (h45 : v4 < v5) (hlarge : v3 ≤ 3 * v1) :
    (∃ t : ℝ, 0 < t ∧ Lonely6 v1 v2 v3 v4 v5 t) ∨ v4 < 2 * v3 := by
  by_cases h : 2 * v3 ≤ v4
  · left
    have p1 : 0 < v1 := h0
    have p3 : 0 < v3 := by omega
    have r1 : (0 : ℝ) < v1 := by exact_mod_cast h0
    have r3 : (0 : ℝ) < v3 := by exact_mod_cast p3
    have r4 : (0 : ℝ) < v4 := by exact_mod_cast (show 0 < v4 by omega)
    have r45 : (v4 : ℝ) < v5 := by exact_mod_cast h45
    have rl : (v3 : ℝ) ≤ 3 * v1 := by exact_mod_cast hlarge
    have rh : 2 * (v3 : ℝ) ≤ v4 := by exact_mod_cast h
    set a : ℝ := ((1 : ℕ) : ℝ) / (6 * v1) with ha
    set L : ℝ := ((5 : ℕ) : ℝ) / (6 * v3) - a with hL
    have hLlen : 2 / (3 * (v4 : ℝ)) ≤ L := by
      have e1 : a ≤ 1 / (2 * v3) := by
        rw [ha, div_le_div_iff₀ (by positivity) (by positivity)]; push_cast; linarith
      have e2 : 2 / (3 * (v4 : ℝ)) ≤ 1 / (3 * v3) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]; linarith
      have e3 : ((5 : ℕ) : ℝ) / (6 * v3) - 1 / (2 * v3) = 1 / (3 * v3) := by
        push_cast; field_simp; ring
      rw [hL]; linarith
    obtain ⟨t, h1, h2, c4, c5, -⟩ := two_flank_window r4 r45 a hLlen
    have hb : a + L = ((5 : ℕ) : ℝ) / (6 * v3) := by rw [hL]; ring
    rw [hb] at h2
    have cl : ∀ d : ℕ, v1 ≤ d → d ≤ v3 → 1 / 6 ≤ circDist ((d : ℝ) * t) := by
      intro d hd1 hd3
      exact clear_window (p := 1) (q := 5) p1 p3 0 (by push_cast; omega) (by push_cast; omega) h1 h2
    have ht : 0 < t := window_pos one_pos p1 h1
    refine ⟨t, ht, cl v1 le_rfl (by omega), cl v2 (by omega) (by omega), cl v3 (by omega) le_rfl,
      by simpa [one_div] using c4, by simpa [one_div] using c5⟩
  · right; omega

/-! ## §8.2 assembled -/

/-- **§8.2** (`v₃ ≤ 3 v₁`, `7 v₃ ≤ 5 v₄`): lonely at `1/6`, at a named instant. -/
theorem lonely_8_2 {v1 v2 v3 v4 v5 : ℕ} (h0 : 0 < v1) (h12 : v1 < v2) (h23 : v2 < v3)
    (h34 : v3 < v4) (h45 : v4 < v5) (hlarge : v3 ≤ 3 * v1) (h82 : 7 * v3 ≤ 5 * v4) :
    ∃ t : ℝ, 0 < t ∧ Lonely6 v1 v2 v3 v4 v5 t := by
  rcases lonely_or_v4_lt_2v3 h0 h12 h23 h34 h45 hlarge with h | h42
  · exact h
  by_cases h821 : 5 * v1 < v4
  · exact lonely_8_2_1 h0 h12 h23 h34 h45 hlarge h82 h821 h42
  · exact lonely_8_2_2 h0 h12 h23 h34 h45 hlarge h82 (by omega) h42

/-! ## One step: four runners in named laps, one flank -/

/-- **One BHK step in framework form.**  Four runners `d₁ … d₄` sit in named clear laps across
`[p/(6a), q/(6b)]`.  Either the flank `x` is clear at a named instant there (lonely for all five),
or the window sits inside one blocked zone of `x`. -/
theorem step4 {x a b p q d1 d2 d3 d4 : ℕ} (hx : 0 < x) (ha : 0 < a) (hb : 0 < b) (hp : 0 < p)
    (hAB : (p : ℤ) * b ≤ (q : ℤ) * a) (m1 m2 m3 m4 : ℤ)
    (l1 : (6 * m1 + 1) * (a : ℤ) ≤ (d1 : ℤ) * p) (u1 : (d1 : ℤ) * q ≤ (6 * m1 + 5) * (b : ℤ))
    (l2 : (6 * m2 + 1) * (a : ℤ) ≤ (d2 : ℤ) * p) (u2 : (d2 : ℤ) * q ≤ (6 * m2 + 5) * (b : ℤ))
    (l3 : (6 * m3 + 1) * (a : ℤ) ≤ (d3 : ℤ) * p) (u3 : (d3 : ℤ) * q ≤ (6 * m3 + 5) * (b : ℤ))
    (l4 : (6 * m4 + 1) * (a : ℤ) ≤ (d4 : ℤ) * p) (u4 : (d4 : ℤ) * q ≤ (6 * m4 + 5) * (b : ℤ)) :
    (∃ t : ℝ, 0 < t ∧ 1 / 6 ≤ circDist ((d1 : ℝ) * t) ∧ 1 / 6 ≤ circDist ((d2 : ℝ) * t) ∧
      1 / 6 ≤ circDist ((d3 : ℝ) * t) ∧ 1 / 6 ≤ circDist ((d4 : ℝ) * t) ∧
      1 / 6 ≤ circDist ((x : ℝ) * t)) ∨
      ∃ k : ℤ, (6 * k - 1) * (a : ℤ) < (x : ℤ) * p ∧ (x : ℤ) * q < (6 * k + 1) * (b : ℤ) := by
  rcases flank_window hx ha hb hAB
      (fun t => 1 / 6 ≤ circDist ((d1 : ℝ) * t) ∧ 1 / 6 ≤ circDist ((d2 : ℝ) * t) ∧
        1 / 6 ≤ circDist ((d3 : ℝ) * t) ∧ 1 / 6 ≤ circDist ((d4 : ℝ) * t))
      (fun t h1 h2 => ⟨clear_window ha hb m1 l1 u1 h1 h2, clear_window ha hb m2 l2 u2 h1 h2,
        clear_window ha hb m3 l3 u3 h1 h2, clear_window ha hb m4 l4 u4 h1 h2⟩) with
    ⟨t, h1, _, ⟨c1, c2, c3, c4⟩, c5⟩ | h
  · exact Or.inl ⟨t, window_pos hp ha h1, c1, c2, c3, c4, c5⟩
  · exact Or.inr h

/-! ## §8.1: `5 v₄ < 7 v₃` -/

section S81

variable {v1 v2 v3 v4 v5 : ℕ}

/-- **§8.1, step 1: the 1234-window, flank `v₅`.**  Lonely, or (65): `5v₁ < v₅` and `5v₅ < 7v₄`. -/
theorem s81_step1 (h0 : 0 < v1) (h12 : v1 < v2) (h23 : v2 < v3) (h34 : v3 < v4) (h45 : v4 < v5)
    (hlarge : v3 ≤ 3 * v1) (h81 : 5 * v4 < 7 * v3) :
    (∃ t : ℝ, 0 < t ∧ Lonely6 v1 v2 v3 v4 v5 t) ∨ (5 * v1 < v5 ∧ 5 * v5 < 7 * v4) := by
  have z1 : (0 : ℤ) < v1 := by exact_mod_cast h0
  have z4 : (0 : ℤ) < v4 := by exact_mod_cast (show 0 < v4 by omega)
  have zl : (v3 : ℤ) ≤ 3 * v1 := by exact_mod_cast hlarge
  have z81 : 5 * (v4 : ℤ) < 7 * v3 := by exact_mod_cast h81
  have z12 : (v1 : ℤ) < v2 := by exact_mod_cast h12
  have z23 : (v2 : ℤ) < v3 := by exact_mod_cast h23
  have z34 : (v3 : ℤ) < v4 := by exact_mod_cast h34
  have z45 : (v4 : ℤ) < v5 := by exact_mod_cast h45
  rcases step4 (x := v5) (a := v1) (b := v4) (p := 1) (q := 5) (d1 := v1) (d2 := v2) (d3 := v3)
      (d4 := v4) (by omega) h0 (by omega) one_pos (by push_cast; linarith) 0 0 0 0
      (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith)
      (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith)
      (by push_cast; linarith) (by push_cast; linarith) with
    ⟨t, ht, c1, c2, c3, c4, c5⟩ | ⟨j, hjL, hjR⟩
  · exact Or.inl ⟨t, ht, c1, c2, c3, c4, c5⟩
  right
  push_cast at hjL hjR
  have hj1 : 1 ≤ j := by
    by_contra hc; push Not at hc
    have : (6 * j + 1) * (v4 : ℤ) ≤ 1 * v4 := mul_le_mul_of_nonneg_right (by omega) z4.le
    nlinarith
  have hpos : 0 < 6 * j + 1 := by omega
  have e1 : (6 * j + 1) * (5 * (v4 : ℤ)) < (6 * j + 1) * (7 * v3) := mul_lt_mul_of_pos_left z81 hpos
  have e2 : (6 * j + 1) * (v3 : ℤ) ≤ (6 * j + 1) * (3 * v1) := mul_le_mul_of_nonneg_left zl hpos.le
  have key : (24 * j - 46) * (v1 : ℤ) < 0 := by nlinarith
  have hj : j = 1 := by
    have : 24 * j - 46 < 0 := by
      by_contra hc; push Not at hc
      nlinarith
    omega
  subst hj
  constructor
  · have : 5 * (v1 : ℤ) < v5 := by linarith
    exact_mod_cast this
  · have : 5 * (v5 : ℤ) < 7 * v4 := by linarith
    exact_mod_cast this

/-- **§8.1, step 2: the 1345-window, flank `v₂`.**  Lonely, or (66) `25v₃ < 39v₂` and (67)
`11v₂ < 7v₄`.  The window starts at the later of `7/(6v₃)` and `13/(6v₅)`. -/
theorem s81_step2 (h0 : 0 < v1) (h12 : v1 < v2) (h23 : v2 < v3) (h34 : v3 < v4) (h45 : v4 < v5)
    (hlarge : v3 ≤ 3 * v1) (h81 : 5 * v4 < 7 * v3) (h65 : 5 * v1 < v5) (h65b : 5 * v5 < 7 * v4) :
    (∃ t : ℝ, 0 < t ∧ Lonely6 v1 v2 v3 v4 v5 t) ∨ (25 * v3 < 39 * v2 ∧ 11 * v2 < 7 * v4) := by
  have z1 : (0 : ℤ) < v1 := by exact_mod_cast h0
  have zl : (v3 : ℤ) ≤ 3 * v1 := by exact_mod_cast hlarge
  have z81 : 5 * (v4 : ℤ) < 7 * v3 := by exact_mod_cast h81
  have z12 : (v1 : ℤ) < v2 := by exact_mod_cast h12
  have z23 : (v2 : ℤ) < v3 := by exact_mod_cast h23
  have z34 : (v3 : ℤ) < v4 := by exact_mod_cast h34
  have z45 : (v4 : ℤ) < v5 := by exact_mod_cast h45
  have z65 : 5 * (v1 : ℤ) < v5 := by exact_mod_cast h65
  have z65b : 5 * (v5 : ℤ) < 7 * v4 := by exact_mod_cast h65b
  have f1 : 11 * (v1 : ℤ) ≤ 5 * v4 := by linarith
  by_cases hM : 13 * v3 ≤ 7 * v5
  · have zM : 13 * (v3 : ℤ) ≤ 7 * v5 := by exact_mod_cast hM
    rcases step4 (x := v2) (a := v3) (b := v4) (p := 7) (q := 11) (d1 := v1) (d2 := v3) (d3 := v4)
        (d4 := v5) (by omega) (by omega) (by omega) (by norm_num) (by push_cast; linarith) 0 1 1 2
        (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith)
        (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith)
        (by push_cast; linarith) (by push_cast; linarith) with
      ⟨t, ht, c1, c3, c4, c5, c2⟩ | ⟨k, hkL, hkR⟩
    · exact Or.inl ⟨t, ht, c1, c2, c3, c4, c5⟩
    right
    push_cast at hkL hkR
    have hk1 : 1 ≤ k := by
      by_contra hc; push Not at hc
      have : (6 * k + 1) * (v4 : ℤ) ≤ 1 * v4 := mul_le_mul_of_nonneg_right (by omega) (by omega)
      nlinarith
    have hk : k = 1 := by
      by_contra hc
      have : 2 ≤ k := by omega
      nlinarith
    subst hk
    constructor
    · have : 25 * (v3 : ℤ) < 39 * v2 := by linarith
      exact_mod_cast this
    · have : 11 * (v2 : ℤ) < 7 * v4 := by linarith
      exact_mod_cast this
  · have zM : 7 * (v5 : ℤ) < 13 * v3 := by push Not at hM; exact_mod_cast hM
    rcases step4 (x := v2) (a := v5) (b := v4) (p := 13) (q := 11) (d1 := v1) (d2 := v3) (d3 := v4)
        (d4 := v5) (by omega) (by omega) (by omega) (by norm_num) (by push_cast; linarith) 0 1 1 2
        (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith)
        (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith)
        (by push_cast; linarith) (by push_cast; linarith) with
      ⟨t, ht, c1, c3, c4, c5, c2⟩ | ⟨k, hkL, hkR⟩
    · exact Or.inl ⟨t, ht, c1, c2, c3, c4, c5⟩
    right
    push_cast at hkL hkR
    have hk1 : 1 ≤ k := by
      by_contra hc; push Not at hc
      have : (6 * k + 1) * (v4 : ℤ) ≤ 1 * v4 := mul_le_mul_of_nonneg_right (by omega) (by omega)
      nlinarith
    have hk : k = 1 := by
      by_contra hc
      have : 2 ≤ k := by omega
      have : 11 * (v5 : ℤ) ≤ (6 * k - 1) * v5 := mul_le_mul_of_nonneg_right (by omega) (by omega)
      nlinarith
    subst hk
    constructor
    · have : 25 * (v3 : ℤ) < 39 * v2 := by linarith
      exact_mod_cast this
    · have : 11 * (v2 : ℤ) < 7 * v4 := by linarith
      exact_mod_cast this

/-- **§8.1.1, step 3: the window `[7/(6v₂), 11/(6v₃)]`, flank `v₅`** (here `13v₂ ≤ 7v₄`, so the
window starts at `7/(6v₂)`).  Lonely, or (68) `11v₅ < 19v₃` and (69) `17v₂ < 7v₅`. -/
theorem s811_step3 (h0 : 0 < v1) (h12 : v1 < v2) (h23 : v2 < v3) (h34 : v3 < v4) (h45 : v4 < v5)
    (hlarge : v3 ≤ 3 * v1) (h81 : 5 * v4 < 7 * v3) (h65 : 5 * v1 < v5) (h65b : 5 * v5 < 7 * v4)
    (h66 : 25 * v3 < 39 * v2) (h811 : 13 * v2 ≤ 7 * v4) :
    (∃ t : ℝ, 0 < t ∧ Lonely6 v1 v2 v3 v4 v5 t) ∨ (11 * v5 < 19 * v3 ∧ 17 * v2 < 7 * v5) := by
  have z1 : (0 : ℤ) < v1 := by exact_mod_cast h0
  have zl : (v3 : ℤ) ≤ 3 * v1 := by exact_mod_cast hlarge
  have z81 : 5 * (v4 : ℤ) < 7 * v3 := by exact_mod_cast h81
  have z12 : (v1 : ℤ) < v2 := by exact_mod_cast h12
  have z23 : (v2 : ℤ) < v3 := by exact_mod_cast h23
  have z34 : (v3 : ℤ) < v4 := by exact_mod_cast h34
  have z45 : (v4 : ℤ) < v5 := by exact_mod_cast h45
  have z65 : 5 * (v1 : ℤ) < v5 := by exact_mod_cast h65
  have z65b : 5 * (v5 : ℤ) < 7 * v4 := by exact_mod_cast h65b
  have z66 : 25 * (v3 : ℤ) < 39 * v2 := by exact_mod_cast h66
  have z811 : 13 * (v2 : ℤ) ≤ 7 * v4 := by exact_mod_cast h811
  have f1 : 11 * (v1 : ℤ) ≤ 5 * v3 := by linarith
  rcases step4 (x := v5) (a := v2) (b := v3) (p := 7) (q := 11) (d1 := v1) (d2 := v2) (d3 := v3)
      (d4 := v4) (by omega) (by omega) (by omega) (by norm_num) (by push_cast; linarith) 0 1 1 2
      (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith)
      (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith)
      (by push_cast; linarith) (by push_cast; linarith) with
    ⟨t, ht, c1, c2, c3, c4, c5⟩ | ⟨k, hkL, hkR⟩
  · exact Or.inl ⟨t, ht, c1, c2, c3, c4, c5⟩
  right
  push_cast at hkL hkR
  have hk3 : 3 ≤ k := by
    by_contra hc; push Not at hc
    have : (6 * k + 1) * (v3 : ℤ) ≤ 13 * v3 := mul_le_mul_of_nonneg_right (by omega) (by omega)
    nlinarith
  have hk : k = 3 := by
    by_contra hc
    have : 4 ≤ k := by omega
    have : 23 * (v2 : ℤ) ≤ (6 * k - 1) * v2 := mul_le_mul_of_nonneg_right (by omega) (by omega)
    nlinarith
  subst hk
  constructor
  · have : 11 * (v5 : ℤ) < 19 * v3 := by linarith
    exact_mod_cast this
  · have : 17 * (v2 : ℤ) < 7 * v5 := by linarith
    exact_mod_cast this

/-- **§8.1.2, step 3: the window `[13/(6v₄), 11/(6v₃)]`, flank `v₅`** (here `7v₄ < 13v₂`).
Lonely, or (68) `11v₅ < 19v₃` and (72) `17v₄ < 13v₅`.  When the window is empty
(`11v₄ < 13v₃`) the two bounds already hold. -/
theorem s812_step3 (h0 : 0 < v1) (h12 : v1 < v2) (h23 : v2 < v3) (h34 : v3 < v4) (h45 : v4 < v5)
    (hlarge : v3 ≤ 3 * v1) (h81 : 5 * v4 < 7 * v3) (h65 : 5 * v1 < v5) (h65b : 5 * v5 < 7 * v4)
    (h66 : 25 * v3 < 39 * v2) (h67 : 11 * v2 < 7 * v4) (h812 : 7 * v4 < 13 * v2) :
    (∃ t : ℝ, 0 < t ∧ Lonely6 v1 v2 v3 v4 v5 t) ∨ (11 * v5 < 19 * v3 ∧ 17 * v4 < 13 * v5) := by
  have z1 : (0 : ℤ) < v1 := by exact_mod_cast h0
  have zl : (v3 : ℤ) ≤ 3 * v1 := by exact_mod_cast hlarge
  have z81 : 5 * (v4 : ℤ) < 7 * v3 := by exact_mod_cast h81
  have z12 : (v1 : ℤ) < v2 := by exact_mod_cast h12
  have z23 : (v2 : ℤ) < v3 := by exact_mod_cast h23
  have z34 : (v3 : ℤ) < v4 := by exact_mod_cast h34
  have z45 : (v4 : ℤ) < v5 := by exact_mod_cast h45
  have z65 : 5 * (v1 : ℤ) < v5 := by exact_mod_cast h65
  have z65b : 5 * (v5 : ℤ) < 7 * v4 := by exact_mod_cast h65b
  have z66 : 25 * (v3 : ℤ) < 39 * v2 := by exact_mod_cast h66
  have z67 : 11 * (v2 : ℤ) < 7 * v4 := by exact_mod_cast h67
  have z812 : 7 * (v4 : ℤ) < 13 * v2 := by exact_mod_cast h812
  have f1 : 11 * (v1 : ℤ) ≤ 5 * v3 := by linarith
  by_cases hE : 13 * v3 ≤ 11 * v4
  · have zE : 13 * (v3 : ℤ) ≤ 11 * v4 := by exact_mod_cast hE
    rcases step4 (x := v5) (a := v4) (b := v3) (p := 13) (q := 11) (d1 := v1) (d2 := v2)
        (d3 := v3) (d4 := v4) (by omega) (by omega) (by omega) (by norm_num)
        (by push_cast; linarith) 0 1 1 2
        (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith)
        (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith)
        (by push_cast; linarith) (by push_cast; linarith) with
      ⟨t, ht, c1, c2, c3, c4, c5⟩ | ⟨k, hkL, hkR⟩
    · exact Or.inl ⟨t, ht, c1, c2, c3, c4, c5⟩
    right
    push_cast at hkL hkR
    have hk3 : 3 ≤ k := by
      by_contra hc; push Not at hc
      have : (6 * k + 1) * (v3 : ℤ) ≤ 13 * v3 := mul_le_mul_of_nonneg_right (by omega) (by omega)
      nlinarith
    have hk : k = 3 := by
      by_contra hc
      have : 4 ≤ k := by omega
      have : 23 * (v4 : ℤ) ≤ (6 * k - 1) * v4 := mul_le_mul_of_nonneg_right (by omega) (by omega)
      nlinarith
    subst hk
    constructor
    · have : 11 * (v5 : ℤ) < 19 * v3 := by linarith
      exact_mod_cast this
    · have : 17 * (v4 : ℤ) < 13 * v5 := by linarith
      exact_mod_cast this
  · -- the window is empty: the bounds hold outright
    have zE : 11 * (v4 : ℤ) < 13 * v3 := by push Not at hE; exact_mod_cast hE
    right
    constructor
    · have : 11 * (v5 : ℤ) < 19 * v3 := by linarith
      exact_mod_cast this
    · have : 17 * (v4 : ℤ) < 13 * v5 := by linarith
      exact_mod_cast this

/-- **§8.1.1, step 4: the window `[25/(6v₅), 5/(6v₁)]`, flank `v₄`.**  Lonely, or (70b)
`5v₄ < 19v₁`. -/
theorem s811_step4 (h0 : 0 < v1) (h12 : v1 < v2) (h23 : v2 < v3) (h34 : v3 < v4) (h45 : v4 < v5)
    (hlarge : v3 ≤ 3 * v1) (h81 : 5 * v4 < 7 * v3) (h65 : 5 * v1 < v5) (h65b : 5 * v5 < 7 * v4)
    (h66 : 25 * v3 < 39 * v2) (h68 : 11 * v5 < 19 * v3) (h69 : 17 * v2 < 7 * v5) :
    (∃ t : ℝ, 0 < t ∧ Lonely6 v1 v2 v3 v4 v5 t) ∨ 5 * v4 < 19 * v1 := by
  have z1 : (0 : ℤ) < v1 := by exact_mod_cast h0
  have zl : (v3 : ℤ) ≤ 3 * v1 := by exact_mod_cast hlarge
  have z81 : 5 * (v4 : ℤ) < 7 * v3 := by exact_mod_cast h81
  have z12 : (v1 : ℤ) < v2 := by exact_mod_cast h12
  have z23 : (v2 : ℤ) < v3 := by exact_mod_cast h23
  have z34 : (v3 : ℤ) < v4 := by exact_mod_cast h34
  have z45 : (v4 : ℤ) < v5 := by exact_mod_cast h45
  have z65 : 5 * (v1 : ℤ) < v5 := by exact_mod_cast h65
  have z65b : 5 * (v5 : ℤ) < 7 * v4 := by exact_mod_cast h65b
  have z66 : 25 * (v3 : ℤ) < 39 * v2 := by exact_mod_cast h66
  have z68 : 11 * (v5 : ℤ) < 19 * v3 := by exact_mod_cast h68
  have z69 : 17 * (v2 : ℤ) < 7 * v5 := by exact_mod_cast h69
  rcases step4 (x := v4) (a := v5) (b := v1) (p := 25) (q := 5) (d1 := v1) (d2 := v2) (d3 := v3)
      (d4 := v5) (by omega) (by omega) h0 (by norm_num) (by push_cast; linarith) 0 1 2 4
      (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith)
      (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith)
      (by push_cast; linarith) (by push_cast; linarith) with
    ⟨t, ht, c1, c2, c3, c5, c4⟩ | ⟨k, hkL, hkR⟩
  · exact Or.inl ⟨t, ht, c1, c2, c3, c4, c5⟩
  right
  push_cast at hkL hkR
  have hk3 : 3 ≤ k := by
    by_contra hc; push Not at hc
    have : (6 * k + 1) * (v1 : ℤ) ≤ 13 * v1 := mul_le_mul_of_nonneg_right (by omega) (by omega)
    nlinarith
  have hk : k = 3 := by
    by_contra hc
    have : 4 ≤ k := by omega
    have : 23 * (v5 : ℤ) ≤ (6 * k - 1) * v5 := mul_le_mul_of_nonneg_right (by omega) (by omega)
    nlinarith
  subst hk
  have : 5 * (v4 : ℤ) < 19 * v1 := by linarith
  exact_mod_cast this

/-- **§8.1.1, step 5: the window `[37/(6v₅), 23/(6v₃)]`, flank `v₄`.**  Lonely, or (71b)
`29v₅ < 37v₄`. -/
theorem s811_step5 (h0 : 0 < v1) (h12 : v1 < v2) (h23 : v2 < v3) (h34 : v3 < v4) (h45 : v4 < v5)
    (hlarge : v3 ≤ 3 * v1) (h81 : 5 * v4 < 7 * v3) (h65 : 5 * v1 < v5) (h65b : 5 * v5 < 7 * v4)
    (h66 : 25 * v3 < 39 * v2) (h68 : 11 * v5 < 19 * v3) (h69 : 17 * v2 < 7 * v5) :
    (∃ t : ℝ, 0 < t ∧ Lonely6 v1 v2 v3 v4 v5 t) ∨ 29 * v5 < 37 * v4 := by
  have z1 : (0 : ℤ) < v1 := by exact_mod_cast h0
  have zl : (v3 : ℤ) ≤ 3 * v1 := by exact_mod_cast hlarge
  have z81 : 5 * (v4 : ℤ) < 7 * v3 := by exact_mod_cast h81
  have z12 : (v1 : ℤ) < v2 := by exact_mod_cast h12
  have z23 : (v2 : ℤ) < v3 := by exact_mod_cast h23
  have z34 : (v3 : ℤ) < v4 := by exact_mod_cast h34
  have z45 : (v4 : ℤ) < v5 := by exact_mod_cast h45
  have z65 : 5 * (v1 : ℤ) < v5 := by exact_mod_cast h65
  have z65b : 5 * (v5 : ℤ) < 7 * v4 := by exact_mod_cast h65b
  have z66 : 25 * (v3 : ℤ) < 39 * v2 := by exact_mod_cast h66
  have z68 : 11 * (v5 : ℤ) < 19 * v3 := by exact_mod_cast h68
  have z69 : 17 * (v2 : ℤ) < 7 * v5 := by exact_mod_cast h69
  rcases step4 (x := v4) (a := v5) (b := v3) (p := 37) (q := 23) (d1 := v1) (d2 := v2) (d3 := v3)
      (d4 := v5) (by omega) (by omega) (by omega) (by norm_num) (by push_cast; linarith) 1 2 3 6
      (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith)
      (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith)
      (by push_cast; linarith) (by push_cast; linarith) with
    ⟨t, ht, c1, c2, c3, c5, c4⟩ | ⟨k, hkL, hkR⟩
  · exact Or.inl ⟨t, ht, c1, c2, c3, c4, c5⟩
  right
  push_cast at hkL hkR
  have hk5 : 5 ≤ k := by
    by_contra hc; push Not at hc
    have : (6 * k + 1) * (v3 : ℤ) ≤ 25 * v3 := mul_le_mul_of_nonneg_right (by omega) (by omega)
    nlinarith
  have : 29 * (v5 : ℤ) ≤ (6 * k - 1) * v5 := mul_le_mul_of_nonneg_right (by omega) (by omega)
  have : 29 * (v5 : ℤ) < 37 * v4 := by linarith
  exact_mod_cast this

/-- **§8.1.2, step 4: the point `13/(6v₃)`, flank `v₄`.**  Lonely, or (73) `17v₃ < 13v₄`. -/
theorem s812_step4 (h0 : 0 < v1) (h12 : v1 < v2) (h23 : v2 < v3) (h34 : v3 < v4) (h45 : v4 < v5)
    (hlarge : v3 ≤ 3 * v1) (h81 : 5 * v4 < 7 * v3) (h65 : 5 * v1 < v5)
    (h66 : 25 * v3 < 39 * v2) (h67 : 11 * v2 < 7 * v4) (h68 : 11 * v5 < 19 * v3)
    (h72 : 17 * v4 < 13 * v5) :
    (∃ t : ℝ, 0 < t ∧ Lonely6 v1 v2 v3 v4 v5 t) ∨ 17 * v3 < 13 * v4 := by
  have z1 : (0 : ℤ) < v1 := by exact_mod_cast h0
  have zl : (v3 : ℤ) ≤ 3 * v1 := by exact_mod_cast hlarge
  have z81 : 5 * (v4 : ℤ) < 7 * v3 := by exact_mod_cast h81
  have z12 : (v1 : ℤ) < v2 := by exact_mod_cast h12
  have z23 : (v2 : ℤ) < v3 := by exact_mod_cast h23
  have z34 : (v3 : ℤ) < v4 := by exact_mod_cast h34
  have z45 : (v4 : ℤ) < v5 := by exact_mod_cast h45
  have z65 : 5 * (v1 : ℤ) < v5 := by exact_mod_cast h65
  have z66 : 25 * (v3 : ℤ) < 39 * v2 := by exact_mod_cast h66
  have z67 : 11 * (v2 : ℤ) < 7 * v4 := by exact_mod_cast h67
  have z68 : 11 * (v5 : ℤ) < 19 * v3 := by exact_mod_cast h68
  have z72 : 17 * (v4 : ℤ) < 13 * v5 := by exact_mod_cast h72
  rcases step4 (x := v4) (a := v3) (b := v3) (p := 13) (q := 13) (d1 := v1) (d2 := v2) (d3 := v3)
      (d4 := v5) (by omega) (by omega) (by omega) (by norm_num) le_rfl 0 1 2 3
      (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith)
      (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith)
      (by push_cast; linarith) (by push_cast; linarith) with
    ⟨t, ht, c1, c2, c3, c5, c4⟩ | ⟨k, hkL, hkR⟩
  · exact Or.inl ⟨t, ht, c1, c2, c3, c4, c5⟩
  right
  push_cast at hkL hkR
  have hk3 : 3 ≤ k := by
    by_contra hc; push Not at hc
    have : (6 * k + 1) * (v3 : ℤ) ≤ 13 * v3 := mul_le_mul_of_nonneg_right (by omega) (by omega)
    nlinarith
  have hk : k = 3 := by
    by_contra hc
    have : 4 ≤ k := by omega
    have : 23 * (v3 : ℤ) ≤ (6 * k - 1) * v3 := mul_le_mul_of_nonneg_right (by omega) (by omega)
    nlinarith
  subst hk
  have : 17 * (v3 : ℤ) < 13 * v4 := by linarith
  exact_mod_cast this

set_option maxHeartbeats 1000000 in
/-- **§8.1.2, step 5: the points `109/(30v₃)` and `26/(6v₃)`, flank `v₂`.**  One of them is
lonely: were `v₂` blocked at both, its zones would force `85v₃ < 109v₂` and `26v₂ < 19v₃`. -/
theorem s812_step5 (h0 : 0 < v1) (h12 : v1 < v2) (h23 : v2 < v3) (h34 : v3 < v4) (h45 : v4 < v5)
    (hlarge : v3 ≤ 3 * v1) (h65 : 5 * v1 < v5) (h66 : 25 * v3 < 39 * v2) (h67 : 11 * v2 < 7 * v4)
    (h68 : 11 * v5 < 19 * v3) (h72 : 17 * v4 < 13 * v5) (h73 : 17 * v3 < 13 * v4) :
    ∃ t : ℝ, 0 < t ∧ Lonely6 v1 v2 v3 v4 v5 t := by
  have z1 : (0 : ℤ) < v1 := by exact_mod_cast h0
  have zl : (v3 : ℤ) ≤ 3 * v1 := by exact_mod_cast hlarge
  have z12 : (v1 : ℤ) < v2 := by exact_mod_cast h12
  have z23 : (v2 : ℤ) < v3 := by exact_mod_cast h23
  have z34 : (v3 : ℤ) < v4 := by exact_mod_cast h34
  have z45 : (v4 : ℤ) < v5 := by exact_mod_cast h45
  have z65 : 5 * (v1 : ℤ) < v5 := by exact_mod_cast h65
  have z66 : 25 * (v3 : ℤ) < 39 * v2 := by exact_mod_cast h66
  have z67 : 11 * (v2 : ℤ) < 7 * v4 := by exact_mod_cast h67
  have z68 : 11 * (v5 : ℤ) < 19 * v3 := by exact_mod_cast h68
  have z72 : 17 * (v4 : ℤ) < 13 * v5 := by exact_mod_cast h72
  have z73 : 17 * (v3 : ℤ) < 13 * v4 := by exact_mod_cast h73
  have p5 : 0 < 5 * v3 := by omega
  -- the point `109/(30v₃) = 109/(6·5v₃)`
  rcases step4 (x := v2) (a := 5 * v3) (b := 5 * v3) (p := 109) (q := 109) (d1 := v1) (d2 := v3)
      (d3 := v4) (d4 := v5) (by omega) p5 p5 (by norm_num) le_rfl 1 3 4 6
      (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith)
      (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith)
      (by push_cast; linarith) (by push_cast; linarith) with
    ⟨t, ht, c1, c3, c4, c5, c2⟩ | ⟨K1, h1L, h1R⟩
  · exact ⟨t, ht, c1, c2, c3, c4, c5⟩
  -- the point `26/(6v₃)`
  rcases step4 (x := v2) (a := v3) (b := v3) (p := 26) (q := 26) (d1 := v1) (d2 := v3)
      (d3 := v4) (d4 := v5) (by omega) (by omega) (by omega) (by norm_num) le_rfl 1 4 5 7
      (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith)
      (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith)
      (by push_cast; linarith) (by push_cast; linarith) with
    ⟨t, ht, c1, c3, c4, c5, c2⟩ | ⟨K2, h2L, h2R⟩
  · exact ⟨t, ht, c1, c2, c3, c4, c5⟩
  exfalso
  push_cast at h1L h1R h2L h2R
  have zv3 : (0 : ℤ) < v3 := by omega
  have hK1 : K1 = 3 := by
    rcases lt_trichotomy K1 3 with h | h | h
    · have : (6 * K1 + 1) * (5 * (v3 : ℤ)) ≤ 13 * (5 * v3) :=
        mul_le_mul_of_nonneg_right (by omega) (by omega)
      nlinarith
    · exact h
    · have : 23 * (5 * (v3 : ℤ)) ≤ (6 * K1 - 1) * (5 * v3) :=
        mul_le_mul_of_nonneg_right (by omega) (by omega)
      nlinarith
  have hK2 : K2 = 3 := by
    rcases lt_trichotomy K2 3 with h | h | h
    · have : (6 * K2 + 1) * (v3 : ℤ) ≤ 13 * v3 := mul_le_mul_of_nonneg_right (by omega) (by omega)
      nlinarith
    · exact h
    · have : 23 * (v3 : ℤ) ≤ (6 * K2 - 1) * v3 := mul_le_mul_of_nonneg_right (by omega) (by omega)
      nlinarith
  subst hK1 hK2
  linarith

end S81

/-! ## §8 assembled -/

/-- **§8.1.1.** -/
theorem lonely_8_1_1 {v1 v2 v3 v4 v5 : ℕ} (h0 : 0 < v1) (h12 : v1 < v2) (h23 : v2 < v3)
    (h34 : v3 < v4) (h45 : v4 < v5) (hlarge : v3 ≤ 3 * v1) (h81 : 5 * v4 < 7 * v3)
    (h811 : 13 * v2 ≤ 7 * v4) : ∃ t : ℝ, 0 < t ∧ Lonely6 v1 v2 v3 v4 v5 t := by
  rcases s81_step1 h0 h12 h23 h34 h45 hlarge h81 with h | ⟨h65, h65b⟩
  · exact h
  rcases s81_step2 h0 h12 h23 h34 h45 hlarge h81 h65 h65b with h | ⟨h66, h67⟩
  · exact h
  rcases s811_step3 h0 h12 h23 h34 h45 hlarge h81 h65 h65b h66 h811 with h | ⟨h68, h69⟩
  · exact h
  rcases s811_step4 h0 h12 h23 h34 h45 hlarge h81 h65 h65b h66 h68 h69 with h | h70
  · exact h
  rcases s811_step5 h0 h12 h23 h34 h45 hlarge h81 h65 h65b h66 h68 h69 with h | h71
  · exact h
  exfalso
  omega

/-- **§8.1.2.** -/
theorem lonely_8_1_2 {v1 v2 v3 v4 v5 : ℕ} (h0 : 0 < v1) (h12 : v1 < v2) (h23 : v2 < v3)
    (h34 : v3 < v4) (h45 : v4 < v5) (hlarge : v3 ≤ 3 * v1) (h81 : 5 * v4 < 7 * v3)
    (h812 : 7 * v4 < 13 * v2) : ∃ t : ℝ, 0 < t ∧ Lonely6 v1 v2 v3 v4 v5 t := by
  rcases s81_step1 h0 h12 h23 h34 h45 hlarge h81 with h | ⟨h65, h65b⟩
  · exact h
  rcases s81_step2 h0 h12 h23 h34 h45 hlarge h81 h65 h65b with h | ⟨h66, h67⟩
  · exact h
  rcases s812_step3 h0 h12 h23 h34 h45 hlarge h81 h65 h65b h66 h67 h812 with h | ⟨h68, h72⟩
  · exact h
  rcases s812_step4 h0 h12 h23 h34 h45 hlarge h81 h65 h66 h67 h68 h72 with h | h73
  · exact h
  exact s812_step5 h0 h12 h23 h34 h45 hlarge h65 h66 h67 h68 h72 h73

/-- **BHK §8 in the framework** (`v₃ ≤ 3 v₁`): five whole-number disparities are lonely at `1/6`,
at a named instant — a flank opening in a window where the other four sit in known clear laps,
or the window's start. -/
theorem lonely_8 {v1 v2 v3 v4 v5 : ℕ} (h0 : 0 < v1) (h12 : v1 < v2) (h23 : v2 < v3)
    (h34 : v3 < v4) (h45 : v4 < v5) (hlarge : v3 ≤ 3 * v1) :
    ∃ t : ℝ, 0 < t ∧ Lonely6 v1 v2 v3 v4 v5 t := by
  by_cases h81 : 5 * v4 < 7 * v3
  · by_cases h811 : 13 * v2 ≤ 7 * v4
    · exact lonely_8_1_1 h0 h12 h23 h34 h45 hlarge h81 h811
    · exact lonely_8_1_2 h0 h12 h23 h34 h45 hlarge h81 (by omega)
  · exact lonely_8_2 h0 h12 h23 h34 h45 hlarge (by omega)

end LRC.OrderSixN
