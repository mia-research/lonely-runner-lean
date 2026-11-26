import Mathlib
import Fresh.Framework
import Fresh.Localisation

/-!
# The first-order lonely window of a component: `[max exits, min entries]`

Written 2026-10-24.  New file.  Readings `p i` (AP) and `x i` (perturbed), `1 ≤ p i ≤ 7`, `|x i - p i| ≤ ε`.  The zone of a reading `x` at lap `z : ℤ`
is the open interval `((z - 1/8)/x, (z + 1/8)/x)`; `t` is clear for `x` iff it lies in no zone (`lonely_iff_nozone`).
An AP lonely component `[a, b]` is described by its window `[a - δ/2, b + δ/2]` and the AP classification of every zone that can meet the window:
far from it, exiting exactly at `a`, or entering exactly at `b`.  `window_iff`: for `ε` small against the margin `δ`, inside the window `t` is lonely for
all readings iff `t` is at or after every exit `(z + 1/8)/x i` and at or before every entry `(z - 1/8)/x i`.  `window_iff_maxmin`: with finite exit and
entry sets this is `max exits ≤ t ≤ min entries`.  Grades: [L].  Not claimed: that the window hypotheses (classification) hold for a given AP component (a finite
check), nor anything for deviations beyond the stated bound.
-/

open Classical

namespace Fresh.WindowFO

open Fresh

theorem zone_iff {x t : ℝ} (hx : 0 < x) (z : ℤ) :
    |x * t - z| < 1 / 8 ↔ ((z : ℝ) - 1 / 8) / x < t ∧ t < ((z : ℝ) + 1 / 8) / x := by
  rw [abs_lt, div_lt_iff₀ hx, lt_div_iff₀ hx]
  constructor
  · rintro ⟨h1, h2⟩; constructor <;> nlinarith
  · rintro ⟨h1, h2⟩; constructor <;> nlinarith

theorem lonely_iff_nozone {x t : ℝ} (hx : 0 < x) :
    (1 / 8 : ℝ) ≤ distInt (x * t) ↔ ∀ z : ℤ, ¬ (((z : ℝ) - 1 / 8) / x < t ∧ t < ((z : ℝ) + 1 / 8) / x) := by
  rw [Fresh.Localisation.le_distInt_iff]
  constructor
  · intro h z hz
    have := (zone_iff hx z).2 hz
    linarith [h z]
  · intro h z
    by_contra hlt
    push Not at hlt
    exact h z ((zone_iff hx z).1 hlt)

theorem edge_pert {c p x ε : ℝ} (hp : 1 ≤ p) (hε : ε ≤ 1 / 2) (hdev : |x - p| ≤ ε) :
    |c / x - c / p| ≤ 2 * |c| * ε := by
  have h1 := abs_le.1 hdev
  have hx : 1 / 2 ≤ x := by linarith
  have hε0 : 0 ≤ ε := le_trans (abs_nonneg _) hdev
  have hxp : 1 / 2 ≤ x * p := by nlinarith
  have hxp0 : 0 < x * p := by linarith
  have e : c / x - c / p = c * (p - x) / (x * p) := by field_simp
  rw [e, abs_div, abs_mul, abs_of_pos hxp0, div_le_iff₀ hxp0]
  have h2 : |p - x| ≤ ε := by rwa [abs_sub_comm]
  have h3 : |c| * |p - x| ≤ |c| * ε := mul_le_mul_of_nonneg_left h2 (abs_nonneg c)
  nlinarith [mul_nonneg (abs_nonneg c) hε0]

/-- One zone: the four facts used in `window_iff`. -/
theorem zone_facts {pi xi ε δ a b t K : ℝ} {z : ℤ}
    (hp1 : 1 ≤ pi) (hp7 : pi ≤ 7) (hdev : |xi - pi| ≤ ε) (hε : ε ≤ 1 / 2)
    (hK1 : |(z : ℝ) - 1 / 8| ≤ K) (hK2 : |(z : ℝ) + 1 / 8| ≤ K) (hKε : 2 * K * ε ≤ δ / 4)
    (hδ : δ ≤ 1 / 28) (hδ0 : 0 < δ) (hab : a ≤ b) (ht1 : a - δ / 2 ≤ t) (ht2 : t ≤ b + δ / 2) :
    (((z : ℝ) + 1 / 8) / pi ≤ a - δ → ¬ (((z : ℝ) - 1 / 8) / xi < t ∧ t < ((z : ℝ) + 1 / 8) / xi)) ∧
    (b + δ ≤ ((z : ℝ) - 1 / 8) / pi → ¬ (((z : ℝ) - 1 / 8) / xi < t ∧ t < ((z : ℝ) + 1 / 8) / xi)) ∧
    (((z : ℝ) + 1 / 8) / pi = a → ((z : ℝ) - 1 / 8) / xi < t) ∧
    (((z : ℝ) - 1 / 8) / pi = b → t < ((z : ℝ) + 1 / 8) / xi) := by
  have hlo := edge_pert (c := (z : ℝ) - 1 / 8) hp1 hε hdev
  have hhi := edge_pert (c := (z : ℝ) + 1 / 8) hp1 hε hdev
  have hlo' : |((z : ℝ) - 1 / 8) / xi - ((z : ℝ) - 1 / 8) / pi| ≤ δ / 4 := by
    refine le_trans hlo ?_
    have hε0 : 0 ≤ ε := le_trans (abs_nonneg _) hdev
    nlinarith [mul_nonneg (sub_nonneg.2 hK1) hε0]
  have hhi' : |((z : ℝ) + 1 / 8) / xi - ((z : ℝ) + 1 / 8) / pi| ≤ δ / 4 := by
    refine le_trans hhi ?_
    have hε0 : 0 ≤ ε := le_trans (abs_nonneg _) hdev
    nlinarith [mul_nonneg (sub_nonneg.2 hK2) hε0]
  have hw : (1 : ℝ) / 28 ≤ ((z : ℝ) + 1 / 8) / pi - ((z : ℝ) - 1 / 8) / pi := by
    have : ((z : ℝ) + 1 / 8) / pi - ((z : ℝ) - 1 / 8) / pi = (1 / 4) / pi := by field_simp; ring
    rw [this, le_div_iff₀ (by linarith)]
    nlinarith
  have hlo2 := abs_le.1 hlo'
  have hhi2 := abs_le.1 hhi'
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h ⟨_, h2⟩; linarith
  · intro h ⟨h1, _⟩; linarith
  · intro h; linarith
  · intro h; linarith

/-- **The first-order window.**  Inside the window `[a - δ/2, b + δ/2]` of an AP lonely component `[a, b]`, a perturbed arrangement (`|x i - p i| ≤ ε`, `ε` small
against the margin `δ`) is lonely for every reading iff `t` is at or after every exit `(z + 1/8)/x i` of an AP exit zone and at or before every entry
`(z - 1/8)/x i` of an AP entry zone.  `hcls` is the AP classification of the zones with laps `0 ≤ z ≤ Z0`: far left of the window, far right of it, exactly an exit at
`a`, or exactly an entry at `b`. -/
theorem window_iff {ι : Type*} (p x : ι → ℝ) (hp : ∀ i, 1 ≤ p i ∧ p i ≤ 7) (ε : ℝ) (hdev : ∀ i, |x i - p i| ≤ ε)
    (a b δ T : ℝ) (Z0 : ℤ) (hab : a ≤ b) (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 28) (ha : δ < a) (hT : b + δ ≤ T)
    (hZ : 8 * T + 1 ≤ (Z0 : ℝ)) (hε : 8 * ((Z0 : ℝ) + 1) * ε ≤ δ)
    (hcls : ∀ i, ∀ z : ℤ, 0 ≤ z → z ≤ Z0 →
      ((z : ℝ) + 1 / 8) / p i ≤ a - δ ∨ b + δ ≤ ((z : ℝ) - 1 / 8) / p i ∨
        ((z : ℝ) + 1 / 8) / p i = a ∨ ((z : ℝ) - 1 / 8) / p i = b)
    (t : ℝ) (ht1 : a - δ / 2 ≤ t) (ht2 : t ≤ b + δ / 2) :
    (∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)) ↔
      (∀ i, ∀ z : ℤ, 0 ≤ z → z ≤ Z0 → ((z : ℝ) + 1 / 8) / p i = a → ((z : ℝ) + 1 / 8) / x i ≤ t) ∧
      (∀ i, ∀ z : ℤ, 0 ≤ z → z ≤ Z0 → ((z : ℝ) - 1 / 8) / p i = b → t ≤ ((z : ℝ) - 1 / 8) / x i) := by
  have hT0 : 0 < T := by linarith
  have hZ1 : (1 : ℝ) ≤ (Z0 : ℝ) := by linarith
  have hε0 : ∀ i : ι, 0 ≤ ε := fun i => le_trans (abs_nonneg _) (hdev i)
  have hεle : ∀ i : ι, ε ≤ 1 / 2 := by
    intro i
    have := hε0 i
    nlinarith
  have hxpos : ∀ i : ι, 0 < x i := by
    intro i
    have h := abs_le.1 (hdev i); have := (hp i).1; have := hεle i; linarith
  have ht0 : 0 < t := by linarith
  have hxle : ∀ i : ι, x i ≤ 8 := by
    intro i
    have h := abs_le.1 (hdev i); have := (hp i).2; have := hεle i; linarith
  have key : ∀ i, ∀ z : ℤ, 0 ≤ z → z ≤ Z0 →
      (((z : ℝ) + 1 / 8) / p i ≤ a - δ → ¬ (((z : ℝ) - 1 / 8) / x i < t ∧ t < ((z : ℝ) + 1 / 8) / x i)) ∧
      (b + δ ≤ ((z : ℝ) - 1 / 8) / p i → ¬ (((z : ℝ) - 1 / 8) / x i < t ∧ t < ((z : ℝ) + 1 / 8) / x i)) ∧
      (((z : ℝ) + 1 / 8) / p i = a → ((z : ℝ) - 1 / 8) / x i < t) ∧
      (((z : ℝ) - 1 / 8) / p i = b → t < ((z : ℝ) + 1 / 8) / x i) := by
    intro i z hz0 hzZ
    have hz0' : (0 : ℝ) ≤ z := by exact_mod_cast hz0
    have hzZ' : (z : ℝ) ≤ Z0 := by exact_mod_cast hzZ
    refine zone_facts (K := (Z0 : ℝ) + 1) (hp i).1 (hp i).2 (hdev i) (hεle i) ?_ ?_ ?_ hδ hδ0 hab ht1 ht2
    · rw [abs_le]; constructor <;> linarith
    · rw [abs_le]; constructor <;> linarith
    · have := hε0 i; nlinarith
  have hnoz : ∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t) ↔ ∀ z : ℤ, ¬ (((z : ℝ) - 1 / 8) / x i < t ∧ t < ((z : ℝ) + 1 / 8) / x i) :=
    fun i => lonely_iff_nozone (hxpos i)
  constructor
  · intro h
    refine ⟨fun i z hz0 hzZ hEq => ?_, fun i z hz0 hzZ hEq => ?_⟩
    · by_contra hlt
      push Not at hlt
      exact (hnoz i).1 (h i) z ⟨((key i z hz0 hzZ).2.2.1 hEq), hlt⟩
    · by_contra hgt
      push Not at hgt
      exact (hnoz i).1 (h i) z ⟨hgt, ((key i z hz0 hzZ).2.2.2 hEq)⟩
  · rintro ⟨hE, hB⟩ i
    rw [hnoz i]
    intro z ⟨hl, hh⟩
    by_cases hz0 : 0 ≤ z
    · by_cases hzZ : z ≤ Z0
      · rcases hcls i z hz0 hzZ with h1 | h2 | h3 | h4
        · exact (key i z hz0 hzZ).1 h1 ⟨hl, hh⟩
        · exact (key i z hz0 hzZ).2.1 h2 ⟨hl, hh⟩
        · have := hE i z hz0 hzZ h3; linarith
        · have := hB i z hz0 hzZ h4; linarith
      · push Not at hzZ
        have hz1 : (Z0 : ℝ) + 1 ≤ z := by exact_mod_cast hzZ
        have h8 := hxle i
        have hxp := hxpos i
        have : t * x i < (z : ℝ) - 1 / 8 := by nlinarith
        rw [div_lt_iff₀ hxp] at hl
        linarith
    · push Not at hz0
      have hz1 : (z : ℝ) ≤ -1 := by exact_mod_cast (by omega : z ≤ -1)
      have hxp := hxpos i
      rw [lt_div_iff₀ hxp] at hh
      nlinarith

/-- The max/min form: finite exit and entry index sets (exactly the AP exit and entry zones at `a` and `b`), both nonempty:
inside the window, lonely for every reading iff `max exits ≤ t ≤ min entries`. -/
theorem window_iff_maxmin {ι : Type*} (p x : ι → ℝ) (hp : ∀ i, 1 ≤ p i ∧ p i ≤ 7) (ε : ℝ) (hdev : ∀ i, |x i - p i| ≤ ε)
    (a b δ T : ℝ) (Z0 : ℤ) (hab : a ≤ b) (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 28) (ha : δ < a) (hT : b + δ ≤ T)
    (hZ : 8 * T + 1 ≤ (Z0 : ℝ)) (hε : 8 * ((Z0 : ℝ) + 1) * ε ≤ δ)
    (hcls : ∀ i, ∀ z : ℤ, 0 ≤ z → z ≤ Z0 →
      ((z : ℝ) + 1 / 8) / p i ≤ a - δ ∨ b + δ ≤ ((z : ℝ) - 1 / 8) / p i ∨
        ((z : ℝ) + 1 / 8) / p i = a ∨ ((z : ℝ) - 1 / 8) / p i = b)
    (EX EN : Finset (ι × ℤ)) (hEX : EX.Nonempty) (hEN : EN.Nonempty)
    (hEXdef : ∀ q : ι × ℤ, q ∈ EX ↔ 0 ≤ q.2 ∧ q.2 ≤ Z0 ∧ ((q.2 : ℝ) + 1 / 8) / p q.1 = a)
    (hENdef : ∀ q : ι × ℤ, q ∈ EN ↔ 0 ≤ q.2 ∧ q.2 ≤ Z0 ∧ ((q.2 : ℝ) - 1 / 8) / p q.1 = b)
    (t : ℝ) (ht1 : a - δ / 2 ≤ t) (ht2 : t ≤ b + δ / 2) :
    (∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)) ↔
      EX.sup' hEX (fun q => ((q.2 : ℝ) + 1 / 8) / x q.1) ≤ t ∧ t ≤ EN.inf' hEN (fun q => ((q.2 : ℝ) - 1 / 8) / x q.1) := by
  rw [window_iff p x hp ε hdev a b δ T Z0 hab hδ0 hδ ha hT hZ hε hcls t ht1 ht2]
  rw [Finset.sup'_le_iff, Finset.le_inf'_iff]
  constructor
  · rintro ⟨hE, hB⟩
    exact ⟨fun q hq => by
        obtain ⟨h0, h1, h2⟩ := (hEXdef q).1 hq
        exact hE q.1 q.2 h0 h1 h2,
      fun q hq => by
        obtain ⟨h0, h1, h2⟩ := (hENdef q).1 hq
        exact hB q.1 q.2 h0 h1 h2⟩
  · rintro ⟨hE, hB⟩
    exact ⟨fun i z h0 h1 h2 => hE (i, z) ((hEXdef (i, z)).2 ⟨h0, h1, h2⟩),
      fun i z h0 h1 h2 => hB (i, z) ((hENdef (i, z)).2 ⟨h0, h1, h2⟩)⟩

#print axioms window_iff
#print axioms window_iff_maxmin

/-! ## The interior subject with AP speed 2: its first lonely component

Readings `p = (1, 1, 2, 3, 4, 5, 6)` (runners with AP speeds 1, 3, 4, 5, 6, 7, 8).  The first lonely component of the AP is `[1/8, 7/48]`: exits at `1/8`
(the two readings `1`, lap `0`), entry at `7/48` (the reading `6`, lap `1`).  Window margin `δ = 1/56`, `T = b + δ = 55/336`, `Z0 = 3`; the deviation bound
`8 (Z0 + 1) ε ≤ δ` is `ε ≤ 1/1792`.  The classification of the zones with laps `0..3` is a finite check. -/

noncomputable def pInt2 : Fin 7 → ℝ := ![1, 1, 2, 3, 4, 5, 6]

theorem pInt2_bounds (i : Fin 7) : 1 ≤ pInt2 i ∧ pInt2 i ≤ 7 := by
  fin_cases i <;> norm_num [pInt2]

theorem pInt2_cls : ∀ i : Fin 7, ∀ z : ℤ, 0 ≤ z → z ≤ 3 →
    ((z : ℝ) + 1 / 8) / pInt2 i ≤ 1 / 8 - 1 / 56 ∨ 7 / 48 + 1 / 56 ≤ ((z : ℝ) - 1 / 8) / pInt2 i ∨
      ((z : ℝ) + 1 / 8) / pInt2 i = 1 / 8 ∨ ((z : ℝ) - 1 / 8) / pInt2 i = 7 / 48 := by
  intro i z hz0 hz3
  interval_cases z <;> fin_cases i <;> norm_num [pInt2]

theorem pInt2_0 : pInt2 0 = 1 := by simp [pInt2]
theorem pInt2_1 : pInt2 1 = 1 := by simp [pInt2]
theorem pInt2_6 : pInt2 6 = 6 := by simp [pInt2]

/-- **Readings form.**  For `|x i - p i| ≤ ε ≤ 1/1792`, inside `[1/8 - 1/112, 7/48 + 1/112]` the perturbed interior subject is lonely iff
`1/(8 x₀) ≤ t`, `1/(8 x₁) ≤ t` and `t ≤ 7/(8 x₆)`: the component is `[1/(8 min(x₀, x₁)), 7/(8 x₆)]`. -/
theorem interior2_window (x : Fin 7 → ℝ) (ε : ℝ) (hdev : ∀ i, |x i - pInt2 i| ≤ ε) (hε : ε ≤ 1 / 1792)
    (t : ℝ) (ht1 : 1 / 8 - 1 / 112 ≤ t) (ht2 : t ≤ 7 / 48 + 1 / 112) :
    (∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)) ↔
      1 / (8 * x 0) ≤ t ∧ 1 / (8 * x 1) ≤ t ∧ t ≤ 7 / (8 * x 6) := by
  have hε' : 8 * (((3 : ℤ) : ℝ) + 1) * ε ≤ 1 / 56 := by push_cast; linarith
  have hw := window_iff pInt2 x pInt2_bounds ε hdev (1 / 8) (7 / 48) (1 / 56) (55 / 336) 3 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by push_cast; norm_num) hε' pInt2_cls t
    (by linarith) (by linarith)
  rw [hw]
  have hx : ∀ i, 0 < x i := by
    intro i
    have h := abs_le.1 (hdev i); have := (pInt2_bounds i).1
    linarith
  have c0 : (((0 : ℤ) : ℝ) + 1 / 8) / x 0 = 1 / (8 * x 0) := by
    have := (hx 0).ne'; push_cast; field_simp; ring
  have c1 : (((0 : ℤ) : ℝ) + 1 / 8) / x 1 = 1 / (8 * x 1) := by
    have := (hx 1).ne'; push_cast; field_simp; ring
  have c6 : (((1 : ℤ) : ℝ) - 1 / 8) / x 6 = 7 / (8 * x 6) := by
    have := (hx 6).ne'; push_cast; field_simp; norm_num
  constructor
  · rintro ⟨hE, hB⟩
    have e0 := hE 0 0 (by norm_num) (by norm_num) (by norm_num [pInt2_0])
    have e1 := hE 1 0 (by norm_num) (by norm_num) (by norm_num [pInt2_1])
    have b6 := hB 6 1 (by norm_num) (by norm_num) (by norm_num [pInt2_6])
    rw [c0] at e0
    rw [c1] at e1
    rw [c6] at b6
    exact ⟨e0, e1, b6⟩
  · rintro ⟨h0, h1, h6⟩
    have h0' : (((0 : ℤ) : ℝ) + 1 / 8) / x 0 ≤ t := by rw [c0]; exact h0
    have h1' : (((0 : ℤ) : ℝ) + 1 / 8) / x 1 ≤ t := by rw [c1]; exact h1
    have h6' : t ≤ (((1 : ℤ) : ℝ) - 1 / 8) / x 6 := by rw [c6]; exact h6
    refine ⟨fun i z hz0 hz3 heq => ?_, fun i z hz0 hz3 heq => ?_⟩
    · interval_cases z <;> fin_cases i <;>
        first
        | (exfalso; norm_num [pInt2] at heq; done)
        | (simpa using h0')
        | (simpa using h1')
    · interval_cases z <;> fin_cases i <;>
        first
        | (exfalso; norm_num [pInt2] at heq; done)
        | (simpa using h6')

#print axioms pInt2_cls
#print axioms interior2_window

theorem read_dev (v : Fin 8 → ℝ) (η : ℝ) (hv : ∀ i : Fin 8, |v i - (((i : ℕ) : ℝ) + 1)| ≤ η) (a b : Fin 8) (c : ℝ)
    (hc : |(((a : ℕ) : ℝ) + 1) - (((b : ℕ) : ℝ) + 1)| = c) : |(|v a - v b| - c)| ≤ 2 * η := by
  rw [← hc]
  refine le_trans (abs_abs_sub_abs_le_abs_sub _ _) ?_
  have e : (v a - v b) - ((((a : ℕ) : ℝ) + 1) - (((b : ℕ) : ℝ) + 1)) =
      (v a - (((a : ℕ) : ℝ) + 1)) - (v b - (((b : ℕ) : ℝ) + 1)) := by ring
  rw [e]
  have h1 := hv a
  have h2 := hv b
  calc _ ≤ |v a - (((a : ℕ) : ℝ) + 1)| + |v b - (((b : ℕ) : ℝ) + 1)| := abs_sub _ _
    _ ≤ 2 * η := by linarith

/-- **The interior subject with AP speed 2, as an arrangement.**  Speeds within `η ≤ 1/3584` of `i + 1` (runner `i`, AP speed `i + 1`; runner `1` is the subject).
Inside `[1/8 - 1/112, 7/48 + 1/112]` the subject is isolated at `t` iff `1/(8 |v 0 - v 1|) ≤ t`, `1/(8 |v 2 - v 1|) ≤ t` and `t ≤ 7/(8 |v 7 - v 1|)`:
the first lonely component is `[1/(8 d), 7/(8 r₆)]` with `d` the nearer neighbour gap. -/
theorem interior2_arrangement (v : Fin 8 → ℝ) (η : ℝ) (hη : η ≤ 1 / 3584)
    (hv : ∀ i : Fin 8, |v i - (((i : ℕ) : ℝ) + 1)| ≤ η)
    (t : ℝ) (ht1 : 1 / 8 - 1 / 112 ≤ t) (ht2 : t ≤ 7 / 48 + 1 / 112) :
    IsolatedAt v 1 t ↔
      1 / (8 * |v 0 - v 1|) ≤ t ∧ 1 / (8 * |v 2 - v 1|) ≤ t ∧ t ≤ 7 / (8 * |v 7 - v 1|) := by
  set x : Fin 7 → ℝ := ![|v 0 - v 1|, |v 2 - v 1|, |v 3 - v 1|, |v 4 - v 1|, |v 5 - v 1|, |v 6 - v 1|, |v 7 - v 1|] with hx
  have hdev : ∀ i, |x i - pInt2 i| ≤ 2 * η := by
    intro i
    fin_cases i
    · simpa [hx, pInt2] using read_dev v η hv 0 1 1 (by norm_num)
    · simpa [hx, pInt2] using read_dev v η hv 2 1 1 (by norm_num)
    · simpa [hx, pInt2] using read_dev v η hv 3 1 2 (by norm_num)
    · simpa [hx, pInt2] using read_dev v η hv 4 1 3 (by norm_num)
    · simpa [hx, pInt2] using read_dev v η hv 5 1 4 (by norm_num)
    · simpa [hx, pInt2] using read_dev v η hv 6 1 5 (by norm_num)
    · simpa [hx, pInt2] using read_dev v η hv 7 1 6 (by norm_num)
  have hiso : IsolatedAt v 1 t ↔ ∀ j : Fin 7, (1 / 8 : ℝ) ≤ distInt (x j * t) := by
    unfold IsolatedAt
    constructor
    · intro h j
      fin_cases j
      · have := h 0 (by decide); rw [← Fresh.Localisation.distInt_abs_mul] at this; simpa [hx] using this
      · have := h 2 (by decide); rw [← Fresh.Localisation.distInt_abs_mul] at this; simpa [hx] using this
      · have := h 3 (by decide); rw [← Fresh.Localisation.distInt_abs_mul] at this; simpa [hx] using this
      · have := h 4 (by decide); rw [← Fresh.Localisation.distInt_abs_mul] at this; simpa [hx] using this
      · have := h 5 (by decide); rw [← Fresh.Localisation.distInt_abs_mul] at this; simpa [hx] using this
      · have := h 6 (by decide); rw [← Fresh.Localisation.distInt_abs_mul] at this; simpa [hx] using this
      · have := h 7 (by decide); rw [← Fresh.Localisation.distInt_abs_mul] at this; simpa [hx] using this
    · intro h i hi
      have key : ∀ j : Fin 7, (1 / 8 : ℝ) ≤ distInt (x j * t) := h
      fin_cases i
      · have := key 0; rw [← Fresh.Localisation.distInt_abs_mul]; simpa [hx] using this
      · exact absurd rfl hi
      · have := key 1; rw [← Fresh.Localisation.distInt_abs_mul]; simpa [hx] using this
      · have := key 2; rw [← Fresh.Localisation.distInt_abs_mul]; simpa [hx] using this
      · have := key 3; rw [← Fresh.Localisation.distInt_abs_mul]; simpa [hx] using this
      · have := key 4; rw [← Fresh.Localisation.distInt_abs_mul]; simpa [hx] using this
      · have := key 5; rw [← Fresh.Localisation.distInt_abs_mul]; simpa [hx] using this
      · have := key 6; rw [← Fresh.Localisation.distInt_abs_mul]; simpa [hx] using this
  rw [hiso, interior2_window x (2 * η) hdev (by linarith) t ht1 ht2]
  simp [hx]

#print axioms interior2_arrangement

end Fresh.WindowFO
