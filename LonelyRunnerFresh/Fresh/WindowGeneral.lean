import Mathlib
import Fresh.Framework
import Fresh.Localisation
import Fresh.WindowFirstOrder

/-!
# The first-order window with a general reading bound `P`

Written 2026-10-24.  New file.  `Fresh.WindowFO.window_iff` and `window_iff_maxmin` with the AP bound `p i ≤ 7` replaced by `p i ≤ P`
(margin `δ ≤ 1/(4P)`, laps `(P + 1) T + 1 ≤ Z0`), for grids and residual subjects whose readings exceed 7.  Same proofs.  Grades: [L].
-/

open Classical

namespace Fresh.WindowFO

open Fresh

/-- One zone: the four facts used in `window_iff`. -/
theorem zone_factsP {P : ℝ} {pi xi ε δ a b t K : ℝ} {z : ℤ}
    (hp1 : 1 ≤ pi) (hp7 : pi ≤ P) (hdev : |xi - pi| ≤ ε) (hε : ε ≤ 1 / 2)
    (hK1 : |(z : ℝ) - 1 / 8| ≤ K) (hK2 : |(z : ℝ) + 1 / 8| ≤ K) (hKε : 2 * K * ε ≤ δ / 4)
    (hδ : δ ≤ 1 / (4 * P)) (hδ0 : 0 < δ) (hab : a ≤ b) (ht1 : a - δ / 2 ≤ t) (ht2 : t ≤ b + δ / 2) :
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
  have hw : 1 / (4 * P) ≤ ((z : ℝ) + 1 / 8) / pi - ((z : ℝ) - 1 / 8) / pi := by
    have : ((z : ℝ) + 1 / 8) / pi - ((z : ℝ) - 1 / 8) / pi = (1 / 4) / pi := by field_simp; ring
    have hP1 : 1 ≤ P := by linarith
    rw [this, div_le_div_iff₀ (by positivity) (by linarith)]
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
theorem window_iffP {ι : Type*} (P : ℝ) (hP : 1 ≤ P) (p x : ι → ℝ) (hp : ∀ i, 1 ≤ p i ∧ p i ≤ P) (ε : ℝ) (hdev : ∀ i, |x i - p i| ≤ ε)
    (a b δ T : ℝ) (Z0 : ℤ) (hab : a ≤ b) (hδ0 : 0 < δ) (hδ : δ ≤ 1 / (4 * P)) (ha : δ < a) (hT : b + δ ≤ T)
    (hZ : (P + 1) * T + 1 ≤ (Z0 : ℝ)) (hε : 8 * ((Z0 : ℝ) + 1) * ε ≤ δ)
    (hcls : ∀ i, ∀ z : ℤ, 0 ≤ z → z ≤ Z0 →
      ((z : ℝ) + 1 / 8) / p i ≤ a - δ ∨ b + δ ≤ ((z : ℝ) - 1 / 8) / p i ∨
        ((z : ℝ) + 1 / 8) / p i = a ∨ ((z : ℝ) - 1 / 8) / p i = b)
    (t : ℝ) (ht1 : a - δ / 2 ≤ t) (ht2 : t ≤ b + δ / 2) :
    (∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)) ↔
      (∀ i, ∀ z : ℤ, 0 ≤ z → z ≤ Z0 → ((z : ℝ) + 1 / 8) / p i = a → ((z : ℝ) + 1 / 8) / x i ≤ t) ∧
      (∀ i, ∀ z : ℤ, 0 ≤ z → z ≤ Z0 → ((z : ℝ) - 1 / 8) / p i = b → t ≤ ((z : ℝ) - 1 / 8) / x i) := by
  have hT0 : 0 < T := by linarith
  have hPT : 0 ≤ (P + 1) * T := by positivity
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
  have hxle : ∀ i : ι, x i ≤ P + 1 := by
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
    refine zone_factsP (P := P) (K := (Z0 : ℝ) + 1) (hp i).1 (hp i).2 (hdev i) (hεle i) ?_ ?_ ?_ hδ hδ0 hab ht1 ht2
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
theorem window_iff_maxminP {ι : Type*} (P : ℝ) (hP : 1 ≤ P) (p x : ι → ℝ) (hp : ∀ i, 1 ≤ p i ∧ p i ≤ P) (ε : ℝ) (hdev : ∀ i, |x i - p i| ≤ ε)
    (a b δ T : ℝ) (Z0 : ℤ) (hab : a ≤ b) (hδ0 : 0 < δ) (hδ : δ ≤ 1 / (4 * P)) (ha : δ < a) (hT : b + δ ≤ T)
    (hZ : (P + 1) * T + 1 ≤ (Z0 : ℝ)) (hε : 8 * ((Z0 : ℝ) + 1) * ε ≤ δ)
    (hcls : ∀ i, ∀ z : ℤ, 0 ≤ z → z ≤ Z0 →
      ((z : ℝ) + 1 / 8) / p i ≤ a - δ ∨ b + δ ≤ ((z : ℝ) - 1 / 8) / p i ∨
        ((z : ℝ) + 1 / 8) / p i = a ∨ ((z : ℝ) - 1 / 8) / p i = b)
    (EX EN : Finset (ι × ℤ)) (hEX : EX.Nonempty) (hEN : EN.Nonempty)
    (hEXdef : ∀ q : ι × ℤ, q ∈ EX ↔ 0 ≤ q.2 ∧ q.2 ≤ Z0 ∧ ((q.2 : ℝ) + 1 / 8) / p q.1 = a)
    (hENdef : ∀ q : ι × ℤ, q ∈ EN ↔ 0 ≤ q.2 ∧ q.2 ≤ Z0 ∧ ((q.2 : ℝ) - 1 / 8) / p q.1 = b)
    (t : ℝ) (ht1 : a - δ / 2 ≤ t) (ht2 : t ≤ b + δ / 2) :
    (∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)) ↔
      EX.sup' hEX (fun q => ((q.2 : ℝ) + 1 / 8) / x q.1) ≤ t ∧ t ≤ EN.inf' hEN (fun q => ((q.2 : ℝ) - 1 / 8) / x q.1) := by
  rw [window_iffP P hP p x hp ε hdev a b δ T Z0 hab hδ0 hδ ha hT hZ hε hcls t ht1 ht2]
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


#print axioms window_iffP
#print axioms window_iff_maxminP

end Fresh.WindowFO
