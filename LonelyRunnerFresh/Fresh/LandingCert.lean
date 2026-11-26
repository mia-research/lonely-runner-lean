import Mathlib
import Fresh.Framework
import Fresh.Localisation
import Fresh.WindowFirstOrder
import Fresh.WindowGeneral
import Fresh.LandingRule

/-!
# The landing certificate: a finite baseline check gives the first isolation of a perturbed subject

Written 2026-10-24.  New file.  Seven readings `p` (the baseline disparities of the subject, each at least `1` and at most `P`) and perturbed readings `x`
(`|x i - p i| ≤ ε`).  A baseline lonely component `[a c, b c]` has margin `δ c`, laps `0..Z0 c`, an exit cluster `EX c` (the zones whose upper edge is `a c`) and an
entry cluster `EN c` (the zones whose lower edge is `b c`); `hcls` is the baseline classification of every zone (far left, far right, or tied).  The components are ordered
and their windows disjoint (`hsep`), all inside `(0, H]`; `hcov` says that no instant of `(0, H]` outside the windows is lonely.  If some component is wide
(`δ/2 ≤ b - a`) it is alive for every `ε` in range, so the first lonely instant exists and equals the largest exit of the first alive component.

`hcov` is **[PROVISIONAL: covering]**, supporting the claim that the first lonely instant is the largest exit of the first alive component; it is a hypothesis here and is proved
in each instance from finite zone chains.  Grades: [L] for the theorem.  Not claimed: any instance; the check of the hypotheses is per subject.
-/

open Classical

namespace Fresh.LandingCert

open Fresh Fresh.WindowFO Fresh.LandingRule

/-- The largest exit of component `c`: the maximum of `(z + 1/8)/x i` over its exit cluster. -/
noncomputable def mxOf {m : ℕ} (x : Fin 7 → ℝ) (EX : Fin m → Finset (Fin 7 × ℤ)) (hEX : ∀ c, (EX c).Nonempty) (c : Fin m) : ℝ :=
  (EX c).sup' (hEX c) (fun q => ((q.2 : ℝ) + 1 / 8) / x q.1)

/-- The least entry of component `c`: the minimum of `(z - 1/8)/x i` over its entry cluster. -/
noncomputable def mnOf {m : ℕ} (x : Fin 7 → ℝ) (EN : Fin m → Finset (Fin 7 × ℤ)) (hEN : ∀ c, (EN c).Nonempty) (c : Fin m) : ℝ :=
  (EN c).inf' (hEN c) (fun q => ((q.2 : ℝ) - 1 / 8) / x q.1)

theorem landing_cert (m : ℕ) (P : ℝ) (hP : 1 ≤ P) (p x : Fin 7 → ℝ) (hp : ∀ i, 1 ≤ p i ∧ p i ≤ P) (ε : ℝ)
    (hdev : ∀ i, |x i - p i| ≤ ε)
    (a b δ T : Fin m → ℝ) (Z0 : Fin m → ℤ)
    (hab : ∀ c, a c ≤ b c) (hδ0 : ∀ c, 0 < δ c) (hδ : ∀ c, δ c ≤ 1 / (4 * P)) (ha : ∀ c, δ c < a c)
    (hT : ∀ c, b c + δ c ≤ T c) (hZ : ∀ c, (P + 1) * T c + 1 ≤ (Z0 c : ℝ))
    (hε : ∀ c, 8 * ((Z0 c : ℝ) + 1) * ε ≤ δ c)
    (hcls : ∀ c i, ∀ z : ℤ, 0 ≤ z → z ≤ Z0 c →
      ((z : ℝ) + 1 / 8) / p i ≤ a c - δ c ∨ b c + δ c ≤ ((z : ℝ) - 1 / 8) / p i ∨
        ((z : ℝ) + 1 / 8) / p i = a c ∨ ((z : ℝ) - 1 / 8) / p i = b c)
    (EX EN : Fin m → Finset (Fin 7 × ℤ)) (hEX : ∀ c, (EX c).Nonempty) (hEN : ∀ c, (EN c).Nonempty)
    (hEXdef : ∀ c, ∀ q : Fin 7 × ℤ, q ∈ EX c ↔ 0 ≤ q.2 ∧ q.2 ≤ Z0 c ∧ ((q.2 : ℝ) + 1 / 8) / p q.1 = a c)
    (hENdef : ∀ c, ∀ q : Fin 7 × ℤ, q ∈ EN c ↔ 0 ≤ q.2 ∧ q.2 ≤ Z0 c ∧ ((q.2 : ℝ) - 1 / 8) / p q.1 = b c)
    (hsep : ∀ c c' : Fin m, c < c' → b c + δ c / 2 < a c' - δ c' / 2)
    (H : ℝ) (hH : ∀ c, b c + δ c / 2 ≤ H)
    -- [PROVISIONAL: covering] `hcov` supports: the first lonely instant is the largest exit of the first alive component
    (hcov : ∀ t : ℝ, 0 < t → t ≤ H → (∀ c, ¬ (a c - δ c / 2 ≤ t ∧ t ≤ b c + δ c / 2)) →
      ¬ (∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)))
    (cw : Fin m) (hwide : δ cw / 2 ≤ b cw - a cw) :
    ∃ c₀ : Fin m, Alive (mxOf x EX hEX) (mnOf x EN hEN) c₀ ∧ (∀ c, c < c₀ → ¬ Alive (mxOf x EX hEX) (mnOf x EN hEN) c) ∧
      IsLeast {t : ℝ | 0 < t ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)} (mxOf x EX hEX c₀) := by
  set mx : Fin m → ℝ := fun c => (EX c).sup' (hEX c) (fun q => ((q.2 : ℝ) + 1 / 8) / x q.1) with hmx
  set mn : Fin m → ℝ := fun c => (EN c).inf' (hEN c) (fun q => ((q.2 : ℝ) - 1 / 8) / x q.1) with hmn
  have hε0 : 0 ≤ ε := by
    have := hdev 0
    exact le_trans (abs_nonneg _) this
  have hP4 : 0 < 1 / (4 * P) := by positivity
  have hεhalf : ∀ c : Fin m, ε ≤ 1 / 2 := by
    intro c
    have h1 := hε c
    have h2 := hδ c
    have hZ1 : (1 : ℝ) ≤ (Z0 c : ℝ) := by
      have := hZ c
      have hTpos : 0 < T c := by linarith [hT c, hδ0 c, ha c, hab c]
      have : 0 ≤ (P + 1) * T c := by positivity
      linarith
    have : (1 / (4 * P)) ≤ 1 / 4 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
    nlinarith
  -- every exit and entry lies within δ/4 of its baseline point
  have hexit : ∀ c : Fin m, ∀ q ∈ EX c, |((q.2 : ℝ) + 1 / 8) / x q.1 - a c| ≤ δ c / 4 := by
    intro c q hq
    obtain ⟨h0, h1, h2⟩ := (hEXdef c q).1 hq
    have hedge := edge_pert (c := (q.2 : ℝ) + 1 / 8) (hp q.1).1 (hεhalf c) (hdev q.1)
    rw [h2] at hedge
    have hq0 : (0 : ℝ) ≤ q.2 := by exact_mod_cast h0
    have hqZ : (q.2 : ℝ) ≤ Z0 c := by exact_mod_cast h1
    have habs : |(q.2 : ℝ) + 1 / 8| ≤ (Z0 c : ℝ) + 1 := by
      rw [abs_of_nonneg (by linarith)]; linarith
    have : 2 * |(q.2 : ℝ) + 1 / 8| * ε ≤ δ c / 4 := by
      have := hε c
      nlinarith [mul_le_mul_of_nonneg_right habs hε0]
    linarith
  have hentry : ∀ c : Fin m, ∀ q ∈ EN c, |((q.2 : ℝ) - 1 / 8) / x q.1 - b c| ≤ δ c / 4 := by
    intro c q hq
    obtain ⟨h0, h1, h2⟩ := (hENdef c q).1 hq
    have hedge := edge_pert (c := (q.2 : ℝ) - 1 / 8) (hp q.1).1 (hεhalf c) (hdev q.1)
    rw [h2] at hedge
    have hq0 : (0 : ℝ) ≤ q.2 := by exact_mod_cast h0
    have hqZ : (q.2 : ℝ) ≤ Z0 c := by exact_mod_cast h1
    have habs : |(q.2 : ℝ) - 1 / 8| ≤ (Z0 c : ℝ) + 1 := by
      rw [abs_le]; constructor <;> linarith
    have : 2 * |(q.2 : ℝ) - 1 / 8| * ε ≤ δ c / 4 := by
      have := hε c
      nlinarith [mul_le_mul_of_nonneg_right habs hε0]
    linarith
  have hmx_bd : ∀ c : Fin m, a c - δ c / 4 ≤ mx c ∧ mx c ≤ a c + δ c / 4 := by
    intro c
    obtain ⟨q0, hq0⟩ := hEX c
    constructor
    · have := Finset.le_sup' (fun q : Fin 7 × ℤ => ((q.2 : ℝ) + 1 / 8) / x q.1) hq0
      have h := abs_le.1 (hexit c q0 hq0)
      simp only [hmx]; linarith [h.1]
    · simp only [hmx]
      rw [Finset.sup'_le_iff]
      intro q hq
      have h := abs_le.1 (hexit c q hq)
      linarith [h.2]
  have hmn_bd : ∀ c : Fin m, b c - δ c / 4 ≤ mn c ∧ mn c ≤ b c + δ c / 4 := by
    intro c
    obtain ⟨q0, hq0⟩ := hEN c
    constructor
    · simp only [hmn]
      rw [Finset.le_inf'_iff]
      intro q hq
      have h := abs_le.1 (hentry c q hq)
      linarith [h.1]
    · have := Finset.inf'_le (fun q : Fin 7 × ℤ => ((q.2 : ℝ) - 1 / 8) / x q.1) hq0
      have h := abs_le.1 (hentry c q0 hq0)
      simp only [hmn]; linarith [h.2]
  have hApos : ∀ c : Fin m, 0 < a c - δ c / 2 := fun c => by linarith [ha c, hδ0 c]
  -- the window description
  have hwin : ∀ (c : Fin m) (t : ℝ), a c - δ c / 2 ≤ t → t ≤ b c + δ c / 2 →
      ((0 < t ∧ t ≤ H ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)) ↔ mx c ≤ t ∧ t ≤ mn c) := by
    intro c t h1 h2
    have hW := window_iff_maxminP P hP p x hp ε hdev (a c) (b c) (δ c) (T c) (Z0 c) (hab c) (hδ0 c) (hδ c) (ha c) (hT c)
      (hZ c) (hε c) (fun i z h0 h1 => hcls c i z h0 h1) (EX c) (EN c) (hEX c) (hEN c) (hEXdef c) (hENdef c) t h1 h2
    constructor
    · rintro ⟨_, _, h⟩; exact hW.1 h
    · intro h
      exact ⟨by linarith [hApos c], le_trans h2 (hH c), hW.2 h⟩
  have hmxw : ∀ c : Fin m, Alive mx mn c → (a c - δ c / 2 ≤ mx c ∧ mx c ≤ b c + δ c / 2) := by
    intro c _
    have := hmx_bd c
    have := hab c
    have := hδ0 c
    constructor <;> linarith [(hmx_bd c).1, (hmx_bd c).2]
  have hcov' : ∀ t : ℝ, (0 < t ∧ t ≤ H ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)) →
      ∃ c : Fin m, a c - δ c / 2 ≤ t ∧ t ≤ b c + δ c / 2 := by
    rintro t ⟨h0, hH', hl⟩
    by_contra hne
    push Not at hne
    exact hcov t h0 hH' (fun c hc => absurd (hne c hc.1) (not_lt.2 hc.2)) hl
  have halive : Alive mx mn cw := by
    unfold Alive
    have := (hmx_bd cw).2
    have := (hmn_bd cw).1
    linarith
  obtain ⟨c₀, hc₀, hmin⟩ := (wellFounded_lt (α := Fin m)).has_min {c | Alive mx mn c} ⟨cw, halive⟩
  have hL := landing_rule (fun t => 0 < t ∧ t ≤ H ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t))
    (fun c => a c - δ c / 2) (fun c => b c + δ c / 2) mx mn hsep hwin hcov' hmxw c₀ hc₀ (fun c hc ha => hmin c ha hc)
  obtain ⟨⟨hp0, hpH, hpl⟩, hlow⟩ := hL
  refine ⟨c₀, hc₀, fun c hc ha => hmin c ha hc, ⟨hp0, hpl⟩, fun t ht => ?_⟩
  by_cases htH : t ≤ H
  · exact hlow t ⟨ht.1, htH, ht.2⟩
  · push Not at htH
    show mx c₀ ≤ t
    have := (hmx_bd c₀).2
    have := hab c₀
    have := hH c₀
    have := hδ0 c₀
    linarith

theorem fin7_cases (i : Fin 7) : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 := by
  revert i; decide

/-- A finset equal to a singleton has its `sup'` at the element. -/
theorem sup'_of_eq_singleton {α : Type*} (S : Finset α) (h : S.Nonempty) (q : α) (hS : S = {q}) (f : α → ℝ) :
    S.sup' h f = f q := by
  subst hS; simp

theorem inf'_of_eq_singleton {α : Type*} (S : Finset α) (h : S.Nonempty) (q : α) (hS : S = {q}) (f : α → ℝ) :
    S.inf' h f = f q := by
  subst hS; simp

theorem landing_cert_alive (m : ℕ) (P : ℝ) (hP : 1 ≤ P) (p x : Fin 7 → ℝ) (hp : ∀ i, 1 ≤ p i ∧ p i ≤ P) (ε : ℝ)
    (hdev : ∀ i, |x i - p i| ≤ ε)
    (a b δ T : Fin m → ℝ) (Z0 : Fin m → ℤ)
    (hab : ∀ c, a c ≤ b c) (hδ0 : ∀ c, 0 < δ c) (hδ : ∀ c, δ c ≤ 1 / (4 * P)) (ha : ∀ c, δ c < a c)
    (hT : ∀ c, b c + δ c ≤ T c) (hZ : ∀ c, (P + 1) * T c + 1 ≤ (Z0 c : ℝ))
    (hε : ∀ c, 8 * ((Z0 c : ℝ) + 1) * ε ≤ δ c)
    (hcls : ∀ c i, ∀ z : ℤ, 0 ≤ z → z ≤ Z0 c →
      ((z : ℝ) + 1 / 8) / p i ≤ a c - δ c ∨ b c + δ c ≤ ((z : ℝ) - 1 / 8) / p i ∨
        ((z : ℝ) + 1 / 8) / p i = a c ∨ ((z : ℝ) - 1 / 8) / p i = b c)
    (EX EN : Fin m → Finset (Fin 7 × ℤ)) (hEX : ∀ c, (EX c).Nonempty) (hEN : ∀ c, (EN c).Nonempty)
    (hEXdef : ∀ c, ∀ q : Fin 7 × ℤ, q ∈ EX c ↔ 0 ≤ q.2 ∧ q.2 ≤ Z0 c ∧ ((q.2 : ℝ) + 1 / 8) / p q.1 = a c)
    (hENdef : ∀ c, ∀ q : Fin 7 × ℤ, q ∈ EN c ↔ 0 ≤ q.2 ∧ q.2 ≤ Z0 c ∧ ((q.2 : ℝ) - 1 / 8) / p q.1 = b c)
    (hsep : ∀ c c' : Fin m, c < c' → b c + δ c / 2 < a c' - δ c' / 2)
    (H : ℝ) (hH : ∀ c, b c + δ c / 2 ≤ H)
    -- [PROVISIONAL: covering] `hcov` supports: the first lonely instant is the largest exit of the first alive component
    (hcov : ∀ t : ℝ, 0 < t → t ≤ H → (∀ c, ¬ (a c - δ c / 2 ≤ t ∧ t ≤ b c + δ c / 2)) →
      ¬ (∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)))
    (hex : ∃ c : Fin m, Alive (mxOf x EX hEX) (mnOf x EN hEN) c) :
    ∃ c₀ : Fin m, Alive (mxOf x EX hEX) (mnOf x EN hEN) c₀ ∧ (∀ c, c < c₀ → ¬ Alive (mxOf x EX hEX) (mnOf x EN hEN) c) ∧
      IsLeast {t : ℝ | 0 < t ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)} (mxOf x EX hEX c₀) := by
  set mx : Fin m → ℝ := fun c => (EX c).sup' (hEX c) (fun q => ((q.2 : ℝ) + 1 / 8) / x q.1) with hmx
  set mn : Fin m → ℝ := fun c => (EN c).inf' (hEN c) (fun q => ((q.2 : ℝ) - 1 / 8) / x q.1) with hmn
  have hε0 : 0 ≤ ε := by
    have := hdev 0
    exact le_trans (abs_nonneg _) this
  have hP4 : 0 < 1 / (4 * P) := by positivity
  have hεhalf : ∀ c : Fin m, ε ≤ 1 / 2 := by
    intro c
    have h1 := hε c
    have h2 := hδ c
    have hZ1 : (1 : ℝ) ≤ (Z0 c : ℝ) := by
      have := hZ c
      have hTpos : 0 < T c := by linarith [hT c, hδ0 c, ha c, hab c]
      have : 0 ≤ (P + 1) * T c := by positivity
      linarith
    have : (1 / (4 * P)) ≤ 1 / 4 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
    nlinarith
  -- every exit and entry lies within δ/4 of its baseline point
  have hexit : ∀ c : Fin m, ∀ q ∈ EX c, |((q.2 : ℝ) + 1 / 8) / x q.1 - a c| ≤ δ c / 4 := by
    intro c q hq
    obtain ⟨h0, h1, h2⟩ := (hEXdef c q).1 hq
    have hedge := edge_pert (c := (q.2 : ℝ) + 1 / 8) (hp q.1).1 (hεhalf c) (hdev q.1)
    rw [h2] at hedge
    have hq0 : (0 : ℝ) ≤ q.2 := by exact_mod_cast h0
    have hqZ : (q.2 : ℝ) ≤ Z0 c := by exact_mod_cast h1
    have habs : |(q.2 : ℝ) + 1 / 8| ≤ (Z0 c : ℝ) + 1 := by
      rw [abs_of_nonneg (by linarith)]; linarith
    have : 2 * |(q.2 : ℝ) + 1 / 8| * ε ≤ δ c / 4 := by
      have := hε c
      nlinarith [mul_le_mul_of_nonneg_right habs hε0]
    linarith
  have hentry : ∀ c : Fin m, ∀ q ∈ EN c, |((q.2 : ℝ) - 1 / 8) / x q.1 - b c| ≤ δ c / 4 := by
    intro c q hq
    obtain ⟨h0, h1, h2⟩ := (hENdef c q).1 hq
    have hedge := edge_pert (c := (q.2 : ℝ) - 1 / 8) (hp q.1).1 (hεhalf c) (hdev q.1)
    rw [h2] at hedge
    have hq0 : (0 : ℝ) ≤ q.2 := by exact_mod_cast h0
    have hqZ : (q.2 : ℝ) ≤ Z0 c := by exact_mod_cast h1
    have habs : |(q.2 : ℝ) - 1 / 8| ≤ (Z0 c : ℝ) + 1 := by
      rw [abs_le]; constructor <;> linarith
    have : 2 * |(q.2 : ℝ) - 1 / 8| * ε ≤ δ c / 4 := by
      have := hε c
      nlinarith [mul_le_mul_of_nonneg_right habs hε0]
    linarith
  have hmx_bd : ∀ c : Fin m, a c - δ c / 4 ≤ mx c ∧ mx c ≤ a c + δ c / 4 := by
    intro c
    obtain ⟨q0, hq0⟩ := hEX c
    constructor
    · have := Finset.le_sup' (fun q : Fin 7 × ℤ => ((q.2 : ℝ) + 1 / 8) / x q.1) hq0
      have h := abs_le.1 (hexit c q0 hq0)
      simp only [hmx]; linarith [h.1]
    · simp only [hmx]
      rw [Finset.sup'_le_iff]
      intro q hq
      have h := abs_le.1 (hexit c q hq)
      linarith [h.2]
  have hmn_bd : ∀ c : Fin m, b c - δ c / 4 ≤ mn c ∧ mn c ≤ b c + δ c / 4 := by
    intro c
    obtain ⟨q0, hq0⟩ := hEN c
    constructor
    · simp only [hmn]
      rw [Finset.le_inf'_iff]
      intro q hq
      have h := abs_le.1 (hentry c q hq)
      linarith [h.1]
    · have := Finset.inf'_le (fun q : Fin 7 × ℤ => ((q.2 : ℝ) - 1 / 8) / x q.1) hq0
      have h := abs_le.1 (hentry c q0 hq0)
      simp only [hmn]; linarith [h.2]
  have hApos : ∀ c : Fin m, 0 < a c - δ c / 2 := fun c => by linarith [ha c, hδ0 c]
  -- the window description
  have hwin : ∀ (c : Fin m) (t : ℝ), a c - δ c / 2 ≤ t → t ≤ b c + δ c / 2 →
      ((0 < t ∧ t ≤ H ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)) ↔ mx c ≤ t ∧ t ≤ mn c) := by
    intro c t h1 h2
    have hW := window_iff_maxminP P hP p x hp ε hdev (a c) (b c) (δ c) (T c) (Z0 c) (hab c) (hδ0 c) (hδ c) (ha c) (hT c)
      (hZ c) (hε c) (fun i z h0 h1 => hcls c i z h0 h1) (EX c) (EN c) (hEX c) (hEN c) (hEXdef c) (hENdef c) t h1 h2
    constructor
    · rintro ⟨_, _, h⟩; exact hW.1 h
    · intro h
      exact ⟨by linarith [hApos c], le_trans h2 (hH c), hW.2 h⟩
  have hmxw : ∀ c : Fin m, Alive mx mn c → (a c - δ c / 2 ≤ mx c ∧ mx c ≤ b c + δ c / 2) := by
    intro c _
    have := hmx_bd c
    have := hab c
    have := hδ0 c
    constructor <;> linarith [(hmx_bd c).1, (hmx_bd c).2]
  have hcov' : ∀ t : ℝ, (0 < t ∧ t ≤ H ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)) →
      ∃ c : Fin m, a c - δ c / 2 ≤ t ∧ t ≤ b c + δ c / 2 := by
    rintro t ⟨h0, hH', hl⟩
    by_contra hne
    push Not at hne
    exact hcov t h0 hH' (fun c hc => absurd (hne c hc.1) (not_lt.2 hc.2)) hl
  obtain ⟨c₀, hc₀, hmin⟩ := (wellFounded_lt (α := Fin m)).has_min {c | Alive mx mn c} hex
  have hL := landing_rule (fun t => 0 < t ∧ t ≤ H ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t))
    (fun c => a c - δ c / 2) (fun c => b c + δ c / 2) mx mn hsep hwin hcov' hmxw c₀ hc₀ (fun c hc ha => hmin c ha hc)
  obtain ⟨⟨hp0, hpH, hpl⟩, hlow⟩ := hL
  refine ⟨c₀, hc₀, fun c hc ha => hmin c ha hc, ⟨hp0, hpl⟩, fun t ht => ?_⟩
  by_cases htH : t ≤ H
  · exact hlow t ⟨ht.1, htH, ht.2⟩
  · push Not at htH
    show mx c₀ ≤ t
    have := (hmx_bd c₀).2
    have := hab c₀
    have := hH c₀
    have := hδ0 c₀
    linarith

/-- A baseline zone with margin `μ` kills every `t ≤ H` strictly inside it, for readings within `ε` with `ε H ≤ μ / 2`. -/
theorem zone_kill_gen (p x : Fin 7 → ℝ) (ε H μ : ℝ) (hp : ∀ i, 1 ≤ p i) (hdev : ∀ i, |x i - p i| ≤ ε)
    (hεH : ε * H ≤ μ / 2) (hμ : 0 < μ) (i : Fin 7) (z : ℤ) (t : ℝ) (h0 : 0 ≤ t) (htH : t ≤ H)
    (h1 : (8 * (z : ℝ) - 1) / (8 * p i) + μ ≤ t) (h2 : t ≤ (8 * (z : ℝ) + 1) / (8 * p i) - μ) :
    ¬ ((1 / 8 : ℝ) ≤ distInt (x i * t)) := by
  intro hk
  have hpi := hp i
  have hpos : (0 : ℝ) < p i := by linarith
  have hd := abs_le.1 (hdev i)
  have hε0 : 0 ≤ ε := le_trans (abs_nonneg _) (hdev i)
  have e1 : (8 * (z : ℝ) - 1) / (8 * p i) = ((z : ℝ) - 1 / 8) / p i := by field_simp
  have e2 : (8 * (z : ℝ) + 1) / (8 * p i) = ((z : ℝ) + 1 / 8) / p i := by field_simp
  rw [e1] at h1
  rw [e2] at h2
  have l1 := (div_le_iff₀ hpos).mp (by linarith : ((z : ℝ) - 1 / 8) / p i ≤ t - μ)
  have l2 := (le_div_iff₀ hpos).mp (by linarith : t + μ ≤ ((z : ℝ) + 1 / 8) / p i)
  have a1 : (x i - p i) * t ≤ ε * t := mul_le_mul_of_nonneg_right hd.2 h0
  have a2 : -(ε * t) ≤ (x i - p i) * t := by nlinarith [hd.1]
  have a3 : ε * t ≤ ε * H := mul_le_mul_of_nonneg_left htH hε0
  have hlt : |x i * t - z| < 1 / 8 := by
    rw [abs_lt]
    constructor <;> nlinarith
  have := Fresh.Localisation.distInt_le (x i * t) z
  linarith

/-- Isolation read on the seven disparities (signs do not matter). -/
theorem iso_iff_readings (v : Fin 8 → ℝ) (k : Fin 8) (σ : Fin 7 → Fin 8) (hσk : ∀ i, σ i ≠ k)
    (hσ : ∀ j, j ≠ k → ∃ i, σ i = j) (t : ℝ) :
    IsolatedAt v k t ↔ ∀ i, (1 / 8 : ℝ) ≤ distInt (|v (σ i) - v k| * t) := by
  constructor
  · intro h i
    rw [Fresh.Localisation.distInt_abs_mul]; exact h (σ i) (hσk i)
  · intro h j hj
    obtain ⟨i, rfl⟩ := hσ j hj
    have := h i
    rwa [Fresh.Localisation.distInt_abs_mul] at this

theorem reading_dev (v : Fin 8 → ℝ) (s : Fin 8 → ℝ) (η : ℝ) (hv : ∀ j, |v j - s j| ≤ η) (j k : Fin 8) :
    |(|v j - v k| - |s j - s k|)| ≤ 2 * η := by
  have h1 := abs_le.1 (hv j)
  have h2 := abs_le.1 (hv k)
  have := abs_abs_sub_abs_le_abs_sub (v j - v k) (s j - s k)
  have h3 : |(v j - v k) - (s j - s k)| ≤ 2 * η := by
    rw [abs_le]; constructor <;> linarith
  linarith

#print axioms landing_cert
#print axioms landing_cert_alive
#print axioms zone_kill_gen
#print axioms iso_iff_readings
#print axioms reading_dev

end Fresh.LandingCert
