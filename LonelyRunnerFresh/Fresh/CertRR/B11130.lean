import Mathlib
import Fresh.Framework
import Fresh.Localisation
import Fresh.LandingCert

/-!
# Landing certificate `CertRR.R11130`: speeds (1, 2, 5, 11, 12, 13, 14, 15), subject index 2

Generated 2026-10-24 by `experiments/n8/cert_gen_v1.py` (exact Fractions).  Baseline readings [4, 3, 6, 7, 8, 9, 10].  Components up to the first wide one: 1.
Radius: speeds within `η ≤ 1/6584` of the baseline speeds, giving `ε = 2η ≤ 1/3292`.  Covering margin `μ = 1/256`.
`hcov` is **[PROVISIONAL: covering]**, supporting the claim that the first lonely instant of this subject is the largest exit of the first alive component.
Result `inst_arr`: for such `v`, the subject has a first isolation (a least element over all `t > 0`).  Grades: [L].
-/

open Classical

namespace Fresh.CertRR.R11130

open Fresh Fresh.LandingCert Fresh.LandingRule

noncomputable def pr : Fin 7 → ℝ := ![(4 : ℝ), (3 : ℝ), (6 : ℝ), (7 : ℝ), (8 : ℝ), (9 : ℝ), (10 : ℝ)]
noncomputable def aV : Fin 1 → ℝ := ![(1 / 24 : ℝ)]
noncomputable def bV : Fin 1 → ℝ := ![(7 / 80 : ℝ)]
noncomputable def dV : Fin 1 → ℝ := ![(7 / 720 : ℝ)]
noncomputable def TV : Fin 1 → ℝ := ![(7 / 72 : ℝ)]
def ZV : Fin 1 → ℤ := ![3]
noncomputable def HV : ℝ := (133 / 1440 : ℝ)
noncomputable def EXs (c : Fin 1) : Finset (Fin 7 × ℤ) :=
  (Finset.univ ×ˢ Finset.Icc 0 (ZV c)).filter (fun q => ((q.2 : ℝ) + 1 / 8) / pr q.1 = aV c)
noncomputable def ENs (c : Fin 1) : Finset (Fin 7 × ℤ) :=
  (Finset.univ ×ˢ Finset.Icc 0 (ZV c)).filter (fun q => ((q.2 : ℝ) - 1 / 8) / pr q.1 = bV c)

theorem hp : ∀ i, 1 ≤ pr i ∧ pr i ≤ (10 : ℝ) := by intro i; fin_cases i <;> norm_num [pr]
theorem hp1 : ∀ i, 1 ≤ pr i := fun i => (hp i).1
theorem pr_0 : pr (0 : Fin 7) = (4 : ℝ) := rfl
theorem pr_1 : pr (1 : Fin 7) = (3 : ℝ) := rfl
theorem pr_2 : pr (2 : Fin 7) = (6 : ℝ) := rfl
theorem pr_3 : pr (3 : Fin 7) = (7 : ℝ) := rfl
theorem pr_4 : pr (4 : Fin 7) = (8 : ℝ) := rfl
theorem pr_5 : pr (5 : Fin 7) = (9 : ℝ) := rfl
theorem pr_6 : pr (6 : Fin 7) = (10 : ℝ) := rfl
theorem aV_0 : aV (0 : Fin 1) = (1 / 24 : ℝ) := rfl
theorem bV_0 : bV (0 : Fin 1) = (7 / 80 : ℝ) := rfl
theorem dV_0 : dV (0 : Fin 1) = (7 / 720 : ℝ) := rfl
theorem TV_0 : TV (0 : Fin 1) = (7 / 72 : ℝ) := rfl
theorem ZV_0 : ZV (0 : Fin 1) = (3 : ℤ) := rfl
theorem hab : ∀ c, aV c ≤ bV c := by intro c; fin_cases c <;> norm_num [aV, bV]
theorem hd0 : ∀ c, 0 < dV c := by intro c; fin_cases c <;> norm_num [dV]
theorem hdP : ∀ c, dV c ≤ 1 / (4 * (10 : ℝ)) := by intro c; fin_cases c <;> norm_num [dV]
theorem haP : ∀ c, dV c < aV c := by intro c; fin_cases c <;> norm_num [dV, aV]
theorem hT : ∀ c, bV c + dV c ≤ TV c := by intro c; fin_cases c <;> norm_num [bV, dV, TV]
theorem hZ : ∀ c, ((10 : ℝ) + 1) * TV c + 1 ≤ (ZV c : ℝ) := by intro c; fin_cases c <;> norm_num [TV, ZV]
theorem hE (ε : ℝ) (hε : ε ≤ (1 / 3292 : ℝ)) : ∀ c, 8 * ((ZV c : ℝ) + 1) * ε ≤ dV c := by
  intro c; fin_cases c <;> norm_num [ZV, dV] <;> linarith
theorem hcls : ∀ c i, ∀ z : ℤ, 0 ≤ z → z ≤ ZV c →
    ((z : ℝ) + 1 / 8) / pr i ≤ aV c - dV c ∨ bV c + dV c ≤ ((z : ℝ) - 1 / 8) / pr i ∨
      ((z : ℝ) + 1 / 8) / pr i = aV c ∨ ((z : ℝ) - 1 / 8) / pr i = bV c := by
  intro c i z h0 h1
  fin_cases c <;> fin_cases i <;> simp [ZV] at h1 <;> interval_cases z <;> norm_num [pr, aV, bV, dV]
theorem hEXne : ∀ c, (EXs c).Nonempty := by
  intro c
  fin_cases c
  · exact ⟨(1, 0), by simp [EXs, ZV, pr, aV] <;> norm_num⟩
theorem hENne : ∀ c, (ENs c).Nonempty := by
  intro c
  fin_cases c
  · exact ⟨(6, 1), by simp [ENs, ZV, pr, bV] <;> norm_num⟩
theorem hEXdef : ∀ c, ∀ q : Fin 7 × ℤ, q ∈ EXs c ↔ 0 ≤ q.2 ∧ q.2 ≤ ZV c ∧ ((q.2 : ℝ) + 1 / 8) / pr q.1 = aV c := by
  intro c q
  simp only [EXs, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, Finset.mem_Icc, true_and]
  tauto
theorem hENdef : ∀ c, ∀ q : Fin 7 × ℤ, q ∈ ENs c ↔ 0 ≤ q.2 ∧ q.2 ≤ ZV c ∧ ((q.2 : ℝ) - 1 / 8) / pr q.1 = bV c := by
  intro c q
  simp only [ENs, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, Finset.mem_Icc, true_and]
  tauto
theorem hsepL : ∀ c c' : Fin 1, c < c' → bV c + dV c / 2 < aV c' - dV c' / 2 := by
  intro c c' h
  fin_cases c <;> fin_cases c' <;> simp at h ⊢ <;> norm_num [aV, bV, dV]
theorem hHL : ∀ c, bV c + dV c / 2 ≤ HV := by intro c; fin_cases c <;> norm_num [bV, dV, HV]

theorem gap0 (x : Fin 7 → ℝ) (ε : ℝ) (hdev : ∀ i, |x i - pr i| ≤ ε) (hεH : ε * HV ≤ (1 / 256 : ℝ) / 2) (t : ℝ) (h0 : 0 ≤ t)
    (hHt : t ≤ HV) (h1 : (0 : ℝ) ≤ t) (h2 : t ≤ (53 / 1440 : ℝ)) (hlon : ∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)) : False := by
  exact zone_kill_gen pr x ε HV (1 / 256 : ℝ) hp1 hdev hεH (by norm_num) (1 : Fin 7) 0 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (1 : Fin 7))
theorem cov (x : Fin 7 → ℝ) (ε : ℝ) (hε : ε ≤ (1 / 3292 : ℝ)) (hdev : ∀ i, |x i - pr i| ≤ ε) :
    ∀ t : ℝ, 0 < t → t ≤ HV → (∀ c, ¬ (aV c - dV c / 2 ≤ t ∧ t ≤ bV c + dV c / 2)) →
      ¬ (∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)) := by
  intro t h0 hHt hnone hlon
  have hεH : ε * HV ≤ (1 / 256 : ℝ) / 2 := by
    have hε0 : 0 ≤ ε := le_trans (abs_nonneg _) (hdev 0)
    have : ε * HV ≤ (1 / 3292 : ℝ) * HV := mul_le_mul_of_nonneg_right hε (by norm_num [HV])
    have h2 : (1 / 3292 : ℝ) * HV ≤ (1 / 256 : ℝ) / 2 := by norm_num [HV]
    linarith
  have n0 := hnone (0 : Fin 1)
  rw [aV_0, bV_0, dV_0] at n0
  rcases lt_or_ge t (53 / 1440 : ℝ) with c0 | c0
  · exact gap0 x ε hdev hεH t h0.le hHt h0.le (by linarith) hlon
  have d0 : (133 / 1440 : ℝ) < t := by
    by_contra hc; push Not at hc; exact n0 ⟨by linarith, by linarith⟩
  have hHv : HV = (133 / 1440 : ℝ) := rfl
  exact absurd (by linarith : t ≤ (133 / 1440 : ℝ)) (not_le.2 d0)

theorem inst (x : Fin 7 → ℝ) (ε : ℝ) (hε : ε ≤ (1 / 3292 : ℝ)) (hdev : ∀ i, |x i - pr i| ≤ ε) :
    ∃ c₀ : Fin 1, Alive (mxOf x EXs hEXne) (mnOf x ENs hENne) c₀ ∧
      (∀ c, c < c₀ → ¬ Alive (mxOf x EXs hEXne) (mnOf x ENs hENne) c) ∧
      IsLeast {t : ℝ | 0 < t ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)} (mxOf x EXs hEXne c₀) :=
  landing_cert 1 (10 : ℝ) (by norm_num) pr x hp ε hdev aV bV dV TV ZV hab hd0 hdP haP hT hZ (hE ε hε) hcls EXs ENs hEXne hENne
    hEXdef hENdef hsepL HV hHL (cov x ε hε hdev) (0 : Fin 1) (by rw [dV_0, bV_0, aV_0]; norm_num)

noncomputable def sv : Fin 8 → ℝ := ![(1 : ℝ), (2 : ℝ), (5 : ℝ), (11 : ℝ), (12 : ℝ), (13 : ℝ), (14 : ℝ), (15 : ℝ)]
def sg : Fin 7 → Fin 8 := ![0, 1, 3, 4, 5, 6, 7]

theorem sv_0 : sv (0 : Fin 8) = (1 : ℝ) := rfl
theorem sv_1 : sv (1 : Fin 8) = (2 : ℝ) := rfl
theorem sv_2 : sv (2 : Fin 8) = (5 : ℝ) := rfl
theorem sv_3 : sv (3 : Fin 8) = (11 : ℝ) := rfl
theorem sv_4 : sv (4 : Fin 8) = (12 : ℝ) := rfl
theorem sv_5 : sv (5 : Fin 8) = (13 : ℝ) := rfl
theorem sv_6 : sv (6 : Fin 8) = (14 : ℝ) := rfl
theorem sv_7 : sv (7 : Fin 8) = (15 : ℝ) := rfl
theorem sg_0 : sg (0 : Fin 7) = (0 : Fin 8) := rfl
theorem sg_1 : sg (1 : Fin 7) = (1 : Fin 8) := rfl
theorem sg_2 : sg (2 : Fin 7) = (3 : Fin 8) := rfl
theorem sg_3 : sg (3 : Fin 7) = (4 : Fin 8) := rfl
theorem sg_4 : sg (4 : Fin 7) = (5 : Fin 8) := rfl
theorem sg_5 : sg (5 : Fin 7) = (6 : Fin 8) := rfl
theorem sg_6 : sg (6 : Fin 7) = (7 : Fin 8) := rfl

theorem inst_arr (v : Fin 8 → ℝ) (η : ℝ) (hη : η ≤ (1 / 6584 : ℝ)) (hv : ∀ j, |v j - sv j| ≤ η) :
    ∃ c₀ : Fin 1, Alive (mxOf (fun i => |v (sg i) - v (2 : Fin 8)|) EXs hEXne) (mnOf (fun i => |v (sg i) - v (2 : Fin 8)|) ENs hENne) c₀ ∧
      (∀ c, c < c₀ → ¬ Alive (mxOf (fun i => |v (sg i) - v (2 : Fin 8)|) EXs hEXne) (mnOf (fun i => |v (sg i) - v (2 : Fin 8)|) ENs hENne) c) ∧
      IsLeast {t : ℝ | 0 < t ∧ IsolatedAt v (2 : Fin 8) t} (mxOf (fun i => |v (sg i) - v (2 : Fin 8)|) EXs hEXne c₀) := by
  have hσk : ∀ i, sg i ≠ (2 : Fin 8) := by decide
  have hσ : ∀ j : Fin 8, j ≠ (2 : Fin 8) → ∃ i, sg i = j := by decide
  have hpr : ∀ i, pr i = |sv (sg i) - sv (2 : Fin 8)| := by
    intro i; rcases fin7_cases i with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6, sv_0, sv_1, sv_2, sv_3, sv_4, sv_5, sv_6, sv_7, sg_0, sg_1, sg_2, sg_3, sg_4, sg_5, sg_6]
  have hdev : ∀ i, |(|v (sg i) - v (2 : Fin 8)| - pr i)| ≤ 2 * η := by
    intro i; rw [hpr i]; exact reading_dev v sv η hv (sg i) (2 : Fin 8)
  obtain ⟨c₀, hal, hbf, hT0⟩ := inst (fun i => |v (sg i) - v (2 : Fin 8)|) (2 * η) (by linarith) hdev
  have hset : {t : ℝ | 0 < t ∧ IsolatedAt v (2 : Fin 8) t} =
      {t : ℝ | 0 < t ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (|v (sg i) - v (2 : Fin 8)| * t)} := by
    ext t; simp only [Set.mem_setOf_eq]; rw [iso_iff_readings v (2 : Fin 8) sg hσk hσ t]
  rw [hset]; exact ⟨c₀, hal, hbf, hT0⟩

#print axioms inst_arr

end Fresh.CertRR.R11130



/-!
# Landing certificate `CertRR.R11138`: speeds (1, 2, 5, 11, 12, 13, 15, 16), subject index 2

Generated 2026-10-24 by `experiments/n8/cert_gen_v1.py` (exact Fractions).  Baseline readings [4, 3, 6, 7, 8, 10, 11].  Components up to the first wide one: 1.
Radius: speeds within `η ≤ 1/8046` of the baseline speeds, giving `ε = 2η ≤ 1/4023`.  Covering margin `μ = 1/256`.
`hcov` is **[PROVISIONAL: covering]**, supporting the claim that the first lonely instant of this subject is the largest exit of the first alive component.
Result `inst_arr`: for such `v`, the subject has a first isolation (a least element over all `t > 0`).  Grades: [L].
-/

open Classical

namespace Fresh.CertRR.R11138

open Fresh Fresh.LandingCert Fresh.LandingRule

noncomputable def pr : Fin 7 → ℝ := ![(4 : ℝ), (3 : ℝ), (6 : ℝ), (7 : ℝ), (8 : ℝ), (10 : ℝ), (11 : ℝ)]
noncomputable def aV : Fin 1 → ℝ := ![(1 / 24 : ℝ)]
noncomputable def bV : Fin 1 → ℝ := ![(7 / 88 : ℝ)]
noncomputable def dV : Fin 1 → ℝ := ![(7 / 880 : ℝ)]
noncomputable def TV : Fin 1 → ℝ := ![(7 / 80 : ℝ)]
def ZV : Fin 1 → ℤ := ![3]
noncomputable def HV : ℝ := (147 / 1760 : ℝ)
noncomputable def EXs (c : Fin 1) : Finset (Fin 7 × ℤ) :=
  (Finset.univ ×ˢ Finset.Icc 0 (ZV c)).filter (fun q => ((q.2 : ℝ) + 1 / 8) / pr q.1 = aV c)
noncomputable def ENs (c : Fin 1) : Finset (Fin 7 × ℤ) :=
  (Finset.univ ×ˢ Finset.Icc 0 (ZV c)).filter (fun q => ((q.2 : ℝ) - 1 / 8) / pr q.1 = bV c)

theorem hp : ∀ i, 1 ≤ pr i ∧ pr i ≤ (11 : ℝ) := by intro i; fin_cases i <;> norm_num [pr]
theorem hp1 : ∀ i, 1 ≤ pr i := fun i => (hp i).1
theorem pr_0 : pr (0 : Fin 7) = (4 : ℝ) := rfl
theorem pr_1 : pr (1 : Fin 7) = (3 : ℝ) := rfl
theorem pr_2 : pr (2 : Fin 7) = (6 : ℝ) := rfl
theorem pr_3 : pr (3 : Fin 7) = (7 : ℝ) := rfl
theorem pr_4 : pr (4 : Fin 7) = (8 : ℝ) := rfl
theorem pr_5 : pr (5 : Fin 7) = (10 : ℝ) := rfl
theorem pr_6 : pr (6 : Fin 7) = (11 : ℝ) := rfl
theorem aV_0 : aV (0 : Fin 1) = (1 / 24 : ℝ) := rfl
theorem bV_0 : bV (0 : Fin 1) = (7 / 88 : ℝ) := rfl
theorem dV_0 : dV (0 : Fin 1) = (7 / 880 : ℝ) := rfl
theorem TV_0 : TV (0 : Fin 1) = (7 / 80 : ℝ) := rfl
theorem ZV_0 : ZV (0 : Fin 1) = (3 : ℤ) := rfl
theorem hab : ∀ c, aV c ≤ bV c := by intro c; fin_cases c <;> norm_num [aV, bV]
theorem hd0 : ∀ c, 0 < dV c := by intro c; fin_cases c <;> norm_num [dV]
theorem hdP : ∀ c, dV c ≤ 1 / (4 * (11 : ℝ)) := by intro c; fin_cases c <;> norm_num [dV]
theorem haP : ∀ c, dV c < aV c := by intro c; fin_cases c <;> norm_num [dV, aV]
theorem hT : ∀ c, bV c + dV c ≤ TV c := by intro c; fin_cases c <;> norm_num [bV, dV, TV]
theorem hZ : ∀ c, ((11 : ℝ) + 1) * TV c + 1 ≤ (ZV c : ℝ) := by intro c; fin_cases c <;> norm_num [TV, ZV]
theorem hE (ε : ℝ) (hε : ε ≤ (1 / 4023 : ℝ)) : ∀ c, 8 * ((ZV c : ℝ) + 1) * ε ≤ dV c := by
  intro c; fin_cases c <;> norm_num [ZV, dV] <;> linarith
theorem hcls : ∀ c i, ∀ z : ℤ, 0 ≤ z → z ≤ ZV c →
    ((z : ℝ) + 1 / 8) / pr i ≤ aV c - dV c ∨ bV c + dV c ≤ ((z : ℝ) - 1 / 8) / pr i ∨
      ((z : ℝ) + 1 / 8) / pr i = aV c ∨ ((z : ℝ) - 1 / 8) / pr i = bV c := by
  intro c i z h0 h1
  fin_cases c <;> fin_cases i <;> simp [ZV] at h1 <;> interval_cases z <;> norm_num [pr, aV, bV, dV]
theorem hEXne : ∀ c, (EXs c).Nonempty := by
  intro c
  fin_cases c
  · exact ⟨(1, 0), by simp [EXs, ZV, pr, aV] <;> norm_num⟩
theorem hENne : ∀ c, (ENs c).Nonempty := by
  intro c
  fin_cases c
  · exact ⟨(6, 1), by simp [ENs, ZV, pr, bV] <;> norm_num⟩
theorem hEXdef : ∀ c, ∀ q : Fin 7 × ℤ, q ∈ EXs c ↔ 0 ≤ q.2 ∧ q.2 ≤ ZV c ∧ ((q.2 : ℝ) + 1 / 8) / pr q.1 = aV c := by
  intro c q
  simp only [EXs, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, Finset.mem_Icc, true_and]
  tauto
theorem hENdef : ∀ c, ∀ q : Fin 7 × ℤ, q ∈ ENs c ↔ 0 ≤ q.2 ∧ q.2 ≤ ZV c ∧ ((q.2 : ℝ) - 1 / 8) / pr q.1 = bV c := by
  intro c q
  simp only [ENs, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, Finset.mem_Icc, true_and]
  tauto
theorem hsepL : ∀ c c' : Fin 1, c < c' → bV c + dV c / 2 < aV c' - dV c' / 2 := by
  intro c c' h
  fin_cases c <;> fin_cases c' <;> simp at h ⊢ <;> norm_num [aV, bV, dV]
theorem hHL : ∀ c, bV c + dV c / 2 ≤ HV := by intro c; fin_cases c <;> norm_num [bV, dV, HV]

theorem gap0 (x : Fin 7 → ℝ) (ε : ℝ) (hdev : ∀ i, |x i - pr i| ≤ ε) (hεH : ε * HV ≤ (1 / 256 : ℝ) / 2) (t : ℝ) (h0 : 0 ≤ t)
    (hHt : t ≤ HV) (h1 : (0 : ℝ) ≤ t) (h2 : t ≤ (199 / 5280 : ℝ)) (hlon : ∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)) : False := by
  exact zone_kill_gen pr x ε HV (1 / 256 : ℝ) hp1 hdev hεH (by norm_num) (1 : Fin 7) 0 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (1 : Fin 7))
theorem cov (x : Fin 7 → ℝ) (ε : ℝ) (hε : ε ≤ (1 / 4023 : ℝ)) (hdev : ∀ i, |x i - pr i| ≤ ε) :
    ∀ t : ℝ, 0 < t → t ≤ HV → (∀ c, ¬ (aV c - dV c / 2 ≤ t ∧ t ≤ bV c + dV c / 2)) →
      ¬ (∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)) := by
  intro t h0 hHt hnone hlon
  have hεH : ε * HV ≤ (1 / 256 : ℝ) / 2 := by
    have hε0 : 0 ≤ ε := le_trans (abs_nonneg _) (hdev 0)
    have : ε * HV ≤ (1 / 4023 : ℝ) * HV := mul_le_mul_of_nonneg_right hε (by norm_num [HV])
    have h2 : (1 / 4023 : ℝ) * HV ≤ (1 / 256 : ℝ) / 2 := by norm_num [HV]
    linarith
  have n0 := hnone (0 : Fin 1)
  rw [aV_0, bV_0, dV_0] at n0
  rcases lt_or_ge t (199 / 5280 : ℝ) with c0 | c0
  · exact gap0 x ε hdev hεH t h0.le hHt h0.le (by linarith) hlon
  have d0 : (147 / 1760 : ℝ) < t := by
    by_contra hc; push Not at hc; exact n0 ⟨by linarith, by linarith⟩
  have hHv : HV = (147 / 1760 : ℝ) := rfl
  exact absurd (by linarith : t ≤ (147 / 1760 : ℝ)) (not_le.2 d0)

theorem inst (x : Fin 7 → ℝ) (ε : ℝ) (hε : ε ≤ (1 / 4023 : ℝ)) (hdev : ∀ i, |x i - pr i| ≤ ε) :
    ∃ c₀ : Fin 1, Alive (mxOf x EXs hEXne) (mnOf x ENs hENne) c₀ ∧
      (∀ c, c < c₀ → ¬ Alive (mxOf x EXs hEXne) (mnOf x ENs hENne) c) ∧
      IsLeast {t : ℝ | 0 < t ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)} (mxOf x EXs hEXne c₀) :=
  landing_cert 1 (11 : ℝ) (by norm_num) pr x hp ε hdev aV bV dV TV ZV hab hd0 hdP haP hT hZ (hE ε hε) hcls EXs ENs hEXne hENne
    hEXdef hENdef hsepL HV hHL (cov x ε hε hdev) (0 : Fin 1) (by rw [dV_0, bV_0, aV_0]; norm_num)

noncomputable def sv : Fin 8 → ℝ := ![(1 : ℝ), (2 : ℝ), (5 : ℝ), (11 : ℝ), (12 : ℝ), (13 : ℝ), (15 : ℝ), (16 : ℝ)]
def sg : Fin 7 → Fin 8 := ![0, 1, 3, 4, 5, 6, 7]

theorem sv_0 : sv (0 : Fin 8) = (1 : ℝ) := rfl
theorem sv_1 : sv (1 : Fin 8) = (2 : ℝ) := rfl
theorem sv_2 : sv (2 : Fin 8) = (5 : ℝ) := rfl
theorem sv_3 : sv (3 : Fin 8) = (11 : ℝ) := rfl
theorem sv_4 : sv (4 : Fin 8) = (12 : ℝ) := rfl
theorem sv_5 : sv (5 : Fin 8) = (13 : ℝ) := rfl
theorem sv_6 : sv (6 : Fin 8) = (15 : ℝ) := rfl
theorem sv_7 : sv (7 : Fin 8) = (16 : ℝ) := rfl
theorem sg_0 : sg (0 : Fin 7) = (0 : Fin 8) := rfl
theorem sg_1 : sg (1 : Fin 7) = (1 : Fin 8) := rfl
theorem sg_2 : sg (2 : Fin 7) = (3 : Fin 8) := rfl
theorem sg_3 : sg (3 : Fin 7) = (4 : Fin 8) := rfl
theorem sg_4 : sg (4 : Fin 7) = (5 : Fin 8) := rfl
theorem sg_5 : sg (5 : Fin 7) = (6 : Fin 8) := rfl
theorem sg_6 : sg (6 : Fin 7) = (7 : Fin 8) := rfl

theorem inst_arr (v : Fin 8 → ℝ) (η : ℝ) (hη : η ≤ (1 / 8046 : ℝ)) (hv : ∀ j, |v j - sv j| ≤ η) :
    ∃ c₀ : Fin 1, Alive (mxOf (fun i => |v (sg i) - v (2 : Fin 8)|) EXs hEXne) (mnOf (fun i => |v (sg i) - v (2 : Fin 8)|) ENs hENne) c₀ ∧
      (∀ c, c < c₀ → ¬ Alive (mxOf (fun i => |v (sg i) - v (2 : Fin 8)|) EXs hEXne) (mnOf (fun i => |v (sg i) - v (2 : Fin 8)|) ENs hENne) c) ∧
      IsLeast {t : ℝ | 0 < t ∧ IsolatedAt v (2 : Fin 8) t} (mxOf (fun i => |v (sg i) - v (2 : Fin 8)|) EXs hEXne c₀) := by
  have hσk : ∀ i, sg i ≠ (2 : Fin 8) := by decide
  have hσ : ∀ j : Fin 8, j ≠ (2 : Fin 8) → ∃ i, sg i = j := by decide
  have hpr : ∀ i, pr i = |sv (sg i) - sv (2 : Fin 8)| := by
    intro i; rcases fin7_cases i with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6, sv_0, sv_1, sv_2, sv_3, sv_4, sv_5, sv_6, sv_7, sg_0, sg_1, sg_2, sg_3, sg_4, sg_5, sg_6]
  have hdev : ∀ i, |(|v (sg i) - v (2 : Fin 8)| - pr i)| ≤ 2 * η := by
    intro i; rw [hpr i]; exact reading_dev v sv η hv (sg i) (2 : Fin 8)
  obtain ⟨c₀, hal, hbf, hT0⟩ := inst (fun i => |v (sg i) - v (2 : Fin 8)|) (2 * η) (by linarith) hdev
  have hset : {t : ℝ | 0 < t ∧ IsolatedAt v (2 : Fin 8) t} =
      {t : ℝ | 0 < t ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (|v (sg i) - v (2 : Fin 8)| * t)} := by
    ext t; simp only [Set.mem_setOf_eq]; rw [iso_iff_readings v (2 : Fin 8) sg hσk hσ t]
  rw [hset]; exact ⟨c₀, hal, hbf, hT0⟩

#print axioms inst_arr

end Fresh.CertRR.R11138



/-!
# Landing certificate `CertRR.R11144`: speeds (1, 2, 6, 7, 8, 9, 10, 11), subject index 0

Generated 2026-10-24 by `experiments/n8/cert_gen_v1.py` (exact Fractions).  Baseline readings [1, 5, 6, 7, 8, 9, 10].  Components up to the first wide one: 1.
Radius: speeds within `η ≤ 1/21504` of the baseline speeds, giving `ε = 2η ≤ 1/10752`.  Covering margin `μ = 1/2048`.
`hcov` is **[PROVISIONAL: covering]**, supporting the claim that the first lonely instant of this subject is the largest exit of the first alive component.
Result `inst_arr`: for such `v`, the subject has a first isolation (a least element over all `t > 0`).  Grades: [L].
-/

open Classical

namespace Fresh.CertRR.R11144

open Fresh Fresh.LandingCert Fresh.LandingRule

noncomputable def pr : Fin 7 → ℝ := ![(1 : ℝ), (5 : ℝ), (6 : ℝ), (7 : ℝ), (8 : ℝ), (9 : ℝ), (10 : ℝ)]
noncomputable def aV : Fin 1 → ℝ := ![(17 / 64 : ℝ)]
noncomputable def bV : Fin 1 → ℝ := ![(15 / 56 : ℝ)]
noncomputable def dV : Fin 1 → ℝ := ![(1 / 224 : ℝ)]
noncomputable def TV : Fin 1 → ℝ := ![(61 / 224 : ℝ)]
def ZV : Fin 1 → ℤ := ![5]
noncomputable def HV : ℝ := (121 / 448 : ℝ)
noncomputable def EXs (c : Fin 1) : Finset (Fin 7 × ℤ) :=
  (Finset.univ ×ˢ Finset.Icc 0 (ZV c)).filter (fun q => ((q.2 : ℝ) + 1 / 8) / pr q.1 = aV c)
noncomputable def ENs (c : Fin 1) : Finset (Fin 7 × ℤ) :=
  (Finset.univ ×ˢ Finset.Icc 0 (ZV c)).filter (fun q => ((q.2 : ℝ) - 1 / 8) / pr q.1 = bV c)

theorem hp : ∀ i, 1 ≤ pr i ∧ pr i ≤ (10 : ℝ) := by intro i; fin_cases i <;> norm_num [pr]
theorem hp1 : ∀ i, 1 ≤ pr i := fun i => (hp i).1
theorem pr_0 : pr (0 : Fin 7) = (1 : ℝ) := rfl
theorem pr_1 : pr (1 : Fin 7) = (5 : ℝ) := rfl
theorem pr_2 : pr (2 : Fin 7) = (6 : ℝ) := rfl
theorem pr_3 : pr (3 : Fin 7) = (7 : ℝ) := rfl
theorem pr_4 : pr (4 : Fin 7) = (8 : ℝ) := rfl
theorem pr_5 : pr (5 : Fin 7) = (9 : ℝ) := rfl
theorem pr_6 : pr (6 : Fin 7) = (10 : ℝ) := rfl
theorem aV_0 : aV (0 : Fin 1) = (17 / 64 : ℝ) := rfl
theorem bV_0 : bV (0 : Fin 1) = (15 / 56 : ℝ) := rfl
theorem dV_0 : dV (0 : Fin 1) = (1 / 224 : ℝ) := rfl
theorem TV_0 : TV (0 : Fin 1) = (61 / 224 : ℝ) := rfl
theorem ZV_0 : ZV (0 : Fin 1) = (5 : ℤ) := rfl
theorem hab : ∀ c, aV c ≤ bV c := by intro c; fin_cases c <;> norm_num [aV, bV]
theorem hd0 : ∀ c, 0 < dV c := by intro c; fin_cases c <;> norm_num [dV]
theorem hdP : ∀ c, dV c ≤ 1 / (4 * (10 : ℝ)) := by intro c; fin_cases c <;> norm_num [dV]
theorem haP : ∀ c, dV c < aV c := by intro c; fin_cases c <;> norm_num [dV, aV]
theorem hT : ∀ c, bV c + dV c ≤ TV c := by intro c; fin_cases c <;> norm_num [bV, dV, TV]
theorem hZ : ∀ c, ((10 : ℝ) + 1) * TV c + 1 ≤ (ZV c : ℝ) := by intro c; fin_cases c <;> norm_num [TV, ZV]
theorem hE (ε : ℝ) (hε : ε ≤ (1 / 10752 : ℝ)) : ∀ c, 8 * ((ZV c : ℝ) + 1) * ε ≤ dV c := by
  intro c; fin_cases c <;> norm_num [ZV, dV] <;> linarith
theorem hcls : ∀ c i, ∀ z : ℤ, 0 ≤ z → z ≤ ZV c →
    ((z : ℝ) + 1 / 8) / pr i ≤ aV c - dV c ∨ bV c + dV c ≤ ((z : ℝ) - 1 / 8) / pr i ∨
      ((z : ℝ) + 1 / 8) / pr i = aV c ∨ ((z : ℝ) - 1 / 8) / pr i = bV c := by
  intro c i z h0 h1
  fin_cases c <;> fin_cases i <;> simp [ZV] at h1 <;> interval_cases z <;> norm_num [pr, aV, bV, dV]
theorem hEXne : ∀ c, (EXs c).Nonempty := by
  intro c
  fin_cases c
  · exact ⟨(4, 2), by simp [EXs, ZV, pr, aV] <;> norm_num⟩
theorem hENne : ∀ c, (ENs c).Nonempty := by
  intro c
  fin_cases c
  · exact ⟨(3, 2), by simp [ENs, ZV, pr, bV] <;> norm_num⟩
theorem hEXdef : ∀ c, ∀ q : Fin 7 × ℤ, q ∈ EXs c ↔ 0 ≤ q.2 ∧ q.2 ≤ ZV c ∧ ((q.2 : ℝ) + 1 / 8) / pr q.1 = aV c := by
  intro c q
  simp only [EXs, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, Finset.mem_Icc, true_and]
  tauto
theorem hENdef : ∀ c, ∀ q : Fin 7 × ℤ, q ∈ ENs c ↔ 0 ≤ q.2 ∧ q.2 ≤ ZV c ∧ ((q.2 : ℝ) - 1 / 8) / pr q.1 = bV c := by
  intro c q
  simp only [ENs, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, Finset.mem_Icc, true_and]
  tauto
theorem hsepL : ∀ c c' : Fin 1, c < c' → bV c + dV c / 2 < aV c' - dV c' / 2 := by
  intro c c' h
  fin_cases c <;> fin_cases c' <;> simp at h ⊢ <;> norm_num [aV, bV, dV]
theorem hHL : ∀ c, bV c + dV c / 2 ≤ HV := by intro c; fin_cases c <;> norm_num [bV, dV, HV]

theorem gap0 (x : Fin 7 → ℝ) (ε : ℝ) (hdev : ∀ i, |x i - pr i| ≤ ε) (hεH : ε * HV ≤ (1 / 2048 : ℝ) / 2) (t : ℝ) (h0 : 0 ≤ t)
    (hHt : t ≤ HV) (h1 : (0 : ℝ) ≤ t) (h2 : t ≤ (59 / 224 : ℝ)) (hlon : ∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)) : False := by
  rcases le_total t (255 / 2048 : ℝ) with hs0 | hs0
  · exact zone_kill_gen pr x ε HV (1 / 2048 : ℝ) hp1 hdev hεH (by norm_num) (0 : Fin 7) 0 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (0 : Fin 7))
  rcases le_total t (287 / 2048 : ℝ) with hs1 | hs1
  · exact zone_kill_gen pr x ε HV (1 / 2048 : ℝ) hp1 hdev hεH (by norm_num) (4 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (4 : Fin 7))
  rcases le_total t (2297 / 14336 : ℝ) with hs2 | hs2
  · exact zone_kill_gen pr x ε HV (1 / 2048 : ℝ) hp1 hdev hεH (by norm_num) (3 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (3 : Fin 7))
  rcases le_total t (383 / 2048 : ℝ) with hs3 | hs3
  · exact zone_kill_gen pr x ε HV (1 / 2048 : ℝ) hp1 hdev hεH (by norm_num) (2 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (2 : Fin 7))
  rcases le_total t (2299 / 10240 : ℝ) with hs4 | hs4
  · exact zone_kill_gen pr x ε HV (1 / 2048 : ℝ) hp1 hdev hεH (by norm_num) (1 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (1 : Fin 7))
  rcases le_total t (4343 / 18432 : ℝ) with hs5 | hs5
  · exact zone_kill_gen pr x ε HV (1 / 2048 : ℝ) hp1 hdev hεH (by norm_num) (5 : Fin 7) 2 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (5 : Fin 7))
  exact zone_kill_gen pr x ε HV (1 / 2048 : ℝ) hp1 hdev hεH (by norm_num) (4 : Fin 7) 2 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (4 : Fin 7))
theorem cov (x : Fin 7 → ℝ) (ε : ℝ) (hε : ε ≤ (1 / 10752 : ℝ)) (hdev : ∀ i, |x i - pr i| ≤ ε) :
    ∀ t : ℝ, 0 < t → t ≤ HV → (∀ c, ¬ (aV c - dV c / 2 ≤ t ∧ t ≤ bV c + dV c / 2)) →
      ¬ (∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)) := by
  intro t h0 hHt hnone hlon
  have hεH : ε * HV ≤ (1 / 2048 : ℝ) / 2 := by
    have hε0 : 0 ≤ ε := le_trans (abs_nonneg _) (hdev 0)
    have : ε * HV ≤ (1 / 10752 : ℝ) * HV := mul_le_mul_of_nonneg_right hε (by norm_num [HV])
    have h2 : (1 / 10752 : ℝ) * HV ≤ (1 / 2048 : ℝ) / 2 := by norm_num [HV]
    linarith
  have n0 := hnone (0 : Fin 1)
  rw [aV_0, bV_0, dV_0] at n0
  rcases lt_or_ge t (59 / 224 : ℝ) with c0 | c0
  · exact gap0 x ε hdev hεH t h0.le hHt h0.le (by linarith) hlon
  have d0 : (121 / 448 : ℝ) < t := by
    by_contra hc; push Not at hc; exact n0 ⟨by linarith, by linarith⟩
  have hHv : HV = (121 / 448 : ℝ) := rfl
  exact absurd (by linarith : t ≤ (121 / 448 : ℝ)) (not_le.2 d0)

theorem inst (x : Fin 7 → ℝ) (ε : ℝ) (hε : ε ≤ (1 / 10752 : ℝ)) (hdev : ∀ i, |x i - pr i| ≤ ε) :
    ∃ c₀ : Fin 1, Alive (mxOf x EXs hEXne) (mnOf x ENs hENne) c₀ ∧
      (∀ c, c < c₀ → ¬ Alive (mxOf x EXs hEXne) (mnOf x ENs hENne) c) ∧
      IsLeast {t : ℝ | 0 < t ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)} (mxOf x EXs hEXne c₀) :=
  landing_cert 1 (10 : ℝ) (by norm_num) pr x hp ε hdev aV bV dV TV ZV hab hd0 hdP haP hT hZ (hE ε hε) hcls EXs ENs hEXne hENne
    hEXdef hENdef hsepL HV hHL (cov x ε hε hdev) (0 : Fin 1) (by rw [dV_0, bV_0, aV_0]; norm_num)

noncomputable def sv : Fin 8 → ℝ := ![(1 : ℝ), (2 : ℝ), (6 : ℝ), (7 : ℝ), (8 : ℝ), (9 : ℝ), (10 : ℝ), (11 : ℝ)]
def sg : Fin 7 → Fin 8 := ![1, 2, 3, 4, 5, 6, 7]

theorem sv_0 : sv (0 : Fin 8) = (1 : ℝ) := rfl
theorem sv_1 : sv (1 : Fin 8) = (2 : ℝ) := rfl
theorem sv_2 : sv (2 : Fin 8) = (6 : ℝ) := rfl
theorem sv_3 : sv (3 : Fin 8) = (7 : ℝ) := rfl
theorem sv_4 : sv (4 : Fin 8) = (8 : ℝ) := rfl
theorem sv_5 : sv (5 : Fin 8) = (9 : ℝ) := rfl
theorem sv_6 : sv (6 : Fin 8) = (10 : ℝ) := rfl
theorem sv_7 : sv (7 : Fin 8) = (11 : ℝ) := rfl
theorem sg_0 : sg (0 : Fin 7) = (1 : Fin 8) := rfl
theorem sg_1 : sg (1 : Fin 7) = (2 : Fin 8) := rfl
theorem sg_2 : sg (2 : Fin 7) = (3 : Fin 8) := rfl
theorem sg_3 : sg (3 : Fin 7) = (4 : Fin 8) := rfl
theorem sg_4 : sg (4 : Fin 7) = (5 : Fin 8) := rfl
theorem sg_5 : sg (5 : Fin 7) = (6 : Fin 8) := rfl
theorem sg_6 : sg (6 : Fin 7) = (7 : Fin 8) := rfl

theorem inst_arr (v : Fin 8 → ℝ) (η : ℝ) (hη : η ≤ (1 / 21504 : ℝ)) (hv : ∀ j, |v j - sv j| ≤ η) :
    ∃ c₀ : Fin 1, Alive (mxOf (fun i => |v (sg i) - v (0 : Fin 8)|) EXs hEXne) (mnOf (fun i => |v (sg i) - v (0 : Fin 8)|) ENs hENne) c₀ ∧
      (∀ c, c < c₀ → ¬ Alive (mxOf (fun i => |v (sg i) - v (0 : Fin 8)|) EXs hEXne) (mnOf (fun i => |v (sg i) - v (0 : Fin 8)|) ENs hENne) c) ∧
      IsLeast {t : ℝ | 0 < t ∧ IsolatedAt v (0 : Fin 8) t} (mxOf (fun i => |v (sg i) - v (0 : Fin 8)|) EXs hEXne c₀) := by
  have hσk : ∀ i, sg i ≠ (0 : Fin 8) := by decide
  have hσ : ∀ j : Fin 8, j ≠ (0 : Fin 8) → ∃ i, sg i = j := by decide
  have hpr : ∀ i, pr i = |sv (sg i) - sv (0 : Fin 8)| := by
    intro i; rcases fin7_cases i with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6, sv_0, sv_1, sv_2, sv_3, sv_4, sv_5, sv_6, sv_7, sg_0, sg_1, sg_2, sg_3, sg_4, sg_5, sg_6]
  have hdev : ∀ i, |(|v (sg i) - v (0 : Fin 8)| - pr i)| ≤ 2 * η := by
    intro i; rw [hpr i]; exact reading_dev v sv η hv (sg i) (0 : Fin 8)
  obtain ⟨c₀, hal, hbf, hT0⟩ := inst (fun i => |v (sg i) - v (0 : Fin 8)|) (2 * η) (by linarith) hdev
  have hset : {t : ℝ | 0 < t ∧ IsolatedAt v (0 : Fin 8) t} =
      {t : ℝ | 0 < t ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (|v (sg i) - v (0 : Fin 8)| * t)} := by
    ext t; simp only [Set.mem_setOf_eq]; rw [iso_iff_readings v (0 : Fin 8) sg hσk hσ t]
  rw [hset]; exact ⟨c₀, hal, hbf, hT0⟩

#print axioms inst_arr

end Fresh.CertRR.R11144



/-!
# Landing certificate `CertRR.R11145`: speeds (1, 2, 6, 7, 8, 9, 10, 11), subject index 1

Generated 2026-10-24 by `experiments/n8/cert_gen_v1.py` (exact Fractions).  Baseline readings [1, 4, 5, 6, 7, 8, 9].  Components up to the first wide one: 1.
Radius: speeds within `η ≤ 1/13824` of the baseline speeds, giving `ε = 2η ≤ 1/6912`.  Covering margin `μ = 1/512`.
`hcov` is **[PROVISIONAL: covering]**, supporting the claim that the first lonely instant of this subject is the largest exit of the first alive component.
Result `inst_arr`: for such `v`, the subject has a first isolation (a least element over all `t > 0`).  Grades: [L].
-/

open Classical

namespace Fresh.CertRR.R11145

open Fresh Fresh.LandingCert Fresh.LandingRule

noncomputable def pr : Fin 7 → ℝ := ![(1 : ℝ), (4 : ℝ), (5 : ℝ), (6 : ℝ), (7 : ℝ), (8 : ℝ), (9 : ℝ)]
noncomputable def aV : Fin 1 → ℝ := ![(17 / 56 : ℝ)]
noncomputable def bV : Fin 1 → ℝ := ![(5 / 16 : ℝ)]
noncomputable def dV : Fin 1 → ℝ := ![(1 / 144 : ℝ)]
noncomputable def TV : Fin 1 → ℝ := ![(23 / 72 : ℝ)]
def ZV : Fin 1 → ℤ := ![5]
noncomputable def HV : ℝ := (91 / 288 : ℝ)
noncomputable def EXs (c : Fin 1) : Finset (Fin 7 × ℤ) :=
  (Finset.univ ×ˢ Finset.Icc 0 (ZV c)).filter (fun q => ((q.2 : ℝ) + 1 / 8) / pr q.1 = aV c)
noncomputable def ENs (c : Fin 1) : Finset (Fin 7 × ℤ) :=
  (Finset.univ ×ˢ Finset.Icc 0 (ZV c)).filter (fun q => ((q.2 : ℝ) - 1 / 8) / pr q.1 = bV c)

theorem hp : ∀ i, 1 ≤ pr i ∧ pr i ≤ (9 : ℝ) := by intro i; fin_cases i <;> norm_num [pr]
theorem hp1 : ∀ i, 1 ≤ pr i := fun i => (hp i).1
theorem pr_0 : pr (0 : Fin 7) = (1 : ℝ) := rfl
theorem pr_1 : pr (1 : Fin 7) = (4 : ℝ) := rfl
theorem pr_2 : pr (2 : Fin 7) = (5 : ℝ) := rfl
theorem pr_3 : pr (3 : Fin 7) = (6 : ℝ) := rfl
theorem pr_4 : pr (4 : Fin 7) = (7 : ℝ) := rfl
theorem pr_5 : pr (5 : Fin 7) = (8 : ℝ) := rfl
theorem pr_6 : pr (6 : Fin 7) = (9 : ℝ) := rfl
theorem aV_0 : aV (0 : Fin 1) = (17 / 56 : ℝ) := rfl
theorem bV_0 : bV (0 : Fin 1) = (5 / 16 : ℝ) := rfl
theorem dV_0 : dV (0 : Fin 1) = (1 / 144 : ℝ) := rfl
theorem TV_0 : TV (0 : Fin 1) = (23 / 72 : ℝ) := rfl
theorem ZV_0 : ZV (0 : Fin 1) = (5 : ℤ) := rfl
theorem hab : ∀ c, aV c ≤ bV c := by intro c; fin_cases c <;> norm_num [aV, bV]
theorem hd0 : ∀ c, 0 < dV c := by intro c; fin_cases c <;> norm_num [dV]
theorem hdP : ∀ c, dV c ≤ 1 / (4 * (9 : ℝ)) := by intro c; fin_cases c <;> norm_num [dV]
theorem haP : ∀ c, dV c < aV c := by intro c; fin_cases c <;> norm_num [dV, aV]
theorem hT : ∀ c, bV c + dV c ≤ TV c := by intro c; fin_cases c <;> norm_num [bV, dV, TV]
theorem hZ : ∀ c, ((9 : ℝ) + 1) * TV c + 1 ≤ (ZV c : ℝ) := by intro c; fin_cases c <;> norm_num [TV, ZV]
theorem hE (ε : ℝ) (hε : ε ≤ (1 / 6912 : ℝ)) : ∀ c, 8 * ((ZV c : ℝ) + 1) * ε ≤ dV c := by
  intro c; fin_cases c <;> norm_num [ZV, dV] <;> linarith
theorem hcls : ∀ c i, ∀ z : ℤ, 0 ≤ z → z ≤ ZV c →
    ((z : ℝ) + 1 / 8) / pr i ≤ aV c - dV c ∨ bV c + dV c ≤ ((z : ℝ) - 1 / 8) / pr i ∨
      ((z : ℝ) + 1 / 8) / pr i = aV c ∨ ((z : ℝ) - 1 / 8) / pr i = bV c := by
  intro c i z h0 h1
  fin_cases c <;> fin_cases i <;> simp [ZV] at h1 <;> interval_cases z <;> norm_num [pr, aV, bV, dV]
theorem hEXne : ∀ c, (EXs c).Nonempty := by
  intro c
  fin_cases c
  · exact ⟨(4, 2), by simp [EXs, ZV, pr, aV] <;> norm_num⟩
theorem hENne : ∀ c, (ENs c).Nonempty := by
  intro c
  fin_cases c
  · exact ⟨(3, 2), by simp [ENs, ZV, pr, bV] <;> norm_num⟩
theorem hEXdef : ∀ c, ∀ q : Fin 7 × ℤ, q ∈ EXs c ↔ 0 ≤ q.2 ∧ q.2 ≤ ZV c ∧ ((q.2 : ℝ) + 1 / 8) / pr q.1 = aV c := by
  intro c q
  simp only [EXs, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, Finset.mem_Icc, true_and]
  tauto
theorem hENdef : ∀ c, ∀ q : Fin 7 × ℤ, q ∈ ENs c ↔ 0 ≤ q.2 ∧ q.2 ≤ ZV c ∧ ((q.2 : ℝ) - 1 / 8) / pr q.1 = bV c := by
  intro c q
  simp only [ENs, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, Finset.mem_Icc, true_and]
  tauto
theorem hsepL : ∀ c c' : Fin 1, c < c' → bV c + dV c / 2 < aV c' - dV c' / 2 := by
  intro c c' h
  fin_cases c <;> fin_cases c' <;> simp at h ⊢ <;> norm_num [aV, bV, dV]
theorem hHL : ∀ c, bV c + dV c / 2 ≤ HV := by intro c; fin_cases c <;> norm_num [bV, dV, HV]

theorem gap0 (x : Fin 7 → ℝ) (ε : ℝ) (hdev : ∀ i, |x i - pr i| ≤ ε) (hεH : ε * HV ≤ (1 / 512 : ℝ) / 2) (t : ℝ) (h0 : 0 ≤ t)
    (hHt : t ≤ HV) (h1 : (0 : ℝ) ≤ t) (h2 : t ≤ (605 / 2016 : ℝ)) (hlon : ∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)) : False := by
  rcases le_total t (63 / 512 : ℝ) with hs0 | hs0
  · exact zone_kill_gen pr x ε HV (1 / 512 : ℝ) hp1 hdev hεH (by norm_num) (0 : Fin 7) 0 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (0 : Fin 7))
  rcases le_total t (71 / 512 : ℝ) with hs1 | hs1
  · exact zone_kill_gen pr x ε HV (1 / 512 : ℝ) hp1 hdev hεH (by norm_num) (5 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (5 : Fin 7))
  rcases le_total t (569 / 3584 : ℝ) with hs2 | hs2
  · exact zone_kill_gen pr x ε HV (1 / 512 : ℝ) hp1 hdev hεH (by norm_num) (4 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (4 : Fin 7))
  rcases le_total t (95 / 512 : ℝ) with hs3 | hs3
  · exact zone_kill_gen pr x ε HV (1 / 512 : ℝ) hp1 hdev hεH (by norm_num) (3 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (3 : Fin 7))
  rcases le_total t (571 / 2560 : ℝ) with hs4 | hs4
  · exact zone_kill_gen pr x ε HV (1 / 512 : ℝ) hp1 hdev hεH (by norm_num) (2 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (2 : Fin 7))
  rcases le_total t (143 / 512 : ℝ) with hs5 | hs5
  · exact zone_kill_gen pr x ε HV (1 / 512 : ℝ) hp1 hdev hεH (by norm_num) (1 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (1 : Fin 7))
  exact zone_kill_gen pr x ε HV (1 / 512 : ℝ) hp1 hdev hεH (by norm_num) (4 : Fin 7) 2 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (4 : Fin 7))
theorem cov (x : Fin 7 → ℝ) (ε : ℝ) (hε : ε ≤ (1 / 6912 : ℝ)) (hdev : ∀ i, |x i - pr i| ≤ ε) :
    ∀ t : ℝ, 0 < t → t ≤ HV → (∀ c, ¬ (aV c - dV c / 2 ≤ t ∧ t ≤ bV c + dV c / 2)) →
      ¬ (∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)) := by
  intro t h0 hHt hnone hlon
  have hεH : ε * HV ≤ (1 / 512 : ℝ) / 2 := by
    have hε0 : 0 ≤ ε := le_trans (abs_nonneg _) (hdev 0)
    have : ε * HV ≤ (1 / 6912 : ℝ) * HV := mul_le_mul_of_nonneg_right hε (by norm_num [HV])
    have h2 : (1 / 6912 : ℝ) * HV ≤ (1 / 512 : ℝ) / 2 := by norm_num [HV]
    linarith
  have n0 := hnone (0 : Fin 1)
  rw [aV_0, bV_0, dV_0] at n0
  rcases lt_or_ge t (605 / 2016 : ℝ) with c0 | c0
  · exact gap0 x ε hdev hεH t h0.le hHt h0.le (by linarith) hlon
  have d0 : (91 / 288 : ℝ) < t := by
    by_contra hc; push Not at hc; exact n0 ⟨by linarith, by linarith⟩
  have hHv : HV = (91 / 288 : ℝ) := rfl
  exact absurd (by linarith : t ≤ (91 / 288 : ℝ)) (not_le.2 d0)

theorem inst (x : Fin 7 → ℝ) (ε : ℝ) (hε : ε ≤ (1 / 6912 : ℝ)) (hdev : ∀ i, |x i - pr i| ≤ ε) :
    ∃ c₀ : Fin 1, Alive (mxOf x EXs hEXne) (mnOf x ENs hENne) c₀ ∧
      (∀ c, c < c₀ → ¬ Alive (mxOf x EXs hEXne) (mnOf x ENs hENne) c) ∧
      IsLeast {t : ℝ | 0 < t ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)} (mxOf x EXs hEXne c₀) :=
  landing_cert 1 (9 : ℝ) (by norm_num) pr x hp ε hdev aV bV dV TV ZV hab hd0 hdP haP hT hZ (hE ε hε) hcls EXs ENs hEXne hENne
    hEXdef hENdef hsepL HV hHL (cov x ε hε hdev) (0 : Fin 1) (by rw [dV_0, bV_0, aV_0]; norm_num)

noncomputable def sv : Fin 8 → ℝ := ![(1 : ℝ), (2 : ℝ), (6 : ℝ), (7 : ℝ), (8 : ℝ), (9 : ℝ), (10 : ℝ), (11 : ℝ)]
def sg : Fin 7 → Fin 8 := ![0, 2, 3, 4, 5, 6, 7]

theorem sv_0 : sv (0 : Fin 8) = (1 : ℝ) := rfl
theorem sv_1 : sv (1 : Fin 8) = (2 : ℝ) := rfl
theorem sv_2 : sv (2 : Fin 8) = (6 : ℝ) := rfl
theorem sv_3 : sv (3 : Fin 8) = (7 : ℝ) := rfl
theorem sv_4 : sv (4 : Fin 8) = (8 : ℝ) := rfl
theorem sv_5 : sv (5 : Fin 8) = (9 : ℝ) := rfl
theorem sv_6 : sv (6 : Fin 8) = (10 : ℝ) := rfl
theorem sv_7 : sv (7 : Fin 8) = (11 : ℝ) := rfl
theorem sg_0 : sg (0 : Fin 7) = (0 : Fin 8) := rfl
theorem sg_1 : sg (1 : Fin 7) = (2 : Fin 8) := rfl
theorem sg_2 : sg (2 : Fin 7) = (3 : Fin 8) := rfl
theorem sg_3 : sg (3 : Fin 7) = (4 : Fin 8) := rfl
theorem sg_4 : sg (4 : Fin 7) = (5 : Fin 8) := rfl
theorem sg_5 : sg (5 : Fin 7) = (6 : Fin 8) := rfl
theorem sg_6 : sg (6 : Fin 7) = (7 : Fin 8) := rfl

theorem inst_arr (v : Fin 8 → ℝ) (η : ℝ) (hη : η ≤ (1 / 13824 : ℝ)) (hv : ∀ j, |v j - sv j| ≤ η) :
    ∃ c₀ : Fin 1, Alive (mxOf (fun i => |v (sg i) - v (1 : Fin 8)|) EXs hEXne) (mnOf (fun i => |v (sg i) - v (1 : Fin 8)|) ENs hENne) c₀ ∧
      (∀ c, c < c₀ → ¬ Alive (mxOf (fun i => |v (sg i) - v (1 : Fin 8)|) EXs hEXne) (mnOf (fun i => |v (sg i) - v (1 : Fin 8)|) ENs hENne) c) ∧
      IsLeast {t : ℝ | 0 < t ∧ IsolatedAt v (1 : Fin 8) t} (mxOf (fun i => |v (sg i) - v (1 : Fin 8)|) EXs hEXne c₀) := by
  have hσk : ∀ i, sg i ≠ (1 : Fin 8) := by decide
  have hσ : ∀ j : Fin 8, j ≠ (1 : Fin 8) → ∃ i, sg i = j := by decide
  have hpr : ∀ i, pr i = |sv (sg i) - sv (1 : Fin 8)| := by
    intro i; rcases fin7_cases i with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6, sv_0, sv_1, sv_2, sv_3, sv_4, sv_5, sv_6, sv_7, sg_0, sg_1, sg_2, sg_3, sg_4, sg_5, sg_6]
  have hdev : ∀ i, |(|v (sg i) - v (1 : Fin 8)| - pr i)| ≤ 2 * η := by
    intro i; rw [hpr i]; exact reading_dev v sv η hv (sg i) (1 : Fin 8)
  obtain ⟨c₀, hal, hbf, hT0⟩ := inst (fun i => |v (sg i) - v (1 : Fin 8)|) (2 * η) (by linarith) hdev
  have hset : {t : ℝ | 0 < t ∧ IsolatedAt v (1 : Fin 8) t} =
      {t : ℝ | 0 < t ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (|v (sg i) - v (1 : Fin 8)| * t)} := by
    ext t; simp only [Set.mem_setOf_eq]; rw [iso_iff_readings v (1 : Fin 8) sg hσk hσ t]
  rw [hset]; exact ⟨c₀, hal, hbf, hT0⟩

#print axioms inst_arr

end Fresh.CertRR.R11145



/-!
# Landing certificate `CertRR.R11152`: speeds (1, 2, 6, 7, 8, 9, 10, 12), subject index 0

Generated 2026-10-24 by `experiments/n8/cert_gen_v1.py` (exact Fractions).  Baseline readings [1, 5, 6, 7, 8, 9, 11].  Components up to the first wide one: 1.
Radius: speeds within `η ≤ 1/16128` of the baseline speeds, giving `ε = 2η ≤ 1/8064`.  Covering margin `μ = 1/2048`.
`hcov` is **[PROVISIONAL: covering]**, supporting the claim that the first lonely instant of this subject is the largest exit of the first alive component.
Result `inst_arr`: for such `v`, the subject has a first isolation (a least element over all `t > 0`).  Grades: [L].
-/

open Classical

namespace Fresh.CertRR.R11152

open Fresh Fresh.LandingCert Fresh.LandingRule

noncomputable def pr : Fin 7 → ℝ := ![(1 : ℝ), (5 : ℝ), (6 : ℝ), (7 : ℝ), (8 : ℝ), (9 : ℝ), (11 : ℝ)]
noncomputable def aV : Fin 1 → ℝ := ![(17 / 56 : ℝ)]
noncomputable def bV : Fin 1 → ℝ := ![(5 / 16 : ℝ)]
noncomputable def dV : Fin 1 → ℝ := ![(1 / 144 : ℝ)]
noncomputable def TV : Fin 1 → ℝ := ![(23 / 72 : ℝ)]
def ZV : Fin 1 → ℤ := ![6]
noncomputable def HV : ℝ := (91 / 288 : ℝ)
noncomputable def EXs (c : Fin 1) : Finset (Fin 7 × ℤ) :=
  (Finset.univ ×ˢ Finset.Icc 0 (ZV c)).filter (fun q => ((q.2 : ℝ) + 1 / 8) / pr q.1 = aV c)
noncomputable def ENs (c : Fin 1) : Finset (Fin 7 × ℤ) :=
  (Finset.univ ×ˢ Finset.Icc 0 (ZV c)).filter (fun q => ((q.2 : ℝ) - 1 / 8) / pr q.1 = bV c)

theorem hp : ∀ i, 1 ≤ pr i ∧ pr i ≤ (11 : ℝ) := by intro i; fin_cases i <;> norm_num [pr]
theorem hp1 : ∀ i, 1 ≤ pr i := fun i => (hp i).1
theorem pr_0 : pr (0 : Fin 7) = (1 : ℝ) := rfl
theorem pr_1 : pr (1 : Fin 7) = (5 : ℝ) := rfl
theorem pr_2 : pr (2 : Fin 7) = (6 : ℝ) := rfl
theorem pr_3 : pr (3 : Fin 7) = (7 : ℝ) := rfl
theorem pr_4 : pr (4 : Fin 7) = (8 : ℝ) := rfl
theorem pr_5 : pr (5 : Fin 7) = (9 : ℝ) := rfl
theorem pr_6 : pr (6 : Fin 7) = (11 : ℝ) := rfl
theorem aV_0 : aV (0 : Fin 1) = (17 / 56 : ℝ) := rfl
theorem bV_0 : bV (0 : Fin 1) = (5 / 16 : ℝ) := rfl
theorem dV_0 : dV (0 : Fin 1) = (1 / 144 : ℝ) := rfl
theorem TV_0 : TV (0 : Fin 1) = (23 / 72 : ℝ) := rfl
theorem ZV_0 : ZV (0 : Fin 1) = (6 : ℤ) := rfl
theorem hab : ∀ c, aV c ≤ bV c := by intro c; fin_cases c <;> norm_num [aV, bV]
theorem hd0 : ∀ c, 0 < dV c := by intro c; fin_cases c <;> norm_num [dV]
theorem hdP : ∀ c, dV c ≤ 1 / (4 * (11 : ℝ)) := by intro c; fin_cases c <;> norm_num [dV]
theorem haP : ∀ c, dV c < aV c := by intro c; fin_cases c <;> norm_num [dV, aV]
theorem hT : ∀ c, bV c + dV c ≤ TV c := by intro c; fin_cases c <;> norm_num [bV, dV, TV]
theorem hZ : ∀ c, ((11 : ℝ) + 1) * TV c + 1 ≤ (ZV c : ℝ) := by intro c; fin_cases c <;> norm_num [TV, ZV]
theorem hE (ε : ℝ) (hε : ε ≤ (1 / 8064 : ℝ)) : ∀ c, 8 * ((ZV c : ℝ) + 1) * ε ≤ dV c := by
  intro c; fin_cases c <;> norm_num [ZV, dV] <;> linarith
theorem hcls : ∀ c i, ∀ z : ℤ, 0 ≤ z → z ≤ ZV c →
    ((z : ℝ) + 1 / 8) / pr i ≤ aV c - dV c ∨ bV c + dV c ≤ ((z : ℝ) - 1 / 8) / pr i ∨
      ((z : ℝ) + 1 / 8) / pr i = aV c ∨ ((z : ℝ) - 1 / 8) / pr i = bV c := by
  intro c i z h0 h1
  fin_cases c <;> fin_cases i <;> simp [ZV] at h1 <;> interval_cases z <;> norm_num [pr, aV, bV, dV]
theorem hEXne : ∀ c, (EXs c).Nonempty := by
  intro c
  fin_cases c
  · exact ⟨(3, 2), by simp [EXs, ZV, pr, aV] <;> norm_num⟩
theorem hENne : ∀ c, (ENs c).Nonempty := by
  intro c
  fin_cases c
  · exact ⟨(2, 2), by simp [ENs, ZV, pr, bV] <;> norm_num⟩
theorem hEXdef : ∀ c, ∀ q : Fin 7 × ℤ, q ∈ EXs c ↔ 0 ≤ q.2 ∧ q.2 ≤ ZV c ∧ ((q.2 : ℝ) + 1 / 8) / pr q.1 = aV c := by
  intro c q
  simp only [EXs, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, Finset.mem_Icc, true_and]
  tauto
theorem hENdef : ∀ c, ∀ q : Fin 7 × ℤ, q ∈ ENs c ↔ 0 ≤ q.2 ∧ q.2 ≤ ZV c ∧ ((q.2 : ℝ) - 1 / 8) / pr q.1 = bV c := by
  intro c q
  simp only [ENs, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, Finset.mem_Icc, true_and]
  tauto
theorem hsepL : ∀ c c' : Fin 1, c < c' → bV c + dV c / 2 < aV c' - dV c' / 2 := by
  intro c c' h
  fin_cases c <;> fin_cases c' <;> simp at h ⊢ <;> norm_num [aV, bV, dV]
theorem hHL : ∀ c, bV c + dV c / 2 ≤ HV := by intro c; fin_cases c <;> norm_num [bV, dV, HV]

theorem gap0 (x : Fin 7 → ℝ) (ε : ℝ) (hdev : ∀ i, |x i - pr i| ≤ ε) (hεH : ε * HV ≤ (1 / 2048 : ℝ) / 2) (t : ℝ) (h0 : 0 ≤ t)
    (hHt : t ≤ HV) (h1 : (0 : ℝ) ≤ t) (h2 : t ≤ (605 / 2016 : ℝ)) (hlon : ∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)) : False := by
  rcases le_total t (255 / 2048 : ℝ) with hs0 | hs0
  · exact zone_kill_gen pr x ε HV (1 / 2048 : ℝ) hp1 hdev hεH (by norm_num) (0 : Fin 7) 0 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (0 : Fin 7))
  rcases le_total t (287 / 2048 : ℝ) with hs1 | hs1
  · exact zone_kill_gen pr x ε HV (1 / 2048 : ℝ) hp1 hdev hεH (by norm_num) (4 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (4 : Fin 7))
  rcases le_total t (2297 / 14336 : ℝ) with hs2 | hs2
  · exact zone_kill_gen pr x ε HV (1 / 2048 : ℝ) hp1 hdev hεH (by norm_num) (3 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (3 : Fin 7))
  rcases le_total t (383 / 2048 : ℝ) with hs3 | hs3
  · exact zone_kill_gen pr x ε HV (1 / 2048 : ℝ) hp1 hdev hεH (by norm_num) (2 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (2 : Fin 7))
  rcases le_total t (2299 / 10240 : ℝ) with hs4 | hs4
  · exact zone_kill_gen pr x ε HV (1 / 2048 : ℝ) hp1 hdev hεH (by norm_num) (1 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (1 : Fin 7))
  rcases le_total t (4343 / 18432 : ℝ) with hs5 | hs5
  · exact zone_kill_gen pr x ε HV (1 / 2048 : ℝ) hp1 hdev hεH (by norm_num) (5 : Fin 7) 2 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (5 : Fin 7))
  rcases le_total t (543 / 2048 : ℝ) with hs6 | hs6
  · exact zone_kill_gen pr x ε HV (1 / 2048 : ℝ) hp1 hdev hεH (by norm_num) (4 : Fin 7) 2 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (4 : Fin 7))
  rcases le_total t (6389 / 22528 : ℝ) with hs7 | hs7
  · exact zone_kill_gen pr x ε HV (1 / 2048 : ℝ) hp1 hdev hεH (by norm_num) (6 : Fin 7) 3 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (6 : Fin 7))
  exact zone_kill_gen pr x ε HV (1 / 2048 : ℝ) hp1 hdev hεH (by norm_num) (3 : Fin 7) 2 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (3 : Fin 7))
theorem cov (x : Fin 7 → ℝ) (ε : ℝ) (hε : ε ≤ (1 / 8064 : ℝ)) (hdev : ∀ i, |x i - pr i| ≤ ε) :
    ∀ t : ℝ, 0 < t → t ≤ HV → (∀ c, ¬ (aV c - dV c / 2 ≤ t ∧ t ≤ bV c + dV c / 2)) →
      ¬ (∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)) := by
  intro t h0 hHt hnone hlon
  have hεH : ε * HV ≤ (1 / 2048 : ℝ) / 2 := by
    have hε0 : 0 ≤ ε := le_trans (abs_nonneg _) (hdev 0)
    have : ε * HV ≤ (1 / 8064 : ℝ) * HV := mul_le_mul_of_nonneg_right hε (by norm_num [HV])
    have h2 : (1 / 8064 : ℝ) * HV ≤ (1 / 2048 : ℝ) / 2 := by norm_num [HV]
    linarith
  have n0 := hnone (0 : Fin 1)
  rw [aV_0, bV_0, dV_0] at n0
  rcases lt_or_ge t (605 / 2016 : ℝ) with c0 | c0
  · exact gap0 x ε hdev hεH t h0.le hHt h0.le (by linarith) hlon
  have d0 : (91 / 288 : ℝ) < t := by
    by_contra hc; push Not at hc; exact n0 ⟨by linarith, by linarith⟩
  have hHv : HV = (91 / 288 : ℝ) := rfl
  exact absurd (by linarith : t ≤ (91 / 288 : ℝ)) (not_le.2 d0)

theorem inst (x : Fin 7 → ℝ) (ε : ℝ) (hε : ε ≤ (1 / 8064 : ℝ)) (hdev : ∀ i, |x i - pr i| ≤ ε) :
    ∃ c₀ : Fin 1, Alive (mxOf x EXs hEXne) (mnOf x ENs hENne) c₀ ∧
      (∀ c, c < c₀ → ¬ Alive (mxOf x EXs hEXne) (mnOf x ENs hENne) c) ∧
      IsLeast {t : ℝ | 0 < t ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)} (mxOf x EXs hEXne c₀) :=
  landing_cert 1 (11 : ℝ) (by norm_num) pr x hp ε hdev aV bV dV TV ZV hab hd0 hdP haP hT hZ (hE ε hε) hcls EXs ENs hEXne hENne
    hEXdef hENdef hsepL HV hHL (cov x ε hε hdev) (0 : Fin 1) (by rw [dV_0, bV_0, aV_0]; norm_num)

noncomputable def sv : Fin 8 → ℝ := ![(1 : ℝ), (2 : ℝ), (6 : ℝ), (7 : ℝ), (8 : ℝ), (9 : ℝ), (10 : ℝ), (12 : ℝ)]
def sg : Fin 7 → Fin 8 := ![1, 2, 3, 4, 5, 6, 7]

theorem sv_0 : sv (0 : Fin 8) = (1 : ℝ) := rfl
theorem sv_1 : sv (1 : Fin 8) = (2 : ℝ) := rfl
theorem sv_2 : sv (2 : Fin 8) = (6 : ℝ) := rfl
theorem sv_3 : sv (3 : Fin 8) = (7 : ℝ) := rfl
theorem sv_4 : sv (4 : Fin 8) = (8 : ℝ) := rfl
theorem sv_5 : sv (5 : Fin 8) = (9 : ℝ) := rfl
theorem sv_6 : sv (6 : Fin 8) = (10 : ℝ) := rfl
theorem sv_7 : sv (7 : Fin 8) = (12 : ℝ) := rfl
theorem sg_0 : sg (0 : Fin 7) = (1 : Fin 8) := rfl
theorem sg_1 : sg (1 : Fin 7) = (2 : Fin 8) := rfl
theorem sg_2 : sg (2 : Fin 7) = (3 : Fin 8) := rfl
theorem sg_3 : sg (3 : Fin 7) = (4 : Fin 8) := rfl
theorem sg_4 : sg (4 : Fin 7) = (5 : Fin 8) := rfl
theorem sg_5 : sg (5 : Fin 7) = (6 : Fin 8) := rfl
theorem sg_6 : sg (6 : Fin 7) = (7 : Fin 8) := rfl

theorem inst_arr (v : Fin 8 → ℝ) (η : ℝ) (hη : η ≤ (1 / 16128 : ℝ)) (hv : ∀ j, |v j - sv j| ≤ η) :
    ∃ c₀ : Fin 1, Alive (mxOf (fun i => |v (sg i) - v (0 : Fin 8)|) EXs hEXne) (mnOf (fun i => |v (sg i) - v (0 : Fin 8)|) ENs hENne) c₀ ∧
      (∀ c, c < c₀ → ¬ Alive (mxOf (fun i => |v (sg i) - v (0 : Fin 8)|) EXs hEXne) (mnOf (fun i => |v (sg i) - v (0 : Fin 8)|) ENs hENne) c) ∧
      IsLeast {t : ℝ | 0 < t ∧ IsolatedAt v (0 : Fin 8) t} (mxOf (fun i => |v (sg i) - v (0 : Fin 8)|) EXs hEXne c₀) := by
  have hσk : ∀ i, sg i ≠ (0 : Fin 8) := by decide
  have hσ : ∀ j : Fin 8, j ≠ (0 : Fin 8) → ∃ i, sg i = j := by decide
  have hpr : ∀ i, pr i = |sv (sg i) - sv (0 : Fin 8)| := by
    intro i; rcases fin7_cases i with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6, sv_0, sv_1, sv_2, sv_3, sv_4, sv_5, sv_6, sv_7, sg_0, sg_1, sg_2, sg_3, sg_4, sg_5, sg_6]
  have hdev : ∀ i, |(|v (sg i) - v (0 : Fin 8)| - pr i)| ≤ 2 * η := by
    intro i; rw [hpr i]; exact reading_dev v sv η hv (sg i) (0 : Fin 8)
  obtain ⟨c₀, hal, hbf, hT0⟩ := inst (fun i => |v (sg i) - v (0 : Fin 8)|) (2 * η) (by linarith) hdev
  have hset : {t : ℝ | 0 < t ∧ IsolatedAt v (0 : Fin 8) t} =
      {t : ℝ | 0 < t ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (|v (sg i) - v (0 : Fin 8)| * t)} := by
    ext t; simp only [Set.mem_setOf_eq]; rw [iso_iff_readings v (0 : Fin 8) sg hσk hσ t]
  rw [hset]; exact ⟨c₀, hal, hbf, hT0⟩

#print axioms inst_arr

end Fresh.CertRR.R11152



/-!
# Landing certificate `CertRR.R11153`: speeds (1, 2, 6, 7, 8, 9, 10, 12), subject index 1

Generated 2026-10-24 by `experiments/n8/cert_gen_v1.py` (exact Fractions).  Baseline readings [1, 4, 5, 6, 7, 8, 10].  Components up to the first wide one: 2.
Radius: speeds within `η ≤ 1/10752` of the baseline speeds, giving `ε = 2η ≤ 1/5376`.  Covering margin `μ = 1/512`.
`hcov` is **[PROVISIONAL: covering]**, supporting the claim that the first lonely instant of this subject is the largest exit of the first alive component.
Result `inst_arr`: for such `v`, the subject has a first isolation (a least element over all `t > 0`).  Grades: [L].
-/

open Classical

namespace Fresh.CertRR.R11153

open Fresh Fresh.LandingCert Fresh.LandingRule

noncomputable def pr : Fin 7 → ℝ := ![(1 : ℝ), (4 : ℝ), (5 : ℝ), (6 : ℝ), (7 : ℝ), (8 : ℝ), (10 : ℝ)]
noncomputable def aV : Fin 2 → ℝ := ![(5 / 16 : ℝ), (17 / 48 : ℝ)]
noncomputable def bV : Fin 2 → ℝ := ![(5 / 16 : ℝ), (23 / 64 : ℝ)]
noncomputable def dV : Fin 2 → ℝ := ![(1 / 112 : ℝ), (1 / 96 : ℝ)]
noncomputable def TV : Fin 2 → ℝ := ![(9 / 28 : ℝ), (71 / 192 : ℝ)]
def ZV : Fin 2 → ℤ := ![5, 6]
noncomputable def HV : ℝ := (35 / 96 : ℝ)
noncomputable def EXs (c : Fin 2) : Finset (Fin 7 × ℤ) :=
  (Finset.univ ×ˢ Finset.Icc 0 (ZV c)).filter (fun q => ((q.2 : ℝ) + 1 / 8) / pr q.1 = aV c)
noncomputable def ENs (c : Fin 2) : Finset (Fin 7 × ℤ) :=
  (Finset.univ ×ˢ Finset.Icc 0 (ZV c)).filter (fun q => ((q.2 : ℝ) - 1 / 8) / pr q.1 = bV c)

theorem hp : ∀ i, 1 ≤ pr i ∧ pr i ≤ (10 : ℝ) := by intro i; fin_cases i <;> norm_num [pr]
theorem hp1 : ∀ i, 1 ≤ pr i := fun i => (hp i).1
theorem pr_0 : pr (0 : Fin 7) = (1 : ℝ) := rfl
theorem pr_1 : pr (1 : Fin 7) = (4 : ℝ) := rfl
theorem pr_2 : pr (2 : Fin 7) = (5 : ℝ) := rfl
theorem pr_3 : pr (3 : Fin 7) = (6 : ℝ) := rfl
theorem pr_4 : pr (4 : Fin 7) = (7 : ℝ) := rfl
theorem pr_5 : pr (5 : Fin 7) = (8 : ℝ) := rfl
theorem pr_6 : pr (6 : Fin 7) = (10 : ℝ) := rfl
theorem aV_0 : aV (0 : Fin 2) = (5 / 16 : ℝ) := rfl
theorem bV_0 : bV (0 : Fin 2) = (5 / 16 : ℝ) := rfl
theorem dV_0 : dV (0 : Fin 2) = (1 / 112 : ℝ) := rfl
theorem TV_0 : TV (0 : Fin 2) = (9 / 28 : ℝ) := rfl
theorem ZV_0 : ZV (0 : Fin 2) = (5 : ℤ) := rfl
theorem aV_1 : aV (1 : Fin 2) = (17 / 48 : ℝ) := rfl
theorem bV_1 : bV (1 : Fin 2) = (23 / 64 : ℝ) := rfl
theorem dV_1 : dV (1 : Fin 2) = (1 / 96 : ℝ) := rfl
theorem TV_1 : TV (1 : Fin 2) = (71 / 192 : ℝ) := rfl
theorem ZV_1 : ZV (1 : Fin 2) = (6 : ℤ) := rfl
theorem hab : ∀ c, aV c ≤ bV c := by intro c; fin_cases c <;> norm_num [aV, bV]
theorem hd0 : ∀ c, 0 < dV c := by intro c; fin_cases c <;> norm_num [dV]
theorem hdP : ∀ c, dV c ≤ 1 / (4 * (10 : ℝ)) := by intro c; fin_cases c <;> norm_num [dV]
theorem haP : ∀ c, dV c < aV c := by intro c; fin_cases c <;> norm_num [dV, aV]
theorem hT : ∀ c, bV c + dV c ≤ TV c := by intro c; fin_cases c <;> norm_num [bV, dV, TV]
theorem hZ : ∀ c, ((10 : ℝ) + 1) * TV c + 1 ≤ (ZV c : ℝ) := by intro c; fin_cases c <;> norm_num [TV, ZV]
theorem hE (ε : ℝ) (hε : ε ≤ (1 / 5376 : ℝ)) : ∀ c, 8 * ((ZV c : ℝ) + 1) * ε ≤ dV c := by
  intro c; fin_cases c <;> norm_num [ZV, dV] <;> linarith
theorem hcls : ∀ c i, ∀ z : ℤ, 0 ≤ z → z ≤ ZV c →
    ((z : ℝ) + 1 / 8) / pr i ≤ aV c - dV c ∨ bV c + dV c ≤ ((z : ℝ) - 1 / 8) / pr i ∨
      ((z : ℝ) + 1 / 8) / pr i = aV c ∨ ((z : ℝ) - 1 / 8) / pr i = bV c := by
  intro c i z h0 h1
  fin_cases c <;> fin_cases i <;> simp [ZV] at h1 <;> interval_cases z <;> norm_num [pr, aV, bV, dV]
theorem hEXne : ∀ c, (EXs c).Nonempty := by
  intro c
  fin_cases c
  · exact ⟨(6, 3), by simp [EXs, ZV, pr, aV] <;> norm_num⟩
  · exact ⟨(3, 2), by simp [EXs, ZV, pr, aV] <;> norm_num⟩
theorem hENne : ∀ c, (ENs c).Nonempty := by
  intro c
  fin_cases c
  · exact ⟨(3, 2), by simp [ENs, ZV, pr, bV] <;> norm_num⟩
  · exact ⟨(5, 3), by simp [ENs, ZV, pr, bV] <;> norm_num⟩
theorem hEXdef : ∀ c, ∀ q : Fin 7 × ℤ, q ∈ EXs c ↔ 0 ≤ q.2 ∧ q.2 ≤ ZV c ∧ ((q.2 : ℝ) + 1 / 8) / pr q.1 = aV c := by
  intro c q
  simp only [EXs, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, Finset.mem_Icc, true_and]
  tauto
theorem hENdef : ∀ c, ∀ q : Fin 7 × ℤ, q ∈ ENs c ↔ 0 ≤ q.2 ∧ q.2 ≤ ZV c ∧ ((q.2 : ℝ) - 1 / 8) / pr q.1 = bV c := by
  intro c q
  simp only [ENs, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, Finset.mem_Icc, true_and]
  tauto
theorem hsepL : ∀ c c' : Fin 2, c < c' → bV c + dV c / 2 < aV c' - dV c' / 2 := by
  intro c c' h
  fin_cases c <;> fin_cases c' <;> simp at h ⊢ <;> norm_num [aV, bV, dV]
theorem hHL : ∀ c, bV c + dV c / 2 ≤ HV := by intro c; fin_cases c <;> norm_num [bV, dV, HV]

theorem gap0 (x : Fin 7 → ℝ) (ε : ℝ) (hdev : ∀ i, |x i - pr i| ≤ ε) (hεH : ε * HV ≤ (1 / 512 : ℝ) / 2) (t : ℝ) (h0 : 0 ≤ t)
    (hHt : t ≤ HV) (h1 : (0 : ℝ) ≤ t) (h2 : t ≤ (69 / 224 : ℝ)) (hlon : ∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)) : False := by
  rcases le_total t (63 / 512 : ℝ) with hs0 | hs0
  · exact zone_kill_gen pr x ε HV (1 / 512 : ℝ) hp1 hdev hεH (by norm_num) (0 : Fin 7) 0 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (0 : Fin 7))
  rcases le_total t (71 / 512 : ℝ) with hs1 | hs1
  · exact zone_kill_gen pr x ε HV (1 / 512 : ℝ) hp1 hdev hεH (by norm_num) (5 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (5 : Fin 7))
  rcases le_total t (569 / 3584 : ℝ) with hs2 | hs2
  · exact zone_kill_gen pr x ε HV (1 / 512 : ℝ) hp1 hdev hεH (by norm_num) (4 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (4 : Fin 7))
  rcases le_total t (95 / 512 : ℝ) with hs3 | hs3
  · exact zone_kill_gen pr x ε HV (1 / 512 : ℝ) hp1 hdev hεH (by norm_num) (3 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (3 : Fin 7))
  rcases le_total t (571 / 2560 : ℝ) with hs4 | hs4
  · exact zone_kill_gen pr x ε HV (1 / 512 : ℝ) hp1 hdev hεH (by norm_num) (2 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (2 : Fin 7))
  rcases le_total t (143 / 512 : ℝ) with hs5 | hs5
  · exact zone_kill_gen pr x ε HV (1 / 512 : ℝ) hp1 hdev hεH (by norm_num) (1 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (1 : Fin 7))
  rcases le_total t (1081 / 3584 : ℝ) with hs6 | hs6
  · exact zone_kill_gen pr x ε HV (1 / 512 : ℝ) hp1 hdev hεH (by norm_num) (4 : Fin 7) 2 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (4 : Fin 7))
  exact zone_kill_gen pr x ε HV (1 / 512 : ℝ) hp1 hdev hεH (by norm_num) (6 : Fin 7) 3 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (6 : Fin 7))
theorem gap1 (x : Fin 7 → ℝ) (ε : ℝ) (hdev : ∀ i, |x i - pr i| ≤ ε) (hεH : ε * HV ≤ (1 / 512 : ℝ) / 2) (t : ℝ) (h0 : 0 ≤ t)
    (hHt : t ≤ HV) (h1 : (71 / 224 : ℝ) ≤ t) (h2 : t ≤ (67 / 192 : ℝ)) (hlon : ∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)) : False := by
  exact zone_kill_gen pr x ε HV (1 / 512 : ℝ) hp1 hdev hεH (by norm_num) (3 : Fin 7) 2 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (3 : Fin 7))
theorem cov (x : Fin 7 → ℝ) (ε : ℝ) (hε : ε ≤ (1 / 5376 : ℝ)) (hdev : ∀ i, |x i - pr i| ≤ ε) :
    ∀ t : ℝ, 0 < t → t ≤ HV → (∀ c, ¬ (aV c - dV c / 2 ≤ t ∧ t ≤ bV c + dV c / 2)) →
      ¬ (∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)) := by
  intro t h0 hHt hnone hlon
  have hεH : ε * HV ≤ (1 / 512 : ℝ) / 2 := by
    have hε0 : 0 ≤ ε := le_trans (abs_nonneg _) (hdev 0)
    have : ε * HV ≤ (1 / 5376 : ℝ) * HV := mul_le_mul_of_nonneg_right hε (by norm_num [HV])
    have h2 : (1 / 5376 : ℝ) * HV ≤ (1 / 512 : ℝ) / 2 := by norm_num [HV]
    linarith
  have n0 := hnone (0 : Fin 2)
  rw [aV_0, bV_0, dV_0] at n0
  have n1 := hnone (1 : Fin 2)
  rw [aV_1, bV_1, dV_1] at n1
  rcases lt_or_ge t (69 / 224 : ℝ) with c0 | c0
  · exact gap0 x ε hdev hεH t h0.le hHt h0.le (by linarith) hlon
  have d0 : (71 / 224 : ℝ) < t := by
    by_contra hc; push Not at hc; exact n0 ⟨by linarith, by linarith⟩
  rcases lt_or_ge t (67 / 192 : ℝ) with c1 | c1
  · exact gap1 x ε hdev hεH t h0.le hHt d0.le (by linarith) hlon
  have d1 : (35 / 96 : ℝ) < t := by
    by_contra hc; push Not at hc; exact n1 ⟨by linarith, by linarith⟩
  have hHv : HV = (35 / 96 : ℝ) := rfl
  exact absurd (by linarith : t ≤ (35 / 96 : ℝ)) (not_le.2 d1)

theorem inst (x : Fin 7 → ℝ) (ε : ℝ) (hε : ε ≤ (1 / 5376 : ℝ)) (hdev : ∀ i, |x i - pr i| ≤ ε) :
    ∃ c₀ : Fin 2, Alive (mxOf x EXs hEXne) (mnOf x ENs hENne) c₀ ∧
      (∀ c, c < c₀ → ¬ Alive (mxOf x EXs hEXne) (mnOf x ENs hENne) c) ∧
      IsLeast {t : ℝ | 0 < t ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)} (mxOf x EXs hEXne c₀) :=
  landing_cert 2 (10 : ℝ) (by norm_num) pr x hp ε hdev aV bV dV TV ZV hab hd0 hdP haP hT hZ (hE ε hε) hcls EXs ENs hEXne hENne
    hEXdef hENdef hsepL HV hHL (cov x ε hε hdev) (1 : Fin 2) (by rw [dV_1, bV_1, aV_1]; norm_num)

noncomputable def sv : Fin 8 → ℝ := ![(1 : ℝ), (2 : ℝ), (6 : ℝ), (7 : ℝ), (8 : ℝ), (9 : ℝ), (10 : ℝ), (12 : ℝ)]
def sg : Fin 7 → Fin 8 := ![0, 2, 3, 4, 5, 6, 7]

theorem sv_0 : sv (0 : Fin 8) = (1 : ℝ) := rfl
theorem sv_1 : sv (1 : Fin 8) = (2 : ℝ) := rfl
theorem sv_2 : sv (2 : Fin 8) = (6 : ℝ) := rfl
theorem sv_3 : sv (3 : Fin 8) = (7 : ℝ) := rfl
theorem sv_4 : sv (4 : Fin 8) = (8 : ℝ) := rfl
theorem sv_5 : sv (5 : Fin 8) = (9 : ℝ) := rfl
theorem sv_6 : sv (6 : Fin 8) = (10 : ℝ) := rfl
theorem sv_7 : sv (7 : Fin 8) = (12 : ℝ) := rfl
theorem sg_0 : sg (0 : Fin 7) = (0 : Fin 8) := rfl
theorem sg_1 : sg (1 : Fin 7) = (2 : Fin 8) := rfl
theorem sg_2 : sg (2 : Fin 7) = (3 : Fin 8) := rfl
theorem sg_3 : sg (3 : Fin 7) = (4 : Fin 8) := rfl
theorem sg_4 : sg (4 : Fin 7) = (5 : Fin 8) := rfl
theorem sg_5 : sg (5 : Fin 7) = (6 : Fin 8) := rfl
theorem sg_6 : sg (6 : Fin 7) = (7 : Fin 8) := rfl

theorem inst_arr (v : Fin 8 → ℝ) (η : ℝ) (hη : η ≤ (1 / 10752 : ℝ)) (hv : ∀ j, |v j - sv j| ≤ η) :
    ∃ c₀ : Fin 2, Alive (mxOf (fun i => |v (sg i) - v (1 : Fin 8)|) EXs hEXne) (mnOf (fun i => |v (sg i) - v (1 : Fin 8)|) ENs hENne) c₀ ∧
      (∀ c, c < c₀ → ¬ Alive (mxOf (fun i => |v (sg i) - v (1 : Fin 8)|) EXs hEXne) (mnOf (fun i => |v (sg i) - v (1 : Fin 8)|) ENs hENne) c) ∧
      IsLeast {t : ℝ | 0 < t ∧ IsolatedAt v (1 : Fin 8) t} (mxOf (fun i => |v (sg i) - v (1 : Fin 8)|) EXs hEXne c₀) := by
  have hσk : ∀ i, sg i ≠ (1 : Fin 8) := by decide
  have hσ : ∀ j : Fin 8, j ≠ (1 : Fin 8) → ∃ i, sg i = j := by decide
  have hpr : ∀ i, pr i = |sv (sg i) - sv (1 : Fin 8)| := by
    intro i; rcases fin7_cases i with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6, sv_0, sv_1, sv_2, sv_3, sv_4, sv_5, sv_6, sv_7, sg_0, sg_1, sg_2, sg_3, sg_4, sg_5, sg_6]
  have hdev : ∀ i, |(|v (sg i) - v (1 : Fin 8)| - pr i)| ≤ 2 * η := by
    intro i; rw [hpr i]; exact reading_dev v sv η hv (sg i) (1 : Fin 8)
  obtain ⟨c₀, hal, hbf, hT0⟩ := inst (fun i => |v (sg i) - v (1 : Fin 8)|) (2 * η) (by linarith) hdev
  have hset : {t : ℝ | 0 < t ∧ IsolatedAt v (1 : Fin 8) t} =
      {t : ℝ | 0 < t ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (|v (sg i) - v (1 : Fin 8)| * t)} := by
    ext t; simp only [Set.mem_setOf_eq]; rw [iso_iff_readings v (1 : Fin 8) sg hσk hσ t]
  rw [hset]; exact ⟨c₀, hal, hbf, hT0⟩

#print axioms inst_arr

end Fresh.CertRR.R11153



/-!
# Landing certificate `CertRR.R11160`: speeds (1, 2, 6, 7, 8, 9, 10, 13), subject index 0

Generated 2026-10-24 by `experiments/n8/cert_gen_v1.py` (exact Fractions).  Baseline readings [1, 5, 6, 7, 8, 9, 12].  Components up to the first wide one: 1.
Radius: speeds within `η ≤ 1/21504` of the baseline speeds, giving `ε = 2η ≤ 1/10752`.  Covering margin `μ = 1/2048`.
`hcov` is **[PROVISIONAL: covering]**, supporting the claim that the first lonely instant of this subject is the largest exit of the first alive component.
Result `inst_arr`: for such `v`, the subject has a first isolation (a least element over all `t > 0`).  Grades: [L].
-/

open Classical

namespace Fresh.CertRR.R11160

open Fresh Fresh.LandingCert Fresh.LandingRule

noncomputable def pr : Fin 7 → ℝ := ![(1 : ℝ), (5 : ℝ), (6 : ℝ), (7 : ℝ), (8 : ℝ), (9 : ℝ), (12 : ℝ)]
noncomputable def aV : Fin 1 → ℝ := ![(17 / 64 : ℝ)]
noncomputable def bV : Fin 1 → ℝ := ![(15 / 56 : ℝ)]
noncomputable def dV : Fin 1 → ℝ := ![(1 / 224 : ℝ)]
noncomputable def TV : Fin 1 → ℝ := ![(61 / 224 : ℝ)]
def ZV : Fin 1 → ℤ := ![5]
noncomputable def HV : ℝ := (121 / 448 : ℝ)
noncomputable def EXs (c : Fin 1) : Finset (Fin 7 × ℤ) :=
  (Finset.univ ×ˢ Finset.Icc 0 (ZV c)).filter (fun q => ((q.2 : ℝ) + 1 / 8) / pr q.1 = aV c)
noncomputable def ENs (c : Fin 1) : Finset (Fin 7 × ℤ) :=
  (Finset.univ ×ˢ Finset.Icc 0 (ZV c)).filter (fun q => ((q.2 : ℝ) - 1 / 8) / pr q.1 = bV c)

theorem hp : ∀ i, 1 ≤ pr i ∧ pr i ≤ (12 : ℝ) := by intro i; fin_cases i <;> norm_num [pr]
theorem hp1 : ∀ i, 1 ≤ pr i := fun i => (hp i).1
theorem pr_0 : pr (0 : Fin 7) = (1 : ℝ) := rfl
theorem pr_1 : pr (1 : Fin 7) = (5 : ℝ) := rfl
theorem pr_2 : pr (2 : Fin 7) = (6 : ℝ) := rfl
theorem pr_3 : pr (3 : Fin 7) = (7 : ℝ) := rfl
theorem pr_4 : pr (4 : Fin 7) = (8 : ℝ) := rfl
theorem pr_5 : pr (5 : Fin 7) = (9 : ℝ) := rfl
theorem pr_6 : pr (6 : Fin 7) = (12 : ℝ) := rfl
theorem aV_0 : aV (0 : Fin 1) = (17 / 64 : ℝ) := rfl
theorem bV_0 : bV (0 : Fin 1) = (15 / 56 : ℝ) := rfl
theorem dV_0 : dV (0 : Fin 1) = (1 / 224 : ℝ) := rfl
theorem TV_0 : TV (0 : Fin 1) = (61 / 224 : ℝ) := rfl
theorem ZV_0 : ZV (0 : Fin 1) = (5 : ℤ) := rfl
theorem hab : ∀ c, aV c ≤ bV c := by intro c; fin_cases c <;> norm_num [aV, bV]
theorem hd0 : ∀ c, 0 < dV c := by intro c; fin_cases c <;> norm_num [dV]
theorem hdP : ∀ c, dV c ≤ 1 / (4 * (12 : ℝ)) := by intro c; fin_cases c <;> norm_num [dV]
theorem haP : ∀ c, dV c < aV c := by intro c; fin_cases c <;> norm_num [dV, aV]
theorem hT : ∀ c, bV c + dV c ≤ TV c := by intro c; fin_cases c <;> norm_num [bV, dV, TV]
theorem hZ : ∀ c, ((12 : ℝ) + 1) * TV c + 1 ≤ (ZV c : ℝ) := by intro c; fin_cases c <;> norm_num [TV, ZV]
theorem hE (ε : ℝ) (hε : ε ≤ (1 / 10752 : ℝ)) : ∀ c, 8 * ((ZV c : ℝ) + 1) * ε ≤ dV c := by
  intro c; fin_cases c <;> norm_num [ZV, dV] <;> linarith
theorem hcls : ∀ c i, ∀ z : ℤ, 0 ≤ z → z ≤ ZV c →
    ((z : ℝ) + 1 / 8) / pr i ≤ aV c - dV c ∨ bV c + dV c ≤ ((z : ℝ) - 1 / 8) / pr i ∨
      ((z : ℝ) + 1 / 8) / pr i = aV c ∨ ((z : ℝ) - 1 / 8) / pr i = bV c := by
  intro c i z h0 h1
  fin_cases c <;> fin_cases i <;> simp [ZV] at h1 <;> interval_cases z <;> norm_num [pr, aV, bV, dV]
theorem hEXne : ∀ c, (EXs c).Nonempty := by
  intro c
  fin_cases c
  · exact ⟨(4, 2), by simp [EXs, ZV, pr, aV] <;> norm_num⟩
theorem hENne : ∀ c, (ENs c).Nonempty := by
  intro c
  fin_cases c
  · exact ⟨(3, 2), by simp [ENs, ZV, pr, bV] <;> norm_num⟩
theorem hEXdef : ∀ c, ∀ q : Fin 7 × ℤ, q ∈ EXs c ↔ 0 ≤ q.2 ∧ q.2 ≤ ZV c ∧ ((q.2 : ℝ) + 1 / 8) / pr q.1 = aV c := by
  intro c q
  simp only [EXs, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, Finset.mem_Icc, true_and]
  tauto
theorem hENdef : ∀ c, ∀ q : Fin 7 × ℤ, q ∈ ENs c ↔ 0 ≤ q.2 ∧ q.2 ≤ ZV c ∧ ((q.2 : ℝ) - 1 / 8) / pr q.1 = bV c := by
  intro c q
  simp only [ENs, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, Finset.mem_Icc, true_and]
  tauto
theorem hsepL : ∀ c c' : Fin 1, c < c' → bV c + dV c / 2 < aV c' - dV c' / 2 := by
  intro c c' h
  fin_cases c <;> fin_cases c' <;> simp at h ⊢ <;> norm_num [aV, bV, dV]
theorem hHL : ∀ c, bV c + dV c / 2 ≤ HV := by intro c; fin_cases c <;> norm_num [bV, dV, HV]

theorem gap0 (x : Fin 7 → ℝ) (ε : ℝ) (hdev : ∀ i, |x i - pr i| ≤ ε) (hεH : ε * HV ≤ (1 / 2048 : ℝ) / 2) (t : ℝ) (h0 : 0 ≤ t)
    (hHt : t ≤ HV) (h1 : (0 : ℝ) ≤ t) (h2 : t ≤ (59 / 224 : ℝ)) (hlon : ∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)) : False := by
  rcases le_total t (255 / 2048 : ℝ) with hs0 | hs0
  · exact zone_kill_gen pr x ε HV (1 / 2048 : ℝ) hp1 hdev hεH (by norm_num) (0 : Fin 7) 0 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (0 : Fin 7))
  rcases le_total t (287 / 2048 : ℝ) with hs1 | hs1
  · exact zone_kill_gen pr x ε HV (1 / 2048 : ℝ) hp1 hdev hεH (by norm_num) (4 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (4 : Fin 7))
  rcases le_total t (2297 / 14336 : ℝ) with hs2 | hs2
  · exact zone_kill_gen pr x ε HV (1 / 2048 : ℝ) hp1 hdev hεH (by norm_num) (3 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (3 : Fin 7))
  rcases le_total t (383 / 2048 : ℝ) with hs3 | hs3
  · exact zone_kill_gen pr x ε HV (1 / 2048 : ℝ) hp1 hdev hεH (by norm_num) (2 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (2 : Fin 7))
  rcases le_total t (2299 / 10240 : ℝ) with hs4 | hs4
  · exact zone_kill_gen pr x ε HV (1 / 2048 : ℝ) hp1 hdev hεH (by norm_num) (1 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (1 : Fin 7))
  rcases le_total t (4343 / 18432 : ℝ) with hs5 | hs5
  · exact zone_kill_gen pr x ε HV (1 / 2048 : ℝ) hp1 hdev hεH (by norm_num) (5 : Fin 7) 2 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (5 : Fin 7))
  exact zone_kill_gen pr x ε HV (1 / 2048 : ℝ) hp1 hdev hεH (by norm_num) (4 : Fin 7) 2 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (4 : Fin 7))
theorem cov (x : Fin 7 → ℝ) (ε : ℝ) (hε : ε ≤ (1 / 10752 : ℝ)) (hdev : ∀ i, |x i - pr i| ≤ ε) :
    ∀ t : ℝ, 0 < t → t ≤ HV → (∀ c, ¬ (aV c - dV c / 2 ≤ t ∧ t ≤ bV c + dV c / 2)) →
      ¬ (∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)) := by
  intro t h0 hHt hnone hlon
  have hεH : ε * HV ≤ (1 / 2048 : ℝ) / 2 := by
    have hε0 : 0 ≤ ε := le_trans (abs_nonneg _) (hdev 0)
    have : ε * HV ≤ (1 / 10752 : ℝ) * HV := mul_le_mul_of_nonneg_right hε (by norm_num [HV])
    have h2 : (1 / 10752 : ℝ) * HV ≤ (1 / 2048 : ℝ) / 2 := by norm_num [HV]
    linarith
  have n0 := hnone (0 : Fin 1)
  rw [aV_0, bV_0, dV_0] at n0
  rcases lt_or_ge t (59 / 224 : ℝ) with c0 | c0
  · exact gap0 x ε hdev hεH t h0.le hHt h0.le (by linarith) hlon
  have d0 : (121 / 448 : ℝ) < t := by
    by_contra hc; push Not at hc; exact n0 ⟨by linarith, by linarith⟩
  have hHv : HV = (121 / 448 : ℝ) := rfl
  exact absurd (by linarith : t ≤ (121 / 448 : ℝ)) (not_le.2 d0)

theorem inst (x : Fin 7 → ℝ) (ε : ℝ) (hε : ε ≤ (1 / 10752 : ℝ)) (hdev : ∀ i, |x i - pr i| ≤ ε) :
    ∃ c₀ : Fin 1, Alive (mxOf x EXs hEXne) (mnOf x ENs hENne) c₀ ∧
      (∀ c, c < c₀ → ¬ Alive (mxOf x EXs hEXne) (mnOf x ENs hENne) c) ∧
      IsLeast {t : ℝ | 0 < t ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)} (mxOf x EXs hEXne c₀) :=
  landing_cert 1 (12 : ℝ) (by norm_num) pr x hp ε hdev aV bV dV TV ZV hab hd0 hdP haP hT hZ (hE ε hε) hcls EXs ENs hEXne hENne
    hEXdef hENdef hsepL HV hHL (cov x ε hε hdev) (0 : Fin 1) (by rw [dV_0, bV_0, aV_0]; norm_num)

noncomputable def sv : Fin 8 → ℝ := ![(1 : ℝ), (2 : ℝ), (6 : ℝ), (7 : ℝ), (8 : ℝ), (9 : ℝ), (10 : ℝ), (13 : ℝ)]
def sg : Fin 7 → Fin 8 := ![1, 2, 3, 4, 5, 6, 7]

theorem sv_0 : sv (0 : Fin 8) = (1 : ℝ) := rfl
theorem sv_1 : sv (1 : Fin 8) = (2 : ℝ) := rfl
theorem sv_2 : sv (2 : Fin 8) = (6 : ℝ) := rfl
theorem sv_3 : sv (3 : Fin 8) = (7 : ℝ) := rfl
theorem sv_4 : sv (4 : Fin 8) = (8 : ℝ) := rfl
theorem sv_5 : sv (5 : Fin 8) = (9 : ℝ) := rfl
theorem sv_6 : sv (6 : Fin 8) = (10 : ℝ) := rfl
theorem sv_7 : sv (7 : Fin 8) = (13 : ℝ) := rfl
theorem sg_0 : sg (0 : Fin 7) = (1 : Fin 8) := rfl
theorem sg_1 : sg (1 : Fin 7) = (2 : Fin 8) := rfl
theorem sg_2 : sg (2 : Fin 7) = (3 : Fin 8) := rfl
theorem sg_3 : sg (3 : Fin 7) = (4 : Fin 8) := rfl
theorem sg_4 : sg (4 : Fin 7) = (5 : Fin 8) := rfl
theorem sg_5 : sg (5 : Fin 7) = (6 : Fin 8) := rfl
theorem sg_6 : sg (6 : Fin 7) = (7 : Fin 8) := rfl

theorem inst_arr (v : Fin 8 → ℝ) (η : ℝ) (hη : η ≤ (1 / 21504 : ℝ)) (hv : ∀ j, |v j - sv j| ≤ η) :
    ∃ c₀ : Fin 1, Alive (mxOf (fun i => |v (sg i) - v (0 : Fin 8)|) EXs hEXne) (mnOf (fun i => |v (sg i) - v (0 : Fin 8)|) ENs hENne) c₀ ∧
      (∀ c, c < c₀ → ¬ Alive (mxOf (fun i => |v (sg i) - v (0 : Fin 8)|) EXs hEXne) (mnOf (fun i => |v (sg i) - v (0 : Fin 8)|) ENs hENne) c) ∧
      IsLeast {t : ℝ | 0 < t ∧ IsolatedAt v (0 : Fin 8) t} (mxOf (fun i => |v (sg i) - v (0 : Fin 8)|) EXs hEXne c₀) := by
  have hσk : ∀ i, sg i ≠ (0 : Fin 8) := by decide
  have hσ : ∀ j : Fin 8, j ≠ (0 : Fin 8) → ∃ i, sg i = j := by decide
  have hpr : ∀ i, pr i = |sv (sg i) - sv (0 : Fin 8)| := by
    intro i; rcases fin7_cases i with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6, sv_0, sv_1, sv_2, sv_3, sv_4, sv_5, sv_6, sv_7, sg_0, sg_1, sg_2, sg_3, sg_4, sg_5, sg_6]
  have hdev : ∀ i, |(|v (sg i) - v (0 : Fin 8)| - pr i)| ≤ 2 * η := by
    intro i; rw [hpr i]; exact reading_dev v sv η hv (sg i) (0 : Fin 8)
  obtain ⟨c₀, hal, hbf, hT0⟩ := inst (fun i => |v (sg i) - v (0 : Fin 8)|) (2 * η) (by linarith) hdev
  have hset : {t : ℝ | 0 < t ∧ IsolatedAt v (0 : Fin 8) t} =
      {t : ℝ | 0 < t ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (|v (sg i) - v (0 : Fin 8)| * t)} := by
    ext t; simp only [Set.mem_setOf_eq]; rw [iso_iff_readings v (0 : Fin 8) sg hσk hσ t]
  rw [hset]; exact ⟨c₀, hal, hbf, hT0⟩

#print axioms inst_arr

end Fresh.CertRR.R11160



/-!
# Landing certificate `CertRR.R11161`: speeds (1, 2, 6, 7, 8, 9, 10, 13), subject index 1

Generated 2026-10-24 by `experiments/n8/cert_gen_v1.py` (exact Fractions).  Baseline readings [1, 4, 5, 6, 7, 8, 11].  Components up to the first wide one: 1.
Radius: speeds within `η ≤ 1/6272` of the baseline speeds, giving `ε = 2η ≤ 1/3136`.  Covering margin `μ = 1/512`.
`hcov` is **[PROVISIONAL: covering]**, supporting the claim that the first lonely instant of this subject is the largest exit of the first alive component.
Result `inst_arr`: for such `v`, the subject has a first isolation (a least element over all `t > 0`).  Grades: [L].
-/

open Classical

namespace Fresh.CertRR.R11161

open Fresh Fresh.LandingCert Fresh.LandingRule

noncomputable def pr : Fin 7 → ℝ := ![(1 : ℝ), (4 : ℝ), (5 : ℝ), (6 : ℝ), (7 : ℝ), (8 : ℝ), (11 : ℝ)]
noncomputable def aV : Fin 1 → ℝ := ![(17 / 56 : ℝ)]
noncomputable def bV : Fin 1 → ℝ := ![(5 / 16 : ℝ)]
noncomputable def dV : Fin 1 → ℝ := ![(1 / 56 : ℝ)]
noncomputable def TV : Fin 1 → ℝ := ![(37 / 112 : ℝ)]
def ZV : Fin 1 → ℤ := ![6]
noncomputable def HV : ℝ := (9 / 28 : ℝ)
noncomputable def EXs (c : Fin 1) : Finset (Fin 7 × ℤ) :=
  (Finset.univ ×ˢ Finset.Icc 0 (ZV c)).filter (fun q => ((q.2 : ℝ) + 1 / 8) / pr q.1 = aV c)
noncomputable def ENs (c : Fin 1) : Finset (Fin 7 × ℤ) :=
  (Finset.univ ×ˢ Finset.Icc 0 (ZV c)).filter (fun q => ((q.2 : ℝ) - 1 / 8) / pr q.1 = bV c)

theorem hp : ∀ i, 1 ≤ pr i ∧ pr i ≤ (11 : ℝ) := by intro i; fin_cases i <;> norm_num [pr]
theorem hp1 : ∀ i, 1 ≤ pr i := fun i => (hp i).1
theorem pr_0 : pr (0 : Fin 7) = (1 : ℝ) := rfl
theorem pr_1 : pr (1 : Fin 7) = (4 : ℝ) := rfl
theorem pr_2 : pr (2 : Fin 7) = (5 : ℝ) := rfl
theorem pr_3 : pr (3 : Fin 7) = (6 : ℝ) := rfl
theorem pr_4 : pr (4 : Fin 7) = (7 : ℝ) := rfl
theorem pr_5 : pr (5 : Fin 7) = (8 : ℝ) := rfl
theorem pr_6 : pr (6 : Fin 7) = (11 : ℝ) := rfl
theorem aV_0 : aV (0 : Fin 1) = (17 / 56 : ℝ) := rfl
theorem bV_0 : bV (0 : Fin 1) = (5 / 16 : ℝ) := rfl
theorem dV_0 : dV (0 : Fin 1) = (1 / 56 : ℝ) := rfl
theorem TV_0 : TV (0 : Fin 1) = (37 / 112 : ℝ) := rfl
theorem ZV_0 : ZV (0 : Fin 1) = (6 : ℤ) := rfl
theorem hab : ∀ c, aV c ≤ bV c := by intro c; fin_cases c <;> norm_num [aV, bV]
theorem hd0 : ∀ c, 0 < dV c := by intro c; fin_cases c <;> norm_num [dV]
theorem hdP : ∀ c, dV c ≤ 1 / (4 * (11 : ℝ)) := by intro c; fin_cases c <;> norm_num [dV]
theorem haP : ∀ c, dV c < aV c := by intro c; fin_cases c <;> norm_num [dV, aV]
theorem hT : ∀ c, bV c + dV c ≤ TV c := by intro c; fin_cases c <;> norm_num [bV, dV, TV]
theorem hZ : ∀ c, ((11 : ℝ) + 1) * TV c + 1 ≤ (ZV c : ℝ) := by intro c; fin_cases c <;> norm_num [TV, ZV]
theorem hE (ε : ℝ) (hε : ε ≤ (1 / 3136 : ℝ)) : ∀ c, 8 * ((ZV c : ℝ) + 1) * ε ≤ dV c := by
  intro c; fin_cases c <;> norm_num [ZV, dV] <;> linarith
theorem hcls : ∀ c i, ∀ z : ℤ, 0 ≤ z → z ≤ ZV c →
    ((z : ℝ) + 1 / 8) / pr i ≤ aV c - dV c ∨ bV c + dV c ≤ ((z : ℝ) - 1 / 8) / pr i ∨
      ((z : ℝ) + 1 / 8) / pr i = aV c ∨ ((z : ℝ) - 1 / 8) / pr i = bV c := by
  intro c i z h0 h1
  fin_cases c <;> fin_cases i <;> simp [ZV] at h1 <;> interval_cases z <;> norm_num [pr, aV, bV, dV]
theorem hEXne : ∀ c, (EXs c).Nonempty := by
  intro c
  fin_cases c
  · exact ⟨(4, 2), by simp [EXs, ZV, pr, aV] <;> norm_num⟩
theorem hENne : ∀ c, (ENs c).Nonempty := by
  intro c
  fin_cases c
  · exact ⟨(3, 2), by simp [ENs, ZV, pr, bV] <;> norm_num⟩
theorem hEXdef : ∀ c, ∀ q : Fin 7 × ℤ, q ∈ EXs c ↔ 0 ≤ q.2 ∧ q.2 ≤ ZV c ∧ ((q.2 : ℝ) + 1 / 8) / pr q.1 = aV c := by
  intro c q
  simp only [EXs, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, Finset.mem_Icc, true_and]
  tauto
theorem hENdef : ∀ c, ∀ q : Fin 7 × ℤ, q ∈ ENs c ↔ 0 ≤ q.2 ∧ q.2 ≤ ZV c ∧ ((q.2 : ℝ) - 1 / 8) / pr q.1 = bV c := by
  intro c q
  simp only [ENs, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, Finset.mem_Icc, true_and]
  tauto
theorem hsepL : ∀ c c' : Fin 1, c < c' → bV c + dV c / 2 < aV c' - dV c' / 2 := by
  intro c c' h
  fin_cases c <;> fin_cases c' <;> simp at h ⊢ <;> norm_num [aV, bV, dV]
theorem hHL : ∀ c, bV c + dV c / 2 ≤ HV := by intro c; fin_cases c <;> norm_num [bV, dV, HV]

theorem gap0 (x : Fin 7 → ℝ) (ε : ℝ) (hdev : ∀ i, |x i - pr i| ≤ ε) (hεH : ε * HV ≤ (1 / 512 : ℝ) / 2) (t : ℝ) (h0 : 0 ≤ t)
    (hHt : t ≤ HV) (h1 : (0 : ℝ) ≤ t) (h2 : t ≤ (33 / 112 : ℝ)) (hlon : ∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)) : False := by
  rcases le_total t (63 / 512 : ℝ) with hs0 | hs0
  · exact zone_kill_gen pr x ε HV (1 / 512 : ℝ) hp1 hdev hεH (by norm_num) (0 : Fin 7) 0 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (0 : Fin 7))
  rcases le_total t (71 / 512 : ℝ) with hs1 | hs1
  · exact zone_kill_gen pr x ε HV (1 / 512 : ℝ) hp1 hdev hεH (by norm_num) (5 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (5 : Fin 7))
  rcases le_total t (569 / 3584 : ℝ) with hs2 | hs2
  · exact zone_kill_gen pr x ε HV (1 / 512 : ℝ) hp1 hdev hεH (by norm_num) (4 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (4 : Fin 7))
  rcases le_total t (95 / 512 : ℝ) with hs3 | hs3
  · exact zone_kill_gen pr x ε HV (1 / 512 : ℝ) hp1 hdev hεH (by norm_num) (3 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (3 : Fin 7))
  rcases le_total t (571 / 2560 : ℝ) with hs4 | hs4
  · exact zone_kill_gen pr x ε HV (1 / 512 : ℝ) hp1 hdev hεH (by norm_num) (2 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (2 : Fin 7))
  rcases le_total t (143 / 512 : ℝ) with hs5 | hs5
  · exact zone_kill_gen pr x ε HV (1 / 512 : ℝ) hp1 hdev hεH (by norm_num) (1 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (1 : Fin 7))
  exact zone_kill_gen pr x ε HV (1 / 512 : ℝ) hp1 hdev hεH (by norm_num) (4 : Fin 7) 2 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (4 : Fin 7))
theorem cov (x : Fin 7 → ℝ) (ε : ℝ) (hε : ε ≤ (1 / 3136 : ℝ)) (hdev : ∀ i, |x i - pr i| ≤ ε) :
    ∀ t : ℝ, 0 < t → t ≤ HV → (∀ c, ¬ (aV c - dV c / 2 ≤ t ∧ t ≤ bV c + dV c / 2)) →
      ¬ (∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)) := by
  intro t h0 hHt hnone hlon
  have hεH : ε * HV ≤ (1 / 512 : ℝ) / 2 := by
    have hε0 : 0 ≤ ε := le_trans (abs_nonneg _) (hdev 0)
    have : ε * HV ≤ (1 / 3136 : ℝ) * HV := mul_le_mul_of_nonneg_right hε (by norm_num [HV])
    have h2 : (1 / 3136 : ℝ) * HV ≤ (1 / 512 : ℝ) / 2 := by norm_num [HV]
    linarith
  have n0 := hnone (0 : Fin 1)
  rw [aV_0, bV_0, dV_0] at n0
  rcases lt_or_ge t (33 / 112 : ℝ) with c0 | c0
  · exact gap0 x ε hdev hεH t h0.le hHt h0.le (by linarith) hlon
  have d0 : (9 / 28 : ℝ) < t := by
    by_contra hc; push Not at hc; exact n0 ⟨by linarith, by linarith⟩
  have hHv : HV = (9 / 28 : ℝ) := rfl
  exact absurd (by linarith : t ≤ (9 / 28 : ℝ)) (not_le.2 d0)

theorem inst (x : Fin 7 → ℝ) (ε : ℝ) (hε : ε ≤ (1 / 3136 : ℝ)) (hdev : ∀ i, |x i - pr i| ≤ ε) :
    ∃ c₀ : Fin 1, Alive (mxOf x EXs hEXne) (mnOf x ENs hENne) c₀ ∧
      (∀ c, c < c₀ → ¬ Alive (mxOf x EXs hEXne) (mnOf x ENs hENne) c) ∧
      IsLeast {t : ℝ | 0 < t ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)} (mxOf x EXs hEXne c₀) :=
  landing_cert 1 (11 : ℝ) (by norm_num) pr x hp ε hdev aV bV dV TV ZV hab hd0 hdP haP hT hZ (hE ε hε) hcls EXs ENs hEXne hENne
    hEXdef hENdef hsepL HV hHL (cov x ε hε hdev) (0 : Fin 1) (by rw [dV_0, bV_0, aV_0]; norm_num)

noncomputable def sv : Fin 8 → ℝ := ![(1 : ℝ), (2 : ℝ), (6 : ℝ), (7 : ℝ), (8 : ℝ), (9 : ℝ), (10 : ℝ), (13 : ℝ)]
def sg : Fin 7 → Fin 8 := ![0, 2, 3, 4, 5, 6, 7]

theorem sv_0 : sv (0 : Fin 8) = (1 : ℝ) := rfl
theorem sv_1 : sv (1 : Fin 8) = (2 : ℝ) := rfl
theorem sv_2 : sv (2 : Fin 8) = (6 : ℝ) := rfl
theorem sv_3 : sv (3 : Fin 8) = (7 : ℝ) := rfl
theorem sv_4 : sv (4 : Fin 8) = (8 : ℝ) := rfl
theorem sv_5 : sv (5 : Fin 8) = (9 : ℝ) := rfl
theorem sv_6 : sv (6 : Fin 8) = (10 : ℝ) := rfl
theorem sv_7 : sv (7 : Fin 8) = (13 : ℝ) := rfl
theorem sg_0 : sg (0 : Fin 7) = (0 : Fin 8) := rfl
theorem sg_1 : sg (1 : Fin 7) = (2 : Fin 8) := rfl
theorem sg_2 : sg (2 : Fin 7) = (3 : Fin 8) := rfl
theorem sg_3 : sg (3 : Fin 7) = (4 : Fin 8) := rfl
theorem sg_4 : sg (4 : Fin 7) = (5 : Fin 8) := rfl
theorem sg_5 : sg (5 : Fin 7) = (6 : Fin 8) := rfl
theorem sg_6 : sg (6 : Fin 7) = (7 : Fin 8) := rfl

theorem inst_arr (v : Fin 8 → ℝ) (η : ℝ) (hη : η ≤ (1 / 6272 : ℝ)) (hv : ∀ j, |v j - sv j| ≤ η) :
    ∃ c₀ : Fin 1, Alive (mxOf (fun i => |v (sg i) - v (1 : Fin 8)|) EXs hEXne) (mnOf (fun i => |v (sg i) - v (1 : Fin 8)|) ENs hENne) c₀ ∧
      (∀ c, c < c₀ → ¬ Alive (mxOf (fun i => |v (sg i) - v (1 : Fin 8)|) EXs hEXne) (mnOf (fun i => |v (sg i) - v (1 : Fin 8)|) ENs hENne) c) ∧
      IsLeast {t : ℝ | 0 < t ∧ IsolatedAt v (1 : Fin 8) t} (mxOf (fun i => |v (sg i) - v (1 : Fin 8)|) EXs hEXne c₀) := by
  have hσk : ∀ i, sg i ≠ (1 : Fin 8) := by decide
  have hσ : ∀ j : Fin 8, j ≠ (1 : Fin 8) → ∃ i, sg i = j := by decide
  have hpr : ∀ i, pr i = |sv (sg i) - sv (1 : Fin 8)| := by
    intro i; rcases fin7_cases i with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6, sv_0, sv_1, sv_2, sv_3, sv_4, sv_5, sv_6, sv_7, sg_0, sg_1, sg_2, sg_3, sg_4, sg_5, sg_6]
  have hdev : ∀ i, |(|v (sg i) - v (1 : Fin 8)| - pr i)| ≤ 2 * η := by
    intro i; rw [hpr i]; exact reading_dev v sv η hv (sg i) (1 : Fin 8)
  obtain ⟨c₀, hal, hbf, hT0⟩ := inst (fun i => |v (sg i) - v (1 : Fin 8)|) (2 * η) (by linarith) hdev
  have hset : {t : ℝ | 0 < t ∧ IsolatedAt v (1 : Fin 8) t} =
      {t : ℝ | 0 < t ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (|v (sg i) - v (1 : Fin 8)| * t)} := by
    ext t; simp only [Set.mem_setOf_eq]; rw [iso_iff_readings v (1 : Fin 8) sg hσk hσ t]
  rw [hset]; exact ⟨c₀, hal, hbf, hT0⟩

#print axioms inst_arr

end Fresh.CertRR.R11161



/-!
# Landing certificate `CertRR.R11168`: speeds (1, 2, 6, 7, 8, 9, 10, 14), subject index 0

Generated 2026-10-24 by `experiments/n8/cert_gen_v1.py` (exact Fractions).  Baseline readings [1, 5, 6, 7, 8, 9, 13].  Components up to the first wide one: 1.
Radius: speeds within `η ≤ 1/25088` of the baseline speeds, giving `ε = 2η ≤ 1/12544`.  Covering margin `μ = 1/512`.
`hcov` is **[PROVISIONAL: covering]**, supporting the claim that the first lonely instant of this subject is the largest exit of the first alive component.
Result `inst_arr`: for such `v`, the subject has a first isolation (a least element over all `t > 0`).  Grades: [L].
-/

open Classical

namespace Fresh.CertRR.R11168

open Fresh Fresh.LandingCert Fresh.LandingRule

noncomputable def pr : Fin 7 → ℝ := ![(1 : ℝ), (5 : ℝ), (6 : ℝ), (7 : ℝ), (8 : ℝ), (9 : ℝ), (13 : ℝ)]
noncomputable def aV : Fin 1 → ℝ := ![(17 / 64 : ℝ)]
noncomputable def bV : Fin 1 → ℝ := ![(15 / 56 : ℝ)]
noncomputable def dV : Fin 1 → ℝ := ![(1 / 224 : ℝ)]
noncomputable def TV : Fin 1 → ℝ := ![(61 / 224 : ℝ)]
def ZV : Fin 1 → ℤ := ![6]
noncomputable def HV : ℝ := (121 / 448 : ℝ)
noncomputable def EXs (c : Fin 1) : Finset (Fin 7 × ℤ) :=
  (Finset.univ ×ˢ Finset.Icc 0 (ZV c)).filter (fun q => ((q.2 : ℝ) + 1 / 8) / pr q.1 = aV c)
noncomputable def ENs (c : Fin 1) : Finset (Fin 7 × ℤ) :=
  (Finset.univ ×ˢ Finset.Icc 0 (ZV c)).filter (fun q => ((q.2 : ℝ) - 1 / 8) / pr q.1 = bV c)

theorem hp : ∀ i, 1 ≤ pr i ∧ pr i ≤ (13 : ℝ) := by intro i; fin_cases i <;> norm_num [pr]
theorem hp1 : ∀ i, 1 ≤ pr i := fun i => (hp i).1
theorem pr_0 : pr (0 : Fin 7) = (1 : ℝ) := rfl
theorem pr_1 : pr (1 : Fin 7) = (5 : ℝ) := rfl
theorem pr_2 : pr (2 : Fin 7) = (6 : ℝ) := rfl
theorem pr_3 : pr (3 : Fin 7) = (7 : ℝ) := rfl
theorem pr_4 : pr (4 : Fin 7) = (8 : ℝ) := rfl
theorem pr_5 : pr (5 : Fin 7) = (9 : ℝ) := rfl
theorem pr_6 : pr (6 : Fin 7) = (13 : ℝ) := rfl
theorem aV_0 : aV (0 : Fin 1) = (17 / 64 : ℝ) := rfl
theorem bV_0 : bV (0 : Fin 1) = (15 / 56 : ℝ) := rfl
theorem dV_0 : dV (0 : Fin 1) = (1 / 224 : ℝ) := rfl
theorem TV_0 : TV (0 : Fin 1) = (61 / 224 : ℝ) := rfl
theorem ZV_0 : ZV (0 : Fin 1) = (6 : ℤ) := rfl
theorem hab : ∀ c, aV c ≤ bV c := by intro c; fin_cases c <;> norm_num [aV, bV]
theorem hd0 : ∀ c, 0 < dV c := by intro c; fin_cases c <;> norm_num [dV]
theorem hdP : ∀ c, dV c ≤ 1 / (4 * (13 : ℝ)) := by intro c; fin_cases c <;> norm_num [dV]
theorem haP : ∀ c, dV c < aV c := by intro c; fin_cases c <;> norm_num [dV, aV]
theorem hT : ∀ c, bV c + dV c ≤ TV c := by intro c; fin_cases c <;> norm_num [bV, dV, TV]
theorem hZ : ∀ c, ((13 : ℝ) + 1) * TV c + 1 ≤ (ZV c : ℝ) := by intro c; fin_cases c <;> norm_num [TV, ZV]
theorem hE (ε : ℝ) (hε : ε ≤ (1 / 12544 : ℝ)) : ∀ c, 8 * ((ZV c : ℝ) + 1) * ε ≤ dV c := by
  intro c; fin_cases c <;> norm_num [ZV, dV] <;> linarith
theorem hcls : ∀ c i, ∀ z : ℤ, 0 ≤ z → z ≤ ZV c →
    ((z : ℝ) + 1 / 8) / pr i ≤ aV c - dV c ∨ bV c + dV c ≤ ((z : ℝ) - 1 / 8) / pr i ∨
      ((z : ℝ) + 1 / 8) / pr i = aV c ∨ ((z : ℝ) - 1 / 8) / pr i = bV c := by
  intro c i z h0 h1
  fin_cases c <;> fin_cases i <;> simp [ZV] at h1 <;> interval_cases z <;> norm_num [pr, aV, bV, dV]
theorem hEXne : ∀ c, (EXs c).Nonempty := by
  intro c
  fin_cases c
  · exact ⟨(4, 2), by simp [EXs, ZV, pr, aV] <;> norm_num⟩
theorem hENne : ∀ c, (ENs c).Nonempty := by
  intro c
  fin_cases c
  · exact ⟨(3, 2), by simp [ENs, ZV, pr, bV] <;> norm_num⟩
theorem hEXdef : ∀ c, ∀ q : Fin 7 × ℤ, q ∈ EXs c ↔ 0 ≤ q.2 ∧ q.2 ≤ ZV c ∧ ((q.2 : ℝ) + 1 / 8) / pr q.1 = aV c := by
  intro c q
  simp only [EXs, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, Finset.mem_Icc, true_and]
  tauto
theorem hENdef : ∀ c, ∀ q : Fin 7 × ℤ, q ∈ ENs c ↔ 0 ≤ q.2 ∧ q.2 ≤ ZV c ∧ ((q.2 : ℝ) - 1 / 8) / pr q.1 = bV c := by
  intro c q
  simp only [ENs, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, Finset.mem_Icc, true_and]
  tauto
theorem hsepL : ∀ c c' : Fin 1, c < c' → bV c + dV c / 2 < aV c' - dV c' / 2 := by
  intro c c' h
  fin_cases c <;> fin_cases c' <;> simp at h ⊢ <;> norm_num [aV, bV, dV]
theorem hHL : ∀ c, bV c + dV c / 2 ≤ HV := by intro c; fin_cases c <;> norm_num [bV, dV, HV]

theorem gap0 (x : Fin 7 → ℝ) (ε : ℝ) (hdev : ∀ i, |x i - pr i| ≤ ε) (hεH : ε * HV ≤ (1 / 512 : ℝ) / 2) (t : ℝ) (h0 : 0 ≤ t)
    (hHt : t ≤ HV) (h1 : (0 : ℝ) ≤ t) (h2 : t ≤ (59 / 224 : ℝ)) (hlon : ∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)) : False := by
  rcases le_total t (63 / 512 : ℝ) with hs0 | hs0
  · exact zone_kill_gen pr x ε HV (1 / 512 : ℝ) hp1 hdev hεH (by norm_num) (0 : Fin 7) 0 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (0 : Fin 7))
  rcases le_total t (71 / 512 : ℝ) with hs1 | hs1
  · exact zone_kill_gen pr x ε HV (1 / 512 : ℝ) hp1 hdev hεH (by norm_num) (4 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (4 : Fin 7))
  rcases le_total t (569 / 3584 : ℝ) with hs2 | hs2
  · exact zone_kill_gen pr x ε HV (1 / 512 : ℝ) hp1 hdev hεH (by norm_num) (3 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (3 : Fin 7))
  rcases le_total t (95 / 512 : ℝ) with hs3 | hs3
  · exact zone_kill_gen pr x ε HV (1 / 512 : ℝ) hp1 hdev hεH (by norm_num) (2 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (2 : Fin 7))
  rcases le_total t (571 / 2560 : ℝ) with hs4 | hs4
  · exact zone_kill_gen pr x ε HV (1 / 512 : ℝ) hp1 hdev hεH (by norm_num) (1 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (1 : Fin 7))
  rcases le_total t (1079 / 4608 : ℝ) with hs5 | hs5
  · exact zone_kill_gen pr x ε HV (1 / 512 : ℝ) hp1 hdev hεH (by norm_num) (5 : Fin 7) 2 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (5 : Fin 7))
  rcases le_total t (1587 / 6656 : ℝ) with hs6 | hs6
  · exact zone_kill_gen pr x ε HV (1 / 512 : ℝ) hp1 hdev hεH (by norm_num) (6 : Fin 7) 3 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (6 : Fin 7))
  exact zone_kill_gen pr x ε HV (1 / 512 : ℝ) hp1 hdev hεH (by norm_num) (4 : Fin 7) 2 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (4 : Fin 7))
theorem cov (x : Fin 7 → ℝ) (ε : ℝ) (hε : ε ≤ (1 / 12544 : ℝ)) (hdev : ∀ i, |x i - pr i| ≤ ε) :
    ∀ t : ℝ, 0 < t → t ≤ HV → (∀ c, ¬ (aV c - dV c / 2 ≤ t ∧ t ≤ bV c + dV c / 2)) →
      ¬ (∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)) := by
  intro t h0 hHt hnone hlon
  have hεH : ε * HV ≤ (1 / 512 : ℝ) / 2 := by
    have hε0 : 0 ≤ ε := le_trans (abs_nonneg _) (hdev 0)
    have : ε * HV ≤ (1 / 12544 : ℝ) * HV := mul_le_mul_of_nonneg_right hε (by norm_num [HV])
    have h2 : (1 / 12544 : ℝ) * HV ≤ (1 / 512 : ℝ) / 2 := by norm_num [HV]
    linarith
  have n0 := hnone (0 : Fin 1)
  rw [aV_0, bV_0, dV_0] at n0
  rcases lt_or_ge t (59 / 224 : ℝ) with c0 | c0
  · exact gap0 x ε hdev hεH t h0.le hHt h0.le (by linarith) hlon
  have d0 : (121 / 448 : ℝ) < t := by
    by_contra hc; push Not at hc; exact n0 ⟨by linarith, by linarith⟩
  have hHv : HV = (121 / 448 : ℝ) := rfl
  exact absurd (by linarith : t ≤ (121 / 448 : ℝ)) (not_le.2 d0)

theorem inst (x : Fin 7 → ℝ) (ε : ℝ) (hε : ε ≤ (1 / 12544 : ℝ)) (hdev : ∀ i, |x i - pr i| ≤ ε) :
    ∃ c₀ : Fin 1, Alive (mxOf x EXs hEXne) (mnOf x ENs hENne) c₀ ∧
      (∀ c, c < c₀ → ¬ Alive (mxOf x EXs hEXne) (mnOf x ENs hENne) c) ∧
      IsLeast {t : ℝ | 0 < t ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)} (mxOf x EXs hEXne c₀) :=
  landing_cert 1 (13 : ℝ) (by norm_num) pr x hp ε hdev aV bV dV TV ZV hab hd0 hdP haP hT hZ (hE ε hε) hcls EXs ENs hEXne hENne
    hEXdef hENdef hsepL HV hHL (cov x ε hε hdev) (0 : Fin 1) (by rw [dV_0, bV_0, aV_0]; norm_num)

noncomputable def sv : Fin 8 → ℝ := ![(1 : ℝ), (2 : ℝ), (6 : ℝ), (7 : ℝ), (8 : ℝ), (9 : ℝ), (10 : ℝ), (14 : ℝ)]
def sg : Fin 7 → Fin 8 := ![1, 2, 3, 4, 5, 6, 7]

theorem sv_0 : sv (0 : Fin 8) = (1 : ℝ) := rfl
theorem sv_1 : sv (1 : Fin 8) = (2 : ℝ) := rfl
theorem sv_2 : sv (2 : Fin 8) = (6 : ℝ) := rfl
theorem sv_3 : sv (3 : Fin 8) = (7 : ℝ) := rfl
theorem sv_4 : sv (4 : Fin 8) = (8 : ℝ) := rfl
theorem sv_5 : sv (5 : Fin 8) = (9 : ℝ) := rfl
theorem sv_6 : sv (6 : Fin 8) = (10 : ℝ) := rfl
theorem sv_7 : sv (7 : Fin 8) = (14 : ℝ) := rfl
theorem sg_0 : sg (0 : Fin 7) = (1 : Fin 8) := rfl
theorem sg_1 : sg (1 : Fin 7) = (2 : Fin 8) := rfl
theorem sg_2 : sg (2 : Fin 7) = (3 : Fin 8) := rfl
theorem sg_3 : sg (3 : Fin 7) = (4 : Fin 8) := rfl
theorem sg_4 : sg (4 : Fin 7) = (5 : Fin 8) := rfl
theorem sg_5 : sg (5 : Fin 7) = (6 : Fin 8) := rfl
theorem sg_6 : sg (6 : Fin 7) = (7 : Fin 8) := rfl

theorem inst_arr (v : Fin 8 → ℝ) (η : ℝ) (hη : η ≤ (1 / 25088 : ℝ)) (hv : ∀ j, |v j - sv j| ≤ η) :
    ∃ c₀ : Fin 1, Alive (mxOf (fun i => |v (sg i) - v (0 : Fin 8)|) EXs hEXne) (mnOf (fun i => |v (sg i) - v (0 : Fin 8)|) ENs hENne) c₀ ∧
      (∀ c, c < c₀ → ¬ Alive (mxOf (fun i => |v (sg i) - v (0 : Fin 8)|) EXs hEXne) (mnOf (fun i => |v (sg i) - v (0 : Fin 8)|) ENs hENne) c) ∧
      IsLeast {t : ℝ | 0 < t ∧ IsolatedAt v (0 : Fin 8) t} (mxOf (fun i => |v (sg i) - v (0 : Fin 8)|) EXs hEXne c₀) := by
  have hσk : ∀ i, sg i ≠ (0 : Fin 8) := by decide
  have hσ : ∀ j : Fin 8, j ≠ (0 : Fin 8) → ∃ i, sg i = j := by decide
  have hpr : ∀ i, pr i = |sv (sg i) - sv (0 : Fin 8)| := by
    intro i; rcases fin7_cases i with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6, sv_0, sv_1, sv_2, sv_3, sv_4, sv_5, sv_6, sv_7, sg_0, sg_1, sg_2, sg_3, sg_4, sg_5, sg_6]
  have hdev : ∀ i, |(|v (sg i) - v (0 : Fin 8)| - pr i)| ≤ 2 * η := by
    intro i; rw [hpr i]; exact reading_dev v sv η hv (sg i) (0 : Fin 8)
  obtain ⟨c₀, hal, hbf, hT0⟩ := inst (fun i => |v (sg i) - v (0 : Fin 8)|) (2 * η) (by linarith) hdev
  have hset : {t : ℝ | 0 < t ∧ IsolatedAt v (0 : Fin 8) t} =
      {t : ℝ | 0 < t ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (|v (sg i) - v (0 : Fin 8)| * t)} := by
    ext t; simp only [Set.mem_setOf_eq]; rw [iso_iff_readings v (0 : Fin 8) sg hσk hσ t]
  rw [hset]; exact ⟨c₀, hal, hbf, hT0⟩

#print axioms inst_arr

end Fresh.CertRR.R11168



/-!
# Landing certificate `CertRR.R11169`: speeds (1, 2, 6, 7, 8, 9, 10, 14), subject index 1

Generated 2026-10-24 by `experiments/n8/cert_gen_v1.py` (exact Fractions).  Baseline readings [1, 4, 5, 6, 7, 8, 12].  Components up to the first wide one: 1.
Radius: speeds within `η ≤ 1/10752` of the baseline speeds, giving `ε = 2η ≤ 1/5376`.  Covering margin `μ = 1/512`.
`hcov` is **[PROVISIONAL: covering]**, supporting the claim that the first lonely instant of this subject is the largest exit of the first alive component.
Result `inst_arr`: for such `v`, the subject has a first isolation (a least element over all `t > 0`).  Grades: [L].
-/

open Classical

namespace Fresh.CertRR.R11169

open Fresh Fresh.LandingCert Fresh.LandingRule

noncomputable def pr : Fin 7 → ℝ := ![(1 : ℝ), (4 : ℝ), (5 : ℝ), (6 : ℝ), (7 : ℝ), (8 : ℝ), (12 : ℝ)]
noncomputable def aV : Fin 1 → ℝ := ![(17 / 56 : ℝ)]
noncomputable def bV : Fin 1 → ℝ := ![(5 / 16 : ℝ)]
noncomputable def dV : Fin 1 → ℝ := ![(1 / 96 : ℝ)]
noncomputable def TV : Fin 1 → ℝ := ![(31 / 96 : ℝ)]
def ZV : Fin 1 → ℤ := ![6]
noncomputable def HV : ℝ := (61 / 192 : ℝ)
noncomputable def EXs (c : Fin 1) : Finset (Fin 7 × ℤ) :=
  (Finset.univ ×ˢ Finset.Icc 0 (ZV c)).filter (fun q => ((q.2 : ℝ) + 1 / 8) / pr q.1 = aV c)
noncomputable def ENs (c : Fin 1) : Finset (Fin 7 × ℤ) :=
  (Finset.univ ×ˢ Finset.Icc 0 (ZV c)).filter (fun q => ((q.2 : ℝ) - 1 / 8) / pr q.1 = bV c)

theorem hp : ∀ i, 1 ≤ pr i ∧ pr i ≤ (12 : ℝ) := by intro i; fin_cases i <;> norm_num [pr]
theorem hp1 : ∀ i, 1 ≤ pr i := fun i => (hp i).1
theorem pr_0 : pr (0 : Fin 7) = (1 : ℝ) := rfl
theorem pr_1 : pr (1 : Fin 7) = (4 : ℝ) := rfl
theorem pr_2 : pr (2 : Fin 7) = (5 : ℝ) := rfl
theorem pr_3 : pr (3 : Fin 7) = (6 : ℝ) := rfl
theorem pr_4 : pr (4 : Fin 7) = (7 : ℝ) := rfl
theorem pr_5 : pr (5 : Fin 7) = (8 : ℝ) := rfl
theorem pr_6 : pr (6 : Fin 7) = (12 : ℝ) := rfl
theorem aV_0 : aV (0 : Fin 1) = (17 / 56 : ℝ) := rfl
theorem bV_0 : bV (0 : Fin 1) = (5 / 16 : ℝ) := rfl
theorem dV_0 : dV (0 : Fin 1) = (1 / 96 : ℝ) := rfl
theorem TV_0 : TV (0 : Fin 1) = (31 / 96 : ℝ) := rfl
theorem ZV_0 : ZV (0 : Fin 1) = (6 : ℤ) := rfl
theorem hab : ∀ c, aV c ≤ bV c := by intro c; fin_cases c <;> norm_num [aV, bV]
theorem hd0 : ∀ c, 0 < dV c := by intro c; fin_cases c <;> norm_num [dV]
theorem hdP : ∀ c, dV c ≤ 1 / (4 * (12 : ℝ)) := by intro c; fin_cases c <;> norm_num [dV]
theorem haP : ∀ c, dV c < aV c := by intro c; fin_cases c <;> norm_num [dV, aV]
theorem hT : ∀ c, bV c + dV c ≤ TV c := by intro c; fin_cases c <;> norm_num [bV, dV, TV]
theorem hZ : ∀ c, ((12 : ℝ) + 1) * TV c + 1 ≤ (ZV c : ℝ) := by intro c; fin_cases c <;> norm_num [TV, ZV]
theorem hE (ε : ℝ) (hε : ε ≤ (1 / 5376 : ℝ)) : ∀ c, 8 * ((ZV c : ℝ) + 1) * ε ≤ dV c := by
  intro c; fin_cases c <;> norm_num [ZV, dV] <;> linarith
theorem hcls : ∀ c i, ∀ z : ℤ, 0 ≤ z → z ≤ ZV c →
    ((z : ℝ) + 1 / 8) / pr i ≤ aV c - dV c ∨ bV c + dV c ≤ ((z : ℝ) - 1 / 8) / pr i ∨
      ((z : ℝ) + 1 / 8) / pr i = aV c ∨ ((z : ℝ) - 1 / 8) / pr i = bV c := by
  intro c i z h0 h1
  fin_cases c <;> fin_cases i <;> simp [ZV] at h1 <;> interval_cases z <;> norm_num [pr, aV, bV, dV]
theorem hEXne : ∀ c, (EXs c).Nonempty := by
  intro c
  fin_cases c
  · exact ⟨(4, 2), by simp [EXs, ZV, pr, aV] <;> norm_num⟩
theorem hENne : ∀ c, (ENs c).Nonempty := by
  intro c
  fin_cases c
  · exact ⟨(3, 2), by simp [ENs, ZV, pr, bV] <;> norm_num⟩
theorem hEXdef : ∀ c, ∀ q : Fin 7 × ℤ, q ∈ EXs c ↔ 0 ≤ q.2 ∧ q.2 ≤ ZV c ∧ ((q.2 : ℝ) + 1 / 8) / pr q.1 = aV c := by
  intro c q
  simp only [EXs, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, Finset.mem_Icc, true_and]
  tauto
theorem hENdef : ∀ c, ∀ q : Fin 7 × ℤ, q ∈ ENs c ↔ 0 ≤ q.2 ∧ q.2 ≤ ZV c ∧ ((q.2 : ℝ) - 1 / 8) / pr q.1 = bV c := by
  intro c q
  simp only [ENs, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, Finset.mem_Icc, true_and]
  tauto
theorem hsepL : ∀ c c' : Fin 1, c < c' → bV c + dV c / 2 < aV c' - dV c' / 2 := by
  intro c c' h
  fin_cases c <;> fin_cases c' <;> simp at h ⊢ <;> norm_num [aV, bV, dV]
theorem hHL : ∀ c, bV c + dV c / 2 ≤ HV := by intro c; fin_cases c <;> norm_num [bV, dV, HV]

theorem gap0 (x : Fin 7 → ℝ) (ε : ℝ) (hdev : ∀ i, |x i - pr i| ≤ ε) (hεH : ε * HV ≤ (1 / 512 : ℝ) / 2) (t : ℝ) (h0 : 0 ≤ t)
    (hHt : t ≤ HV) (h1 : (0 : ℝ) ≤ t) (h2 : t ≤ (401 / 1344 : ℝ)) (hlon : ∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)) : False := by
  rcases le_total t (63 / 512 : ℝ) with hs0 | hs0
  · exact zone_kill_gen pr x ε HV (1 / 512 : ℝ) hp1 hdev hεH (by norm_num) (0 : Fin 7) 0 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (0 : Fin 7))
  rcases le_total t (71 / 512 : ℝ) with hs1 | hs1
  · exact zone_kill_gen pr x ε HV (1 / 512 : ℝ) hp1 hdev hεH (by norm_num) (5 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (5 : Fin 7))
  rcases le_total t (569 / 3584 : ℝ) with hs2 | hs2
  · exact zone_kill_gen pr x ε HV (1 / 512 : ℝ) hp1 hdev hεH (by norm_num) (4 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (4 : Fin 7))
  rcases le_total t (95 / 512 : ℝ) with hs3 | hs3
  · exact zone_kill_gen pr x ε HV (1 / 512 : ℝ) hp1 hdev hεH (by norm_num) (3 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (3 : Fin 7))
  rcases le_total t (571 / 2560 : ℝ) with hs4 | hs4
  · exact zone_kill_gen pr x ε HV (1 / 512 : ℝ) hp1 hdev hεH (by norm_num) (2 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (2 : Fin 7))
  rcases le_total t (143 / 512 : ℝ) with hs5 | hs5
  · exact zone_kill_gen pr x ε HV (1 / 512 : ℝ) hp1 hdev hεH (by norm_num) (1 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (1 : Fin 7))
  exact zone_kill_gen pr x ε HV (1 / 512 : ℝ) hp1 hdev hεH (by norm_num) (4 : Fin 7) 2 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (4 : Fin 7))
theorem cov (x : Fin 7 → ℝ) (ε : ℝ) (hε : ε ≤ (1 / 5376 : ℝ)) (hdev : ∀ i, |x i - pr i| ≤ ε) :
    ∀ t : ℝ, 0 < t → t ≤ HV → (∀ c, ¬ (aV c - dV c / 2 ≤ t ∧ t ≤ bV c + dV c / 2)) →
      ¬ (∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)) := by
  intro t h0 hHt hnone hlon
  have hεH : ε * HV ≤ (1 / 512 : ℝ) / 2 := by
    have hε0 : 0 ≤ ε := le_trans (abs_nonneg _) (hdev 0)
    have : ε * HV ≤ (1 / 5376 : ℝ) * HV := mul_le_mul_of_nonneg_right hε (by norm_num [HV])
    have h2 : (1 / 5376 : ℝ) * HV ≤ (1 / 512 : ℝ) / 2 := by norm_num [HV]
    linarith
  have n0 := hnone (0 : Fin 1)
  rw [aV_0, bV_0, dV_0] at n0
  rcases lt_or_ge t (401 / 1344 : ℝ) with c0 | c0
  · exact gap0 x ε hdev hεH t h0.le hHt h0.le (by linarith) hlon
  have d0 : (61 / 192 : ℝ) < t := by
    by_contra hc; push Not at hc; exact n0 ⟨by linarith, by linarith⟩
  have hHv : HV = (61 / 192 : ℝ) := rfl
  exact absurd (by linarith : t ≤ (61 / 192 : ℝ)) (not_le.2 d0)

theorem inst (x : Fin 7 → ℝ) (ε : ℝ) (hε : ε ≤ (1 / 5376 : ℝ)) (hdev : ∀ i, |x i - pr i| ≤ ε) :
    ∃ c₀ : Fin 1, Alive (mxOf x EXs hEXne) (mnOf x ENs hENne) c₀ ∧
      (∀ c, c < c₀ → ¬ Alive (mxOf x EXs hEXne) (mnOf x ENs hENne) c) ∧
      IsLeast {t : ℝ | 0 < t ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)} (mxOf x EXs hEXne c₀) :=
  landing_cert 1 (12 : ℝ) (by norm_num) pr x hp ε hdev aV bV dV TV ZV hab hd0 hdP haP hT hZ (hE ε hε) hcls EXs ENs hEXne hENne
    hEXdef hENdef hsepL HV hHL (cov x ε hε hdev) (0 : Fin 1) (by rw [dV_0, bV_0, aV_0]; norm_num)

noncomputable def sv : Fin 8 → ℝ := ![(1 : ℝ), (2 : ℝ), (6 : ℝ), (7 : ℝ), (8 : ℝ), (9 : ℝ), (10 : ℝ), (14 : ℝ)]
def sg : Fin 7 → Fin 8 := ![0, 2, 3, 4, 5, 6, 7]

theorem sv_0 : sv (0 : Fin 8) = (1 : ℝ) := rfl
theorem sv_1 : sv (1 : Fin 8) = (2 : ℝ) := rfl
theorem sv_2 : sv (2 : Fin 8) = (6 : ℝ) := rfl
theorem sv_3 : sv (3 : Fin 8) = (7 : ℝ) := rfl
theorem sv_4 : sv (4 : Fin 8) = (8 : ℝ) := rfl
theorem sv_5 : sv (5 : Fin 8) = (9 : ℝ) := rfl
theorem sv_6 : sv (6 : Fin 8) = (10 : ℝ) := rfl
theorem sv_7 : sv (7 : Fin 8) = (14 : ℝ) := rfl
theorem sg_0 : sg (0 : Fin 7) = (0 : Fin 8) := rfl
theorem sg_1 : sg (1 : Fin 7) = (2 : Fin 8) := rfl
theorem sg_2 : sg (2 : Fin 7) = (3 : Fin 8) := rfl
theorem sg_3 : sg (3 : Fin 7) = (4 : Fin 8) := rfl
theorem sg_4 : sg (4 : Fin 7) = (5 : Fin 8) := rfl
theorem sg_5 : sg (5 : Fin 7) = (6 : Fin 8) := rfl
theorem sg_6 : sg (6 : Fin 7) = (7 : Fin 8) := rfl

theorem inst_arr (v : Fin 8 → ℝ) (η : ℝ) (hη : η ≤ (1 / 10752 : ℝ)) (hv : ∀ j, |v j - sv j| ≤ η) :
    ∃ c₀ : Fin 1, Alive (mxOf (fun i => |v (sg i) - v (1 : Fin 8)|) EXs hEXne) (mnOf (fun i => |v (sg i) - v (1 : Fin 8)|) ENs hENne) c₀ ∧
      (∀ c, c < c₀ → ¬ Alive (mxOf (fun i => |v (sg i) - v (1 : Fin 8)|) EXs hEXne) (mnOf (fun i => |v (sg i) - v (1 : Fin 8)|) ENs hENne) c) ∧
      IsLeast {t : ℝ | 0 < t ∧ IsolatedAt v (1 : Fin 8) t} (mxOf (fun i => |v (sg i) - v (1 : Fin 8)|) EXs hEXne c₀) := by
  have hσk : ∀ i, sg i ≠ (1 : Fin 8) := by decide
  have hσ : ∀ j : Fin 8, j ≠ (1 : Fin 8) → ∃ i, sg i = j := by decide
  have hpr : ∀ i, pr i = |sv (sg i) - sv (1 : Fin 8)| := by
    intro i; rcases fin7_cases i with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6, sv_0, sv_1, sv_2, sv_3, sv_4, sv_5, sv_6, sv_7, sg_0, sg_1, sg_2, sg_3, sg_4, sg_5, sg_6]
  have hdev : ∀ i, |(|v (sg i) - v (1 : Fin 8)| - pr i)| ≤ 2 * η := by
    intro i; rw [hpr i]; exact reading_dev v sv η hv (sg i) (1 : Fin 8)
  obtain ⟨c₀, hal, hbf, hT0⟩ := inst (fun i => |v (sg i) - v (1 : Fin 8)|) (2 * η) (by linarith) hdev
  have hset : {t : ℝ | 0 < t ∧ IsolatedAt v (1 : Fin 8) t} =
      {t : ℝ | 0 < t ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (|v (sg i) - v (1 : Fin 8)| * t)} := by
    ext t; simp only [Set.mem_setOf_eq]; rw [iso_iff_readings v (1 : Fin 8) sg hσk hσ t]
  rw [hset]; exact ⟨c₀, hal, hbf, hT0⟩

#print axioms inst_arr

end Fresh.CertRR.R11169



/-!
# Landing certificate `CertRR.R11175`: speeds (1, 2, 6, 7, 8, 9, 10, 14), subject index 7

Generated 2026-10-24 by `experiments/n8/cert_gen_v1.py` (exact Fractions).  Baseline readings [13, 12, 8, 7, 6, 5, 4].  Components up to the first wide one: 1.
Radius: speeds within `η ≤ 1/11412` of the baseline speeds, giving `ε = 2η ≤ 1/5706`.  Covering margin `μ = 1/512`.
`hcov` is **[PROVISIONAL: covering]**, supporting the claim that the first lonely instant of this subject is the largest exit of the first alive component.
Result `inst_arr`: for such `v`, the subject has a first isolation (a least element over all `t > 0`).  Grades: [L].
-/

open Classical

namespace Fresh.CertRR.R11175

open Fresh Fresh.LandingCert Fresh.LandingRule

noncomputable def pr : Fin 7 → ℝ := ![(13 : ℝ), (12 : ℝ), (8 : ℝ), (7 : ℝ), (6 : ℝ), (5 : ℝ), (4 : ℝ)]
noncomputable def aV : Fin 1 → ℝ := ![(1 / 32 : ℝ)]
noncomputable def bV : Fin 1 → ℝ := ![(7 / 104 : ℝ)]
noncomputable def dV : Fin 1 → ℝ := ![(7 / 1248 : ℝ)]
noncomputable def TV : Fin 1 → ℝ := ![(7 / 96 : ℝ)]
def ZV : Fin 1 → ℤ := ![3]
noncomputable def HV : ℝ := (175 / 2496 : ℝ)
noncomputable def EXs (c : Fin 1) : Finset (Fin 7 × ℤ) :=
  (Finset.univ ×ˢ Finset.Icc 0 (ZV c)).filter (fun q => ((q.2 : ℝ) + 1 / 8) / pr q.1 = aV c)
noncomputable def ENs (c : Fin 1) : Finset (Fin 7 × ℤ) :=
  (Finset.univ ×ˢ Finset.Icc 0 (ZV c)).filter (fun q => ((q.2 : ℝ) - 1 / 8) / pr q.1 = bV c)

theorem hp : ∀ i, 1 ≤ pr i ∧ pr i ≤ (13 : ℝ) := by intro i; fin_cases i <;> norm_num [pr]
theorem hp1 : ∀ i, 1 ≤ pr i := fun i => (hp i).1
theorem pr_0 : pr (0 : Fin 7) = (13 : ℝ) := rfl
theorem pr_1 : pr (1 : Fin 7) = (12 : ℝ) := rfl
theorem pr_2 : pr (2 : Fin 7) = (8 : ℝ) := rfl
theorem pr_3 : pr (3 : Fin 7) = (7 : ℝ) := rfl
theorem pr_4 : pr (4 : Fin 7) = (6 : ℝ) := rfl
theorem pr_5 : pr (5 : Fin 7) = (5 : ℝ) := rfl
theorem pr_6 : pr (6 : Fin 7) = (4 : ℝ) := rfl
theorem aV_0 : aV (0 : Fin 1) = (1 / 32 : ℝ) := rfl
theorem bV_0 : bV (0 : Fin 1) = (7 / 104 : ℝ) := rfl
theorem dV_0 : dV (0 : Fin 1) = (7 / 1248 : ℝ) := rfl
theorem TV_0 : TV (0 : Fin 1) = (7 / 96 : ℝ) := rfl
theorem ZV_0 : ZV (0 : Fin 1) = (3 : ℤ) := rfl
theorem hab : ∀ c, aV c ≤ bV c := by intro c; fin_cases c <;> norm_num [aV, bV]
theorem hd0 : ∀ c, 0 < dV c := by intro c; fin_cases c <;> norm_num [dV]
theorem hdP : ∀ c, dV c ≤ 1 / (4 * (13 : ℝ)) := by intro c; fin_cases c <;> norm_num [dV]
theorem haP : ∀ c, dV c < aV c := by intro c; fin_cases c <;> norm_num [dV, aV]
theorem hT : ∀ c, bV c + dV c ≤ TV c := by intro c; fin_cases c <;> norm_num [bV, dV, TV]
theorem hZ : ∀ c, ((13 : ℝ) + 1) * TV c + 1 ≤ (ZV c : ℝ) := by intro c; fin_cases c <;> norm_num [TV, ZV]
theorem hE (ε : ℝ) (hε : ε ≤ (1 / 5706 : ℝ)) : ∀ c, 8 * ((ZV c : ℝ) + 1) * ε ≤ dV c := by
  intro c; fin_cases c <;> norm_num [ZV, dV] <;> linarith
theorem hcls : ∀ c i, ∀ z : ℤ, 0 ≤ z → z ≤ ZV c →
    ((z : ℝ) + 1 / 8) / pr i ≤ aV c - dV c ∨ bV c + dV c ≤ ((z : ℝ) - 1 / 8) / pr i ∨
      ((z : ℝ) + 1 / 8) / pr i = aV c ∨ ((z : ℝ) - 1 / 8) / pr i = bV c := by
  intro c i z h0 h1
  fin_cases c <;> fin_cases i <;> simp [ZV] at h1 <;> interval_cases z <;> norm_num [pr, aV, bV, dV]
theorem hEXne : ∀ c, (EXs c).Nonempty := by
  intro c
  fin_cases c
  · exact ⟨(6, 0), by simp [EXs, ZV, pr, aV] <;> norm_num⟩
theorem hENne : ∀ c, (ENs c).Nonempty := by
  intro c
  fin_cases c
  · exact ⟨(0, 1), by simp [ENs, ZV, pr, bV] <;> norm_num⟩
theorem hEXdef : ∀ c, ∀ q : Fin 7 × ℤ, q ∈ EXs c ↔ 0 ≤ q.2 ∧ q.2 ≤ ZV c ∧ ((q.2 : ℝ) + 1 / 8) / pr q.1 = aV c := by
  intro c q
  simp only [EXs, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, Finset.mem_Icc, true_and]
  tauto
theorem hENdef : ∀ c, ∀ q : Fin 7 × ℤ, q ∈ ENs c ↔ 0 ≤ q.2 ∧ q.2 ≤ ZV c ∧ ((q.2 : ℝ) - 1 / 8) / pr q.1 = bV c := by
  intro c q
  simp only [ENs, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, Finset.mem_Icc, true_and]
  tauto
theorem hsepL : ∀ c c' : Fin 1, c < c' → bV c + dV c / 2 < aV c' - dV c' / 2 := by
  intro c c' h
  fin_cases c <;> fin_cases c' <;> simp at h ⊢ <;> norm_num [aV, bV, dV]
theorem hHL : ∀ c, bV c + dV c / 2 ≤ HV := by intro c; fin_cases c <;> norm_num [bV, dV, HV]

theorem gap0 (x : Fin 7 → ℝ) (ε : ℝ) (hdev : ∀ i, |x i - pr i| ≤ ε) (hεH : ε * HV ≤ (1 / 512 : ℝ) / 2) (t : ℝ) (h0 : 0 ≤ t)
    (hHt : t ≤ HV) (h1 : (0 : ℝ) ≤ t) (h2 : t ≤ (71 / 2496 : ℝ)) (hlon : ∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)) : False := by
  exact zone_kill_gen pr x ε HV (1 / 512 : ℝ) hp1 hdev hεH (by norm_num) (6 : Fin 7) 0 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (6 : Fin 7))
theorem cov (x : Fin 7 → ℝ) (ε : ℝ) (hε : ε ≤ (1 / 5706 : ℝ)) (hdev : ∀ i, |x i - pr i| ≤ ε) :
    ∀ t : ℝ, 0 < t → t ≤ HV → (∀ c, ¬ (aV c - dV c / 2 ≤ t ∧ t ≤ bV c + dV c / 2)) →
      ¬ (∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)) := by
  intro t h0 hHt hnone hlon
  have hεH : ε * HV ≤ (1 / 512 : ℝ) / 2 := by
    have hε0 : 0 ≤ ε := le_trans (abs_nonneg _) (hdev 0)
    have : ε * HV ≤ (1 / 5706 : ℝ) * HV := mul_le_mul_of_nonneg_right hε (by norm_num [HV])
    have h2 : (1 / 5706 : ℝ) * HV ≤ (1 / 512 : ℝ) / 2 := by norm_num [HV]
    linarith
  have n0 := hnone (0 : Fin 1)
  rw [aV_0, bV_0, dV_0] at n0
  rcases lt_or_ge t (71 / 2496 : ℝ) with c0 | c0
  · exact gap0 x ε hdev hεH t h0.le hHt h0.le (by linarith) hlon
  have d0 : (175 / 2496 : ℝ) < t := by
    by_contra hc; push Not at hc; exact n0 ⟨by linarith, by linarith⟩
  have hHv : HV = (175 / 2496 : ℝ) := rfl
  exact absurd (by linarith : t ≤ (175 / 2496 : ℝ)) (not_le.2 d0)

theorem inst (x : Fin 7 → ℝ) (ε : ℝ) (hε : ε ≤ (1 / 5706 : ℝ)) (hdev : ∀ i, |x i - pr i| ≤ ε) :
    ∃ c₀ : Fin 1, Alive (mxOf x EXs hEXne) (mnOf x ENs hENne) c₀ ∧
      (∀ c, c < c₀ → ¬ Alive (mxOf x EXs hEXne) (mnOf x ENs hENne) c) ∧
      IsLeast {t : ℝ | 0 < t ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)} (mxOf x EXs hEXne c₀) :=
  landing_cert 1 (13 : ℝ) (by norm_num) pr x hp ε hdev aV bV dV TV ZV hab hd0 hdP haP hT hZ (hE ε hε) hcls EXs ENs hEXne hENne
    hEXdef hENdef hsepL HV hHL (cov x ε hε hdev) (0 : Fin 1) (by rw [dV_0, bV_0, aV_0]; norm_num)

noncomputable def sv : Fin 8 → ℝ := ![(1 : ℝ), (2 : ℝ), (6 : ℝ), (7 : ℝ), (8 : ℝ), (9 : ℝ), (10 : ℝ), (14 : ℝ)]
def sg : Fin 7 → Fin 8 := ![0, 1, 2, 3, 4, 5, 6]

theorem sv_0 : sv (0 : Fin 8) = (1 : ℝ) := rfl
theorem sv_1 : sv (1 : Fin 8) = (2 : ℝ) := rfl
theorem sv_2 : sv (2 : Fin 8) = (6 : ℝ) := rfl
theorem sv_3 : sv (3 : Fin 8) = (7 : ℝ) := rfl
theorem sv_4 : sv (4 : Fin 8) = (8 : ℝ) := rfl
theorem sv_5 : sv (5 : Fin 8) = (9 : ℝ) := rfl
theorem sv_6 : sv (6 : Fin 8) = (10 : ℝ) := rfl
theorem sv_7 : sv (7 : Fin 8) = (14 : ℝ) := rfl
theorem sg_0 : sg (0 : Fin 7) = (0 : Fin 8) := rfl
theorem sg_1 : sg (1 : Fin 7) = (1 : Fin 8) := rfl
theorem sg_2 : sg (2 : Fin 7) = (2 : Fin 8) := rfl
theorem sg_3 : sg (3 : Fin 7) = (3 : Fin 8) := rfl
theorem sg_4 : sg (4 : Fin 7) = (4 : Fin 8) := rfl
theorem sg_5 : sg (5 : Fin 7) = (5 : Fin 8) := rfl
theorem sg_6 : sg (6 : Fin 7) = (6 : Fin 8) := rfl

theorem inst_arr (v : Fin 8 → ℝ) (η : ℝ) (hη : η ≤ (1 / 11412 : ℝ)) (hv : ∀ j, |v j - sv j| ≤ η) :
    ∃ c₀ : Fin 1, Alive (mxOf (fun i => |v (sg i) - v (7 : Fin 8)|) EXs hEXne) (mnOf (fun i => |v (sg i) - v (7 : Fin 8)|) ENs hENne) c₀ ∧
      (∀ c, c < c₀ → ¬ Alive (mxOf (fun i => |v (sg i) - v (7 : Fin 8)|) EXs hEXne) (mnOf (fun i => |v (sg i) - v (7 : Fin 8)|) ENs hENne) c) ∧
      IsLeast {t : ℝ | 0 < t ∧ IsolatedAt v (7 : Fin 8) t} (mxOf (fun i => |v (sg i) - v (7 : Fin 8)|) EXs hEXne c₀) := by
  have hσk : ∀ i, sg i ≠ (7 : Fin 8) := by decide
  have hσ : ∀ j : Fin 8, j ≠ (7 : Fin 8) → ∃ i, sg i = j := by decide
  have hpr : ∀ i, pr i = |sv (sg i) - sv (7 : Fin 8)| := by
    intro i; rcases fin7_cases i with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6, sv_0, sv_1, sv_2, sv_3, sv_4, sv_5, sv_6, sv_7, sg_0, sg_1, sg_2, sg_3, sg_4, sg_5, sg_6]
  have hdev : ∀ i, |(|v (sg i) - v (7 : Fin 8)| - pr i)| ≤ 2 * η := by
    intro i; rw [hpr i]; exact reading_dev v sv η hv (sg i) (7 : Fin 8)
  obtain ⟨c₀, hal, hbf, hT0⟩ := inst (fun i => |v (sg i) - v (7 : Fin 8)|) (2 * η) (by linarith) hdev
  have hset : {t : ℝ | 0 < t ∧ IsolatedAt v (7 : Fin 8) t} =
      {t : ℝ | 0 < t ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (|v (sg i) - v (7 : Fin 8)| * t)} := by
    ext t; simp only [Set.mem_setOf_eq]; rw [iso_iff_readings v (7 : Fin 8) sg hσk hσ t]
  rw [hset]; exact ⟨c₀, hal, hbf, hT0⟩

#print axioms inst_arr

end Fresh.CertRR.R11175



/-!
# Landing certificate `CertRR.R11176`: speeds (1, 2, 6, 7, 8, 9, 10, 15), subject index 0

Generated 2026-10-24 by `experiments/n8/cert_gen_v1.py` (exact Fractions).  Baseline readings [1, 5, 6, 7, 8, 9, 14].  Components up to the first wide one: 1.
Radius: speeds within `η ≤ 1/25088` of the baseline speeds, giving `ε = 2η ≤ 1/12544`.  Covering margin `μ = 1/2048`.
`hcov` is **[PROVISIONAL: covering]**, supporting the claim that the first lonely instant of this subject is the largest exit of the first alive component.
Result `inst_arr`: for such `v`, the subject has a first isolation (a least element over all `t > 0`).  Grades: [L].
-/

open Classical

namespace Fresh.CertRR.R11176

open Fresh Fresh.LandingCert Fresh.LandingRule

noncomputable def pr : Fin 7 → ℝ := ![(1 : ℝ), (5 : ℝ), (6 : ℝ), (7 : ℝ), (8 : ℝ), (9 : ℝ), (14 : ℝ)]
noncomputable def aV : Fin 1 → ℝ := ![(17 / 64 : ℝ)]
noncomputable def bV : Fin 1 → ℝ := ![(15 / 56 : ℝ)]
noncomputable def dV : Fin 1 → ℝ := ![(1 / 224 : ℝ)]
noncomputable def TV : Fin 1 → ℝ := ![(61 / 224 : ℝ)]
def ZV : Fin 1 → ℤ := ![6]
noncomputable def HV : ℝ := (121 / 448 : ℝ)
noncomputable def EXs (c : Fin 1) : Finset (Fin 7 × ℤ) :=
  (Finset.univ ×ˢ Finset.Icc 0 (ZV c)).filter (fun q => ((q.2 : ℝ) + 1 / 8) / pr q.1 = aV c)
noncomputable def ENs (c : Fin 1) : Finset (Fin 7 × ℤ) :=
  (Finset.univ ×ˢ Finset.Icc 0 (ZV c)).filter (fun q => ((q.2 : ℝ) - 1 / 8) / pr q.1 = bV c)

theorem hp : ∀ i, 1 ≤ pr i ∧ pr i ≤ (14 : ℝ) := by intro i; fin_cases i <;> norm_num [pr]
theorem hp1 : ∀ i, 1 ≤ pr i := fun i => (hp i).1
theorem pr_0 : pr (0 : Fin 7) = (1 : ℝ) := rfl
theorem pr_1 : pr (1 : Fin 7) = (5 : ℝ) := rfl
theorem pr_2 : pr (2 : Fin 7) = (6 : ℝ) := rfl
theorem pr_3 : pr (3 : Fin 7) = (7 : ℝ) := rfl
theorem pr_4 : pr (4 : Fin 7) = (8 : ℝ) := rfl
theorem pr_5 : pr (5 : Fin 7) = (9 : ℝ) := rfl
theorem pr_6 : pr (6 : Fin 7) = (14 : ℝ) := rfl
theorem aV_0 : aV (0 : Fin 1) = (17 / 64 : ℝ) := rfl
theorem bV_0 : bV (0 : Fin 1) = (15 / 56 : ℝ) := rfl
theorem dV_0 : dV (0 : Fin 1) = (1 / 224 : ℝ) := rfl
theorem TV_0 : TV (0 : Fin 1) = (61 / 224 : ℝ) := rfl
theorem ZV_0 : ZV (0 : Fin 1) = (6 : ℤ) := rfl
theorem hab : ∀ c, aV c ≤ bV c := by intro c; fin_cases c <;> norm_num [aV, bV]
theorem hd0 : ∀ c, 0 < dV c := by intro c; fin_cases c <;> norm_num [dV]
theorem hdP : ∀ c, dV c ≤ 1 / (4 * (14 : ℝ)) := by intro c; fin_cases c <;> norm_num [dV]
theorem haP : ∀ c, dV c < aV c := by intro c; fin_cases c <;> norm_num [dV, aV]
theorem hT : ∀ c, bV c + dV c ≤ TV c := by intro c; fin_cases c <;> norm_num [bV, dV, TV]
theorem hZ : ∀ c, ((14 : ℝ) + 1) * TV c + 1 ≤ (ZV c : ℝ) := by intro c; fin_cases c <;> norm_num [TV, ZV]
theorem hE (ε : ℝ) (hε : ε ≤ (1 / 12544 : ℝ)) : ∀ c, 8 * ((ZV c : ℝ) + 1) * ε ≤ dV c := by
  intro c; fin_cases c <;> norm_num [ZV, dV] <;> linarith
theorem hcls : ∀ c i, ∀ z : ℤ, 0 ≤ z → z ≤ ZV c →
    ((z : ℝ) + 1 / 8) / pr i ≤ aV c - dV c ∨ bV c + dV c ≤ ((z : ℝ) - 1 / 8) / pr i ∨
      ((z : ℝ) + 1 / 8) / pr i = aV c ∨ ((z : ℝ) - 1 / 8) / pr i = bV c := by
  intro c i z h0 h1
  fin_cases c <;> fin_cases i <;> simp [ZV] at h1 <;> interval_cases z <;> norm_num [pr, aV, bV, dV]
theorem hEXne : ∀ c, (EXs c).Nonempty := by
  intro c
  fin_cases c
  · exact ⟨(4, 2), by simp [EXs, ZV, pr, aV] <;> norm_num⟩
theorem hENne : ∀ c, (ENs c).Nonempty := by
  intro c
  fin_cases c
  · exact ⟨(3, 2), by simp [ENs, ZV, pr, bV] <;> norm_num⟩
theorem hEXdef : ∀ c, ∀ q : Fin 7 × ℤ, q ∈ EXs c ↔ 0 ≤ q.2 ∧ q.2 ≤ ZV c ∧ ((q.2 : ℝ) + 1 / 8) / pr q.1 = aV c := by
  intro c q
  simp only [EXs, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, Finset.mem_Icc, true_and]
  tauto
theorem hENdef : ∀ c, ∀ q : Fin 7 × ℤ, q ∈ ENs c ↔ 0 ≤ q.2 ∧ q.2 ≤ ZV c ∧ ((q.2 : ℝ) - 1 / 8) / pr q.1 = bV c := by
  intro c q
  simp only [ENs, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, Finset.mem_Icc, true_and]
  tauto
theorem hsepL : ∀ c c' : Fin 1, c < c' → bV c + dV c / 2 < aV c' - dV c' / 2 := by
  intro c c' h
  fin_cases c <;> fin_cases c' <;> simp at h ⊢ <;> norm_num [aV, bV, dV]
theorem hHL : ∀ c, bV c + dV c / 2 ≤ HV := by intro c; fin_cases c <;> norm_num [bV, dV, HV]

theorem gap0 (x : Fin 7 → ℝ) (ε : ℝ) (hdev : ∀ i, |x i - pr i| ≤ ε) (hεH : ε * HV ≤ (1 / 2048 : ℝ) / 2) (t : ℝ) (h0 : 0 ≤ t)
    (hHt : t ≤ HV) (h1 : (0 : ℝ) ≤ t) (h2 : t ≤ (59 / 224 : ℝ)) (hlon : ∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)) : False := by
  rcases le_total t (255 / 2048 : ℝ) with hs0 | hs0
  · exact zone_kill_gen pr x ε HV (1 / 2048 : ℝ) hp1 hdev hεH (by norm_num) (0 : Fin 7) 0 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (0 : Fin 7))
  rcases le_total t (287 / 2048 : ℝ) with hs1 | hs1
  · exact zone_kill_gen pr x ε HV (1 / 2048 : ℝ) hp1 hdev hεH (by norm_num) (4 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (4 : Fin 7))
  rcases le_total t (2297 / 14336 : ℝ) with hs2 | hs2
  · exact zone_kill_gen pr x ε HV (1 / 2048 : ℝ) hp1 hdev hεH (by norm_num) (3 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (3 : Fin 7))
  rcases le_total t (383 / 2048 : ℝ) with hs3 | hs3
  · exact zone_kill_gen pr x ε HV (1 / 2048 : ℝ) hp1 hdev hεH (by norm_num) (2 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (2 : Fin 7))
  rcases le_total t (2299 / 10240 : ℝ) with hs4 | hs4
  · exact zone_kill_gen pr x ε HV (1 / 2048 : ℝ) hp1 hdev hεH (by norm_num) (1 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (1 : Fin 7))
  rcases le_total t (4343 / 18432 : ℝ) with hs5 | hs5
  · exact zone_kill_gen pr x ε HV (1 / 2048 : ℝ) hp1 hdev hεH (by norm_num) (5 : Fin 7) 2 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (5 : Fin 7))
  exact zone_kill_gen pr x ε HV (1 / 2048 : ℝ) hp1 hdev hεH (by norm_num) (4 : Fin 7) 2 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (4 : Fin 7))
theorem cov (x : Fin 7 → ℝ) (ε : ℝ) (hε : ε ≤ (1 / 12544 : ℝ)) (hdev : ∀ i, |x i - pr i| ≤ ε) :
    ∀ t : ℝ, 0 < t → t ≤ HV → (∀ c, ¬ (aV c - dV c / 2 ≤ t ∧ t ≤ bV c + dV c / 2)) →
      ¬ (∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)) := by
  intro t h0 hHt hnone hlon
  have hεH : ε * HV ≤ (1 / 2048 : ℝ) / 2 := by
    have hε0 : 0 ≤ ε := le_trans (abs_nonneg _) (hdev 0)
    have : ε * HV ≤ (1 / 12544 : ℝ) * HV := mul_le_mul_of_nonneg_right hε (by norm_num [HV])
    have h2 : (1 / 12544 : ℝ) * HV ≤ (1 / 2048 : ℝ) / 2 := by norm_num [HV]
    linarith
  have n0 := hnone (0 : Fin 1)
  rw [aV_0, bV_0, dV_0] at n0
  rcases lt_or_ge t (59 / 224 : ℝ) with c0 | c0
  · exact gap0 x ε hdev hεH t h0.le hHt h0.le (by linarith) hlon
  have d0 : (121 / 448 : ℝ) < t := by
    by_contra hc; push Not at hc; exact n0 ⟨by linarith, by linarith⟩
  have hHv : HV = (121 / 448 : ℝ) := rfl
  exact absurd (by linarith : t ≤ (121 / 448 : ℝ)) (not_le.2 d0)

theorem inst (x : Fin 7 → ℝ) (ε : ℝ) (hε : ε ≤ (1 / 12544 : ℝ)) (hdev : ∀ i, |x i - pr i| ≤ ε) :
    ∃ c₀ : Fin 1, Alive (mxOf x EXs hEXne) (mnOf x ENs hENne) c₀ ∧
      (∀ c, c < c₀ → ¬ Alive (mxOf x EXs hEXne) (mnOf x ENs hENne) c) ∧
      IsLeast {t : ℝ | 0 < t ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)} (mxOf x EXs hEXne c₀) :=
  landing_cert 1 (14 : ℝ) (by norm_num) pr x hp ε hdev aV bV dV TV ZV hab hd0 hdP haP hT hZ (hE ε hε) hcls EXs ENs hEXne hENne
    hEXdef hENdef hsepL HV hHL (cov x ε hε hdev) (0 : Fin 1) (by rw [dV_0, bV_0, aV_0]; norm_num)

noncomputable def sv : Fin 8 → ℝ := ![(1 : ℝ), (2 : ℝ), (6 : ℝ), (7 : ℝ), (8 : ℝ), (9 : ℝ), (10 : ℝ), (15 : ℝ)]
def sg : Fin 7 → Fin 8 := ![1, 2, 3, 4, 5, 6, 7]

theorem sv_0 : sv (0 : Fin 8) = (1 : ℝ) := rfl
theorem sv_1 : sv (1 : Fin 8) = (2 : ℝ) := rfl
theorem sv_2 : sv (2 : Fin 8) = (6 : ℝ) := rfl
theorem sv_3 : sv (3 : Fin 8) = (7 : ℝ) := rfl
theorem sv_4 : sv (4 : Fin 8) = (8 : ℝ) := rfl
theorem sv_5 : sv (5 : Fin 8) = (9 : ℝ) := rfl
theorem sv_6 : sv (6 : Fin 8) = (10 : ℝ) := rfl
theorem sv_7 : sv (7 : Fin 8) = (15 : ℝ) := rfl
theorem sg_0 : sg (0 : Fin 7) = (1 : Fin 8) := rfl
theorem sg_1 : sg (1 : Fin 7) = (2 : Fin 8) := rfl
theorem sg_2 : sg (2 : Fin 7) = (3 : Fin 8) := rfl
theorem sg_3 : sg (3 : Fin 7) = (4 : Fin 8) := rfl
theorem sg_4 : sg (4 : Fin 7) = (5 : Fin 8) := rfl
theorem sg_5 : sg (5 : Fin 7) = (6 : Fin 8) := rfl
theorem sg_6 : sg (6 : Fin 7) = (7 : Fin 8) := rfl

theorem inst_arr (v : Fin 8 → ℝ) (η : ℝ) (hη : η ≤ (1 / 25088 : ℝ)) (hv : ∀ j, |v j - sv j| ≤ η) :
    ∃ c₀ : Fin 1, Alive (mxOf (fun i => |v (sg i) - v (0 : Fin 8)|) EXs hEXne) (mnOf (fun i => |v (sg i) - v (0 : Fin 8)|) ENs hENne) c₀ ∧
      (∀ c, c < c₀ → ¬ Alive (mxOf (fun i => |v (sg i) - v (0 : Fin 8)|) EXs hEXne) (mnOf (fun i => |v (sg i) - v (0 : Fin 8)|) ENs hENne) c) ∧
      IsLeast {t : ℝ | 0 < t ∧ IsolatedAt v (0 : Fin 8) t} (mxOf (fun i => |v (sg i) - v (0 : Fin 8)|) EXs hEXne c₀) := by
  have hσk : ∀ i, sg i ≠ (0 : Fin 8) := by decide
  have hσ : ∀ j : Fin 8, j ≠ (0 : Fin 8) → ∃ i, sg i = j := by decide
  have hpr : ∀ i, pr i = |sv (sg i) - sv (0 : Fin 8)| := by
    intro i; rcases fin7_cases i with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6, sv_0, sv_1, sv_2, sv_3, sv_4, sv_5, sv_6, sv_7, sg_0, sg_1, sg_2, sg_3, sg_4, sg_5, sg_6]
  have hdev : ∀ i, |(|v (sg i) - v (0 : Fin 8)| - pr i)| ≤ 2 * η := by
    intro i; rw [hpr i]; exact reading_dev v sv η hv (sg i) (0 : Fin 8)
  obtain ⟨c₀, hal, hbf, hT0⟩ := inst (fun i => |v (sg i) - v (0 : Fin 8)|) (2 * η) (by linarith) hdev
  have hset : {t : ℝ | 0 < t ∧ IsolatedAt v (0 : Fin 8) t} =
      {t : ℝ | 0 < t ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (|v (sg i) - v (0 : Fin 8)| * t)} := by
    ext t; simp only [Set.mem_setOf_eq]; rw [iso_iff_readings v (0 : Fin 8) sg hσk hσ t]
  rw [hset]; exact ⟨c₀, hal, hbf, hT0⟩

#print axioms inst_arr

end Fresh.CertRR.R11176



/-!
# Landing certificate `CertRR.R11177`: speeds (1, 2, 6, 7, 8, 9, 10, 15), subject index 1

Generated 2026-10-24 by `experiments/n8/cert_gen_v1.py` (exact Fractions).  Baseline readings [1, 4, 5, 6, 7, 8, 13].  Components up to the first wide one: 1.
Radius: speeds within `η ≤ 1/12288` of the baseline speeds, giving `ε = 2η ≤ 1/6144`.  Covering margin `μ = 1/512`.
`hcov` is **[PROVISIONAL: covering]**, supporting the claim that the first lonely instant of this subject is the largest exit of the first alive component.
Result `inst_arr`: for such `v`, the subject has a first isolation (a least element over all `t > 0`).  Grades: [L].
-/

open Classical

namespace Fresh.CertRR.R11177

open Fresh Fresh.LandingCert Fresh.LandingRule

noncomputable def pr : Fin 7 → ℝ := ![(1 : ℝ), (4 : ℝ), (5 : ℝ), (6 : ℝ), (7 : ℝ), (8 : ℝ), (13 : ℝ)]
noncomputable def aV : Fin 1 → ℝ := ![(17 / 48 : ℝ)]
noncomputable def bV : Fin 1 → ℝ := ![(23 / 64 : ℝ)]
noncomputable def dV : Fin 1 → ℝ := ![(1 / 96 : ℝ)]
noncomputable def TV : Fin 1 → ℝ := ![(71 / 192 : ℝ)]
def ZV : Fin 1 → ℤ := ![7]
noncomputable def HV : ℝ := (35 / 96 : ℝ)
noncomputable def EXs (c : Fin 1) : Finset (Fin 7 × ℤ) :=
  (Finset.univ ×ˢ Finset.Icc 0 (ZV c)).filter (fun q => ((q.2 : ℝ) + 1 / 8) / pr q.1 = aV c)
noncomputable def ENs (c : Fin 1) : Finset (Fin 7 × ℤ) :=
  (Finset.univ ×ˢ Finset.Icc 0 (ZV c)).filter (fun q => ((q.2 : ℝ) - 1 / 8) / pr q.1 = bV c)

theorem hp : ∀ i, 1 ≤ pr i ∧ pr i ≤ (13 : ℝ) := by intro i; fin_cases i <;> norm_num [pr]
theorem hp1 : ∀ i, 1 ≤ pr i := fun i => (hp i).1
theorem pr_0 : pr (0 : Fin 7) = (1 : ℝ) := rfl
theorem pr_1 : pr (1 : Fin 7) = (4 : ℝ) := rfl
theorem pr_2 : pr (2 : Fin 7) = (5 : ℝ) := rfl
theorem pr_3 : pr (3 : Fin 7) = (6 : ℝ) := rfl
theorem pr_4 : pr (4 : Fin 7) = (7 : ℝ) := rfl
theorem pr_5 : pr (5 : Fin 7) = (8 : ℝ) := rfl
theorem pr_6 : pr (6 : Fin 7) = (13 : ℝ) := rfl
theorem aV_0 : aV (0 : Fin 1) = (17 / 48 : ℝ) := rfl
theorem bV_0 : bV (0 : Fin 1) = (23 / 64 : ℝ) := rfl
theorem dV_0 : dV (0 : Fin 1) = (1 / 96 : ℝ) := rfl
theorem TV_0 : TV (0 : Fin 1) = (71 / 192 : ℝ) := rfl
theorem ZV_0 : ZV (0 : Fin 1) = (7 : ℤ) := rfl
theorem hab : ∀ c, aV c ≤ bV c := by intro c; fin_cases c <;> norm_num [aV, bV]
theorem hd0 : ∀ c, 0 < dV c := by intro c; fin_cases c <;> norm_num [dV]
theorem hdP : ∀ c, dV c ≤ 1 / (4 * (13 : ℝ)) := by intro c; fin_cases c <;> norm_num [dV]
theorem haP : ∀ c, dV c < aV c := by intro c; fin_cases c <;> norm_num [dV, aV]
theorem hT : ∀ c, bV c + dV c ≤ TV c := by intro c; fin_cases c <;> norm_num [bV, dV, TV]
theorem hZ : ∀ c, ((13 : ℝ) + 1) * TV c + 1 ≤ (ZV c : ℝ) := by intro c; fin_cases c <;> norm_num [TV, ZV]
theorem hE (ε : ℝ) (hε : ε ≤ (1 / 6144 : ℝ)) : ∀ c, 8 * ((ZV c : ℝ) + 1) * ε ≤ dV c := by
  intro c; fin_cases c <;> norm_num [ZV, dV] <;> linarith
theorem hcls : ∀ c i, ∀ z : ℤ, 0 ≤ z → z ≤ ZV c →
    ((z : ℝ) + 1 / 8) / pr i ≤ aV c - dV c ∨ bV c + dV c ≤ ((z : ℝ) - 1 / 8) / pr i ∨
      ((z : ℝ) + 1 / 8) / pr i = aV c ∨ ((z : ℝ) - 1 / 8) / pr i = bV c := by
  intro c i z h0 h1
  fin_cases c <;> fin_cases i <;> simp [ZV] at h1 <;> interval_cases z <;> norm_num [pr, aV, bV, dV]
theorem hEXne : ∀ c, (EXs c).Nonempty := by
  intro c
  fin_cases c
  · exact ⟨(3, 2), by simp [EXs, ZV, pr, aV] <;> norm_num⟩
theorem hENne : ∀ c, (ENs c).Nonempty := by
  intro c
  fin_cases c
  · exact ⟨(5, 3), by simp [ENs, ZV, pr, bV] <;> norm_num⟩
theorem hEXdef : ∀ c, ∀ q : Fin 7 × ℤ, q ∈ EXs c ↔ 0 ≤ q.2 ∧ q.2 ≤ ZV c ∧ ((q.2 : ℝ) + 1 / 8) / pr q.1 = aV c := by
  intro c q
  simp only [EXs, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, Finset.mem_Icc, true_and]
  tauto
theorem hENdef : ∀ c, ∀ q : Fin 7 × ℤ, q ∈ ENs c ↔ 0 ≤ q.2 ∧ q.2 ≤ ZV c ∧ ((q.2 : ℝ) - 1 / 8) / pr q.1 = bV c := by
  intro c q
  simp only [ENs, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, Finset.mem_Icc, true_and]
  tauto
theorem hsepL : ∀ c c' : Fin 1, c < c' → bV c + dV c / 2 < aV c' - dV c' / 2 := by
  intro c c' h
  fin_cases c <;> fin_cases c' <;> simp at h ⊢ <;> norm_num [aV, bV, dV]
theorem hHL : ∀ c, bV c + dV c / 2 ≤ HV := by intro c; fin_cases c <;> norm_num [bV, dV, HV]

theorem gap0 (x : Fin 7 → ℝ) (ε : ℝ) (hdev : ∀ i, |x i - pr i| ≤ ε) (hεH : ε * HV ≤ (1 / 512 : ℝ) / 2) (t : ℝ) (h0 : 0 ≤ t)
    (hHt : t ≤ HV) (h1 : (0 : ℝ) ≤ t) (h2 : t ≤ (67 / 192 : ℝ)) (hlon : ∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)) : False := by
  rcases le_total t (63 / 512 : ℝ) with hs0 | hs0
  · exact zone_kill_gen pr x ε HV (1 / 512 : ℝ) hp1 hdev hεH (by norm_num) (0 : Fin 7) 0 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (0 : Fin 7))
  rcases le_total t (71 / 512 : ℝ) with hs1 | hs1
  · exact zone_kill_gen pr x ε HV (1 / 512 : ℝ) hp1 hdev hεH (by norm_num) (5 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (5 : Fin 7))
  rcases le_total t (569 / 3584 : ℝ) with hs2 | hs2
  · exact zone_kill_gen pr x ε HV (1 / 512 : ℝ) hp1 hdev hεH (by norm_num) (4 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (4 : Fin 7))
  rcases le_total t (95 / 512 : ℝ) with hs3 | hs3
  · exact zone_kill_gen pr x ε HV (1 / 512 : ℝ) hp1 hdev hεH (by norm_num) (3 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (3 : Fin 7))
  rcases le_total t (571 / 2560 : ℝ) with hs4 | hs4
  · exact zone_kill_gen pr x ε HV (1 / 512 : ℝ) hp1 hdev hεH (by norm_num) (2 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (2 : Fin 7))
  rcases le_total t (143 / 512 : ℝ) with hs5 | hs5
  · exact zone_kill_gen pr x ε HV (1 / 512 : ℝ) hp1 hdev hεH (by norm_num) (1 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (1 : Fin 7))
  rcases le_total t (1081 / 3584 : ℝ) with hs6 | hs6
  · exact zone_kill_gen pr x ε HV (1 / 512 : ℝ) hp1 hdev hεH (by norm_num) (4 : Fin 7) 2 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (4 : Fin 7))
  rcases le_total t (2099 / 6656 : ℝ) with hs7 | hs7
  · exact zone_kill_gen pr x ε HV (1 / 512 : ℝ) hp1 hdev hεH (by norm_num) (6 : Fin 7) 4 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (6 : Fin 7))
  exact zone_kill_gen pr x ε HV (1 / 512 : ℝ) hp1 hdev hεH (by norm_num) (3 : Fin 7) 2 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (3 : Fin 7))
theorem cov (x : Fin 7 → ℝ) (ε : ℝ) (hε : ε ≤ (1 / 6144 : ℝ)) (hdev : ∀ i, |x i - pr i| ≤ ε) :
    ∀ t : ℝ, 0 < t → t ≤ HV → (∀ c, ¬ (aV c - dV c / 2 ≤ t ∧ t ≤ bV c + dV c / 2)) →
      ¬ (∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)) := by
  intro t h0 hHt hnone hlon
  have hεH : ε * HV ≤ (1 / 512 : ℝ) / 2 := by
    have hε0 : 0 ≤ ε := le_trans (abs_nonneg _) (hdev 0)
    have : ε * HV ≤ (1 / 6144 : ℝ) * HV := mul_le_mul_of_nonneg_right hε (by norm_num [HV])
    have h2 : (1 / 6144 : ℝ) * HV ≤ (1 / 512 : ℝ) / 2 := by norm_num [HV]
    linarith
  have n0 := hnone (0 : Fin 1)
  rw [aV_0, bV_0, dV_0] at n0
  rcases lt_or_ge t (67 / 192 : ℝ) with c0 | c0
  · exact gap0 x ε hdev hεH t h0.le hHt h0.le (by linarith) hlon
  have d0 : (35 / 96 : ℝ) < t := by
    by_contra hc; push Not at hc; exact n0 ⟨by linarith, by linarith⟩
  have hHv : HV = (35 / 96 : ℝ) := rfl
  exact absurd (by linarith : t ≤ (35 / 96 : ℝ)) (not_le.2 d0)

theorem inst (x : Fin 7 → ℝ) (ε : ℝ) (hε : ε ≤ (1 / 6144 : ℝ)) (hdev : ∀ i, |x i - pr i| ≤ ε) :
    ∃ c₀ : Fin 1, Alive (mxOf x EXs hEXne) (mnOf x ENs hENne) c₀ ∧
      (∀ c, c < c₀ → ¬ Alive (mxOf x EXs hEXne) (mnOf x ENs hENne) c) ∧
      IsLeast {t : ℝ | 0 < t ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)} (mxOf x EXs hEXne c₀) :=
  landing_cert 1 (13 : ℝ) (by norm_num) pr x hp ε hdev aV bV dV TV ZV hab hd0 hdP haP hT hZ (hE ε hε) hcls EXs ENs hEXne hENne
    hEXdef hENdef hsepL HV hHL (cov x ε hε hdev) (0 : Fin 1) (by rw [dV_0, bV_0, aV_0]; norm_num)

noncomputable def sv : Fin 8 → ℝ := ![(1 : ℝ), (2 : ℝ), (6 : ℝ), (7 : ℝ), (8 : ℝ), (9 : ℝ), (10 : ℝ), (15 : ℝ)]
def sg : Fin 7 → Fin 8 := ![0, 2, 3, 4, 5, 6, 7]

theorem sv_0 : sv (0 : Fin 8) = (1 : ℝ) := rfl
theorem sv_1 : sv (1 : Fin 8) = (2 : ℝ) := rfl
theorem sv_2 : sv (2 : Fin 8) = (6 : ℝ) := rfl
theorem sv_3 : sv (3 : Fin 8) = (7 : ℝ) := rfl
theorem sv_4 : sv (4 : Fin 8) = (8 : ℝ) := rfl
theorem sv_5 : sv (5 : Fin 8) = (9 : ℝ) := rfl
theorem sv_6 : sv (6 : Fin 8) = (10 : ℝ) := rfl
theorem sv_7 : sv (7 : Fin 8) = (15 : ℝ) := rfl
theorem sg_0 : sg (0 : Fin 7) = (0 : Fin 8) := rfl
theorem sg_1 : sg (1 : Fin 7) = (2 : Fin 8) := rfl
theorem sg_2 : sg (2 : Fin 7) = (3 : Fin 8) := rfl
theorem sg_3 : sg (3 : Fin 7) = (4 : Fin 8) := rfl
theorem sg_4 : sg (4 : Fin 7) = (5 : Fin 8) := rfl
theorem sg_5 : sg (5 : Fin 7) = (6 : Fin 8) := rfl
theorem sg_6 : sg (6 : Fin 7) = (7 : Fin 8) := rfl

theorem inst_arr (v : Fin 8 → ℝ) (η : ℝ) (hη : η ≤ (1 / 12288 : ℝ)) (hv : ∀ j, |v j - sv j| ≤ η) :
    ∃ c₀ : Fin 1, Alive (mxOf (fun i => |v (sg i) - v (1 : Fin 8)|) EXs hEXne) (mnOf (fun i => |v (sg i) - v (1 : Fin 8)|) ENs hENne) c₀ ∧
      (∀ c, c < c₀ → ¬ Alive (mxOf (fun i => |v (sg i) - v (1 : Fin 8)|) EXs hEXne) (mnOf (fun i => |v (sg i) - v (1 : Fin 8)|) ENs hENne) c) ∧
      IsLeast {t : ℝ | 0 < t ∧ IsolatedAt v (1 : Fin 8) t} (mxOf (fun i => |v (sg i) - v (1 : Fin 8)|) EXs hEXne c₀) := by
  have hσk : ∀ i, sg i ≠ (1 : Fin 8) := by decide
  have hσ : ∀ j : Fin 8, j ≠ (1 : Fin 8) → ∃ i, sg i = j := by decide
  have hpr : ∀ i, pr i = |sv (sg i) - sv (1 : Fin 8)| := by
    intro i; rcases fin7_cases i with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6, sv_0, sv_1, sv_2, sv_3, sv_4, sv_5, sv_6, sv_7, sg_0, sg_1, sg_2, sg_3, sg_4, sg_5, sg_6]
  have hdev : ∀ i, |(|v (sg i) - v (1 : Fin 8)| - pr i)| ≤ 2 * η := by
    intro i; rw [hpr i]; exact reading_dev v sv η hv (sg i) (1 : Fin 8)
  obtain ⟨c₀, hal, hbf, hT0⟩ := inst (fun i => |v (sg i) - v (1 : Fin 8)|) (2 * η) (by linarith) hdev
  have hset : {t : ℝ | 0 < t ∧ IsolatedAt v (1 : Fin 8) t} =
      {t : ℝ | 0 < t ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (|v (sg i) - v (1 : Fin 8)| * t)} := by
    ext t; simp only [Set.mem_setOf_eq]; rw [iso_iff_readings v (1 : Fin 8) sg hσk hσ t]
  rw [hset]; exact ⟨c₀, hal, hbf, hT0⟩

#print axioms inst_arr

end Fresh.CertRR.R11177



/-!
# Landing certificate `CertRR.R11183`: speeds (1, 2, 6, 7, 8, 9, 10, 15), subject index 7

Generated 2026-10-24 by `experiments/n8/cert_gen_v1.py` (exact Fractions).  Baseline readings [14, 13, 9, 8, 7, 6, 5].  Components up to the first wide one: 1.
Radius: speeds within `η ≤ 1/15360` of the baseline speeds, giving `ε = 2η ≤ 1/7680`.  Covering margin `μ = 1/512`.
`hcov` is **[PROVISIONAL: covering]**, supporting the claim that the first lonely instant of this subject is the largest exit of the first alive component.
Result `inst_arr`: for such `v`, the subject has a first isolation (a least element over all `t > 0`).  Grades: [L].
-/

open Classical

namespace Fresh.CertRR.R11183

open Fresh Fresh.LandingCert Fresh.LandingRule

noncomputable def pr : Fin 7 → ℝ := ![(14 : ℝ), (13 : ℝ), (9 : ℝ), (8 : ℝ), (7 : ℝ), (6 : ℝ), (5 : ℝ)]
noncomputable def aV : Fin 1 → ℝ := ![(1 / 40 : ℝ)]
noncomputable def bV : Fin 1 → ℝ := ![(1 / 16 : ℝ)]
noncomputable def dV : Fin 1 → ℝ := ![(1 / 240 : ℝ)]
noncomputable def TV : Fin 1 → ℝ := ![(1 / 15 : ℝ)]
def ZV : Fin 1 → ℤ := ![3]
noncomputable def HV : ℝ := (31 / 480 : ℝ)
noncomputable def EXs (c : Fin 1) : Finset (Fin 7 × ℤ) :=
  (Finset.univ ×ˢ Finset.Icc 0 (ZV c)).filter (fun q => ((q.2 : ℝ) + 1 / 8) / pr q.1 = aV c)
noncomputable def ENs (c : Fin 1) : Finset (Fin 7 × ℤ) :=
  (Finset.univ ×ˢ Finset.Icc 0 (ZV c)).filter (fun q => ((q.2 : ℝ) - 1 / 8) / pr q.1 = bV c)

theorem hp : ∀ i, 1 ≤ pr i ∧ pr i ≤ (14 : ℝ) := by intro i; fin_cases i <;> norm_num [pr]
theorem hp1 : ∀ i, 1 ≤ pr i := fun i => (hp i).1
theorem pr_0 : pr (0 : Fin 7) = (14 : ℝ) := rfl
theorem pr_1 : pr (1 : Fin 7) = (13 : ℝ) := rfl
theorem pr_2 : pr (2 : Fin 7) = (9 : ℝ) := rfl
theorem pr_3 : pr (3 : Fin 7) = (8 : ℝ) := rfl
theorem pr_4 : pr (4 : Fin 7) = (7 : ℝ) := rfl
theorem pr_5 : pr (5 : Fin 7) = (6 : ℝ) := rfl
theorem pr_6 : pr (6 : Fin 7) = (5 : ℝ) := rfl
theorem aV_0 : aV (0 : Fin 1) = (1 / 40 : ℝ) := rfl
theorem bV_0 : bV (0 : Fin 1) = (1 / 16 : ℝ) := rfl
theorem dV_0 : dV (0 : Fin 1) = (1 / 240 : ℝ) := rfl
theorem TV_0 : TV (0 : Fin 1) = (1 / 15 : ℝ) := rfl
theorem ZV_0 : ZV (0 : Fin 1) = (3 : ℤ) := rfl
theorem hab : ∀ c, aV c ≤ bV c := by intro c; fin_cases c <;> norm_num [aV, bV]
theorem hd0 : ∀ c, 0 < dV c := by intro c; fin_cases c <;> norm_num [dV]
theorem hdP : ∀ c, dV c ≤ 1 / (4 * (14 : ℝ)) := by intro c; fin_cases c <;> norm_num [dV]
theorem haP : ∀ c, dV c < aV c := by intro c; fin_cases c <;> norm_num [dV, aV]
theorem hT : ∀ c, bV c + dV c ≤ TV c := by intro c; fin_cases c <;> norm_num [bV, dV, TV]
theorem hZ : ∀ c, ((14 : ℝ) + 1) * TV c + 1 ≤ (ZV c : ℝ) := by intro c; fin_cases c <;> norm_num [TV, ZV]
theorem hE (ε : ℝ) (hε : ε ≤ (1 / 7680 : ℝ)) : ∀ c, 8 * ((ZV c : ℝ) + 1) * ε ≤ dV c := by
  intro c; fin_cases c <;> norm_num [ZV, dV] <;> linarith
theorem hcls : ∀ c i, ∀ z : ℤ, 0 ≤ z → z ≤ ZV c →
    ((z : ℝ) + 1 / 8) / pr i ≤ aV c - dV c ∨ bV c + dV c ≤ ((z : ℝ) - 1 / 8) / pr i ∨
      ((z : ℝ) + 1 / 8) / pr i = aV c ∨ ((z : ℝ) - 1 / 8) / pr i = bV c := by
  intro c i z h0 h1
  fin_cases c <;> fin_cases i <;> simp [ZV] at h1 <;> interval_cases z <;> norm_num [pr, aV, bV, dV]
theorem hEXne : ∀ c, (EXs c).Nonempty := by
  intro c
  fin_cases c
  · exact ⟨(6, 0), by simp [EXs, ZV, pr, aV] <;> norm_num⟩
theorem hENne : ∀ c, (ENs c).Nonempty := by
  intro c
  fin_cases c
  · exact ⟨(0, 1), by simp [ENs, ZV, pr, bV] <;> norm_num⟩
theorem hEXdef : ∀ c, ∀ q : Fin 7 × ℤ, q ∈ EXs c ↔ 0 ≤ q.2 ∧ q.2 ≤ ZV c ∧ ((q.2 : ℝ) + 1 / 8) / pr q.1 = aV c := by
  intro c q
  simp only [EXs, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, Finset.mem_Icc, true_and]
  tauto
theorem hENdef : ∀ c, ∀ q : Fin 7 × ℤ, q ∈ ENs c ↔ 0 ≤ q.2 ∧ q.2 ≤ ZV c ∧ ((q.2 : ℝ) - 1 / 8) / pr q.1 = bV c := by
  intro c q
  simp only [ENs, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, Finset.mem_Icc, true_and]
  tauto
theorem hsepL : ∀ c c' : Fin 1, c < c' → bV c + dV c / 2 < aV c' - dV c' / 2 := by
  intro c c' h
  fin_cases c <;> fin_cases c' <;> simp at h ⊢ <;> norm_num [aV, bV, dV]
theorem hHL : ∀ c, bV c + dV c / 2 ≤ HV := by intro c; fin_cases c <;> norm_num [bV, dV, HV]

theorem gap0 (x : Fin 7 → ℝ) (ε : ℝ) (hdev : ∀ i, |x i - pr i| ≤ ε) (hεH : ε * HV ≤ (1 / 512 : ℝ) / 2) (t : ℝ) (h0 : 0 ≤ t)
    (hHt : t ≤ HV) (h1 : (0 : ℝ) ≤ t) (h2 : t ≤ (11 / 480 : ℝ)) (hlon : ∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)) : False := by
  exact zone_kill_gen pr x ε HV (1 / 512 : ℝ) hp1 hdev hεH (by norm_num) (6 : Fin 7) 0 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (6 : Fin 7))
theorem cov (x : Fin 7 → ℝ) (ε : ℝ) (hε : ε ≤ (1 / 7680 : ℝ)) (hdev : ∀ i, |x i - pr i| ≤ ε) :
    ∀ t : ℝ, 0 < t → t ≤ HV → (∀ c, ¬ (aV c - dV c / 2 ≤ t ∧ t ≤ bV c + dV c / 2)) →
      ¬ (∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)) := by
  intro t h0 hHt hnone hlon
  have hεH : ε * HV ≤ (1 / 512 : ℝ) / 2 := by
    have hε0 : 0 ≤ ε := le_trans (abs_nonneg _) (hdev 0)
    have : ε * HV ≤ (1 / 7680 : ℝ) * HV := mul_le_mul_of_nonneg_right hε (by norm_num [HV])
    have h2 : (1 / 7680 : ℝ) * HV ≤ (1 / 512 : ℝ) / 2 := by norm_num [HV]
    linarith
  have n0 := hnone (0 : Fin 1)
  rw [aV_0, bV_0, dV_0] at n0
  rcases lt_or_ge t (11 / 480 : ℝ) with c0 | c0
  · exact gap0 x ε hdev hεH t h0.le hHt h0.le (by linarith) hlon
  have d0 : (31 / 480 : ℝ) < t := by
    by_contra hc; push Not at hc; exact n0 ⟨by linarith, by linarith⟩
  have hHv : HV = (31 / 480 : ℝ) := rfl
  exact absurd (by linarith : t ≤ (31 / 480 : ℝ)) (not_le.2 d0)

theorem inst (x : Fin 7 → ℝ) (ε : ℝ) (hε : ε ≤ (1 / 7680 : ℝ)) (hdev : ∀ i, |x i - pr i| ≤ ε) :
    ∃ c₀ : Fin 1, Alive (mxOf x EXs hEXne) (mnOf x ENs hENne) c₀ ∧
      (∀ c, c < c₀ → ¬ Alive (mxOf x EXs hEXne) (mnOf x ENs hENne) c) ∧
      IsLeast {t : ℝ | 0 < t ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)} (mxOf x EXs hEXne c₀) :=
  landing_cert 1 (14 : ℝ) (by norm_num) pr x hp ε hdev aV bV dV TV ZV hab hd0 hdP haP hT hZ (hE ε hε) hcls EXs ENs hEXne hENne
    hEXdef hENdef hsepL HV hHL (cov x ε hε hdev) (0 : Fin 1) (by rw [dV_0, bV_0, aV_0]; norm_num)

noncomputable def sv : Fin 8 → ℝ := ![(1 : ℝ), (2 : ℝ), (6 : ℝ), (7 : ℝ), (8 : ℝ), (9 : ℝ), (10 : ℝ), (15 : ℝ)]
def sg : Fin 7 → Fin 8 := ![0, 1, 2, 3, 4, 5, 6]

theorem sv_0 : sv (0 : Fin 8) = (1 : ℝ) := rfl
theorem sv_1 : sv (1 : Fin 8) = (2 : ℝ) := rfl
theorem sv_2 : sv (2 : Fin 8) = (6 : ℝ) := rfl
theorem sv_3 : sv (3 : Fin 8) = (7 : ℝ) := rfl
theorem sv_4 : sv (4 : Fin 8) = (8 : ℝ) := rfl
theorem sv_5 : sv (5 : Fin 8) = (9 : ℝ) := rfl
theorem sv_6 : sv (6 : Fin 8) = (10 : ℝ) := rfl
theorem sv_7 : sv (7 : Fin 8) = (15 : ℝ) := rfl
theorem sg_0 : sg (0 : Fin 7) = (0 : Fin 8) := rfl
theorem sg_1 : sg (1 : Fin 7) = (1 : Fin 8) := rfl
theorem sg_2 : sg (2 : Fin 7) = (2 : Fin 8) := rfl
theorem sg_3 : sg (3 : Fin 7) = (3 : Fin 8) := rfl
theorem sg_4 : sg (4 : Fin 7) = (4 : Fin 8) := rfl
theorem sg_5 : sg (5 : Fin 7) = (5 : Fin 8) := rfl
theorem sg_6 : sg (6 : Fin 7) = (6 : Fin 8) := rfl

theorem inst_arr (v : Fin 8 → ℝ) (η : ℝ) (hη : η ≤ (1 / 15360 : ℝ)) (hv : ∀ j, |v j - sv j| ≤ η) :
    ∃ c₀ : Fin 1, Alive (mxOf (fun i => |v (sg i) - v (7 : Fin 8)|) EXs hEXne) (mnOf (fun i => |v (sg i) - v (7 : Fin 8)|) ENs hENne) c₀ ∧
      (∀ c, c < c₀ → ¬ Alive (mxOf (fun i => |v (sg i) - v (7 : Fin 8)|) EXs hEXne) (mnOf (fun i => |v (sg i) - v (7 : Fin 8)|) ENs hENne) c) ∧
      IsLeast {t : ℝ | 0 < t ∧ IsolatedAt v (7 : Fin 8) t} (mxOf (fun i => |v (sg i) - v (7 : Fin 8)|) EXs hEXne c₀) := by
  have hσk : ∀ i, sg i ≠ (7 : Fin 8) := by decide
  have hσ : ∀ j : Fin 8, j ≠ (7 : Fin 8) → ∃ i, sg i = j := by decide
  have hpr : ∀ i, pr i = |sv (sg i) - sv (7 : Fin 8)| := by
    intro i; rcases fin7_cases i with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6, sv_0, sv_1, sv_2, sv_3, sv_4, sv_5, sv_6, sv_7, sg_0, sg_1, sg_2, sg_3, sg_4, sg_5, sg_6]
  have hdev : ∀ i, |(|v (sg i) - v (7 : Fin 8)| - pr i)| ≤ 2 * η := by
    intro i; rw [hpr i]; exact reading_dev v sv η hv (sg i) (7 : Fin 8)
  obtain ⟨c₀, hal, hbf, hT0⟩ := inst (fun i => |v (sg i) - v (7 : Fin 8)|) (2 * η) (by linarith) hdev
  have hset : {t : ℝ | 0 < t ∧ IsolatedAt v (7 : Fin 8) t} =
      {t : ℝ | 0 < t ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (|v (sg i) - v (7 : Fin 8)| * t)} := by
    ext t; simp only [Set.mem_setOf_eq]; rw [iso_iff_readings v (7 : Fin 8) sg hσk hσ t]
  rw [hset]; exact ⟨c₀, hal, hbf, hT0⟩

#print axioms inst_arr

end Fresh.CertRR.R11183



/-!
# Landing certificate `CertRR.R11184`: speeds (1, 2, 6, 7, 8, 9, 10, 16), subject index 0

Generated 2026-10-24 by `experiments/n8/cert_gen_v1.py` (exact Fractions).  Baseline readings [1, 5, 6, 7, 8, 9, 15].  Components up to the first wide one: 1.
Radius: speeds within `η ≤ 1/18432` of the baseline speeds, giving `ε = 2η ≤ 1/9216`.  Covering margin `μ = 1/2048`.
`hcov` is **[PROVISIONAL: covering]**, supporting the claim that the first lonely instant of this subject is the largest exit of the first alive component.
Result `inst_arr`: for such `v`, the subject has a first isolation (a least element over all `t > 0`).  Grades: [L].
-/

open Classical

namespace Fresh.CertRR.R11184

open Fresh Fresh.LandingCert Fresh.LandingRule

noncomputable def pr : Fin 7 → ℝ := ![(1 : ℝ), (5 : ℝ), (6 : ℝ), (7 : ℝ), (8 : ℝ), (9 : ℝ), (15 : ℝ)]
noncomputable def aV : Fin 1 → ℝ := ![(17 / 56 : ℝ)]
noncomputable def bV : Fin 1 → ℝ := ![(5 / 16 : ℝ)]
noncomputable def dV : Fin 1 → ℝ := ![(1 / 144 : ℝ)]
noncomputable def TV : Fin 1 → ℝ := ![(23 / 72 : ℝ)]
def ZV : Fin 1 → ℤ := ![7]
noncomputable def HV : ℝ := (91 / 288 : ℝ)
noncomputable def EXs (c : Fin 1) : Finset (Fin 7 × ℤ) :=
  (Finset.univ ×ˢ Finset.Icc 0 (ZV c)).filter (fun q => ((q.2 : ℝ) + 1 / 8) / pr q.1 = aV c)
noncomputable def ENs (c : Fin 1) : Finset (Fin 7 × ℤ) :=
  (Finset.univ ×ˢ Finset.Icc 0 (ZV c)).filter (fun q => ((q.2 : ℝ) - 1 / 8) / pr q.1 = bV c)

theorem hp : ∀ i, 1 ≤ pr i ∧ pr i ≤ (15 : ℝ) := by intro i; fin_cases i <;> norm_num [pr]
theorem hp1 : ∀ i, 1 ≤ pr i := fun i => (hp i).1
theorem pr_0 : pr (0 : Fin 7) = (1 : ℝ) := rfl
theorem pr_1 : pr (1 : Fin 7) = (5 : ℝ) := rfl
theorem pr_2 : pr (2 : Fin 7) = (6 : ℝ) := rfl
theorem pr_3 : pr (3 : Fin 7) = (7 : ℝ) := rfl
theorem pr_4 : pr (4 : Fin 7) = (8 : ℝ) := rfl
theorem pr_5 : pr (5 : Fin 7) = (9 : ℝ) := rfl
theorem pr_6 : pr (6 : Fin 7) = (15 : ℝ) := rfl
theorem aV_0 : aV (0 : Fin 1) = (17 / 56 : ℝ) := rfl
theorem bV_0 : bV (0 : Fin 1) = (5 / 16 : ℝ) := rfl
theorem dV_0 : dV (0 : Fin 1) = (1 / 144 : ℝ) := rfl
theorem TV_0 : TV (0 : Fin 1) = (23 / 72 : ℝ) := rfl
theorem ZV_0 : ZV (0 : Fin 1) = (7 : ℤ) := rfl
theorem hab : ∀ c, aV c ≤ bV c := by intro c; fin_cases c <;> norm_num [aV, bV]
theorem hd0 : ∀ c, 0 < dV c := by intro c; fin_cases c <;> norm_num [dV]
theorem hdP : ∀ c, dV c ≤ 1 / (4 * (15 : ℝ)) := by intro c; fin_cases c <;> norm_num [dV]
theorem haP : ∀ c, dV c < aV c := by intro c; fin_cases c <;> norm_num [dV, aV]
theorem hT : ∀ c, bV c + dV c ≤ TV c := by intro c; fin_cases c <;> norm_num [bV, dV, TV]
theorem hZ : ∀ c, ((15 : ℝ) + 1) * TV c + 1 ≤ (ZV c : ℝ) := by intro c; fin_cases c <;> norm_num [TV, ZV]
theorem hE (ε : ℝ) (hε : ε ≤ (1 / 9216 : ℝ)) : ∀ c, 8 * ((ZV c : ℝ) + 1) * ε ≤ dV c := by
  intro c; fin_cases c <;> norm_num [ZV, dV] <;> linarith
theorem hcls : ∀ c i, ∀ z : ℤ, 0 ≤ z → z ≤ ZV c →
    ((z : ℝ) + 1 / 8) / pr i ≤ aV c - dV c ∨ bV c + dV c ≤ ((z : ℝ) - 1 / 8) / pr i ∨
      ((z : ℝ) + 1 / 8) / pr i = aV c ∨ ((z : ℝ) - 1 / 8) / pr i = bV c := by
  intro c i z h0 h1
  fin_cases c <;> fin_cases i <;> simp [ZV] at h1 <;> interval_cases z <;> norm_num [pr, aV, bV, dV]
theorem hEXne : ∀ c, (EXs c).Nonempty := by
  intro c
  fin_cases c
  · exact ⟨(3, 2), by simp [EXs, ZV, pr, aV] <;> norm_num⟩
theorem hENne : ∀ c, (ENs c).Nonempty := by
  intro c
  fin_cases c
  · exact ⟨(2, 2), by simp [ENs, ZV, pr, bV] <;> norm_num⟩
theorem hEXdef : ∀ c, ∀ q : Fin 7 × ℤ, q ∈ EXs c ↔ 0 ≤ q.2 ∧ q.2 ≤ ZV c ∧ ((q.2 : ℝ) + 1 / 8) / pr q.1 = aV c := by
  intro c q
  simp only [EXs, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, Finset.mem_Icc, true_and]
  tauto
theorem hENdef : ∀ c, ∀ q : Fin 7 × ℤ, q ∈ ENs c ↔ 0 ≤ q.2 ∧ q.2 ≤ ZV c ∧ ((q.2 : ℝ) - 1 / 8) / pr q.1 = bV c := by
  intro c q
  simp only [ENs, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, Finset.mem_Icc, true_and]
  tauto
theorem hsepL : ∀ c c' : Fin 1, c < c' → bV c + dV c / 2 < aV c' - dV c' / 2 := by
  intro c c' h
  fin_cases c <;> fin_cases c' <;> simp at h ⊢ <;> norm_num [aV, bV, dV]
theorem hHL : ∀ c, bV c + dV c / 2 ≤ HV := by intro c; fin_cases c <;> norm_num [bV, dV, HV]

theorem gap0 (x : Fin 7 → ℝ) (ε : ℝ) (hdev : ∀ i, |x i - pr i| ≤ ε) (hεH : ε * HV ≤ (1 / 2048 : ℝ) / 2) (t : ℝ) (h0 : 0 ≤ t)
    (hHt : t ≤ HV) (h1 : (0 : ℝ) ≤ t) (h2 : t ≤ (605 / 2016 : ℝ)) (hlon : ∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)) : False := by
  rcases le_total t (255 / 2048 : ℝ) with hs0 | hs0
  · exact zone_kill_gen pr x ε HV (1 / 2048 : ℝ) hp1 hdev hεH (by norm_num) (0 : Fin 7) 0 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (0 : Fin 7))
  rcases le_total t (287 / 2048 : ℝ) with hs1 | hs1
  · exact zone_kill_gen pr x ε HV (1 / 2048 : ℝ) hp1 hdev hεH (by norm_num) (4 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (4 : Fin 7))
  rcases le_total t (2297 / 14336 : ℝ) with hs2 | hs2
  · exact zone_kill_gen pr x ε HV (1 / 2048 : ℝ) hp1 hdev hεH (by norm_num) (3 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (3 : Fin 7))
  rcases le_total t (383 / 2048 : ℝ) with hs3 | hs3
  · exact zone_kill_gen pr x ε HV (1 / 2048 : ℝ) hp1 hdev hεH (by norm_num) (2 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (2 : Fin 7))
  rcases le_total t (2299 / 10240 : ℝ) with hs4 | hs4
  · exact zone_kill_gen pr x ε HV (1 / 2048 : ℝ) hp1 hdev hεH (by norm_num) (1 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (1 : Fin 7))
  rcases le_total t (4343 / 18432 : ℝ) with hs5 | hs5
  · exact zone_kill_gen pr x ε HV (1 / 2048 : ℝ) hp1 hdev hεH (by norm_num) (5 : Fin 7) 2 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (5 : Fin 7))
  rcases le_total t (543 / 2048 : ℝ) with hs6 | hs6
  · exact zone_kill_gen pr x ε HV (1 / 2048 : ℝ) hp1 hdev hεH (by norm_num) (4 : Fin 7) 2 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (4 : Fin 7))
  rcases le_total t (2811 / 10240 : ℝ) with hs7 | hs7
  · exact zone_kill_gen pr x ε HV (1 / 2048 : ℝ) hp1 hdev hεH (by norm_num) (6 : Fin 7) 4 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (6 : Fin 7))
  exact zone_kill_gen pr x ε HV (1 / 2048 : ℝ) hp1 hdev hεH (by norm_num) (3 : Fin 7) 2 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (3 : Fin 7))
theorem cov (x : Fin 7 → ℝ) (ε : ℝ) (hε : ε ≤ (1 / 9216 : ℝ)) (hdev : ∀ i, |x i - pr i| ≤ ε) :
    ∀ t : ℝ, 0 < t → t ≤ HV → (∀ c, ¬ (aV c - dV c / 2 ≤ t ∧ t ≤ bV c + dV c / 2)) →
      ¬ (∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)) := by
  intro t h0 hHt hnone hlon
  have hεH : ε * HV ≤ (1 / 2048 : ℝ) / 2 := by
    have hε0 : 0 ≤ ε := le_trans (abs_nonneg _) (hdev 0)
    have : ε * HV ≤ (1 / 9216 : ℝ) * HV := mul_le_mul_of_nonneg_right hε (by norm_num [HV])
    have h2 : (1 / 9216 : ℝ) * HV ≤ (1 / 2048 : ℝ) / 2 := by norm_num [HV]
    linarith
  have n0 := hnone (0 : Fin 1)
  rw [aV_0, bV_0, dV_0] at n0
  rcases lt_or_ge t (605 / 2016 : ℝ) with c0 | c0
  · exact gap0 x ε hdev hεH t h0.le hHt h0.le (by linarith) hlon
  have d0 : (91 / 288 : ℝ) < t := by
    by_contra hc; push Not at hc; exact n0 ⟨by linarith, by linarith⟩
  have hHv : HV = (91 / 288 : ℝ) := rfl
  exact absurd (by linarith : t ≤ (91 / 288 : ℝ)) (not_le.2 d0)

theorem inst (x : Fin 7 → ℝ) (ε : ℝ) (hε : ε ≤ (1 / 9216 : ℝ)) (hdev : ∀ i, |x i - pr i| ≤ ε) :
    ∃ c₀ : Fin 1, Alive (mxOf x EXs hEXne) (mnOf x ENs hENne) c₀ ∧
      (∀ c, c < c₀ → ¬ Alive (mxOf x EXs hEXne) (mnOf x ENs hENne) c) ∧
      IsLeast {t : ℝ | 0 < t ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)} (mxOf x EXs hEXne c₀) :=
  landing_cert 1 (15 : ℝ) (by norm_num) pr x hp ε hdev aV bV dV TV ZV hab hd0 hdP haP hT hZ (hE ε hε) hcls EXs ENs hEXne hENne
    hEXdef hENdef hsepL HV hHL (cov x ε hε hdev) (0 : Fin 1) (by rw [dV_0, bV_0, aV_0]; norm_num)

noncomputable def sv : Fin 8 → ℝ := ![(1 : ℝ), (2 : ℝ), (6 : ℝ), (7 : ℝ), (8 : ℝ), (9 : ℝ), (10 : ℝ), (16 : ℝ)]
def sg : Fin 7 → Fin 8 := ![1, 2, 3, 4, 5, 6, 7]

theorem sv_0 : sv (0 : Fin 8) = (1 : ℝ) := rfl
theorem sv_1 : sv (1 : Fin 8) = (2 : ℝ) := rfl
theorem sv_2 : sv (2 : Fin 8) = (6 : ℝ) := rfl
theorem sv_3 : sv (3 : Fin 8) = (7 : ℝ) := rfl
theorem sv_4 : sv (4 : Fin 8) = (8 : ℝ) := rfl
theorem sv_5 : sv (5 : Fin 8) = (9 : ℝ) := rfl
theorem sv_6 : sv (6 : Fin 8) = (10 : ℝ) := rfl
theorem sv_7 : sv (7 : Fin 8) = (16 : ℝ) := rfl
theorem sg_0 : sg (0 : Fin 7) = (1 : Fin 8) := rfl
theorem sg_1 : sg (1 : Fin 7) = (2 : Fin 8) := rfl
theorem sg_2 : sg (2 : Fin 7) = (3 : Fin 8) := rfl
theorem sg_3 : sg (3 : Fin 7) = (4 : Fin 8) := rfl
theorem sg_4 : sg (4 : Fin 7) = (5 : Fin 8) := rfl
theorem sg_5 : sg (5 : Fin 7) = (6 : Fin 8) := rfl
theorem sg_6 : sg (6 : Fin 7) = (7 : Fin 8) := rfl

theorem inst_arr (v : Fin 8 → ℝ) (η : ℝ) (hη : η ≤ (1 / 18432 : ℝ)) (hv : ∀ j, |v j - sv j| ≤ η) :
    ∃ c₀ : Fin 1, Alive (mxOf (fun i => |v (sg i) - v (0 : Fin 8)|) EXs hEXne) (mnOf (fun i => |v (sg i) - v (0 : Fin 8)|) ENs hENne) c₀ ∧
      (∀ c, c < c₀ → ¬ Alive (mxOf (fun i => |v (sg i) - v (0 : Fin 8)|) EXs hEXne) (mnOf (fun i => |v (sg i) - v (0 : Fin 8)|) ENs hENne) c) ∧
      IsLeast {t : ℝ | 0 < t ∧ IsolatedAt v (0 : Fin 8) t} (mxOf (fun i => |v (sg i) - v (0 : Fin 8)|) EXs hEXne c₀) := by
  have hσk : ∀ i, sg i ≠ (0 : Fin 8) := by decide
  have hσ : ∀ j : Fin 8, j ≠ (0 : Fin 8) → ∃ i, sg i = j := by decide
  have hpr : ∀ i, pr i = |sv (sg i) - sv (0 : Fin 8)| := by
    intro i; rcases fin7_cases i with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6, sv_0, sv_1, sv_2, sv_3, sv_4, sv_5, sv_6, sv_7, sg_0, sg_1, sg_2, sg_3, sg_4, sg_5, sg_6]
  have hdev : ∀ i, |(|v (sg i) - v (0 : Fin 8)| - pr i)| ≤ 2 * η := by
    intro i; rw [hpr i]; exact reading_dev v sv η hv (sg i) (0 : Fin 8)
  obtain ⟨c₀, hal, hbf, hT0⟩ := inst (fun i => |v (sg i) - v (0 : Fin 8)|) (2 * η) (by linarith) hdev
  have hset : {t : ℝ | 0 < t ∧ IsolatedAt v (0 : Fin 8) t} =
      {t : ℝ | 0 < t ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (|v (sg i) - v (0 : Fin 8)| * t)} := by
    ext t; simp only [Set.mem_setOf_eq]; rw [iso_iff_readings v (0 : Fin 8) sg hσk hσ t]
  rw [hset]; exact ⟨c₀, hal, hbf, hT0⟩

#print axioms inst_arr

end Fresh.CertRR.R11184



/-!
# Landing certificate `CertRR.R11185`: speeds (1, 2, 6, 7, 8, 9, 10, 16), subject index 1

Generated 2026-10-24 by `experiments/n8/cert_gen_v1.py` (exact Fractions).  Baseline readings [1, 4, 5, 6, 7, 8, 14].  Components up to the first wide one: 1.
Radius: speeds within `η ≤ 1/12544` of the baseline speeds, giving `ε = 2η ≤ 1/6272`.  Covering margin `μ = 1/512`.
`hcov` is **[PROVISIONAL: covering]**, supporting the claim that the first lonely instant of this subject is the largest exit of the first alive component.
Result `inst_arr`: for such `v`, the subject has a first isolation (a least element over all `t > 0`).  Grades: [L].
-/

open Classical

namespace Fresh.CertRR.R11185

open Fresh Fresh.LandingCert Fresh.LandingRule

noncomputable def pr : Fin 7 → ℝ := ![(1 : ℝ), (4 : ℝ), (5 : ℝ), (6 : ℝ), (7 : ℝ), (8 : ℝ), (14 : ℝ)]
noncomputable def aV : Fin 1 → ℝ := ![(17 / 56 : ℝ)]
noncomputable def bV : Fin 1 → ℝ := ![(5 / 16 : ℝ)]
noncomputable def dV : Fin 1 → ℝ := ![(1 / 112 : ℝ)]
noncomputable def TV : Fin 1 → ℝ := ![(9 / 28 : ℝ)]
def ZV : Fin 1 → ℤ := ![6]
noncomputable def HV : ℝ := (71 / 224 : ℝ)
noncomputable def EXs (c : Fin 1) : Finset (Fin 7 × ℤ) :=
  (Finset.univ ×ˢ Finset.Icc 0 (ZV c)).filter (fun q => ((q.2 : ℝ) + 1 / 8) / pr q.1 = aV c)
noncomputable def ENs (c : Fin 1) : Finset (Fin 7 × ℤ) :=
  (Finset.univ ×ˢ Finset.Icc 0 (ZV c)).filter (fun q => ((q.2 : ℝ) - 1 / 8) / pr q.1 = bV c)

theorem hp : ∀ i, 1 ≤ pr i ∧ pr i ≤ (14 : ℝ) := by intro i; fin_cases i <;> norm_num [pr]
theorem hp1 : ∀ i, 1 ≤ pr i := fun i => (hp i).1
theorem pr_0 : pr (0 : Fin 7) = (1 : ℝ) := rfl
theorem pr_1 : pr (1 : Fin 7) = (4 : ℝ) := rfl
theorem pr_2 : pr (2 : Fin 7) = (5 : ℝ) := rfl
theorem pr_3 : pr (3 : Fin 7) = (6 : ℝ) := rfl
theorem pr_4 : pr (4 : Fin 7) = (7 : ℝ) := rfl
theorem pr_5 : pr (5 : Fin 7) = (8 : ℝ) := rfl
theorem pr_6 : pr (6 : Fin 7) = (14 : ℝ) := rfl
theorem aV_0 : aV (0 : Fin 1) = (17 / 56 : ℝ) := rfl
theorem bV_0 : bV (0 : Fin 1) = (5 / 16 : ℝ) := rfl
theorem dV_0 : dV (0 : Fin 1) = (1 / 112 : ℝ) := rfl
theorem TV_0 : TV (0 : Fin 1) = (9 / 28 : ℝ) := rfl
theorem ZV_0 : ZV (0 : Fin 1) = (6 : ℤ) := rfl
theorem hab : ∀ c, aV c ≤ bV c := by intro c; fin_cases c <;> norm_num [aV, bV]
theorem hd0 : ∀ c, 0 < dV c := by intro c; fin_cases c <;> norm_num [dV]
theorem hdP : ∀ c, dV c ≤ 1 / (4 * (14 : ℝ)) := by intro c; fin_cases c <;> norm_num [dV]
theorem haP : ∀ c, dV c < aV c := by intro c; fin_cases c <;> norm_num [dV, aV]
theorem hT : ∀ c, bV c + dV c ≤ TV c := by intro c; fin_cases c <;> norm_num [bV, dV, TV]
theorem hZ : ∀ c, ((14 : ℝ) + 1) * TV c + 1 ≤ (ZV c : ℝ) := by intro c; fin_cases c <;> norm_num [TV, ZV]
theorem hE (ε : ℝ) (hε : ε ≤ (1 / 6272 : ℝ)) : ∀ c, 8 * ((ZV c : ℝ) + 1) * ε ≤ dV c := by
  intro c; fin_cases c <;> norm_num [ZV, dV] <;> linarith
theorem hcls : ∀ c i, ∀ z : ℤ, 0 ≤ z → z ≤ ZV c →
    ((z : ℝ) + 1 / 8) / pr i ≤ aV c - dV c ∨ bV c + dV c ≤ ((z : ℝ) - 1 / 8) / pr i ∨
      ((z : ℝ) + 1 / 8) / pr i = aV c ∨ ((z : ℝ) - 1 / 8) / pr i = bV c := by
  intro c i z h0 h1
  fin_cases c <;> fin_cases i <;> simp [ZV] at h1 <;> interval_cases z <;> norm_num [pr, aV, bV, dV]
theorem hEXne : ∀ c, (EXs c).Nonempty := by
  intro c
  fin_cases c
  · exact ⟨(4, 2), by simp [EXs, ZV, pr, aV] <;> norm_num⟩
theorem hENne : ∀ c, (ENs c).Nonempty := by
  intro c
  fin_cases c
  · exact ⟨(3, 2), by simp [ENs, ZV, pr, bV] <;> norm_num⟩
theorem hEXdef : ∀ c, ∀ q : Fin 7 × ℤ, q ∈ EXs c ↔ 0 ≤ q.2 ∧ q.2 ≤ ZV c ∧ ((q.2 : ℝ) + 1 / 8) / pr q.1 = aV c := by
  intro c q
  simp only [EXs, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, Finset.mem_Icc, true_and]
  tauto
theorem hENdef : ∀ c, ∀ q : Fin 7 × ℤ, q ∈ ENs c ↔ 0 ≤ q.2 ∧ q.2 ≤ ZV c ∧ ((q.2 : ℝ) - 1 / 8) / pr q.1 = bV c := by
  intro c q
  simp only [ENs, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, Finset.mem_Icc, true_and]
  tauto
theorem hsepL : ∀ c c' : Fin 1, c < c' → bV c + dV c / 2 < aV c' - dV c' / 2 := by
  intro c c' h
  fin_cases c <;> fin_cases c' <;> simp at h ⊢ <;> norm_num [aV, bV, dV]
theorem hHL : ∀ c, bV c + dV c / 2 ≤ HV := by intro c; fin_cases c <;> norm_num [bV, dV, HV]

theorem gap0 (x : Fin 7 → ℝ) (ε : ℝ) (hdev : ∀ i, |x i - pr i| ≤ ε) (hεH : ε * HV ≤ (1 / 512 : ℝ) / 2) (t : ℝ) (h0 : 0 ≤ t)
    (hHt : t ≤ HV) (h1 : (0 : ℝ) ≤ t) (h2 : t ≤ (67 / 224 : ℝ)) (hlon : ∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)) : False := by
  rcases le_total t (63 / 512 : ℝ) with hs0 | hs0
  · exact zone_kill_gen pr x ε HV (1 / 512 : ℝ) hp1 hdev hεH (by norm_num) (0 : Fin 7) 0 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (0 : Fin 7))
  rcases le_total t (71 / 512 : ℝ) with hs1 | hs1
  · exact zone_kill_gen pr x ε HV (1 / 512 : ℝ) hp1 hdev hεH (by norm_num) (5 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (5 : Fin 7))
  rcases le_total t (569 / 3584 : ℝ) with hs2 | hs2
  · exact zone_kill_gen pr x ε HV (1 / 512 : ℝ) hp1 hdev hεH (by norm_num) (4 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (4 : Fin 7))
  rcases le_total t (95 / 512 : ℝ) with hs3 | hs3
  · exact zone_kill_gen pr x ε HV (1 / 512 : ℝ) hp1 hdev hεH (by norm_num) (3 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (3 : Fin 7))
  rcases le_total t (571 / 2560 : ℝ) with hs4 | hs4
  · exact zone_kill_gen pr x ε HV (1 / 512 : ℝ) hp1 hdev hεH (by norm_num) (2 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (2 : Fin 7))
  rcases le_total t (143 / 512 : ℝ) with hs5 | hs5
  · exact zone_kill_gen pr x ε HV (1 / 512 : ℝ) hp1 hdev hεH (by norm_num) (1 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (1 : Fin 7))
  exact zone_kill_gen pr x ε HV (1 / 512 : ℝ) hp1 hdev hεH (by norm_num) (4 : Fin 7) 2 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (4 : Fin 7))
theorem cov (x : Fin 7 → ℝ) (ε : ℝ) (hε : ε ≤ (1 / 6272 : ℝ)) (hdev : ∀ i, |x i - pr i| ≤ ε) :
    ∀ t : ℝ, 0 < t → t ≤ HV → (∀ c, ¬ (aV c - dV c / 2 ≤ t ∧ t ≤ bV c + dV c / 2)) →
      ¬ (∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)) := by
  intro t h0 hHt hnone hlon
  have hεH : ε * HV ≤ (1 / 512 : ℝ) / 2 := by
    have hε0 : 0 ≤ ε := le_trans (abs_nonneg _) (hdev 0)
    have : ε * HV ≤ (1 / 6272 : ℝ) * HV := mul_le_mul_of_nonneg_right hε (by norm_num [HV])
    have h2 : (1 / 6272 : ℝ) * HV ≤ (1 / 512 : ℝ) / 2 := by norm_num [HV]
    linarith
  have n0 := hnone (0 : Fin 1)
  rw [aV_0, bV_0, dV_0] at n0
  rcases lt_or_ge t (67 / 224 : ℝ) with c0 | c0
  · exact gap0 x ε hdev hεH t h0.le hHt h0.le (by linarith) hlon
  have d0 : (71 / 224 : ℝ) < t := by
    by_contra hc; push Not at hc; exact n0 ⟨by linarith, by linarith⟩
  have hHv : HV = (71 / 224 : ℝ) := rfl
  exact absurd (by linarith : t ≤ (71 / 224 : ℝ)) (not_le.2 d0)

theorem inst (x : Fin 7 → ℝ) (ε : ℝ) (hε : ε ≤ (1 / 6272 : ℝ)) (hdev : ∀ i, |x i - pr i| ≤ ε) :
    ∃ c₀ : Fin 1, Alive (mxOf x EXs hEXne) (mnOf x ENs hENne) c₀ ∧
      (∀ c, c < c₀ → ¬ Alive (mxOf x EXs hEXne) (mnOf x ENs hENne) c) ∧
      IsLeast {t : ℝ | 0 < t ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)} (mxOf x EXs hEXne c₀) :=
  landing_cert 1 (14 : ℝ) (by norm_num) pr x hp ε hdev aV bV dV TV ZV hab hd0 hdP haP hT hZ (hE ε hε) hcls EXs ENs hEXne hENne
    hEXdef hENdef hsepL HV hHL (cov x ε hε hdev) (0 : Fin 1) (by rw [dV_0, bV_0, aV_0]; norm_num)

noncomputable def sv : Fin 8 → ℝ := ![(1 : ℝ), (2 : ℝ), (6 : ℝ), (7 : ℝ), (8 : ℝ), (9 : ℝ), (10 : ℝ), (16 : ℝ)]
def sg : Fin 7 → Fin 8 := ![0, 2, 3, 4, 5, 6, 7]

theorem sv_0 : sv (0 : Fin 8) = (1 : ℝ) := rfl
theorem sv_1 : sv (1 : Fin 8) = (2 : ℝ) := rfl
theorem sv_2 : sv (2 : Fin 8) = (6 : ℝ) := rfl
theorem sv_3 : sv (3 : Fin 8) = (7 : ℝ) := rfl
theorem sv_4 : sv (4 : Fin 8) = (8 : ℝ) := rfl
theorem sv_5 : sv (5 : Fin 8) = (9 : ℝ) := rfl
theorem sv_6 : sv (6 : Fin 8) = (10 : ℝ) := rfl
theorem sv_7 : sv (7 : Fin 8) = (16 : ℝ) := rfl
theorem sg_0 : sg (0 : Fin 7) = (0 : Fin 8) := rfl
theorem sg_1 : sg (1 : Fin 7) = (2 : Fin 8) := rfl
theorem sg_2 : sg (2 : Fin 7) = (3 : Fin 8) := rfl
theorem sg_3 : sg (3 : Fin 7) = (4 : Fin 8) := rfl
theorem sg_4 : sg (4 : Fin 7) = (5 : Fin 8) := rfl
theorem sg_5 : sg (5 : Fin 7) = (6 : Fin 8) := rfl
theorem sg_6 : sg (6 : Fin 7) = (7 : Fin 8) := rfl

theorem inst_arr (v : Fin 8 → ℝ) (η : ℝ) (hη : η ≤ (1 / 12544 : ℝ)) (hv : ∀ j, |v j - sv j| ≤ η) :
    ∃ c₀ : Fin 1, Alive (mxOf (fun i => |v (sg i) - v (1 : Fin 8)|) EXs hEXne) (mnOf (fun i => |v (sg i) - v (1 : Fin 8)|) ENs hENne) c₀ ∧
      (∀ c, c < c₀ → ¬ Alive (mxOf (fun i => |v (sg i) - v (1 : Fin 8)|) EXs hEXne) (mnOf (fun i => |v (sg i) - v (1 : Fin 8)|) ENs hENne) c) ∧
      IsLeast {t : ℝ | 0 < t ∧ IsolatedAt v (1 : Fin 8) t} (mxOf (fun i => |v (sg i) - v (1 : Fin 8)|) EXs hEXne c₀) := by
  have hσk : ∀ i, sg i ≠ (1 : Fin 8) := by decide
  have hσ : ∀ j : Fin 8, j ≠ (1 : Fin 8) → ∃ i, sg i = j := by decide
  have hpr : ∀ i, pr i = |sv (sg i) - sv (1 : Fin 8)| := by
    intro i; rcases fin7_cases i with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6, sv_0, sv_1, sv_2, sv_3, sv_4, sv_5, sv_6, sv_7, sg_0, sg_1, sg_2, sg_3, sg_4, sg_5, sg_6]
  have hdev : ∀ i, |(|v (sg i) - v (1 : Fin 8)| - pr i)| ≤ 2 * η := by
    intro i; rw [hpr i]; exact reading_dev v sv η hv (sg i) (1 : Fin 8)
  obtain ⟨c₀, hal, hbf, hT0⟩ := inst (fun i => |v (sg i) - v (1 : Fin 8)|) (2 * η) (by linarith) hdev
  have hset : {t : ℝ | 0 < t ∧ IsolatedAt v (1 : Fin 8) t} =
      {t : ℝ | 0 < t ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (|v (sg i) - v (1 : Fin 8)| * t)} := by
    ext t; simp only [Set.mem_setOf_eq]; rw [iso_iff_readings v (1 : Fin 8) sg hσk hσ t]
  rw [hset]; exact ⟨c₀, hal, hbf, hT0⟩

#print axioms inst_arr

end Fresh.CertRR.R11185



/-!
# Landing certificate `CertRR.R11191`: speeds (1, 2, 6, 7, 8, 9, 10, 16), subject index 7

Generated 2026-10-24 by `experiments/n8/cert_gen_v1.py` (exact Fractions).  Baseline readings [15, 14, 10, 9, 8, 7, 6].  Components up to the first wide one: 1.
Radius: speeds within `η ≤ 1/21504` of the baseline speeds, giving `ε = 2η ≤ 1/10752`.  Covering margin `μ = 1/1024`.
`hcov` is **[PROVISIONAL: covering]**, supporting the claim that the first lonely instant of this subject is the largest exit of the first alive component.
Result `inst_arr`: for such `v`, the subject has a first isolation (a least element over all `t > 0`).  Grades: [L].
-/

open Classical

namespace Fresh.CertRR.R11191

open Fresh Fresh.LandingCert Fresh.LandingRule

noncomputable def pr : Fin 7 → ℝ := ![(15 : ℝ), (14 : ℝ), (10 : ℝ), (9 : ℝ), (8 : ℝ), (7 : ℝ), (6 : ℝ)]
noncomputable def aV : Fin 1 → ℝ := ![(1 / 48 : ℝ)]
noncomputable def bV : Fin 1 → ℝ := ![(7 / 120 : ℝ)]
noncomputable def dV : Fin 1 → ℝ := ![(1 / 336 : ℝ)]
noncomputable def TV : Fin 1 → ℝ := ![(103 / 1680 : ℝ)]
def ZV : Fin 1 → ℤ := ![3]
noncomputable def HV : ℝ := (67 / 1120 : ℝ)
noncomputable def EXs (c : Fin 1) : Finset (Fin 7 × ℤ) :=
  (Finset.univ ×ˢ Finset.Icc 0 (ZV c)).filter (fun q => ((q.2 : ℝ) + 1 / 8) / pr q.1 = aV c)
noncomputable def ENs (c : Fin 1) : Finset (Fin 7 × ℤ) :=
  (Finset.univ ×ˢ Finset.Icc 0 (ZV c)).filter (fun q => ((q.2 : ℝ) - 1 / 8) / pr q.1 = bV c)

theorem hp : ∀ i, 1 ≤ pr i ∧ pr i ≤ (15 : ℝ) := by intro i; fin_cases i <;> norm_num [pr]
theorem hp1 : ∀ i, 1 ≤ pr i := fun i => (hp i).1
theorem pr_0 : pr (0 : Fin 7) = (15 : ℝ) := rfl
theorem pr_1 : pr (1 : Fin 7) = (14 : ℝ) := rfl
theorem pr_2 : pr (2 : Fin 7) = (10 : ℝ) := rfl
theorem pr_3 : pr (3 : Fin 7) = (9 : ℝ) := rfl
theorem pr_4 : pr (4 : Fin 7) = (8 : ℝ) := rfl
theorem pr_5 : pr (5 : Fin 7) = (7 : ℝ) := rfl
theorem pr_6 : pr (6 : Fin 7) = (6 : ℝ) := rfl
theorem aV_0 : aV (0 : Fin 1) = (1 / 48 : ℝ) := rfl
theorem bV_0 : bV (0 : Fin 1) = (7 / 120 : ℝ) := rfl
theorem dV_0 : dV (0 : Fin 1) = (1 / 336 : ℝ) := rfl
theorem TV_0 : TV (0 : Fin 1) = (103 / 1680 : ℝ) := rfl
theorem ZV_0 : ZV (0 : Fin 1) = (3 : ℤ) := rfl
theorem hab : ∀ c, aV c ≤ bV c := by intro c; fin_cases c <;> norm_num [aV, bV]
theorem hd0 : ∀ c, 0 < dV c := by intro c; fin_cases c <;> norm_num [dV]
theorem hdP : ∀ c, dV c ≤ 1 / (4 * (15 : ℝ)) := by intro c; fin_cases c <;> norm_num [dV]
theorem haP : ∀ c, dV c < aV c := by intro c; fin_cases c <;> norm_num [dV, aV]
theorem hT : ∀ c, bV c + dV c ≤ TV c := by intro c; fin_cases c <;> norm_num [bV, dV, TV]
theorem hZ : ∀ c, ((15 : ℝ) + 1) * TV c + 1 ≤ (ZV c : ℝ) := by intro c; fin_cases c <;> norm_num [TV, ZV]
theorem hE (ε : ℝ) (hε : ε ≤ (1 / 10752 : ℝ)) : ∀ c, 8 * ((ZV c : ℝ) + 1) * ε ≤ dV c := by
  intro c; fin_cases c <;> norm_num [ZV, dV] <;> linarith
theorem hcls : ∀ c i, ∀ z : ℤ, 0 ≤ z → z ≤ ZV c →
    ((z : ℝ) + 1 / 8) / pr i ≤ aV c - dV c ∨ bV c + dV c ≤ ((z : ℝ) - 1 / 8) / pr i ∨
      ((z : ℝ) + 1 / 8) / pr i = aV c ∨ ((z : ℝ) - 1 / 8) / pr i = bV c := by
  intro c i z h0 h1
  fin_cases c <;> fin_cases i <;> simp [ZV] at h1 <;> interval_cases z <;> norm_num [pr, aV, bV, dV]
theorem hEXne : ∀ c, (EXs c).Nonempty := by
  intro c
  fin_cases c
  · exact ⟨(6, 0), by simp [EXs, ZV, pr, aV] <;> norm_num⟩
theorem hENne : ∀ c, (ENs c).Nonempty := by
  intro c
  fin_cases c
  · exact ⟨(0, 1), by simp [ENs, ZV, pr, bV] <;> norm_num⟩
theorem hEXdef : ∀ c, ∀ q : Fin 7 × ℤ, q ∈ EXs c ↔ 0 ≤ q.2 ∧ q.2 ≤ ZV c ∧ ((q.2 : ℝ) + 1 / 8) / pr q.1 = aV c := by
  intro c q
  simp only [EXs, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, Finset.mem_Icc, true_and]
  tauto
theorem hENdef : ∀ c, ∀ q : Fin 7 × ℤ, q ∈ ENs c ↔ 0 ≤ q.2 ∧ q.2 ≤ ZV c ∧ ((q.2 : ℝ) - 1 / 8) / pr q.1 = bV c := by
  intro c q
  simp only [ENs, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, Finset.mem_Icc, true_and]
  tauto
theorem hsepL : ∀ c c' : Fin 1, c < c' → bV c + dV c / 2 < aV c' - dV c' / 2 := by
  intro c c' h
  fin_cases c <;> fin_cases c' <;> simp at h ⊢ <;> norm_num [aV, bV, dV]
theorem hHL : ∀ c, bV c + dV c / 2 ≤ HV := by intro c; fin_cases c <;> norm_num [bV, dV, HV]

theorem gap0 (x : Fin 7 → ℝ) (ε : ℝ) (hdev : ∀ i, |x i - pr i| ≤ ε) (hεH : ε * HV ≤ (1 / 1024 : ℝ) / 2) (t : ℝ) (h0 : 0 ≤ t)
    (hHt : t ≤ HV) (h1 : (0 : ℝ) ≤ t) (h2 : t ≤ (13 / 672 : ℝ)) (hlon : ∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)) : False := by
  exact zone_kill_gen pr x ε HV (1 / 1024 : ℝ) hp1 hdev hεH (by norm_num) (6 : Fin 7) 0 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (6 : Fin 7))
theorem cov (x : Fin 7 → ℝ) (ε : ℝ) (hε : ε ≤ (1 / 10752 : ℝ)) (hdev : ∀ i, |x i - pr i| ≤ ε) :
    ∀ t : ℝ, 0 < t → t ≤ HV → (∀ c, ¬ (aV c - dV c / 2 ≤ t ∧ t ≤ bV c + dV c / 2)) →
      ¬ (∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)) := by
  intro t h0 hHt hnone hlon
  have hεH : ε * HV ≤ (1 / 1024 : ℝ) / 2 := by
    have hε0 : 0 ≤ ε := le_trans (abs_nonneg _) (hdev 0)
    have : ε * HV ≤ (1 / 10752 : ℝ) * HV := mul_le_mul_of_nonneg_right hε (by norm_num [HV])
    have h2 : (1 / 10752 : ℝ) * HV ≤ (1 / 1024 : ℝ) / 2 := by norm_num [HV]
    linarith
  have n0 := hnone (0 : Fin 1)
  rw [aV_0, bV_0, dV_0] at n0
  rcases lt_or_ge t (13 / 672 : ℝ) with c0 | c0
  · exact gap0 x ε hdev hεH t h0.le hHt h0.le (by linarith) hlon
  have d0 : (67 / 1120 : ℝ) < t := by
    by_contra hc; push Not at hc; exact n0 ⟨by linarith, by linarith⟩
  have hHv : HV = (67 / 1120 : ℝ) := rfl
  exact absurd (by linarith : t ≤ (67 / 1120 : ℝ)) (not_le.2 d0)

theorem inst (x : Fin 7 → ℝ) (ε : ℝ) (hε : ε ≤ (1 / 10752 : ℝ)) (hdev : ∀ i, |x i - pr i| ≤ ε) :
    ∃ c₀ : Fin 1, Alive (mxOf x EXs hEXne) (mnOf x ENs hENne) c₀ ∧
      (∀ c, c < c₀ → ¬ Alive (mxOf x EXs hEXne) (mnOf x ENs hENne) c) ∧
      IsLeast {t : ℝ | 0 < t ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)} (mxOf x EXs hEXne c₀) :=
  landing_cert 1 (15 : ℝ) (by norm_num) pr x hp ε hdev aV bV dV TV ZV hab hd0 hdP haP hT hZ (hE ε hε) hcls EXs ENs hEXne hENne
    hEXdef hENdef hsepL HV hHL (cov x ε hε hdev) (0 : Fin 1) (by rw [dV_0, bV_0, aV_0]; norm_num)

noncomputable def sv : Fin 8 → ℝ := ![(1 : ℝ), (2 : ℝ), (6 : ℝ), (7 : ℝ), (8 : ℝ), (9 : ℝ), (10 : ℝ), (16 : ℝ)]
def sg : Fin 7 → Fin 8 := ![0, 1, 2, 3, 4, 5, 6]

theorem sv_0 : sv (0 : Fin 8) = (1 : ℝ) := rfl
theorem sv_1 : sv (1 : Fin 8) = (2 : ℝ) := rfl
theorem sv_2 : sv (2 : Fin 8) = (6 : ℝ) := rfl
theorem sv_3 : sv (3 : Fin 8) = (7 : ℝ) := rfl
theorem sv_4 : sv (4 : Fin 8) = (8 : ℝ) := rfl
theorem sv_5 : sv (5 : Fin 8) = (9 : ℝ) := rfl
theorem sv_6 : sv (6 : Fin 8) = (10 : ℝ) := rfl
theorem sv_7 : sv (7 : Fin 8) = (16 : ℝ) := rfl
theorem sg_0 : sg (0 : Fin 7) = (0 : Fin 8) := rfl
theorem sg_1 : sg (1 : Fin 7) = (1 : Fin 8) := rfl
theorem sg_2 : sg (2 : Fin 7) = (2 : Fin 8) := rfl
theorem sg_3 : sg (3 : Fin 7) = (3 : Fin 8) := rfl
theorem sg_4 : sg (4 : Fin 7) = (4 : Fin 8) := rfl
theorem sg_5 : sg (5 : Fin 7) = (5 : Fin 8) := rfl
theorem sg_6 : sg (6 : Fin 7) = (6 : Fin 8) := rfl

theorem inst_arr (v : Fin 8 → ℝ) (η : ℝ) (hη : η ≤ (1 / 21504 : ℝ)) (hv : ∀ j, |v j - sv j| ≤ η) :
    ∃ c₀ : Fin 1, Alive (mxOf (fun i => |v (sg i) - v (7 : Fin 8)|) EXs hEXne) (mnOf (fun i => |v (sg i) - v (7 : Fin 8)|) ENs hENne) c₀ ∧
      (∀ c, c < c₀ → ¬ Alive (mxOf (fun i => |v (sg i) - v (7 : Fin 8)|) EXs hEXne) (mnOf (fun i => |v (sg i) - v (7 : Fin 8)|) ENs hENne) c) ∧
      IsLeast {t : ℝ | 0 < t ∧ IsolatedAt v (7 : Fin 8) t} (mxOf (fun i => |v (sg i) - v (7 : Fin 8)|) EXs hEXne c₀) := by
  have hσk : ∀ i, sg i ≠ (7 : Fin 8) := by decide
  have hσ : ∀ j : Fin 8, j ≠ (7 : Fin 8) → ∃ i, sg i = j := by decide
  have hpr : ∀ i, pr i = |sv (sg i) - sv (7 : Fin 8)| := by
    intro i; rcases fin7_cases i with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6, sv_0, sv_1, sv_2, sv_3, sv_4, sv_5, sv_6, sv_7, sg_0, sg_1, sg_2, sg_3, sg_4, sg_5, sg_6]
  have hdev : ∀ i, |(|v (sg i) - v (7 : Fin 8)| - pr i)| ≤ 2 * η := by
    intro i; rw [hpr i]; exact reading_dev v sv η hv (sg i) (7 : Fin 8)
  obtain ⟨c₀, hal, hbf, hT0⟩ := inst (fun i => |v (sg i) - v (7 : Fin 8)|) (2 * η) (by linarith) hdev
  have hset : {t : ℝ | 0 < t ∧ IsolatedAt v (7 : Fin 8) t} =
      {t : ℝ | 0 < t ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (|v (sg i) - v (7 : Fin 8)| * t)} := by
    ext t; simp only [Set.mem_setOf_eq]; rw [iso_iff_readings v (7 : Fin 8) sg hσk hσ t]
  rw [hset]; exact ⟨c₀, hal, hbf, hT0⟩

#print axioms inst_arr

end Fresh.CertRR.R11191



/-!
# Landing certificate `CertRR.R11192`: speeds (1, 2, 6, 7, 8, 9, 11, 12), subject index 0

Generated 2026-10-24 by `experiments/n8/cert_gen_v1.py` (exact Fractions).  Baseline readings [1, 5, 6, 7, 8, 10, 11].  Components up to the first wide one: 1.
Radius: speeds within `η ≤ 1/7680` of the baseline speeds, giving `ε = 2η ≤ 1/3840`.  Covering margin `μ = 1/256`.
`hcov` is **[PROVISIONAL: covering]**, supporting the claim that the first lonely instant of this subject is the largest exit of the first alive component.
Result `inst_arr`: for such `v`, the subject has a first isolation (a least element over all `t > 0`).  Grades: [L].
-/

open Classical

namespace Fresh.CertRR.R11192

open Fresh Fresh.LandingCert Fresh.LandingRule

noncomputable def pr : Fin 7 → ℝ := ![(1 : ℝ), (5 : ℝ), (6 : ℝ), (7 : ℝ), (8 : ℝ), (10 : ℝ), (11 : ℝ)]
noncomputable def aV : Fin 1 → ℝ := ![(9 / 40 : ℝ)]
noncomputable def bV : Fin 1 → ℝ := ![(15 / 64 : ℝ)]
noncomputable def dV : Fin 1 → ℝ := ![(1 / 80 : ℝ)]
noncomputable def TV : Fin 1 → ℝ := ![(79 / 320 : ℝ)]
def ZV : Fin 1 → ℤ := ![5]
noncomputable def HV : ℝ := (77 / 320 : ℝ)
noncomputable def EXs (c : Fin 1) : Finset (Fin 7 × ℤ) :=
  (Finset.univ ×ˢ Finset.Icc 0 (ZV c)).filter (fun q => ((q.2 : ℝ) + 1 / 8) / pr q.1 = aV c)
noncomputable def ENs (c : Fin 1) : Finset (Fin 7 × ℤ) :=
  (Finset.univ ×ˢ Finset.Icc 0 (ZV c)).filter (fun q => ((q.2 : ℝ) - 1 / 8) / pr q.1 = bV c)

theorem hp : ∀ i, 1 ≤ pr i ∧ pr i ≤ (11 : ℝ) := by intro i; fin_cases i <;> norm_num [pr]
theorem hp1 : ∀ i, 1 ≤ pr i := fun i => (hp i).1
theorem pr_0 : pr (0 : Fin 7) = (1 : ℝ) := rfl
theorem pr_1 : pr (1 : Fin 7) = (5 : ℝ) := rfl
theorem pr_2 : pr (2 : Fin 7) = (6 : ℝ) := rfl
theorem pr_3 : pr (3 : Fin 7) = (7 : ℝ) := rfl
theorem pr_4 : pr (4 : Fin 7) = (8 : ℝ) := rfl
theorem pr_5 : pr (5 : Fin 7) = (10 : ℝ) := rfl
theorem pr_6 : pr (6 : Fin 7) = (11 : ℝ) := rfl
theorem aV_0 : aV (0 : Fin 1) = (9 / 40 : ℝ) := rfl
theorem bV_0 : bV (0 : Fin 1) = (15 / 64 : ℝ) := rfl
theorem dV_0 : dV (0 : Fin 1) = (1 / 80 : ℝ) := rfl
theorem TV_0 : TV (0 : Fin 1) = (79 / 320 : ℝ) := rfl
theorem ZV_0 : ZV (0 : Fin 1) = (5 : ℤ) := rfl
theorem hab : ∀ c, aV c ≤ bV c := by intro c; fin_cases c <;> norm_num [aV, bV]
theorem hd0 : ∀ c, 0 < dV c := by intro c; fin_cases c <;> norm_num [dV]
theorem hdP : ∀ c, dV c ≤ 1 / (4 * (11 : ℝ)) := by intro c; fin_cases c <;> norm_num [dV]
theorem haP : ∀ c, dV c < aV c := by intro c; fin_cases c <;> norm_num [dV, aV]
theorem hT : ∀ c, bV c + dV c ≤ TV c := by intro c; fin_cases c <;> norm_num [bV, dV, TV]
theorem hZ : ∀ c, ((11 : ℝ) + 1) * TV c + 1 ≤ (ZV c : ℝ) := by intro c; fin_cases c <;> norm_num [TV, ZV]
theorem hE (ε : ℝ) (hε : ε ≤ (1 / 3840 : ℝ)) : ∀ c, 8 * ((ZV c : ℝ) + 1) * ε ≤ dV c := by
  intro c; fin_cases c <;> norm_num [ZV, dV] <;> linarith
theorem hcls : ∀ c i, ∀ z : ℤ, 0 ≤ z → z ≤ ZV c →
    ((z : ℝ) + 1 / 8) / pr i ≤ aV c - dV c ∨ bV c + dV c ≤ ((z : ℝ) - 1 / 8) / pr i ∨
      ((z : ℝ) + 1 / 8) / pr i = aV c ∨ ((z : ℝ) - 1 / 8) / pr i = bV c := by
  intro c i z h0 h1
  fin_cases c <;> fin_cases i <;> simp [ZV] at h1 <;> interval_cases z <;> norm_num [pr, aV, bV, dV]
theorem hEXne : ∀ c, (EXs c).Nonempty := by
  intro c
  fin_cases c
  · exact ⟨(1, 1), by simp [EXs, ZV, pr, aV] <;> norm_num⟩
theorem hENne : ∀ c, (ENs c).Nonempty := by
  intro c
  fin_cases c
  · exact ⟨(4, 2), by simp [ENs, ZV, pr, bV] <;> norm_num⟩
theorem hEXdef : ∀ c, ∀ q : Fin 7 × ℤ, q ∈ EXs c ↔ 0 ≤ q.2 ∧ q.2 ≤ ZV c ∧ ((q.2 : ℝ) + 1 / 8) / pr q.1 = aV c := by
  intro c q
  simp only [EXs, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, Finset.mem_Icc, true_and]
  tauto
theorem hENdef : ∀ c, ∀ q : Fin 7 × ℤ, q ∈ ENs c ↔ 0 ≤ q.2 ∧ q.2 ≤ ZV c ∧ ((q.2 : ℝ) - 1 / 8) / pr q.1 = bV c := by
  intro c q
  simp only [ENs, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, Finset.mem_Icc, true_and]
  tauto
theorem hsepL : ∀ c c' : Fin 1, c < c' → bV c + dV c / 2 < aV c' - dV c' / 2 := by
  intro c c' h
  fin_cases c <;> fin_cases c' <;> simp at h ⊢ <;> norm_num [aV, bV, dV]
theorem hHL : ∀ c, bV c + dV c / 2 ≤ HV := by intro c; fin_cases c <;> norm_num [bV, dV, HV]

theorem gap0 (x : Fin 7 → ℝ) (ε : ℝ) (hdev : ∀ i, |x i - pr i| ≤ ε) (hεH : ε * HV ≤ (1 / 256 : ℝ) / 2) (t : ℝ) (h0 : 0 ≤ t)
    (hHt : t ≤ HV) (h1 : (0 : ℝ) ≤ t) (h2 : t ≤ (7 / 32 : ℝ)) (hlon : ∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)) : False := by
  rcases le_total t (31 / 256 : ℝ) with hs0 | hs0
  · exact zone_kill_gen pr x ε HV (1 / 256 : ℝ) hp1 hdev hεH (by norm_num) (0 : Fin 7) 0 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (0 : Fin 7))
  rcases le_total t (35 / 256 : ℝ) with hs1 | hs1
  · exact zone_kill_gen pr x ε HV (1 / 256 : ℝ) hp1 hdev hεH (by norm_num) (4 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (4 : Fin 7))
  rcases le_total t (281 / 1792 : ℝ) with hs2 | hs2
  · exact zone_kill_gen pr x ε HV (1 / 256 : ℝ) hp1 hdev hεH (by norm_num) (3 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (3 : Fin 7))
  rcases le_total t (47 / 256 : ℝ) with hs3 | hs3
  · exact zone_kill_gen pr x ε HV (1 / 256 : ℝ) hp1 hdev hεH (by norm_num) (2 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (2 : Fin 7))
  exact zone_kill_gen pr x ε HV (1 / 256 : ℝ) hp1 hdev hεH (by norm_num) (1 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (1 : Fin 7))
theorem cov (x : Fin 7 → ℝ) (ε : ℝ) (hε : ε ≤ (1 / 3840 : ℝ)) (hdev : ∀ i, |x i - pr i| ≤ ε) :
    ∀ t : ℝ, 0 < t → t ≤ HV → (∀ c, ¬ (aV c - dV c / 2 ≤ t ∧ t ≤ bV c + dV c / 2)) →
      ¬ (∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)) := by
  intro t h0 hHt hnone hlon
  have hεH : ε * HV ≤ (1 / 256 : ℝ) / 2 := by
    have hε0 : 0 ≤ ε := le_trans (abs_nonneg _) (hdev 0)
    have : ε * HV ≤ (1 / 3840 : ℝ) * HV := mul_le_mul_of_nonneg_right hε (by norm_num [HV])
    have h2 : (1 / 3840 : ℝ) * HV ≤ (1 / 256 : ℝ) / 2 := by norm_num [HV]
    linarith
  have n0 := hnone (0 : Fin 1)
  rw [aV_0, bV_0, dV_0] at n0
  rcases lt_or_ge t (7 / 32 : ℝ) with c0 | c0
  · exact gap0 x ε hdev hεH t h0.le hHt h0.le (by linarith) hlon
  have d0 : (77 / 320 : ℝ) < t := by
    by_contra hc; push Not at hc; exact n0 ⟨by linarith, by linarith⟩
  have hHv : HV = (77 / 320 : ℝ) := rfl
  exact absurd (by linarith : t ≤ (77 / 320 : ℝ)) (not_le.2 d0)

theorem inst (x : Fin 7 → ℝ) (ε : ℝ) (hε : ε ≤ (1 / 3840 : ℝ)) (hdev : ∀ i, |x i - pr i| ≤ ε) :
    ∃ c₀ : Fin 1, Alive (mxOf x EXs hEXne) (mnOf x ENs hENne) c₀ ∧
      (∀ c, c < c₀ → ¬ Alive (mxOf x EXs hEXne) (mnOf x ENs hENne) c) ∧
      IsLeast {t : ℝ | 0 < t ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)} (mxOf x EXs hEXne c₀) :=
  landing_cert 1 (11 : ℝ) (by norm_num) pr x hp ε hdev aV bV dV TV ZV hab hd0 hdP haP hT hZ (hE ε hε) hcls EXs ENs hEXne hENne
    hEXdef hENdef hsepL HV hHL (cov x ε hε hdev) (0 : Fin 1) (by rw [dV_0, bV_0, aV_0]; norm_num)

noncomputable def sv : Fin 8 → ℝ := ![(1 : ℝ), (2 : ℝ), (6 : ℝ), (7 : ℝ), (8 : ℝ), (9 : ℝ), (11 : ℝ), (12 : ℝ)]
def sg : Fin 7 → Fin 8 := ![1, 2, 3, 4, 5, 6, 7]

theorem sv_0 : sv (0 : Fin 8) = (1 : ℝ) := rfl
theorem sv_1 : sv (1 : Fin 8) = (2 : ℝ) := rfl
theorem sv_2 : sv (2 : Fin 8) = (6 : ℝ) := rfl
theorem sv_3 : sv (3 : Fin 8) = (7 : ℝ) := rfl
theorem sv_4 : sv (4 : Fin 8) = (8 : ℝ) := rfl
theorem sv_5 : sv (5 : Fin 8) = (9 : ℝ) := rfl
theorem sv_6 : sv (6 : Fin 8) = (11 : ℝ) := rfl
theorem sv_7 : sv (7 : Fin 8) = (12 : ℝ) := rfl
theorem sg_0 : sg (0 : Fin 7) = (1 : Fin 8) := rfl
theorem sg_1 : sg (1 : Fin 7) = (2 : Fin 8) := rfl
theorem sg_2 : sg (2 : Fin 7) = (3 : Fin 8) := rfl
theorem sg_3 : sg (3 : Fin 7) = (4 : Fin 8) := rfl
theorem sg_4 : sg (4 : Fin 7) = (5 : Fin 8) := rfl
theorem sg_5 : sg (5 : Fin 7) = (6 : Fin 8) := rfl
theorem sg_6 : sg (6 : Fin 7) = (7 : Fin 8) := rfl

theorem inst_arr (v : Fin 8 → ℝ) (η : ℝ) (hη : η ≤ (1 / 7680 : ℝ)) (hv : ∀ j, |v j - sv j| ≤ η) :
    ∃ c₀ : Fin 1, Alive (mxOf (fun i => |v (sg i) - v (0 : Fin 8)|) EXs hEXne) (mnOf (fun i => |v (sg i) - v (0 : Fin 8)|) ENs hENne) c₀ ∧
      (∀ c, c < c₀ → ¬ Alive (mxOf (fun i => |v (sg i) - v (0 : Fin 8)|) EXs hEXne) (mnOf (fun i => |v (sg i) - v (0 : Fin 8)|) ENs hENne) c) ∧
      IsLeast {t : ℝ | 0 < t ∧ IsolatedAt v (0 : Fin 8) t} (mxOf (fun i => |v (sg i) - v (0 : Fin 8)|) EXs hEXne c₀) := by
  have hσk : ∀ i, sg i ≠ (0 : Fin 8) := by decide
  have hσ : ∀ j : Fin 8, j ≠ (0 : Fin 8) → ∃ i, sg i = j := by decide
  have hpr : ∀ i, pr i = |sv (sg i) - sv (0 : Fin 8)| := by
    intro i; rcases fin7_cases i with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6, sv_0, sv_1, sv_2, sv_3, sv_4, sv_5, sv_6, sv_7, sg_0, sg_1, sg_2, sg_3, sg_4, sg_5, sg_6]
  have hdev : ∀ i, |(|v (sg i) - v (0 : Fin 8)| - pr i)| ≤ 2 * η := by
    intro i; rw [hpr i]; exact reading_dev v sv η hv (sg i) (0 : Fin 8)
  obtain ⟨c₀, hal, hbf, hT0⟩ := inst (fun i => |v (sg i) - v (0 : Fin 8)|) (2 * η) (by linarith) hdev
  have hset : {t : ℝ | 0 < t ∧ IsolatedAt v (0 : Fin 8) t} =
      {t : ℝ | 0 < t ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (|v (sg i) - v (0 : Fin 8)| * t)} := by
    ext t; simp only [Set.mem_setOf_eq]; rw [iso_iff_readings v (0 : Fin 8) sg hσk hσ t]
  rw [hset]; exact ⟨c₀, hal, hbf, hT0⟩

#print axioms inst_arr

end Fresh.CertRR.R11192



/-!
# Landing certificate `CertRR.R11200`: speeds (1, 2, 6, 7, 8, 9, 11, 13), subject index 0

Generated 2026-10-24 by `experiments/n8/cert_gen_v1.py` (exact Fractions).  Baseline readings [1, 5, 6, 7, 8, 10, 12].  Components up to the first wide one: 1.
Radius: speeds within `η ≤ 1/18432` of the baseline speeds, giving `ε = 2η ≤ 1/9216`.  Covering margin `μ = 1/512`.
`hcov` is **[PROVISIONAL: covering]**, supporting the claim that the first lonely instant of this subject is the largest exit of the first alive component.
Result `inst_arr`: for such `v`, the subject has a first isolation (a least element over all `t > 0`).  Grades: [L].
-/

open Classical

namespace Fresh.CertRR.R11200

open Fresh Fresh.LandingCert Fresh.LandingRule

noncomputable def pr : Fin 7 → ℝ := ![(1 : ℝ), (5 : ℝ), (6 : ℝ), (7 : ℝ), (8 : ℝ), (10 : ℝ), (12 : ℝ)]
noncomputable def aV : Fin 1 → ℝ := ![(9 / 40 : ℝ)]
noncomputable def bV : Fin 1 → ℝ := ![(15 / 64 : ℝ)]
noncomputable def dV : Fin 1 → ℝ := ![(1 / 192 : ℝ)]
noncomputable def TV : Fin 1 → ℝ := ![(23 / 96 : ℝ)]
def ZV : Fin 1 → ℤ := ![5]
noncomputable def HV : ℝ := (91 / 384 : ℝ)
noncomputable def EXs (c : Fin 1) : Finset (Fin 7 × ℤ) :=
  (Finset.univ ×ˢ Finset.Icc 0 (ZV c)).filter (fun q => ((q.2 : ℝ) + 1 / 8) / pr q.1 = aV c)
noncomputable def ENs (c : Fin 1) : Finset (Fin 7 × ℤ) :=
  (Finset.univ ×ˢ Finset.Icc 0 (ZV c)).filter (fun q => ((q.2 : ℝ) - 1 / 8) / pr q.1 = bV c)

theorem hp : ∀ i, 1 ≤ pr i ∧ pr i ≤ (12 : ℝ) := by intro i; fin_cases i <;> norm_num [pr]
theorem hp1 : ∀ i, 1 ≤ pr i := fun i => (hp i).1
theorem pr_0 : pr (0 : Fin 7) = (1 : ℝ) := rfl
theorem pr_1 : pr (1 : Fin 7) = (5 : ℝ) := rfl
theorem pr_2 : pr (2 : Fin 7) = (6 : ℝ) := rfl
theorem pr_3 : pr (3 : Fin 7) = (7 : ℝ) := rfl
theorem pr_4 : pr (4 : Fin 7) = (8 : ℝ) := rfl
theorem pr_5 : pr (5 : Fin 7) = (10 : ℝ) := rfl
theorem pr_6 : pr (6 : Fin 7) = (12 : ℝ) := rfl
theorem aV_0 : aV (0 : Fin 1) = (9 / 40 : ℝ) := rfl
theorem bV_0 : bV (0 : Fin 1) = (15 / 64 : ℝ) := rfl
theorem dV_0 : dV (0 : Fin 1) = (1 / 192 : ℝ) := rfl
theorem TV_0 : TV (0 : Fin 1) = (23 / 96 : ℝ) := rfl
theorem ZV_0 : ZV (0 : Fin 1) = (5 : ℤ) := rfl
theorem hab : ∀ c, aV c ≤ bV c := by intro c; fin_cases c <;> norm_num [aV, bV]
theorem hd0 : ∀ c, 0 < dV c := by intro c; fin_cases c <;> norm_num [dV]
theorem hdP : ∀ c, dV c ≤ 1 / (4 * (12 : ℝ)) := by intro c; fin_cases c <;> norm_num [dV]
theorem haP : ∀ c, dV c < aV c := by intro c; fin_cases c <;> norm_num [dV, aV]
theorem hT : ∀ c, bV c + dV c ≤ TV c := by intro c; fin_cases c <;> norm_num [bV, dV, TV]
theorem hZ : ∀ c, ((12 : ℝ) + 1) * TV c + 1 ≤ (ZV c : ℝ) := by intro c; fin_cases c <;> norm_num [TV, ZV]
theorem hE (ε : ℝ) (hε : ε ≤ (1 / 9216 : ℝ)) : ∀ c, 8 * ((ZV c : ℝ) + 1) * ε ≤ dV c := by
  intro c; fin_cases c <;> norm_num [ZV, dV] <;> linarith
theorem hcls : ∀ c i, ∀ z : ℤ, 0 ≤ z → z ≤ ZV c →
    ((z : ℝ) + 1 / 8) / pr i ≤ aV c - dV c ∨ bV c + dV c ≤ ((z : ℝ) - 1 / 8) / pr i ∨
      ((z : ℝ) + 1 / 8) / pr i = aV c ∨ ((z : ℝ) - 1 / 8) / pr i = bV c := by
  intro c i z h0 h1
  fin_cases c <;> fin_cases i <;> simp [ZV] at h1 <;> interval_cases z <;> norm_num [pr, aV, bV, dV]
theorem hEXne : ∀ c, (EXs c).Nonempty := by
  intro c
  fin_cases c
  · exact ⟨(1, 1), by simp [EXs, ZV, pr, aV] <;> norm_num⟩
theorem hENne : ∀ c, (ENs c).Nonempty := by
  intro c
  fin_cases c
  · exact ⟨(4, 2), by simp [ENs, ZV, pr, bV] <;> norm_num⟩
theorem hEXdef : ∀ c, ∀ q : Fin 7 × ℤ, q ∈ EXs c ↔ 0 ≤ q.2 ∧ q.2 ≤ ZV c ∧ ((q.2 : ℝ) + 1 / 8) / pr q.1 = aV c := by
  intro c q
  simp only [EXs, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, Finset.mem_Icc, true_and]
  tauto
theorem hENdef : ∀ c, ∀ q : Fin 7 × ℤ, q ∈ ENs c ↔ 0 ≤ q.2 ∧ q.2 ≤ ZV c ∧ ((q.2 : ℝ) - 1 / 8) / pr q.1 = bV c := by
  intro c q
  simp only [ENs, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, Finset.mem_Icc, true_and]
  tauto
theorem hsepL : ∀ c c' : Fin 1, c < c' → bV c + dV c / 2 < aV c' - dV c' / 2 := by
  intro c c' h
  fin_cases c <;> fin_cases c' <;> simp at h ⊢ <;> norm_num [aV, bV, dV]
theorem hHL : ∀ c, bV c + dV c / 2 ≤ HV := by intro c; fin_cases c <;> norm_num [bV, dV, HV]

theorem gap0 (x : Fin 7 → ℝ) (ε : ℝ) (hdev : ∀ i, |x i - pr i| ≤ ε) (hεH : ε * HV ≤ (1 / 512 : ℝ) / 2) (t : ℝ) (h0 : 0 ≤ t)
    (hHt : t ≤ HV) (h1 : (0 : ℝ) ≤ t) (h2 : t ≤ (427 / 1920 : ℝ)) (hlon : ∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)) : False := by
  rcases le_total t (63 / 512 : ℝ) with hs0 | hs0
  · exact zone_kill_gen pr x ε HV (1 / 512 : ℝ) hp1 hdev hεH (by norm_num) (0 : Fin 7) 0 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (0 : Fin 7))
  rcases le_total t (71 / 512 : ℝ) with hs1 | hs1
  · exact zone_kill_gen pr x ε HV (1 / 512 : ℝ) hp1 hdev hεH (by norm_num) (4 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (4 : Fin 7))
  rcases le_total t (569 / 3584 : ℝ) with hs2 | hs2
  · exact zone_kill_gen pr x ε HV (1 / 512 : ℝ) hp1 hdev hεH (by norm_num) (3 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (3 : Fin 7))
  rcases le_total t (95 / 512 : ℝ) with hs3 | hs3
  · exact zone_kill_gen pr x ε HV (1 / 512 : ℝ) hp1 hdev hεH (by norm_num) (2 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (2 : Fin 7))
  exact zone_kill_gen pr x ε HV (1 / 512 : ℝ) hp1 hdev hεH (by norm_num) (1 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (1 : Fin 7))
theorem cov (x : Fin 7 → ℝ) (ε : ℝ) (hε : ε ≤ (1 / 9216 : ℝ)) (hdev : ∀ i, |x i - pr i| ≤ ε) :
    ∀ t : ℝ, 0 < t → t ≤ HV → (∀ c, ¬ (aV c - dV c / 2 ≤ t ∧ t ≤ bV c + dV c / 2)) →
      ¬ (∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)) := by
  intro t h0 hHt hnone hlon
  have hεH : ε * HV ≤ (1 / 512 : ℝ) / 2 := by
    have hε0 : 0 ≤ ε := le_trans (abs_nonneg _) (hdev 0)
    have : ε * HV ≤ (1 / 9216 : ℝ) * HV := mul_le_mul_of_nonneg_right hε (by norm_num [HV])
    have h2 : (1 / 9216 : ℝ) * HV ≤ (1 / 512 : ℝ) / 2 := by norm_num [HV]
    linarith
  have n0 := hnone (0 : Fin 1)
  rw [aV_0, bV_0, dV_0] at n0
  rcases lt_or_ge t (427 / 1920 : ℝ) with c0 | c0
  · exact gap0 x ε hdev hεH t h0.le hHt h0.le (by linarith) hlon
  have d0 : (91 / 384 : ℝ) < t := by
    by_contra hc; push Not at hc; exact n0 ⟨by linarith, by linarith⟩
  have hHv : HV = (91 / 384 : ℝ) := rfl
  exact absurd (by linarith : t ≤ (91 / 384 : ℝ)) (not_le.2 d0)

theorem inst (x : Fin 7 → ℝ) (ε : ℝ) (hε : ε ≤ (1 / 9216 : ℝ)) (hdev : ∀ i, |x i - pr i| ≤ ε) :
    ∃ c₀ : Fin 1, Alive (mxOf x EXs hEXne) (mnOf x ENs hENne) c₀ ∧
      (∀ c, c < c₀ → ¬ Alive (mxOf x EXs hEXne) (mnOf x ENs hENne) c) ∧
      IsLeast {t : ℝ | 0 < t ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)} (mxOf x EXs hEXne c₀) :=
  landing_cert 1 (12 : ℝ) (by norm_num) pr x hp ε hdev aV bV dV TV ZV hab hd0 hdP haP hT hZ (hE ε hε) hcls EXs ENs hEXne hENne
    hEXdef hENdef hsepL HV hHL (cov x ε hε hdev) (0 : Fin 1) (by rw [dV_0, bV_0, aV_0]; norm_num)

noncomputable def sv : Fin 8 → ℝ := ![(1 : ℝ), (2 : ℝ), (6 : ℝ), (7 : ℝ), (8 : ℝ), (9 : ℝ), (11 : ℝ), (13 : ℝ)]
def sg : Fin 7 → Fin 8 := ![1, 2, 3, 4, 5, 6, 7]

theorem sv_0 : sv (0 : Fin 8) = (1 : ℝ) := rfl
theorem sv_1 : sv (1 : Fin 8) = (2 : ℝ) := rfl
theorem sv_2 : sv (2 : Fin 8) = (6 : ℝ) := rfl
theorem sv_3 : sv (3 : Fin 8) = (7 : ℝ) := rfl
theorem sv_4 : sv (4 : Fin 8) = (8 : ℝ) := rfl
theorem sv_5 : sv (5 : Fin 8) = (9 : ℝ) := rfl
theorem sv_6 : sv (6 : Fin 8) = (11 : ℝ) := rfl
theorem sv_7 : sv (7 : Fin 8) = (13 : ℝ) := rfl
theorem sg_0 : sg (0 : Fin 7) = (1 : Fin 8) := rfl
theorem sg_1 : sg (1 : Fin 7) = (2 : Fin 8) := rfl
theorem sg_2 : sg (2 : Fin 7) = (3 : Fin 8) := rfl
theorem sg_3 : sg (3 : Fin 7) = (4 : Fin 8) := rfl
theorem sg_4 : sg (4 : Fin 7) = (5 : Fin 8) := rfl
theorem sg_5 : sg (5 : Fin 7) = (6 : Fin 8) := rfl
theorem sg_6 : sg (6 : Fin 7) = (7 : Fin 8) := rfl

theorem inst_arr (v : Fin 8 → ℝ) (η : ℝ) (hη : η ≤ (1 / 18432 : ℝ)) (hv : ∀ j, |v j - sv j| ≤ η) :
    ∃ c₀ : Fin 1, Alive (mxOf (fun i => |v (sg i) - v (0 : Fin 8)|) EXs hEXne) (mnOf (fun i => |v (sg i) - v (0 : Fin 8)|) ENs hENne) c₀ ∧
      (∀ c, c < c₀ → ¬ Alive (mxOf (fun i => |v (sg i) - v (0 : Fin 8)|) EXs hEXne) (mnOf (fun i => |v (sg i) - v (0 : Fin 8)|) ENs hENne) c) ∧
      IsLeast {t : ℝ | 0 < t ∧ IsolatedAt v (0 : Fin 8) t} (mxOf (fun i => |v (sg i) - v (0 : Fin 8)|) EXs hEXne c₀) := by
  have hσk : ∀ i, sg i ≠ (0 : Fin 8) := by decide
  have hσ : ∀ j : Fin 8, j ≠ (0 : Fin 8) → ∃ i, sg i = j := by decide
  have hpr : ∀ i, pr i = |sv (sg i) - sv (0 : Fin 8)| := by
    intro i; rcases fin7_cases i with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6, sv_0, sv_1, sv_2, sv_3, sv_4, sv_5, sv_6, sv_7, sg_0, sg_1, sg_2, sg_3, sg_4, sg_5, sg_6]
  have hdev : ∀ i, |(|v (sg i) - v (0 : Fin 8)| - pr i)| ≤ 2 * η := by
    intro i; rw [hpr i]; exact reading_dev v sv η hv (sg i) (0 : Fin 8)
  obtain ⟨c₀, hal, hbf, hT0⟩ := inst (fun i => |v (sg i) - v (0 : Fin 8)|) (2 * η) (by linarith) hdev
  have hset : {t : ℝ | 0 < t ∧ IsolatedAt v (0 : Fin 8) t} =
      {t : ℝ | 0 < t ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (|v (sg i) - v (0 : Fin 8)| * t)} := by
    ext t; simp only [Set.mem_setOf_eq]; rw [iso_iff_readings v (0 : Fin 8) sg hσk hσ t]
  rw [hset]; exact ⟨c₀, hal, hbf, hT0⟩

#print axioms inst_arr

end Fresh.CertRR.R11200



/-!
# Landing certificate `CertRR.R11208`: speeds (1, 2, 6, 7, 8, 9, 11, 14), subject index 0

Generated 2026-10-24 by `experiments/n8/cert_gen_v1.py` (exact Fractions).  Baseline readings [1, 5, 6, 7, 8, 10, 13].  Components up to the first wide one: 1.
Radius: speeds within `η ≤ 1/25088` of the baseline speeds, giving `ε = 2η ≤ 1/12544`.  Covering margin `μ = 1/1024`.
`hcov` is **[PROVISIONAL: covering]**, supporting the claim that the first lonely instant of this subject is the largest exit of the first alive component.
Result `inst_arr`: for such `v`, the subject has a first isolation (a least element over all `t > 0`).  Grades: [L].
-/

open Classical

namespace Fresh.CertRR.R11208

open Fresh Fresh.LandingCert Fresh.LandingRule

noncomputable def pr : Fin 7 → ℝ := ![(1 : ℝ), (5 : ℝ), (6 : ℝ), (7 : ℝ), (8 : ℝ), (10 : ℝ), (13 : ℝ)]
noncomputable def aV : Fin 1 → ℝ := ![(17 / 64 : ℝ)]
noncomputable def bV : Fin 1 → ℝ := ![(15 / 56 : ℝ)]
noncomputable def dV : Fin 1 → ℝ := ![(1 / 224 : ℝ)]
noncomputable def TV : Fin 1 → ℝ := ![(61 / 224 : ℝ)]
def ZV : Fin 1 → ℤ := ![6]
noncomputable def HV : ℝ := (121 / 448 : ℝ)
noncomputable def EXs (c : Fin 1) : Finset (Fin 7 × ℤ) :=
  (Finset.univ ×ˢ Finset.Icc 0 (ZV c)).filter (fun q => ((q.2 : ℝ) + 1 / 8) / pr q.1 = aV c)
noncomputable def ENs (c : Fin 1) : Finset (Fin 7 × ℤ) :=
  (Finset.univ ×ˢ Finset.Icc 0 (ZV c)).filter (fun q => ((q.2 : ℝ) - 1 / 8) / pr q.1 = bV c)

theorem hp : ∀ i, 1 ≤ pr i ∧ pr i ≤ (13 : ℝ) := by intro i; fin_cases i <;> norm_num [pr]
theorem hp1 : ∀ i, 1 ≤ pr i := fun i => (hp i).1
theorem pr_0 : pr (0 : Fin 7) = (1 : ℝ) := rfl
theorem pr_1 : pr (1 : Fin 7) = (5 : ℝ) := rfl
theorem pr_2 : pr (2 : Fin 7) = (6 : ℝ) := rfl
theorem pr_3 : pr (3 : Fin 7) = (7 : ℝ) := rfl
theorem pr_4 : pr (4 : Fin 7) = (8 : ℝ) := rfl
theorem pr_5 : pr (5 : Fin 7) = (10 : ℝ) := rfl
theorem pr_6 : pr (6 : Fin 7) = (13 : ℝ) := rfl
theorem aV_0 : aV (0 : Fin 1) = (17 / 64 : ℝ) := rfl
theorem bV_0 : bV (0 : Fin 1) = (15 / 56 : ℝ) := rfl
theorem dV_0 : dV (0 : Fin 1) = (1 / 224 : ℝ) := rfl
theorem TV_0 : TV (0 : Fin 1) = (61 / 224 : ℝ) := rfl
theorem ZV_0 : ZV (0 : Fin 1) = (6 : ℤ) := rfl
theorem hab : ∀ c, aV c ≤ bV c := by intro c; fin_cases c <;> norm_num [aV, bV]
theorem hd0 : ∀ c, 0 < dV c := by intro c; fin_cases c <;> norm_num [dV]
theorem hdP : ∀ c, dV c ≤ 1 / (4 * (13 : ℝ)) := by intro c; fin_cases c <;> norm_num [dV]
theorem haP : ∀ c, dV c < aV c := by intro c; fin_cases c <;> norm_num [dV, aV]
theorem hT : ∀ c, bV c + dV c ≤ TV c := by intro c; fin_cases c <;> norm_num [bV, dV, TV]
theorem hZ : ∀ c, ((13 : ℝ) + 1) * TV c + 1 ≤ (ZV c : ℝ) := by intro c; fin_cases c <;> norm_num [TV, ZV]
theorem hE (ε : ℝ) (hε : ε ≤ (1 / 12544 : ℝ)) : ∀ c, 8 * ((ZV c : ℝ) + 1) * ε ≤ dV c := by
  intro c; fin_cases c <;> norm_num [ZV, dV] <;> linarith
theorem hcls : ∀ c i, ∀ z : ℤ, 0 ≤ z → z ≤ ZV c →
    ((z : ℝ) + 1 / 8) / pr i ≤ aV c - dV c ∨ bV c + dV c ≤ ((z : ℝ) - 1 / 8) / pr i ∨
      ((z : ℝ) + 1 / 8) / pr i = aV c ∨ ((z : ℝ) - 1 / 8) / pr i = bV c := by
  intro c i z h0 h1
  fin_cases c <;> fin_cases i <;> simp [ZV] at h1 <;> interval_cases z <;> norm_num [pr, aV, bV, dV]
theorem hEXne : ∀ c, (EXs c).Nonempty := by
  intro c
  fin_cases c
  · exact ⟨(4, 2), by simp [EXs, ZV, pr, aV] <;> norm_num⟩
theorem hENne : ∀ c, (ENs c).Nonempty := by
  intro c
  fin_cases c
  · exact ⟨(3, 2), by simp [ENs, ZV, pr, bV] <;> norm_num⟩
theorem hEXdef : ∀ c, ∀ q : Fin 7 × ℤ, q ∈ EXs c ↔ 0 ≤ q.2 ∧ q.2 ≤ ZV c ∧ ((q.2 : ℝ) + 1 / 8) / pr q.1 = aV c := by
  intro c q
  simp only [EXs, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, Finset.mem_Icc, true_and]
  tauto
theorem hENdef : ∀ c, ∀ q : Fin 7 × ℤ, q ∈ ENs c ↔ 0 ≤ q.2 ∧ q.2 ≤ ZV c ∧ ((q.2 : ℝ) - 1 / 8) / pr q.1 = bV c := by
  intro c q
  simp only [ENs, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, Finset.mem_Icc, true_and]
  tauto
theorem hsepL : ∀ c c' : Fin 1, c < c' → bV c + dV c / 2 < aV c' - dV c' / 2 := by
  intro c c' h
  fin_cases c <;> fin_cases c' <;> simp at h ⊢ <;> norm_num [aV, bV, dV]
theorem hHL : ∀ c, bV c + dV c / 2 ≤ HV := by intro c; fin_cases c <;> norm_num [bV, dV, HV]

theorem gap0 (x : Fin 7 → ℝ) (ε : ℝ) (hdev : ∀ i, |x i - pr i| ≤ ε) (hεH : ε * HV ≤ (1 / 1024 : ℝ) / 2) (t : ℝ) (h0 : 0 ≤ t)
    (hHt : t ≤ HV) (h1 : (0 : ℝ) ≤ t) (h2 : t ≤ (59 / 224 : ℝ)) (hlon : ∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)) : False := by
  rcases le_total t (127 / 1024 : ℝ) with hs0 | hs0
  · exact zone_kill_gen pr x ε HV (1 / 1024 : ℝ) hp1 hdev hεH (by norm_num) (0 : Fin 7) 0 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (0 : Fin 7))
  rcases le_total t (143 / 1024 : ℝ) with hs1 | hs1
  · exact zone_kill_gen pr x ε HV (1 / 1024 : ℝ) hp1 hdev hεH (by norm_num) (4 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (4 : Fin 7))
  rcases le_total t (1145 / 7168 : ℝ) with hs2 | hs2
  · exact zone_kill_gen pr x ε HV (1 / 1024 : ℝ) hp1 hdev hεH (by norm_num) (3 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (3 : Fin 7))
  rcases le_total t (191 / 1024 : ℝ) with hs3 | hs3
  · exact zone_kill_gen pr x ε HV (1 / 1024 : ℝ) hp1 hdev hεH (by norm_num) (2 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (2 : Fin 7))
  rcases le_total t (1147 / 5120 : ℝ) with hs4 | hs4
  · exact zone_kill_gen pr x ε HV (1 / 1024 : ℝ) hp1 hdev hεH (by norm_num) (1 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (1 : Fin 7))
  rcases le_total t (3187 / 13312 : ℝ) with hs5 | hs5
  · exact zone_kill_gen pr x ε HV (1 / 1024 : ℝ) hp1 hdev hεH (by norm_num) (6 : Fin 7) 3 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (6 : Fin 7))
  exact zone_kill_gen pr x ε HV (1 / 1024 : ℝ) hp1 hdev hεH (by norm_num) (4 : Fin 7) 2 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (4 : Fin 7))
theorem cov (x : Fin 7 → ℝ) (ε : ℝ) (hε : ε ≤ (1 / 12544 : ℝ)) (hdev : ∀ i, |x i - pr i| ≤ ε) :
    ∀ t : ℝ, 0 < t → t ≤ HV → (∀ c, ¬ (aV c - dV c / 2 ≤ t ∧ t ≤ bV c + dV c / 2)) →
      ¬ (∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)) := by
  intro t h0 hHt hnone hlon
  have hεH : ε * HV ≤ (1 / 1024 : ℝ) / 2 := by
    have hε0 : 0 ≤ ε := le_trans (abs_nonneg _) (hdev 0)
    have : ε * HV ≤ (1 / 12544 : ℝ) * HV := mul_le_mul_of_nonneg_right hε (by norm_num [HV])
    have h2 : (1 / 12544 : ℝ) * HV ≤ (1 / 1024 : ℝ) / 2 := by norm_num [HV]
    linarith
  have n0 := hnone (0 : Fin 1)
  rw [aV_0, bV_0, dV_0] at n0
  rcases lt_or_ge t (59 / 224 : ℝ) with c0 | c0
  · exact gap0 x ε hdev hεH t h0.le hHt h0.le (by linarith) hlon
  have d0 : (121 / 448 : ℝ) < t := by
    by_contra hc; push Not at hc; exact n0 ⟨by linarith, by linarith⟩
  have hHv : HV = (121 / 448 : ℝ) := rfl
  exact absurd (by linarith : t ≤ (121 / 448 : ℝ)) (not_le.2 d0)

theorem inst (x : Fin 7 → ℝ) (ε : ℝ) (hε : ε ≤ (1 / 12544 : ℝ)) (hdev : ∀ i, |x i - pr i| ≤ ε) :
    ∃ c₀ : Fin 1, Alive (mxOf x EXs hEXne) (mnOf x ENs hENne) c₀ ∧
      (∀ c, c < c₀ → ¬ Alive (mxOf x EXs hEXne) (mnOf x ENs hENne) c) ∧
      IsLeast {t : ℝ | 0 < t ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)} (mxOf x EXs hEXne c₀) :=
  landing_cert 1 (13 : ℝ) (by norm_num) pr x hp ε hdev aV bV dV TV ZV hab hd0 hdP haP hT hZ (hE ε hε) hcls EXs ENs hEXne hENne
    hEXdef hENdef hsepL HV hHL (cov x ε hε hdev) (0 : Fin 1) (by rw [dV_0, bV_0, aV_0]; norm_num)

noncomputable def sv : Fin 8 → ℝ := ![(1 : ℝ), (2 : ℝ), (6 : ℝ), (7 : ℝ), (8 : ℝ), (9 : ℝ), (11 : ℝ), (14 : ℝ)]
def sg : Fin 7 → Fin 8 := ![1, 2, 3, 4, 5, 6, 7]

theorem sv_0 : sv (0 : Fin 8) = (1 : ℝ) := rfl
theorem sv_1 : sv (1 : Fin 8) = (2 : ℝ) := rfl
theorem sv_2 : sv (2 : Fin 8) = (6 : ℝ) := rfl
theorem sv_3 : sv (3 : Fin 8) = (7 : ℝ) := rfl
theorem sv_4 : sv (4 : Fin 8) = (8 : ℝ) := rfl
theorem sv_5 : sv (5 : Fin 8) = (9 : ℝ) := rfl
theorem sv_6 : sv (6 : Fin 8) = (11 : ℝ) := rfl
theorem sv_7 : sv (7 : Fin 8) = (14 : ℝ) := rfl
theorem sg_0 : sg (0 : Fin 7) = (1 : Fin 8) := rfl
theorem sg_1 : sg (1 : Fin 7) = (2 : Fin 8) := rfl
theorem sg_2 : sg (2 : Fin 7) = (3 : Fin 8) := rfl
theorem sg_3 : sg (3 : Fin 7) = (4 : Fin 8) := rfl
theorem sg_4 : sg (4 : Fin 7) = (5 : Fin 8) := rfl
theorem sg_5 : sg (5 : Fin 7) = (6 : Fin 8) := rfl
theorem sg_6 : sg (6 : Fin 7) = (7 : Fin 8) := rfl

theorem inst_arr (v : Fin 8 → ℝ) (η : ℝ) (hη : η ≤ (1 / 25088 : ℝ)) (hv : ∀ j, |v j - sv j| ≤ η) :
    ∃ c₀ : Fin 1, Alive (mxOf (fun i => |v (sg i) - v (0 : Fin 8)|) EXs hEXne) (mnOf (fun i => |v (sg i) - v (0 : Fin 8)|) ENs hENne) c₀ ∧
      (∀ c, c < c₀ → ¬ Alive (mxOf (fun i => |v (sg i) - v (0 : Fin 8)|) EXs hEXne) (mnOf (fun i => |v (sg i) - v (0 : Fin 8)|) ENs hENne) c) ∧
      IsLeast {t : ℝ | 0 < t ∧ IsolatedAt v (0 : Fin 8) t} (mxOf (fun i => |v (sg i) - v (0 : Fin 8)|) EXs hEXne c₀) := by
  have hσk : ∀ i, sg i ≠ (0 : Fin 8) := by decide
  have hσ : ∀ j : Fin 8, j ≠ (0 : Fin 8) → ∃ i, sg i = j := by decide
  have hpr : ∀ i, pr i = |sv (sg i) - sv (0 : Fin 8)| := by
    intro i; rcases fin7_cases i with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6, sv_0, sv_1, sv_2, sv_3, sv_4, sv_5, sv_6, sv_7, sg_0, sg_1, sg_2, sg_3, sg_4, sg_5, sg_6]
  have hdev : ∀ i, |(|v (sg i) - v (0 : Fin 8)| - pr i)| ≤ 2 * η := by
    intro i; rw [hpr i]; exact reading_dev v sv η hv (sg i) (0 : Fin 8)
  obtain ⟨c₀, hal, hbf, hT0⟩ := inst (fun i => |v (sg i) - v (0 : Fin 8)|) (2 * η) (by linarith) hdev
  have hset : {t : ℝ | 0 < t ∧ IsolatedAt v (0 : Fin 8) t} =
      {t : ℝ | 0 < t ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (|v (sg i) - v (0 : Fin 8)| * t)} := by
    ext t; simp only [Set.mem_setOf_eq]; rw [iso_iff_readings v (0 : Fin 8) sg hσk hσ t]
  rw [hset]; exact ⟨c₀, hal, hbf, hT0⟩

#print axioms inst_arr

end Fresh.CertRR.R11208



/-!
# Landing certificate `CertRR.R11215`: speeds (1, 2, 6, 7, 8, 9, 11, 14), subject index 7

Generated 2026-10-24 by `experiments/n8/cert_gen_v1.py` (exact Fractions).  Baseline readings [13, 12, 8, 7, 6, 5, 3].  Components up to the first wide one: 1.
Radius: speeds within `η ≤ 1/11412` of the baseline speeds, giving `ε = 2η ≤ 1/5706`.  Covering margin `μ = 1/512`.
`hcov` is **[PROVISIONAL: covering]**, supporting the claim that the first lonely instant of this subject is the largest exit of the first alive component.
Result `inst_arr`: for such `v`, the subject has a first isolation (a least element over all `t > 0`).  Grades: [L].
-/

open Classical

namespace Fresh.CertRR.R11215

open Fresh Fresh.LandingCert Fresh.LandingRule

noncomputable def pr : Fin 7 → ℝ := ![(13 : ℝ), (12 : ℝ), (8 : ℝ), (7 : ℝ), (6 : ℝ), (5 : ℝ), (3 : ℝ)]
noncomputable def aV : Fin 1 → ℝ := ![(1 / 24 : ℝ)]
noncomputable def bV : Fin 1 → ℝ := ![(7 / 104 : ℝ)]
noncomputable def dV : Fin 1 → ℝ := ![(7 / 1248 : ℝ)]
noncomputable def TV : Fin 1 → ℝ := ![(7 / 96 : ℝ)]
def ZV : Fin 1 → ℤ := ![3]
noncomputable def HV : ℝ := (175 / 2496 : ℝ)
noncomputable def EXs (c : Fin 1) : Finset (Fin 7 × ℤ) :=
  (Finset.univ ×ˢ Finset.Icc 0 (ZV c)).filter (fun q => ((q.2 : ℝ) + 1 / 8) / pr q.1 = aV c)
noncomputable def ENs (c : Fin 1) : Finset (Fin 7 × ℤ) :=
  (Finset.univ ×ˢ Finset.Icc 0 (ZV c)).filter (fun q => ((q.2 : ℝ) - 1 / 8) / pr q.1 = bV c)

theorem hp : ∀ i, 1 ≤ pr i ∧ pr i ≤ (13 : ℝ) := by intro i; fin_cases i <;> norm_num [pr]
theorem hp1 : ∀ i, 1 ≤ pr i := fun i => (hp i).1
theorem pr_0 : pr (0 : Fin 7) = (13 : ℝ) := rfl
theorem pr_1 : pr (1 : Fin 7) = (12 : ℝ) := rfl
theorem pr_2 : pr (2 : Fin 7) = (8 : ℝ) := rfl
theorem pr_3 : pr (3 : Fin 7) = (7 : ℝ) := rfl
theorem pr_4 : pr (4 : Fin 7) = (6 : ℝ) := rfl
theorem pr_5 : pr (5 : Fin 7) = (5 : ℝ) := rfl
theorem pr_6 : pr (6 : Fin 7) = (3 : ℝ) := rfl
theorem aV_0 : aV (0 : Fin 1) = (1 / 24 : ℝ) := rfl
theorem bV_0 : bV (0 : Fin 1) = (7 / 104 : ℝ) := rfl
theorem dV_0 : dV (0 : Fin 1) = (7 / 1248 : ℝ) := rfl
theorem TV_0 : TV (0 : Fin 1) = (7 / 96 : ℝ) := rfl
theorem ZV_0 : ZV (0 : Fin 1) = (3 : ℤ) := rfl
theorem hab : ∀ c, aV c ≤ bV c := by intro c; fin_cases c <;> norm_num [aV, bV]
theorem hd0 : ∀ c, 0 < dV c := by intro c; fin_cases c <;> norm_num [dV]
theorem hdP : ∀ c, dV c ≤ 1 / (4 * (13 : ℝ)) := by intro c; fin_cases c <;> norm_num [dV]
theorem haP : ∀ c, dV c < aV c := by intro c; fin_cases c <;> norm_num [dV, aV]
theorem hT : ∀ c, bV c + dV c ≤ TV c := by intro c; fin_cases c <;> norm_num [bV, dV, TV]
theorem hZ : ∀ c, ((13 : ℝ) + 1) * TV c + 1 ≤ (ZV c : ℝ) := by intro c; fin_cases c <;> norm_num [TV, ZV]
theorem hE (ε : ℝ) (hε : ε ≤ (1 / 5706 : ℝ)) : ∀ c, 8 * ((ZV c : ℝ) + 1) * ε ≤ dV c := by
  intro c; fin_cases c <;> norm_num [ZV, dV] <;> linarith
theorem hcls : ∀ c i, ∀ z : ℤ, 0 ≤ z → z ≤ ZV c →
    ((z : ℝ) + 1 / 8) / pr i ≤ aV c - dV c ∨ bV c + dV c ≤ ((z : ℝ) - 1 / 8) / pr i ∨
      ((z : ℝ) + 1 / 8) / pr i = aV c ∨ ((z : ℝ) - 1 / 8) / pr i = bV c := by
  intro c i z h0 h1
  fin_cases c <;> fin_cases i <;> simp [ZV] at h1 <;> interval_cases z <;> norm_num [pr, aV, bV, dV]
theorem hEXne : ∀ c, (EXs c).Nonempty := by
  intro c
  fin_cases c
  · exact ⟨(6, 0), by simp [EXs, ZV, pr, aV] <;> norm_num⟩
theorem hENne : ∀ c, (ENs c).Nonempty := by
  intro c
  fin_cases c
  · exact ⟨(0, 1), by simp [ENs, ZV, pr, bV] <;> norm_num⟩
theorem hEXdef : ∀ c, ∀ q : Fin 7 × ℤ, q ∈ EXs c ↔ 0 ≤ q.2 ∧ q.2 ≤ ZV c ∧ ((q.2 : ℝ) + 1 / 8) / pr q.1 = aV c := by
  intro c q
  simp only [EXs, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, Finset.mem_Icc, true_and]
  tauto
theorem hENdef : ∀ c, ∀ q : Fin 7 × ℤ, q ∈ ENs c ↔ 0 ≤ q.2 ∧ q.2 ≤ ZV c ∧ ((q.2 : ℝ) - 1 / 8) / pr q.1 = bV c := by
  intro c q
  simp only [ENs, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, Finset.mem_Icc, true_and]
  tauto
theorem hsepL : ∀ c c' : Fin 1, c < c' → bV c + dV c / 2 < aV c' - dV c' / 2 := by
  intro c c' h
  fin_cases c <;> fin_cases c' <;> simp at h ⊢ <;> norm_num [aV, bV, dV]
theorem hHL : ∀ c, bV c + dV c / 2 ≤ HV := by intro c; fin_cases c <;> norm_num [bV, dV, HV]

theorem gap0 (x : Fin 7 → ℝ) (ε : ℝ) (hdev : ∀ i, |x i - pr i| ≤ ε) (hεH : ε * HV ≤ (1 / 512 : ℝ) / 2) (t : ℝ) (h0 : 0 ≤ t)
    (hHt : t ≤ HV) (h1 : (0 : ℝ) ≤ t) (h2 : t ≤ (97 / 2496 : ℝ)) (hlon : ∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)) : False := by
  exact zone_kill_gen pr x ε HV (1 / 512 : ℝ) hp1 hdev hεH (by norm_num) (6 : Fin 7) 0 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (6 : Fin 7))
theorem cov (x : Fin 7 → ℝ) (ε : ℝ) (hε : ε ≤ (1 / 5706 : ℝ)) (hdev : ∀ i, |x i - pr i| ≤ ε) :
    ∀ t : ℝ, 0 < t → t ≤ HV → (∀ c, ¬ (aV c - dV c / 2 ≤ t ∧ t ≤ bV c + dV c / 2)) →
      ¬ (∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)) := by
  intro t h0 hHt hnone hlon
  have hεH : ε * HV ≤ (1 / 512 : ℝ) / 2 := by
    have hε0 : 0 ≤ ε := le_trans (abs_nonneg _) (hdev 0)
    have : ε * HV ≤ (1 / 5706 : ℝ) * HV := mul_le_mul_of_nonneg_right hε (by norm_num [HV])
    have h2 : (1 / 5706 : ℝ) * HV ≤ (1 / 512 : ℝ) / 2 := by norm_num [HV]
    linarith
  have n0 := hnone (0 : Fin 1)
  rw [aV_0, bV_0, dV_0] at n0
  rcases lt_or_ge t (97 / 2496 : ℝ) with c0 | c0
  · exact gap0 x ε hdev hεH t h0.le hHt h0.le (by linarith) hlon
  have d0 : (175 / 2496 : ℝ) < t := by
    by_contra hc; push Not at hc; exact n0 ⟨by linarith, by linarith⟩
  have hHv : HV = (175 / 2496 : ℝ) := rfl
  exact absurd (by linarith : t ≤ (175 / 2496 : ℝ)) (not_le.2 d0)

theorem inst (x : Fin 7 → ℝ) (ε : ℝ) (hε : ε ≤ (1 / 5706 : ℝ)) (hdev : ∀ i, |x i - pr i| ≤ ε) :
    ∃ c₀ : Fin 1, Alive (mxOf x EXs hEXne) (mnOf x ENs hENne) c₀ ∧
      (∀ c, c < c₀ → ¬ Alive (mxOf x EXs hEXne) (mnOf x ENs hENne) c) ∧
      IsLeast {t : ℝ | 0 < t ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)} (mxOf x EXs hEXne c₀) :=
  landing_cert 1 (13 : ℝ) (by norm_num) pr x hp ε hdev aV bV dV TV ZV hab hd0 hdP haP hT hZ (hE ε hε) hcls EXs ENs hEXne hENne
    hEXdef hENdef hsepL HV hHL (cov x ε hε hdev) (0 : Fin 1) (by rw [dV_0, bV_0, aV_0]; norm_num)

noncomputable def sv : Fin 8 → ℝ := ![(1 : ℝ), (2 : ℝ), (6 : ℝ), (7 : ℝ), (8 : ℝ), (9 : ℝ), (11 : ℝ), (14 : ℝ)]
def sg : Fin 7 → Fin 8 := ![0, 1, 2, 3, 4, 5, 6]

theorem sv_0 : sv (0 : Fin 8) = (1 : ℝ) := rfl
theorem sv_1 : sv (1 : Fin 8) = (2 : ℝ) := rfl
theorem sv_2 : sv (2 : Fin 8) = (6 : ℝ) := rfl
theorem sv_3 : sv (3 : Fin 8) = (7 : ℝ) := rfl
theorem sv_4 : sv (4 : Fin 8) = (8 : ℝ) := rfl
theorem sv_5 : sv (5 : Fin 8) = (9 : ℝ) := rfl
theorem sv_6 : sv (6 : Fin 8) = (11 : ℝ) := rfl
theorem sv_7 : sv (7 : Fin 8) = (14 : ℝ) := rfl
theorem sg_0 : sg (0 : Fin 7) = (0 : Fin 8) := rfl
theorem sg_1 : sg (1 : Fin 7) = (1 : Fin 8) := rfl
theorem sg_2 : sg (2 : Fin 7) = (2 : Fin 8) := rfl
theorem sg_3 : sg (3 : Fin 7) = (3 : Fin 8) := rfl
theorem sg_4 : sg (4 : Fin 7) = (4 : Fin 8) := rfl
theorem sg_5 : sg (5 : Fin 7) = (5 : Fin 8) := rfl
theorem sg_6 : sg (6 : Fin 7) = (6 : Fin 8) := rfl

theorem inst_arr (v : Fin 8 → ℝ) (η : ℝ) (hη : η ≤ (1 / 11412 : ℝ)) (hv : ∀ j, |v j - sv j| ≤ η) :
    ∃ c₀ : Fin 1, Alive (mxOf (fun i => |v (sg i) - v (7 : Fin 8)|) EXs hEXne) (mnOf (fun i => |v (sg i) - v (7 : Fin 8)|) ENs hENne) c₀ ∧
      (∀ c, c < c₀ → ¬ Alive (mxOf (fun i => |v (sg i) - v (7 : Fin 8)|) EXs hEXne) (mnOf (fun i => |v (sg i) - v (7 : Fin 8)|) ENs hENne) c) ∧
      IsLeast {t : ℝ | 0 < t ∧ IsolatedAt v (7 : Fin 8) t} (mxOf (fun i => |v (sg i) - v (7 : Fin 8)|) EXs hEXne c₀) := by
  have hσk : ∀ i, sg i ≠ (7 : Fin 8) := by decide
  have hσ : ∀ j : Fin 8, j ≠ (7 : Fin 8) → ∃ i, sg i = j := by decide
  have hpr : ∀ i, pr i = |sv (sg i) - sv (7 : Fin 8)| := by
    intro i; rcases fin7_cases i with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6, sv_0, sv_1, sv_2, sv_3, sv_4, sv_5, sv_6, sv_7, sg_0, sg_1, sg_2, sg_3, sg_4, sg_5, sg_6]
  have hdev : ∀ i, |(|v (sg i) - v (7 : Fin 8)| - pr i)| ≤ 2 * η := by
    intro i; rw [hpr i]; exact reading_dev v sv η hv (sg i) (7 : Fin 8)
  obtain ⟨c₀, hal, hbf, hT0⟩ := inst (fun i => |v (sg i) - v (7 : Fin 8)|) (2 * η) (by linarith) hdev
  have hset : {t : ℝ | 0 < t ∧ IsolatedAt v (7 : Fin 8) t} =
      {t : ℝ | 0 < t ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (|v (sg i) - v (7 : Fin 8)| * t)} := by
    ext t; simp only [Set.mem_setOf_eq]; rw [iso_iff_readings v (7 : Fin 8) sg hσk hσ t]
  rw [hset]; exact ⟨c₀, hal, hbf, hT0⟩

#print axioms inst_arr

end Fresh.CertRR.R11215



/-!
# Landing certificate `CertRR.R11216`: speeds (1, 2, 6, 7, 8, 9, 11, 15), subject index 0

Generated 2026-10-24 by `experiments/n8/cert_gen_v1.py` (exact Fractions).  Baseline readings [1, 5, 6, 7, 8, 10, 14].  Components up to the first wide one: 1.
Radius: speeds within `η ≤ 1/53760` of the baseline speeds, giving `ε = 2η ≤ 1/26880`.  Covering margin `μ = 1/2048`.
`hcov` is **[PROVISIONAL: covering]**, supporting the claim that the first lonely instant of this subject is the largest exit of the first alive component.
Result `inst_arr`: for such `v`, the subject has a first isolation (a least element over all `t > 0`).  Grades: [L].
-/

open Classical

namespace Fresh.CertRR.R11216

open Fresh Fresh.LandingCert Fresh.LandingRule

noncomputable def pr : Fin 7 → ℝ := ![(1 : ℝ), (5 : ℝ), (6 : ℝ), (7 : ℝ), (8 : ℝ), (10 : ℝ), (14 : ℝ)]
noncomputable def aV : Fin 1 → ℝ := ![(9 / 40 : ℝ)]
noncomputable def bV : Fin 1 → ℝ := ![(15 / 64 : ℝ)]
noncomputable def dV : Fin 1 → ℝ := ![(1 / 560 : ℝ)]
noncomputable def TV : Fin 1 → ℝ := ![(529 / 2240 : ℝ)]
def ZV : Fin 1 → ℤ := ![5]
noncomputable def HV : ℝ := (527 / 2240 : ℝ)
noncomputable def EXs (c : Fin 1) : Finset (Fin 7 × ℤ) :=
  (Finset.univ ×ˢ Finset.Icc 0 (ZV c)).filter (fun q => ((q.2 : ℝ) + 1 / 8) / pr q.1 = aV c)
noncomputable def ENs (c : Fin 1) : Finset (Fin 7 × ℤ) :=
  (Finset.univ ×ˢ Finset.Icc 0 (ZV c)).filter (fun q => ((q.2 : ℝ) - 1 / 8) / pr q.1 = bV c)

theorem hp : ∀ i, 1 ≤ pr i ∧ pr i ≤ (14 : ℝ) := by intro i; fin_cases i <;> norm_num [pr]
theorem hp1 : ∀ i, 1 ≤ pr i := fun i => (hp i).1
theorem pr_0 : pr (0 : Fin 7) = (1 : ℝ) := rfl
theorem pr_1 : pr (1 : Fin 7) = (5 : ℝ) := rfl
theorem pr_2 : pr (2 : Fin 7) = (6 : ℝ) := rfl
theorem pr_3 : pr (3 : Fin 7) = (7 : ℝ) := rfl
theorem pr_4 : pr (4 : Fin 7) = (8 : ℝ) := rfl
theorem pr_5 : pr (5 : Fin 7) = (10 : ℝ) := rfl
theorem pr_6 : pr (6 : Fin 7) = (14 : ℝ) := rfl
theorem aV_0 : aV (0 : Fin 1) = (9 / 40 : ℝ) := rfl
theorem bV_0 : bV (0 : Fin 1) = (15 / 64 : ℝ) := rfl
theorem dV_0 : dV (0 : Fin 1) = (1 / 560 : ℝ) := rfl
theorem TV_0 : TV (0 : Fin 1) = (529 / 2240 : ℝ) := rfl
theorem ZV_0 : ZV (0 : Fin 1) = (5 : ℤ) := rfl
theorem hab : ∀ c, aV c ≤ bV c := by intro c; fin_cases c <;> norm_num [aV, bV]
theorem hd0 : ∀ c, 0 < dV c := by intro c; fin_cases c <;> norm_num [dV]
theorem hdP : ∀ c, dV c ≤ 1 / (4 * (14 : ℝ)) := by intro c; fin_cases c <;> norm_num [dV]
theorem haP : ∀ c, dV c < aV c := by intro c; fin_cases c <;> norm_num [dV, aV]
theorem hT : ∀ c, bV c + dV c ≤ TV c := by intro c; fin_cases c <;> norm_num [bV, dV, TV]
theorem hZ : ∀ c, ((14 : ℝ) + 1) * TV c + 1 ≤ (ZV c : ℝ) := by intro c; fin_cases c <;> norm_num [TV, ZV]
theorem hE (ε : ℝ) (hε : ε ≤ (1 / 26880 : ℝ)) : ∀ c, 8 * ((ZV c : ℝ) + 1) * ε ≤ dV c := by
  intro c; fin_cases c <;> norm_num [ZV, dV] <;> linarith
theorem hcls : ∀ c i, ∀ z : ℤ, 0 ≤ z → z ≤ ZV c →
    ((z : ℝ) + 1 / 8) / pr i ≤ aV c - dV c ∨ bV c + dV c ≤ ((z : ℝ) - 1 / 8) / pr i ∨
      ((z : ℝ) + 1 / 8) / pr i = aV c ∨ ((z : ℝ) - 1 / 8) / pr i = bV c := by
  intro c i z h0 h1
  fin_cases c <;> fin_cases i <;> simp [ZV] at h1 <;> interval_cases z <;> norm_num [pr, aV, bV, dV]
theorem hEXne : ∀ c, (EXs c).Nonempty := by
  intro c
  fin_cases c
  · exact ⟨(1, 1), by simp [EXs, ZV, pr, aV] <;> norm_num⟩
theorem hENne : ∀ c, (ENs c).Nonempty := by
  intro c
  fin_cases c
  · exact ⟨(4, 2), by simp [ENs, ZV, pr, bV] <;> norm_num⟩
theorem hEXdef : ∀ c, ∀ q : Fin 7 × ℤ, q ∈ EXs c ↔ 0 ≤ q.2 ∧ q.2 ≤ ZV c ∧ ((q.2 : ℝ) + 1 / 8) / pr q.1 = aV c := by
  intro c q
  simp only [EXs, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, Finset.mem_Icc, true_and]
  tauto
theorem hENdef : ∀ c, ∀ q : Fin 7 × ℤ, q ∈ ENs c ↔ 0 ≤ q.2 ∧ q.2 ≤ ZV c ∧ ((q.2 : ℝ) - 1 / 8) / pr q.1 = bV c := by
  intro c q
  simp only [ENs, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, Finset.mem_Icc, true_and]
  tauto
theorem hsepL : ∀ c c' : Fin 1, c < c' → bV c + dV c / 2 < aV c' - dV c' / 2 := by
  intro c c' h
  fin_cases c <;> fin_cases c' <;> simp at h ⊢ <;> norm_num [aV, bV, dV]
theorem hHL : ∀ c, bV c + dV c / 2 ≤ HV := by intro c; fin_cases c <;> norm_num [bV, dV, HV]

theorem gap0 (x : Fin 7 → ℝ) (ε : ℝ) (hdev : ∀ i, |x i - pr i| ≤ ε) (hεH : ε * HV ≤ (1 / 2048 : ℝ) / 2) (t : ℝ) (h0 : 0 ≤ t)
    (hHt : t ≤ HV) (h1 : (0 : ℝ) ≤ t) (h2 : t ≤ (251 / 1120 : ℝ)) (hlon : ∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)) : False := by
  rcases le_total t (255 / 2048 : ℝ) with hs0 | hs0
  · exact zone_kill_gen pr x ε HV (1 / 2048 : ℝ) hp1 hdev hεH (by norm_num) (0 : Fin 7) 0 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (0 : Fin 7))
  rcases le_total t (287 / 2048 : ℝ) with hs1 | hs1
  · exact zone_kill_gen pr x ε HV (1 / 2048 : ℝ) hp1 hdev hεH (by norm_num) (4 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (4 : Fin 7))
  rcases le_total t (2297 / 14336 : ℝ) with hs2 | hs2
  · exact zone_kill_gen pr x ε HV (1 / 2048 : ℝ) hp1 hdev hεH (by norm_num) (3 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (3 : Fin 7))
  rcases le_total t (383 / 2048 : ℝ) with hs3 | hs3
  · exact zone_kill_gen pr x ε HV (1 / 2048 : ℝ) hp1 hdev hεH (by norm_num) (2 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (2 : Fin 7))
  exact zone_kill_gen pr x ε HV (1 / 2048 : ℝ) hp1 hdev hεH (by norm_num) (1 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (1 : Fin 7))
theorem cov (x : Fin 7 → ℝ) (ε : ℝ) (hε : ε ≤ (1 / 26880 : ℝ)) (hdev : ∀ i, |x i - pr i| ≤ ε) :
    ∀ t : ℝ, 0 < t → t ≤ HV → (∀ c, ¬ (aV c - dV c / 2 ≤ t ∧ t ≤ bV c + dV c / 2)) →
      ¬ (∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)) := by
  intro t h0 hHt hnone hlon
  have hεH : ε * HV ≤ (1 / 2048 : ℝ) / 2 := by
    have hε0 : 0 ≤ ε := le_trans (abs_nonneg _) (hdev 0)
    have : ε * HV ≤ (1 / 26880 : ℝ) * HV := mul_le_mul_of_nonneg_right hε (by norm_num [HV])
    have h2 : (1 / 26880 : ℝ) * HV ≤ (1 / 2048 : ℝ) / 2 := by norm_num [HV]
    linarith
  have n0 := hnone (0 : Fin 1)
  rw [aV_0, bV_0, dV_0] at n0
  rcases lt_or_ge t (251 / 1120 : ℝ) with c0 | c0
  · exact gap0 x ε hdev hεH t h0.le hHt h0.le (by linarith) hlon
  have d0 : (527 / 2240 : ℝ) < t := by
    by_contra hc; push Not at hc; exact n0 ⟨by linarith, by linarith⟩
  have hHv : HV = (527 / 2240 : ℝ) := rfl
  exact absurd (by linarith : t ≤ (527 / 2240 : ℝ)) (not_le.2 d0)

theorem inst (x : Fin 7 → ℝ) (ε : ℝ) (hε : ε ≤ (1 / 26880 : ℝ)) (hdev : ∀ i, |x i - pr i| ≤ ε) :
    ∃ c₀ : Fin 1, Alive (mxOf x EXs hEXne) (mnOf x ENs hENne) c₀ ∧
      (∀ c, c < c₀ → ¬ Alive (mxOf x EXs hEXne) (mnOf x ENs hENne) c) ∧
      IsLeast {t : ℝ | 0 < t ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)} (mxOf x EXs hEXne c₀) :=
  landing_cert 1 (14 : ℝ) (by norm_num) pr x hp ε hdev aV bV dV TV ZV hab hd0 hdP haP hT hZ (hE ε hε) hcls EXs ENs hEXne hENne
    hEXdef hENdef hsepL HV hHL (cov x ε hε hdev) (0 : Fin 1) (by rw [dV_0, bV_0, aV_0]; norm_num)

noncomputable def sv : Fin 8 → ℝ := ![(1 : ℝ), (2 : ℝ), (6 : ℝ), (7 : ℝ), (8 : ℝ), (9 : ℝ), (11 : ℝ), (15 : ℝ)]
def sg : Fin 7 → Fin 8 := ![1, 2, 3, 4, 5, 6, 7]

theorem sv_0 : sv (0 : Fin 8) = (1 : ℝ) := rfl
theorem sv_1 : sv (1 : Fin 8) = (2 : ℝ) := rfl
theorem sv_2 : sv (2 : Fin 8) = (6 : ℝ) := rfl
theorem sv_3 : sv (3 : Fin 8) = (7 : ℝ) := rfl
theorem sv_4 : sv (4 : Fin 8) = (8 : ℝ) := rfl
theorem sv_5 : sv (5 : Fin 8) = (9 : ℝ) := rfl
theorem sv_6 : sv (6 : Fin 8) = (11 : ℝ) := rfl
theorem sv_7 : sv (7 : Fin 8) = (15 : ℝ) := rfl
theorem sg_0 : sg (0 : Fin 7) = (1 : Fin 8) := rfl
theorem sg_1 : sg (1 : Fin 7) = (2 : Fin 8) := rfl
theorem sg_2 : sg (2 : Fin 7) = (3 : Fin 8) := rfl
theorem sg_3 : sg (3 : Fin 7) = (4 : Fin 8) := rfl
theorem sg_4 : sg (4 : Fin 7) = (5 : Fin 8) := rfl
theorem sg_5 : sg (5 : Fin 7) = (6 : Fin 8) := rfl
theorem sg_6 : sg (6 : Fin 7) = (7 : Fin 8) := rfl

theorem inst_arr (v : Fin 8 → ℝ) (η : ℝ) (hη : η ≤ (1 / 53760 : ℝ)) (hv : ∀ j, |v j - sv j| ≤ η) :
    ∃ c₀ : Fin 1, Alive (mxOf (fun i => |v (sg i) - v (0 : Fin 8)|) EXs hEXne) (mnOf (fun i => |v (sg i) - v (0 : Fin 8)|) ENs hENne) c₀ ∧
      (∀ c, c < c₀ → ¬ Alive (mxOf (fun i => |v (sg i) - v (0 : Fin 8)|) EXs hEXne) (mnOf (fun i => |v (sg i) - v (0 : Fin 8)|) ENs hENne) c) ∧
      IsLeast {t : ℝ | 0 < t ∧ IsolatedAt v (0 : Fin 8) t} (mxOf (fun i => |v (sg i) - v (0 : Fin 8)|) EXs hEXne c₀) := by
  have hσk : ∀ i, sg i ≠ (0 : Fin 8) := by decide
  have hσ : ∀ j : Fin 8, j ≠ (0 : Fin 8) → ∃ i, sg i = j := by decide
  have hpr : ∀ i, pr i = |sv (sg i) - sv (0 : Fin 8)| := by
    intro i; rcases fin7_cases i with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6, sv_0, sv_1, sv_2, sv_3, sv_4, sv_5, sv_6, sv_7, sg_0, sg_1, sg_2, sg_3, sg_4, sg_5, sg_6]
  have hdev : ∀ i, |(|v (sg i) - v (0 : Fin 8)| - pr i)| ≤ 2 * η := by
    intro i; rw [hpr i]; exact reading_dev v sv η hv (sg i) (0 : Fin 8)
  obtain ⟨c₀, hal, hbf, hT0⟩ := inst (fun i => |v (sg i) - v (0 : Fin 8)|) (2 * η) (by linarith) hdev
  have hset : {t : ℝ | 0 < t ∧ IsolatedAt v (0 : Fin 8) t} =
      {t : ℝ | 0 < t ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (|v (sg i) - v (0 : Fin 8)| * t)} := by
    ext t; simp only [Set.mem_setOf_eq]; rw [iso_iff_readings v (0 : Fin 8) sg hσk hσ t]
  rw [hset]; exact ⟨c₀, hal, hbf, hT0⟩

#print axioms inst_arr

end Fresh.CertRR.R11216



/-!
# Landing certificate `CertRR.R11224`: speeds (1, 2, 6, 7, 8, 9, 11, 16), subject index 0

Generated 2026-10-24 by `experiments/n8/cert_gen_v1.py` (exact Fractions).  Baseline readings [1, 5, 6, 7, 8, 10, 15].  Components up to the first wide one: 1.
Radius: speeds within `η ≤ 1/8960` of the baseline speeds, giving `ε = 2η ≤ 1/4480`.  Covering margin `μ = 1/256`.
`hcov` is **[PROVISIONAL: covering]**, supporting the claim that the first lonely instant of this subject is the largest exit of the first alive component.
Result `inst_arr`: for such `v`, the subject has a first isolation (a least element over all `t > 0`).  Grades: [L].
-/

open Classical

namespace Fresh.CertRR.R11224

open Fresh Fresh.LandingCert Fresh.LandingRule

noncomputable def pr : Fin 7 → ℝ := ![(1 : ℝ), (5 : ℝ), (6 : ℝ), (7 : ℝ), (8 : ℝ), (10 : ℝ), (15 : ℝ)]
noncomputable def aV : Fin 1 → ℝ := ![(9 / 40 : ℝ)]
noncomputable def bV : Fin 1 → ℝ := ![(15 / 64 : ℝ)]
noncomputable def dV : Fin 1 → ℝ := ![(1 / 80 : ℝ)]
noncomputable def TV : Fin 1 → ℝ := ![(79 / 320 : ℝ)]
def ZV : Fin 1 → ℤ := ![6]
noncomputable def HV : ℝ := (77 / 320 : ℝ)
noncomputable def EXs (c : Fin 1) : Finset (Fin 7 × ℤ) :=
  (Finset.univ ×ˢ Finset.Icc 0 (ZV c)).filter (fun q => ((q.2 : ℝ) + 1 / 8) / pr q.1 = aV c)
noncomputable def ENs (c : Fin 1) : Finset (Fin 7 × ℤ) :=
  (Finset.univ ×ˢ Finset.Icc 0 (ZV c)).filter (fun q => ((q.2 : ℝ) - 1 / 8) / pr q.1 = bV c)

theorem hp : ∀ i, 1 ≤ pr i ∧ pr i ≤ (15 : ℝ) := by intro i; fin_cases i <;> norm_num [pr]
theorem hp1 : ∀ i, 1 ≤ pr i := fun i => (hp i).1
theorem pr_0 : pr (0 : Fin 7) = (1 : ℝ) := rfl
theorem pr_1 : pr (1 : Fin 7) = (5 : ℝ) := rfl
theorem pr_2 : pr (2 : Fin 7) = (6 : ℝ) := rfl
theorem pr_3 : pr (3 : Fin 7) = (7 : ℝ) := rfl
theorem pr_4 : pr (4 : Fin 7) = (8 : ℝ) := rfl
theorem pr_5 : pr (5 : Fin 7) = (10 : ℝ) := rfl
theorem pr_6 : pr (6 : Fin 7) = (15 : ℝ) := rfl
theorem aV_0 : aV (0 : Fin 1) = (9 / 40 : ℝ) := rfl
theorem bV_0 : bV (0 : Fin 1) = (15 / 64 : ℝ) := rfl
theorem dV_0 : dV (0 : Fin 1) = (1 / 80 : ℝ) := rfl
theorem TV_0 : TV (0 : Fin 1) = (79 / 320 : ℝ) := rfl
theorem ZV_0 : ZV (0 : Fin 1) = (6 : ℤ) := rfl
theorem hab : ∀ c, aV c ≤ bV c := by intro c; fin_cases c <;> norm_num [aV, bV]
theorem hd0 : ∀ c, 0 < dV c := by intro c; fin_cases c <;> norm_num [dV]
theorem hdP : ∀ c, dV c ≤ 1 / (4 * (15 : ℝ)) := by intro c; fin_cases c <;> norm_num [dV]
theorem haP : ∀ c, dV c < aV c := by intro c; fin_cases c <;> norm_num [dV, aV]
theorem hT : ∀ c, bV c + dV c ≤ TV c := by intro c; fin_cases c <;> norm_num [bV, dV, TV]
theorem hZ : ∀ c, ((15 : ℝ) + 1) * TV c + 1 ≤ (ZV c : ℝ) := by intro c; fin_cases c <;> norm_num [TV, ZV]
theorem hE (ε : ℝ) (hε : ε ≤ (1 / 4480 : ℝ)) : ∀ c, 8 * ((ZV c : ℝ) + 1) * ε ≤ dV c := by
  intro c; fin_cases c <;> norm_num [ZV, dV] <;> linarith
theorem hcls : ∀ c i, ∀ z : ℤ, 0 ≤ z → z ≤ ZV c →
    ((z : ℝ) + 1 / 8) / pr i ≤ aV c - dV c ∨ bV c + dV c ≤ ((z : ℝ) - 1 / 8) / pr i ∨
      ((z : ℝ) + 1 / 8) / pr i = aV c ∨ ((z : ℝ) - 1 / 8) / pr i = bV c := by
  intro c i z h0 h1
  fin_cases c <;> fin_cases i <;> simp [ZV] at h1 <;> interval_cases z <;> norm_num [pr, aV, bV, dV]
theorem hEXne : ∀ c, (EXs c).Nonempty := by
  intro c
  fin_cases c
  · exact ⟨(1, 1), by simp [EXs, ZV, pr, aV] <;> norm_num⟩
theorem hENne : ∀ c, (ENs c).Nonempty := by
  intro c
  fin_cases c
  · exact ⟨(4, 2), by simp [ENs, ZV, pr, bV] <;> norm_num⟩
theorem hEXdef : ∀ c, ∀ q : Fin 7 × ℤ, q ∈ EXs c ↔ 0 ≤ q.2 ∧ q.2 ≤ ZV c ∧ ((q.2 : ℝ) + 1 / 8) / pr q.1 = aV c := by
  intro c q
  simp only [EXs, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, Finset.mem_Icc, true_and]
  tauto
theorem hENdef : ∀ c, ∀ q : Fin 7 × ℤ, q ∈ ENs c ↔ 0 ≤ q.2 ∧ q.2 ≤ ZV c ∧ ((q.2 : ℝ) - 1 / 8) / pr q.1 = bV c := by
  intro c q
  simp only [ENs, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, Finset.mem_Icc, true_and]
  tauto
theorem hsepL : ∀ c c' : Fin 1, c < c' → bV c + dV c / 2 < aV c' - dV c' / 2 := by
  intro c c' h
  fin_cases c <;> fin_cases c' <;> simp at h ⊢ <;> norm_num [aV, bV, dV]
theorem hHL : ∀ c, bV c + dV c / 2 ≤ HV := by intro c; fin_cases c <;> norm_num [bV, dV, HV]

theorem gap0 (x : Fin 7 → ℝ) (ε : ℝ) (hdev : ∀ i, |x i - pr i| ≤ ε) (hεH : ε * HV ≤ (1 / 256 : ℝ) / 2) (t : ℝ) (h0 : 0 ≤ t)
    (hHt : t ≤ HV) (h1 : (0 : ℝ) ≤ t) (h2 : t ≤ (7 / 32 : ℝ)) (hlon : ∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)) : False := by
  rcases le_total t (31 / 256 : ℝ) with hs0 | hs0
  · exact zone_kill_gen pr x ε HV (1 / 256 : ℝ) hp1 hdev hεH (by norm_num) (0 : Fin 7) 0 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (0 : Fin 7))
  rcases le_total t (35 / 256 : ℝ) with hs1 | hs1
  · exact zone_kill_gen pr x ε HV (1 / 256 : ℝ) hp1 hdev hεH (by norm_num) (4 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (4 : Fin 7))
  rcases le_total t (281 / 1792 : ℝ) with hs2 | hs2
  · exact zone_kill_gen pr x ε HV (1 / 256 : ℝ) hp1 hdev hεH (by norm_num) (3 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (3 : Fin 7))
  rcases le_total t (47 / 256 : ℝ) with hs3 | hs3
  · exact zone_kill_gen pr x ε HV (1 / 256 : ℝ) hp1 hdev hεH (by norm_num) (2 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (2 : Fin 7))
  exact zone_kill_gen pr x ε HV (1 / 256 : ℝ) hp1 hdev hεH (by norm_num) (1 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (1 : Fin 7))
theorem cov (x : Fin 7 → ℝ) (ε : ℝ) (hε : ε ≤ (1 / 4480 : ℝ)) (hdev : ∀ i, |x i - pr i| ≤ ε) :
    ∀ t : ℝ, 0 < t → t ≤ HV → (∀ c, ¬ (aV c - dV c / 2 ≤ t ∧ t ≤ bV c + dV c / 2)) →
      ¬ (∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)) := by
  intro t h0 hHt hnone hlon
  have hεH : ε * HV ≤ (1 / 256 : ℝ) / 2 := by
    have hε0 : 0 ≤ ε := le_trans (abs_nonneg _) (hdev 0)
    have : ε * HV ≤ (1 / 4480 : ℝ) * HV := mul_le_mul_of_nonneg_right hε (by norm_num [HV])
    have h2 : (1 / 4480 : ℝ) * HV ≤ (1 / 256 : ℝ) / 2 := by norm_num [HV]
    linarith
  have n0 := hnone (0 : Fin 1)
  rw [aV_0, bV_0, dV_0] at n0
  rcases lt_or_ge t (7 / 32 : ℝ) with c0 | c0
  · exact gap0 x ε hdev hεH t h0.le hHt h0.le (by linarith) hlon
  have d0 : (77 / 320 : ℝ) < t := by
    by_contra hc; push Not at hc; exact n0 ⟨by linarith, by linarith⟩
  have hHv : HV = (77 / 320 : ℝ) := rfl
  exact absurd (by linarith : t ≤ (77 / 320 : ℝ)) (not_le.2 d0)

theorem inst (x : Fin 7 → ℝ) (ε : ℝ) (hε : ε ≤ (1 / 4480 : ℝ)) (hdev : ∀ i, |x i - pr i| ≤ ε) :
    ∃ c₀ : Fin 1, Alive (mxOf x EXs hEXne) (mnOf x ENs hENne) c₀ ∧
      (∀ c, c < c₀ → ¬ Alive (mxOf x EXs hEXne) (mnOf x ENs hENne) c) ∧
      IsLeast {t : ℝ | 0 < t ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)} (mxOf x EXs hEXne c₀) :=
  landing_cert 1 (15 : ℝ) (by norm_num) pr x hp ε hdev aV bV dV TV ZV hab hd0 hdP haP hT hZ (hE ε hε) hcls EXs ENs hEXne hENne
    hEXdef hENdef hsepL HV hHL (cov x ε hε hdev) (0 : Fin 1) (by rw [dV_0, bV_0, aV_0]; norm_num)

noncomputable def sv : Fin 8 → ℝ := ![(1 : ℝ), (2 : ℝ), (6 : ℝ), (7 : ℝ), (8 : ℝ), (9 : ℝ), (11 : ℝ), (16 : ℝ)]
def sg : Fin 7 → Fin 8 := ![1, 2, 3, 4, 5, 6, 7]

theorem sv_0 : sv (0 : Fin 8) = (1 : ℝ) := rfl
theorem sv_1 : sv (1 : Fin 8) = (2 : ℝ) := rfl
theorem sv_2 : sv (2 : Fin 8) = (6 : ℝ) := rfl
theorem sv_3 : sv (3 : Fin 8) = (7 : ℝ) := rfl
theorem sv_4 : sv (4 : Fin 8) = (8 : ℝ) := rfl
theorem sv_5 : sv (5 : Fin 8) = (9 : ℝ) := rfl
theorem sv_6 : sv (6 : Fin 8) = (11 : ℝ) := rfl
theorem sv_7 : sv (7 : Fin 8) = (16 : ℝ) := rfl
theorem sg_0 : sg (0 : Fin 7) = (1 : Fin 8) := rfl
theorem sg_1 : sg (1 : Fin 7) = (2 : Fin 8) := rfl
theorem sg_2 : sg (2 : Fin 7) = (3 : Fin 8) := rfl
theorem sg_3 : sg (3 : Fin 7) = (4 : Fin 8) := rfl
theorem sg_4 : sg (4 : Fin 7) = (5 : Fin 8) := rfl
theorem sg_5 : sg (5 : Fin 7) = (6 : Fin 8) := rfl
theorem sg_6 : sg (6 : Fin 7) = (7 : Fin 8) := rfl

theorem inst_arr (v : Fin 8 → ℝ) (η : ℝ) (hη : η ≤ (1 / 8960 : ℝ)) (hv : ∀ j, |v j - sv j| ≤ η) :
    ∃ c₀ : Fin 1, Alive (mxOf (fun i => |v (sg i) - v (0 : Fin 8)|) EXs hEXne) (mnOf (fun i => |v (sg i) - v (0 : Fin 8)|) ENs hENne) c₀ ∧
      (∀ c, c < c₀ → ¬ Alive (mxOf (fun i => |v (sg i) - v (0 : Fin 8)|) EXs hEXne) (mnOf (fun i => |v (sg i) - v (0 : Fin 8)|) ENs hENne) c) ∧
      IsLeast {t : ℝ | 0 < t ∧ IsolatedAt v (0 : Fin 8) t} (mxOf (fun i => |v (sg i) - v (0 : Fin 8)|) EXs hEXne c₀) := by
  have hσk : ∀ i, sg i ≠ (0 : Fin 8) := by decide
  have hσ : ∀ j : Fin 8, j ≠ (0 : Fin 8) → ∃ i, sg i = j := by decide
  have hpr : ∀ i, pr i = |sv (sg i) - sv (0 : Fin 8)| := by
    intro i; rcases fin7_cases i with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6, sv_0, sv_1, sv_2, sv_3, sv_4, sv_5, sv_6, sv_7, sg_0, sg_1, sg_2, sg_3, sg_4, sg_5, sg_6]
  have hdev : ∀ i, |(|v (sg i) - v (0 : Fin 8)| - pr i)| ≤ 2 * η := by
    intro i; rw [hpr i]; exact reading_dev v sv η hv (sg i) (0 : Fin 8)
  obtain ⟨c₀, hal, hbf, hT0⟩ := inst (fun i => |v (sg i) - v (0 : Fin 8)|) (2 * η) (by linarith) hdev
  have hset : {t : ℝ | 0 < t ∧ IsolatedAt v (0 : Fin 8) t} =
      {t : ℝ | 0 < t ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (|v (sg i) - v (0 : Fin 8)| * t)} := by
    ext t; simp only [Set.mem_setOf_eq]; rw [iso_iff_readings v (0 : Fin 8) sg hσk hσ t]
  rw [hset]; exact ⟨c₀, hal, hbf, hT0⟩

#print axioms inst_arr

end Fresh.CertRR.R11224



/-!
# Landing certificate `CertRR.R11232`: speeds (1, 2, 6, 7, 8, 9, 12, 13), subject index 0

Generated 2026-10-24 by `experiments/n8/cert_gen_v1.py` (exact Fractions).  Baseline readings [1, 5, 6, 7, 8, 11, 12].  Components up to the first wide one: 1.
Radius: speeds within `η ≤ 1/18432` of the baseline speeds, giving `ε = 2η ≤ 1/9216`.  Covering margin `μ = 1/512`.
`hcov` is **[PROVISIONAL: covering]**, supporting the claim that the first lonely instant of this subject is the largest exit of the first alive component.
Result `inst_arr`: for such `v`, the subject has a first isolation (a least element over all `t > 0`).  Grades: [L].
-/

open Classical

namespace Fresh.CertRR.R11232

open Fresh Fresh.LandingCert Fresh.LandingRule

noncomputable def pr : Fin 7 → ℝ := ![(1 : ℝ), (5 : ℝ), (6 : ℝ), (7 : ℝ), (8 : ℝ), (11 : ℝ), (12 : ℝ)]
noncomputable def aV : Fin 1 → ℝ := ![(9 / 40 : ℝ)]
noncomputable def bV : Fin 1 → ℝ := ![(15 / 64 : ℝ)]
noncomputable def dV : Fin 1 → ℝ := ![(1 / 192 : ℝ)]
noncomputable def TV : Fin 1 → ℝ := ![(23 / 96 : ℝ)]
def ZV : Fin 1 → ℤ := ![5]
noncomputable def HV : ℝ := (91 / 384 : ℝ)
noncomputable def EXs (c : Fin 1) : Finset (Fin 7 × ℤ) :=
  (Finset.univ ×ˢ Finset.Icc 0 (ZV c)).filter (fun q => ((q.2 : ℝ) + 1 / 8) / pr q.1 = aV c)
noncomputable def ENs (c : Fin 1) : Finset (Fin 7 × ℤ) :=
  (Finset.univ ×ˢ Finset.Icc 0 (ZV c)).filter (fun q => ((q.2 : ℝ) - 1 / 8) / pr q.1 = bV c)

theorem hp : ∀ i, 1 ≤ pr i ∧ pr i ≤ (12 : ℝ) := by intro i; fin_cases i <;> norm_num [pr]
theorem hp1 : ∀ i, 1 ≤ pr i := fun i => (hp i).1
theorem pr_0 : pr (0 : Fin 7) = (1 : ℝ) := rfl
theorem pr_1 : pr (1 : Fin 7) = (5 : ℝ) := rfl
theorem pr_2 : pr (2 : Fin 7) = (6 : ℝ) := rfl
theorem pr_3 : pr (3 : Fin 7) = (7 : ℝ) := rfl
theorem pr_4 : pr (4 : Fin 7) = (8 : ℝ) := rfl
theorem pr_5 : pr (5 : Fin 7) = (11 : ℝ) := rfl
theorem pr_6 : pr (6 : Fin 7) = (12 : ℝ) := rfl
theorem aV_0 : aV (0 : Fin 1) = (9 / 40 : ℝ) := rfl
theorem bV_0 : bV (0 : Fin 1) = (15 / 64 : ℝ) := rfl
theorem dV_0 : dV (0 : Fin 1) = (1 / 192 : ℝ) := rfl
theorem TV_0 : TV (0 : Fin 1) = (23 / 96 : ℝ) := rfl
theorem ZV_0 : ZV (0 : Fin 1) = (5 : ℤ) := rfl
theorem hab : ∀ c, aV c ≤ bV c := by intro c; fin_cases c <;> norm_num [aV, bV]
theorem hd0 : ∀ c, 0 < dV c := by intro c; fin_cases c <;> norm_num [dV]
theorem hdP : ∀ c, dV c ≤ 1 / (4 * (12 : ℝ)) := by intro c; fin_cases c <;> norm_num [dV]
theorem haP : ∀ c, dV c < aV c := by intro c; fin_cases c <;> norm_num [dV, aV]
theorem hT : ∀ c, bV c + dV c ≤ TV c := by intro c; fin_cases c <;> norm_num [bV, dV, TV]
theorem hZ : ∀ c, ((12 : ℝ) + 1) * TV c + 1 ≤ (ZV c : ℝ) := by intro c; fin_cases c <;> norm_num [TV, ZV]
theorem hE (ε : ℝ) (hε : ε ≤ (1 / 9216 : ℝ)) : ∀ c, 8 * ((ZV c : ℝ) + 1) * ε ≤ dV c := by
  intro c; fin_cases c <;> norm_num [ZV, dV] <;> linarith
theorem hcls : ∀ c i, ∀ z : ℤ, 0 ≤ z → z ≤ ZV c →
    ((z : ℝ) + 1 / 8) / pr i ≤ aV c - dV c ∨ bV c + dV c ≤ ((z : ℝ) - 1 / 8) / pr i ∨
      ((z : ℝ) + 1 / 8) / pr i = aV c ∨ ((z : ℝ) - 1 / 8) / pr i = bV c := by
  intro c i z h0 h1
  fin_cases c <;> fin_cases i <;> simp [ZV] at h1 <;> interval_cases z <;> norm_num [pr, aV, bV, dV]
theorem hEXne : ∀ c, (EXs c).Nonempty := by
  intro c
  fin_cases c
  · exact ⟨(1, 1), by simp [EXs, ZV, pr, aV] <;> norm_num⟩
theorem hENne : ∀ c, (ENs c).Nonempty := by
  intro c
  fin_cases c
  · exact ⟨(4, 2), by simp [ENs, ZV, pr, bV] <;> norm_num⟩
theorem hEXdef : ∀ c, ∀ q : Fin 7 × ℤ, q ∈ EXs c ↔ 0 ≤ q.2 ∧ q.2 ≤ ZV c ∧ ((q.2 : ℝ) + 1 / 8) / pr q.1 = aV c := by
  intro c q
  simp only [EXs, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, Finset.mem_Icc, true_and]
  tauto
theorem hENdef : ∀ c, ∀ q : Fin 7 × ℤ, q ∈ ENs c ↔ 0 ≤ q.2 ∧ q.2 ≤ ZV c ∧ ((q.2 : ℝ) - 1 / 8) / pr q.1 = bV c := by
  intro c q
  simp only [ENs, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, Finset.mem_Icc, true_and]
  tauto
theorem hsepL : ∀ c c' : Fin 1, c < c' → bV c + dV c / 2 < aV c' - dV c' / 2 := by
  intro c c' h
  fin_cases c <;> fin_cases c' <;> simp at h ⊢ <;> norm_num [aV, bV, dV]
theorem hHL : ∀ c, bV c + dV c / 2 ≤ HV := by intro c; fin_cases c <;> norm_num [bV, dV, HV]

theorem gap0 (x : Fin 7 → ℝ) (ε : ℝ) (hdev : ∀ i, |x i - pr i| ≤ ε) (hεH : ε * HV ≤ (1 / 512 : ℝ) / 2) (t : ℝ) (h0 : 0 ≤ t)
    (hHt : t ≤ HV) (h1 : (0 : ℝ) ≤ t) (h2 : t ≤ (427 / 1920 : ℝ)) (hlon : ∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)) : False := by
  rcases le_total t (63 / 512 : ℝ) with hs0 | hs0
  · exact zone_kill_gen pr x ε HV (1 / 512 : ℝ) hp1 hdev hεH (by norm_num) (0 : Fin 7) 0 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (0 : Fin 7))
  rcases le_total t (71 / 512 : ℝ) with hs1 | hs1
  · exact zone_kill_gen pr x ε HV (1 / 512 : ℝ) hp1 hdev hεH (by norm_num) (4 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (4 : Fin 7))
  rcases le_total t (569 / 3584 : ℝ) with hs2 | hs2
  · exact zone_kill_gen pr x ε HV (1 / 512 : ℝ) hp1 hdev hεH (by norm_num) (3 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (3 : Fin 7))
  rcases le_total t (95 / 512 : ℝ) with hs3 | hs3
  · exact zone_kill_gen pr x ε HV (1 / 512 : ℝ) hp1 hdev hεH (by norm_num) (2 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (2 : Fin 7))
  exact zone_kill_gen pr x ε HV (1 / 512 : ℝ) hp1 hdev hεH (by norm_num) (1 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (1 : Fin 7))
theorem cov (x : Fin 7 → ℝ) (ε : ℝ) (hε : ε ≤ (1 / 9216 : ℝ)) (hdev : ∀ i, |x i - pr i| ≤ ε) :
    ∀ t : ℝ, 0 < t → t ≤ HV → (∀ c, ¬ (aV c - dV c / 2 ≤ t ∧ t ≤ bV c + dV c / 2)) →
      ¬ (∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)) := by
  intro t h0 hHt hnone hlon
  have hεH : ε * HV ≤ (1 / 512 : ℝ) / 2 := by
    have hε0 : 0 ≤ ε := le_trans (abs_nonneg _) (hdev 0)
    have : ε * HV ≤ (1 / 9216 : ℝ) * HV := mul_le_mul_of_nonneg_right hε (by norm_num [HV])
    have h2 : (1 / 9216 : ℝ) * HV ≤ (1 / 512 : ℝ) / 2 := by norm_num [HV]
    linarith
  have n0 := hnone (0 : Fin 1)
  rw [aV_0, bV_0, dV_0] at n0
  rcases lt_or_ge t (427 / 1920 : ℝ) with c0 | c0
  · exact gap0 x ε hdev hεH t h0.le hHt h0.le (by linarith) hlon
  have d0 : (91 / 384 : ℝ) < t := by
    by_contra hc; push Not at hc; exact n0 ⟨by linarith, by linarith⟩
  have hHv : HV = (91 / 384 : ℝ) := rfl
  exact absurd (by linarith : t ≤ (91 / 384 : ℝ)) (not_le.2 d0)

theorem inst (x : Fin 7 → ℝ) (ε : ℝ) (hε : ε ≤ (1 / 9216 : ℝ)) (hdev : ∀ i, |x i - pr i| ≤ ε) :
    ∃ c₀ : Fin 1, Alive (mxOf x EXs hEXne) (mnOf x ENs hENne) c₀ ∧
      (∀ c, c < c₀ → ¬ Alive (mxOf x EXs hEXne) (mnOf x ENs hENne) c) ∧
      IsLeast {t : ℝ | 0 < t ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)} (mxOf x EXs hEXne c₀) :=
  landing_cert 1 (12 : ℝ) (by norm_num) pr x hp ε hdev aV bV dV TV ZV hab hd0 hdP haP hT hZ (hE ε hε) hcls EXs ENs hEXne hENne
    hEXdef hENdef hsepL HV hHL (cov x ε hε hdev) (0 : Fin 1) (by rw [dV_0, bV_0, aV_0]; norm_num)

noncomputable def sv : Fin 8 → ℝ := ![(1 : ℝ), (2 : ℝ), (6 : ℝ), (7 : ℝ), (8 : ℝ), (9 : ℝ), (12 : ℝ), (13 : ℝ)]
def sg : Fin 7 → Fin 8 := ![1, 2, 3, 4, 5, 6, 7]

theorem sv_0 : sv (0 : Fin 8) = (1 : ℝ) := rfl
theorem sv_1 : sv (1 : Fin 8) = (2 : ℝ) := rfl
theorem sv_2 : sv (2 : Fin 8) = (6 : ℝ) := rfl
theorem sv_3 : sv (3 : Fin 8) = (7 : ℝ) := rfl
theorem sv_4 : sv (4 : Fin 8) = (8 : ℝ) := rfl
theorem sv_5 : sv (5 : Fin 8) = (9 : ℝ) := rfl
theorem sv_6 : sv (6 : Fin 8) = (12 : ℝ) := rfl
theorem sv_7 : sv (7 : Fin 8) = (13 : ℝ) := rfl
theorem sg_0 : sg (0 : Fin 7) = (1 : Fin 8) := rfl
theorem sg_1 : sg (1 : Fin 7) = (2 : Fin 8) := rfl
theorem sg_2 : sg (2 : Fin 7) = (3 : Fin 8) := rfl
theorem sg_3 : sg (3 : Fin 7) = (4 : Fin 8) := rfl
theorem sg_4 : sg (4 : Fin 7) = (5 : Fin 8) := rfl
theorem sg_5 : sg (5 : Fin 7) = (6 : Fin 8) := rfl
theorem sg_6 : sg (6 : Fin 7) = (7 : Fin 8) := rfl

theorem inst_arr (v : Fin 8 → ℝ) (η : ℝ) (hη : η ≤ (1 / 18432 : ℝ)) (hv : ∀ j, |v j - sv j| ≤ η) :
    ∃ c₀ : Fin 1, Alive (mxOf (fun i => |v (sg i) - v (0 : Fin 8)|) EXs hEXne) (mnOf (fun i => |v (sg i) - v (0 : Fin 8)|) ENs hENne) c₀ ∧
      (∀ c, c < c₀ → ¬ Alive (mxOf (fun i => |v (sg i) - v (0 : Fin 8)|) EXs hEXne) (mnOf (fun i => |v (sg i) - v (0 : Fin 8)|) ENs hENne) c) ∧
      IsLeast {t : ℝ | 0 < t ∧ IsolatedAt v (0 : Fin 8) t} (mxOf (fun i => |v (sg i) - v (0 : Fin 8)|) EXs hEXne c₀) := by
  have hσk : ∀ i, sg i ≠ (0 : Fin 8) := by decide
  have hσ : ∀ j : Fin 8, j ≠ (0 : Fin 8) → ∃ i, sg i = j := by decide
  have hpr : ∀ i, pr i = |sv (sg i) - sv (0 : Fin 8)| := by
    intro i; rcases fin7_cases i with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6, sv_0, sv_1, sv_2, sv_3, sv_4, sv_5, sv_6, sv_7, sg_0, sg_1, sg_2, sg_3, sg_4, sg_5, sg_6]
  have hdev : ∀ i, |(|v (sg i) - v (0 : Fin 8)| - pr i)| ≤ 2 * η := by
    intro i; rw [hpr i]; exact reading_dev v sv η hv (sg i) (0 : Fin 8)
  obtain ⟨c₀, hal, hbf, hT0⟩ := inst (fun i => |v (sg i) - v (0 : Fin 8)|) (2 * η) (by linarith) hdev
  have hset : {t : ℝ | 0 < t ∧ IsolatedAt v (0 : Fin 8) t} =
      {t : ℝ | 0 < t ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (|v (sg i) - v (0 : Fin 8)| * t)} := by
    ext t; simp only [Set.mem_setOf_eq]; rw [iso_iff_readings v (0 : Fin 8) sg hσk hσ t]
  rw [hset]; exact ⟨c₀, hal, hbf, hT0⟩

#print axioms inst_arr

end Fresh.CertRR.R11232



/-!
# Landing certificate `CertRR.R11240`: speeds (1, 2, 6, 7, 8, 9, 12, 14), subject index 0

Generated 2026-10-24 by `experiments/n8/cert_gen_v1.py` (exact Fractions).  Baseline readings [1, 5, 6, 7, 8, 11, 13].  Components up to the first wide one: 1.
Radius: speeds within `η ≤ 1/27648` of the baseline speeds, giving `ε = 2η ≤ 1/13824`.  Covering margin `μ = 1/2048`.
`hcov` is **[PROVISIONAL: covering]**, supporting the claim that the first lonely instant of this subject is the largest exit of the first alive component.
Result `inst_arr`: for such `v`, the subject has a first isolation (a least element over all `t > 0`).  Grades: [L].
-/

open Classical

namespace Fresh.CertRR.R11240

open Fresh Fresh.LandingCert Fresh.LandingRule

noncomputable def pr : Fin 7 → ℝ := ![(1 : ℝ), (5 : ℝ), (6 : ℝ), (7 : ℝ), (8 : ℝ), (11 : ℝ), (13 : ℝ)]
noncomputable def aV : Fin 1 → ℝ := ![(49 / 104 : ℝ)]
noncomputable def bV : Fin 1 → ℝ := ![(23 / 48 : ℝ)]
noncomputable def dV : Fin 1 → ℝ := ![(1 / 192 : ℝ)]
noncomputable def TV : Fin 1 → ℝ := ![(31 / 64 : ℝ)]
def ZV : Fin 1 → ℤ := ![8]
noncomputable def HV : ℝ := (185 / 384 : ℝ)
noncomputable def EXs (c : Fin 1) : Finset (Fin 7 × ℤ) :=
  (Finset.univ ×ˢ Finset.Icc 0 (ZV c)).filter (fun q => ((q.2 : ℝ) + 1 / 8) / pr q.1 = aV c)
noncomputable def ENs (c : Fin 1) : Finset (Fin 7 × ℤ) :=
  (Finset.univ ×ˢ Finset.Icc 0 (ZV c)).filter (fun q => ((q.2 : ℝ) - 1 / 8) / pr q.1 = bV c)

theorem hp : ∀ i, 1 ≤ pr i ∧ pr i ≤ (13 : ℝ) := by intro i; fin_cases i <;> norm_num [pr]
theorem hp1 : ∀ i, 1 ≤ pr i := fun i => (hp i).1
theorem pr_0 : pr (0 : Fin 7) = (1 : ℝ) := rfl
theorem pr_1 : pr (1 : Fin 7) = (5 : ℝ) := rfl
theorem pr_2 : pr (2 : Fin 7) = (6 : ℝ) := rfl
theorem pr_3 : pr (3 : Fin 7) = (7 : ℝ) := rfl
theorem pr_4 : pr (4 : Fin 7) = (8 : ℝ) := rfl
theorem pr_5 : pr (5 : Fin 7) = (11 : ℝ) := rfl
theorem pr_6 : pr (6 : Fin 7) = (13 : ℝ) := rfl
theorem aV_0 : aV (0 : Fin 1) = (49 / 104 : ℝ) := rfl
theorem bV_0 : bV (0 : Fin 1) = (23 / 48 : ℝ) := rfl
theorem dV_0 : dV (0 : Fin 1) = (1 / 192 : ℝ) := rfl
theorem TV_0 : TV (0 : Fin 1) = (31 / 64 : ℝ) := rfl
theorem ZV_0 : ZV (0 : Fin 1) = (8 : ℤ) := rfl
theorem hab : ∀ c, aV c ≤ bV c := by intro c; fin_cases c <;> norm_num [aV, bV]
theorem hd0 : ∀ c, 0 < dV c := by intro c; fin_cases c <;> norm_num [dV]
theorem hdP : ∀ c, dV c ≤ 1 / (4 * (13 : ℝ)) := by intro c; fin_cases c <;> norm_num [dV]
theorem haP : ∀ c, dV c < aV c := by intro c; fin_cases c <;> norm_num [dV, aV]
theorem hT : ∀ c, bV c + dV c ≤ TV c := by intro c; fin_cases c <;> norm_num [bV, dV, TV]
theorem hZ : ∀ c, ((13 : ℝ) + 1) * TV c + 1 ≤ (ZV c : ℝ) := by intro c; fin_cases c <;> norm_num [TV, ZV]
theorem hE (ε : ℝ) (hε : ε ≤ (1 / 13824 : ℝ)) : ∀ c, 8 * ((ZV c : ℝ) + 1) * ε ≤ dV c := by
  intro c; fin_cases c <;> norm_num [ZV, dV] <;> linarith
theorem hcls : ∀ c i, ∀ z : ℤ, 0 ≤ z → z ≤ ZV c →
    ((z : ℝ) + 1 / 8) / pr i ≤ aV c - dV c ∨ bV c + dV c ≤ ((z : ℝ) - 1 / 8) / pr i ∨
      ((z : ℝ) + 1 / 8) / pr i = aV c ∨ ((z : ℝ) - 1 / 8) / pr i = bV c := by
  intro c i z h0 h1
  fin_cases c <;> fin_cases i <;> simp [ZV] at h1 <;> interval_cases z <;> norm_num [pr, aV, bV, dV]
theorem hEXne : ∀ c, (EXs c).Nonempty := by
  intro c
  fin_cases c
  · exact ⟨(6, 6), by simp [EXs, ZV, pr, aV] <;> norm_num⟩
theorem hENne : ∀ c, (ENs c).Nonempty := by
  intro c
  fin_cases c
  · exact ⟨(2, 3), by simp [ENs, ZV, pr, bV] <;> norm_num⟩
theorem hEXdef : ∀ c, ∀ q : Fin 7 × ℤ, q ∈ EXs c ↔ 0 ≤ q.2 ∧ q.2 ≤ ZV c ∧ ((q.2 : ℝ) + 1 / 8) / pr q.1 = aV c := by
  intro c q
  simp only [EXs, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, Finset.mem_Icc, true_and]
  tauto
theorem hENdef : ∀ c, ∀ q : Fin 7 × ℤ, q ∈ ENs c ↔ 0 ≤ q.2 ∧ q.2 ≤ ZV c ∧ ((q.2 : ℝ) - 1 / 8) / pr q.1 = bV c := by
  intro c q
  simp only [ENs, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, Finset.mem_Icc, true_and]
  tauto
theorem hsepL : ∀ c c' : Fin 1, c < c' → bV c + dV c / 2 < aV c' - dV c' / 2 := by
  intro c c' h
  fin_cases c <;> fin_cases c' <;> simp at h ⊢ <;> norm_num [aV, bV, dV]
theorem hHL : ∀ c, bV c + dV c / 2 ≤ HV := by intro c; fin_cases c <;> norm_num [bV, dV, HV]

theorem gap0 (x : Fin 7 → ℝ) (ε : ℝ) (hdev : ∀ i, |x i - pr i| ≤ ε) (hεH : ε * HV ≤ (1 / 2048 : ℝ) / 2) (t : ℝ) (h0 : 0 ≤ t)
    (hHt : t ≤ HV) (h1 : (0 : ℝ) ≤ t) (h2 : t ≤ (2339 / 4992 : ℝ)) (hlon : ∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)) : False := by
  rcases le_total t (255 / 2048 : ℝ) with hs0 | hs0
  · exact zone_kill_gen pr x ε HV (1 / 2048 : ℝ) hp1 hdev hεH (by norm_num) (0 : Fin 7) 0 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (0 : Fin 7))
  rcases le_total t (287 / 2048 : ℝ) with hs1 | hs1
  · exact zone_kill_gen pr x ε HV (1 / 2048 : ℝ) hp1 hdev hεH (by norm_num) (4 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (4 : Fin 7))
  rcases le_total t (2297 / 14336 : ℝ) with hs2 | hs2
  · exact zone_kill_gen pr x ε HV (1 / 2048 : ℝ) hp1 hdev hεH (by norm_num) (3 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (3 : Fin 7))
  rcases le_total t (383 / 2048 : ℝ) with hs3 | hs3
  · exact zone_kill_gen pr x ε HV (1 / 2048 : ℝ) hp1 hdev hεH (by norm_num) (2 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (2 : Fin 7))
  rcases le_total t (2299 / 10240 : ℝ) with hs4 | hs4
  · exact zone_kill_gen pr x ε HV (1 / 2048 : ℝ) hp1 hdev hεH (by norm_num) (1 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (1 : Fin 7))
  rcases le_total t (6387 / 26624 : ℝ) with hs5 | hs5
  · exact zone_kill_gen pr x ε HV (1 / 2048 : ℝ) hp1 hdev hεH (by norm_num) (6 : Fin 7) 3 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (6 : Fin 7))
  rcases le_total t (543 / 2048 : ℝ) with hs6 | hs6
  · exact zone_kill_gen pr x ε HV (1 / 2048 : ℝ) hp1 hdev hεH (by norm_num) (4 : Fin 7) 2 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (4 : Fin 7))
  rcases le_total t (6389 / 22528 : ℝ) with hs7 | hs7
  · exact zone_kill_gen pr x ε HV (1 / 2048 : ℝ) hp1 hdev hεH (by norm_num) (5 : Fin 7) 3 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (5 : Fin 7))
  rcases le_total t (4345 / 14336 : ℝ) with hs8 | hs8
  · exact zone_kill_gen pr x ε HV (1 / 2048 : ℝ) hp1 hdev hεH (by norm_num) (3 : Fin 7) 2 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (3 : Fin 7))
  rcases le_total t (8435 / 26624 : ℝ) with hs9 | hs9
  · exact zone_kill_gen pr x ε HV (1 / 2048 : ℝ) hp1 hdev hεH (by norm_num) (6 : Fin 7) 4 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (6 : Fin 7))
  rcases le_total t (2173 / 6144 : ℝ) with hs10 | hs10
  · exact zone_kill_gen pr x ε HV (1 / 2048 : ℝ) hp1 hdev hεH (by norm_num) (2 : Fin 7) 2 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (2 : Fin 7))
  rcases le_total t (767 / 2048 : ℝ) with hs11 | hs11
  · exact zone_kill_gen pr x ε HV (1 / 2048 : ℝ) hp1 hdev hεH (by norm_num) (5 : Fin 7) 4 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (5 : Fin 7))
  rcases le_total t (799 / 2048 : ℝ) with hs12 | hs12
  · exact zone_kill_gen pr x ε HV (1 / 2048 : ℝ) hp1 hdev hεH (by norm_num) (4 : Fin 7) 3 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (4 : Fin 7))
  rcases le_total t (4347 / 10240 : ℝ) with hs13 | hs13
  · exact zone_kill_gen pr x ε HV (1 / 2048 : ℝ) hp1 hdev hεH (by norm_num) (1 : Fin 7) 2 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (1 : Fin 7))
  rcases le_total t (6393 / 14336 : ℝ) with hs14 | hs14
  · exact zone_kill_gen pr x ε HV (1 / 2048 : ℝ) hp1 hdev hεH (by norm_num) (3 : Fin 7) 3 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (3 : Fin 7))
  rcases le_total t (10485 / 22528 : ℝ) with hs15 | hs15
  · exact zone_kill_gen pr x ε HV (1 / 2048 : ℝ) hp1 hdev hεH (by norm_num) (5 : Fin 7) 5 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (5 : Fin 7))
  exact zone_kill_gen pr x ε HV (1 / 2048 : ℝ) hp1 hdev hεH (by norm_num) (6 : Fin 7) 6 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (6 : Fin 7))
theorem cov (x : Fin 7 → ℝ) (ε : ℝ) (hε : ε ≤ (1 / 13824 : ℝ)) (hdev : ∀ i, |x i - pr i| ≤ ε) :
    ∀ t : ℝ, 0 < t → t ≤ HV → (∀ c, ¬ (aV c - dV c / 2 ≤ t ∧ t ≤ bV c + dV c / 2)) →
      ¬ (∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)) := by
  intro t h0 hHt hnone hlon
  have hεH : ε * HV ≤ (1 / 2048 : ℝ) / 2 := by
    have hε0 : 0 ≤ ε := le_trans (abs_nonneg _) (hdev 0)
    have : ε * HV ≤ (1 / 13824 : ℝ) * HV := mul_le_mul_of_nonneg_right hε (by norm_num [HV])
    have h2 : (1 / 13824 : ℝ) * HV ≤ (1 / 2048 : ℝ) / 2 := by norm_num [HV]
    linarith
  have n0 := hnone (0 : Fin 1)
  rw [aV_0, bV_0, dV_0] at n0
  rcases lt_or_ge t (2339 / 4992 : ℝ) with c0 | c0
  · exact gap0 x ε hdev hεH t h0.le hHt h0.le (by linarith) hlon
  have d0 : (185 / 384 : ℝ) < t := by
    by_contra hc; push Not at hc; exact n0 ⟨by linarith, by linarith⟩
  have hHv : HV = (185 / 384 : ℝ) := rfl
  exact absurd (by linarith : t ≤ (185 / 384 : ℝ)) (not_le.2 d0)

theorem inst (x : Fin 7 → ℝ) (ε : ℝ) (hε : ε ≤ (1 / 13824 : ℝ)) (hdev : ∀ i, |x i - pr i| ≤ ε) :
    ∃ c₀ : Fin 1, Alive (mxOf x EXs hEXne) (mnOf x ENs hENne) c₀ ∧
      (∀ c, c < c₀ → ¬ Alive (mxOf x EXs hEXne) (mnOf x ENs hENne) c) ∧
      IsLeast {t : ℝ | 0 < t ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)} (mxOf x EXs hEXne c₀) :=
  landing_cert 1 (13 : ℝ) (by norm_num) pr x hp ε hdev aV bV dV TV ZV hab hd0 hdP haP hT hZ (hE ε hε) hcls EXs ENs hEXne hENne
    hEXdef hENdef hsepL HV hHL (cov x ε hε hdev) (0 : Fin 1) (by rw [dV_0, bV_0, aV_0]; norm_num)

noncomputable def sv : Fin 8 → ℝ := ![(1 : ℝ), (2 : ℝ), (6 : ℝ), (7 : ℝ), (8 : ℝ), (9 : ℝ), (12 : ℝ), (14 : ℝ)]
def sg : Fin 7 → Fin 8 := ![1, 2, 3, 4, 5, 6, 7]

theorem sv_0 : sv (0 : Fin 8) = (1 : ℝ) := rfl
theorem sv_1 : sv (1 : Fin 8) = (2 : ℝ) := rfl
theorem sv_2 : sv (2 : Fin 8) = (6 : ℝ) := rfl
theorem sv_3 : sv (3 : Fin 8) = (7 : ℝ) := rfl
theorem sv_4 : sv (4 : Fin 8) = (8 : ℝ) := rfl
theorem sv_5 : sv (5 : Fin 8) = (9 : ℝ) := rfl
theorem sv_6 : sv (6 : Fin 8) = (12 : ℝ) := rfl
theorem sv_7 : sv (7 : Fin 8) = (14 : ℝ) := rfl
theorem sg_0 : sg (0 : Fin 7) = (1 : Fin 8) := rfl
theorem sg_1 : sg (1 : Fin 7) = (2 : Fin 8) := rfl
theorem sg_2 : sg (2 : Fin 7) = (3 : Fin 8) := rfl
theorem sg_3 : sg (3 : Fin 7) = (4 : Fin 8) := rfl
theorem sg_4 : sg (4 : Fin 7) = (5 : Fin 8) := rfl
theorem sg_5 : sg (5 : Fin 7) = (6 : Fin 8) := rfl
theorem sg_6 : sg (6 : Fin 7) = (7 : Fin 8) := rfl

theorem inst_arr (v : Fin 8 → ℝ) (η : ℝ) (hη : η ≤ (1 / 27648 : ℝ)) (hv : ∀ j, |v j - sv j| ≤ η) :
    ∃ c₀ : Fin 1, Alive (mxOf (fun i => |v (sg i) - v (0 : Fin 8)|) EXs hEXne) (mnOf (fun i => |v (sg i) - v (0 : Fin 8)|) ENs hENne) c₀ ∧
      (∀ c, c < c₀ → ¬ Alive (mxOf (fun i => |v (sg i) - v (0 : Fin 8)|) EXs hEXne) (mnOf (fun i => |v (sg i) - v (0 : Fin 8)|) ENs hENne) c) ∧
      IsLeast {t : ℝ | 0 < t ∧ IsolatedAt v (0 : Fin 8) t} (mxOf (fun i => |v (sg i) - v (0 : Fin 8)|) EXs hEXne c₀) := by
  have hσk : ∀ i, sg i ≠ (0 : Fin 8) := by decide
  have hσ : ∀ j : Fin 8, j ≠ (0 : Fin 8) → ∃ i, sg i = j := by decide
  have hpr : ∀ i, pr i = |sv (sg i) - sv (0 : Fin 8)| := by
    intro i; rcases fin7_cases i with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6, sv_0, sv_1, sv_2, sv_3, sv_4, sv_5, sv_6, sv_7, sg_0, sg_1, sg_2, sg_3, sg_4, sg_5, sg_6]
  have hdev : ∀ i, |(|v (sg i) - v (0 : Fin 8)| - pr i)| ≤ 2 * η := by
    intro i; rw [hpr i]; exact reading_dev v sv η hv (sg i) (0 : Fin 8)
  obtain ⟨c₀, hal, hbf, hT0⟩ := inst (fun i => |v (sg i) - v (0 : Fin 8)|) (2 * η) (by linarith) hdev
  have hset : {t : ℝ | 0 < t ∧ IsolatedAt v (0 : Fin 8) t} =
      {t : ℝ | 0 < t ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (|v (sg i) - v (0 : Fin 8)| * t)} := by
    ext t; simp only [Set.mem_setOf_eq]; rw [iso_iff_readings v (0 : Fin 8) sg hσk hσ t]
  rw [hset]; exact ⟨c₀, hal, hbf, hT0⟩

#print axioms inst_arr

end Fresh.CertRR.R11240

