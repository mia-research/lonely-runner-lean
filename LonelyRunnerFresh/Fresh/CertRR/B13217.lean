import Mathlib
import Fresh.Framework
import Fresh.Localisation
import Fresh.LandingCert

/-!
# Landing certificate `CertRR.R13217`: speeds (1, 2, 8, 9, 10, 12, 13, 16), subject index 1

Generated 2026-10-24 by `experiments/n8/cert_gen_v1.py` (exact Fractions).  Baseline readings [1, 6, 7, 8, 10, 11, 14].  Components up to the first wide one: 1.
Radius: speeds within `η ≤ 1/8960` of the baseline speeds, giving `ε = 2η ≤ 1/4480`.  Covering margin `μ = 1/512`.
`hcov` is **[PROVISIONAL: covering]**, supporting the claim that the first lonely instant of this subject is the largest exit of the first alive component.
Result `inst_arr`: for such `v`, the subject has a first isolation (a least element over all `t > 0`).  Grades: [L].
-/

open Classical

namespace Fresh.CertRR.R13217

open Fresh Fresh.LandingCert Fresh.LandingRule

noncomputable def pr : Fin 7 → ℝ := ![(1 : ℝ), (6 : ℝ), (7 : ℝ), (8 : ℝ), (10 : ℝ), (11 : ℝ), (14 : ℝ)]
noncomputable def aV : Fin 1 → ℝ := ![(25 / 112 : ℝ)]
noncomputable def bV : Fin 1 → ℝ := ![(15 / 64 : ℝ)]
noncomputable def dV : Fin 1 → ℝ := ![(3 / 280 : ℝ)]
noncomputable def TV : Fin 1 → ℝ := ![(549 / 2240 : ℝ)]
def ZV : Fin 1 → ℤ := ![5]
noncomputable def HV : ℝ := (537 / 2240 : ℝ)
noncomputable def EXs (c : Fin 1) : Finset (Fin 7 × ℤ) :=
  (Finset.univ ×ˢ Finset.Icc 0 (ZV c)).filter (fun q => ((q.2 : ℝ) + 1 / 8) / pr q.1 = aV c)
noncomputable def ENs (c : Fin 1) : Finset (Fin 7 × ℤ) :=
  (Finset.univ ×ˢ Finset.Icc 0 (ZV c)).filter (fun q => ((q.2 : ℝ) - 1 / 8) / pr q.1 = bV c)

theorem hp : ∀ i, 1 ≤ pr i ∧ pr i ≤ (14 : ℝ) := by intro i; fin_cases i <;> norm_num [pr]
theorem hp1 : ∀ i, 1 ≤ pr i := fun i => (hp i).1
theorem pr_0 : pr (0 : Fin 7) = (1 : ℝ) := rfl
theorem pr_1 : pr (1 : Fin 7) = (6 : ℝ) := rfl
theorem pr_2 : pr (2 : Fin 7) = (7 : ℝ) := rfl
theorem pr_3 : pr (3 : Fin 7) = (8 : ℝ) := rfl
theorem pr_4 : pr (4 : Fin 7) = (10 : ℝ) := rfl
theorem pr_5 : pr (5 : Fin 7) = (11 : ℝ) := rfl
theorem pr_6 : pr (6 : Fin 7) = (14 : ℝ) := rfl
theorem aV_0 : aV (0 : Fin 1) = (25 / 112 : ℝ) := rfl
theorem bV_0 : bV (0 : Fin 1) = (15 / 64 : ℝ) := rfl
theorem dV_0 : dV (0 : Fin 1) = (3 / 280 : ℝ) := rfl
theorem TV_0 : TV (0 : Fin 1) = (549 / 2240 : ℝ) := rfl
theorem ZV_0 : ZV (0 : Fin 1) = (5 : ℤ) := rfl
theorem hab : ∀ c, aV c ≤ bV c := by intro c; fin_cases c <;> norm_num [aV, bV]
theorem hd0 : ∀ c, 0 < dV c := by intro c; fin_cases c <;> norm_num [dV]
theorem hdP : ∀ c, dV c ≤ 1 / (4 * (14 : ℝ)) := by intro c; fin_cases c <;> norm_num [dV]
theorem haP : ∀ c, dV c < aV c := by intro c; fin_cases c <;> norm_num [dV, aV]
theorem hT : ∀ c, bV c + dV c ≤ TV c := by intro c; fin_cases c <;> norm_num [bV, dV, TV]
theorem hZ : ∀ c, ((14 : ℝ) + 1) * TV c + 1 ≤ (ZV c : ℝ) := by intro c; fin_cases c <;> norm_num [TV, ZV]
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
  · exact ⟨(6, 3), by simp [EXs, ZV, pr, aV] <;> norm_num⟩
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
    (hHt : t ≤ HV) (h1 : (0 : ℝ) ≤ t) (h2 : t ≤ (61 / 280 : ℝ)) (hlon : ∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)) : False := by
  rcases le_total t (63 / 512 : ℝ) with hs0 | hs0
  · exact zone_kill_gen pr x ε HV (1 / 512 : ℝ) hp1 hdev hεH (by norm_num) (0 : Fin 7) 0 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (0 : Fin 7))
  rcases le_total t (71 / 512 : ℝ) with hs1 | hs1
  · exact zone_kill_gen pr x ε HV (1 / 512 : ℝ) hp1 hdev hεH (by norm_num) (3 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (3 : Fin 7))
  rcases le_total t (569 / 3584 : ℝ) with hs2 | hs2
  · exact zone_kill_gen pr x ε HV (1 / 512 : ℝ) hp1 hdev hεH (by norm_num) (2 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (2 : Fin 7))
  rcases le_total t (95 / 512 : ℝ) with hs3 | hs3
  · exact zone_kill_gen pr x ε HV (1 / 512 : ℝ) hp1 hdev hεH (by norm_num) (1 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (1 : Fin 7))
  rcases le_total t (1077 / 5632 : ℝ) with hs4 | hs4
  · exact zone_kill_gen pr x ε HV (1 / 512 : ℝ) hp1 hdev hεH (by norm_num) (5 : Fin 7) 2 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (5 : Fin 7))
  rcases le_total t (539 / 2560 : ℝ) with hs5 | hs5
  · exact zone_kill_gen pr x ε HV (1 / 512 : ℝ) hp1 hdev hεH (by norm_num) (4 : Fin 7) 2 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (4 : Fin 7))
  exact zone_kill_gen pr x ε HV (1 / 512 : ℝ) hp1 hdev hεH (by norm_num) (6 : Fin 7) 3 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (6 : Fin 7))
theorem cov (x : Fin 7 → ℝ) (ε : ℝ) (hε : ε ≤ (1 / 4480 : ℝ)) (hdev : ∀ i, |x i - pr i| ≤ ε) :
    ∀ t : ℝ, 0 < t → t ≤ HV → (∀ c, ¬ (aV c - dV c / 2 ≤ t ∧ t ≤ bV c + dV c / 2)) →
      ¬ (∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)) := by
  intro t h0 hHt hnone hlon
  have hεH : ε * HV ≤ (1 / 512 : ℝ) / 2 := by
    have hε0 : 0 ≤ ε := le_trans (abs_nonneg _) (hdev 0)
    have : ε * HV ≤ (1 / 4480 : ℝ) * HV := mul_le_mul_of_nonneg_right hε (by norm_num [HV])
    have h2 : (1 / 4480 : ℝ) * HV ≤ (1 / 512 : ℝ) / 2 := by norm_num [HV]
    linarith
  have n0 := hnone (0 : Fin 1)
  rw [aV_0, bV_0, dV_0] at n0
  rcases lt_or_ge t (61 / 280 : ℝ) with c0 | c0
  · exact gap0 x ε hdev hεH t h0.le hHt h0.le (by linarith) hlon
  have d0 : (537 / 2240 : ℝ) < t := by
    by_contra hc; push Not at hc; exact n0 ⟨by linarith, by linarith⟩
  have hHv : HV = (537 / 2240 : ℝ) := rfl
  exact absurd (by linarith : t ≤ (537 / 2240 : ℝ)) (not_le.2 d0)

theorem inst (x : Fin 7 → ℝ) (ε : ℝ) (hε : ε ≤ (1 / 4480 : ℝ)) (hdev : ∀ i, |x i - pr i| ≤ ε) :
    ∃ c₀ : Fin 1, Alive (mxOf x EXs hEXne) (mnOf x ENs hENne) c₀ ∧
      (∀ c, c < c₀ → ¬ Alive (mxOf x EXs hEXne) (mnOf x ENs hENne) c) ∧
      IsLeast {t : ℝ | 0 < t ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)} (mxOf x EXs hEXne c₀) :=
  landing_cert 1 (14 : ℝ) (by norm_num) pr x hp ε hdev aV bV dV TV ZV hab hd0 hdP haP hT hZ (hE ε hε) hcls EXs ENs hEXne hENne
    hEXdef hENdef hsepL HV hHL (cov x ε hε hdev) (0 : Fin 1) (by rw [dV_0, bV_0, aV_0]; norm_num)

noncomputable def sv : Fin 8 → ℝ := ![(1 : ℝ), (2 : ℝ), (8 : ℝ), (9 : ℝ), (10 : ℝ), (12 : ℝ), (13 : ℝ), (16 : ℝ)]
def sg : Fin 7 → Fin 8 := ![0, 2, 3, 4, 5, 6, 7]

theorem sv_0 : sv (0 : Fin 8) = (1 : ℝ) := rfl
theorem sv_1 : sv (1 : Fin 8) = (2 : ℝ) := rfl
theorem sv_2 : sv (2 : Fin 8) = (8 : ℝ) := rfl
theorem sv_3 : sv (3 : Fin 8) = (9 : ℝ) := rfl
theorem sv_4 : sv (4 : Fin 8) = (10 : ℝ) := rfl
theorem sv_5 : sv (5 : Fin 8) = (12 : ℝ) := rfl
theorem sv_6 : sv (6 : Fin 8) = (13 : ℝ) := rfl
theorem sv_7 : sv (7 : Fin 8) = (16 : ℝ) := rfl
theorem sg_0 : sg (0 : Fin 7) = (0 : Fin 8) := rfl
theorem sg_1 : sg (1 : Fin 7) = (2 : Fin 8) := rfl
theorem sg_2 : sg (2 : Fin 7) = (3 : Fin 8) := rfl
theorem sg_3 : sg (3 : Fin 7) = (4 : Fin 8) := rfl
theorem sg_4 : sg (4 : Fin 7) = (5 : Fin 8) := rfl
theorem sg_5 : sg (5 : Fin 7) = (6 : Fin 8) := rfl
theorem sg_6 : sg (6 : Fin 7) = (7 : Fin 8) := rfl

theorem inst_arr (v : Fin 8 → ℝ) (η : ℝ) (hη : η ≤ (1 / 8960 : ℝ)) (hv : ∀ j, |v j - sv j| ≤ η) :
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

end Fresh.CertRR.R13217



/-!
# Landing certificate `CertRR.R13218`: speeds (1, 2, 8, 9, 10, 12, 13, 16), subject index 2

Generated 2026-10-24 by `experiments/n8/cert_gen_v1.py` (exact Fractions).  Baseline readings [7, 6, 1, 2, 4, 5, 8].  Components up to the first wide one: 1.
Radius: speeds within `η ≤ 1/5376` of the baseline speeds, giving `ε = 2η ≤ 1/2688`.  Covering margin `μ = 1/512`.
`hcov` is **[PROVISIONAL: covering]**, supporting the claim that the first lonely instant of this subject is the largest exit of the first alive component.
Result `inst_arr`: for such `v`, the subject has a first isolation (a least element over all `t > 0`).  Grades: [L].
-/

open Classical

namespace Fresh.CertRR.R13218

open Fresh Fresh.LandingCert Fresh.LandingRule

noncomputable def pr : Fin 7 → ℝ := ![(7 : ℝ), (6 : ℝ), (1 : ℝ), (2 : ℝ), (4 : ℝ), (5 : ℝ), (8 : ℝ)]
noncomputable def aV : Fin 1 → ℝ := ![(17 / 56 : ℝ)]
noncomputable def bV : Fin 1 → ℝ := ![(5 / 16 : ℝ)]
noncomputable def dV : Fin 1 → ℝ := ![(1 / 56 : ℝ)]
noncomputable def TV : Fin 1 → ℝ := ![(37 / 112 : ℝ)]
def ZV : Fin 1 → ℤ := ![5]
noncomputable def HV : ℝ := (9 / 28 : ℝ)
noncomputable def EXs (c : Fin 1) : Finset (Fin 7 × ℤ) :=
  (Finset.univ ×ˢ Finset.Icc 0 (ZV c)).filter (fun q => ((q.2 : ℝ) + 1 / 8) / pr q.1 = aV c)
noncomputable def ENs (c : Fin 1) : Finset (Fin 7 × ℤ) :=
  (Finset.univ ×ˢ Finset.Icc 0 (ZV c)).filter (fun q => ((q.2 : ℝ) - 1 / 8) / pr q.1 = bV c)

theorem hp : ∀ i, 1 ≤ pr i ∧ pr i ≤ (8 : ℝ) := by intro i; fin_cases i <;> norm_num [pr]
theorem hp1 : ∀ i, 1 ≤ pr i := fun i => (hp i).1
theorem pr_0 : pr (0 : Fin 7) = (7 : ℝ) := rfl
theorem pr_1 : pr (1 : Fin 7) = (6 : ℝ) := rfl
theorem pr_2 : pr (2 : Fin 7) = (1 : ℝ) := rfl
theorem pr_3 : pr (3 : Fin 7) = (2 : ℝ) := rfl
theorem pr_4 : pr (4 : Fin 7) = (4 : ℝ) := rfl
theorem pr_5 : pr (5 : Fin 7) = (5 : ℝ) := rfl
theorem pr_6 : pr (6 : Fin 7) = (8 : ℝ) := rfl
theorem aV_0 : aV (0 : Fin 1) = (17 / 56 : ℝ) := rfl
theorem bV_0 : bV (0 : Fin 1) = (5 / 16 : ℝ) := rfl
theorem dV_0 : dV (0 : Fin 1) = (1 / 56 : ℝ) := rfl
theorem TV_0 : TV (0 : Fin 1) = (37 / 112 : ℝ) := rfl
theorem ZV_0 : ZV (0 : Fin 1) = (5 : ℤ) := rfl
theorem hab : ∀ c, aV c ≤ bV c := by intro c; fin_cases c <;> norm_num [aV, bV]
theorem hd0 : ∀ c, 0 < dV c := by intro c; fin_cases c <;> norm_num [dV]
theorem hdP : ∀ c, dV c ≤ 1 / (4 * (8 : ℝ)) := by intro c; fin_cases c <;> norm_num [dV]
theorem haP : ∀ c, dV c < aV c := by intro c; fin_cases c <;> norm_num [dV, aV]
theorem hT : ∀ c, bV c + dV c ≤ TV c := by intro c; fin_cases c <;> norm_num [bV, dV, TV]
theorem hZ : ∀ c, ((8 : ℝ) + 1) * TV c + 1 ≤ (ZV c : ℝ) := by intro c; fin_cases c <;> norm_num [TV, ZV]
theorem hE (ε : ℝ) (hε : ε ≤ (1 / 2688 : ℝ)) : ∀ c, 8 * ((ZV c : ℝ) + 1) * ε ≤ dV c := by
  intro c; fin_cases c <;> norm_num [ZV, dV] <;> linarith
theorem hcls : ∀ c i, ∀ z : ℤ, 0 ≤ z → z ≤ ZV c →
    ((z : ℝ) + 1 / 8) / pr i ≤ aV c - dV c ∨ bV c + dV c ≤ ((z : ℝ) - 1 / 8) / pr i ∨
      ((z : ℝ) + 1 / 8) / pr i = aV c ∨ ((z : ℝ) - 1 / 8) / pr i = bV c := by
  intro c i z h0 h1
  fin_cases c <;> fin_cases i <;> simp [ZV] at h1 <;> interval_cases z <;> norm_num [pr, aV, bV, dV]
theorem hEXne : ∀ c, (EXs c).Nonempty := by
  intro c
  fin_cases c
  · exact ⟨(0, 2), by simp [EXs, ZV, pr, aV] <;> norm_num⟩
theorem hENne : ∀ c, (ENs c).Nonempty := by
  intro c
  fin_cases c
  · exact ⟨(1, 2), by simp [ENs, ZV, pr, bV] <;> norm_num⟩
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
  · exact zone_kill_gen pr x ε HV (1 / 512 : ℝ) hp1 hdev hεH (by norm_num) (2 : Fin 7) 0 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (2 : Fin 7))
  rcases le_total t (71 / 512 : ℝ) with hs1 | hs1
  · exact zone_kill_gen pr x ε HV (1 / 512 : ℝ) hp1 hdev hεH (by norm_num) (6 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (6 : Fin 7))
  rcases le_total t (569 / 3584 : ℝ) with hs2 | hs2
  · exact zone_kill_gen pr x ε HV (1 / 512 : ℝ) hp1 hdev hεH (by norm_num) (0 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (0 : Fin 7))
  rcases le_total t (95 / 512 : ℝ) with hs3 | hs3
  · exact zone_kill_gen pr x ε HV (1 / 512 : ℝ) hp1 hdev hεH (by norm_num) (1 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (1 : Fin 7))
  rcases le_total t (571 / 2560 : ℝ) with hs4 | hs4
  · exact zone_kill_gen pr x ε HV (1 / 512 : ℝ) hp1 hdev hεH (by norm_num) (5 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (5 : Fin 7))
  rcases le_total t (143 / 512 : ℝ) with hs5 | hs5
  · exact zone_kill_gen pr x ε HV (1 / 512 : ℝ) hp1 hdev hεH (by norm_num) (4 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (4 : Fin 7))
  exact zone_kill_gen pr x ε HV (1 / 512 : ℝ) hp1 hdev hεH (by norm_num) (0 : Fin 7) 2 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (0 : Fin 7))
theorem cov (x : Fin 7 → ℝ) (ε : ℝ) (hε : ε ≤ (1 / 2688 : ℝ)) (hdev : ∀ i, |x i - pr i| ≤ ε) :
    ∀ t : ℝ, 0 < t → t ≤ HV → (∀ c, ¬ (aV c - dV c / 2 ≤ t ∧ t ≤ bV c + dV c / 2)) →
      ¬ (∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)) := by
  intro t h0 hHt hnone hlon
  have hεH : ε * HV ≤ (1 / 512 : ℝ) / 2 := by
    have hε0 : 0 ≤ ε := le_trans (abs_nonneg _) (hdev 0)
    have : ε * HV ≤ (1 / 2688 : ℝ) * HV := mul_le_mul_of_nonneg_right hε (by norm_num [HV])
    have h2 : (1 / 2688 : ℝ) * HV ≤ (1 / 512 : ℝ) / 2 := by norm_num [HV]
    linarith
  have n0 := hnone (0 : Fin 1)
  rw [aV_0, bV_0, dV_0] at n0
  rcases lt_or_ge t (33 / 112 : ℝ) with c0 | c0
  · exact gap0 x ε hdev hεH t h0.le hHt h0.le (by linarith) hlon
  have d0 : (9 / 28 : ℝ) < t := by
    by_contra hc; push Not at hc; exact n0 ⟨by linarith, by linarith⟩
  have hHv : HV = (9 / 28 : ℝ) := rfl
  exact absurd (by linarith : t ≤ (9 / 28 : ℝ)) (not_le.2 d0)

theorem inst (x : Fin 7 → ℝ) (ε : ℝ) (hε : ε ≤ (1 / 2688 : ℝ)) (hdev : ∀ i, |x i - pr i| ≤ ε) :
    ∃ c₀ : Fin 1, Alive (mxOf x EXs hEXne) (mnOf x ENs hENne) c₀ ∧
      (∀ c, c < c₀ → ¬ Alive (mxOf x EXs hEXne) (mnOf x ENs hENne) c) ∧
      IsLeast {t : ℝ | 0 < t ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)} (mxOf x EXs hEXne c₀) :=
  landing_cert 1 (8 : ℝ) (by norm_num) pr x hp ε hdev aV bV dV TV ZV hab hd0 hdP haP hT hZ (hE ε hε) hcls EXs ENs hEXne hENne
    hEXdef hENdef hsepL HV hHL (cov x ε hε hdev) (0 : Fin 1) (by rw [dV_0, bV_0, aV_0]; norm_num)

noncomputable def sv : Fin 8 → ℝ := ![(1 : ℝ), (2 : ℝ), (8 : ℝ), (9 : ℝ), (10 : ℝ), (12 : ℝ), (13 : ℝ), (16 : ℝ)]
def sg : Fin 7 → Fin 8 := ![0, 1, 3, 4, 5, 6, 7]

theorem sv_0 : sv (0 : Fin 8) = (1 : ℝ) := rfl
theorem sv_1 : sv (1 : Fin 8) = (2 : ℝ) := rfl
theorem sv_2 : sv (2 : Fin 8) = (8 : ℝ) := rfl
theorem sv_3 : sv (3 : Fin 8) = (9 : ℝ) := rfl
theorem sv_4 : sv (4 : Fin 8) = (10 : ℝ) := rfl
theorem sv_5 : sv (5 : Fin 8) = (12 : ℝ) := rfl
theorem sv_6 : sv (6 : Fin 8) = (13 : ℝ) := rfl
theorem sv_7 : sv (7 : Fin 8) = (16 : ℝ) := rfl
theorem sg_0 : sg (0 : Fin 7) = (0 : Fin 8) := rfl
theorem sg_1 : sg (1 : Fin 7) = (1 : Fin 8) := rfl
theorem sg_2 : sg (2 : Fin 7) = (3 : Fin 8) := rfl
theorem sg_3 : sg (3 : Fin 7) = (4 : Fin 8) := rfl
theorem sg_4 : sg (4 : Fin 7) = (5 : Fin 8) := rfl
theorem sg_5 : sg (5 : Fin 7) = (6 : Fin 8) := rfl
theorem sg_6 : sg (6 : Fin 7) = (7 : Fin 8) := rfl

theorem inst_arr (v : Fin 8 → ℝ) (η : ℝ) (hη : η ≤ (1 / 5376 : ℝ)) (hv : ∀ j, |v j - sv j| ≤ η) :
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

end Fresh.CertRR.R13218



/-!
# Landing certificate `CertRR.R13223`: speeds (1, 2, 8, 9, 10, 12, 13, 16), subject index 7

Generated 2026-10-24 by `experiments/n8/cert_gen_v1.py` (exact Fractions).  Baseline readings [15, 14, 8, 7, 6, 4, 3].  Components up to the first wide one: 1.
Radius: speeds within `η ≤ 1/15360` of the baseline speeds, giving `ε = 2η ≤ 1/7680`.  Covering margin `μ = 1/512`.
`hcov` is **[PROVISIONAL: covering]**, supporting the claim that the first lonely instant of this subject is the largest exit of the first alive component.
Result `inst_arr`: for such `v`, the subject has a first isolation (a least element over all `t > 0`).  Grades: [L].
-/

open Classical

namespace Fresh.CertRR.R13223

open Fresh Fresh.LandingCert Fresh.LandingRule

noncomputable def pr : Fin 7 → ℝ := ![(15 : ℝ), (14 : ℝ), (8 : ℝ), (7 : ℝ), (6 : ℝ), (4 : ℝ), (3 : ℝ)]
noncomputable def aV : Fin 1 → ℝ := ![(1 / 24 : ℝ)]
noncomputable def bV : Fin 1 → ℝ := ![(7 / 120 : ℝ)]
noncomputable def dV : Fin 1 → ℝ := ![(1 / 240 : ℝ)]
noncomputable def TV : Fin 1 → ℝ := ![(1 / 16 : ℝ)]
def ZV : Fin 1 → ℤ := ![3]
noncomputable def HV : ℝ := (29 / 480 : ℝ)
noncomputable def EXs (c : Fin 1) : Finset (Fin 7 × ℤ) :=
  (Finset.univ ×ˢ Finset.Icc 0 (ZV c)).filter (fun q => ((q.2 : ℝ) + 1 / 8) / pr q.1 = aV c)
noncomputable def ENs (c : Fin 1) : Finset (Fin 7 × ℤ) :=
  (Finset.univ ×ˢ Finset.Icc 0 (ZV c)).filter (fun q => ((q.2 : ℝ) - 1 / 8) / pr q.1 = bV c)

theorem hp : ∀ i, 1 ≤ pr i ∧ pr i ≤ (15 : ℝ) := by intro i; fin_cases i <;> norm_num [pr]
theorem hp1 : ∀ i, 1 ≤ pr i := fun i => (hp i).1
theorem pr_0 : pr (0 : Fin 7) = (15 : ℝ) := rfl
theorem pr_1 : pr (1 : Fin 7) = (14 : ℝ) := rfl
theorem pr_2 : pr (2 : Fin 7) = (8 : ℝ) := rfl
theorem pr_3 : pr (3 : Fin 7) = (7 : ℝ) := rfl
theorem pr_4 : pr (4 : Fin 7) = (6 : ℝ) := rfl
theorem pr_5 : pr (5 : Fin 7) = (4 : ℝ) := rfl
theorem pr_6 : pr (6 : Fin 7) = (3 : ℝ) := rfl
theorem aV_0 : aV (0 : Fin 1) = (1 / 24 : ℝ) := rfl
theorem bV_0 : bV (0 : Fin 1) = (7 / 120 : ℝ) := rfl
theorem dV_0 : dV (0 : Fin 1) = (1 / 240 : ℝ) := rfl
theorem TV_0 : TV (0 : Fin 1) = (1 / 16 : ℝ) := rfl
theorem ZV_0 : ZV (0 : Fin 1) = (3 : ℤ) := rfl
theorem hab : ∀ c, aV c ≤ bV c := by intro c; fin_cases c <;> norm_num [aV, bV]
theorem hd0 : ∀ c, 0 < dV c := by intro c; fin_cases c <;> norm_num [dV]
theorem hdP : ∀ c, dV c ≤ 1 / (4 * (15 : ℝ)) := by intro c; fin_cases c <;> norm_num [dV]
theorem haP : ∀ c, dV c < aV c := by intro c; fin_cases c <;> norm_num [dV, aV]
theorem hT : ∀ c, bV c + dV c ≤ TV c := by intro c; fin_cases c <;> norm_num [bV, dV, TV]
theorem hZ : ∀ c, ((15 : ℝ) + 1) * TV c + 1 ≤ (ZV c : ℝ) := by intro c; fin_cases c <;> norm_num [TV, ZV]
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
    (hHt : t ≤ HV) (h1 : (0 : ℝ) ≤ t) (h2 : t ≤ (19 / 480 : ℝ)) (hlon : ∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)) : False := by
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
  rcases lt_or_ge t (19 / 480 : ℝ) with c0 | c0
  · exact gap0 x ε hdev hεH t h0.le hHt h0.le (by linarith) hlon
  have d0 : (29 / 480 : ℝ) < t := by
    by_contra hc; push Not at hc; exact n0 ⟨by linarith, by linarith⟩
  have hHv : HV = (29 / 480 : ℝ) := rfl
  exact absurd (by linarith : t ≤ (29 / 480 : ℝ)) (not_le.2 d0)

theorem inst (x : Fin 7 → ℝ) (ε : ℝ) (hε : ε ≤ (1 / 7680 : ℝ)) (hdev : ∀ i, |x i - pr i| ≤ ε) :
    ∃ c₀ : Fin 1, Alive (mxOf x EXs hEXne) (mnOf x ENs hENne) c₀ ∧
      (∀ c, c < c₀ → ¬ Alive (mxOf x EXs hEXne) (mnOf x ENs hENne) c) ∧
      IsLeast {t : ℝ | 0 < t ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)} (mxOf x EXs hEXne c₀) :=
  landing_cert 1 (15 : ℝ) (by norm_num) pr x hp ε hdev aV bV dV TV ZV hab hd0 hdP haP hT hZ (hE ε hε) hcls EXs ENs hEXne hENne
    hEXdef hENdef hsepL HV hHL (cov x ε hε hdev) (0 : Fin 1) (by rw [dV_0, bV_0, aV_0]; norm_num)

noncomputable def sv : Fin 8 → ℝ := ![(1 : ℝ), (2 : ℝ), (8 : ℝ), (9 : ℝ), (10 : ℝ), (12 : ℝ), (13 : ℝ), (16 : ℝ)]
def sg : Fin 7 → Fin 8 := ![0, 1, 2, 3, 4, 5, 6]

theorem sv_0 : sv (0 : Fin 8) = (1 : ℝ) := rfl
theorem sv_1 : sv (1 : Fin 8) = (2 : ℝ) := rfl
theorem sv_2 : sv (2 : Fin 8) = (8 : ℝ) := rfl
theorem sv_3 : sv (3 : Fin 8) = (9 : ℝ) := rfl
theorem sv_4 : sv (4 : Fin 8) = (10 : ℝ) := rfl
theorem sv_5 : sv (5 : Fin 8) = (12 : ℝ) := rfl
theorem sv_6 : sv (6 : Fin 8) = (13 : ℝ) := rfl
theorem sv_7 : sv (7 : Fin 8) = (16 : ℝ) := rfl
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

end Fresh.CertRR.R13223



/-!
# Landing certificate `CertRR.R13225`: speeds (1, 2, 8, 9, 10, 12, 14, 15), subject index 1

Generated 2026-10-24 by `experiments/n8/cert_gen_v1.py` (exact Fractions).  Baseline readings [1, 6, 7, 8, 10, 12, 13].  Components up to the first wide one: 2.
Radius: speeds within `η ≤ 1/7680` of the baseline speeds, giving `ε = 2η ≤ 1/3840`.  Covering margin `μ = 1/256`.
`hcov` is **[PROVISIONAL: covering]**, supporting the claim that the first lonely instant of this subject is the largest exit of the first alive component.
Result `inst_arr`: for such `v`, the subject has a first isolation (a least element over all `t > 0`).  Grades: [L].
-/

open Classical

namespace Fresh.CertRR.R13225

open Fresh Fresh.LandingCert Fresh.LandingRule

noncomputable def pr : Fin 7 → ℝ := ![(1 : ℝ), (6 : ℝ), (7 : ℝ), (8 : ℝ), (10 : ℝ), (12 : ℝ), (13 : ℝ)]
noncomputable def aV : Fin 2 → ℝ := ![(3 / 16 : ℝ), (17 / 80 : ℝ)]
noncomputable def bV : Fin 2 → ℝ := ![(3 / 16 : ℝ), (23 / 104 : ℝ)]
noncomputable def dV : Fin 2 → ℝ := ![(1 / 96 : ℝ), (1 / 80 : ℝ)]
noncomputable def TV : Fin 2 → ℝ := ![(19 / 96 : ℝ), (243 / 1040 : ℝ)]
def ZV : Fin 2 → ℤ := ![4, 5]
noncomputable def HV : ℝ := (473 / 2080 : ℝ)
noncomputable def EXs (c : Fin 2) : Finset (Fin 7 × ℤ) :=
  (Finset.univ ×ˢ Finset.Icc 0 (ZV c)).filter (fun q => ((q.2 : ℝ) + 1 / 8) / pr q.1 = aV c)
noncomputable def ENs (c : Fin 2) : Finset (Fin 7 × ℤ) :=
  (Finset.univ ×ˢ Finset.Icc 0 (ZV c)).filter (fun q => ((q.2 : ℝ) - 1 / 8) / pr q.1 = bV c)

theorem hp : ∀ i, 1 ≤ pr i ∧ pr i ≤ (13 : ℝ) := by intro i; fin_cases i <;> norm_num [pr]
theorem hp1 : ∀ i, 1 ≤ pr i := fun i => (hp i).1
theorem pr_0 : pr (0 : Fin 7) = (1 : ℝ) := rfl
theorem pr_1 : pr (1 : Fin 7) = (6 : ℝ) := rfl
theorem pr_2 : pr (2 : Fin 7) = (7 : ℝ) := rfl
theorem pr_3 : pr (3 : Fin 7) = (8 : ℝ) := rfl
theorem pr_4 : pr (4 : Fin 7) = (10 : ℝ) := rfl
theorem pr_5 : pr (5 : Fin 7) = (12 : ℝ) := rfl
theorem pr_6 : pr (6 : Fin 7) = (13 : ℝ) := rfl
theorem aV_0 : aV (0 : Fin 2) = (3 / 16 : ℝ) := rfl
theorem bV_0 : bV (0 : Fin 2) = (3 / 16 : ℝ) := rfl
theorem dV_0 : dV (0 : Fin 2) = (1 / 96 : ℝ) := rfl
theorem TV_0 : TV (0 : Fin 2) = (19 / 96 : ℝ) := rfl
theorem ZV_0 : ZV (0 : Fin 2) = (4 : ℤ) := rfl
theorem aV_1 : aV (1 : Fin 2) = (17 / 80 : ℝ) := rfl
theorem bV_1 : bV (1 : Fin 2) = (23 / 104 : ℝ) := rfl
theorem dV_1 : dV (1 : Fin 2) = (1 / 80 : ℝ) := rfl
theorem TV_1 : TV (1 : Fin 2) = (243 / 1040 : ℝ) := rfl
theorem ZV_1 : ZV (1 : Fin 2) = (5 : ℤ) := rfl
theorem hab : ∀ c, aV c ≤ bV c := by intro c; fin_cases c <;> norm_num [aV, bV]
theorem hd0 : ∀ c, 0 < dV c := by intro c; fin_cases c <;> norm_num [dV]
theorem hdP : ∀ c, dV c ≤ 1 / (4 * (13 : ℝ)) := by intro c; fin_cases c <;> norm_num [dV]
theorem haP : ∀ c, dV c < aV c := by intro c; fin_cases c <;> norm_num [dV, aV]
theorem hT : ∀ c, bV c + dV c ≤ TV c := by intro c; fin_cases c <;> norm_num [bV, dV, TV]
theorem hZ : ∀ c, ((13 : ℝ) + 1) * TV c + 1 ≤ (ZV c : ℝ) := by intro c; fin_cases c <;> norm_num [TV, ZV]
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
  · exact ⟨(4, 2), by simp [EXs, ZV, pr, aV] <;> norm_num⟩
theorem hENne : ∀ c, (ENs c).Nonempty := by
  intro c
  fin_cases c
  · exact ⟨(4, 2), by simp [ENs, ZV, pr, bV] <;> norm_num⟩
  · exact ⟨(6, 3), by simp [ENs, ZV, pr, bV] <;> norm_num⟩
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

theorem gap0 (x : Fin 7 → ℝ) (ε : ℝ) (hdev : ∀ i, |x i - pr i| ≤ ε) (hεH : ε * HV ≤ (1 / 256 : ℝ) / 2) (t : ℝ) (h0 : 0 ≤ t)
    (hHt : t ≤ HV) (h1 : (0 : ℝ) ≤ t) (h2 : t ≤ (35 / 192 : ℝ)) (hlon : ∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)) : False := by
  rcases le_total t (31 / 256 : ℝ) with hs0 | hs0
  · exact zone_kill_gen pr x ε HV (1 / 256 : ℝ) hp1 hdev hεH (by norm_num) (0 : Fin 7) 0 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (0 : Fin 7))
  rcases le_total t (35 / 256 : ℝ) with hs1 | hs1
  · exact zone_kill_gen pr x ε HV (1 / 256 : ℝ) hp1 hdev hεH (by norm_num) (3 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (3 : Fin 7))
  rcases le_total t (281 / 1792 : ℝ) with hs2 | hs2
  · exact zone_kill_gen pr x ε HV (1 / 256 : ℝ) hp1 hdev hεH (by norm_num) (2 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (2 : Fin 7))
  exact zone_kill_gen pr x ε HV (1 / 256 : ℝ) hp1 hdev hεH (by norm_num) (1 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (1 : Fin 7))
theorem gap1 (x : Fin 7 → ℝ) (ε : ℝ) (hdev : ∀ i, |x i - pr i| ≤ ε) (hεH : ε * HV ≤ (1 / 256 : ℝ) / 2) (t : ℝ) (h0 : 0 ≤ t)
    (hHt : t ≤ HV) (h1 : (37 / 192 : ℝ) ≤ t) (h2 : t ≤ (33 / 160 : ℝ)) (hlon : ∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)) : False := by
  exact zone_kill_gen pr x ε HV (1 / 256 : ℝ) hp1 hdev hεH (by norm_num) (4 : Fin 7) 2 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (4 : Fin 7))
theorem cov (x : Fin 7 → ℝ) (ε : ℝ) (hε : ε ≤ (1 / 3840 : ℝ)) (hdev : ∀ i, |x i - pr i| ≤ ε) :
    ∀ t : ℝ, 0 < t → t ≤ HV → (∀ c, ¬ (aV c - dV c / 2 ≤ t ∧ t ≤ bV c + dV c / 2)) →
      ¬ (∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)) := by
  intro t h0 hHt hnone hlon
  have hεH : ε * HV ≤ (1 / 256 : ℝ) / 2 := by
    have hε0 : 0 ≤ ε := le_trans (abs_nonneg _) (hdev 0)
    have : ε * HV ≤ (1 / 3840 : ℝ) * HV := mul_le_mul_of_nonneg_right hε (by norm_num [HV])
    have h2 : (1 / 3840 : ℝ) * HV ≤ (1 / 256 : ℝ) / 2 := by norm_num [HV]
    linarith
  have n0 := hnone (0 : Fin 2)
  rw [aV_0, bV_0, dV_0] at n0
  have n1 := hnone (1 : Fin 2)
  rw [aV_1, bV_1, dV_1] at n1
  rcases lt_or_ge t (35 / 192 : ℝ) with c0 | c0
  · exact gap0 x ε hdev hεH t h0.le hHt h0.le (by linarith) hlon
  have d0 : (37 / 192 : ℝ) < t := by
    by_contra hc; push Not at hc; exact n0 ⟨by linarith, by linarith⟩
  rcases lt_or_ge t (33 / 160 : ℝ) with c1 | c1
  · exact gap1 x ε hdev hεH t h0.le hHt d0.le (by linarith) hlon
  have d1 : (473 / 2080 : ℝ) < t := by
    by_contra hc; push Not at hc; exact n1 ⟨by linarith, by linarith⟩
  have hHv : HV = (473 / 2080 : ℝ) := rfl
  exact absurd (by linarith : t ≤ (473 / 2080 : ℝ)) (not_le.2 d1)

theorem inst (x : Fin 7 → ℝ) (ε : ℝ) (hε : ε ≤ (1 / 3840 : ℝ)) (hdev : ∀ i, |x i - pr i| ≤ ε) :
    ∃ c₀ : Fin 2, Alive (mxOf x EXs hEXne) (mnOf x ENs hENne) c₀ ∧
      (∀ c, c < c₀ → ¬ Alive (mxOf x EXs hEXne) (mnOf x ENs hENne) c) ∧
      IsLeast {t : ℝ | 0 < t ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)} (mxOf x EXs hEXne c₀) :=
  landing_cert 2 (13 : ℝ) (by norm_num) pr x hp ε hdev aV bV dV TV ZV hab hd0 hdP haP hT hZ (hE ε hε) hcls EXs ENs hEXne hENne
    hEXdef hENdef hsepL HV hHL (cov x ε hε hdev) (1 : Fin 2) (by rw [dV_1, bV_1, aV_1]; norm_num)

noncomputable def sv : Fin 8 → ℝ := ![(1 : ℝ), (2 : ℝ), (8 : ℝ), (9 : ℝ), (10 : ℝ), (12 : ℝ), (14 : ℝ), (15 : ℝ)]
def sg : Fin 7 → Fin 8 := ![0, 2, 3, 4, 5, 6, 7]

theorem sv_0 : sv (0 : Fin 8) = (1 : ℝ) := rfl
theorem sv_1 : sv (1 : Fin 8) = (2 : ℝ) := rfl
theorem sv_2 : sv (2 : Fin 8) = (8 : ℝ) := rfl
theorem sv_3 : sv (3 : Fin 8) = (9 : ℝ) := rfl
theorem sv_4 : sv (4 : Fin 8) = (10 : ℝ) := rfl
theorem sv_5 : sv (5 : Fin 8) = (12 : ℝ) := rfl
theorem sv_6 : sv (6 : Fin 8) = (14 : ℝ) := rfl
theorem sv_7 : sv (7 : Fin 8) = (15 : ℝ) := rfl
theorem sg_0 : sg (0 : Fin 7) = (0 : Fin 8) := rfl
theorem sg_1 : sg (1 : Fin 7) = (2 : Fin 8) := rfl
theorem sg_2 : sg (2 : Fin 7) = (3 : Fin 8) := rfl
theorem sg_3 : sg (3 : Fin 7) = (4 : Fin 8) := rfl
theorem sg_4 : sg (4 : Fin 7) = (5 : Fin 8) := rfl
theorem sg_5 : sg (5 : Fin 7) = (6 : Fin 8) := rfl
theorem sg_6 : sg (6 : Fin 7) = (7 : Fin 8) := rfl

theorem inst_arr (v : Fin 8 → ℝ) (η : ℝ) (hη : η ≤ (1 / 7680 : ℝ)) (hv : ∀ j, |v j - sv j| ≤ η) :
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

end Fresh.CertRR.R13225



/-!
# Landing certificate `CertRR.R13227`: speeds (1, 2, 8, 9, 10, 12, 14, 15), subject index 3

Generated 2026-10-24 by `experiments/n8/cert_gen_v1.py` (exact Fractions).  Baseline readings [8, 7, 1, 1, 3, 5, 6].  Components up to the first wide one: 1.
Radius: speeds within `η ≤ 1/5120` of the baseline speeds, giving `ε = 2η ≤ 1/2560`.  Covering margin `μ = 1/256`.
`hcov` is **[PROVISIONAL: covering]**, supporting the claim that the first lonely instant of this subject is the largest exit of the first alive component.
Result `inst_arr`: for such `v`, the subject has a first isolation (a least element over all `t > 0`).  Grades: [L].
-/

open Classical

namespace Fresh.CertRR.R13227

open Fresh Fresh.LandingCert Fresh.LandingRule

noncomputable def pr : Fin 7 → ℝ := ![(8 : ℝ), (7 : ℝ), (1 : ℝ), (1 : ℝ), (3 : ℝ), (5 : ℝ), (6 : ℝ)]
noncomputable def aV : Fin 1 → ℝ := ![(9 / 40 : ℝ)]
noncomputable def bV : Fin 1 → ℝ := ![(15 / 64 : ℝ)]
noncomputable def dV : Fin 1 → ℝ := ![(1 / 64 : ℝ)]
noncomputable def TV : Fin 1 → ℝ := ![(1 / 4 : ℝ)]
def ZV : Fin 1 → ℤ := ![4]
noncomputable def HV : ℝ := (31 / 128 : ℝ)
noncomputable def EXs (c : Fin 1) : Finset (Fin 7 × ℤ) :=
  (Finset.univ ×ˢ Finset.Icc 0 (ZV c)).filter (fun q => ((q.2 : ℝ) + 1 / 8) / pr q.1 = aV c)
noncomputable def ENs (c : Fin 1) : Finset (Fin 7 × ℤ) :=
  (Finset.univ ×ˢ Finset.Icc 0 (ZV c)).filter (fun q => ((q.2 : ℝ) - 1 / 8) / pr q.1 = bV c)

theorem hp : ∀ i, 1 ≤ pr i ∧ pr i ≤ (8 : ℝ) := by intro i; fin_cases i <;> norm_num [pr]
theorem hp1 : ∀ i, 1 ≤ pr i := fun i => (hp i).1
theorem pr_0 : pr (0 : Fin 7) = (8 : ℝ) := rfl
theorem pr_1 : pr (1 : Fin 7) = (7 : ℝ) := rfl
theorem pr_2 : pr (2 : Fin 7) = (1 : ℝ) := rfl
theorem pr_3 : pr (3 : Fin 7) = (1 : ℝ) := rfl
theorem pr_4 : pr (4 : Fin 7) = (3 : ℝ) := rfl
theorem pr_5 : pr (5 : Fin 7) = (5 : ℝ) := rfl
theorem pr_6 : pr (6 : Fin 7) = (6 : ℝ) := rfl
theorem aV_0 : aV (0 : Fin 1) = (9 / 40 : ℝ) := rfl
theorem bV_0 : bV (0 : Fin 1) = (15 / 64 : ℝ) := rfl
theorem dV_0 : dV (0 : Fin 1) = (1 / 64 : ℝ) := rfl
theorem TV_0 : TV (0 : Fin 1) = (1 / 4 : ℝ) := rfl
theorem ZV_0 : ZV (0 : Fin 1) = (4 : ℤ) := rfl
theorem hab : ∀ c, aV c ≤ bV c := by intro c; fin_cases c <;> norm_num [aV, bV]
theorem hd0 : ∀ c, 0 < dV c := by intro c; fin_cases c <;> norm_num [dV]
theorem hdP : ∀ c, dV c ≤ 1 / (4 * (8 : ℝ)) := by intro c; fin_cases c <;> norm_num [dV]
theorem haP : ∀ c, dV c < aV c := by intro c; fin_cases c <;> norm_num [dV, aV]
theorem hT : ∀ c, bV c + dV c ≤ TV c := by intro c; fin_cases c <;> norm_num [bV, dV, TV]
theorem hZ : ∀ c, ((8 : ℝ) + 1) * TV c + 1 ≤ (ZV c : ℝ) := by intro c; fin_cases c <;> norm_num [TV, ZV]
theorem hE (ε : ℝ) (hε : ε ≤ (1 / 2560 : ℝ)) : ∀ c, 8 * ((ZV c : ℝ) + 1) * ε ≤ dV c := by
  intro c; fin_cases c <;> norm_num [ZV, dV] <;> linarith
theorem hcls : ∀ c i, ∀ z : ℤ, 0 ≤ z → z ≤ ZV c →
    ((z : ℝ) + 1 / 8) / pr i ≤ aV c - dV c ∨ bV c + dV c ≤ ((z : ℝ) - 1 / 8) / pr i ∨
      ((z : ℝ) + 1 / 8) / pr i = aV c ∨ ((z : ℝ) - 1 / 8) / pr i = bV c := by
  intro c i z h0 h1
  fin_cases c <;> fin_cases i <;> simp [ZV] at h1 <;> interval_cases z <;> norm_num [pr, aV, bV, dV]
theorem hEXne : ∀ c, (EXs c).Nonempty := by
  intro c
  fin_cases c
  · exact ⟨(5, 1), by simp [EXs, ZV, pr, aV] <;> norm_num⟩
theorem hENne : ∀ c, (ENs c).Nonempty := by
  intro c
  fin_cases c
  · exact ⟨(0, 2), by simp [ENs, ZV, pr, bV] <;> norm_num⟩
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
    (hHt : t ≤ HV) (h1 : (0 : ℝ) ≤ t) (h2 : t ≤ (139 / 640 : ℝ)) (hlon : ∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)) : False := by
  rcases le_total t (31 / 256 : ℝ) with hs0 | hs0
  · exact zone_kill_gen pr x ε HV (1 / 256 : ℝ) hp1 hdev hεH (by norm_num) (2 : Fin 7) 0 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (2 : Fin 7))
  rcases le_total t (35 / 256 : ℝ) with hs1 | hs1
  · exact zone_kill_gen pr x ε HV (1 / 256 : ℝ) hp1 hdev hεH (by norm_num) (0 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (0 : Fin 7))
  rcases le_total t (281 / 1792 : ℝ) with hs2 | hs2
  · exact zone_kill_gen pr x ε HV (1 / 256 : ℝ) hp1 hdev hεH (by norm_num) (1 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (1 : Fin 7))
  rcases le_total t (47 / 256 : ℝ) with hs3 | hs3
  · exact zone_kill_gen pr x ε HV (1 / 256 : ℝ) hp1 hdev hεH (by norm_num) (6 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (6 : Fin 7))
  exact zone_kill_gen pr x ε HV (1 / 256 : ℝ) hp1 hdev hεH (by norm_num) (5 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (5 : Fin 7))
theorem cov (x : Fin 7 → ℝ) (ε : ℝ) (hε : ε ≤ (1 / 2560 : ℝ)) (hdev : ∀ i, |x i - pr i| ≤ ε) :
    ∀ t : ℝ, 0 < t → t ≤ HV → (∀ c, ¬ (aV c - dV c / 2 ≤ t ∧ t ≤ bV c + dV c / 2)) →
      ¬ (∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)) := by
  intro t h0 hHt hnone hlon
  have hεH : ε * HV ≤ (1 / 256 : ℝ) / 2 := by
    have hε0 : 0 ≤ ε := le_trans (abs_nonneg _) (hdev 0)
    have : ε * HV ≤ (1 / 2560 : ℝ) * HV := mul_le_mul_of_nonneg_right hε (by norm_num [HV])
    have h2 : (1 / 2560 : ℝ) * HV ≤ (1 / 256 : ℝ) / 2 := by norm_num [HV]
    linarith
  have n0 := hnone (0 : Fin 1)
  rw [aV_0, bV_0, dV_0] at n0
  rcases lt_or_ge t (139 / 640 : ℝ) with c0 | c0
  · exact gap0 x ε hdev hεH t h0.le hHt h0.le (by linarith) hlon
  have d0 : (31 / 128 : ℝ) < t := by
    by_contra hc; push Not at hc; exact n0 ⟨by linarith, by linarith⟩
  have hHv : HV = (31 / 128 : ℝ) := rfl
  exact absurd (by linarith : t ≤ (31 / 128 : ℝ)) (not_le.2 d0)

theorem inst (x : Fin 7 → ℝ) (ε : ℝ) (hε : ε ≤ (1 / 2560 : ℝ)) (hdev : ∀ i, |x i - pr i| ≤ ε) :
    ∃ c₀ : Fin 1, Alive (mxOf x EXs hEXne) (mnOf x ENs hENne) c₀ ∧
      (∀ c, c < c₀ → ¬ Alive (mxOf x EXs hEXne) (mnOf x ENs hENne) c) ∧
      IsLeast {t : ℝ | 0 < t ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)} (mxOf x EXs hEXne c₀) :=
  landing_cert 1 (8 : ℝ) (by norm_num) pr x hp ε hdev aV bV dV TV ZV hab hd0 hdP haP hT hZ (hE ε hε) hcls EXs ENs hEXne hENne
    hEXdef hENdef hsepL HV hHL (cov x ε hε hdev) (0 : Fin 1) (by rw [dV_0, bV_0, aV_0]; norm_num)

noncomputable def sv : Fin 8 → ℝ := ![(1 : ℝ), (2 : ℝ), (8 : ℝ), (9 : ℝ), (10 : ℝ), (12 : ℝ), (14 : ℝ), (15 : ℝ)]
def sg : Fin 7 → Fin 8 := ![0, 1, 2, 4, 5, 6, 7]

theorem sv_0 : sv (0 : Fin 8) = (1 : ℝ) := rfl
theorem sv_1 : sv (1 : Fin 8) = (2 : ℝ) := rfl
theorem sv_2 : sv (2 : Fin 8) = (8 : ℝ) := rfl
theorem sv_3 : sv (3 : Fin 8) = (9 : ℝ) := rfl
theorem sv_4 : sv (4 : Fin 8) = (10 : ℝ) := rfl
theorem sv_5 : sv (5 : Fin 8) = (12 : ℝ) := rfl
theorem sv_6 : sv (6 : Fin 8) = (14 : ℝ) := rfl
theorem sv_7 : sv (7 : Fin 8) = (15 : ℝ) := rfl
theorem sg_0 : sg (0 : Fin 7) = (0 : Fin 8) := rfl
theorem sg_1 : sg (1 : Fin 7) = (1 : Fin 8) := rfl
theorem sg_2 : sg (2 : Fin 7) = (2 : Fin 8) := rfl
theorem sg_3 : sg (3 : Fin 7) = (4 : Fin 8) := rfl
theorem sg_4 : sg (4 : Fin 7) = (5 : Fin 8) := rfl
theorem sg_5 : sg (5 : Fin 7) = (6 : Fin 8) := rfl
theorem sg_6 : sg (6 : Fin 7) = (7 : Fin 8) := rfl

theorem inst_arr (v : Fin 8 → ℝ) (η : ℝ) (hη : η ≤ (1 / 5120 : ℝ)) (hv : ∀ j, |v j - sv j| ≤ η) :
    ∃ c₀ : Fin 1, Alive (mxOf (fun i => |v (sg i) - v (3 : Fin 8)|) EXs hEXne) (mnOf (fun i => |v (sg i) - v (3 : Fin 8)|) ENs hENne) c₀ ∧
      (∀ c, c < c₀ → ¬ Alive (mxOf (fun i => |v (sg i) - v (3 : Fin 8)|) EXs hEXne) (mnOf (fun i => |v (sg i) - v (3 : Fin 8)|) ENs hENne) c) ∧
      IsLeast {t : ℝ | 0 < t ∧ IsolatedAt v (3 : Fin 8) t} (mxOf (fun i => |v (sg i) - v (3 : Fin 8)|) EXs hEXne c₀) := by
  have hσk : ∀ i, sg i ≠ (3 : Fin 8) := by decide
  have hσ : ∀ j : Fin 8, j ≠ (3 : Fin 8) → ∃ i, sg i = j := by decide
  have hpr : ∀ i, pr i = |sv (sg i) - sv (3 : Fin 8)| := by
    intro i; rcases fin7_cases i with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6, sv_0, sv_1, sv_2, sv_3, sv_4, sv_5, sv_6, sv_7, sg_0, sg_1, sg_2, sg_3, sg_4, sg_5, sg_6]
  have hdev : ∀ i, |(|v (sg i) - v (3 : Fin 8)| - pr i)| ≤ 2 * η := by
    intro i; rw [hpr i]; exact reading_dev v sv η hv (sg i) (3 : Fin 8)
  obtain ⟨c₀, hal, hbf, hT0⟩ := inst (fun i => |v (sg i) - v (3 : Fin 8)|) (2 * η) (by linarith) hdev
  have hset : {t : ℝ | 0 < t ∧ IsolatedAt v (3 : Fin 8) t} =
      {t : ℝ | 0 < t ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (|v (sg i) - v (3 : Fin 8)| * t)} := by
    ext t; simp only [Set.mem_setOf_eq]; rw [iso_iff_readings v (3 : Fin 8) sg hσk hσ t]
  rw [hset]; exact ⟨c₀, hal, hbf, hT0⟩

#print axioms inst_arr

end Fresh.CertRR.R13227



/-!
# Landing certificate `CertRR.R13233`: speeds (1, 2, 8, 9, 10, 12, 14, 16), subject index 1

Generated 2026-10-24 by `experiments/n8/cert_gen_v1.py` (exact Fractions).  Baseline readings [1, 6, 7, 8, 10, 12, 14].  Components up to the first wide one: 2.
Radius: speeds within `η ≤ 1/18432` of the baseline speeds, giving `ε = 2η ≤ 1/9216`.  Covering margin `μ = 1/512`.
`hcov` is **[PROVISIONAL: covering]**, supporting the claim that the first lonely instant of this subject is the largest exit of the first alive component.
Result `inst_arr`: for such `v`, the subject has a first isolation (a least element over all `t > 0`).  Grades: [L].
-/

open Classical

namespace Fresh.CertRR.R13233

open Fresh Fresh.LandingCert Fresh.LandingRule

noncomputable def pr : Fin 7 → ℝ := ![(1 : ℝ), (6 : ℝ), (7 : ℝ), (8 : ℝ), (10 : ℝ), (12 : ℝ), (14 : ℝ)]
noncomputable def aV : Fin 2 → ℝ := ![(3 / 16 : ℝ), (25 / 112 : ℝ)]
noncomputable def bV : Fin 2 → ℝ := ![(3 / 16 : ℝ), (15 / 64 : ℝ)]
noncomputable def dV : Fin 2 → ℝ := ![(1 / 96 : ℝ), (1 / 192 : ℝ)]
noncomputable def TV : Fin 2 → ℝ := ![(19 / 96 : ℝ), (23 / 96 : ℝ)]
def ZV : Fin 2 → ℤ := ![5, 5]
noncomputable def HV : ℝ := (91 / 384 : ℝ)
noncomputable def EXs (c : Fin 2) : Finset (Fin 7 × ℤ) :=
  (Finset.univ ×ˢ Finset.Icc 0 (ZV c)).filter (fun q => ((q.2 : ℝ) + 1 / 8) / pr q.1 = aV c)
noncomputable def ENs (c : Fin 2) : Finset (Fin 7 × ℤ) :=
  (Finset.univ ×ˢ Finset.Icc 0 (ZV c)).filter (fun q => ((q.2 : ℝ) - 1 / 8) / pr q.1 = bV c)

theorem hp : ∀ i, 1 ≤ pr i ∧ pr i ≤ (14 : ℝ) := by intro i; fin_cases i <;> norm_num [pr]
theorem hp1 : ∀ i, 1 ≤ pr i := fun i => (hp i).1
theorem pr_0 : pr (0 : Fin 7) = (1 : ℝ) := rfl
theorem pr_1 : pr (1 : Fin 7) = (6 : ℝ) := rfl
theorem pr_2 : pr (2 : Fin 7) = (7 : ℝ) := rfl
theorem pr_3 : pr (3 : Fin 7) = (8 : ℝ) := rfl
theorem pr_4 : pr (4 : Fin 7) = (10 : ℝ) := rfl
theorem pr_5 : pr (5 : Fin 7) = (12 : ℝ) := rfl
theorem pr_6 : pr (6 : Fin 7) = (14 : ℝ) := rfl
theorem aV_0 : aV (0 : Fin 2) = (3 / 16 : ℝ) := rfl
theorem bV_0 : bV (0 : Fin 2) = (3 / 16 : ℝ) := rfl
theorem dV_0 : dV (0 : Fin 2) = (1 / 96 : ℝ) := rfl
theorem TV_0 : TV (0 : Fin 2) = (19 / 96 : ℝ) := rfl
theorem ZV_0 : ZV (0 : Fin 2) = (5 : ℤ) := rfl
theorem aV_1 : aV (1 : Fin 2) = (25 / 112 : ℝ) := rfl
theorem bV_1 : bV (1 : Fin 2) = (15 / 64 : ℝ) := rfl
theorem dV_1 : dV (1 : Fin 2) = (1 / 192 : ℝ) := rfl
theorem TV_1 : TV (1 : Fin 2) = (23 / 96 : ℝ) := rfl
theorem ZV_1 : ZV (1 : Fin 2) = (5 : ℤ) := rfl
theorem hab : ∀ c, aV c ≤ bV c := by intro c; fin_cases c <;> norm_num [aV, bV]
theorem hd0 : ∀ c, 0 < dV c := by intro c; fin_cases c <;> norm_num [dV]
theorem hdP : ∀ c, dV c ≤ 1 / (4 * (14 : ℝ)) := by intro c; fin_cases c <;> norm_num [dV]
theorem haP : ∀ c, dV c < aV c := by intro c; fin_cases c <;> norm_num [dV, aV]
theorem hT : ∀ c, bV c + dV c ≤ TV c := by intro c; fin_cases c <;> norm_num [bV, dV, TV]
theorem hZ : ∀ c, ((14 : ℝ) + 1) * TV c + 1 ≤ (ZV c : ℝ) := by intro c; fin_cases c <;> norm_num [TV, ZV]
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
  · exact ⟨(6, 3), by simp [EXs, ZV, pr, aV] <;> norm_num⟩
theorem hENne : ∀ c, (ENs c).Nonempty := by
  intro c
  fin_cases c
  · exact ⟨(4, 2), by simp [ENs, ZV, pr, bV] <;> norm_num⟩
  · exact ⟨(3, 2), by simp [ENs, ZV, pr, bV] <;> norm_num⟩
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
    (hHt : t ≤ HV) (h1 : (0 : ℝ) ≤ t) (h2 : t ≤ (35 / 192 : ℝ)) (hlon : ∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)) : False := by
  rcases le_total t (63 / 512 : ℝ) with hs0 | hs0
  · exact zone_kill_gen pr x ε HV (1 / 512 : ℝ) hp1 hdev hεH (by norm_num) (0 : Fin 7) 0 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (0 : Fin 7))
  rcases le_total t (71 / 512 : ℝ) with hs1 | hs1
  · exact zone_kill_gen pr x ε HV (1 / 512 : ℝ) hp1 hdev hεH (by norm_num) (3 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (3 : Fin 7))
  rcases le_total t (569 / 3584 : ℝ) with hs2 | hs2
  · exact zone_kill_gen pr x ε HV (1 / 512 : ℝ) hp1 hdev hεH (by norm_num) (2 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (2 : Fin 7))
  exact zone_kill_gen pr x ε HV (1 / 512 : ℝ) hp1 hdev hεH (by norm_num) (1 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (1 : Fin 7))
theorem gap1 (x : Fin 7 → ℝ) (ε : ℝ) (hdev : ∀ i, |x i - pr i| ≤ ε) (hεH : ε * HV ≤ (1 / 512 : ℝ) / 2) (t : ℝ) (h0 : 0 ≤ t)
    (hHt : t ≤ HV) (h1 : (37 / 192 : ℝ) ≤ t) (h2 : t ≤ (593 / 2688 : ℝ)) (hlon : ∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)) : False := by
  rcases le_total t (539 / 2560 : ℝ) with hs0 | hs0
  · exact zone_kill_gen pr x ε HV (1 / 512 : ℝ) hp1 hdev hεH (by norm_num) (4 : Fin 7) 2 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (4 : Fin 7))
  exact zone_kill_gen pr x ε HV (1 / 512 : ℝ) hp1 hdev hεH (by norm_num) (6 : Fin 7) 3 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (6 : Fin 7))
theorem cov (x : Fin 7 → ℝ) (ε : ℝ) (hε : ε ≤ (1 / 9216 : ℝ)) (hdev : ∀ i, |x i - pr i| ≤ ε) :
    ∀ t : ℝ, 0 < t → t ≤ HV → (∀ c, ¬ (aV c - dV c / 2 ≤ t ∧ t ≤ bV c + dV c / 2)) →
      ¬ (∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)) := by
  intro t h0 hHt hnone hlon
  have hεH : ε * HV ≤ (1 / 512 : ℝ) / 2 := by
    have hε0 : 0 ≤ ε := le_trans (abs_nonneg _) (hdev 0)
    have : ε * HV ≤ (1 / 9216 : ℝ) * HV := mul_le_mul_of_nonneg_right hε (by norm_num [HV])
    have h2 : (1 / 9216 : ℝ) * HV ≤ (1 / 512 : ℝ) / 2 := by norm_num [HV]
    linarith
  have n0 := hnone (0 : Fin 2)
  rw [aV_0, bV_0, dV_0] at n0
  have n1 := hnone (1 : Fin 2)
  rw [aV_1, bV_1, dV_1] at n1
  rcases lt_or_ge t (35 / 192 : ℝ) with c0 | c0
  · exact gap0 x ε hdev hεH t h0.le hHt h0.le (by linarith) hlon
  have d0 : (37 / 192 : ℝ) < t := by
    by_contra hc; push Not at hc; exact n0 ⟨by linarith, by linarith⟩
  rcases lt_or_ge t (593 / 2688 : ℝ) with c1 | c1
  · exact gap1 x ε hdev hεH t h0.le hHt d0.le (by linarith) hlon
  have d1 : (91 / 384 : ℝ) < t := by
    by_contra hc; push Not at hc; exact n1 ⟨by linarith, by linarith⟩
  have hHv : HV = (91 / 384 : ℝ) := rfl
  exact absurd (by linarith : t ≤ (91 / 384 : ℝ)) (not_le.2 d1)

theorem inst (x : Fin 7 → ℝ) (ε : ℝ) (hε : ε ≤ (1 / 9216 : ℝ)) (hdev : ∀ i, |x i - pr i| ≤ ε) :
    ∃ c₀ : Fin 2, Alive (mxOf x EXs hEXne) (mnOf x ENs hENne) c₀ ∧
      (∀ c, c < c₀ → ¬ Alive (mxOf x EXs hEXne) (mnOf x ENs hENne) c) ∧
      IsLeast {t : ℝ | 0 < t ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)} (mxOf x EXs hEXne c₀) :=
  landing_cert 2 (14 : ℝ) (by norm_num) pr x hp ε hdev aV bV dV TV ZV hab hd0 hdP haP hT hZ (hE ε hε) hcls EXs ENs hEXne hENne
    hEXdef hENdef hsepL HV hHL (cov x ε hε hdev) (1 : Fin 2) (by rw [dV_1, bV_1, aV_1]; norm_num)

noncomputable def sv : Fin 8 → ℝ := ![(1 : ℝ), (2 : ℝ), (8 : ℝ), (9 : ℝ), (10 : ℝ), (12 : ℝ), (14 : ℝ), (16 : ℝ)]
def sg : Fin 7 → Fin 8 := ![0, 2, 3, 4, 5, 6, 7]

theorem sv_0 : sv (0 : Fin 8) = (1 : ℝ) := rfl
theorem sv_1 : sv (1 : Fin 8) = (2 : ℝ) := rfl
theorem sv_2 : sv (2 : Fin 8) = (8 : ℝ) := rfl
theorem sv_3 : sv (3 : Fin 8) = (9 : ℝ) := rfl
theorem sv_4 : sv (4 : Fin 8) = (10 : ℝ) := rfl
theorem sv_5 : sv (5 : Fin 8) = (12 : ℝ) := rfl
theorem sv_6 : sv (6 : Fin 8) = (14 : ℝ) := rfl
theorem sv_7 : sv (7 : Fin 8) = (16 : ℝ) := rfl
theorem sg_0 : sg (0 : Fin 7) = (0 : Fin 8) := rfl
theorem sg_1 : sg (1 : Fin 7) = (2 : Fin 8) := rfl
theorem sg_2 : sg (2 : Fin 7) = (3 : Fin 8) := rfl
theorem sg_3 : sg (3 : Fin 7) = (4 : Fin 8) := rfl
theorem sg_4 : sg (4 : Fin 7) = (5 : Fin 8) := rfl
theorem sg_5 : sg (5 : Fin 7) = (6 : Fin 8) := rfl
theorem sg_6 : sg (6 : Fin 7) = (7 : Fin 8) := rfl

theorem inst_arr (v : Fin 8 → ℝ) (η : ℝ) (hη : η ≤ (1 / 18432 : ℝ)) (hv : ∀ j, |v j - sv j| ≤ η) :
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

end Fresh.CertRR.R13233



/-!
# Landing certificate `CertRR.R13239`: speeds (1, 2, 8, 9, 10, 12, 14, 16), subject index 7

Generated 2026-10-24 by `experiments/n8/cert_gen_v1.py` (exact Fractions).  Baseline readings [15, 14, 8, 7, 6, 4, 2].  Components up to the first wide one: 1.
Radius: speeds within `η ≤ 1/14934` of the baseline speeds, giving `ε = 2η ≤ 1/7467`.  Covering margin `μ = 1/512`.
`hcov` is **[PROVISIONAL: covering]**, supporting the claim that the first lonely instant of this subject is the largest exit of the first alive component.
Result `inst_arr`: for such `v`, the subject has a first isolation (a least element over all `t > 0`).  Grades: [L].
-/

open Classical

namespace Fresh.CertRR.R13239

open Fresh Fresh.LandingCert Fresh.LandingRule

noncomputable def pr : Fin 7 → ℝ := ![(15 : ℝ), (14 : ℝ), (8 : ℝ), (7 : ℝ), (6 : ℝ), (4 : ℝ), (2 : ℝ)]
noncomputable def aV : Fin 1 → ℝ := ![(9 / 112 : ℝ)]
noncomputable def bV : Fin 1 → ℝ := ![(7 / 64 : ℝ)]
noncomputable def dV : Fin 1 → ℝ := ![(3 / 560 : ℝ)]
noncomputable def TV : Fin 1 → ℝ := ![(257 / 2240 : ℝ)]
def ZV : Fin 1 → ℤ := ![4]
noncomputable def HV : ℝ := (251 / 2240 : ℝ)
noncomputable def EXs (c : Fin 1) : Finset (Fin 7 × ℤ) :=
  (Finset.univ ×ˢ Finset.Icc 0 (ZV c)).filter (fun q => ((q.2 : ℝ) + 1 / 8) / pr q.1 = aV c)
noncomputable def ENs (c : Fin 1) : Finset (Fin 7 × ℤ) :=
  (Finset.univ ×ˢ Finset.Icc 0 (ZV c)).filter (fun q => ((q.2 : ℝ) - 1 / 8) / pr q.1 = bV c)

theorem hp : ∀ i, 1 ≤ pr i ∧ pr i ≤ (15 : ℝ) := by intro i; fin_cases i <;> norm_num [pr]
theorem hp1 : ∀ i, 1 ≤ pr i := fun i => (hp i).1
theorem pr_0 : pr (0 : Fin 7) = (15 : ℝ) := rfl
theorem pr_1 : pr (1 : Fin 7) = (14 : ℝ) := rfl
theorem pr_2 : pr (2 : Fin 7) = (8 : ℝ) := rfl
theorem pr_3 : pr (3 : Fin 7) = (7 : ℝ) := rfl
theorem pr_4 : pr (4 : Fin 7) = (6 : ℝ) := rfl
theorem pr_5 : pr (5 : Fin 7) = (4 : ℝ) := rfl
theorem pr_6 : pr (6 : Fin 7) = (2 : ℝ) := rfl
theorem aV_0 : aV (0 : Fin 1) = (9 / 112 : ℝ) := rfl
theorem bV_0 : bV (0 : Fin 1) = (7 / 64 : ℝ) := rfl
theorem dV_0 : dV (0 : Fin 1) = (3 / 560 : ℝ) := rfl
theorem TV_0 : TV (0 : Fin 1) = (257 / 2240 : ℝ) := rfl
theorem ZV_0 : ZV (0 : Fin 1) = (4 : ℤ) := rfl
theorem hab : ∀ c, aV c ≤ bV c := by intro c; fin_cases c <;> norm_num [aV, bV]
theorem hd0 : ∀ c, 0 < dV c := by intro c; fin_cases c <;> norm_num [dV]
theorem hdP : ∀ c, dV c ≤ 1 / (4 * (15 : ℝ)) := by intro c; fin_cases c <;> norm_num [dV]
theorem haP : ∀ c, dV c < aV c := by intro c; fin_cases c <;> norm_num [dV, aV]
theorem hT : ∀ c, bV c + dV c ≤ TV c := by intro c; fin_cases c <;> norm_num [bV, dV, TV]
theorem hZ : ∀ c, ((15 : ℝ) + 1) * TV c + 1 ≤ (ZV c : ℝ) := by intro c; fin_cases c <;> norm_num [TV, ZV]
theorem hE (ε : ℝ) (hε : ε ≤ (1 / 7467 : ℝ)) : ∀ c, 8 * ((ZV c : ℝ) + 1) * ε ≤ dV c := by
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
  · exact ⟨(2, 1), by simp [ENs, ZV, pr, bV] <;> norm_num⟩
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
    (hHt : t ≤ HV) (h1 : (0 : ℝ) ≤ t) (h2 : t ≤ (87 / 1120 : ℝ)) (hlon : ∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)) : False := by
  rcases le_total t (31 / 512 : ℝ) with hs0 | hs0
  · exact zone_kill_gen pr x ε HV (1 / 512 : ℝ) hp1 hdev hεH (by norm_num) (6 : Fin 7) 0 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (6 : Fin 7))
  rcases le_total t (187 / 2560 : ℝ) with hs1 | hs1
  · exact zone_kill_gen pr x ε HV (1 / 512 : ℝ) hp1 hdev hεH (by norm_num) (0 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (0 : Fin 7))
  exact zone_kill_gen pr x ε HV (1 / 512 : ℝ) hp1 hdev hεH (by norm_num) (1 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (1 : Fin 7))
theorem cov (x : Fin 7 → ℝ) (ε : ℝ) (hε : ε ≤ (1 / 7467 : ℝ)) (hdev : ∀ i, |x i - pr i| ≤ ε) :
    ∀ t : ℝ, 0 < t → t ≤ HV → (∀ c, ¬ (aV c - dV c / 2 ≤ t ∧ t ≤ bV c + dV c / 2)) →
      ¬ (∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)) := by
  intro t h0 hHt hnone hlon
  have hεH : ε * HV ≤ (1 / 512 : ℝ) / 2 := by
    have hε0 : 0 ≤ ε := le_trans (abs_nonneg _) (hdev 0)
    have : ε * HV ≤ (1 / 7467 : ℝ) * HV := mul_le_mul_of_nonneg_right hε (by norm_num [HV])
    have h2 : (1 / 7467 : ℝ) * HV ≤ (1 / 512 : ℝ) / 2 := by norm_num [HV]
    linarith
  have n0 := hnone (0 : Fin 1)
  rw [aV_0, bV_0, dV_0] at n0
  rcases lt_or_ge t (87 / 1120 : ℝ) with c0 | c0
  · exact gap0 x ε hdev hεH t h0.le hHt h0.le (by linarith) hlon
  have d0 : (251 / 2240 : ℝ) < t := by
    by_contra hc; push Not at hc; exact n0 ⟨by linarith, by linarith⟩
  have hHv : HV = (251 / 2240 : ℝ) := rfl
  exact absurd (by linarith : t ≤ (251 / 2240 : ℝ)) (not_le.2 d0)

theorem inst (x : Fin 7 → ℝ) (ε : ℝ) (hε : ε ≤ (1 / 7467 : ℝ)) (hdev : ∀ i, |x i - pr i| ≤ ε) :
    ∃ c₀ : Fin 1, Alive (mxOf x EXs hEXne) (mnOf x ENs hENne) c₀ ∧
      (∀ c, c < c₀ → ¬ Alive (mxOf x EXs hEXne) (mnOf x ENs hENne) c) ∧
      IsLeast {t : ℝ | 0 < t ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)} (mxOf x EXs hEXne c₀) :=
  landing_cert 1 (15 : ℝ) (by norm_num) pr x hp ε hdev aV bV dV TV ZV hab hd0 hdP haP hT hZ (hE ε hε) hcls EXs ENs hEXne hENne
    hEXdef hENdef hsepL HV hHL (cov x ε hε hdev) (0 : Fin 1) (by rw [dV_0, bV_0, aV_0]; norm_num)

noncomputable def sv : Fin 8 → ℝ := ![(1 : ℝ), (2 : ℝ), (8 : ℝ), (9 : ℝ), (10 : ℝ), (12 : ℝ), (14 : ℝ), (16 : ℝ)]
def sg : Fin 7 → Fin 8 := ![0, 1, 2, 3, 4, 5, 6]

theorem sv_0 : sv (0 : Fin 8) = (1 : ℝ) := rfl
theorem sv_1 : sv (1 : Fin 8) = (2 : ℝ) := rfl
theorem sv_2 : sv (2 : Fin 8) = (8 : ℝ) := rfl
theorem sv_3 : sv (3 : Fin 8) = (9 : ℝ) := rfl
theorem sv_4 : sv (4 : Fin 8) = (10 : ℝ) := rfl
theorem sv_5 : sv (5 : Fin 8) = (12 : ℝ) := rfl
theorem sv_6 : sv (6 : Fin 8) = (14 : ℝ) := rfl
theorem sv_7 : sv (7 : Fin 8) = (16 : ℝ) := rfl
theorem sg_0 : sg (0 : Fin 7) = (0 : Fin 8) := rfl
theorem sg_1 : sg (1 : Fin 7) = (1 : Fin 8) := rfl
theorem sg_2 : sg (2 : Fin 7) = (2 : Fin 8) := rfl
theorem sg_3 : sg (3 : Fin 7) = (3 : Fin 8) := rfl
theorem sg_4 : sg (4 : Fin 7) = (4 : Fin 8) := rfl
theorem sg_5 : sg (5 : Fin 7) = (5 : Fin 8) := rfl
theorem sg_6 : sg (6 : Fin 7) = (6 : Fin 8) := rfl

theorem inst_arr (v : Fin 8 → ℝ) (η : ℝ) (hη : η ≤ (1 / 14934 : ℝ)) (hv : ∀ j, |v j - sv j| ≤ η) :
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

end Fresh.CertRR.R13239



/-!
# Landing certificate `CertRR.R13241`: speeds (1, 2, 8, 9, 10, 12, 15, 16), subject index 1

Generated 2026-10-24 by `experiments/n8/cert_gen_v1.py` (exact Fractions).  Baseline readings [1, 6, 7, 8, 10, 13, 14].  Components up to the first wide one: 2.
Radius: speeds within `η ≤ 1/25088` of the baseline speeds, giving `ε = 2η ≤ 1/12544`.  Covering margin `μ = 1/1024`.
`hcov` is **[PROVISIONAL: covering]**, supporting the claim that the first lonely instant of this subject is the largest exit of the first alive component.
Result `inst_arr`: for such `v`, the subject has a first isolation (a least element over all `t > 0`).  Grades: [L].
-/

open Classical

namespace Fresh.CertRR.R13241

open Fresh Fresh.LandingCert Fresh.LandingRule

noncomputable def pr : Fin 7 → ℝ := ![(1 : ℝ), (6 : ℝ), (7 : ℝ), (8 : ℝ), (10 : ℝ), (13 : ℝ), (14 : ℝ)]
noncomputable def aV : Fin 2 → ℝ := ![(3 / 16 : ℝ), (17 / 64 : ℝ)]
noncomputable def bV : Fin 2 → ℝ := ![(3 / 16 : ℝ), (15 / 56 : ℝ)]
noncomputable def dV : Fin 2 → ℝ := ![(1 / 56 : ℝ), (1 / 224 : ℝ)]
noncomputable def TV : Fin 2 → ℝ := ![(23 / 112 : ℝ), (61 / 224 : ℝ)]
def ZV : Fin 2 → ℤ := ![5, 6]
noncomputable def HV : ℝ := (121 / 448 : ℝ)
noncomputable def EXs (c : Fin 2) : Finset (Fin 7 × ℤ) :=
  (Finset.univ ×ˢ Finset.Icc 0 (ZV c)).filter (fun q => ((q.2 : ℝ) + 1 / 8) / pr q.1 = aV c)
noncomputable def ENs (c : Fin 2) : Finset (Fin 7 × ℤ) :=
  (Finset.univ ×ˢ Finset.Icc 0 (ZV c)).filter (fun q => ((q.2 : ℝ) - 1 / 8) / pr q.1 = bV c)

theorem hp : ∀ i, 1 ≤ pr i ∧ pr i ≤ (14 : ℝ) := by intro i; fin_cases i <;> norm_num [pr]
theorem hp1 : ∀ i, 1 ≤ pr i := fun i => (hp i).1
theorem pr_0 : pr (0 : Fin 7) = (1 : ℝ) := rfl
theorem pr_1 : pr (1 : Fin 7) = (6 : ℝ) := rfl
theorem pr_2 : pr (2 : Fin 7) = (7 : ℝ) := rfl
theorem pr_3 : pr (3 : Fin 7) = (8 : ℝ) := rfl
theorem pr_4 : pr (4 : Fin 7) = (10 : ℝ) := rfl
theorem pr_5 : pr (5 : Fin 7) = (13 : ℝ) := rfl
theorem pr_6 : pr (6 : Fin 7) = (14 : ℝ) := rfl
theorem aV_0 : aV (0 : Fin 2) = (3 / 16 : ℝ) := rfl
theorem bV_0 : bV (0 : Fin 2) = (3 / 16 : ℝ) := rfl
theorem dV_0 : dV (0 : Fin 2) = (1 / 56 : ℝ) := rfl
theorem TV_0 : TV (0 : Fin 2) = (23 / 112 : ℝ) := rfl
theorem ZV_0 : ZV (0 : Fin 2) = (5 : ℤ) := rfl
theorem aV_1 : aV (1 : Fin 2) = (17 / 64 : ℝ) := rfl
theorem bV_1 : bV (1 : Fin 2) = (15 / 56 : ℝ) := rfl
theorem dV_1 : dV (1 : Fin 2) = (1 / 224 : ℝ) := rfl
theorem TV_1 : TV (1 : Fin 2) = (61 / 224 : ℝ) := rfl
theorem ZV_1 : ZV (1 : Fin 2) = (6 : ℤ) := rfl
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
  · exact ⟨(1, 1), by simp [EXs, ZV, pr, aV] <;> norm_num⟩
  · exact ⟨(3, 2), by simp [EXs, ZV, pr, aV] <;> norm_num⟩
theorem hENne : ∀ c, (ENs c).Nonempty := by
  intro c
  fin_cases c
  · exact ⟨(4, 2), by simp [ENs, ZV, pr, bV] <;> norm_num⟩
  · exact ⟨(2, 2), by simp [ENs, ZV, pr, bV] <;> norm_num⟩
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

theorem gap0 (x : Fin 7 → ℝ) (ε : ℝ) (hdev : ∀ i, |x i - pr i| ≤ ε) (hεH : ε * HV ≤ (1 / 1024 : ℝ) / 2) (t : ℝ) (h0 : 0 ≤ t)
    (hHt : t ≤ HV) (h1 : (0 : ℝ) ≤ t) (h2 : t ≤ (5 / 28 : ℝ)) (hlon : ∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)) : False := by
  rcases le_total t (127 / 1024 : ℝ) with hs0 | hs0
  · exact zone_kill_gen pr x ε HV (1 / 1024 : ℝ) hp1 hdev hεH (by norm_num) (0 : Fin 7) 0 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (0 : Fin 7))
  rcases le_total t (143 / 1024 : ℝ) with hs1 | hs1
  · exact zone_kill_gen pr x ε HV (1 / 1024 : ℝ) hp1 hdev hεH (by norm_num) (3 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (3 : Fin 7))
  rcases le_total t (1145 / 7168 : ℝ) with hs2 | hs2
  · exact zone_kill_gen pr x ε HV (1 / 1024 : ℝ) hp1 hdev hεH (by norm_num) (2 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (2 : Fin 7))
  exact zone_kill_gen pr x ε HV (1 / 1024 : ℝ) hp1 hdev hεH (by norm_num) (1 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (1 : Fin 7))
theorem gap1 (x : Fin 7 → ℝ) (ε : ℝ) (hdev : ∀ i, |x i - pr i| ≤ ε) (hεH : ε * HV ≤ (1 / 1024 : ℝ) / 2) (t : ℝ) (h0 : 0 ≤ t)
    (hHt : t ≤ HV) (h1 : (11 / 56 : ℝ) ≤ t) (h2 : t ≤ (59 / 224 : ℝ)) (hlon : ∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)) : False := by
  rcases le_total t (1083 / 5120 : ℝ) with hs0 | hs0
  · exact zone_kill_gen pr x ε HV (1 / 1024 : ℝ) hp1 hdev hεH (by norm_num) (4 : Fin 7) 2 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (4 : Fin 7))
  rcases le_total t (1593 / 7168 : ℝ) with hs1 | hs1
  · exact zone_kill_gen pr x ε HV (1 / 1024 : ℝ) hp1 hdev hεH (by norm_num) (6 : Fin 7) 3 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (6 : Fin 7))
  rcases le_total t (3187 / 13312 : ℝ) with hs2 | hs2
  · exact zone_kill_gen pr x ε HV (1 / 1024 : ℝ) hp1 hdev hεH (by norm_num) (5 : Fin 7) 3 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (5 : Fin 7))
  exact zone_kill_gen pr x ε HV (1 / 1024 : ℝ) hp1 hdev hεH (by norm_num) (3 : Fin 7) 2 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (3 : Fin 7))
theorem cov (x : Fin 7 → ℝ) (ε : ℝ) (hε : ε ≤ (1 / 12544 : ℝ)) (hdev : ∀ i, |x i - pr i| ≤ ε) :
    ∀ t : ℝ, 0 < t → t ≤ HV → (∀ c, ¬ (aV c - dV c / 2 ≤ t ∧ t ≤ bV c + dV c / 2)) →
      ¬ (∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)) := by
  intro t h0 hHt hnone hlon
  have hεH : ε * HV ≤ (1 / 1024 : ℝ) / 2 := by
    have hε0 : 0 ≤ ε := le_trans (abs_nonneg _) (hdev 0)
    have : ε * HV ≤ (1 / 12544 : ℝ) * HV := mul_le_mul_of_nonneg_right hε (by norm_num [HV])
    have h2 : (1 / 12544 : ℝ) * HV ≤ (1 / 1024 : ℝ) / 2 := by norm_num [HV]
    linarith
  have n0 := hnone (0 : Fin 2)
  rw [aV_0, bV_0, dV_0] at n0
  have n1 := hnone (1 : Fin 2)
  rw [aV_1, bV_1, dV_1] at n1
  rcases lt_or_ge t (5 / 28 : ℝ) with c0 | c0
  · exact gap0 x ε hdev hεH t h0.le hHt h0.le (by linarith) hlon
  have d0 : (11 / 56 : ℝ) < t := by
    by_contra hc; push Not at hc; exact n0 ⟨by linarith, by linarith⟩
  rcases lt_or_ge t (59 / 224 : ℝ) with c1 | c1
  · exact gap1 x ε hdev hεH t h0.le hHt d0.le (by linarith) hlon
  have d1 : (121 / 448 : ℝ) < t := by
    by_contra hc; push Not at hc; exact n1 ⟨by linarith, by linarith⟩
  have hHv : HV = (121 / 448 : ℝ) := rfl
  exact absurd (by linarith : t ≤ (121 / 448 : ℝ)) (not_le.2 d1)

theorem inst (x : Fin 7 → ℝ) (ε : ℝ) (hε : ε ≤ (1 / 12544 : ℝ)) (hdev : ∀ i, |x i - pr i| ≤ ε) :
    ∃ c₀ : Fin 2, Alive (mxOf x EXs hEXne) (mnOf x ENs hENne) c₀ ∧
      (∀ c, c < c₀ → ¬ Alive (mxOf x EXs hEXne) (mnOf x ENs hENne) c) ∧
      IsLeast {t : ℝ | 0 < t ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)} (mxOf x EXs hEXne c₀) :=
  landing_cert 2 (14 : ℝ) (by norm_num) pr x hp ε hdev aV bV dV TV ZV hab hd0 hdP haP hT hZ (hE ε hε) hcls EXs ENs hEXne hENne
    hEXdef hENdef hsepL HV hHL (cov x ε hε hdev) (1 : Fin 2) (by rw [dV_1, bV_1, aV_1]; norm_num)

noncomputable def sv : Fin 8 → ℝ := ![(1 : ℝ), (2 : ℝ), (8 : ℝ), (9 : ℝ), (10 : ℝ), (12 : ℝ), (15 : ℝ), (16 : ℝ)]
def sg : Fin 7 → Fin 8 := ![0, 2, 3, 4, 5, 6, 7]

theorem sv_0 : sv (0 : Fin 8) = (1 : ℝ) := rfl
theorem sv_1 : sv (1 : Fin 8) = (2 : ℝ) := rfl
theorem sv_2 : sv (2 : Fin 8) = (8 : ℝ) := rfl
theorem sv_3 : sv (3 : Fin 8) = (9 : ℝ) := rfl
theorem sv_4 : sv (4 : Fin 8) = (10 : ℝ) := rfl
theorem sv_5 : sv (5 : Fin 8) = (12 : ℝ) := rfl
theorem sv_6 : sv (6 : Fin 8) = (15 : ℝ) := rfl
theorem sv_7 : sv (7 : Fin 8) = (16 : ℝ) := rfl
theorem sg_0 : sg (0 : Fin 7) = (0 : Fin 8) := rfl
theorem sg_1 : sg (1 : Fin 7) = (2 : Fin 8) := rfl
theorem sg_2 : sg (2 : Fin 7) = (3 : Fin 8) := rfl
theorem sg_3 : sg (3 : Fin 7) = (4 : Fin 8) := rfl
theorem sg_4 : sg (4 : Fin 7) = (5 : Fin 8) := rfl
theorem sg_5 : sg (5 : Fin 7) = (6 : Fin 8) := rfl
theorem sg_6 : sg (6 : Fin 7) = (7 : Fin 8) := rfl

theorem inst_arr (v : Fin 8 → ℝ) (η : ℝ) (hη : η ≤ (1 / 25088 : ℝ)) (hv : ∀ j, |v j - sv j| ≤ η) :
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

end Fresh.CertRR.R13241



/-!
# Landing certificate `CertRR.R13247`: speeds (1, 2, 8, 9, 10, 12, 15, 16), subject index 7

Generated 2026-10-24 by `experiments/n8/cert_gen_v1.py` (exact Fractions).  Baseline readings [15, 14, 8, 7, 6, 4, 1].  Components up to the first wide one: 1.
Radius: speeds within `η ≤ 1/11520` of the baseline speeds, giving `ε = 2η ≤ 1/5760`.  Covering margin `μ = 1/256`.
`hcov` is **[PROVISIONAL: covering]**, supporting the claim that the first lonely instant of this subject is the largest exit of the first alive component.
Result `inst_arr`: for such `v`, the subject has a first isolation (a least element over all `t > 0`).  Grades: [L].
-/

open Classical

namespace Fresh.CertRR.R13247

open Fresh Fresh.LandingCert Fresh.LandingRule

noncomputable def pr : Fin 7 → ℝ := ![(15 : ℝ), (14 : ℝ), (8 : ℝ), (7 : ℝ), (6 : ℝ), (4 : ℝ), (1 : ℝ)]
noncomputable def aV : Fin 1 → ℝ := ![(3 / 16 : ℝ)]
noncomputable def bV : Fin 1 → ℝ := ![(23 / 120 : ℝ)]
noncomputable def dV : Fin 1 → ℝ := ![(1 / 120 : ℝ)]
noncomputable def TV : Fin 1 → ℝ := ![(1 / 5 : ℝ)]
def ZV : Fin 1 → ℤ := ![5]
noncomputable def HV : ℝ := (47 / 240 : ℝ)
noncomputable def EXs (c : Fin 1) : Finset (Fin 7 × ℤ) :=
  (Finset.univ ×ˢ Finset.Icc 0 (ZV c)).filter (fun q => ((q.2 : ℝ) + 1 / 8) / pr q.1 = aV c)
noncomputable def ENs (c : Fin 1) : Finset (Fin 7 × ℤ) :=
  (Finset.univ ×ˢ Finset.Icc 0 (ZV c)).filter (fun q => ((q.2 : ℝ) - 1 / 8) / pr q.1 = bV c)

theorem hp : ∀ i, 1 ≤ pr i ∧ pr i ≤ (15 : ℝ) := by intro i; fin_cases i <;> norm_num [pr]
theorem hp1 : ∀ i, 1 ≤ pr i := fun i => (hp i).1
theorem pr_0 : pr (0 : Fin 7) = (15 : ℝ) := rfl
theorem pr_1 : pr (1 : Fin 7) = (14 : ℝ) := rfl
theorem pr_2 : pr (2 : Fin 7) = (8 : ℝ) := rfl
theorem pr_3 : pr (3 : Fin 7) = (7 : ℝ) := rfl
theorem pr_4 : pr (4 : Fin 7) = (6 : ℝ) := rfl
theorem pr_5 : pr (5 : Fin 7) = (4 : ℝ) := rfl
theorem pr_6 : pr (6 : Fin 7) = (1 : ℝ) := rfl
theorem aV_0 : aV (0 : Fin 1) = (3 / 16 : ℝ) := rfl
theorem bV_0 : bV (0 : Fin 1) = (23 / 120 : ℝ) := rfl
theorem dV_0 : dV (0 : Fin 1) = (1 / 120 : ℝ) := rfl
theorem TV_0 : TV (0 : Fin 1) = (1 / 5 : ℝ) := rfl
theorem ZV_0 : ZV (0 : Fin 1) = (5 : ℤ) := rfl
theorem hab : ∀ c, aV c ≤ bV c := by intro c; fin_cases c <;> norm_num [aV, bV]
theorem hd0 : ∀ c, 0 < dV c := by intro c; fin_cases c <;> norm_num [dV]
theorem hdP : ∀ c, dV c ≤ 1 / (4 * (15 : ℝ)) := by intro c; fin_cases c <;> norm_num [dV]
theorem haP : ∀ c, dV c < aV c := by intro c; fin_cases c <;> norm_num [dV, aV]
theorem hT : ∀ c, bV c + dV c ≤ TV c := by intro c; fin_cases c <;> norm_num [bV, dV, TV]
theorem hZ : ∀ c, ((15 : ℝ) + 1) * TV c + 1 ≤ (ZV c : ℝ) := by intro c; fin_cases c <;> norm_num [TV, ZV]
theorem hE (ε : ℝ) (hε : ε ≤ (1 / 5760 : ℝ)) : ∀ c, 8 * ((ZV c : ℝ) + 1) * ε ≤ dV c := by
  intro c; fin_cases c <;> norm_num [ZV, dV] <;> linarith
theorem hcls : ∀ c i, ∀ z : ℤ, 0 ≤ z → z ≤ ZV c →
    ((z : ℝ) + 1 / 8) / pr i ≤ aV c - dV c ∨ bV c + dV c ≤ ((z : ℝ) - 1 / 8) / pr i ∨
      ((z : ℝ) + 1 / 8) / pr i = aV c ∨ ((z : ℝ) - 1 / 8) / pr i = bV c := by
  intro c i z h0 h1
  fin_cases c <;> fin_cases i <;> simp [ZV] at h1 <;> interval_cases z <;> norm_num [pr, aV, bV, dV]
theorem hEXne : ∀ c, (EXs c).Nonempty := by
  intro c
  fin_cases c
  · exact ⟨(4, 1), by simp [EXs, ZV, pr, aV] <;> norm_num⟩
theorem hENne : ∀ c, (ENs c).Nonempty := by
  intro c
  fin_cases c
  · exact ⟨(0, 3), by simp [ENs, ZV, pr, bV] <;> norm_num⟩
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
    (hHt : t ≤ HV) (h1 : (0 : ℝ) ≤ t) (h2 : t ≤ (11 / 60 : ℝ)) (hlon : ∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)) : False := by
  rcases le_total t (31 / 256 : ℝ) with hs0 | hs0
  · exact zone_kill_gen pr x ε HV (1 / 256 : ℝ) hp1 hdev hεH (by norm_num) (6 : Fin 7) 0 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (6 : Fin 7))
  rcases le_total t (35 / 256 : ℝ) with hs1 | hs1
  · exact zone_kill_gen pr x ε HV (1 / 256 : ℝ) hp1 hdev hεH (by norm_num) (2 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (2 : Fin 7))
  rcases le_total t (281 / 1792 : ℝ) with hs2 | hs2
  · exact zone_kill_gen pr x ε HV (1 / 256 : ℝ) hp1 hdev hεH (by norm_num) (3 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (3 : Fin 7))
  exact zone_kill_gen pr x ε HV (1 / 256 : ℝ) hp1 hdev hεH (by norm_num) (4 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (4 : Fin 7))
theorem cov (x : Fin 7 → ℝ) (ε : ℝ) (hε : ε ≤ (1 / 5760 : ℝ)) (hdev : ∀ i, |x i - pr i| ≤ ε) :
    ∀ t : ℝ, 0 < t → t ≤ HV → (∀ c, ¬ (aV c - dV c / 2 ≤ t ∧ t ≤ bV c + dV c / 2)) →
      ¬ (∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)) := by
  intro t h0 hHt hnone hlon
  have hεH : ε * HV ≤ (1 / 256 : ℝ) / 2 := by
    have hε0 : 0 ≤ ε := le_trans (abs_nonneg _) (hdev 0)
    have : ε * HV ≤ (1 / 5760 : ℝ) * HV := mul_le_mul_of_nonneg_right hε (by norm_num [HV])
    have h2 : (1 / 5760 : ℝ) * HV ≤ (1 / 256 : ℝ) / 2 := by norm_num [HV]
    linarith
  have n0 := hnone (0 : Fin 1)
  rw [aV_0, bV_0, dV_0] at n0
  rcases lt_or_ge t (11 / 60 : ℝ) with c0 | c0
  · exact gap0 x ε hdev hεH t h0.le hHt h0.le (by linarith) hlon
  have d0 : (47 / 240 : ℝ) < t := by
    by_contra hc; push Not at hc; exact n0 ⟨by linarith, by linarith⟩
  have hHv : HV = (47 / 240 : ℝ) := rfl
  exact absurd (by linarith : t ≤ (47 / 240 : ℝ)) (not_le.2 d0)

theorem inst (x : Fin 7 → ℝ) (ε : ℝ) (hε : ε ≤ (1 / 5760 : ℝ)) (hdev : ∀ i, |x i - pr i| ≤ ε) :
    ∃ c₀ : Fin 1, Alive (mxOf x EXs hEXne) (mnOf x ENs hENne) c₀ ∧
      (∀ c, c < c₀ → ¬ Alive (mxOf x EXs hEXne) (mnOf x ENs hENne) c) ∧
      IsLeast {t : ℝ | 0 < t ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)} (mxOf x EXs hEXne c₀) :=
  landing_cert 1 (15 : ℝ) (by norm_num) pr x hp ε hdev aV bV dV TV ZV hab hd0 hdP haP hT hZ (hE ε hε) hcls EXs ENs hEXne hENne
    hEXdef hENdef hsepL HV hHL (cov x ε hε hdev) (0 : Fin 1) (by rw [dV_0, bV_0, aV_0]; norm_num)

noncomputable def sv : Fin 8 → ℝ := ![(1 : ℝ), (2 : ℝ), (8 : ℝ), (9 : ℝ), (10 : ℝ), (12 : ℝ), (15 : ℝ), (16 : ℝ)]
def sg : Fin 7 → Fin 8 := ![0, 1, 2, 3, 4, 5, 6]

theorem sv_0 : sv (0 : Fin 8) = (1 : ℝ) := rfl
theorem sv_1 : sv (1 : Fin 8) = (2 : ℝ) := rfl
theorem sv_2 : sv (2 : Fin 8) = (8 : ℝ) := rfl
theorem sv_3 : sv (3 : Fin 8) = (9 : ℝ) := rfl
theorem sv_4 : sv (4 : Fin 8) = (10 : ℝ) := rfl
theorem sv_5 : sv (5 : Fin 8) = (12 : ℝ) := rfl
theorem sv_6 : sv (6 : Fin 8) = (15 : ℝ) := rfl
theorem sv_7 : sv (7 : Fin 8) = (16 : ℝ) := rfl
theorem sg_0 : sg (0 : Fin 7) = (0 : Fin 8) := rfl
theorem sg_1 : sg (1 : Fin 7) = (1 : Fin 8) := rfl
theorem sg_2 : sg (2 : Fin 7) = (2 : Fin 8) := rfl
theorem sg_3 : sg (3 : Fin 7) = (3 : Fin 8) := rfl
theorem sg_4 : sg (4 : Fin 7) = (4 : Fin 8) := rfl
theorem sg_5 : sg (5 : Fin 7) = (5 : Fin 8) := rfl
theorem sg_6 : sg (6 : Fin 7) = (6 : Fin 8) := rfl

theorem inst_arr (v : Fin 8 → ℝ) (η : ℝ) (hη : η ≤ (1 / 11520 : ℝ)) (hv : ∀ j, |v j - sv j| ≤ η) :
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

end Fresh.CertRR.R13247



/-!
# Landing certificate `CertRR.R13251`: speeds (1, 2, 8, 9, 10, 13, 14, 15), subject index 3

Generated 2026-10-24 by `experiments/n8/cert_gen_v1.py` (exact Fractions).  Baseline readings [8, 7, 1, 1, 4, 5, 6].  Components up to the first wide one: 1.
Radius: speeds within `η ≤ 1/5376` of the baseline speeds, giving `ε = 2η ≤ 1/2688`.  Covering margin `μ = 1/512`.
`hcov` is **[PROVISIONAL: covering]**, supporting the claim that the first lonely instant of this subject is the largest exit of the first alive component.
Result `inst_arr`: for such `v`, the subject has a first isolation (a least element over all `t > 0`).  Grades: [L].
-/

open Classical

namespace Fresh.CertRR.R13251

open Fresh Fresh.LandingCert Fresh.LandingRule

noncomputable def pr : Fin 7 → ℝ := ![(8 : ℝ), (7 : ℝ), (1 : ℝ), (1 : ℝ), (4 : ℝ), (5 : ℝ), (6 : ℝ)]
noncomputable def aV : Fin 1 → ℝ := ![(17 / 56 : ℝ)]
noncomputable def bV : Fin 1 → ℝ := ![(5 / 16 : ℝ)]
noncomputable def dV : Fin 1 → ℝ := ![(1 / 56 : ℝ)]
noncomputable def TV : Fin 1 → ℝ := ![(37 / 112 : ℝ)]
def ZV : Fin 1 → ℤ := ![5]
noncomputable def HV : ℝ := (9 / 28 : ℝ)
noncomputable def EXs (c : Fin 1) : Finset (Fin 7 × ℤ) :=
  (Finset.univ ×ˢ Finset.Icc 0 (ZV c)).filter (fun q => ((q.2 : ℝ) + 1 / 8) / pr q.1 = aV c)
noncomputable def ENs (c : Fin 1) : Finset (Fin 7 × ℤ) :=
  (Finset.univ ×ˢ Finset.Icc 0 (ZV c)).filter (fun q => ((q.2 : ℝ) - 1 / 8) / pr q.1 = bV c)

theorem hp : ∀ i, 1 ≤ pr i ∧ pr i ≤ (8 : ℝ) := by intro i; fin_cases i <;> norm_num [pr]
theorem hp1 : ∀ i, 1 ≤ pr i := fun i => (hp i).1
theorem pr_0 : pr (0 : Fin 7) = (8 : ℝ) := rfl
theorem pr_1 : pr (1 : Fin 7) = (7 : ℝ) := rfl
theorem pr_2 : pr (2 : Fin 7) = (1 : ℝ) := rfl
theorem pr_3 : pr (3 : Fin 7) = (1 : ℝ) := rfl
theorem pr_4 : pr (4 : Fin 7) = (4 : ℝ) := rfl
theorem pr_5 : pr (5 : Fin 7) = (5 : ℝ) := rfl
theorem pr_6 : pr (6 : Fin 7) = (6 : ℝ) := rfl
theorem aV_0 : aV (0 : Fin 1) = (17 / 56 : ℝ) := rfl
theorem bV_0 : bV (0 : Fin 1) = (5 / 16 : ℝ) := rfl
theorem dV_0 : dV (0 : Fin 1) = (1 / 56 : ℝ) := rfl
theorem TV_0 : TV (0 : Fin 1) = (37 / 112 : ℝ) := rfl
theorem ZV_0 : ZV (0 : Fin 1) = (5 : ℤ) := rfl
theorem hab : ∀ c, aV c ≤ bV c := by intro c; fin_cases c <;> norm_num [aV, bV]
theorem hd0 : ∀ c, 0 < dV c := by intro c; fin_cases c <;> norm_num [dV]
theorem hdP : ∀ c, dV c ≤ 1 / (4 * (8 : ℝ)) := by intro c; fin_cases c <;> norm_num [dV]
theorem haP : ∀ c, dV c < aV c := by intro c; fin_cases c <;> norm_num [dV, aV]
theorem hT : ∀ c, bV c + dV c ≤ TV c := by intro c; fin_cases c <;> norm_num [bV, dV, TV]
theorem hZ : ∀ c, ((8 : ℝ) + 1) * TV c + 1 ≤ (ZV c : ℝ) := by intro c; fin_cases c <;> norm_num [TV, ZV]
theorem hE (ε : ℝ) (hε : ε ≤ (1 / 2688 : ℝ)) : ∀ c, 8 * ((ZV c : ℝ) + 1) * ε ≤ dV c := by
  intro c; fin_cases c <;> norm_num [ZV, dV] <;> linarith
theorem hcls : ∀ c i, ∀ z : ℤ, 0 ≤ z → z ≤ ZV c →
    ((z : ℝ) + 1 / 8) / pr i ≤ aV c - dV c ∨ bV c + dV c ≤ ((z : ℝ) - 1 / 8) / pr i ∨
      ((z : ℝ) + 1 / 8) / pr i = aV c ∨ ((z : ℝ) - 1 / 8) / pr i = bV c := by
  intro c i z h0 h1
  fin_cases c <;> fin_cases i <;> simp [ZV] at h1 <;> interval_cases z <;> norm_num [pr, aV, bV, dV]
theorem hEXne : ∀ c, (EXs c).Nonempty := by
  intro c
  fin_cases c
  · exact ⟨(1, 2), by simp [EXs, ZV, pr, aV] <;> norm_num⟩
theorem hENne : ∀ c, (ENs c).Nonempty := by
  intro c
  fin_cases c
  · exact ⟨(6, 2), by simp [ENs, ZV, pr, bV] <;> norm_num⟩
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
  · exact zone_kill_gen pr x ε HV (1 / 512 : ℝ) hp1 hdev hεH (by norm_num) (2 : Fin 7) 0 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (2 : Fin 7))
  rcases le_total t (71 / 512 : ℝ) with hs1 | hs1
  · exact zone_kill_gen pr x ε HV (1 / 512 : ℝ) hp1 hdev hεH (by norm_num) (0 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (0 : Fin 7))
  rcases le_total t (569 / 3584 : ℝ) with hs2 | hs2
  · exact zone_kill_gen pr x ε HV (1 / 512 : ℝ) hp1 hdev hεH (by norm_num) (1 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (1 : Fin 7))
  rcases le_total t (95 / 512 : ℝ) with hs3 | hs3
  · exact zone_kill_gen pr x ε HV (1 / 512 : ℝ) hp1 hdev hεH (by norm_num) (6 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (6 : Fin 7))
  rcases le_total t (571 / 2560 : ℝ) with hs4 | hs4
  · exact zone_kill_gen pr x ε HV (1 / 512 : ℝ) hp1 hdev hεH (by norm_num) (5 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (5 : Fin 7))
  rcases le_total t (143 / 512 : ℝ) with hs5 | hs5
  · exact zone_kill_gen pr x ε HV (1 / 512 : ℝ) hp1 hdev hεH (by norm_num) (4 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (4 : Fin 7))
  exact zone_kill_gen pr x ε HV (1 / 512 : ℝ) hp1 hdev hεH (by norm_num) (1 : Fin 7) 2 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (1 : Fin 7))
theorem cov (x : Fin 7 → ℝ) (ε : ℝ) (hε : ε ≤ (1 / 2688 : ℝ)) (hdev : ∀ i, |x i - pr i| ≤ ε) :
    ∀ t : ℝ, 0 < t → t ≤ HV → (∀ c, ¬ (aV c - dV c / 2 ≤ t ∧ t ≤ bV c + dV c / 2)) →
      ¬ (∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)) := by
  intro t h0 hHt hnone hlon
  have hεH : ε * HV ≤ (1 / 512 : ℝ) / 2 := by
    have hε0 : 0 ≤ ε := le_trans (abs_nonneg _) (hdev 0)
    have : ε * HV ≤ (1 / 2688 : ℝ) * HV := mul_le_mul_of_nonneg_right hε (by norm_num [HV])
    have h2 : (1 / 2688 : ℝ) * HV ≤ (1 / 512 : ℝ) / 2 := by norm_num [HV]
    linarith
  have n0 := hnone (0 : Fin 1)
  rw [aV_0, bV_0, dV_0] at n0
  rcases lt_or_ge t (33 / 112 : ℝ) with c0 | c0
  · exact gap0 x ε hdev hεH t h0.le hHt h0.le (by linarith) hlon
  have d0 : (9 / 28 : ℝ) < t := by
    by_contra hc; push Not at hc; exact n0 ⟨by linarith, by linarith⟩
  have hHv : HV = (9 / 28 : ℝ) := rfl
  exact absurd (by linarith : t ≤ (9 / 28 : ℝ)) (not_le.2 d0)

theorem inst (x : Fin 7 → ℝ) (ε : ℝ) (hε : ε ≤ (1 / 2688 : ℝ)) (hdev : ∀ i, |x i - pr i| ≤ ε) :
    ∃ c₀ : Fin 1, Alive (mxOf x EXs hEXne) (mnOf x ENs hENne) c₀ ∧
      (∀ c, c < c₀ → ¬ Alive (mxOf x EXs hEXne) (mnOf x ENs hENne) c) ∧
      IsLeast {t : ℝ | 0 < t ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)} (mxOf x EXs hEXne c₀) :=
  landing_cert 1 (8 : ℝ) (by norm_num) pr x hp ε hdev aV bV dV TV ZV hab hd0 hdP haP hT hZ (hE ε hε) hcls EXs ENs hEXne hENne
    hEXdef hENdef hsepL HV hHL (cov x ε hε hdev) (0 : Fin 1) (by rw [dV_0, bV_0, aV_0]; norm_num)

noncomputable def sv : Fin 8 → ℝ := ![(1 : ℝ), (2 : ℝ), (8 : ℝ), (9 : ℝ), (10 : ℝ), (13 : ℝ), (14 : ℝ), (15 : ℝ)]
def sg : Fin 7 → Fin 8 := ![0, 1, 2, 4, 5, 6, 7]

theorem sv_0 : sv (0 : Fin 8) = (1 : ℝ) := rfl
theorem sv_1 : sv (1 : Fin 8) = (2 : ℝ) := rfl
theorem sv_2 : sv (2 : Fin 8) = (8 : ℝ) := rfl
theorem sv_3 : sv (3 : Fin 8) = (9 : ℝ) := rfl
theorem sv_4 : sv (4 : Fin 8) = (10 : ℝ) := rfl
theorem sv_5 : sv (5 : Fin 8) = (13 : ℝ) := rfl
theorem sv_6 : sv (6 : Fin 8) = (14 : ℝ) := rfl
theorem sv_7 : sv (7 : Fin 8) = (15 : ℝ) := rfl
theorem sg_0 : sg (0 : Fin 7) = (0 : Fin 8) := rfl
theorem sg_1 : sg (1 : Fin 7) = (1 : Fin 8) := rfl
theorem sg_2 : sg (2 : Fin 7) = (2 : Fin 8) := rfl
theorem sg_3 : sg (3 : Fin 7) = (4 : Fin 8) := rfl
theorem sg_4 : sg (4 : Fin 7) = (5 : Fin 8) := rfl
theorem sg_5 : sg (5 : Fin 7) = (6 : Fin 8) := rfl
theorem sg_6 : sg (6 : Fin 7) = (7 : Fin 8) := rfl

theorem inst_arr (v : Fin 8 → ℝ) (η : ℝ) (hη : η ≤ (1 / 5376 : ℝ)) (hv : ∀ j, |v j - sv j| ≤ η) :
    ∃ c₀ : Fin 1, Alive (mxOf (fun i => |v (sg i) - v (3 : Fin 8)|) EXs hEXne) (mnOf (fun i => |v (sg i) - v (3 : Fin 8)|) ENs hENne) c₀ ∧
      (∀ c, c < c₀ → ¬ Alive (mxOf (fun i => |v (sg i) - v (3 : Fin 8)|) EXs hEXne) (mnOf (fun i => |v (sg i) - v (3 : Fin 8)|) ENs hENne) c) ∧
      IsLeast {t : ℝ | 0 < t ∧ IsolatedAt v (3 : Fin 8) t} (mxOf (fun i => |v (sg i) - v (3 : Fin 8)|) EXs hEXne c₀) := by
  have hσk : ∀ i, sg i ≠ (3 : Fin 8) := by decide
  have hσ : ∀ j : Fin 8, j ≠ (3 : Fin 8) → ∃ i, sg i = j := by decide
  have hpr : ∀ i, pr i = |sv (sg i) - sv (3 : Fin 8)| := by
    intro i; rcases fin7_cases i with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6, sv_0, sv_1, sv_2, sv_3, sv_4, sv_5, sv_6, sv_7, sg_0, sg_1, sg_2, sg_3, sg_4, sg_5, sg_6]
  have hdev : ∀ i, |(|v (sg i) - v (3 : Fin 8)| - pr i)| ≤ 2 * η := by
    intro i; rw [hpr i]; exact reading_dev v sv η hv (sg i) (3 : Fin 8)
  obtain ⟨c₀, hal, hbf, hT0⟩ := inst (fun i => |v (sg i) - v (3 : Fin 8)|) (2 * η) (by linarith) hdev
  have hset : {t : ℝ | 0 < t ∧ IsolatedAt v (3 : Fin 8) t} =
      {t : ℝ | 0 < t ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (|v (sg i) - v (3 : Fin 8)| * t)} := by
    ext t; simp only [Set.mem_setOf_eq]; rw [iso_iff_readings v (3 : Fin 8) sg hσk hσ t]
  rw [hset]; exact ⟨c₀, hal, hbf, hT0⟩

#print axioms inst_arr

end Fresh.CertRR.R13251



/-!
# Landing certificate `CertRR.R13256`: speeds (1, 2, 8, 9, 10, 13, 14, 16), subject index 0

Generated 2026-10-24 by `experiments/n8/cert_gen_v1.py` (exact Fractions).  Baseline readings [1, 7, 8, 9, 12, 13, 15].  Components up to the first wide one: 1.
Radius: speeds within `η ≤ 1/11520` of the baseline speeds, giving `ε = 2η ≤ 1/5760`.  Covering margin `μ = 1/512`.
`hcov` is **[PROVISIONAL: covering]**, supporting the claim that the first lonely instant of this subject is the largest exit of the first alive component.
Result `inst_arr`: for such `v`, the subject has a first isolation (a least element over all `t > 0`).  Grades: [L].
-/

open Classical

namespace Fresh.CertRR.R13256

open Fresh Fresh.LandingCert Fresh.LandingRule

noncomputable def pr : Fin 7 → ℝ := ![(1 : ℝ), (7 : ℝ), (8 : ℝ), (9 : ℝ), (12 : ℝ), (13 : ℝ), (15 : ℝ)]
noncomputable def aV : Fin 1 → ℝ := ![(17 / 96 : ℝ)]
noncomputable def bV : Fin 1 → ℝ := ![(23 / 120 : ℝ)]
noncomputable def dV : Fin 1 → ℝ := ![(1 / 120 : ℝ)]
noncomputable def TV : Fin 1 → ℝ := ![(1 / 5 : ℝ)]
def ZV : Fin 1 → ℤ := ![5]
noncomputable def HV : ℝ := (47 / 240 : ℝ)
noncomputable def EXs (c : Fin 1) : Finset (Fin 7 × ℤ) :=
  (Finset.univ ×ˢ Finset.Icc 0 (ZV c)).filter (fun q => ((q.2 : ℝ) + 1 / 8) / pr q.1 = aV c)
noncomputable def ENs (c : Fin 1) : Finset (Fin 7 × ℤ) :=
  (Finset.univ ×ˢ Finset.Icc 0 (ZV c)).filter (fun q => ((q.2 : ℝ) - 1 / 8) / pr q.1 = bV c)

theorem hp : ∀ i, 1 ≤ pr i ∧ pr i ≤ (15 : ℝ) := by intro i; fin_cases i <;> norm_num [pr]
theorem hp1 : ∀ i, 1 ≤ pr i := fun i => (hp i).1
theorem pr_0 : pr (0 : Fin 7) = (1 : ℝ) := rfl
theorem pr_1 : pr (1 : Fin 7) = (7 : ℝ) := rfl
theorem pr_2 : pr (2 : Fin 7) = (8 : ℝ) := rfl
theorem pr_3 : pr (3 : Fin 7) = (9 : ℝ) := rfl
theorem pr_4 : pr (4 : Fin 7) = (12 : ℝ) := rfl
theorem pr_5 : pr (5 : Fin 7) = (13 : ℝ) := rfl
theorem pr_6 : pr (6 : Fin 7) = (15 : ℝ) := rfl
theorem aV_0 : aV (0 : Fin 1) = (17 / 96 : ℝ) := rfl
theorem bV_0 : bV (0 : Fin 1) = (23 / 120 : ℝ) := rfl
theorem dV_0 : dV (0 : Fin 1) = (1 / 120 : ℝ) := rfl
theorem TV_0 : TV (0 : Fin 1) = (1 / 5 : ℝ) := rfl
theorem ZV_0 : ZV (0 : Fin 1) = (5 : ℤ) := rfl
theorem hab : ∀ c, aV c ≤ bV c := by intro c; fin_cases c <;> norm_num [aV, bV]
theorem hd0 : ∀ c, 0 < dV c := by intro c; fin_cases c <;> norm_num [dV]
theorem hdP : ∀ c, dV c ≤ 1 / (4 * (15 : ℝ)) := by intro c; fin_cases c <;> norm_num [dV]
theorem haP : ∀ c, dV c < aV c := by intro c; fin_cases c <;> norm_num [dV, aV]
theorem hT : ∀ c, bV c + dV c ≤ TV c := by intro c; fin_cases c <;> norm_num [bV, dV, TV]
theorem hZ : ∀ c, ((15 : ℝ) + 1) * TV c + 1 ≤ (ZV c : ℝ) := by intro c; fin_cases c <;> norm_num [TV, ZV]
theorem hE (ε : ℝ) (hε : ε ≤ (1 / 5760 : ℝ)) : ∀ c, 8 * ((ZV c : ℝ) + 1) * ε ≤ dV c := by
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
  · exact ⟨(6, 3), by simp [ENs, ZV, pr, bV] <;> norm_num⟩
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
    (hHt : t ≤ HV) (h1 : (0 : ℝ) ≤ t) (h2 : t ≤ (83 / 480 : ℝ)) (hlon : ∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)) : False := by
  rcases le_total t (63 / 512 : ℝ) with hs0 | hs0
  · exact zone_kill_gen pr x ε HV (1 / 512 : ℝ) hp1 hdev hεH (by norm_num) (0 : Fin 7) 0 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (0 : Fin 7))
  rcases le_total t (71 / 512 : ℝ) with hs1 | hs1
  · exact zone_kill_gen pr x ε HV (1 / 512 : ℝ) hp1 hdev hεH (by norm_num) (2 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (2 : Fin 7))
  rcases le_total t (569 / 3584 : ℝ) with hs2 | hs2
  · exact zone_kill_gen pr x ε HV (1 / 512 : ℝ) hp1 hdev hεH (by norm_num) (1 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (1 : Fin 7))
  exact zone_kill_gen pr x ε HV (1 / 512 : ℝ) hp1 hdev hεH (by norm_num) (4 : Fin 7) 2 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (4 : Fin 7))
theorem cov (x : Fin 7 → ℝ) (ε : ℝ) (hε : ε ≤ (1 / 5760 : ℝ)) (hdev : ∀ i, |x i - pr i| ≤ ε) :
    ∀ t : ℝ, 0 < t → t ≤ HV → (∀ c, ¬ (aV c - dV c / 2 ≤ t ∧ t ≤ bV c + dV c / 2)) →
      ¬ (∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)) := by
  intro t h0 hHt hnone hlon
  have hεH : ε * HV ≤ (1 / 512 : ℝ) / 2 := by
    have hε0 : 0 ≤ ε := le_trans (abs_nonneg _) (hdev 0)
    have : ε * HV ≤ (1 / 5760 : ℝ) * HV := mul_le_mul_of_nonneg_right hε (by norm_num [HV])
    have h2 : (1 / 5760 : ℝ) * HV ≤ (1 / 512 : ℝ) / 2 := by norm_num [HV]
    linarith
  have n0 := hnone (0 : Fin 1)
  rw [aV_0, bV_0, dV_0] at n0
  rcases lt_or_ge t (83 / 480 : ℝ) with c0 | c0
  · exact gap0 x ε hdev hεH t h0.le hHt h0.le (by linarith) hlon
  have d0 : (47 / 240 : ℝ) < t := by
    by_contra hc; push Not at hc; exact n0 ⟨by linarith, by linarith⟩
  have hHv : HV = (47 / 240 : ℝ) := rfl
  exact absurd (by linarith : t ≤ (47 / 240 : ℝ)) (not_le.2 d0)

theorem inst (x : Fin 7 → ℝ) (ε : ℝ) (hε : ε ≤ (1 / 5760 : ℝ)) (hdev : ∀ i, |x i - pr i| ≤ ε) :
    ∃ c₀ : Fin 1, Alive (mxOf x EXs hEXne) (mnOf x ENs hENne) c₀ ∧
      (∀ c, c < c₀ → ¬ Alive (mxOf x EXs hEXne) (mnOf x ENs hENne) c) ∧
      IsLeast {t : ℝ | 0 < t ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)} (mxOf x EXs hEXne c₀) :=
  landing_cert 1 (15 : ℝ) (by norm_num) pr x hp ε hdev aV bV dV TV ZV hab hd0 hdP haP hT hZ (hE ε hε) hcls EXs ENs hEXne hENne
    hEXdef hENdef hsepL HV hHL (cov x ε hε hdev) (0 : Fin 1) (by rw [dV_0, bV_0, aV_0]; norm_num)

noncomputable def sv : Fin 8 → ℝ := ![(1 : ℝ), (2 : ℝ), (8 : ℝ), (9 : ℝ), (10 : ℝ), (13 : ℝ), (14 : ℝ), (16 : ℝ)]
def sg : Fin 7 → Fin 8 := ![1, 2, 3, 4, 5, 6, 7]

theorem sv_0 : sv (0 : Fin 8) = (1 : ℝ) := rfl
theorem sv_1 : sv (1 : Fin 8) = (2 : ℝ) := rfl
theorem sv_2 : sv (2 : Fin 8) = (8 : ℝ) := rfl
theorem sv_3 : sv (3 : Fin 8) = (9 : ℝ) := rfl
theorem sv_4 : sv (4 : Fin 8) = (10 : ℝ) := rfl
theorem sv_5 : sv (5 : Fin 8) = (13 : ℝ) := rfl
theorem sv_6 : sv (6 : Fin 8) = (14 : ℝ) := rfl
theorem sv_7 : sv (7 : Fin 8) = (16 : ℝ) := rfl
theorem sg_0 : sg (0 : Fin 7) = (1 : Fin 8) := rfl
theorem sg_1 : sg (1 : Fin 7) = (2 : Fin 8) := rfl
theorem sg_2 : sg (2 : Fin 7) = (3 : Fin 8) := rfl
theorem sg_3 : sg (3 : Fin 7) = (4 : Fin 8) := rfl
theorem sg_4 : sg (4 : Fin 7) = (5 : Fin 8) := rfl
theorem sg_5 : sg (5 : Fin 7) = (6 : Fin 8) := rfl
theorem sg_6 : sg (6 : Fin 7) = (7 : Fin 8) := rfl

theorem inst_arr (v : Fin 8 → ℝ) (η : ℝ) (hη : η ≤ (1 / 11520 : ℝ)) (hv : ∀ j, |v j - sv j| ≤ η) :
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

end Fresh.CertRR.R13256



/-!
# Landing certificate `CertRR.R13258`: speeds (1, 2, 8, 9, 10, 13, 14, 16), subject index 2

Generated 2026-10-24 by `experiments/n8/cert_gen_v1.py` (exact Fractions).  Baseline readings [7, 6, 1, 2, 5, 6, 8].  Components up to the first wide one: 1.
Radius: speeds within `η ≤ 1/5120` of the baseline speeds, giving `ε = 2η ≤ 1/2560`.  Covering margin `μ = 1/256`.
`hcov` is **[PROVISIONAL: covering]**, supporting the claim that the first lonely instant of this subject is the largest exit of the first alive component.
Result `inst_arr`: for such `v`, the subject has a first isolation (a least element over all `t > 0`).  Grades: [L].
-/

open Classical

namespace Fresh.CertRR.R13258

open Fresh Fresh.LandingCert Fresh.LandingRule

noncomputable def pr : Fin 7 → ℝ := ![(7 : ℝ), (6 : ℝ), (1 : ℝ), (2 : ℝ), (5 : ℝ), (6 : ℝ), (8 : ℝ)]
noncomputable def aV : Fin 1 → ℝ := ![(9 / 40 : ℝ)]
noncomputable def bV : Fin 1 → ℝ := ![(15 / 64 : ℝ)]
noncomputable def dV : Fin 1 → ℝ := ![(1 / 64 : ℝ)]
noncomputable def TV : Fin 1 → ℝ := ![(1 / 4 : ℝ)]
def ZV : Fin 1 → ℤ := ![4]
noncomputable def HV : ℝ := (31 / 128 : ℝ)
noncomputable def EXs (c : Fin 1) : Finset (Fin 7 × ℤ) :=
  (Finset.univ ×ˢ Finset.Icc 0 (ZV c)).filter (fun q => ((q.2 : ℝ) + 1 / 8) / pr q.1 = aV c)
noncomputable def ENs (c : Fin 1) : Finset (Fin 7 × ℤ) :=
  (Finset.univ ×ˢ Finset.Icc 0 (ZV c)).filter (fun q => ((q.2 : ℝ) - 1 / 8) / pr q.1 = bV c)

theorem hp : ∀ i, 1 ≤ pr i ∧ pr i ≤ (8 : ℝ) := by intro i; fin_cases i <;> norm_num [pr]
theorem hp1 : ∀ i, 1 ≤ pr i := fun i => (hp i).1
theorem pr_0 : pr (0 : Fin 7) = (7 : ℝ) := rfl
theorem pr_1 : pr (1 : Fin 7) = (6 : ℝ) := rfl
theorem pr_2 : pr (2 : Fin 7) = (1 : ℝ) := rfl
theorem pr_3 : pr (3 : Fin 7) = (2 : ℝ) := rfl
theorem pr_4 : pr (4 : Fin 7) = (5 : ℝ) := rfl
theorem pr_5 : pr (5 : Fin 7) = (6 : ℝ) := rfl
theorem pr_6 : pr (6 : Fin 7) = (8 : ℝ) := rfl
theorem aV_0 : aV (0 : Fin 1) = (9 / 40 : ℝ) := rfl
theorem bV_0 : bV (0 : Fin 1) = (15 / 64 : ℝ) := rfl
theorem dV_0 : dV (0 : Fin 1) = (1 / 64 : ℝ) := rfl
theorem TV_0 : TV (0 : Fin 1) = (1 / 4 : ℝ) := rfl
theorem ZV_0 : ZV (0 : Fin 1) = (4 : ℤ) := rfl
theorem hab : ∀ c, aV c ≤ bV c := by intro c; fin_cases c <;> norm_num [aV, bV]
theorem hd0 : ∀ c, 0 < dV c := by intro c; fin_cases c <;> norm_num [dV]
theorem hdP : ∀ c, dV c ≤ 1 / (4 * (8 : ℝ)) := by intro c; fin_cases c <;> norm_num [dV]
theorem haP : ∀ c, dV c < aV c := by intro c; fin_cases c <;> norm_num [dV, aV]
theorem hT : ∀ c, bV c + dV c ≤ TV c := by intro c; fin_cases c <;> norm_num [bV, dV, TV]
theorem hZ : ∀ c, ((8 : ℝ) + 1) * TV c + 1 ≤ (ZV c : ℝ) := by intro c; fin_cases c <;> norm_num [TV, ZV]
theorem hE (ε : ℝ) (hε : ε ≤ (1 / 2560 : ℝ)) : ∀ c, 8 * ((ZV c : ℝ) + 1) * ε ≤ dV c := by
  intro c; fin_cases c <;> norm_num [ZV, dV] <;> linarith
theorem hcls : ∀ c i, ∀ z : ℤ, 0 ≤ z → z ≤ ZV c →
    ((z : ℝ) + 1 / 8) / pr i ≤ aV c - dV c ∨ bV c + dV c ≤ ((z : ℝ) - 1 / 8) / pr i ∨
      ((z : ℝ) + 1 / 8) / pr i = aV c ∨ ((z : ℝ) - 1 / 8) / pr i = bV c := by
  intro c i z h0 h1
  fin_cases c <;> fin_cases i <;> simp [ZV] at h1 <;> interval_cases z <;> norm_num [pr, aV, bV, dV]
theorem hEXne : ∀ c, (EXs c).Nonempty := by
  intro c
  fin_cases c
  · exact ⟨(4, 1), by simp [EXs, ZV, pr, aV] <;> norm_num⟩
theorem hENne : ∀ c, (ENs c).Nonempty := by
  intro c
  fin_cases c
  · exact ⟨(6, 2), by simp [ENs, ZV, pr, bV] <;> norm_num⟩
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
    (hHt : t ≤ HV) (h1 : (0 : ℝ) ≤ t) (h2 : t ≤ (139 / 640 : ℝ)) (hlon : ∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)) : False := by
  rcases le_total t (31 / 256 : ℝ) with hs0 | hs0
  · exact zone_kill_gen pr x ε HV (1 / 256 : ℝ) hp1 hdev hεH (by norm_num) (2 : Fin 7) 0 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (2 : Fin 7))
  rcases le_total t (35 / 256 : ℝ) with hs1 | hs1
  · exact zone_kill_gen pr x ε HV (1 / 256 : ℝ) hp1 hdev hεH (by norm_num) (6 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (6 : Fin 7))
  rcases le_total t (281 / 1792 : ℝ) with hs2 | hs2
  · exact zone_kill_gen pr x ε HV (1 / 256 : ℝ) hp1 hdev hεH (by norm_num) (0 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (0 : Fin 7))
  rcases le_total t (47 / 256 : ℝ) with hs3 | hs3
  · exact zone_kill_gen pr x ε HV (1 / 256 : ℝ) hp1 hdev hεH (by norm_num) (1 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (1 : Fin 7))
  exact zone_kill_gen pr x ε HV (1 / 256 : ℝ) hp1 hdev hεH (by norm_num) (4 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (4 : Fin 7))
theorem cov (x : Fin 7 → ℝ) (ε : ℝ) (hε : ε ≤ (1 / 2560 : ℝ)) (hdev : ∀ i, |x i - pr i| ≤ ε) :
    ∀ t : ℝ, 0 < t → t ≤ HV → (∀ c, ¬ (aV c - dV c / 2 ≤ t ∧ t ≤ bV c + dV c / 2)) →
      ¬ (∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)) := by
  intro t h0 hHt hnone hlon
  have hεH : ε * HV ≤ (1 / 256 : ℝ) / 2 := by
    have hε0 : 0 ≤ ε := le_trans (abs_nonneg _) (hdev 0)
    have : ε * HV ≤ (1 / 2560 : ℝ) * HV := mul_le_mul_of_nonneg_right hε (by norm_num [HV])
    have h2 : (1 / 2560 : ℝ) * HV ≤ (1 / 256 : ℝ) / 2 := by norm_num [HV]
    linarith
  have n0 := hnone (0 : Fin 1)
  rw [aV_0, bV_0, dV_0] at n0
  rcases lt_or_ge t (139 / 640 : ℝ) with c0 | c0
  · exact gap0 x ε hdev hεH t h0.le hHt h0.le (by linarith) hlon
  have d0 : (31 / 128 : ℝ) < t := by
    by_contra hc; push Not at hc; exact n0 ⟨by linarith, by linarith⟩
  have hHv : HV = (31 / 128 : ℝ) := rfl
  exact absurd (by linarith : t ≤ (31 / 128 : ℝ)) (not_le.2 d0)

theorem inst (x : Fin 7 → ℝ) (ε : ℝ) (hε : ε ≤ (1 / 2560 : ℝ)) (hdev : ∀ i, |x i - pr i| ≤ ε) :
    ∃ c₀ : Fin 1, Alive (mxOf x EXs hEXne) (mnOf x ENs hENne) c₀ ∧
      (∀ c, c < c₀ → ¬ Alive (mxOf x EXs hEXne) (mnOf x ENs hENne) c) ∧
      IsLeast {t : ℝ | 0 < t ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)} (mxOf x EXs hEXne c₀) :=
  landing_cert 1 (8 : ℝ) (by norm_num) pr x hp ε hdev aV bV dV TV ZV hab hd0 hdP haP hT hZ (hE ε hε) hcls EXs ENs hEXne hENne
    hEXdef hENdef hsepL HV hHL (cov x ε hε hdev) (0 : Fin 1) (by rw [dV_0, bV_0, aV_0]; norm_num)

noncomputable def sv : Fin 8 → ℝ := ![(1 : ℝ), (2 : ℝ), (8 : ℝ), (9 : ℝ), (10 : ℝ), (13 : ℝ), (14 : ℝ), (16 : ℝ)]
def sg : Fin 7 → Fin 8 := ![0, 1, 3, 4, 5, 6, 7]

theorem sv_0 : sv (0 : Fin 8) = (1 : ℝ) := rfl
theorem sv_1 : sv (1 : Fin 8) = (2 : ℝ) := rfl
theorem sv_2 : sv (2 : Fin 8) = (8 : ℝ) := rfl
theorem sv_3 : sv (3 : Fin 8) = (9 : ℝ) := rfl
theorem sv_4 : sv (4 : Fin 8) = (10 : ℝ) := rfl
theorem sv_5 : sv (5 : Fin 8) = (13 : ℝ) := rfl
theorem sv_6 : sv (6 : Fin 8) = (14 : ℝ) := rfl
theorem sv_7 : sv (7 : Fin 8) = (16 : ℝ) := rfl
theorem sg_0 : sg (0 : Fin 7) = (0 : Fin 8) := rfl
theorem sg_1 : sg (1 : Fin 7) = (1 : Fin 8) := rfl
theorem sg_2 : sg (2 : Fin 7) = (3 : Fin 8) := rfl
theorem sg_3 : sg (3 : Fin 7) = (4 : Fin 8) := rfl
theorem sg_4 : sg (4 : Fin 7) = (5 : Fin 8) := rfl
theorem sg_5 : sg (5 : Fin 7) = (6 : Fin 8) := rfl
theorem sg_6 : sg (6 : Fin 7) = (7 : Fin 8) := rfl

theorem inst_arr (v : Fin 8 → ℝ) (η : ℝ) (hη : η ≤ (1 / 5120 : ℝ)) (hv : ∀ j, |v j - sv j| ≤ η) :
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

end Fresh.CertRR.R13258



/-!
# Landing certificate `CertRR.R13263`: speeds (1, 2, 8, 9, 10, 13, 14, 16), subject index 7

Generated 2026-10-24 by `experiments/n8/cert_gen_v1.py` (exact Fractions).  Baseline readings [15, 14, 8, 7, 6, 3, 2].  Components up to the first wide one: 1.
Radius: speeds within `η ≤ 1/14934` of the baseline speeds, giving `ε = 2η ≤ 1/7467`.  Covering margin `μ = 1/512`.
`hcov` is **[PROVISIONAL: covering]**, supporting the claim that the first lonely instant of this subject is the largest exit of the first alive component.
Result `inst_arr`: for such `v`, the subject has a first isolation (a least element over all `t > 0`).  Grades: [L].
-/

open Classical

namespace Fresh.CertRR.R13263

open Fresh Fresh.LandingCert Fresh.LandingRule

noncomputable def pr : Fin 7 → ℝ := ![(15 : ℝ), (14 : ℝ), (8 : ℝ), (7 : ℝ), (6 : ℝ), (3 : ℝ), (2 : ℝ)]
noncomputable def aV : Fin 1 → ℝ := ![(9 / 112 : ℝ)]
noncomputable def bV : Fin 1 → ℝ := ![(7 / 64 : ℝ)]
noncomputable def dV : Fin 1 → ℝ := ![(3 / 560 : ℝ)]
noncomputable def TV : Fin 1 → ℝ := ![(257 / 2240 : ℝ)]
def ZV : Fin 1 → ℤ := ![4]
noncomputable def HV : ℝ := (251 / 2240 : ℝ)
noncomputable def EXs (c : Fin 1) : Finset (Fin 7 × ℤ) :=
  (Finset.univ ×ˢ Finset.Icc 0 (ZV c)).filter (fun q => ((q.2 : ℝ) + 1 / 8) / pr q.1 = aV c)
noncomputable def ENs (c : Fin 1) : Finset (Fin 7 × ℤ) :=
  (Finset.univ ×ˢ Finset.Icc 0 (ZV c)).filter (fun q => ((q.2 : ℝ) - 1 / 8) / pr q.1 = bV c)

theorem hp : ∀ i, 1 ≤ pr i ∧ pr i ≤ (15 : ℝ) := by intro i; fin_cases i <;> norm_num [pr]
theorem hp1 : ∀ i, 1 ≤ pr i := fun i => (hp i).1
theorem pr_0 : pr (0 : Fin 7) = (15 : ℝ) := rfl
theorem pr_1 : pr (1 : Fin 7) = (14 : ℝ) := rfl
theorem pr_2 : pr (2 : Fin 7) = (8 : ℝ) := rfl
theorem pr_3 : pr (3 : Fin 7) = (7 : ℝ) := rfl
theorem pr_4 : pr (4 : Fin 7) = (6 : ℝ) := rfl
theorem pr_5 : pr (5 : Fin 7) = (3 : ℝ) := rfl
theorem pr_6 : pr (6 : Fin 7) = (2 : ℝ) := rfl
theorem aV_0 : aV (0 : Fin 1) = (9 / 112 : ℝ) := rfl
theorem bV_0 : bV (0 : Fin 1) = (7 / 64 : ℝ) := rfl
theorem dV_0 : dV (0 : Fin 1) = (3 / 560 : ℝ) := rfl
theorem TV_0 : TV (0 : Fin 1) = (257 / 2240 : ℝ) := rfl
theorem ZV_0 : ZV (0 : Fin 1) = (4 : ℤ) := rfl
theorem hab : ∀ c, aV c ≤ bV c := by intro c; fin_cases c <;> norm_num [aV, bV]
theorem hd0 : ∀ c, 0 < dV c := by intro c; fin_cases c <;> norm_num [dV]
theorem hdP : ∀ c, dV c ≤ 1 / (4 * (15 : ℝ)) := by intro c; fin_cases c <;> norm_num [dV]
theorem haP : ∀ c, dV c < aV c := by intro c; fin_cases c <;> norm_num [dV, aV]
theorem hT : ∀ c, bV c + dV c ≤ TV c := by intro c; fin_cases c <;> norm_num [bV, dV, TV]
theorem hZ : ∀ c, ((15 : ℝ) + 1) * TV c + 1 ≤ (ZV c : ℝ) := by intro c; fin_cases c <;> norm_num [TV, ZV]
theorem hE (ε : ℝ) (hε : ε ≤ (1 / 7467 : ℝ)) : ∀ c, 8 * ((ZV c : ℝ) + 1) * ε ≤ dV c := by
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
  · exact ⟨(2, 1), by simp [ENs, ZV, pr, bV] <;> norm_num⟩
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
    (hHt : t ≤ HV) (h1 : (0 : ℝ) ≤ t) (h2 : t ≤ (87 / 1120 : ℝ)) (hlon : ∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)) : False := by
  rcases le_total t (31 / 512 : ℝ) with hs0 | hs0
  · exact zone_kill_gen pr x ε HV (1 / 512 : ℝ) hp1 hdev hεH (by norm_num) (6 : Fin 7) 0 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (6 : Fin 7))
  rcases le_total t (187 / 2560 : ℝ) with hs1 | hs1
  · exact zone_kill_gen pr x ε HV (1 / 512 : ℝ) hp1 hdev hεH (by norm_num) (0 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (0 : Fin 7))
  exact zone_kill_gen pr x ε HV (1 / 512 : ℝ) hp1 hdev hεH (by norm_num) (1 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (1 : Fin 7))
theorem cov (x : Fin 7 → ℝ) (ε : ℝ) (hε : ε ≤ (1 / 7467 : ℝ)) (hdev : ∀ i, |x i - pr i| ≤ ε) :
    ∀ t : ℝ, 0 < t → t ≤ HV → (∀ c, ¬ (aV c - dV c / 2 ≤ t ∧ t ≤ bV c + dV c / 2)) →
      ¬ (∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)) := by
  intro t h0 hHt hnone hlon
  have hεH : ε * HV ≤ (1 / 512 : ℝ) / 2 := by
    have hε0 : 0 ≤ ε := le_trans (abs_nonneg _) (hdev 0)
    have : ε * HV ≤ (1 / 7467 : ℝ) * HV := mul_le_mul_of_nonneg_right hε (by norm_num [HV])
    have h2 : (1 / 7467 : ℝ) * HV ≤ (1 / 512 : ℝ) / 2 := by norm_num [HV]
    linarith
  have n0 := hnone (0 : Fin 1)
  rw [aV_0, bV_0, dV_0] at n0
  rcases lt_or_ge t (87 / 1120 : ℝ) with c0 | c0
  · exact gap0 x ε hdev hεH t h0.le hHt h0.le (by linarith) hlon
  have d0 : (251 / 2240 : ℝ) < t := by
    by_contra hc; push Not at hc; exact n0 ⟨by linarith, by linarith⟩
  have hHv : HV = (251 / 2240 : ℝ) := rfl
  exact absurd (by linarith : t ≤ (251 / 2240 : ℝ)) (not_le.2 d0)

theorem inst (x : Fin 7 → ℝ) (ε : ℝ) (hε : ε ≤ (1 / 7467 : ℝ)) (hdev : ∀ i, |x i - pr i| ≤ ε) :
    ∃ c₀ : Fin 1, Alive (mxOf x EXs hEXne) (mnOf x ENs hENne) c₀ ∧
      (∀ c, c < c₀ → ¬ Alive (mxOf x EXs hEXne) (mnOf x ENs hENne) c) ∧
      IsLeast {t : ℝ | 0 < t ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)} (mxOf x EXs hEXne c₀) :=
  landing_cert 1 (15 : ℝ) (by norm_num) pr x hp ε hdev aV bV dV TV ZV hab hd0 hdP haP hT hZ (hE ε hε) hcls EXs ENs hEXne hENne
    hEXdef hENdef hsepL HV hHL (cov x ε hε hdev) (0 : Fin 1) (by rw [dV_0, bV_0, aV_0]; norm_num)

noncomputable def sv : Fin 8 → ℝ := ![(1 : ℝ), (2 : ℝ), (8 : ℝ), (9 : ℝ), (10 : ℝ), (13 : ℝ), (14 : ℝ), (16 : ℝ)]
def sg : Fin 7 → Fin 8 := ![0, 1, 2, 3, 4, 5, 6]

theorem sv_0 : sv (0 : Fin 8) = (1 : ℝ) := rfl
theorem sv_1 : sv (1 : Fin 8) = (2 : ℝ) := rfl
theorem sv_2 : sv (2 : Fin 8) = (8 : ℝ) := rfl
theorem sv_3 : sv (3 : Fin 8) = (9 : ℝ) := rfl
theorem sv_4 : sv (4 : Fin 8) = (10 : ℝ) := rfl
theorem sv_5 : sv (5 : Fin 8) = (13 : ℝ) := rfl
theorem sv_6 : sv (6 : Fin 8) = (14 : ℝ) := rfl
theorem sv_7 : sv (7 : Fin 8) = (16 : ℝ) := rfl
theorem sg_0 : sg (0 : Fin 7) = (0 : Fin 8) := rfl
theorem sg_1 : sg (1 : Fin 7) = (1 : Fin 8) := rfl
theorem sg_2 : sg (2 : Fin 7) = (2 : Fin 8) := rfl
theorem sg_3 : sg (3 : Fin 7) = (3 : Fin 8) := rfl
theorem sg_4 : sg (4 : Fin 7) = (4 : Fin 8) := rfl
theorem sg_5 : sg (5 : Fin 7) = (5 : Fin 8) := rfl
theorem sg_6 : sg (6 : Fin 7) = (6 : Fin 8) := rfl

theorem inst_arr (v : Fin 8 → ℝ) (η : ℝ) (hη : η ≤ (1 / 14934 : ℝ)) (hv : ∀ j, |v j - sv j| ≤ η) :
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

end Fresh.CertRR.R13263



/-!
# Landing certificate `CertRR.R13264`: speeds (1, 2, 8, 9, 10, 13, 15, 16), subject index 0

Generated 2026-10-24 by `experiments/n8/cert_gen_v1.py` (exact Fractions).  Baseline readings [1, 7, 8, 9, 12, 14, 15].  Components up to the first wide one: 1.
Radius: speeds within `η ≤ 1/7014` of the baseline speeds, giving `ε = 2η ≤ 1/3507`.  Covering margin `μ = 1/512`.
`hcov` is **[PROVISIONAL: covering]**, supporting the claim that the first lonely instant of this subject is the largest exit of the first alive component.
Result `inst_arr`: for such `v`, the subject has a first isolation (a least element over all `t > 0`).  Grades: [L].
-/

open Classical

namespace Fresh.CertRR.R13264

open Fresh Fresh.LandingCert Fresh.LandingRule

noncomputable def pr : Fin 7 → ℝ := ![(1 : ℝ), (7 : ℝ), (8 : ℝ), (9 : ℝ), (12 : ℝ), (14 : ℝ), (15 : ℝ)]
noncomputable def aV : Fin 1 → ℝ := ![(17 / 96 : ℝ)]
noncomputable def bV : Fin 1 → ℝ := ![(23 / 120 : ℝ)]
noncomputable def dV : Fin 1 → ℝ := ![(23 / 1680 : ℝ)]
noncomputable def TV : Fin 1 → ℝ := ![(23 / 112 : ℝ)]
def ZV : Fin 1 → ℤ := ![5]
noncomputable def HV : ℝ := (667 / 3360 : ℝ)
noncomputable def EXs (c : Fin 1) : Finset (Fin 7 × ℤ) :=
  (Finset.univ ×ˢ Finset.Icc 0 (ZV c)).filter (fun q => ((q.2 : ℝ) + 1 / 8) / pr q.1 = aV c)
noncomputable def ENs (c : Fin 1) : Finset (Fin 7 × ℤ) :=
  (Finset.univ ×ˢ Finset.Icc 0 (ZV c)).filter (fun q => ((q.2 : ℝ) - 1 / 8) / pr q.1 = bV c)

theorem hp : ∀ i, 1 ≤ pr i ∧ pr i ≤ (15 : ℝ) := by intro i; fin_cases i <;> norm_num [pr]
theorem hp1 : ∀ i, 1 ≤ pr i := fun i => (hp i).1
theorem pr_0 : pr (0 : Fin 7) = (1 : ℝ) := rfl
theorem pr_1 : pr (1 : Fin 7) = (7 : ℝ) := rfl
theorem pr_2 : pr (2 : Fin 7) = (8 : ℝ) := rfl
theorem pr_3 : pr (3 : Fin 7) = (9 : ℝ) := rfl
theorem pr_4 : pr (4 : Fin 7) = (12 : ℝ) := rfl
theorem pr_5 : pr (5 : Fin 7) = (14 : ℝ) := rfl
theorem pr_6 : pr (6 : Fin 7) = (15 : ℝ) := rfl
theorem aV_0 : aV (0 : Fin 1) = (17 / 96 : ℝ) := rfl
theorem bV_0 : bV (0 : Fin 1) = (23 / 120 : ℝ) := rfl
theorem dV_0 : dV (0 : Fin 1) = (23 / 1680 : ℝ) := rfl
theorem TV_0 : TV (0 : Fin 1) = (23 / 112 : ℝ) := rfl
theorem ZV_0 : ZV (0 : Fin 1) = (5 : ℤ) := rfl
theorem hab : ∀ c, aV c ≤ bV c := by intro c; fin_cases c <;> norm_num [aV, bV]
theorem hd0 : ∀ c, 0 < dV c := by intro c; fin_cases c <;> norm_num [dV]
theorem hdP : ∀ c, dV c ≤ 1 / (4 * (15 : ℝ)) := by intro c; fin_cases c <;> norm_num [dV]
theorem haP : ∀ c, dV c < aV c := by intro c; fin_cases c <;> norm_num [dV, aV]
theorem hT : ∀ c, bV c + dV c ≤ TV c := by intro c; fin_cases c <;> norm_num [bV, dV, TV]
theorem hZ : ∀ c, ((15 : ℝ) + 1) * TV c + 1 ≤ (ZV c : ℝ) := by intro c; fin_cases c <;> norm_num [TV, ZV]
theorem hE (ε : ℝ) (hε : ε ≤ (1 / 3507 : ℝ)) : ∀ c, 8 * ((ZV c : ℝ) + 1) * ε ≤ dV c := by
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
  · exact ⟨(6, 3), by simp [ENs, ZV, pr, bV] <;> norm_num⟩
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
    (hHt : t ≤ HV) (h1 : (0 : ℝ) ≤ t) (h2 : t ≤ (143 / 840 : ℝ)) (hlon : ∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)) : False := by
  rcases le_total t (63 / 512 : ℝ) with hs0 | hs0
  · exact zone_kill_gen pr x ε HV (1 / 512 : ℝ) hp1 hdev hεH (by norm_num) (0 : Fin 7) 0 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (0 : Fin 7))
  rcases le_total t (71 / 512 : ℝ) with hs1 | hs1
  · exact zone_kill_gen pr x ε HV (1 / 512 : ℝ) hp1 hdev hεH (by norm_num) (2 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (2 : Fin 7))
  rcases le_total t (569 / 3584 : ℝ) with hs2 | hs2
  · exact zone_kill_gen pr x ε HV (1 / 512 : ℝ) hp1 hdev hεH (by norm_num) (1 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (1 : Fin 7))
  exact zone_kill_gen pr x ε HV (1 / 512 : ℝ) hp1 hdev hεH (by norm_num) (4 : Fin 7) 2 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (4 : Fin 7))
theorem cov (x : Fin 7 → ℝ) (ε : ℝ) (hε : ε ≤ (1 / 3507 : ℝ)) (hdev : ∀ i, |x i - pr i| ≤ ε) :
    ∀ t : ℝ, 0 < t → t ≤ HV → (∀ c, ¬ (aV c - dV c / 2 ≤ t ∧ t ≤ bV c + dV c / 2)) →
      ¬ (∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)) := by
  intro t h0 hHt hnone hlon
  have hεH : ε * HV ≤ (1 / 512 : ℝ) / 2 := by
    have hε0 : 0 ≤ ε := le_trans (abs_nonneg _) (hdev 0)
    have : ε * HV ≤ (1 / 3507 : ℝ) * HV := mul_le_mul_of_nonneg_right hε (by norm_num [HV])
    have h2 : (1 / 3507 : ℝ) * HV ≤ (1 / 512 : ℝ) / 2 := by norm_num [HV]
    linarith
  have n0 := hnone (0 : Fin 1)
  rw [aV_0, bV_0, dV_0] at n0
  rcases lt_or_ge t (143 / 840 : ℝ) with c0 | c0
  · exact gap0 x ε hdev hεH t h0.le hHt h0.le (by linarith) hlon
  have d0 : (667 / 3360 : ℝ) < t := by
    by_contra hc; push Not at hc; exact n0 ⟨by linarith, by linarith⟩
  have hHv : HV = (667 / 3360 : ℝ) := rfl
  exact absurd (by linarith : t ≤ (667 / 3360 : ℝ)) (not_le.2 d0)

theorem inst (x : Fin 7 → ℝ) (ε : ℝ) (hε : ε ≤ (1 / 3507 : ℝ)) (hdev : ∀ i, |x i - pr i| ≤ ε) :
    ∃ c₀ : Fin 1, Alive (mxOf x EXs hEXne) (mnOf x ENs hENne) c₀ ∧
      (∀ c, c < c₀ → ¬ Alive (mxOf x EXs hEXne) (mnOf x ENs hENne) c) ∧
      IsLeast {t : ℝ | 0 < t ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)} (mxOf x EXs hEXne c₀) :=
  landing_cert 1 (15 : ℝ) (by norm_num) pr x hp ε hdev aV bV dV TV ZV hab hd0 hdP haP hT hZ (hE ε hε) hcls EXs ENs hEXne hENne
    hEXdef hENdef hsepL HV hHL (cov x ε hε hdev) (0 : Fin 1) (by rw [dV_0, bV_0, aV_0]; norm_num)

noncomputable def sv : Fin 8 → ℝ := ![(1 : ℝ), (2 : ℝ), (8 : ℝ), (9 : ℝ), (10 : ℝ), (13 : ℝ), (15 : ℝ), (16 : ℝ)]
def sg : Fin 7 → Fin 8 := ![1, 2, 3, 4, 5, 6, 7]

theorem sv_0 : sv (0 : Fin 8) = (1 : ℝ) := rfl
theorem sv_1 : sv (1 : Fin 8) = (2 : ℝ) := rfl
theorem sv_2 : sv (2 : Fin 8) = (8 : ℝ) := rfl
theorem sv_3 : sv (3 : Fin 8) = (9 : ℝ) := rfl
theorem sv_4 : sv (4 : Fin 8) = (10 : ℝ) := rfl
theorem sv_5 : sv (5 : Fin 8) = (13 : ℝ) := rfl
theorem sv_6 : sv (6 : Fin 8) = (15 : ℝ) := rfl
theorem sv_7 : sv (7 : Fin 8) = (16 : ℝ) := rfl
theorem sg_0 : sg (0 : Fin 7) = (1 : Fin 8) := rfl
theorem sg_1 : sg (1 : Fin 7) = (2 : Fin 8) := rfl
theorem sg_2 : sg (2 : Fin 7) = (3 : Fin 8) := rfl
theorem sg_3 : sg (3 : Fin 7) = (4 : Fin 8) := rfl
theorem sg_4 : sg (4 : Fin 7) = (5 : Fin 8) := rfl
theorem sg_5 : sg (5 : Fin 7) = (6 : Fin 8) := rfl
theorem sg_6 : sg (6 : Fin 7) = (7 : Fin 8) := rfl

theorem inst_arr (v : Fin 8 → ℝ) (η : ℝ) (hη : η ≤ (1 / 7014 : ℝ)) (hv : ∀ j, |v j - sv j| ≤ η) :
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

end Fresh.CertRR.R13264



/-!
# Landing certificate `CertRR.R13266`: speeds (1, 2, 8, 9, 10, 13, 15, 16), subject index 2

Generated 2026-10-24 by `experiments/n8/cert_gen_v1.py` (exact Fractions).  Baseline readings [7, 6, 1, 2, 5, 7, 8].  Components up to the first wide one: 1.
Radius: speeds within `η ≤ 1/5120` of the baseline speeds, giving `ε = 2η ≤ 1/2560`.  Covering margin `μ = 1/256`.
`hcov` is **[PROVISIONAL: covering]**, supporting the claim that the first lonely instant of this subject is the largest exit of the first alive component.
Result `inst_arr`: for such `v`, the subject has a first isolation (a least element over all `t > 0`).  Grades: [L].
-/

open Classical

namespace Fresh.CertRR.R13266

open Fresh Fresh.LandingCert Fresh.LandingRule

noncomputable def pr : Fin 7 → ℝ := ![(7 : ℝ), (6 : ℝ), (1 : ℝ), (2 : ℝ), (5 : ℝ), (7 : ℝ), (8 : ℝ)]
noncomputable def aV : Fin 1 → ℝ := ![(9 / 40 : ℝ)]
noncomputable def bV : Fin 1 → ℝ := ![(15 / 64 : ℝ)]
noncomputable def dV : Fin 1 → ℝ := ![(1 / 64 : ℝ)]
noncomputable def TV : Fin 1 → ℝ := ![(1 / 4 : ℝ)]
def ZV : Fin 1 → ℤ := ![4]
noncomputable def HV : ℝ := (31 / 128 : ℝ)
noncomputable def EXs (c : Fin 1) : Finset (Fin 7 × ℤ) :=
  (Finset.univ ×ˢ Finset.Icc 0 (ZV c)).filter (fun q => ((q.2 : ℝ) + 1 / 8) / pr q.1 = aV c)
noncomputable def ENs (c : Fin 1) : Finset (Fin 7 × ℤ) :=
  (Finset.univ ×ˢ Finset.Icc 0 (ZV c)).filter (fun q => ((q.2 : ℝ) - 1 / 8) / pr q.1 = bV c)

theorem hp : ∀ i, 1 ≤ pr i ∧ pr i ≤ (8 : ℝ) := by intro i; fin_cases i <;> norm_num [pr]
theorem hp1 : ∀ i, 1 ≤ pr i := fun i => (hp i).1
theorem pr_0 : pr (0 : Fin 7) = (7 : ℝ) := rfl
theorem pr_1 : pr (1 : Fin 7) = (6 : ℝ) := rfl
theorem pr_2 : pr (2 : Fin 7) = (1 : ℝ) := rfl
theorem pr_3 : pr (3 : Fin 7) = (2 : ℝ) := rfl
theorem pr_4 : pr (4 : Fin 7) = (5 : ℝ) := rfl
theorem pr_5 : pr (5 : Fin 7) = (7 : ℝ) := rfl
theorem pr_6 : pr (6 : Fin 7) = (8 : ℝ) := rfl
theorem aV_0 : aV (0 : Fin 1) = (9 / 40 : ℝ) := rfl
theorem bV_0 : bV (0 : Fin 1) = (15 / 64 : ℝ) := rfl
theorem dV_0 : dV (0 : Fin 1) = (1 / 64 : ℝ) := rfl
theorem TV_0 : TV (0 : Fin 1) = (1 / 4 : ℝ) := rfl
theorem ZV_0 : ZV (0 : Fin 1) = (4 : ℤ) := rfl
theorem hab : ∀ c, aV c ≤ bV c := by intro c; fin_cases c <;> norm_num [aV, bV]
theorem hd0 : ∀ c, 0 < dV c := by intro c; fin_cases c <;> norm_num [dV]
theorem hdP : ∀ c, dV c ≤ 1 / (4 * (8 : ℝ)) := by intro c; fin_cases c <;> norm_num [dV]
theorem haP : ∀ c, dV c < aV c := by intro c; fin_cases c <;> norm_num [dV, aV]
theorem hT : ∀ c, bV c + dV c ≤ TV c := by intro c; fin_cases c <;> norm_num [bV, dV, TV]
theorem hZ : ∀ c, ((8 : ℝ) + 1) * TV c + 1 ≤ (ZV c : ℝ) := by intro c; fin_cases c <;> norm_num [TV, ZV]
theorem hE (ε : ℝ) (hε : ε ≤ (1 / 2560 : ℝ)) : ∀ c, 8 * ((ZV c : ℝ) + 1) * ε ≤ dV c := by
  intro c; fin_cases c <;> norm_num [ZV, dV] <;> linarith
theorem hcls : ∀ c i, ∀ z : ℤ, 0 ≤ z → z ≤ ZV c →
    ((z : ℝ) + 1 / 8) / pr i ≤ aV c - dV c ∨ bV c + dV c ≤ ((z : ℝ) - 1 / 8) / pr i ∨
      ((z : ℝ) + 1 / 8) / pr i = aV c ∨ ((z : ℝ) - 1 / 8) / pr i = bV c := by
  intro c i z h0 h1
  fin_cases c <;> fin_cases i <;> simp [ZV] at h1 <;> interval_cases z <;> norm_num [pr, aV, bV, dV]
theorem hEXne : ∀ c, (EXs c).Nonempty := by
  intro c
  fin_cases c
  · exact ⟨(4, 1), by simp [EXs, ZV, pr, aV] <;> norm_num⟩
theorem hENne : ∀ c, (ENs c).Nonempty := by
  intro c
  fin_cases c
  · exact ⟨(6, 2), by simp [ENs, ZV, pr, bV] <;> norm_num⟩
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
    (hHt : t ≤ HV) (h1 : (0 : ℝ) ≤ t) (h2 : t ≤ (139 / 640 : ℝ)) (hlon : ∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)) : False := by
  rcases le_total t (31 / 256 : ℝ) with hs0 | hs0
  · exact zone_kill_gen pr x ε HV (1 / 256 : ℝ) hp1 hdev hεH (by norm_num) (2 : Fin 7) 0 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (2 : Fin 7))
  rcases le_total t (35 / 256 : ℝ) with hs1 | hs1
  · exact zone_kill_gen pr x ε HV (1 / 256 : ℝ) hp1 hdev hεH (by norm_num) (6 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (6 : Fin 7))
  rcases le_total t (281 / 1792 : ℝ) with hs2 | hs2
  · exact zone_kill_gen pr x ε HV (1 / 256 : ℝ) hp1 hdev hεH (by norm_num) (0 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (0 : Fin 7))
  rcases le_total t (47 / 256 : ℝ) with hs3 | hs3
  · exact zone_kill_gen pr x ε HV (1 / 256 : ℝ) hp1 hdev hεH (by norm_num) (1 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (1 : Fin 7))
  exact zone_kill_gen pr x ε HV (1 / 256 : ℝ) hp1 hdev hεH (by norm_num) (4 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (4 : Fin 7))
theorem cov (x : Fin 7 → ℝ) (ε : ℝ) (hε : ε ≤ (1 / 2560 : ℝ)) (hdev : ∀ i, |x i - pr i| ≤ ε) :
    ∀ t : ℝ, 0 < t → t ≤ HV → (∀ c, ¬ (aV c - dV c / 2 ≤ t ∧ t ≤ bV c + dV c / 2)) →
      ¬ (∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)) := by
  intro t h0 hHt hnone hlon
  have hεH : ε * HV ≤ (1 / 256 : ℝ) / 2 := by
    have hε0 : 0 ≤ ε := le_trans (abs_nonneg _) (hdev 0)
    have : ε * HV ≤ (1 / 2560 : ℝ) * HV := mul_le_mul_of_nonneg_right hε (by norm_num [HV])
    have h2 : (1 / 2560 : ℝ) * HV ≤ (1 / 256 : ℝ) / 2 := by norm_num [HV]
    linarith
  have n0 := hnone (0 : Fin 1)
  rw [aV_0, bV_0, dV_0] at n0
  rcases lt_or_ge t (139 / 640 : ℝ) with c0 | c0
  · exact gap0 x ε hdev hεH t h0.le hHt h0.le (by linarith) hlon
  have d0 : (31 / 128 : ℝ) < t := by
    by_contra hc; push Not at hc; exact n0 ⟨by linarith, by linarith⟩
  have hHv : HV = (31 / 128 : ℝ) := rfl
  exact absurd (by linarith : t ≤ (31 / 128 : ℝ)) (not_le.2 d0)

theorem inst (x : Fin 7 → ℝ) (ε : ℝ) (hε : ε ≤ (1 / 2560 : ℝ)) (hdev : ∀ i, |x i - pr i| ≤ ε) :
    ∃ c₀ : Fin 1, Alive (mxOf x EXs hEXne) (mnOf x ENs hENne) c₀ ∧
      (∀ c, c < c₀ → ¬ Alive (mxOf x EXs hEXne) (mnOf x ENs hENne) c) ∧
      IsLeast {t : ℝ | 0 < t ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)} (mxOf x EXs hEXne c₀) :=
  landing_cert 1 (8 : ℝ) (by norm_num) pr x hp ε hdev aV bV dV TV ZV hab hd0 hdP haP hT hZ (hE ε hε) hcls EXs ENs hEXne hENne
    hEXdef hENdef hsepL HV hHL (cov x ε hε hdev) (0 : Fin 1) (by rw [dV_0, bV_0, aV_0]; norm_num)

noncomputable def sv : Fin 8 → ℝ := ![(1 : ℝ), (2 : ℝ), (8 : ℝ), (9 : ℝ), (10 : ℝ), (13 : ℝ), (15 : ℝ), (16 : ℝ)]
def sg : Fin 7 → Fin 8 := ![0, 1, 3, 4, 5, 6, 7]

theorem sv_0 : sv (0 : Fin 8) = (1 : ℝ) := rfl
theorem sv_1 : sv (1 : Fin 8) = (2 : ℝ) := rfl
theorem sv_2 : sv (2 : Fin 8) = (8 : ℝ) := rfl
theorem sv_3 : sv (3 : Fin 8) = (9 : ℝ) := rfl
theorem sv_4 : sv (4 : Fin 8) = (10 : ℝ) := rfl
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

theorem inst_arr (v : Fin 8 → ℝ) (η : ℝ) (hη : η ≤ (1 / 5120 : ℝ)) (hv : ∀ j, |v j - sv j| ≤ η) :
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

end Fresh.CertRR.R13266



/-!
# Landing certificate `CertRR.R13271`: speeds (1, 2, 8, 9, 10, 13, 15, 16), subject index 7

Generated 2026-10-24 by `experiments/n8/cert_gen_v1.py` (exact Fractions).  Baseline readings [15, 14, 8, 7, 6, 3, 1].  Components up to the first wide one: 1.
Radius: speeds within `η ≤ 1/11520` of the baseline speeds, giving `ε = 2η ≤ 1/5760`.  Covering margin `μ = 1/256`.
`hcov` is **[PROVISIONAL: covering]**, supporting the claim that the first lonely instant of this subject is the largest exit of the first alive component.
Result `inst_arr`: for such `v`, the subject has a first isolation (a least element over all `t > 0`).  Grades: [L].
-/

open Classical

namespace Fresh.CertRR.R13271

open Fresh Fresh.LandingCert Fresh.LandingRule

noncomputable def pr : Fin 7 → ℝ := ![(15 : ℝ), (14 : ℝ), (8 : ℝ), (7 : ℝ), (6 : ℝ), (3 : ℝ), (1 : ℝ)]
noncomputable def aV : Fin 1 → ℝ := ![(3 / 16 : ℝ)]
noncomputable def bV : Fin 1 → ℝ := ![(23 / 120 : ℝ)]
noncomputable def dV : Fin 1 → ℝ := ![(1 / 120 : ℝ)]
noncomputable def TV : Fin 1 → ℝ := ![(1 / 5 : ℝ)]
def ZV : Fin 1 → ℤ := ![5]
noncomputable def HV : ℝ := (47 / 240 : ℝ)
noncomputable def EXs (c : Fin 1) : Finset (Fin 7 × ℤ) :=
  (Finset.univ ×ˢ Finset.Icc 0 (ZV c)).filter (fun q => ((q.2 : ℝ) + 1 / 8) / pr q.1 = aV c)
noncomputable def ENs (c : Fin 1) : Finset (Fin 7 × ℤ) :=
  (Finset.univ ×ˢ Finset.Icc 0 (ZV c)).filter (fun q => ((q.2 : ℝ) - 1 / 8) / pr q.1 = bV c)

theorem hp : ∀ i, 1 ≤ pr i ∧ pr i ≤ (15 : ℝ) := by intro i; fin_cases i <;> norm_num [pr]
theorem hp1 : ∀ i, 1 ≤ pr i := fun i => (hp i).1
theorem pr_0 : pr (0 : Fin 7) = (15 : ℝ) := rfl
theorem pr_1 : pr (1 : Fin 7) = (14 : ℝ) := rfl
theorem pr_2 : pr (2 : Fin 7) = (8 : ℝ) := rfl
theorem pr_3 : pr (3 : Fin 7) = (7 : ℝ) := rfl
theorem pr_4 : pr (4 : Fin 7) = (6 : ℝ) := rfl
theorem pr_5 : pr (5 : Fin 7) = (3 : ℝ) := rfl
theorem pr_6 : pr (6 : Fin 7) = (1 : ℝ) := rfl
theorem aV_0 : aV (0 : Fin 1) = (3 / 16 : ℝ) := rfl
theorem bV_0 : bV (0 : Fin 1) = (23 / 120 : ℝ) := rfl
theorem dV_0 : dV (0 : Fin 1) = (1 / 120 : ℝ) := rfl
theorem TV_0 : TV (0 : Fin 1) = (1 / 5 : ℝ) := rfl
theorem ZV_0 : ZV (0 : Fin 1) = (5 : ℤ) := rfl
theorem hab : ∀ c, aV c ≤ bV c := by intro c; fin_cases c <;> norm_num [aV, bV]
theorem hd0 : ∀ c, 0 < dV c := by intro c; fin_cases c <;> norm_num [dV]
theorem hdP : ∀ c, dV c ≤ 1 / (4 * (15 : ℝ)) := by intro c; fin_cases c <;> norm_num [dV]
theorem haP : ∀ c, dV c < aV c := by intro c; fin_cases c <;> norm_num [dV, aV]
theorem hT : ∀ c, bV c + dV c ≤ TV c := by intro c; fin_cases c <;> norm_num [bV, dV, TV]
theorem hZ : ∀ c, ((15 : ℝ) + 1) * TV c + 1 ≤ (ZV c : ℝ) := by intro c; fin_cases c <;> norm_num [TV, ZV]
theorem hE (ε : ℝ) (hε : ε ≤ (1 / 5760 : ℝ)) : ∀ c, 8 * ((ZV c : ℝ) + 1) * ε ≤ dV c := by
  intro c; fin_cases c <;> norm_num [ZV, dV] <;> linarith
theorem hcls : ∀ c i, ∀ z : ℤ, 0 ≤ z → z ≤ ZV c →
    ((z : ℝ) + 1 / 8) / pr i ≤ aV c - dV c ∨ bV c + dV c ≤ ((z : ℝ) - 1 / 8) / pr i ∨
      ((z : ℝ) + 1 / 8) / pr i = aV c ∨ ((z : ℝ) - 1 / 8) / pr i = bV c := by
  intro c i z h0 h1
  fin_cases c <;> fin_cases i <;> simp [ZV] at h1 <;> interval_cases z <;> norm_num [pr, aV, bV, dV]
theorem hEXne : ∀ c, (EXs c).Nonempty := by
  intro c
  fin_cases c
  · exact ⟨(4, 1), by simp [EXs, ZV, pr, aV] <;> norm_num⟩
theorem hENne : ∀ c, (ENs c).Nonempty := by
  intro c
  fin_cases c
  · exact ⟨(0, 3), by simp [ENs, ZV, pr, bV] <;> norm_num⟩
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
    (hHt : t ≤ HV) (h1 : (0 : ℝ) ≤ t) (h2 : t ≤ (11 / 60 : ℝ)) (hlon : ∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)) : False := by
  rcases le_total t (31 / 256 : ℝ) with hs0 | hs0
  · exact zone_kill_gen pr x ε HV (1 / 256 : ℝ) hp1 hdev hεH (by norm_num) (6 : Fin 7) 0 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (6 : Fin 7))
  rcases le_total t (35 / 256 : ℝ) with hs1 | hs1
  · exact zone_kill_gen pr x ε HV (1 / 256 : ℝ) hp1 hdev hεH (by norm_num) (2 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (2 : Fin 7))
  rcases le_total t (281 / 1792 : ℝ) with hs2 | hs2
  · exact zone_kill_gen pr x ε HV (1 / 256 : ℝ) hp1 hdev hεH (by norm_num) (3 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (3 : Fin 7))
  exact zone_kill_gen pr x ε HV (1 / 256 : ℝ) hp1 hdev hεH (by norm_num) (4 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (4 : Fin 7))
theorem cov (x : Fin 7 → ℝ) (ε : ℝ) (hε : ε ≤ (1 / 5760 : ℝ)) (hdev : ∀ i, |x i - pr i| ≤ ε) :
    ∀ t : ℝ, 0 < t → t ≤ HV → (∀ c, ¬ (aV c - dV c / 2 ≤ t ∧ t ≤ bV c + dV c / 2)) →
      ¬ (∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)) := by
  intro t h0 hHt hnone hlon
  have hεH : ε * HV ≤ (1 / 256 : ℝ) / 2 := by
    have hε0 : 0 ≤ ε := le_trans (abs_nonneg _) (hdev 0)
    have : ε * HV ≤ (1 / 5760 : ℝ) * HV := mul_le_mul_of_nonneg_right hε (by norm_num [HV])
    have h2 : (1 / 5760 : ℝ) * HV ≤ (1 / 256 : ℝ) / 2 := by norm_num [HV]
    linarith
  have n0 := hnone (0 : Fin 1)
  rw [aV_0, bV_0, dV_0] at n0
  rcases lt_or_ge t (11 / 60 : ℝ) with c0 | c0
  · exact gap0 x ε hdev hεH t h0.le hHt h0.le (by linarith) hlon
  have d0 : (47 / 240 : ℝ) < t := by
    by_contra hc; push Not at hc; exact n0 ⟨by linarith, by linarith⟩
  have hHv : HV = (47 / 240 : ℝ) := rfl
  exact absurd (by linarith : t ≤ (47 / 240 : ℝ)) (not_le.2 d0)

theorem inst (x : Fin 7 → ℝ) (ε : ℝ) (hε : ε ≤ (1 / 5760 : ℝ)) (hdev : ∀ i, |x i - pr i| ≤ ε) :
    ∃ c₀ : Fin 1, Alive (mxOf x EXs hEXne) (mnOf x ENs hENne) c₀ ∧
      (∀ c, c < c₀ → ¬ Alive (mxOf x EXs hEXne) (mnOf x ENs hENne) c) ∧
      IsLeast {t : ℝ | 0 < t ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)} (mxOf x EXs hEXne c₀) :=
  landing_cert 1 (15 : ℝ) (by norm_num) pr x hp ε hdev aV bV dV TV ZV hab hd0 hdP haP hT hZ (hE ε hε) hcls EXs ENs hEXne hENne
    hEXdef hENdef hsepL HV hHL (cov x ε hε hdev) (0 : Fin 1) (by rw [dV_0, bV_0, aV_0]; norm_num)

noncomputable def sv : Fin 8 → ℝ := ![(1 : ℝ), (2 : ℝ), (8 : ℝ), (9 : ℝ), (10 : ℝ), (13 : ℝ), (15 : ℝ), (16 : ℝ)]
def sg : Fin 7 → Fin 8 := ![0, 1, 2, 3, 4, 5, 6]

theorem sv_0 : sv (0 : Fin 8) = (1 : ℝ) := rfl
theorem sv_1 : sv (1 : Fin 8) = (2 : ℝ) := rfl
theorem sv_2 : sv (2 : Fin 8) = (8 : ℝ) := rfl
theorem sv_3 : sv (3 : Fin 8) = (9 : ℝ) := rfl
theorem sv_4 : sv (4 : Fin 8) = (10 : ℝ) := rfl
theorem sv_5 : sv (5 : Fin 8) = (13 : ℝ) := rfl
theorem sv_6 : sv (6 : Fin 8) = (15 : ℝ) := rfl
theorem sv_7 : sv (7 : Fin 8) = (16 : ℝ) := rfl
theorem sg_0 : sg (0 : Fin 7) = (0 : Fin 8) := rfl
theorem sg_1 : sg (1 : Fin 7) = (1 : Fin 8) := rfl
theorem sg_2 : sg (2 : Fin 7) = (2 : Fin 8) := rfl
theorem sg_3 : sg (3 : Fin 7) = (3 : Fin 8) := rfl
theorem sg_4 : sg (4 : Fin 7) = (4 : Fin 8) := rfl
theorem sg_5 : sg (5 : Fin 7) = (5 : Fin 8) := rfl
theorem sg_6 : sg (6 : Fin 7) = (6 : Fin 8) := rfl

theorem inst_arr (v : Fin 8 → ℝ) (η : ℝ) (hη : η ≤ (1 / 11520 : ℝ)) (hv : ∀ j, |v j - sv j| ≤ η) :
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

end Fresh.CertRR.R13271



/-!
# Landing certificate `CertRR.R13275`: speeds (1, 2, 8, 9, 10, 14, 15, 16), subject index 3

Generated 2026-10-24 by `experiments/n8/cert_gen_v1.py` (exact Fractions).  Baseline readings [8, 7, 1, 1, 5, 6, 7].  Components up to the first wide one: 1.
Radius: speeds within `η ≤ 1/5120` of the baseline speeds, giving `ε = 2η ≤ 1/2560`.  Covering margin `μ = 1/256`.
`hcov` is **[PROVISIONAL: covering]**, supporting the claim that the first lonely instant of this subject is the largest exit of the first alive component.
Result `inst_arr`: for such `v`, the subject has a first isolation (a least element over all `t > 0`).  Grades: [L].
-/

open Classical

namespace Fresh.CertRR.R13275

open Fresh Fresh.LandingCert Fresh.LandingRule

noncomputable def pr : Fin 7 → ℝ := ![(8 : ℝ), (7 : ℝ), (1 : ℝ), (1 : ℝ), (5 : ℝ), (6 : ℝ), (7 : ℝ)]
noncomputable def aV : Fin 1 → ℝ := ![(9 / 40 : ℝ)]
noncomputable def bV : Fin 1 → ℝ := ![(15 / 64 : ℝ)]
noncomputable def dV : Fin 1 → ℝ := ![(1 / 64 : ℝ)]
noncomputable def TV : Fin 1 → ℝ := ![(1 / 4 : ℝ)]
def ZV : Fin 1 → ℤ := ![4]
noncomputable def HV : ℝ := (31 / 128 : ℝ)
noncomputable def EXs (c : Fin 1) : Finset (Fin 7 × ℤ) :=
  (Finset.univ ×ˢ Finset.Icc 0 (ZV c)).filter (fun q => ((q.2 : ℝ) + 1 / 8) / pr q.1 = aV c)
noncomputable def ENs (c : Fin 1) : Finset (Fin 7 × ℤ) :=
  (Finset.univ ×ˢ Finset.Icc 0 (ZV c)).filter (fun q => ((q.2 : ℝ) - 1 / 8) / pr q.1 = bV c)

theorem hp : ∀ i, 1 ≤ pr i ∧ pr i ≤ (8 : ℝ) := by intro i; fin_cases i <;> norm_num [pr]
theorem hp1 : ∀ i, 1 ≤ pr i := fun i => (hp i).1
theorem pr_0 : pr (0 : Fin 7) = (8 : ℝ) := rfl
theorem pr_1 : pr (1 : Fin 7) = (7 : ℝ) := rfl
theorem pr_2 : pr (2 : Fin 7) = (1 : ℝ) := rfl
theorem pr_3 : pr (3 : Fin 7) = (1 : ℝ) := rfl
theorem pr_4 : pr (4 : Fin 7) = (5 : ℝ) := rfl
theorem pr_5 : pr (5 : Fin 7) = (6 : ℝ) := rfl
theorem pr_6 : pr (6 : Fin 7) = (7 : ℝ) := rfl
theorem aV_0 : aV (0 : Fin 1) = (9 / 40 : ℝ) := rfl
theorem bV_0 : bV (0 : Fin 1) = (15 / 64 : ℝ) := rfl
theorem dV_0 : dV (0 : Fin 1) = (1 / 64 : ℝ) := rfl
theorem TV_0 : TV (0 : Fin 1) = (1 / 4 : ℝ) := rfl
theorem ZV_0 : ZV (0 : Fin 1) = (4 : ℤ) := rfl
theorem hab : ∀ c, aV c ≤ bV c := by intro c; fin_cases c <;> norm_num [aV, bV]
theorem hd0 : ∀ c, 0 < dV c := by intro c; fin_cases c <;> norm_num [dV]
theorem hdP : ∀ c, dV c ≤ 1 / (4 * (8 : ℝ)) := by intro c; fin_cases c <;> norm_num [dV]
theorem haP : ∀ c, dV c < aV c := by intro c; fin_cases c <;> norm_num [dV, aV]
theorem hT : ∀ c, bV c + dV c ≤ TV c := by intro c; fin_cases c <;> norm_num [bV, dV, TV]
theorem hZ : ∀ c, ((8 : ℝ) + 1) * TV c + 1 ≤ (ZV c : ℝ) := by intro c; fin_cases c <;> norm_num [TV, ZV]
theorem hE (ε : ℝ) (hε : ε ≤ (1 / 2560 : ℝ)) : ∀ c, 8 * ((ZV c : ℝ) + 1) * ε ≤ dV c := by
  intro c; fin_cases c <;> norm_num [ZV, dV] <;> linarith
theorem hcls : ∀ c i, ∀ z : ℤ, 0 ≤ z → z ≤ ZV c →
    ((z : ℝ) + 1 / 8) / pr i ≤ aV c - dV c ∨ bV c + dV c ≤ ((z : ℝ) - 1 / 8) / pr i ∨
      ((z : ℝ) + 1 / 8) / pr i = aV c ∨ ((z : ℝ) - 1 / 8) / pr i = bV c := by
  intro c i z h0 h1
  fin_cases c <;> fin_cases i <;> simp [ZV] at h1 <;> interval_cases z <;> norm_num [pr, aV, bV, dV]
theorem hEXne : ∀ c, (EXs c).Nonempty := by
  intro c
  fin_cases c
  · exact ⟨(4, 1), by simp [EXs, ZV, pr, aV] <;> norm_num⟩
theorem hENne : ∀ c, (ENs c).Nonempty := by
  intro c
  fin_cases c
  · exact ⟨(0, 2), by simp [ENs, ZV, pr, bV] <;> norm_num⟩
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
    (hHt : t ≤ HV) (h1 : (0 : ℝ) ≤ t) (h2 : t ≤ (139 / 640 : ℝ)) (hlon : ∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)) : False := by
  rcases le_total t (31 / 256 : ℝ) with hs0 | hs0
  · exact zone_kill_gen pr x ε HV (1 / 256 : ℝ) hp1 hdev hεH (by norm_num) (2 : Fin 7) 0 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (2 : Fin 7))
  rcases le_total t (35 / 256 : ℝ) with hs1 | hs1
  · exact zone_kill_gen pr x ε HV (1 / 256 : ℝ) hp1 hdev hεH (by norm_num) (0 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (0 : Fin 7))
  rcases le_total t (281 / 1792 : ℝ) with hs2 | hs2
  · exact zone_kill_gen pr x ε HV (1 / 256 : ℝ) hp1 hdev hεH (by norm_num) (1 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (1 : Fin 7))
  rcases le_total t (47 / 256 : ℝ) with hs3 | hs3
  · exact zone_kill_gen pr x ε HV (1 / 256 : ℝ) hp1 hdev hεH (by norm_num) (5 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (5 : Fin 7))
  exact zone_kill_gen pr x ε HV (1 / 256 : ℝ) hp1 hdev hεH (by norm_num) (4 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (4 : Fin 7))
theorem cov (x : Fin 7 → ℝ) (ε : ℝ) (hε : ε ≤ (1 / 2560 : ℝ)) (hdev : ∀ i, |x i - pr i| ≤ ε) :
    ∀ t : ℝ, 0 < t → t ≤ HV → (∀ c, ¬ (aV c - dV c / 2 ≤ t ∧ t ≤ bV c + dV c / 2)) →
      ¬ (∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)) := by
  intro t h0 hHt hnone hlon
  have hεH : ε * HV ≤ (1 / 256 : ℝ) / 2 := by
    have hε0 : 0 ≤ ε := le_trans (abs_nonneg _) (hdev 0)
    have : ε * HV ≤ (1 / 2560 : ℝ) * HV := mul_le_mul_of_nonneg_right hε (by norm_num [HV])
    have h2 : (1 / 2560 : ℝ) * HV ≤ (1 / 256 : ℝ) / 2 := by norm_num [HV]
    linarith
  have n0 := hnone (0 : Fin 1)
  rw [aV_0, bV_0, dV_0] at n0
  rcases lt_or_ge t (139 / 640 : ℝ) with c0 | c0
  · exact gap0 x ε hdev hεH t h0.le hHt h0.le (by linarith) hlon
  have d0 : (31 / 128 : ℝ) < t := by
    by_contra hc; push Not at hc; exact n0 ⟨by linarith, by linarith⟩
  have hHv : HV = (31 / 128 : ℝ) := rfl
  exact absurd (by linarith : t ≤ (31 / 128 : ℝ)) (not_le.2 d0)

theorem inst (x : Fin 7 → ℝ) (ε : ℝ) (hε : ε ≤ (1 / 2560 : ℝ)) (hdev : ∀ i, |x i - pr i| ≤ ε) :
    ∃ c₀ : Fin 1, Alive (mxOf x EXs hEXne) (mnOf x ENs hENne) c₀ ∧
      (∀ c, c < c₀ → ¬ Alive (mxOf x EXs hEXne) (mnOf x ENs hENne) c) ∧
      IsLeast {t : ℝ | 0 < t ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)} (mxOf x EXs hEXne c₀) :=
  landing_cert 1 (8 : ℝ) (by norm_num) pr x hp ε hdev aV bV dV TV ZV hab hd0 hdP haP hT hZ (hE ε hε) hcls EXs ENs hEXne hENne
    hEXdef hENdef hsepL HV hHL (cov x ε hε hdev) (0 : Fin 1) (by rw [dV_0, bV_0, aV_0]; norm_num)

noncomputable def sv : Fin 8 → ℝ := ![(1 : ℝ), (2 : ℝ), (8 : ℝ), (9 : ℝ), (10 : ℝ), (14 : ℝ), (15 : ℝ), (16 : ℝ)]
def sg : Fin 7 → Fin 8 := ![0, 1, 2, 4, 5, 6, 7]

theorem sv_0 : sv (0 : Fin 8) = (1 : ℝ) := rfl
theorem sv_1 : sv (1 : Fin 8) = (2 : ℝ) := rfl
theorem sv_2 : sv (2 : Fin 8) = (8 : ℝ) := rfl
theorem sv_3 : sv (3 : Fin 8) = (9 : ℝ) := rfl
theorem sv_4 : sv (4 : Fin 8) = (10 : ℝ) := rfl
theorem sv_5 : sv (5 : Fin 8) = (14 : ℝ) := rfl
theorem sv_6 : sv (6 : Fin 8) = (15 : ℝ) := rfl
theorem sv_7 : sv (7 : Fin 8) = (16 : ℝ) := rfl
theorem sg_0 : sg (0 : Fin 7) = (0 : Fin 8) := rfl
theorem sg_1 : sg (1 : Fin 7) = (1 : Fin 8) := rfl
theorem sg_2 : sg (2 : Fin 7) = (2 : Fin 8) := rfl
theorem sg_3 : sg (3 : Fin 7) = (4 : Fin 8) := rfl
theorem sg_4 : sg (4 : Fin 7) = (5 : Fin 8) := rfl
theorem sg_5 : sg (5 : Fin 7) = (6 : Fin 8) := rfl
theorem sg_6 : sg (6 : Fin 7) = (7 : Fin 8) := rfl

theorem inst_arr (v : Fin 8 → ℝ) (η : ℝ) (hη : η ≤ (1 / 5120 : ℝ)) (hv : ∀ j, |v j - sv j| ≤ η) :
    ∃ c₀ : Fin 1, Alive (mxOf (fun i => |v (sg i) - v (3 : Fin 8)|) EXs hEXne) (mnOf (fun i => |v (sg i) - v (3 : Fin 8)|) ENs hENne) c₀ ∧
      (∀ c, c < c₀ → ¬ Alive (mxOf (fun i => |v (sg i) - v (3 : Fin 8)|) EXs hEXne) (mnOf (fun i => |v (sg i) - v (3 : Fin 8)|) ENs hENne) c) ∧
      IsLeast {t : ℝ | 0 < t ∧ IsolatedAt v (3 : Fin 8) t} (mxOf (fun i => |v (sg i) - v (3 : Fin 8)|) EXs hEXne c₀) := by
  have hσk : ∀ i, sg i ≠ (3 : Fin 8) := by decide
  have hσ : ∀ j : Fin 8, j ≠ (3 : Fin 8) → ∃ i, sg i = j := by decide
  have hpr : ∀ i, pr i = |sv (sg i) - sv (3 : Fin 8)| := by
    intro i; rcases fin7_cases i with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6, sv_0, sv_1, sv_2, sv_3, sv_4, sv_5, sv_6, sv_7, sg_0, sg_1, sg_2, sg_3, sg_4, sg_5, sg_6]
  have hdev : ∀ i, |(|v (sg i) - v (3 : Fin 8)| - pr i)| ≤ 2 * η := by
    intro i; rw [hpr i]; exact reading_dev v sv η hv (sg i) (3 : Fin 8)
  obtain ⟨c₀, hal, hbf, hT0⟩ := inst (fun i => |v (sg i) - v (3 : Fin 8)|) (2 * η) (by linarith) hdev
  have hset : {t : ℝ | 0 < t ∧ IsolatedAt v (3 : Fin 8) t} =
      {t : ℝ | 0 < t ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (|v (sg i) - v (3 : Fin 8)| * t)} := by
    ext t; simp only [Set.mem_setOf_eq]; rw [iso_iff_readings v (3 : Fin 8) sg hσk hσ t]
  rw [hset]; exact ⟨c₀, hal, hbf, hT0⟩

#print axioms inst_arr

end Fresh.CertRR.R13275



/-!
# Landing certificate `CertRR.R13279`: speeds (1, 2, 8, 9, 10, 14, 15, 16), subject index 7

Generated 2026-10-24 by `experiments/n8/cert_gen_v1.py` (exact Fractions).  Baseline readings [15, 14, 8, 7, 6, 2, 1].  Components up to the first wide one: 1.
Radius: speeds within `η ≤ 1/11520` of the baseline speeds, giving `ε = 2η ≤ 1/5760`.  Covering margin `μ = 1/256`.
`hcov` is **[PROVISIONAL: covering]**, supporting the claim that the first lonely instant of this subject is the largest exit of the first alive component.
Result `inst_arr`: for such `v`, the subject has a first isolation (a least element over all `t > 0`).  Grades: [L].
-/

open Classical

namespace Fresh.CertRR.R13279

open Fresh Fresh.LandingCert Fresh.LandingRule

noncomputable def pr : Fin 7 → ℝ := ![(15 : ℝ), (14 : ℝ), (8 : ℝ), (7 : ℝ), (6 : ℝ), (2 : ℝ), (1 : ℝ)]
noncomputable def aV : Fin 1 → ℝ := ![(3 / 16 : ℝ)]
noncomputable def bV : Fin 1 → ℝ := ![(23 / 120 : ℝ)]
noncomputable def dV : Fin 1 → ℝ := ![(1 / 120 : ℝ)]
noncomputable def TV : Fin 1 → ℝ := ![(1 / 5 : ℝ)]
def ZV : Fin 1 → ℤ := ![5]
noncomputable def HV : ℝ := (47 / 240 : ℝ)
noncomputable def EXs (c : Fin 1) : Finset (Fin 7 × ℤ) :=
  (Finset.univ ×ˢ Finset.Icc 0 (ZV c)).filter (fun q => ((q.2 : ℝ) + 1 / 8) / pr q.1 = aV c)
noncomputable def ENs (c : Fin 1) : Finset (Fin 7 × ℤ) :=
  (Finset.univ ×ˢ Finset.Icc 0 (ZV c)).filter (fun q => ((q.2 : ℝ) - 1 / 8) / pr q.1 = bV c)

theorem hp : ∀ i, 1 ≤ pr i ∧ pr i ≤ (15 : ℝ) := by intro i; fin_cases i <;> norm_num [pr]
theorem hp1 : ∀ i, 1 ≤ pr i := fun i => (hp i).1
theorem pr_0 : pr (0 : Fin 7) = (15 : ℝ) := rfl
theorem pr_1 : pr (1 : Fin 7) = (14 : ℝ) := rfl
theorem pr_2 : pr (2 : Fin 7) = (8 : ℝ) := rfl
theorem pr_3 : pr (3 : Fin 7) = (7 : ℝ) := rfl
theorem pr_4 : pr (4 : Fin 7) = (6 : ℝ) := rfl
theorem pr_5 : pr (5 : Fin 7) = (2 : ℝ) := rfl
theorem pr_6 : pr (6 : Fin 7) = (1 : ℝ) := rfl
theorem aV_0 : aV (0 : Fin 1) = (3 / 16 : ℝ) := rfl
theorem bV_0 : bV (0 : Fin 1) = (23 / 120 : ℝ) := rfl
theorem dV_0 : dV (0 : Fin 1) = (1 / 120 : ℝ) := rfl
theorem TV_0 : TV (0 : Fin 1) = (1 / 5 : ℝ) := rfl
theorem ZV_0 : ZV (0 : Fin 1) = (5 : ℤ) := rfl
theorem hab : ∀ c, aV c ≤ bV c := by intro c; fin_cases c <;> norm_num [aV, bV]
theorem hd0 : ∀ c, 0 < dV c := by intro c; fin_cases c <;> norm_num [dV]
theorem hdP : ∀ c, dV c ≤ 1 / (4 * (15 : ℝ)) := by intro c; fin_cases c <;> norm_num [dV]
theorem haP : ∀ c, dV c < aV c := by intro c; fin_cases c <;> norm_num [dV, aV]
theorem hT : ∀ c, bV c + dV c ≤ TV c := by intro c; fin_cases c <;> norm_num [bV, dV, TV]
theorem hZ : ∀ c, ((15 : ℝ) + 1) * TV c + 1 ≤ (ZV c : ℝ) := by intro c; fin_cases c <;> norm_num [TV, ZV]
theorem hE (ε : ℝ) (hε : ε ≤ (1 / 5760 : ℝ)) : ∀ c, 8 * ((ZV c : ℝ) + 1) * ε ≤ dV c := by
  intro c; fin_cases c <;> norm_num [ZV, dV] <;> linarith
theorem hcls : ∀ c i, ∀ z : ℤ, 0 ≤ z → z ≤ ZV c →
    ((z : ℝ) + 1 / 8) / pr i ≤ aV c - dV c ∨ bV c + dV c ≤ ((z : ℝ) - 1 / 8) / pr i ∨
      ((z : ℝ) + 1 / 8) / pr i = aV c ∨ ((z : ℝ) - 1 / 8) / pr i = bV c := by
  intro c i z h0 h1
  fin_cases c <;> fin_cases i <;> simp [ZV] at h1 <;> interval_cases z <;> norm_num [pr, aV, bV, dV]
theorem hEXne : ∀ c, (EXs c).Nonempty := by
  intro c
  fin_cases c
  · exact ⟨(4, 1), by simp [EXs, ZV, pr, aV] <;> norm_num⟩
theorem hENne : ∀ c, (ENs c).Nonempty := by
  intro c
  fin_cases c
  · exact ⟨(0, 3), by simp [ENs, ZV, pr, bV] <;> norm_num⟩
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
    (hHt : t ≤ HV) (h1 : (0 : ℝ) ≤ t) (h2 : t ≤ (11 / 60 : ℝ)) (hlon : ∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)) : False := by
  rcases le_total t (31 / 256 : ℝ) with hs0 | hs0
  · exact zone_kill_gen pr x ε HV (1 / 256 : ℝ) hp1 hdev hεH (by norm_num) (6 : Fin 7) 0 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (6 : Fin 7))
  rcases le_total t (35 / 256 : ℝ) with hs1 | hs1
  · exact zone_kill_gen pr x ε HV (1 / 256 : ℝ) hp1 hdev hεH (by norm_num) (2 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (2 : Fin 7))
  rcases le_total t (281 / 1792 : ℝ) with hs2 | hs2
  · exact zone_kill_gen pr x ε HV (1 / 256 : ℝ) hp1 hdev hεH (by norm_num) (3 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (3 : Fin 7))
  exact zone_kill_gen pr x ε HV (1 / 256 : ℝ) hp1 hdev hεH (by norm_num) (4 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (4 : Fin 7))
theorem cov (x : Fin 7 → ℝ) (ε : ℝ) (hε : ε ≤ (1 / 5760 : ℝ)) (hdev : ∀ i, |x i - pr i| ≤ ε) :
    ∀ t : ℝ, 0 < t → t ≤ HV → (∀ c, ¬ (aV c - dV c / 2 ≤ t ∧ t ≤ bV c + dV c / 2)) →
      ¬ (∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)) := by
  intro t h0 hHt hnone hlon
  have hεH : ε * HV ≤ (1 / 256 : ℝ) / 2 := by
    have hε0 : 0 ≤ ε := le_trans (abs_nonneg _) (hdev 0)
    have : ε * HV ≤ (1 / 5760 : ℝ) * HV := mul_le_mul_of_nonneg_right hε (by norm_num [HV])
    have h2 : (1 / 5760 : ℝ) * HV ≤ (1 / 256 : ℝ) / 2 := by norm_num [HV]
    linarith
  have n0 := hnone (0 : Fin 1)
  rw [aV_0, bV_0, dV_0] at n0
  rcases lt_or_ge t (11 / 60 : ℝ) with c0 | c0
  · exact gap0 x ε hdev hεH t h0.le hHt h0.le (by linarith) hlon
  have d0 : (47 / 240 : ℝ) < t := by
    by_contra hc; push Not at hc; exact n0 ⟨by linarith, by linarith⟩
  have hHv : HV = (47 / 240 : ℝ) := rfl
  exact absurd (by linarith : t ≤ (47 / 240 : ℝ)) (not_le.2 d0)

theorem inst (x : Fin 7 → ℝ) (ε : ℝ) (hε : ε ≤ (1 / 5760 : ℝ)) (hdev : ∀ i, |x i - pr i| ≤ ε) :
    ∃ c₀ : Fin 1, Alive (mxOf x EXs hEXne) (mnOf x ENs hENne) c₀ ∧
      (∀ c, c < c₀ → ¬ Alive (mxOf x EXs hEXne) (mnOf x ENs hENne) c) ∧
      IsLeast {t : ℝ | 0 < t ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)} (mxOf x EXs hEXne c₀) :=
  landing_cert 1 (15 : ℝ) (by norm_num) pr x hp ε hdev aV bV dV TV ZV hab hd0 hdP haP hT hZ (hE ε hε) hcls EXs ENs hEXne hENne
    hEXdef hENdef hsepL HV hHL (cov x ε hε hdev) (0 : Fin 1) (by rw [dV_0, bV_0, aV_0]; norm_num)

noncomputable def sv : Fin 8 → ℝ := ![(1 : ℝ), (2 : ℝ), (8 : ℝ), (9 : ℝ), (10 : ℝ), (14 : ℝ), (15 : ℝ), (16 : ℝ)]
def sg : Fin 7 → Fin 8 := ![0, 1, 2, 3, 4, 5, 6]

theorem sv_0 : sv (0 : Fin 8) = (1 : ℝ) := rfl
theorem sv_1 : sv (1 : Fin 8) = (2 : ℝ) := rfl
theorem sv_2 : sv (2 : Fin 8) = (8 : ℝ) := rfl
theorem sv_3 : sv (3 : Fin 8) = (9 : ℝ) := rfl
theorem sv_4 : sv (4 : Fin 8) = (10 : ℝ) := rfl
theorem sv_5 : sv (5 : Fin 8) = (14 : ℝ) := rfl
theorem sv_6 : sv (6 : Fin 8) = (15 : ℝ) := rfl
theorem sv_7 : sv (7 : Fin 8) = (16 : ℝ) := rfl
theorem sg_0 : sg (0 : Fin 7) = (0 : Fin 8) := rfl
theorem sg_1 : sg (1 : Fin 7) = (1 : Fin 8) := rfl
theorem sg_2 : sg (2 : Fin 7) = (2 : Fin 8) := rfl
theorem sg_3 : sg (3 : Fin 7) = (3 : Fin 8) := rfl
theorem sg_4 : sg (4 : Fin 7) = (4 : Fin 8) := rfl
theorem sg_5 : sg (5 : Fin 7) = (5 : Fin 8) := rfl
theorem sg_6 : sg (6 : Fin 7) = (6 : Fin 8) := rfl

theorem inst_arr (v : Fin 8 → ℝ) (η : ℝ) (hη : η ≤ (1 / 11520 : ℝ)) (hv : ∀ j, |v j - sv j| ≤ η) :
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

end Fresh.CertRR.R13279



/-!
# Landing certificate `CertRR.R13280`: speeds (1, 2, 8, 9, 11, 12, 13, 14), subject index 0

Generated 2026-10-24 by `experiments/n8/cert_gen_v1.py` (exact Fractions).  Baseline readings [1, 7, 8, 10, 11, 12, 13].  Components up to the first wide one: 1.
Radius: speeds within `η ≤ 1/7262` of the baseline speeds, giving `ε = 2η ≤ 1/3631`.  Covering margin `μ = 1/512`.
`hcov` is **[PROVISIONAL: covering]**, supporting the claim that the first lonely instant of this subject is the largest exit of the first alive component.
Result `inst_arr`: for such `v`, the subject has a first isolation (a least element over all `t > 0`).  Grades: [L].
-/

open Classical

namespace Fresh.CertRR.R13280

open Fresh Fresh.LandingCert Fresh.LandingRule

noncomputable def pr : Fin 7 → ℝ := ![(1 : ℝ), (7 : ℝ), (8 : ℝ), (10 : ℝ), (11 : ℝ), (12 : ℝ), (13 : ℝ)]
noncomputable def aV : Fin 1 → ℝ := ![(17 / 80 : ℝ)]
noncomputable def bV : Fin 1 → ℝ := ![(23 / 104 : ℝ)]
noncomputable def dV : Fin 1 → ℝ := ![(11 / 832 : ℝ)]
noncomputable def TV : Fin 1 → ℝ := ![(15 / 64 : ℝ)]
def ZV : Fin 1 → ℤ := ![5]
noncomputable def HV : ℝ := (379 / 1664 : ℝ)
noncomputable def EXs (c : Fin 1) : Finset (Fin 7 × ℤ) :=
  (Finset.univ ×ˢ Finset.Icc 0 (ZV c)).filter (fun q => ((q.2 : ℝ) + 1 / 8) / pr q.1 = aV c)
noncomputable def ENs (c : Fin 1) : Finset (Fin 7 × ℤ) :=
  (Finset.univ ×ˢ Finset.Icc 0 (ZV c)).filter (fun q => ((q.2 : ℝ) - 1 / 8) / pr q.1 = bV c)

theorem hp : ∀ i, 1 ≤ pr i ∧ pr i ≤ (13 : ℝ) := by intro i; fin_cases i <;> norm_num [pr]
theorem hp1 : ∀ i, 1 ≤ pr i := fun i => (hp i).1
theorem pr_0 : pr (0 : Fin 7) = (1 : ℝ) := rfl
theorem pr_1 : pr (1 : Fin 7) = (7 : ℝ) := rfl
theorem pr_2 : pr (2 : Fin 7) = (8 : ℝ) := rfl
theorem pr_3 : pr (3 : Fin 7) = (10 : ℝ) := rfl
theorem pr_4 : pr (4 : Fin 7) = (11 : ℝ) := rfl
theorem pr_5 : pr (5 : Fin 7) = (12 : ℝ) := rfl
theorem pr_6 : pr (6 : Fin 7) = (13 : ℝ) := rfl
theorem aV_0 : aV (0 : Fin 1) = (17 / 80 : ℝ) := rfl
theorem bV_0 : bV (0 : Fin 1) = (23 / 104 : ℝ) := rfl
theorem dV_0 : dV (0 : Fin 1) = (11 / 832 : ℝ) := rfl
theorem TV_0 : TV (0 : Fin 1) = (15 / 64 : ℝ) := rfl
theorem ZV_0 : ZV (0 : Fin 1) = (5 : ℤ) := rfl
theorem hab : ∀ c, aV c ≤ bV c := by intro c; fin_cases c <;> norm_num [aV, bV]
theorem hd0 : ∀ c, 0 < dV c := by intro c; fin_cases c <;> norm_num [dV]
theorem hdP : ∀ c, dV c ≤ 1 / (4 * (13 : ℝ)) := by intro c; fin_cases c <;> norm_num [dV]
theorem haP : ∀ c, dV c < aV c := by intro c; fin_cases c <;> norm_num [dV, aV]
theorem hT : ∀ c, bV c + dV c ≤ TV c := by intro c; fin_cases c <;> norm_num [bV, dV, TV]
theorem hZ : ∀ c, ((13 : ℝ) + 1) * TV c + 1 ≤ (ZV c : ℝ) := by intro c; fin_cases c <;> norm_num [TV, ZV]
theorem hE (ε : ℝ) (hε : ε ≤ (1 / 3631 : ℝ)) : ∀ c, 8 * ((ZV c : ℝ) + 1) * ε ≤ dV c := by
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
  · exact ⟨(6, 3), by simp [ENs, ZV, pr, bV] <;> norm_num⟩
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
    (hHt : t ≤ HV) (h1 : (0 : ℝ) ≤ t) (h2 : t ≤ (1713 / 8320 : ℝ)) (hlon : ∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)) : False := by
  rcases le_total t (63 / 512 : ℝ) with hs0 | hs0
  · exact zone_kill_gen pr x ε HV (1 / 512 : ℝ) hp1 hdev hεH (by norm_num) (0 : Fin 7) 0 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (0 : Fin 7))
  rcases le_total t (71 / 512 : ℝ) with hs1 | hs1
  · exact zone_kill_gen pr x ε HV (1 / 512 : ℝ) hp1 hdev hεH (by norm_num) (2 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (2 : Fin 7))
  rcases le_total t (569 / 3584 : ℝ) with hs2 | hs2
  · exact zone_kill_gen pr x ε HV (1 / 512 : ℝ) hp1 hdev hεH (by norm_num) (1 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (1 : Fin 7))
  rcases le_total t (269 / 1536 : ℝ) with hs3 | hs3
  · exact zone_kill_gen pr x ε HV (1 / 512 : ℝ) hp1 hdev hεH (by norm_num) (5 : Fin 7) 2 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (5 : Fin 7))
  rcases le_total t (1077 / 5632 : ℝ) with hs4 | hs4
  · exact zone_kill_gen pr x ε HV (1 / 512 : ℝ) hp1 hdev hεH (by norm_num) (4 : Fin 7) 2 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (4 : Fin 7))
  exact zone_kill_gen pr x ε HV (1 / 512 : ℝ) hp1 hdev hεH (by norm_num) (3 : Fin 7) 2 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (3 : Fin 7))
theorem cov (x : Fin 7 → ℝ) (ε : ℝ) (hε : ε ≤ (1 / 3631 : ℝ)) (hdev : ∀ i, |x i - pr i| ≤ ε) :
    ∀ t : ℝ, 0 < t → t ≤ HV → (∀ c, ¬ (aV c - dV c / 2 ≤ t ∧ t ≤ bV c + dV c / 2)) →
      ¬ (∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)) := by
  intro t h0 hHt hnone hlon
  have hεH : ε * HV ≤ (1 / 512 : ℝ) / 2 := by
    have hε0 : 0 ≤ ε := le_trans (abs_nonneg _) (hdev 0)
    have : ε * HV ≤ (1 / 3631 : ℝ) * HV := mul_le_mul_of_nonneg_right hε (by norm_num [HV])
    have h2 : (1 / 3631 : ℝ) * HV ≤ (1 / 512 : ℝ) / 2 := by norm_num [HV]
    linarith
  have n0 := hnone (0 : Fin 1)
  rw [aV_0, bV_0, dV_0] at n0
  rcases lt_or_ge t (1713 / 8320 : ℝ) with c0 | c0
  · exact gap0 x ε hdev hεH t h0.le hHt h0.le (by linarith) hlon
  have d0 : (379 / 1664 : ℝ) < t := by
    by_contra hc; push Not at hc; exact n0 ⟨by linarith, by linarith⟩
  have hHv : HV = (379 / 1664 : ℝ) := rfl
  exact absurd (by linarith : t ≤ (379 / 1664 : ℝ)) (not_le.2 d0)

theorem inst (x : Fin 7 → ℝ) (ε : ℝ) (hε : ε ≤ (1 / 3631 : ℝ)) (hdev : ∀ i, |x i - pr i| ≤ ε) :
    ∃ c₀ : Fin 1, Alive (mxOf x EXs hEXne) (mnOf x ENs hENne) c₀ ∧
      (∀ c, c < c₀ → ¬ Alive (mxOf x EXs hEXne) (mnOf x ENs hENne) c) ∧
      IsLeast {t : ℝ | 0 < t ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)} (mxOf x EXs hEXne c₀) :=
  landing_cert 1 (13 : ℝ) (by norm_num) pr x hp ε hdev aV bV dV TV ZV hab hd0 hdP haP hT hZ (hE ε hε) hcls EXs ENs hEXne hENne
    hEXdef hENdef hsepL HV hHL (cov x ε hε hdev) (0 : Fin 1) (by rw [dV_0, bV_0, aV_0]; norm_num)

noncomputable def sv : Fin 8 → ℝ := ![(1 : ℝ), (2 : ℝ), (8 : ℝ), (9 : ℝ), (11 : ℝ), (12 : ℝ), (13 : ℝ), (14 : ℝ)]
def sg : Fin 7 → Fin 8 := ![1, 2, 3, 4, 5, 6, 7]

theorem sv_0 : sv (0 : Fin 8) = (1 : ℝ) := rfl
theorem sv_1 : sv (1 : Fin 8) = (2 : ℝ) := rfl
theorem sv_2 : sv (2 : Fin 8) = (8 : ℝ) := rfl
theorem sv_3 : sv (3 : Fin 8) = (9 : ℝ) := rfl
theorem sv_4 : sv (4 : Fin 8) = (11 : ℝ) := rfl
theorem sv_5 : sv (5 : Fin 8) = (12 : ℝ) := rfl
theorem sv_6 : sv (6 : Fin 8) = (13 : ℝ) := rfl
theorem sv_7 : sv (7 : Fin 8) = (14 : ℝ) := rfl
theorem sg_0 : sg (0 : Fin 7) = (1 : Fin 8) := rfl
theorem sg_1 : sg (1 : Fin 7) = (2 : Fin 8) := rfl
theorem sg_2 : sg (2 : Fin 7) = (3 : Fin 8) := rfl
theorem sg_3 : sg (3 : Fin 7) = (4 : Fin 8) := rfl
theorem sg_4 : sg (4 : Fin 7) = (5 : Fin 8) := rfl
theorem sg_5 : sg (5 : Fin 7) = (6 : Fin 8) := rfl
theorem sg_6 : sg (6 : Fin 7) = (7 : Fin 8) := rfl

theorem inst_arr (v : Fin 8 → ℝ) (η : ℝ) (hη : η ≤ (1 / 7262 : ℝ)) (hv : ∀ j, |v j - sv j| ≤ η) :
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

end Fresh.CertRR.R13280



/-!
# Landing certificate `CertRR.R13288`: speeds (1, 2, 8, 9, 11, 12, 13, 15), subject index 0

Generated 2026-10-24 by `experiments/n8/cert_gen_v1.py` (exact Fractions).  Baseline readings [1, 7, 8, 10, 11, 12, 14].  Components up to the first wide one: 1.
Radius: speeds within `η ≤ 1/18432` of the baseline speeds, giving `ε = 2η ≤ 1/9216`.  Covering margin `μ = 1/512`.
`hcov` is **[PROVISIONAL: covering]**, supporting the claim that the first lonely instant of this subject is the largest exit of the first alive component.
Result `inst_arr`: for such `v`, the subject has a first isolation (a least element over all `t > 0`).  Grades: [L].
-/

open Classical

namespace Fresh.CertRR.R13288

open Fresh Fresh.LandingCert Fresh.LandingRule

noncomputable def pr : Fin 7 → ℝ := ![(1 : ℝ), (7 : ℝ), (8 : ℝ), (10 : ℝ), (11 : ℝ), (12 : ℝ), (14 : ℝ)]
noncomputable def aV : Fin 1 → ℝ := ![(25 / 112 : ℝ)]
noncomputable def bV : Fin 1 → ℝ := ![(15 / 64 : ℝ)]
noncomputable def dV : Fin 1 → ℝ := ![(1 / 192 : ℝ)]
noncomputable def TV : Fin 1 → ℝ := ![(23 / 96 : ℝ)]
def ZV : Fin 1 → ℤ := ![5]
noncomputable def HV : ℝ := (91 / 384 : ℝ)
noncomputable def EXs (c : Fin 1) : Finset (Fin 7 × ℤ) :=
  (Finset.univ ×ˢ Finset.Icc 0 (ZV c)).filter (fun q => ((q.2 : ℝ) + 1 / 8) / pr q.1 = aV c)
noncomputable def ENs (c : Fin 1) : Finset (Fin 7 × ℤ) :=
  (Finset.univ ×ˢ Finset.Icc 0 (ZV c)).filter (fun q => ((q.2 : ℝ) - 1 / 8) / pr q.1 = bV c)

theorem hp : ∀ i, 1 ≤ pr i ∧ pr i ≤ (14 : ℝ) := by intro i; fin_cases i <;> norm_num [pr]
theorem hp1 : ∀ i, 1 ≤ pr i := fun i => (hp i).1
theorem pr_0 : pr (0 : Fin 7) = (1 : ℝ) := rfl
theorem pr_1 : pr (1 : Fin 7) = (7 : ℝ) := rfl
theorem pr_2 : pr (2 : Fin 7) = (8 : ℝ) := rfl
theorem pr_3 : pr (3 : Fin 7) = (10 : ℝ) := rfl
theorem pr_4 : pr (4 : Fin 7) = (11 : ℝ) := rfl
theorem pr_5 : pr (5 : Fin 7) = (12 : ℝ) := rfl
theorem pr_6 : pr (6 : Fin 7) = (14 : ℝ) := rfl
theorem aV_0 : aV (0 : Fin 1) = (25 / 112 : ℝ) := rfl
theorem bV_0 : bV (0 : Fin 1) = (15 / 64 : ℝ) := rfl
theorem dV_0 : dV (0 : Fin 1) = (1 / 192 : ℝ) := rfl
theorem TV_0 : TV (0 : Fin 1) = (23 / 96 : ℝ) := rfl
theorem ZV_0 : ZV (0 : Fin 1) = (5 : ℤ) := rfl
theorem hab : ∀ c, aV c ≤ bV c := by intro c; fin_cases c <;> norm_num [aV, bV]
theorem hd0 : ∀ c, 0 < dV c := by intro c; fin_cases c <;> norm_num [dV]
theorem hdP : ∀ c, dV c ≤ 1 / (4 * (14 : ℝ)) := by intro c; fin_cases c <;> norm_num [dV]
theorem haP : ∀ c, dV c < aV c := by intro c; fin_cases c <;> norm_num [dV, aV]
theorem hT : ∀ c, bV c + dV c ≤ TV c := by intro c; fin_cases c <;> norm_num [bV, dV, TV]
theorem hZ : ∀ c, ((14 : ℝ) + 1) * TV c + 1 ≤ (ZV c : ℝ) := by intro c; fin_cases c <;> norm_num [TV, ZV]
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
  · exact ⟨(6, 3), by simp [EXs, ZV, pr, aV] <;> norm_num⟩
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

theorem gap0 (x : Fin 7 → ℝ) (ε : ℝ) (hdev : ∀ i, |x i - pr i| ≤ ε) (hεH : ε * HV ≤ (1 / 512 : ℝ) / 2) (t : ℝ) (h0 : 0 ≤ t)
    (hHt : t ≤ HV) (h1 : (0 : ℝ) ≤ t) (h2 : t ≤ (593 / 2688 : ℝ)) (hlon : ∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)) : False := by
  rcases le_total t (63 / 512 : ℝ) with hs0 | hs0
  · exact zone_kill_gen pr x ε HV (1 / 512 : ℝ) hp1 hdev hεH (by norm_num) (0 : Fin 7) 0 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (0 : Fin 7))
  rcases le_total t (71 / 512 : ℝ) with hs1 | hs1
  · exact zone_kill_gen pr x ε HV (1 / 512 : ℝ) hp1 hdev hεH (by norm_num) (2 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (2 : Fin 7))
  rcases le_total t (569 / 3584 : ℝ) with hs2 | hs2
  · exact zone_kill_gen pr x ε HV (1 / 512 : ℝ) hp1 hdev hεH (by norm_num) (1 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (1 : Fin 7))
  rcases le_total t (269 / 1536 : ℝ) with hs3 | hs3
  · exact zone_kill_gen pr x ε HV (1 / 512 : ℝ) hp1 hdev hεH (by norm_num) (5 : Fin 7) 2 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (5 : Fin 7))
  rcases le_total t (1077 / 5632 : ℝ) with hs4 | hs4
  · exact zone_kill_gen pr x ε HV (1 / 512 : ℝ) hp1 hdev hεH (by norm_num) (4 : Fin 7) 2 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (4 : Fin 7))
  rcases le_total t (539 / 2560 : ℝ) with hs5 | hs5
  · exact zone_kill_gen pr x ε HV (1 / 512 : ℝ) hp1 hdev hεH (by norm_num) (3 : Fin 7) 2 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (3 : Fin 7))
  exact zone_kill_gen pr x ε HV (1 / 512 : ℝ) hp1 hdev hεH (by norm_num) (6 : Fin 7) 3 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (6 : Fin 7))
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
  rcases lt_or_ge t (593 / 2688 : ℝ) with c0 | c0
  · exact gap0 x ε hdev hεH t h0.le hHt h0.le (by linarith) hlon
  have d0 : (91 / 384 : ℝ) < t := by
    by_contra hc; push Not at hc; exact n0 ⟨by linarith, by linarith⟩
  have hHv : HV = (91 / 384 : ℝ) := rfl
  exact absurd (by linarith : t ≤ (91 / 384 : ℝ)) (not_le.2 d0)

theorem inst (x : Fin 7 → ℝ) (ε : ℝ) (hε : ε ≤ (1 / 9216 : ℝ)) (hdev : ∀ i, |x i - pr i| ≤ ε) :
    ∃ c₀ : Fin 1, Alive (mxOf x EXs hEXne) (mnOf x ENs hENne) c₀ ∧
      (∀ c, c < c₀ → ¬ Alive (mxOf x EXs hEXne) (mnOf x ENs hENne) c) ∧
      IsLeast {t : ℝ | 0 < t ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)} (mxOf x EXs hEXne c₀) :=
  landing_cert 1 (14 : ℝ) (by norm_num) pr x hp ε hdev aV bV dV TV ZV hab hd0 hdP haP hT hZ (hE ε hε) hcls EXs ENs hEXne hENne
    hEXdef hENdef hsepL HV hHL (cov x ε hε hdev) (0 : Fin 1) (by rw [dV_0, bV_0, aV_0]; norm_num)

noncomputable def sv : Fin 8 → ℝ := ![(1 : ℝ), (2 : ℝ), (8 : ℝ), (9 : ℝ), (11 : ℝ), (12 : ℝ), (13 : ℝ), (15 : ℝ)]
def sg : Fin 7 → Fin 8 := ![1, 2, 3, 4, 5, 6, 7]

theorem sv_0 : sv (0 : Fin 8) = (1 : ℝ) := rfl
theorem sv_1 : sv (1 : Fin 8) = (2 : ℝ) := rfl
theorem sv_2 : sv (2 : Fin 8) = (8 : ℝ) := rfl
theorem sv_3 : sv (3 : Fin 8) = (9 : ℝ) := rfl
theorem sv_4 : sv (4 : Fin 8) = (11 : ℝ) := rfl
theorem sv_5 : sv (5 : Fin 8) = (12 : ℝ) := rfl
theorem sv_6 : sv (6 : Fin 8) = (13 : ℝ) := rfl
theorem sv_7 : sv (7 : Fin 8) = (15 : ℝ) := rfl
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

end Fresh.CertRR.R13288



/-!
# Landing certificate `CertRR.R13296`: speeds (1, 2, 8, 9, 11, 12, 13, 16), subject index 0

Generated 2026-10-24 by `experiments/n8/cert_gen_v1.py` (exact Fractions).  Baseline readings [1, 7, 8, 10, 11, 12, 15].  Components up to the first wide one: 1.
Radius: speeds within `η ≤ 1/26880` of the baseline speeds, giving `ε = 2η ≤ 1/13440`.  Covering margin `μ = 1/512`.
`hcov` is **[PROVISIONAL: covering]**, supporting the claim that the first lonely instant of this subject is the largest exit of the first alive component.
Result `inst_arr`: for such `v`, the subject has a first isolation (a least element over all `t > 0`).  Grades: [L].
-/

open Classical

namespace Fresh.CertRR.R13296

open Fresh Fresh.LandingCert Fresh.LandingRule

noncomputable def pr : Fin 7 → ℝ := ![(1 : ℝ), (7 : ℝ), (8 : ℝ), (10 : ℝ), (11 : ℝ), (12 : ℝ), (15 : ℝ)]
noncomputable def aV : Fin 1 → ℝ := ![(17 / 80 : ℝ)]
noncomputable def bV : Fin 1 → ℝ := ![(15 / 64 : ℝ)]
noncomputable def dV : Fin 1 → ℝ := ![(1 / 240 : ℝ)]
noncomputable def TV : Fin 1 → ℝ := ![(229 / 960 : ℝ)]
def ZV : Fin 1 → ℤ := ![6]
noncomputable def HV : ℝ := (227 / 960 : ℝ)
noncomputable def EXs (c : Fin 1) : Finset (Fin 7 × ℤ) :=
  (Finset.univ ×ˢ Finset.Icc 0 (ZV c)).filter (fun q => ((q.2 : ℝ) + 1 / 8) / pr q.1 = aV c)
noncomputable def ENs (c : Fin 1) : Finset (Fin 7 × ℤ) :=
  (Finset.univ ×ˢ Finset.Icc 0 (ZV c)).filter (fun q => ((q.2 : ℝ) - 1 / 8) / pr q.1 = bV c)

theorem hp : ∀ i, 1 ≤ pr i ∧ pr i ≤ (15 : ℝ) := by intro i; fin_cases i <;> norm_num [pr]
theorem hp1 : ∀ i, 1 ≤ pr i := fun i => (hp i).1
theorem pr_0 : pr (0 : Fin 7) = (1 : ℝ) := rfl
theorem pr_1 : pr (1 : Fin 7) = (7 : ℝ) := rfl
theorem pr_2 : pr (2 : Fin 7) = (8 : ℝ) := rfl
theorem pr_3 : pr (3 : Fin 7) = (10 : ℝ) := rfl
theorem pr_4 : pr (4 : Fin 7) = (11 : ℝ) := rfl
theorem pr_5 : pr (5 : Fin 7) = (12 : ℝ) := rfl
theorem pr_6 : pr (6 : Fin 7) = (15 : ℝ) := rfl
theorem aV_0 : aV (0 : Fin 1) = (17 / 80 : ℝ) := rfl
theorem bV_0 : bV (0 : Fin 1) = (15 / 64 : ℝ) := rfl
theorem dV_0 : dV (0 : Fin 1) = (1 / 240 : ℝ) := rfl
theorem TV_0 : TV (0 : Fin 1) = (229 / 960 : ℝ) := rfl
theorem ZV_0 : ZV (0 : Fin 1) = (6 : ℤ) := rfl
theorem hab : ∀ c, aV c ≤ bV c := by intro c; fin_cases c <;> norm_num [aV, bV]
theorem hd0 : ∀ c, 0 < dV c := by intro c; fin_cases c <;> norm_num [dV]
theorem hdP : ∀ c, dV c ≤ 1 / (4 * (15 : ℝ)) := by intro c; fin_cases c <;> norm_num [dV]
theorem haP : ∀ c, dV c < aV c := by intro c; fin_cases c <;> norm_num [dV, aV]
theorem hT : ∀ c, bV c + dV c ≤ TV c := by intro c; fin_cases c <;> norm_num [bV, dV, TV]
theorem hZ : ∀ c, ((15 : ℝ) + 1) * TV c + 1 ≤ (ZV c : ℝ) := by intro c; fin_cases c <;> norm_num [TV, ZV]
theorem hE (ε : ℝ) (hε : ε ≤ (1 / 13440 : ℝ)) : ∀ c, 8 * ((ZV c : ℝ) + 1) * ε ≤ dV c := by
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

theorem gap0 (x : Fin 7 → ℝ) (ε : ℝ) (hdev : ∀ i, |x i - pr i| ≤ ε) (hεH : ε * HV ≤ (1 / 512 : ℝ) / 2) (t : ℝ) (h0 : 0 ≤ t)
    (hHt : t ≤ HV) (h1 : (0 : ℝ) ≤ t) (h2 : t ≤ (101 / 480 : ℝ)) (hlon : ∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)) : False := by
  rcases le_total t (63 / 512 : ℝ) with hs0 | hs0
  · exact zone_kill_gen pr x ε HV (1 / 512 : ℝ) hp1 hdev hεH (by norm_num) (0 : Fin 7) 0 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (0 : Fin 7))
  rcases le_total t (71 / 512 : ℝ) with hs1 | hs1
  · exact zone_kill_gen pr x ε HV (1 / 512 : ℝ) hp1 hdev hεH (by norm_num) (2 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (2 : Fin 7))
  rcases le_total t (569 / 3584 : ℝ) with hs2 | hs2
  · exact zone_kill_gen pr x ε HV (1 / 512 : ℝ) hp1 hdev hεH (by norm_num) (1 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (1 : Fin 7))
  rcases le_total t (269 / 1536 : ℝ) with hs3 | hs3
  · exact zone_kill_gen pr x ε HV (1 / 512 : ℝ) hp1 hdev hεH (by norm_num) (5 : Fin 7) 2 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (5 : Fin 7))
  rcases le_total t (1077 / 5632 : ℝ) with hs4 | hs4
  · exact zone_kill_gen pr x ε HV (1 / 512 : ℝ) hp1 hdev hεH (by norm_num) (4 : Fin 7) 2 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (4 : Fin 7))
  exact zone_kill_gen pr x ε HV (1 / 512 : ℝ) hp1 hdev hεH (by norm_num) (3 : Fin 7) 2 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (3 : Fin 7))
theorem cov (x : Fin 7 → ℝ) (ε : ℝ) (hε : ε ≤ (1 / 13440 : ℝ)) (hdev : ∀ i, |x i - pr i| ≤ ε) :
    ∀ t : ℝ, 0 < t → t ≤ HV → (∀ c, ¬ (aV c - dV c / 2 ≤ t ∧ t ≤ bV c + dV c / 2)) →
      ¬ (∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)) := by
  intro t h0 hHt hnone hlon
  have hεH : ε * HV ≤ (1 / 512 : ℝ) / 2 := by
    have hε0 : 0 ≤ ε := le_trans (abs_nonneg _) (hdev 0)
    have : ε * HV ≤ (1 / 13440 : ℝ) * HV := mul_le_mul_of_nonneg_right hε (by norm_num [HV])
    have h2 : (1 / 13440 : ℝ) * HV ≤ (1 / 512 : ℝ) / 2 := by norm_num [HV]
    linarith
  have n0 := hnone (0 : Fin 1)
  rw [aV_0, bV_0, dV_0] at n0
  rcases lt_or_ge t (101 / 480 : ℝ) with c0 | c0
  · exact gap0 x ε hdev hεH t h0.le hHt h0.le (by linarith) hlon
  have d0 : (227 / 960 : ℝ) < t := by
    by_contra hc; push Not at hc; exact n0 ⟨by linarith, by linarith⟩
  have hHv : HV = (227 / 960 : ℝ) := rfl
  exact absurd (by linarith : t ≤ (227 / 960 : ℝ)) (not_le.2 d0)

theorem inst (x : Fin 7 → ℝ) (ε : ℝ) (hε : ε ≤ (1 / 13440 : ℝ)) (hdev : ∀ i, |x i - pr i| ≤ ε) :
    ∃ c₀ : Fin 1, Alive (mxOf x EXs hEXne) (mnOf x ENs hENne) c₀ ∧
      (∀ c, c < c₀ → ¬ Alive (mxOf x EXs hEXne) (mnOf x ENs hENne) c) ∧
      IsLeast {t : ℝ | 0 < t ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)} (mxOf x EXs hEXne c₀) :=
  landing_cert 1 (15 : ℝ) (by norm_num) pr x hp ε hdev aV bV dV TV ZV hab hd0 hdP haP hT hZ (hE ε hε) hcls EXs ENs hEXne hENne
    hEXdef hENdef hsepL HV hHL (cov x ε hε hdev) (0 : Fin 1) (by rw [dV_0, bV_0, aV_0]; norm_num)

noncomputable def sv : Fin 8 → ℝ := ![(1 : ℝ), (2 : ℝ), (8 : ℝ), (9 : ℝ), (11 : ℝ), (12 : ℝ), (13 : ℝ), (16 : ℝ)]
def sg : Fin 7 → Fin 8 := ![1, 2, 3, 4, 5, 6, 7]

theorem sv_0 : sv (0 : Fin 8) = (1 : ℝ) := rfl
theorem sv_1 : sv (1 : Fin 8) = (2 : ℝ) := rfl
theorem sv_2 : sv (2 : Fin 8) = (8 : ℝ) := rfl
theorem sv_3 : sv (3 : Fin 8) = (9 : ℝ) := rfl
theorem sv_4 : sv (4 : Fin 8) = (11 : ℝ) := rfl
theorem sv_5 : sv (5 : Fin 8) = (12 : ℝ) := rfl
theorem sv_6 : sv (6 : Fin 8) = (13 : ℝ) := rfl
theorem sv_7 : sv (7 : Fin 8) = (16 : ℝ) := rfl
theorem sg_0 : sg (0 : Fin 7) = (1 : Fin 8) := rfl
theorem sg_1 : sg (1 : Fin 7) = (2 : Fin 8) := rfl
theorem sg_2 : sg (2 : Fin 7) = (3 : Fin 8) := rfl
theorem sg_3 : sg (3 : Fin 7) = (4 : Fin 8) := rfl
theorem sg_4 : sg (4 : Fin 7) = (5 : Fin 8) := rfl
theorem sg_5 : sg (5 : Fin 7) = (6 : Fin 8) := rfl
theorem sg_6 : sg (6 : Fin 7) = (7 : Fin 8) := rfl

theorem inst_arr (v : Fin 8 → ℝ) (η : ℝ) (hη : η ≤ (1 / 26880 : ℝ)) (hv : ∀ j, |v j - sv j| ≤ η) :
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

end Fresh.CertRR.R13296



/-!
# Landing certificate `CertRR.R13298`: speeds (1, 2, 8, 9, 11, 12, 13, 16), subject index 2

Generated 2026-10-24 by `experiments/n8/cert_gen_v1.py` (exact Fractions).  Baseline readings [7, 6, 1, 3, 4, 5, 8].  Components up to the first wide one: 1.
Radius: speeds within `η ≤ 1/10752` of the baseline speeds, giving `ε = 2η ≤ 1/5376`.  Covering margin `μ = 1/512`.
`hcov` is **[PROVISIONAL: covering]**, supporting the claim that the first lonely instant of this subject is the largest exit of the first alive component.
Result `inst_arr`: for such `v`, the subject has a first isolation (a least element over all `t > 0`).  Grades: [L].
-/

open Classical

namespace Fresh.CertRR.R13298

open Fresh Fresh.LandingCert Fresh.LandingRule

noncomputable def pr : Fin 7 → ℝ := ![(7 : ℝ), (6 : ℝ), (1 : ℝ), (3 : ℝ), (4 : ℝ), (5 : ℝ), (8 : ℝ)]
noncomputable def aV : Fin 1 → ℝ := ![(25 / 56 : ℝ)]
noncomputable def bV : Fin 1 → ℝ := ![(15 / 32 : ℝ)]
noncomputable def dV : Fin 1 → ℝ := ![(1 / 96 : ℝ)]
noncomputable def TV : Fin 1 → ℝ := ![(23 / 48 : ℝ)]
def ZV : Fin 1 → ℤ := ![6]
noncomputable def HV : ℝ := (91 / 192 : ℝ)
noncomputable def EXs (c : Fin 1) : Finset (Fin 7 × ℤ) :=
  (Finset.univ ×ˢ Finset.Icc 0 (ZV c)).filter (fun q => ((q.2 : ℝ) + 1 / 8) / pr q.1 = aV c)
noncomputable def ENs (c : Fin 1) : Finset (Fin 7 × ℤ) :=
  (Finset.univ ×ˢ Finset.Icc 0 (ZV c)).filter (fun q => ((q.2 : ℝ) - 1 / 8) / pr q.1 = bV c)

theorem hp : ∀ i, 1 ≤ pr i ∧ pr i ≤ (8 : ℝ) := by intro i; fin_cases i <;> norm_num [pr]
theorem hp1 : ∀ i, 1 ≤ pr i := fun i => (hp i).1
theorem pr_0 : pr (0 : Fin 7) = (7 : ℝ) := rfl
theorem pr_1 : pr (1 : Fin 7) = (6 : ℝ) := rfl
theorem pr_2 : pr (2 : Fin 7) = (1 : ℝ) := rfl
theorem pr_3 : pr (3 : Fin 7) = (3 : ℝ) := rfl
theorem pr_4 : pr (4 : Fin 7) = (4 : ℝ) := rfl
theorem pr_5 : pr (5 : Fin 7) = (5 : ℝ) := rfl
theorem pr_6 : pr (6 : Fin 7) = (8 : ℝ) := rfl
theorem aV_0 : aV (0 : Fin 1) = (25 / 56 : ℝ) := rfl
theorem bV_0 : bV (0 : Fin 1) = (15 / 32 : ℝ) := rfl
theorem dV_0 : dV (0 : Fin 1) = (1 / 96 : ℝ) := rfl
theorem TV_0 : TV (0 : Fin 1) = (23 / 48 : ℝ) := rfl
theorem ZV_0 : ZV (0 : Fin 1) = (6 : ℤ) := rfl
theorem hab : ∀ c, aV c ≤ bV c := by intro c; fin_cases c <;> norm_num [aV, bV]
theorem hd0 : ∀ c, 0 < dV c := by intro c; fin_cases c <;> norm_num [dV]
theorem hdP : ∀ c, dV c ≤ 1 / (4 * (8 : ℝ)) := by intro c; fin_cases c <;> norm_num [dV]
theorem haP : ∀ c, dV c < aV c := by intro c; fin_cases c <;> norm_num [dV, aV]
theorem hT : ∀ c, bV c + dV c ≤ TV c := by intro c; fin_cases c <;> norm_num [bV, dV, TV]
theorem hZ : ∀ c, ((8 : ℝ) + 1) * TV c + 1 ≤ (ZV c : ℝ) := by intro c; fin_cases c <;> norm_num [TV, ZV]
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
  · exact ⟨(0, 3), by simp [EXs, ZV, pr, aV] <;> norm_num⟩
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
    (hHt : t ≤ HV) (h1 : (0 : ℝ) ≤ t) (h2 : t ≤ (593 / 1344 : ℝ)) (hlon : ∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)) : False := by
  rcases le_total t (63 / 512 : ℝ) with hs0 | hs0
  · exact zone_kill_gen pr x ε HV (1 / 512 : ℝ) hp1 hdev hεH (by norm_num) (2 : Fin 7) 0 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (2 : Fin 7))
  rcases le_total t (71 / 512 : ℝ) with hs1 | hs1
  · exact zone_kill_gen pr x ε HV (1 / 512 : ℝ) hp1 hdev hεH (by norm_num) (6 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (6 : Fin 7))
  rcases le_total t (569 / 3584 : ℝ) with hs2 | hs2
  · exact zone_kill_gen pr x ε HV (1 / 512 : ℝ) hp1 hdev hεH (by norm_num) (0 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (0 : Fin 7))
  rcases le_total t (95 / 512 : ℝ) with hs3 | hs3
  · exact zone_kill_gen pr x ε HV (1 / 512 : ℝ) hp1 hdev hεH (by norm_num) (1 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (1 : Fin 7))
  rcases le_total t (571 / 2560 : ℝ) with hs4 | hs4
  · exact zone_kill_gen pr x ε HV (1 / 512 : ℝ) hp1 hdev hεH (by norm_num) (5 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (5 : Fin 7))
  rcases le_total t (143 / 512 : ℝ) with hs5 | hs5
  · exact zone_kill_gen pr x ε HV (1 / 512 : ℝ) hp1 hdev hεH (by norm_num) (4 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (4 : Fin 7))
  rcases le_total t (1081 / 3584 : ℝ) with hs6 | hs6
  · exact zone_kill_gen pr x ε HV (1 / 512 : ℝ) hp1 hdev hεH (by norm_num) (0 : Fin 7) 2 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (0 : Fin 7))
  rcases le_total t (191 / 512 : ℝ) with hs7 | hs7
  · exact zone_kill_gen pr x ε HV (1 / 512 : ℝ) hp1 hdev hεH (by norm_num) (3 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (3 : Fin 7))
  rcases le_total t (199 / 512 : ℝ) with hs8 | hs8
  · exact zone_kill_gen pr x ε HV (1 / 512 : ℝ) hp1 hdev hεH (by norm_num) (6 : Fin 7) 3 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (6 : Fin 7))
  rcases le_total t (1083 / 2560 : ℝ) with hs9 | hs9
  · exact zone_kill_gen pr x ε HV (1 / 512 : ℝ) hp1 hdev hεH (by norm_num) (5 : Fin 7) 2 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (5 : Fin 7))
  exact zone_kill_gen pr x ε HV (1 / 512 : ℝ) hp1 hdev hεH (by norm_num) (0 : Fin 7) 3 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (0 : Fin 7))
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
  rcases lt_or_ge t (593 / 1344 : ℝ) with c0 | c0
  · exact gap0 x ε hdev hεH t h0.le hHt h0.le (by linarith) hlon
  have d0 : (91 / 192 : ℝ) < t := by
    by_contra hc; push Not at hc; exact n0 ⟨by linarith, by linarith⟩
  have hHv : HV = (91 / 192 : ℝ) := rfl
  exact absurd (by linarith : t ≤ (91 / 192 : ℝ)) (not_le.2 d0)

theorem inst (x : Fin 7 → ℝ) (ε : ℝ) (hε : ε ≤ (1 / 5376 : ℝ)) (hdev : ∀ i, |x i - pr i| ≤ ε) :
    ∃ c₀ : Fin 1, Alive (mxOf x EXs hEXne) (mnOf x ENs hENne) c₀ ∧
      (∀ c, c < c₀ → ¬ Alive (mxOf x EXs hEXne) (mnOf x ENs hENne) c) ∧
      IsLeast {t : ℝ | 0 < t ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)} (mxOf x EXs hEXne c₀) :=
  landing_cert 1 (8 : ℝ) (by norm_num) pr x hp ε hdev aV bV dV TV ZV hab hd0 hdP haP hT hZ (hE ε hε) hcls EXs ENs hEXne hENne
    hEXdef hENdef hsepL HV hHL (cov x ε hε hdev) (0 : Fin 1) (by rw [dV_0, bV_0, aV_0]; norm_num)

noncomputable def sv : Fin 8 → ℝ := ![(1 : ℝ), (2 : ℝ), (8 : ℝ), (9 : ℝ), (11 : ℝ), (12 : ℝ), (13 : ℝ), (16 : ℝ)]
def sg : Fin 7 → Fin 8 := ![0, 1, 3, 4, 5, 6, 7]

theorem sv_0 : sv (0 : Fin 8) = (1 : ℝ) := rfl
theorem sv_1 : sv (1 : Fin 8) = (2 : ℝ) := rfl
theorem sv_2 : sv (2 : Fin 8) = (8 : ℝ) := rfl
theorem sv_3 : sv (3 : Fin 8) = (9 : ℝ) := rfl
theorem sv_4 : sv (4 : Fin 8) = (11 : ℝ) := rfl
theorem sv_5 : sv (5 : Fin 8) = (12 : ℝ) := rfl
theorem sv_6 : sv (6 : Fin 8) = (13 : ℝ) := rfl
theorem sv_7 : sv (7 : Fin 8) = (16 : ℝ) := rfl
theorem sg_0 : sg (0 : Fin 7) = (0 : Fin 8) := rfl
theorem sg_1 : sg (1 : Fin 7) = (1 : Fin 8) := rfl
theorem sg_2 : sg (2 : Fin 7) = (3 : Fin 8) := rfl
theorem sg_3 : sg (3 : Fin 7) = (4 : Fin 8) := rfl
theorem sg_4 : sg (4 : Fin 7) = (5 : Fin 8) := rfl
theorem sg_5 : sg (5 : Fin 7) = (6 : Fin 8) := rfl
theorem sg_6 : sg (6 : Fin 7) = (7 : Fin 8) := rfl

theorem inst_arr (v : Fin 8 → ℝ) (η : ℝ) (hη : η ≤ (1 / 10752 : ℝ)) (hv : ∀ j, |v j - sv j| ≤ η) :
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

end Fresh.CertRR.R13298



/-!
# Landing certificate `CertRR.R13307`: speeds (1, 2, 8, 9, 11, 12, 14, 15), subject index 3

Generated 2026-10-24 by `experiments/n8/cert_gen_v1.py` (exact Fractions).  Baseline readings [8, 7, 1, 2, 3, 5, 6].  Components up to the first wide one: 1.
Radius: speeds within `η ≤ 1/5120` of the baseline speeds, giving `ε = 2η ≤ 1/2560`.  Covering margin `μ = 1/256`.
`hcov` is **[PROVISIONAL: covering]**, supporting the claim that the first lonely instant of this subject is the largest exit of the first alive component.
Result `inst_arr`: for such `v`, the subject has a first isolation (a least element over all `t > 0`).  Grades: [L].
-/

open Classical

namespace Fresh.CertRR.R13307

open Fresh Fresh.LandingCert Fresh.LandingRule

noncomputable def pr : Fin 7 → ℝ := ![(8 : ℝ), (7 : ℝ), (1 : ℝ), (2 : ℝ), (3 : ℝ), (5 : ℝ), (6 : ℝ)]
noncomputable def aV : Fin 1 → ℝ := ![(9 / 40 : ℝ)]
noncomputable def bV : Fin 1 → ℝ := ![(15 / 64 : ℝ)]
noncomputable def dV : Fin 1 → ℝ := ![(1 / 64 : ℝ)]
noncomputable def TV : Fin 1 → ℝ := ![(1 / 4 : ℝ)]
def ZV : Fin 1 → ℤ := ![4]
noncomputable def HV : ℝ := (31 / 128 : ℝ)
noncomputable def EXs (c : Fin 1) : Finset (Fin 7 × ℤ) :=
  (Finset.univ ×ˢ Finset.Icc 0 (ZV c)).filter (fun q => ((q.2 : ℝ) + 1 / 8) / pr q.1 = aV c)
noncomputable def ENs (c : Fin 1) : Finset (Fin 7 × ℤ) :=
  (Finset.univ ×ˢ Finset.Icc 0 (ZV c)).filter (fun q => ((q.2 : ℝ) - 1 / 8) / pr q.1 = bV c)

theorem hp : ∀ i, 1 ≤ pr i ∧ pr i ≤ (8 : ℝ) := by intro i; fin_cases i <;> norm_num [pr]
theorem hp1 : ∀ i, 1 ≤ pr i := fun i => (hp i).1
theorem pr_0 : pr (0 : Fin 7) = (8 : ℝ) := rfl
theorem pr_1 : pr (1 : Fin 7) = (7 : ℝ) := rfl
theorem pr_2 : pr (2 : Fin 7) = (1 : ℝ) := rfl
theorem pr_3 : pr (3 : Fin 7) = (2 : ℝ) := rfl
theorem pr_4 : pr (4 : Fin 7) = (3 : ℝ) := rfl
theorem pr_5 : pr (5 : Fin 7) = (5 : ℝ) := rfl
theorem pr_6 : pr (6 : Fin 7) = (6 : ℝ) := rfl
theorem aV_0 : aV (0 : Fin 1) = (9 / 40 : ℝ) := rfl
theorem bV_0 : bV (0 : Fin 1) = (15 / 64 : ℝ) := rfl
theorem dV_0 : dV (0 : Fin 1) = (1 / 64 : ℝ) := rfl
theorem TV_0 : TV (0 : Fin 1) = (1 / 4 : ℝ) := rfl
theorem ZV_0 : ZV (0 : Fin 1) = (4 : ℤ) := rfl
theorem hab : ∀ c, aV c ≤ bV c := by intro c; fin_cases c <;> norm_num [aV, bV]
theorem hd0 : ∀ c, 0 < dV c := by intro c; fin_cases c <;> norm_num [dV]
theorem hdP : ∀ c, dV c ≤ 1 / (4 * (8 : ℝ)) := by intro c; fin_cases c <;> norm_num [dV]
theorem haP : ∀ c, dV c < aV c := by intro c; fin_cases c <;> norm_num [dV, aV]
theorem hT : ∀ c, bV c + dV c ≤ TV c := by intro c; fin_cases c <;> norm_num [bV, dV, TV]
theorem hZ : ∀ c, ((8 : ℝ) + 1) * TV c + 1 ≤ (ZV c : ℝ) := by intro c; fin_cases c <;> norm_num [TV, ZV]
theorem hE (ε : ℝ) (hε : ε ≤ (1 / 2560 : ℝ)) : ∀ c, 8 * ((ZV c : ℝ) + 1) * ε ≤ dV c := by
  intro c; fin_cases c <;> norm_num [ZV, dV] <;> linarith
theorem hcls : ∀ c i, ∀ z : ℤ, 0 ≤ z → z ≤ ZV c →
    ((z : ℝ) + 1 / 8) / pr i ≤ aV c - dV c ∨ bV c + dV c ≤ ((z : ℝ) - 1 / 8) / pr i ∨
      ((z : ℝ) + 1 / 8) / pr i = aV c ∨ ((z : ℝ) - 1 / 8) / pr i = bV c := by
  intro c i z h0 h1
  fin_cases c <;> fin_cases i <;> simp [ZV] at h1 <;> interval_cases z <;> norm_num [pr, aV, bV, dV]
theorem hEXne : ∀ c, (EXs c).Nonempty := by
  intro c
  fin_cases c
  · exact ⟨(5, 1), by simp [EXs, ZV, pr, aV] <;> norm_num⟩
theorem hENne : ∀ c, (ENs c).Nonempty := by
  intro c
  fin_cases c
  · exact ⟨(0, 2), by simp [ENs, ZV, pr, bV] <;> norm_num⟩
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
    (hHt : t ≤ HV) (h1 : (0 : ℝ) ≤ t) (h2 : t ≤ (139 / 640 : ℝ)) (hlon : ∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)) : False := by
  rcases le_total t (31 / 256 : ℝ) with hs0 | hs0
  · exact zone_kill_gen pr x ε HV (1 / 256 : ℝ) hp1 hdev hεH (by norm_num) (2 : Fin 7) 0 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (2 : Fin 7))
  rcases le_total t (35 / 256 : ℝ) with hs1 | hs1
  · exact zone_kill_gen pr x ε HV (1 / 256 : ℝ) hp1 hdev hεH (by norm_num) (0 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (0 : Fin 7))
  rcases le_total t (281 / 1792 : ℝ) with hs2 | hs2
  · exact zone_kill_gen pr x ε HV (1 / 256 : ℝ) hp1 hdev hεH (by norm_num) (1 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (1 : Fin 7))
  rcases le_total t (47 / 256 : ℝ) with hs3 | hs3
  · exact zone_kill_gen pr x ε HV (1 / 256 : ℝ) hp1 hdev hεH (by norm_num) (6 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (6 : Fin 7))
  exact zone_kill_gen pr x ε HV (1 / 256 : ℝ) hp1 hdev hεH (by norm_num) (5 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (5 : Fin 7))
theorem cov (x : Fin 7 → ℝ) (ε : ℝ) (hε : ε ≤ (1 / 2560 : ℝ)) (hdev : ∀ i, |x i - pr i| ≤ ε) :
    ∀ t : ℝ, 0 < t → t ≤ HV → (∀ c, ¬ (aV c - dV c / 2 ≤ t ∧ t ≤ bV c + dV c / 2)) →
      ¬ (∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)) := by
  intro t h0 hHt hnone hlon
  have hεH : ε * HV ≤ (1 / 256 : ℝ) / 2 := by
    have hε0 : 0 ≤ ε := le_trans (abs_nonneg _) (hdev 0)
    have : ε * HV ≤ (1 / 2560 : ℝ) * HV := mul_le_mul_of_nonneg_right hε (by norm_num [HV])
    have h2 : (1 / 2560 : ℝ) * HV ≤ (1 / 256 : ℝ) / 2 := by norm_num [HV]
    linarith
  have n0 := hnone (0 : Fin 1)
  rw [aV_0, bV_0, dV_0] at n0
  rcases lt_or_ge t (139 / 640 : ℝ) with c0 | c0
  · exact gap0 x ε hdev hεH t h0.le hHt h0.le (by linarith) hlon
  have d0 : (31 / 128 : ℝ) < t := by
    by_contra hc; push Not at hc; exact n0 ⟨by linarith, by linarith⟩
  have hHv : HV = (31 / 128 : ℝ) := rfl
  exact absurd (by linarith : t ≤ (31 / 128 : ℝ)) (not_le.2 d0)

theorem inst (x : Fin 7 → ℝ) (ε : ℝ) (hε : ε ≤ (1 / 2560 : ℝ)) (hdev : ∀ i, |x i - pr i| ≤ ε) :
    ∃ c₀ : Fin 1, Alive (mxOf x EXs hEXne) (mnOf x ENs hENne) c₀ ∧
      (∀ c, c < c₀ → ¬ Alive (mxOf x EXs hEXne) (mnOf x ENs hENne) c) ∧
      IsLeast {t : ℝ | 0 < t ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)} (mxOf x EXs hEXne c₀) :=
  landing_cert 1 (8 : ℝ) (by norm_num) pr x hp ε hdev aV bV dV TV ZV hab hd0 hdP haP hT hZ (hE ε hε) hcls EXs ENs hEXne hENne
    hEXdef hENdef hsepL HV hHL (cov x ε hε hdev) (0 : Fin 1) (by rw [dV_0, bV_0, aV_0]; norm_num)

noncomputable def sv : Fin 8 → ℝ := ![(1 : ℝ), (2 : ℝ), (8 : ℝ), (9 : ℝ), (11 : ℝ), (12 : ℝ), (14 : ℝ), (15 : ℝ)]
def sg : Fin 7 → Fin 8 := ![0, 1, 2, 4, 5, 6, 7]

theorem sv_0 : sv (0 : Fin 8) = (1 : ℝ) := rfl
theorem sv_1 : sv (1 : Fin 8) = (2 : ℝ) := rfl
theorem sv_2 : sv (2 : Fin 8) = (8 : ℝ) := rfl
theorem sv_3 : sv (3 : Fin 8) = (9 : ℝ) := rfl
theorem sv_4 : sv (4 : Fin 8) = (11 : ℝ) := rfl
theorem sv_5 : sv (5 : Fin 8) = (12 : ℝ) := rfl
theorem sv_6 : sv (6 : Fin 8) = (14 : ℝ) := rfl
theorem sv_7 : sv (7 : Fin 8) = (15 : ℝ) := rfl
theorem sg_0 : sg (0 : Fin 7) = (0 : Fin 8) := rfl
theorem sg_1 : sg (1 : Fin 7) = (1 : Fin 8) := rfl
theorem sg_2 : sg (2 : Fin 7) = (2 : Fin 8) := rfl
theorem sg_3 : sg (3 : Fin 7) = (4 : Fin 8) := rfl
theorem sg_4 : sg (4 : Fin 7) = (5 : Fin 8) := rfl
theorem sg_5 : sg (5 : Fin 7) = (6 : Fin 8) := rfl
theorem sg_6 : sg (6 : Fin 7) = (7 : Fin 8) := rfl

theorem inst_arr (v : Fin 8 → ℝ) (η : ℝ) (hη : η ≤ (1 / 5120 : ℝ)) (hv : ∀ j, |v j - sv j| ≤ η) :
    ∃ c₀ : Fin 1, Alive (mxOf (fun i => |v (sg i) - v (3 : Fin 8)|) EXs hEXne) (mnOf (fun i => |v (sg i) - v (3 : Fin 8)|) ENs hENne) c₀ ∧
      (∀ c, c < c₀ → ¬ Alive (mxOf (fun i => |v (sg i) - v (3 : Fin 8)|) EXs hEXne) (mnOf (fun i => |v (sg i) - v (3 : Fin 8)|) ENs hENne) c) ∧
      IsLeast {t : ℝ | 0 < t ∧ IsolatedAt v (3 : Fin 8) t} (mxOf (fun i => |v (sg i) - v (3 : Fin 8)|) EXs hEXne c₀) := by
  have hσk : ∀ i, sg i ≠ (3 : Fin 8) := by decide
  have hσ : ∀ j : Fin 8, j ≠ (3 : Fin 8) → ∃ i, sg i = j := by decide
  have hpr : ∀ i, pr i = |sv (sg i) - sv (3 : Fin 8)| := by
    intro i; rcases fin7_cases i with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6, sv_0, sv_1, sv_2, sv_3, sv_4, sv_5, sv_6, sv_7, sg_0, sg_1, sg_2, sg_3, sg_4, sg_5, sg_6]
  have hdev : ∀ i, |(|v (sg i) - v (3 : Fin 8)| - pr i)| ≤ 2 * η := by
    intro i; rw [hpr i]; exact reading_dev v sv η hv (sg i) (3 : Fin 8)
  obtain ⟨c₀, hal, hbf, hT0⟩ := inst (fun i => |v (sg i) - v (3 : Fin 8)|) (2 * η) (by linarith) hdev
  have hset : {t : ℝ | 0 < t ∧ IsolatedAt v (3 : Fin 8) t} =
      {t : ℝ | 0 < t ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (|v (sg i) - v (3 : Fin 8)| * t)} := by
    ext t; simp only [Set.mem_setOf_eq]; rw [iso_iff_readings v (3 : Fin 8) sg hσk hσ t]
  rw [hset]; exact ⟨c₀, hal, hbf, hT0⟩

#print axioms inst_arr

end Fresh.CertRR.R13307



/-!
# Landing certificate `CertRR.R13312`: speeds (1, 2, 8, 9, 11, 13, 14, 15), subject index 0

Generated 2026-10-24 by `experiments/n8/cert_gen_v1.py` (exact Fractions).  Baseline readings [1, 7, 8, 10, 12, 13, 14].  Components up to the first wide one: 1.
Radius: speeds within `η ≤ 1/7048` of the baseline speeds, giving `ε = 2η ≤ 1/3524`.  Covering margin `μ = 1/512`.
`hcov` is **[PROVISIONAL: covering]**, supporting the claim that the first lonely instant of this subject is the largest exit of the first alive component.
Result `inst_arr`: for such `v`, the subject has a first isolation (a least element over all `t > 0`).  Grades: [L].
-/

open Classical

namespace Fresh.CertRR.R13312

open Fresh Fresh.LandingCert Fresh.LandingRule

noncomputable def pr : Fin 7 → ℝ := ![(1 : ℝ), (7 : ℝ), (8 : ℝ), (10 : ℝ), (12 : ℝ), (13 : ℝ), (14 : ℝ)]
noncomputable def aV : Fin 1 → ℝ := ![(17 / 96 : ℝ)]
noncomputable def bV : Fin 1 → ℝ := ![(3 / 16 : ℝ)]
noncomputable def dV : Fin 1 → ℝ := ![(17 / 1248 : ℝ)]
noncomputable def TV : Fin 1 → ℝ := ![(251 / 1248 : ℝ)]
def ZV : Fin 1 → ℤ := ![5]
noncomputable def HV : ℝ := (485 / 2496 : ℝ)
noncomputable def EXs (c : Fin 1) : Finset (Fin 7 × ℤ) :=
  (Finset.univ ×ˢ Finset.Icc 0 (ZV c)).filter (fun q => ((q.2 : ℝ) + 1 / 8) / pr q.1 = aV c)
noncomputable def ENs (c : Fin 1) : Finset (Fin 7 × ℤ) :=
  (Finset.univ ×ˢ Finset.Icc 0 (ZV c)).filter (fun q => ((q.2 : ℝ) - 1 / 8) / pr q.1 = bV c)

theorem hp : ∀ i, 1 ≤ pr i ∧ pr i ≤ (14 : ℝ) := by intro i; fin_cases i <;> norm_num [pr]
theorem hp1 : ∀ i, 1 ≤ pr i := fun i => (hp i).1
theorem pr_0 : pr (0 : Fin 7) = (1 : ℝ) := rfl
theorem pr_1 : pr (1 : Fin 7) = (7 : ℝ) := rfl
theorem pr_2 : pr (2 : Fin 7) = (8 : ℝ) := rfl
theorem pr_3 : pr (3 : Fin 7) = (10 : ℝ) := rfl
theorem pr_4 : pr (4 : Fin 7) = (12 : ℝ) := rfl
theorem pr_5 : pr (5 : Fin 7) = (13 : ℝ) := rfl
theorem pr_6 : pr (6 : Fin 7) = (14 : ℝ) := rfl
theorem aV_0 : aV (0 : Fin 1) = (17 / 96 : ℝ) := rfl
theorem bV_0 : bV (0 : Fin 1) = (3 / 16 : ℝ) := rfl
theorem dV_0 : dV (0 : Fin 1) = (17 / 1248 : ℝ) := rfl
theorem TV_0 : TV (0 : Fin 1) = (251 / 1248 : ℝ) := rfl
theorem ZV_0 : ZV (0 : Fin 1) = (5 : ℤ) := rfl
theorem hab : ∀ c, aV c ≤ bV c := by intro c; fin_cases c <;> norm_num [aV, bV]
theorem hd0 : ∀ c, 0 < dV c := by intro c; fin_cases c <;> norm_num [dV]
theorem hdP : ∀ c, dV c ≤ 1 / (4 * (14 : ℝ)) := by intro c; fin_cases c <;> norm_num [dV]
theorem haP : ∀ c, dV c < aV c := by intro c; fin_cases c <;> norm_num [dV, aV]
theorem hT : ∀ c, bV c + dV c ≤ TV c := by intro c; fin_cases c <;> norm_num [bV, dV, TV]
theorem hZ : ∀ c, ((14 : ℝ) + 1) * TV c + 1 ≤ (ZV c : ℝ) := by intro c; fin_cases c <;> norm_num [TV, ZV]
theorem hE (ε : ℝ) (hε : ε ≤ (1 / 3524 : ℝ)) : ∀ c, 8 * ((ZV c : ℝ) + 1) * ε ≤ dV c := by
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
    (hHt : t ≤ HV) (h1 : (0 : ℝ) ≤ t) (h2 : t ≤ (425 / 2496 : ℝ)) (hlon : ∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)) : False := by
  rcases le_total t (63 / 512 : ℝ) with hs0 | hs0
  · exact zone_kill_gen pr x ε HV (1 / 512 : ℝ) hp1 hdev hεH (by norm_num) (0 : Fin 7) 0 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (0 : Fin 7))
  rcases le_total t (71 / 512 : ℝ) with hs1 | hs1
  · exact zone_kill_gen pr x ε HV (1 / 512 : ℝ) hp1 hdev hεH (by norm_num) (2 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (2 : Fin 7))
  rcases le_total t (569 / 3584 : ℝ) with hs2 | hs2
  · exact zone_kill_gen pr x ε HV (1 / 512 : ℝ) hp1 hdev hεH (by norm_num) (1 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (1 : Fin 7))
  exact zone_kill_gen pr x ε HV (1 / 512 : ℝ) hp1 hdev hεH (by norm_num) (4 : Fin 7) 2 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (4 : Fin 7))
theorem cov (x : Fin 7 → ℝ) (ε : ℝ) (hε : ε ≤ (1 / 3524 : ℝ)) (hdev : ∀ i, |x i - pr i| ≤ ε) :
    ∀ t : ℝ, 0 < t → t ≤ HV → (∀ c, ¬ (aV c - dV c / 2 ≤ t ∧ t ≤ bV c + dV c / 2)) →
      ¬ (∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)) := by
  intro t h0 hHt hnone hlon
  have hεH : ε * HV ≤ (1 / 512 : ℝ) / 2 := by
    have hε0 : 0 ≤ ε := le_trans (abs_nonneg _) (hdev 0)
    have : ε * HV ≤ (1 / 3524 : ℝ) * HV := mul_le_mul_of_nonneg_right hε (by norm_num [HV])
    have h2 : (1 / 3524 : ℝ) * HV ≤ (1 / 512 : ℝ) / 2 := by norm_num [HV]
    linarith
  have n0 := hnone (0 : Fin 1)
  rw [aV_0, bV_0, dV_0] at n0
  rcases lt_or_ge t (425 / 2496 : ℝ) with c0 | c0
  · exact gap0 x ε hdev hεH t h0.le hHt h0.le (by linarith) hlon
  have d0 : (485 / 2496 : ℝ) < t := by
    by_contra hc; push Not at hc; exact n0 ⟨by linarith, by linarith⟩
  have hHv : HV = (485 / 2496 : ℝ) := rfl
  exact absurd (by linarith : t ≤ (485 / 2496 : ℝ)) (not_le.2 d0)

theorem inst (x : Fin 7 → ℝ) (ε : ℝ) (hε : ε ≤ (1 / 3524 : ℝ)) (hdev : ∀ i, |x i - pr i| ≤ ε) :
    ∃ c₀ : Fin 1, Alive (mxOf x EXs hEXne) (mnOf x ENs hENne) c₀ ∧
      (∀ c, c < c₀ → ¬ Alive (mxOf x EXs hEXne) (mnOf x ENs hENne) c) ∧
      IsLeast {t : ℝ | 0 < t ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)} (mxOf x EXs hEXne c₀) :=
  landing_cert 1 (14 : ℝ) (by norm_num) pr x hp ε hdev aV bV dV TV ZV hab hd0 hdP haP hT hZ (hE ε hε) hcls EXs ENs hEXne hENne
    hEXdef hENdef hsepL HV hHL (cov x ε hε hdev) (0 : Fin 1) (by rw [dV_0, bV_0, aV_0]; norm_num)

noncomputable def sv : Fin 8 → ℝ := ![(1 : ℝ), (2 : ℝ), (8 : ℝ), (9 : ℝ), (11 : ℝ), (13 : ℝ), (14 : ℝ), (15 : ℝ)]
def sg : Fin 7 → Fin 8 := ![1, 2, 3, 4, 5, 6, 7]

theorem sv_0 : sv (0 : Fin 8) = (1 : ℝ) := rfl
theorem sv_1 : sv (1 : Fin 8) = (2 : ℝ) := rfl
theorem sv_2 : sv (2 : Fin 8) = (8 : ℝ) := rfl
theorem sv_3 : sv (3 : Fin 8) = (9 : ℝ) := rfl
theorem sv_4 : sv (4 : Fin 8) = (11 : ℝ) := rfl
theorem sv_5 : sv (5 : Fin 8) = (13 : ℝ) := rfl
theorem sv_6 : sv (6 : Fin 8) = (14 : ℝ) := rfl
theorem sv_7 : sv (7 : Fin 8) = (15 : ℝ) := rfl
theorem sg_0 : sg (0 : Fin 7) = (1 : Fin 8) := rfl
theorem sg_1 : sg (1 : Fin 7) = (2 : Fin 8) := rfl
theorem sg_2 : sg (2 : Fin 7) = (3 : Fin 8) := rfl
theorem sg_3 : sg (3 : Fin 7) = (4 : Fin 8) := rfl
theorem sg_4 : sg (4 : Fin 7) = (5 : Fin 8) := rfl
theorem sg_5 : sg (5 : Fin 7) = (6 : Fin 8) := rfl
theorem sg_6 : sg (6 : Fin 7) = (7 : Fin 8) := rfl

theorem inst_arr (v : Fin 8 → ℝ) (η : ℝ) (hη : η ≤ (1 / 7048 : ℝ)) (hv : ∀ j, |v j - sv j| ≤ η) :
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

end Fresh.CertRR.R13312



/-!
# Landing certificate `CertRR.R13315`: speeds (1, 2, 8, 9, 11, 13, 14, 15), subject index 3

Generated 2026-10-24 by `experiments/n8/cert_gen_v1.py` (exact Fractions).  Baseline readings [8, 7, 1, 2, 4, 5, 6].  Components up to the first wide one: 1.
Radius: speeds within `η ≤ 1/5376` of the baseline speeds, giving `ε = 2η ≤ 1/2688`.  Covering margin `μ = 1/512`.
`hcov` is **[PROVISIONAL: covering]**, supporting the claim that the first lonely instant of this subject is the largest exit of the first alive component.
Result `inst_arr`: for such `v`, the subject has a first isolation (a least element over all `t > 0`).  Grades: [L].
-/

open Classical

namespace Fresh.CertRR.R13315

open Fresh Fresh.LandingCert Fresh.LandingRule

noncomputable def pr : Fin 7 → ℝ := ![(8 : ℝ), (7 : ℝ), (1 : ℝ), (2 : ℝ), (4 : ℝ), (5 : ℝ), (6 : ℝ)]
noncomputable def aV : Fin 1 → ℝ := ![(17 / 56 : ℝ)]
noncomputable def bV : Fin 1 → ℝ := ![(5 / 16 : ℝ)]
noncomputable def dV : Fin 1 → ℝ := ![(1 / 56 : ℝ)]
noncomputable def TV : Fin 1 → ℝ := ![(37 / 112 : ℝ)]
def ZV : Fin 1 → ℤ := ![5]
noncomputable def HV : ℝ := (9 / 28 : ℝ)
noncomputable def EXs (c : Fin 1) : Finset (Fin 7 × ℤ) :=
  (Finset.univ ×ˢ Finset.Icc 0 (ZV c)).filter (fun q => ((q.2 : ℝ) + 1 / 8) / pr q.1 = aV c)
noncomputable def ENs (c : Fin 1) : Finset (Fin 7 × ℤ) :=
  (Finset.univ ×ˢ Finset.Icc 0 (ZV c)).filter (fun q => ((q.2 : ℝ) - 1 / 8) / pr q.1 = bV c)

theorem hp : ∀ i, 1 ≤ pr i ∧ pr i ≤ (8 : ℝ) := by intro i; fin_cases i <;> norm_num [pr]
theorem hp1 : ∀ i, 1 ≤ pr i := fun i => (hp i).1
theorem pr_0 : pr (0 : Fin 7) = (8 : ℝ) := rfl
theorem pr_1 : pr (1 : Fin 7) = (7 : ℝ) := rfl
theorem pr_2 : pr (2 : Fin 7) = (1 : ℝ) := rfl
theorem pr_3 : pr (3 : Fin 7) = (2 : ℝ) := rfl
theorem pr_4 : pr (4 : Fin 7) = (4 : ℝ) := rfl
theorem pr_5 : pr (5 : Fin 7) = (5 : ℝ) := rfl
theorem pr_6 : pr (6 : Fin 7) = (6 : ℝ) := rfl
theorem aV_0 : aV (0 : Fin 1) = (17 / 56 : ℝ) := rfl
theorem bV_0 : bV (0 : Fin 1) = (5 / 16 : ℝ) := rfl
theorem dV_0 : dV (0 : Fin 1) = (1 / 56 : ℝ) := rfl
theorem TV_0 : TV (0 : Fin 1) = (37 / 112 : ℝ) := rfl
theorem ZV_0 : ZV (0 : Fin 1) = (5 : ℤ) := rfl
theorem hab : ∀ c, aV c ≤ bV c := by intro c; fin_cases c <;> norm_num [aV, bV]
theorem hd0 : ∀ c, 0 < dV c := by intro c; fin_cases c <;> norm_num [dV]
theorem hdP : ∀ c, dV c ≤ 1 / (4 * (8 : ℝ)) := by intro c; fin_cases c <;> norm_num [dV]
theorem haP : ∀ c, dV c < aV c := by intro c; fin_cases c <;> norm_num [dV, aV]
theorem hT : ∀ c, bV c + dV c ≤ TV c := by intro c; fin_cases c <;> norm_num [bV, dV, TV]
theorem hZ : ∀ c, ((8 : ℝ) + 1) * TV c + 1 ≤ (ZV c : ℝ) := by intro c; fin_cases c <;> norm_num [TV, ZV]
theorem hE (ε : ℝ) (hε : ε ≤ (1 / 2688 : ℝ)) : ∀ c, 8 * ((ZV c : ℝ) + 1) * ε ≤ dV c := by
  intro c; fin_cases c <;> norm_num [ZV, dV] <;> linarith
theorem hcls : ∀ c i, ∀ z : ℤ, 0 ≤ z → z ≤ ZV c →
    ((z : ℝ) + 1 / 8) / pr i ≤ aV c - dV c ∨ bV c + dV c ≤ ((z : ℝ) - 1 / 8) / pr i ∨
      ((z : ℝ) + 1 / 8) / pr i = aV c ∨ ((z : ℝ) - 1 / 8) / pr i = bV c := by
  intro c i z h0 h1
  fin_cases c <;> fin_cases i <;> simp [ZV] at h1 <;> interval_cases z <;> norm_num [pr, aV, bV, dV]
theorem hEXne : ∀ c, (EXs c).Nonempty := by
  intro c
  fin_cases c
  · exact ⟨(1, 2), by simp [EXs, ZV, pr, aV] <;> norm_num⟩
theorem hENne : ∀ c, (ENs c).Nonempty := by
  intro c
  fin_cases c
  · exact ⟨(6, 2), by simp [ENs, ZV, pr, bV] <;> norm_num⟩
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
  · exact zone_kill_gen pr x ε HV (1 / 512 : ℝ) hp1 hdev hεH (by norm_num) (2 : Fin 7) 0 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (2 : Fin 7))
  rcases le_total t (71 / 512 : ℝ) with hs1 | hs1
  · exact zone_kill_gen pr x ε HV (1 / 512 : ℝ) hp1 hdev hεH (by norm_num) (0 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (0 : Fin 7))
  rcases le_total t (569 / 3584 : ℝ) with hs2 | hs2
  · exact zone_kill_gen pr x ε HV (1 / 512 : ℝ) hp1 hdev hεH (by norm_num) (1 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (1 : Fin 7))
  rcases le_total t (95 / 512 : ℝ) with hs3 | hs3
  · exact zone_kill_gen pr x ε HV (1 / 512 : ℝ) hp1 hdev hεH (by norm_num) (6 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (6 : Fin 7))
  rcases le_total t (571 / 2560 : ℝ) with hs4 | hs4
  · exact zone_kill_gen pr x ε HV (1 / 512 : ℝ) hp1 hdev hεH (by norm_num) (5 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (5 : Fin 7))
  rcases le_total t (143 / 512 : ℝ) with hs5 | hs5
  · exact zone_kill_gen pr x ε HV (1 / 512 : ℝ) hp1 hdev hεH (by norm_num) (4 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (4 : Fin 7))
  exact zone_kill_gen pr x ε HV (1 / 512 : ℝ) hp1 hdev hεH (by norm_num) (1 : Fin 7) 2 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (1 : Fin 7))
theorem cov (x : Fin 7 → ℝ) (ε : ℝ) (hε : ε ≤ (1 / 2688 : ℝ)) (hdev : ∀ i, |x i - pr i| ≤ ε) :
    ∀ t : ℝ, 0 < t → t ≤ HV → (∀ c, ¬ (aV c - dV c / 2 ≤ t ∧ t ≤ bV c + dV c / 2)) →
      ¬ (∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)) := by
  intro t h0 hHt hnone hlon
  have hεH : ε * HV ≤ (1 / 512 : ℝ) / 2 := by
    have hε0 : 0 ≤ ε := le_trans (abs_nonneg _) (hdev 0)
    have : ε * HV ≤ (1 / 2688 : ℝ) * HV := mul_le_mul_of_nonneg_right hε (by norm_num [HV])
    have h2 : (1 / 2688 : ℝ) * HV ≤ (1 / 512 : ℝ) / 2 := by norm_num [HV]
    linarith
  have n0 := hnone (0 : Fin 1)
  rw [aV_0, bV_0, dV_0] at n0
  rcases lt_or_ge t (33 / 112 : ℝ) with c0 | c0
  · exact gap0 x ε hdev hεH t h0.le hHt h0.le (by linarith) hlon
  have d0 : (9 / 28 : ℝ) < t := by
    by_contra hc; push Not at hc; exact n0 ⟨by linarith, by linarith⟩
  have hHv : HV = (9 / 28 : ℝ) := rfl
  exact absurd (by linarith : t ≤ (9 / 28 : ℝ)) (not_le.2 d0)

theorem inst (x : Fin 7 → ℝ) (ε : ℝ) (hε : ε ≤ (1 / 2688 : ℝ)) (hdev : ∀ i, |x i - pr i| ≤ ε) :
    ∃ c₀ : Fin 1, Alive (mxOf x EXs hEXne) (mnOf x ENs hENne) c₀ ∧
      (∀ c, c < c₀ → ¬ Alive (mxOf x EXs hEXne) (mnOf x ENs hENne) c) ∧
      IsLeast {t : ℝ | 0 < t ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)} (mxOf x EXs hEXne c₀) :=
  landing_cert 1 (8 : ℝ) (by norm_num) pr x hp ε hdev aV bV dV TV ZV hab hd0 hdP haP hT hZ (hE ε hε) hcls EXs ENs hEXne hENne
    hEXdef hENdef hsepL HV hHL (cov x ε hε hdev) (0 : Fin 1) (by rw [dV_0, bV_0, aV_0]; norm_num)

noncomputable def sv : Fin 8 → ℝ := ![(1 : ℝ), (2 : ℝ), (8 : ℝ), (9 : ℝ), (11 : ℝ), (13 : ℝ), (14 : ℝ), (15 : ℝ)]
def sg : Fin 7 → Fin 8 := ![0, 1, 2, 4, 5, 6, 7]

theorem sv_0 : sv (0 : Fin 8) = (1 : ℝ) := rfl
theorem sv_1 : sv (1 : Fin 8) = (2 : ℝ) := rfl
theorem sv_2 : sv (2 : Fin 8) = (8 : ℝ) := rfl
theorem sv_3 : sv (3 : Fin 8) = (9 : ℝ) := rfl
theorem sv_4 : sv (4 : Fin 8) = (11 : ℝ) := rfl
theorem sv_5 : sv (5 : Fin 8) = (13 : ℝ) := rfl
theorem sv_6 : sv (6 : Fin 8) = (14 : ℝ) := rfl
theorem sv_7 : sv (7 : Fin 8) = (15 : ℝ) := rfl
theorem sg_0 : sg (0 : Fin 7) = (0 : Fin 8) := rfl
theorem sg_1 : sg (1 : Fin 7) = (1 : Fin 8) := rfl
theorem sg_2 : sg (2 : Fin 7) = (2 : Fin 8) := rfl
theorem sg_3 : sg (3 : Fin 7) = (4 : Fin 8) := rfl
theorem sg_4 : sg (4 : Fin 7) = (5 : Fin 8) := rfl
theorem sg_5 : sg (5 : Fin 7) = (6 : Fin 8) := rfl
theorem sg_6 : sg (6 : Fin 7) = (7 : Fin 8) := rfl

theorem inst_arr (v : Fin 8 → ℝ) (η : ℝ) (hη : η ≤ (1 / 5376 : ℝ)) (hv : ∀ j, |v j - sv j| ≤ η) :
    ∃ c₀ : Fin 1, Alive (mxOf (fun i => |v (sg i) - v (3 : Fin 8)|) EXs hEXne) (mnOf (fun i => |v (sg i) - v (3 : Fin 8)|) ENs hENne) c₀ ∧
      (∀ c, c < c₀ → ¬ Alive (mxOf (fun i => |v (sg i) - v (3 : Fin 8)|) EXs hEXne) (mnOf (fun i => |v (sg i) - v (3 : Fin 8)|) ENs hENne) c) ∧
      IsLeast {t : ℝ | 0 < t ∧ IsolatedAt v (3 : Fin 8) t} (mxOf (fun i => |v (sg i) - v (3 : Fin 8)|) EXs hEXne c₀) := by
  have hσk : ∀ i, sg i ≠ (3 : Fin 8) := by decide
  have hσ : ∀ j : Fin 8, j ≠ (3 : Fin 8) → ∃ i, sg i = j := by decide
  have hpr : ∀ i, pr i = |sv (sg i) - sv (3 : Fin 8)| := by
    intro i; rcases fin7_cases i with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6, sv_0, sv_1, sv_2, sv_3, sv_4, sv_5, sv_6, sv_7, sg_0, sg_1, sg_2, sg_3, sg_4, sg_5, sg_6]
  have hdev : ∀ i, |(|v (sg i) - v (3 : Fin 8)| - pr i)| ≤ 2 * η := by
    intro i; rw [hpr i]; exact reading_dev v sv η hv (sg i) (3 : Fin 8)
  obtain ⟨c₀, hal, hbf, hT0⟩ := inst (fun i => |v (sg i) - v (3 : Fin 8)|) (2 * η) (by linarith) hdev
  have hset : {t : ℝ | 0 < t ∧ IsolatedAt v (3 : Fin 8) t} =
      {t : ℝ | 0 < t ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (|v (sg i) - v (3 : Fin 8)| * t)} := by
    ext t; simp only [Set.mem_setOf_eq]; rw [iso_iff_readings v (3 : Fin 8) sg hσk hσ t]
  rw [hset]; exact ⟨c₀, hal, hbf, hT0⟩

#print axioms inst_arr

end Fresh.CertRR.R13315

