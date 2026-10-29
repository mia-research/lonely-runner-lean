import Mathlib
import Fresh.Framework
import Fresh.Localisation
import Fresh.LandingCert

/-!
# Landing certificate `CertRS.R06974`: speeds (1, 2, 4, 5, 8, 9, 10, 16), subject index 6

Generated 2026-10-24 by `experiments/n8/cert_gen_v1.py` (exact Fractions).  Baseline readings [9, 8, 6, 5, 2, 1, 6].  Components up to the first wide one: 1.
Radius: speeds within `η ≤ 1/6144` of the baseline speeds, giving `ε = 2η ≤ 1/3072`.  Covering margin `μ = 1/256`.
`hcov` is **[PROVISIONAL: covering]**, supporting the claim that the first lonely instant of this subject is the largest exit of the first alive component.
Result `inst_arr`: for such `v`, the subject has a first isolation (a least element over all `t > 0`).  Grades: [L].
-/

open Classical

namespace Fresh.CertRS.R06974

open Fresh Fresh.LandingCert Fresh.LandingRule

noncomputable def pr : Fin 7 → ℝ := ![(9 : ℝ), (8 : ℝ), (6 : ℝ), (5 : ℝ), (2 : ℝ), (1 : ℝ), (6 : ℝ)]
noncomputable def aV : Fin 1 → ℝ := ![(9 / 64 : ℝ)]
noncomputable def bV : Fin 1 → ℝ := ![(7 / 48 : ℝ)]
noncomputable def dV : Fin 1 → ℝ := ![(1 / 96 : ℝ)]
noncomputable def TV : Fin 1 → ℝ := ![(5 / 32 : ℝ)]
def ZV : Fin 1 → ℤ := ![3]
noncomputable def HV : ℝ := (29 / 192 : ℝ)
noncomputable def EXs (c : Fin 1) : Finset (Fin 7 × ℤ) :=
  (Finset.univ ×ˢ Finset.Icc 0 (ZV c)).filter (fun q => ((q.2 : ℝ) + 1 / 8) / pr q.1 = aV c)
noncomputable def ENs (c : Fin 1) : Finset (Fin 7 × ℤ) :=
  (Finset.univ ×ˢ Finset.Icc 0 (ZV c)).filter (fun q => ((q.2 : ℝ) - 1 / 8) / pr q.1 = bV c)

theorem hp : ∀ i, 1 ≤ pr i ∧ pr i ≤ (9 : ℝ) := by intro i; fin_cases i <;> norm_num [pr]
theorem hp1 : ∀ i, 1 ≤ pr i := fun i => (hp i).1
theorem pr_0 : pr (0 : Fin 7) = (9 : ℝ) := rfl
theorem pr_1 : pr (1 : Fin 7) = (8 : ℝ) := rfl
theorem pr_2 : pr (2 : Fin 7) = (6 : ℝ) := rfl
theorem pr_3 : pr (3 : Fin 7) = (5 : ℝ) := rfl
theorem pr_4 : pr (4 : Fin 7) = (2 : ℝ) := rfl
theorem pr_5 : pr (5 : Fin 7) = (1 : ℝ) := rfl
theorem pr_6 : pr (6 : Fin 7) = (6 : ℝ) := rfl
theorem aV_0 : aV (0 : Fin 1) = (9 / 64 : ℝ) := rfl
theorem bV_0 : bV (0 : Fin 1) = (7 / 48 : ℝ) := rfl
theorem dV_0 : dV (0 : Fin 1) = (1 / 96 : ℝ) := rfl
theorem TV_0 : TV (0 : Fin 1) = (5 / 32 : ℝ) := rfl
theorem ZV_0 : ZV (0 : Fin 1) = (3 : ℤ) := rfl
theorem hab : ∀ c, aV c ≤ bV c := by intro c; fin_cases c <;> norm_num [aV, bV]
theorem hd0 : ∀ c, 0 < dV c := by intro c; fin_cases c <;> norm_num [dV]
theorem hdP : ∀ c, dV c ≤ 1 / (4 * (9 : ℝ)) := by intro c; fin_cases c <;> norm_num [dV]
theorem haP : ∀ c, dV c < aV c := by intro c; fin_cases c <;> norm_num [dV, aV]
theorem hT : ∀ c, bV c + dV c ≤ TV c := by intro c; fin_cases c <;> norm_num [bV, dV, TV]
theorem hZ : ∀ c, ((9 : ℝ) + 1) * TV c + 1 ≤ (ZV c : ℝ) := by intro c; fin_cases c <;> norm_num [TV, ZV]
theorem hE (ε : ℝ) (hε : ε ≤ (1 / 3072 : ℝ)) : ∀ c, 8 * ((ZV c : ℝ) + 1) * ε ≤ dV c := by
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

theorem gap0 (x : Fin 7 → ℝ) (ε : ℝ) (hdev : ∀ i, |x i - pr i| ≤ ε) (hεH : ε * HV ≤ (1 / 256 : ℝ) / 2) (t : ℝ) (h0 : 0 ≤ t)
    (hHt : t ≤ HV) (h1 : (0 : ℝ) ≤ t) (h2 : t ≤ (13 / 96 : ℝ)) (hlon : ∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)) : False := by
  rcases le_total t (31 / 256 : ℝ) with hs0 | hs0
  · exact zone_kill_gen pr x ε HV (1 / 256 : ℝ) hp1 hdev hεH (by norm_num) (5 : Fin 7) 0 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (5 : Fin 7))
  exact zone_kill_gen pr x ε HV (1 / 256 : ℝ) hp1 hdev hεH (by norm_num) (1 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (1 : Fin 7))
theorem cov (x : Fin 7 → ℝ) (ε : ℝ) (hε : ε ≤ (1 / 3072 : ℝ)) (hdev : ∀ i, |x i - pr i| ≤ ε) :
    ∀ t : ℝ, 0 < t → t ≤ HV → (∀ c, ¬ (aV c - dV c / 2 ≤ t ∧ t ≤ bV c + dV c / 2)) →
      ¬ (∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)) := by
  intro t h0 hHt hnone hlon
  have hεH : ε * HV ≤ (1 / 256 : ℝ) / 2 := by
    have hε0 : 0 ≤ ε := le_trans (abs_nonneg _) (hdev 0)
    have : ε * HV ≤ (1 / 3072 : ℝ) * HV := mul_le_mul_of_nonneg_right hε (by norm_num [HV])
    have h2 : (1 / 3072 : ℝ) * HV ≤ (1 / 256 : ℝ) / 2 := by norm_num [HV]
    linarith
  have n0 := hnone (0 : Fin 1)
  rw [aV_0, bV_0, dV_0] at n0
  rcases lt_or_ge t (13 / 96 : ℝ) with c0 | c0
  · exact gap0 x ε hdev hεH t h0.le hHt h0.le (by linarith) hlon
  have d0 : (29 / 192 : ℝ) < t := by
    by_contra hc; push Not at hc; exact n0 ⟨by linarith, by linarith⟩
  have hHv : HV = (29 / 192 : ℝ) := rfl
  exact absurd (by linarith : t ≤ (29 / 192 : ℝ)) (not_le.2 d0)

theorem inst (x : Fin 7 → ℝ) (ε : ℝ) (hε : ε ≤ (1 / 3072 : ℝ)) (hdev : ∀ i, |x i - pr i| ≤ ε) :
    ∃ c₀ : Fin 1, Alive (mxOf x EXs hEXne) (mnOf x ENs hENne) c₀ ∧
      (∀ c, c < c₀ → ¬ Alive (mxOf x EXs hEXne) (mnOf x ENs hENne) c) ∧
      IsLeast {t : ℝ | 0 < t ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)} (mxOf x EXs hEXne c₀) :=
  landing_cert 1 (9 : ℝ) (by norm_num) pr x hp ε hdev aV bV dV TV ZV hab hd0 hdP haP hT hZ (hE ε hε) hcls EXs ENs hEXne hENne
    hEXdef hENdef hsepL HV hHL (cov x ε hε hdev) (0 : Fin 1) (by rw [dV_0, bV_0, aV_0]; norm_num)

noncomputable def sv : Fin 8 → ℝ := ![(1 : ℝ), (2 : ℝ), (4 : ℝ), (5 : ℝ), (8 : ℝ), (9 : ℝ), (10 : ℝ), (16 : ℝ)]
def sg : Fin 7 → Fin 8 := ![0, 1, 2, 3, 4, 5, 7]

theorem sv_0 : sv (0 : Fin 8) = (1 : ℝ) := rfl
theorem sv_1 : sv (1 : Fin 8) = (2 : ℝ) := rfl
theorem sv_2 : sv (2 : Fin 8) = (4 : ℝ) := rfl
theorem sv_3 : sv (3 : Fin 8) = (5 : ℝ) := rfl
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
theorem sg_6 : sg (6 : Fin 7) = (7 : Fin 8) := rfl

theorem inst_arr (v : Fin 8 → ℝ) (η : ℝ) (hη : η ≤ (1 / 6144 : ℝ)) (hv : ∀ j, |v j - sv j| ≤ η) :
    ∃ c₀ : Fin 1, Alive (mxOf (fun i => |v (sg i) - v (6 : Fin 8)|) EXs hEXne) (mnOf (fun i => |v (sg i) - v (6 : Fin 8)|) ENs hENne) c₀ ∧
      (∀ c, c < c₀ → ¬ Alive (mxOf (fun i => |v (sg i) - v (6 : Fin 8)|) EXs hEXne) (mnOf (fun i => |v (sg i) - v (6 : Fin 8)|) ENs hENne) c) ∧
      IsLeast {t : ℝ | 0 < t ∧ IsolatedAt v (6 : Fin 8) t} (mxOf (fun i => |v (sg i) - v (6 : Fin 8)|) EXs hEXne c₀) := by
  have hσk : ∀ i, sg i ≠ (6 : Fin 8) := by decide
  have hσ : ∀ j : Fin 8, j ≠ (6 : Fin 8) → ∃ i, sg i = j := by decide
  have hpr : ∀ i, pr i = |sv (sg i) - sv (6 : Fin 8)| := by
    intro i; rcases fin7_cases i with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6, sv_0, sv_1, sv_2, sv_3, sv_4, sv_5, sv_6, sv_7, sg_0, sg_1, sg_2, sg_3, sg_4, sg_5, sg_6]
  have hdev : ∀ i, |(|v (sg i) - v (6 : Fin 8)| - pr i)| ≤ 2 * η := by
    intro i; rw [hpr i]; exact reading_dev v sv η hv (sg i) (6 : Fin 8)
  obtain ⟨c₀, hal, hbf, hT0⟩ := inst (fun i => |v (sg i) - v (6 : Fin 8)|) (2 * η) (by linarith) hdev
  have hset : {t : ℝ | 0 < t ∧ IsolatedAt v (6 : Fin 8) t} =
      {t : ℝ | 0 < t ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (|v (sg i) - v (6 : Fin 8)| * t)} := by
    ext t; simp only [Set.mem_setOf_eq]; rw [iso_iff_readings v (6 : Fin 8) sg hσk hσ t]
  rw [hset]; exact ⟨c₀, hal, hbf, hT0⟩

#print axioms inst_arr

end Fresh.CertRS.R06974



/-!
# Landing certificate `CertRS.R06977`: speeds (1, 2, 4, 5, 8, 9, 11, 13), subject index 1

Generated 2026-10-24 by `experiments/n8/cert_gen_v1.py` (exact Fractions).  Baseline readings [1, 2, 3, 6, 7, 9, 11].  Components up to the first wide one: 2.
Radius: speeds within `η ≤ 1/14080` of the baseline speeds, giving `ε = 2η ≤ 1/7040`.  Covering margin `μ = 1/512`.
`hcov` is **[PROVISIONAL: covering]**, supporting the claim that the first lonely instant of this subject is the largest exit of the first alive component.
Result `inst_arr`: for such `v`, the subject has a first isolation (a least element over all `t > 0`).  Grades: [L].
-/

open Classical

namespace Fresh.CertRS.R06977

open Fresh Fresh.LandingCert Fresh.LandingRule

noncomputable def pr : Fin 7 → ℝ := ![(1 : ℝ), (2 : ℝ), (3 : ℝ), (6 : ℝ), (7 : ℝ), (9 : ℝ), (11 : ℝ)]
noncomputable def aV : Fin 2 → ℝ := ![(1 / 8 : ℝ), (17 / 88 : ℝ)]
noncomputable def bV : Fin 2 → ℝ := ![(1 / 8 : ℝ), (5 / 24 : ℝ)]
noncomputable def dV : Fin 2 → ℝ := ![(1 / 48 : ℝ), (1 / 176 : ℝ)]
noncomputable def TV : Fin 2 → ℝ := ![(7 / 48 : ℝ), (113 / 528 : ℝ)]
def ZV : Fin 2 → ℤ := ![3, 4]
noncomputable def HV : ℝ := (223 / 1056 : ℝ)
noncomputable def EXs (c : Fin 2) : Finset (Fin 7 × ℤ) :=
  (Finset.univ ×ˢ Finset.Icc 0 (ZV c)).filter (fun q => ((q.2 : ℝ) + 1 / 8) / pr q.1 = aV c)
noncomputable def ENs (c : Fin 2) : Finset (Fin 7 × ℤ) :=
  (Finset.univ ×ˢ Finset.Icc 0 (ZV c)).filter (fun q => ((q.2 : ℝ) - 1 / 8) / pr q.1 = bV c)

theorem hp : ∀ i, 1 ≤ pr i ∧ pr i ≤ (11 : ℝ) := by intro i; fin_cases i <;> norm_num [pr]
theorem hp1 : ∀ i, 1 ≤ pr i := fun i => (hp i).1
theorem pr_0 : pr (0 : Fin 7) = (1 : ℝ) := rfl
theorem pr_1 : pr (1 : Fin 7) = (2 : ℝ) := rfl
theorem pr_2 : pr (2 : Fin 7) = (3 : ℝ) := rfl
theorem pr_3 : pr (3 : Fin 7) = (6 : ℝ) := rfl
theorem pr_4 : pr (4 : Fin 7) = (7 : ℝ) := rfl
theorem pr_5 : pr (5 : Fin 7) = (9 : ℝ) := rfl
theorem pr_6 : pr (6 : Fin 7) = (11 : ℝ) := rfl
theorem aV_0 : aV (0 : Fin 2) = (1 / 8 : ℝ) := rfl
theorem bV_0 : bV (0 : Fin 2) = (1 / 8 : ℝ) := rfl
theorem dV_0 : dV (0 : Fin 2) = (1 / 48 : ℝ) := rfl
theorem TV_0 : TV (0 : Fin 2) = (7 / 48 : ℝ) := rfl
theorem ZV_0 : ZV (0 : Fin 2) = (3 : ℤ) := rfl
theorem aV_1 : aV (1 : Fin 2) = (17 / 88 : ℝ) := rfl
theorem bV_1 : bV (1 : Fin 2) = (5 / 24 : ℝ) := rfl
theorem dV_1 : dV (1 : Fin 2) = (1 / 176 : ℝ) := rfl
theorem TV_1 : TV (1 : Fin 2) = (113 / 528 : ℝ) := rfl
theorem ZV_1 : ZV (1 : Fin 2) = (4 : ℤ) := rfl
theorem hab : ∀ c, aV c ≤ bV c := by intro c; fin_cases c <;> norm_num [aV, bV]
theorem hd0 : ∀ c, 0 < dV c := by intro c; fin_cases c <;> norm_num [dV]
theorem hdP : ∀ c, dV c ≤ 1 / (4 * (11 : ℝ)) := by intro c; fin_cases c <;> norm_num [dV]
theorem haP : ∀ c, dV c < aV c := by intro c; fin_cases c <;> norm_num [dV, aV]
theorem hT : ∀ c, bV c + dV c ≤ TV c := by intro c; fin_cases c <;> norm_num [bV, dV, TV]
theorem hZ : ∀ c, ((11 : ℝ) + 1) * TV c + 1 ≤ (ZV c : ℝ) := by intro c; fin_cases c <;> norm_num [TV, ZV]
theorem hE (ε : ℝ) (hε : ε ≤ (1 / 7040 : ℝ)) : ∀ c, 8 * ((ZV c : ℝ) + 1) * ε ≤ dV c := by
  intro c; fin_cases c <;> norm_num [ZV, dV] <;> linarith
theorem hcls : ∀ c i, ∀ z : ℤ, 0 ≤ z → z ≤ ZV c →
    ((z : ℝ) + 1 / 8) / pr i ≤ aV c - dV c ∨ bV c + dV c ≤ ((z : ℝ) - 1 / 8) / pr i ∨
      ((z : ℝ) + 1 / 8) / pr i = aV c ∨ ((z : ℝ) - 1 / 8) / pr i = bV c := by
  intro c i z h0 h1
  fin_cases c <;> fin_cases i <;> simp [ZV] at h1 <;> interval_cases z <;> norm_num [pr, aV, bV, dV]
theorem hEXne : ∀ c, (EXs c).Nonempty := by
  intro c
  fin_cases c
  · exact ⟨(0, 0), by simp [EXs, ZV, pr, aV] <;> norm_num⟩
  · exact ⟨(6, 2), by simp [EXs, ZV, pr, aV] <;> norm_num⟩
theorem hENne : ∀ c, (ENs c).Nonempty := by
  intro c
  fin_cases c
  · exact ⟨(4, 1), by simp [ENs, ZV, pr, bV] <;> norm_num⟩
  · exact ⟨(5, 2), by simp [ENs, ZV, pr, bV] <;> norm_num⟩
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
    (hHt : t ≤ HV) (h1 : (0 : ℝ) ≤ t) (h2 : t ≤ (11 / 96 : ℝ)) (hlon : ∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)) : False := by
  exact zone_kill_gen pr x ε HV (1 / 512 : ℝ) hp1 hdev hεH (by norm_num) (0 : Fin 7) 0 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (0 : Fin 7))
theorem gap1 (x : Fin 7 → ℝ) (ε : ℝ) (hdev : ∀ i, |x i - pr i| ≤ ε) (hεH : ε * HV ≤ (1 / 512 : ℝ) / 2) (t : ℝ) (h0 : 0 ≤ t)
    (hHt : t ≤ HV) (h1 : (13 / 96 : ℝ) ≤ t) (h2 : t ≤ (67 / 352 : ℝ)) (hlon : ∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)) : False := by
  rcases le_total t (569 / 3584 : ℝ) with hs0 | hs0
  · exact zone_kill_gen pr x ε HV (1 / 512 : ℝ) hp1 hdev hεH (by norm_num) (4 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (4 : Fin 7))
  rcases le_total t (95 / 512 : ℝ) with hs1 | hs1
  · exact zone_kill_gen pr x ε HV (1 / 512 : ℝ) hp1 hdev hεH (by norm_num) (3 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (3 : Fin 7))
  exact zone_kill_gen pr x ε HV (1 / 512 : ℝ) hp1 hdev hεH (by norm_num) (6 : Fin 7) 2 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (6 : Fin 7))
theorem cov (x : Fin 7 → ℝ) (ε : ℝ) (hε : ε ≤ (1 / 7040 : ℝ)) (hdev : ∀ i, |x i - pr i| ≤ ε) :
    ∀ t : ℝ, 0 < t → t ≤ HV → (∀ c, ¬ (aV c - dV c / 2 ≤ t ∧ t ≤ bV c + dV c / 2)) →
      ¬ (∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)) := by
  intro t h0 hHt hnone hlon
  have hεH : ε * HV ≤ (1 / 512 : ℝ) / 2 := by
    have hε0 : 0 ≤ ε := le_trans (abs_nonneg _) (hdev 0)
    have : ε * HV ≤ (1 / 7040 : ℝ) * HV := mul_le_mul_of_nonneg_right hε (by norm_num [HV])
    have h2 : (1 / 7040 : ℝ) * HV ≤ (1 / 512 : ℝ) / 2 := by norm_num [HV]
    linarith
  have n0 := hnone (0 : Fin 2)
  rw [aV_0, bV_0, dV_0] at n0
  have n1 := hnone (1 : Fin 2)
  rw [aV_1, bV_1, dV_1] at n1
  rcases lt_or_ge t (11 / 96 : ℝ) with c0 | c0
  · exact gap0 x ε hdev hεH t h0.le hHt h0.le (by linarith) hlon
  have d0 : (13 / 96 : ℝ) < t := by
    by_contra hc; push Not at hc; exact n0 ⟨by linarith, by linarith⟩
  rcases lt_or_ge t (67 / 352 : ℝ) with c1 | c1
  · exact gap1 x ε hdev hεH t h0.le hHt d0.le (by linarith) hlon
  have d1 : (223 / 1056 : ℝ) < t := by
    by_contra hc; push Not at hc; exact n1 ⟨by linarith, by linarith⟩
  have hHv : HV = (223 / 1056 : ℝ) := rfl
  exact absurd (by linarith : t ≤ (223 / 1056 : ℝ)) (not_le.2 d1)

theorem inst (x : Fin 7 → ℝ) (ε : ℝ) (hε : ε ≤ (1 / 7040 : ℝ)) (hdev : ∀ i, |x i - pr i| ≤ ε) :
    ∃ c₀ : Fin 2, Alive (mxOf x EXs hEXne) (mnOf x ENs hENne) c₀ ∧
      (∀ c, c < c₀ → ¬ Alive (mxOf x EXs hEXne) (mnOf x ENs hENne) c) ∧
      IsLeast {t : ℝ | 0 < t ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)} (mxOf x EXs hEXne c₀) :=
  landing_cert 2 (11 : ℝ) (by norm_num) pr x hp ε hdev aV bV dV TV ZV hab hd0 hdP haP hT hZ (hE ε hε) hcls EXs ENs hEXne hENne
    hEXdef hENdef hsepL HV hHL (cov x ε hε hdev) (1 : Fin 2) (by rw [dV_1, bV_1, aV_1]; norm_num)

noncomputable def sv : Fin 8 → ℝ := ![(1 : ℝ), (2 : ℝ), (4 : ℝ), (5 : ℝ), (8 : ℝ), (9 : ℝ), (11 : ℝ), (13 : ℝ)]
def sg : Fin 7 → Fin 8 := ![0, 2, 3, 4, 5, 6, 7]

theorem sv_0 : sv (0 : Fin 8) = (1 : ℝ) := rfl
theorem sv_1 : sv (1 : Fin 8) = (2 : ℝ) := rfl
theorem sv_2 : sv (2 : Fin 8) = (4 : ℝ) := rfl
theorem sv_3 : sv (3 : Fin 8) = (5 : ℝ) := rfl
theorem sv_4 : sv (4 : Fin 8) = (8 : ℝ) := rfl
theorem sv_5 : sv (5 : Fin 8) = (9 : ℝ) := rfl
theorem sv_6 : sv (6 : Fin 8) = (11 : ℝ) := rfl
theorem sv_7 : sv (7 : Fin 8) = (13 : ℝ) := rfl
theorem sg_0 : sg (0 : Fin 7) = (0 : Fin 8) := rfl
theorem sg_1 : sg (1 : Fin 7) = (2 : Fin 8) := rfl
theorem sg_2 : sg (2 : Fin 7) = (3 : Fin 8) := rfl
theorem sg_3 : sg (3 : Fin 7) = (4 : Fin 8) := rfl
theorem sg_4 : sg (4 : Fin 7) = (5 : Fin 8) := rfl
theorem sg_5 : sg (5 : Fin 7) = (6 : Fin 8) := rfl
theorem sg_6 : sg (6 : Fin 7) = (7 : Fin 8) := rfl

theorem inst_arr (v : Fin 8 → ℝ) (η : ℝ) (hη : η ≤ (1 / 14080 : ℝ)) (hv : ∀ j, |v j - sv j| ≤ η) :
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

end Fresh.CertRS.R06977



/-!
# Landing certificate `CertRS.R06978`: speeds (1, 2, 4, 5, 8, 9, 11, 13), subject index 2

Generated 2026-10-24 by `experiments/n8/cert_gen_v1.py` (exact Fractions).  Baseline readings [3, 2, 1, 4, 5, 7, 9].  Components up to the first wide one: 2.
Radius: speeds within `η ≤ 1/4480` of the baseline speeds, giving `ε = 2η ≤ 1/2240`.  Covering margin `μ = 1/128`.
`hcov` is **[PROVISIONAL: covering]**, supporting the claim that the first lonely instant of this subject is the largest exit of the first alive component.
Result `inst_arr`: for such `v`, the subject has a first isolation (a least element over all `t > 0`).  Grades: [L].
-/

open Classical

namespace Fresh.CertRS.R06978

open Fresh Fresh.LandingCert Fresh.LandingRule

noncomputable def pr : Fin 7 → ℝ := ![(3 : ℝ), (2 : ℝ), (1 : ℝ), (4 : ℝ), (5 : ℝ), (7 : ℝ), (9 : ℝ)]
noncomputable def aV : Fin 2 → ℝ := ![(1 / 8 : ℝ), (9 / 56 : ℝ)]
noncomputable def bV : Fin 2 → ℝ := ![(1 / 8 : ℝ), (7 / 40 : ℝ)]
noncomputable def dV : Fin 2 → ℝ := ![(1 / 56 : ℝ), (1 / 56 : ℝ)]
noncomputable def TV : Fin 2 → ℝ := ![(1 / 7 : ℝ), (27 / 140 : ℝ)]
def ZV : Fin 2 → ℤ := ![3, 4]
noncomputable def HV : ℝ := (103 / 560 : ℝ)
noncomputable def EXs (c : Fin 2) : Finset (Fin 7 × ℤ) :=
  (Finset.univ ×ˢ Finset.Icc 0 (ZV c)).filter (fun q => ((q.2 : ℝ) + 1 / 8) / pr q.1 = aV c)
noncomputable def ENs (c : Fin 2) : Finset (Fin 7 × ℤ) :=
  (Finset.univ ×ˢ Finset.Icc 0 (ZV c)).filter (fun q => ((q.2 : ℝ) - 1 / 8) / pr q.1 = bV c)

theorem hp : ∀ i, 1 ≤ pr i ∧ pr i ≤ (9 : ℝ) := by intro i; fin_cases i <;> norm_num [pr]
theorem hp1 : ∀ i, 1 ≤ pr i := fun i => (hp i).1
theorem pr_0 : pr (0 : Fin 7) = (3 : ℝ) := rfl
theorem pr_1 : pr (1 : Fin 7) = (2 : ℝ) := rfl
theorem pr_2 : pr (2 : Fin 7) = (1 : ℝ) := rfl
theorem pr_3 : pr (3 : Fin 7) = (4 : ℝ) := rfl
theorem pr_4 : pr (4 : Fin 7) = (5 : ℝ) := rfl
theorem pr_5 : pr (5 : Fin 7) = (7 : ℝ) := rfl
theorem pr_6 : pr (6 : Fin 7) = (9 : ℝ) := rfl
theorem aV_0 : aV (0 : Fin 2) = (1 / 8 : ℝ) := rfl
theorem bV_0 : bV (0 : Fin 2) = (1 / 8 : ℝ) := rfl
theorem dV_0 : dV (0 : Fin 2) = (1 / 56 : ℝ) := rfl
theorem TV_0 : TV (0 : Fin 2) = (1 / 7 : ℝ) := rfl
theorem ZV_0 : ZV (0 : Fin 2) = (3 : ℤ) := rfl
theorem aV_1 : aV (1 : Fin 2) = (9 / 56 : ℝ) := rfl
theorem bV_1 : bV (1 : Fin 2) = (7 / 40 : ℝ) := rfl
theorem dV_1 : dV (1 : Fin 2) = (1 / 56 : ℝ) := rfl
theorem TV_1 : TV (1 : Fin 2) = (27 / 140 : ℝ) := rfl
theorem ZV_1 : ZV (1 : Fin 2) = (4 : ℤ) := rfl
theorem hab : ∀ c, aV c ≤ bV c := by intro c; fin_cases c <;> norm_num [aV, bV]
theorem hd0 : ∀ c, 0 < dV c := by intro c; fin_cases c <;> norm_num [dV]
theorem hdP : ∀ c, dV c ≤ 1 / (4 * (9 : ℝ)) := by intro c; fin_cases c <;> norm_num [dV]
theorem haP : ∀ c, dV c < aV c := by intro c; fin_cases c <;> norm_num [dV, aV]
theorem hT : ∀ c, bV c + dV c ≤ TV c := by intro c; fin_cases c <;> norm_num [bV, dV, TV]
theorem hZ : ∀ c, ((9 : ℝ) + 1) * TV c + 1 ≤ (ZV c : ℝ) := by intro c; fin_cases c <;> norm_num [TV, ZV]
theorem hE (ε : ℝ) (hε : ε ≤ (1 / 2240 : ℝ)) : ∀ c, 8 * ((ZV c : ℝ) + 1) * ε ≤ dV c := by
  intro c; fin_cases c <;> norm_num [ZV, dV] <;> linarith
theorem hcls : ∀ c i, ∀ z : ℤ, 0 ≤ z → z ≤ ZV c →
    ((z : ℝ) + 1 / 8) / pr i ≤ aV c - dV c ∨ bV c + dV c ≤ ((z : ℝ) - 1 / 8) / pr i ∨
      ((z : ℝ) + 1 / 8) / pr i = aV c ∨ ((z : ℝ) - 1 / 8) / pr i = bV c := by
  intro c i z h0 h1
  fin_cases c <;> fin_cases i <;> simp [ZV] at h1 <;> interval_cases z <;> norm_num [pr, aV, bV, dV]
theorem hEXne : ∀ c, (EXs c).Nonempty := by
  intro c
  fin_cases c
  · exact ⟨(2, 0), by simp [EXs, ZV, pr, aV] <;> norm_num⟩
  · exact ⟨(5, 1), by simp [EXs, ZV, pr, aV] <;> norm_num⟩
theorem hENne : ∀ c, (ENs c).Nonempty := by
  intro c
  fin_cases c
  · exact ⟨(5, 1), by simp [ENs, ZV, pr, bV] <;> norm_num⟩
  · exact ⟨(4, 1), by simp [ENs, ZV, pr, bV] <;> norm_num⟩
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

theorem gap0 (x : Fin 7 → ℝ) (ε : ℝ) (hdev : ∀ i, |x i - pr i| ≤ ε) (hεH : ε * HV ≤ (1 / 128 : ℝ) / 2) (t : ℝ) (h0 : 0 ≤ t)
    (hHt : t ≤ HV) (h1 : (0 : ℝ) ≤ t) (h2 : t ≤ (13 / 112 : ℝ)) (hlon : ∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)) : False := by
  exact zone_kill_gen pr x ε HV (1 / 128 : ℝ) hp1 hdev hεH (by norm_num) (2 : Fin 7) 0 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (2 : Fin 7))
theorem gap1 (x : Fin 7 → ℝ) (ε : ℝ) (hdev : ∀ i, |x i - pr i| ≤ ε) (hεH : ε * HV ≤ (1 / 128 : ℝ) / 2) (t : ℝ) (h0 : 0 ≤ t)
    (hHt : t ≤ HV) (h1 : (15 / 112 : ℝ) ≤ t) (h2 : t ≤ (17 / 112 : ℝ)) (hlon : ∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)) : False := by
  exact zone_kill_gen pr x ε HV (1 / 128 : ℝ) hp1 hdev hεH (by norm_num) (5 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (5 : Fin 7))
theorem cov (x : Fin 7 → ℝ) (ε : ℝ) (hε : ε ≤ (1 / 2240 : ℝ)) (hdev : ∀ i, |x i - pr i| ≤ ε) :
    ∀ t : ℝ, 0 < t → t ≤ HV → (∀ c, ¬ (aV c - dV c / 2 ≤ t ∧ t ≤ bV c + dV c / 2)) →
      ¬ (∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)) := by
  intro t h0 hHt hnone hlon
  have hεH : ε * HV ≤ (1 / 128 : ℝ) / 2 := by
    have hε0 : 0 ≤ ε := le_trans (abs_nonneg _) (hdev 0)
    have : ε * HV ≤ (1 / 2240 : ℝ) * HV := mul_le_mul_of_nonneg_right hε (by norm_num [HV])
    have h2 : (1 / 2240 : ℝ) * HV ≤ (1 / 128 : ℝ) / 2 := by norm_num [HV]
    linarith
  have n0 := hnone (0 : Fin 2)
  rw [aV_0, bV_0, dV_0] at n0
  have n1 := hnone (1 : Fin 2)
  rw [aV_1, bV_1, dV_1] at n1
  rcases lt_or_ge t (13 / 112 : ℝ) with c0 | c0
  · exact gap0 x ε hdev hεH t h0.le hHt h0.le (by linarith) hlon
  have d0 : (15 / 112 : ℝ) < t := by
    by_contra hc; push Not at hc; exact n0 ⟨by linarith, by linarith⟩
  rcases lt_or_ge t (17 / 112 : ℝ) with c1 | c1
  · exact gap1 x ε hdev hεH t h0.le hHt d0.le (by linarith) hlon
  have d1 : (103 / 560 : ℝ) < t := by
    by_contra hc; push Not at hc; exact n1 ⟨by linarith, by linarith⟩
  have hHv : HV = (103 / 560 : ℝ) := rfl
  exact absurd (by linarith : t ≤ (103 / 560 : ℝ)) (not_le.2 d1)

theorem inst (x : Fin 7 → ℝ) (ε : ℝ) (hε : ε ≤ (1 / 2240 : ℝ)) (hdev : ∀ i, |x i - pr i| ≤ ε) :
    ∃ c₀ : Fin 2, Alive (mxOf x EXs hEXne) (mnOf x ENs hENne) c₀ ∧
      (∀ c, c < c₀ → ¬ Alive (mxOf x EXs hEXne) (mnOf x ENs hENne) c) ∧
      IsLeast {t : ℝ | 0 < t ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)} (mxOf x EXs hEXne c₀) :=
  landing_cert 2 (9 : ℝ) (by norm_num) pr x hp ε hdev aV bV dV TV ZV hab hd0 hdP haP hT hZ (hE ε hε) hcls EXs ENs hEXne hENne
    hEXdef hENdef hsepL HV hHL (cov x ε hε hdev) (1 : Fin 2) (by rw [dV_1, bV_1, aV_1]; norm_num)

noncomputable def sv : Fin 8 → ℝ := ![(1 : ℝ), (2 : ℝ), (4 : ℝ), (5 : ℝ), (8 : ℝ), (9 : ℝ), (11 : ℝ), (13 : ℝ)]
def sg : Fin 7 → Fin 8 := ![0, 1, 3, 4, 5, 6, 7]

theorem sv_0 : sv (0 : Fin 8) = (1 : ℝ) := rfl
theorem sv_1 : sv (1 : Fin 8) = (2 : ℝ) := rfl
theorem sv_2 : sv (2 : Fin 8) = (4 : ℝ) := rfl
theorem sv_3 : sv (3 : Fin 8) = (5 : ℝ) := rfl
theorem sv_4 : sv (4 : Fin 8) = (8 : ℝ) := rfl
theorem sv_5 : sv (5 : Fin 8) = (9 : ℝ) := rfl
theorem sv_6 : sv (6 : Fin 8) = (11 : ℝ) := rfl
theorem sv_7 : sv (7 : Fin 8) = (13 : ℝ) := rfl
theorem sg_0 : sg (0 : Fin 7) = (0 : Fin 8) := rfl
theorem sg_1 : sg (1 : Fin 7) = (1 : Fin 8) := rfl
theorem sg_2 : sg (2 : Fin 7) = (3 : Fin 8) := rfl
theorem sg_3 : sg (3 : Fin 7) = (4 : Fin 8) := rfl
theorem sg_4 : sg (4 : Fin 7) = (5 : Fin 8) := rfl
theorem sg_5 : sg (5 : Fin 7) = (6 : Fin 8) := rfl
theorem sg_6 : sg (6 : Fin 7) = (7 : Fin 8) := rfl

theorem inst_arr (v : Fin 8 → ℝ) (η : ℝ) (hη : η ≤ (1 / 4480 : ℝ)) (hv : ∀ j, |v j - sv j| ≤ η) :
    ∃ c₀ : Fin 2, Alive (mxOf (fun i => |v (sg i) - v (2 : Fin 8)|) EXs hEXne) (mnOf (fun i => |v (sg i) - v (2 : Fin 8)|) ENs hENne) c₀ ∧
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

end Fresh.CertRS.R06978



/-!
# Landing certificate `CertRS.R06979`: speeds (1, 2, 4, 5, 8, 9, 11, 13), subject index 3

Generated 2026-10-24 by `experiments/n8/cert_gen_v1.py` (exact Fractions).  Baseline readings [4, 3, 1, 3, 4, 6, 8].  Components up to the first wide one: 1.
Radius: speeds within `η ≤ 1/6144` of the baseline speeds, giving `ε = 2η ≤ 1/3072`.  Covering margin `μ = 1/256`.
`hcov` is **[PROVISIONAL: covering]**, supporting the claim that the first lonely instant of this subject is the largest exit of the first alive component.
Result `inst_arr`: for such `v`, the subject has a first isolation (a least element over all `t > 0`).  Grades: [L].
-/

open Classical

namespace Fresh.CertRS.R06979

open Fresh Fresh.LandingCert Fresh.LandingRule

noncomputable def pr : Fin 7 → ℝ := ![(4 : ℝ), (3 : ℝ), (1 : ℝ), (3 : ℝ), (4 : ℝ), (6 : ℝ), (8 : ℝ)]
noncomputable def aV : Fin 1 → ℝ := ![(9 / 64 : ℝ)]
noncomputable def bV : Fin 1 → ℝ := ![(7 / 48 : ℝ)]
noncomputable def dV : Fin 1 → ℝ := ![(1 / 96 : ℝ)]
noncomputable def TV : Fin 1 → ℝ := ![(5 / 32 : ℝ)]
def ZV : Fin 1 → ℤ := ![3]
noncomputable def HV : ℝ := (29 / 192 : ℝ)
noncomputable def EXs (c : Fin 1) : Finset (Fin 7 × ℤ) :=
  (Finset.univ ×ˢ Finset.Icc 0 (ZV c)).filter (fun q => ((q.2 : ℝ) + 1 / 8) / pr q.1 = aV c)
noncomputable def ENs (c : Fin 1) : Finset (Fin 7 × ℤ) :=
  (Finset.univ ×ˢ Finset.Icc 0 (ZV c)).filter (fun q => ((q.2 : ℝ) - 1 / 8) / pr q.1 = bV c)

theorem hp : ∀ i, 1 ≤ pr i ∧ pr i ≤ (8 : ℝ) := by intro i; fin_cases i <;> norm_num [pr]
theorem hp1 : ∀ i, 1 ≤ pr i := fun i => (hp i).1
theorem pr_0 : pr (0 : Fin 7) = (4 : ℝ) := rfl
theorem pr_1 : pr (1 : Fin 7) = (3 : ℝ) := rfl
theorem pr_2 : pr (2 : Fin 7) = (1 : ℝ) := rfl
theorem pr_3 : pr (3 : Fin 7) = (3 : ℝ) := rfl
theorem pr_4 : pr (4 : Fin 7) = (4 : ℝ) := rfl
theorem pr_5 : pr (5 : Fin 7) = (6 : ℝ) := rfl
theorem pr_6 : pr (6 : Fin 7) = (8 : ℝ) := rfl
theorem aV_0 : aV (0 : Fin 1) = (9 / 64 : ℝ) := rfl
theorem bV_0 : bV (0 : Fin 1) = (7 / 48 : ℝ) := rfl
theorem dV_0 : dV (0 : Fin 1) = (1 / 96 : ℝ) := rfl
theorem TV_0 : TV (0 : Fin 1) = (5 / 32 : ℝ) := rfl
theorem ZV_0 : ZV (0 : Fin 1) = (3 : ℤ) := rfl
theorem hab : ∀ c, aV c ≤ bV c := by intro c; fin_cases c <;> norm_num [aV, bV]
theorem hd0 : ∀ c, 0 < dV c := by intro c; fin_cases c <;> norm_num [dV]
theorem hdP : ∀ c, dV c ≤ 1 / (4 * (8 : ℝ)) := by intro c; fin_cases c <;> norm_num [dV]
theorem haP : ∀ c, dV c < aV c := by intro c; fin_cases c <;> norm_num [dV, aV]
theorem hT : ∀ c, bV c + dV c ≤ TV c := by intro c; fin_cases c <;> norm_num [bV, dV, TV]
theorem hZ : ∀ c, ((8 : ℝ) + 1) * TV c + 1 ≤ (ZV c : ℝ) := by intro c; fin_cases c <;> norm_num [TV, ZV]
theorem hE (ε : ℝ) (hε : ε ≤ (1 / 3072 : ℝ)) : ∀ c, 8 * ((ZV c : ℝ) + 1) * ε ≤ dV c := by
  intro c; fin_cases c <;> norm_num [ZV, dV] <;> linarith
theorem hcls : ∀ c i, ∀ z : ℤ, 0 ≤ z → z ≤ ZV c →
    ((z : ℝ) + 1 / 8) / pr i ≤ aV c - dV c ∨ bV c + dV c ≤ ((z : ℝ) - 1 / 8) / pr i ∨
      ((z : ℝ) + 1 / 8) / pr i = aV c ∨ ((z : ℝ) - 1 / 8) / pr i = bV c := by
  intro c i z h0 h1
  fin_cases c <;> fin_cases i <;> simp [ZV] at h1 <;> interval_cases z <;> norm_num [pr, aV, bV, dV]
theorem hEXne : ∀ c, (EXs c).Nonempty := by
  intro c
  fin_cases c
  · exact ⟨(6, 1), by simp [EXs, ZV, pr, aV] <;> norm_num⟩
theorem hENne : ∀ c, (ENs c).Nonempty := by
  intro c
  fin_cases c
  · exact ⟨(5, 1), by simp [ENs, ZV, pr, bV] <;> norm_num⟩
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
    (hHt : t ≤ HV) (h1 : (0 : ℝ) ≤ t) (h2 : t ≤ (13 / 96 : ℝ)) (hlon : ∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)) : False := by
  rcases le_total t (31 / 256 : ℝ) with hs0 | hs0
  · exact zone_kill_gen pr x ε HV (1 / 256 : ℝ) hp1 hdev hεH (by norm_num) (2 : Fin 7) 0 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (2 : Fin 7))
  exact zone_kill_gen pr x ε HV (1 / 256 : ℝ) hp1 hdev hεH (by norm_num) (6 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (6 : Fin 7))
theorem cov (x : Fin 7 → ℝ) (ε : ℝ) (hε : ε ≤ (1 / 3072 : ℝ)) (hdev : ∀ i, |x i - pr i| ≤ ε) :
    ∀ t : ℝ, 0 < t → t ≤ HV → (∀ c, ¬ (aV c - dV c / 2 ≤ t ∧ t ≤ bV c + dV c / 2)) →
      ¬ (∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)) := by
  intro t h0 hHt hnone hlon
  have hεH : ε * HV ≤ (1 / 256 : ℝ) / 2 := by
    have hε0 : 0 ≤ ε := le_trans (abs_nonneg _) (hdev 0)
    have : ε * HV ≤ (1 / 3072 : ℝ) * HV := mul_le_mul_of_nonneg_right hε (by norm_num [HV])
    have h2 : (1 / 3072 : ℝ) * HV ≤ (1 / 256 : ℝ) / 2 := by norm_num [HV]
    linarith
  have n0 := hnone (0 : Fin 1)
  rw [aV_0, bV_0, dV_0] at n0
  rcases lt_or_ge t (13 / 96 : ℝ) with c0 | c0
  · exact gap0 x ε hdev hεH t h0.le hHt h0.le (by linarith) hlon
  have d0 : (29 / 192 : ℝ) < t := by
    by_contra hc; push Not at hc; exact n0 ⟨by linarith, by linarith⟩
  have hHv : HV = (29 / 192 : ℝ) := rfl
  exact absurd (by linarith : t ≤ (29 / 192 : ℝ)) (not_le.2 d0)

theorem inst (x : Fin 7 → ℝ) (ε : ℝ) (hε : ε ≤ (1 / 3072 : ℝ)) (hdev : ∀ i, |x i - pr i| ≤ ε) :
    ∃ c₀ : Fin 1, Alive (mxOf x EXs hEXne) (mnOf x ENs hENne) c₀ ∧
      (∀ c, c < c₀ → ¬ Alive (mxOf x EXs hEXne) (mnOf x ENs hENne) c) ∧
      IsLeast {t : ℝ | 0 < t ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)} (mxOf x EXs hEXne c₀) :=
  landing_cert 1 (8 : ℝ) (by norm_num) pr x hp ε hdev aV bV dV TV ZV hab hd0 hdP haP hT hZ (hE ε hε) hcls EXs ENs hEXne hENne
    hEXdef hENdef hsepL HV hHL (cov x ε hε hdev) (0 : Fin 1) (by rw [dV_0, bV_0, aV_0]; norm_num)

noncomputable def sv : Fin 8 → ℝ := ![(1 : ℝ), (2 : ℝ), (4 : ℝ), (5 : ℝ), (8 : ℝ), (9 : ℝ), (11 : ℝ), (13 : ℝ)]
def sg : Fin 7 → Fin 8 := ![0, 1, 2, 4, 5, 6, 7]

theorem sv_0 : sv (0 : Fin 8) = (1 : ℝ) := rfl
theorem sv_1 : sv (1 : Fin 8) = (2 : ℝ) := rfl
theorem sv_2 : sv (2 : Fin 8) = (4 : ℝ) := rfl
theorem sv_3 : sv (3 : Fin 8) = (5 : ℝ) := rfl
theorem sv_4 : sv (4 : Fin 8) = (8 : ℝ) := rfl
theorem sv_5 : sv (5 : Fin 8) = (9 : ℝ) := rfl
theorem sv_6 : sv (6 : Fin 8) = (11 : ℝ) := rfl
theorem sv_7 : sv (7 : Fin 8) = (13 : ℝ) := rfl
theorem sg_0 : sg (0 : Fin 7) = (0 : Fin 8) := rfl
theorem sg_1 : sg (1 : Fin 7) = (1 : Fin 8) := rfl
theorem sg_2 : sg (2 : Fin 7) = (2 : Fin 8) := rfl
theorem sg_3 : sg (3 : Fin 7) = (4 : Fin 8) := rfl
theorem sg_4 : sg (4 : Fin 7) = (5 : Fin 8) := rfl
theorem sg_5 : sg (5 : Fin 7) = (6 : Fin 8) := rfl
theorem sg_6 : sg (6 : Fin 7) = (7 : Fin 8) := rfl

theorem inst_arr (v : Fin 8 → ℝ) (η : ℝ) (hη : η ≤ (1 / 6144 : ℝ)) (hv : ∀ j, |v j - sv j| ≤ η) :
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

end Fresh.CertRS.R06979



/-!
# Landing certificate `CertRS.R06980`: speeds (1, 2, 4, 5, 8, 9, 11, 13), subject index 4

Generated 2026-10-24 by `experiments/n8/cert_gen_v1.py` (exact Fractions).  Baseline readings [7, 6, 4, 3, 1, 3, 5].  Components up to the first wide one: 3.
Radius: speeds within `η ≤ 1/10752` of the baseline speeds, giving `ε = 2η ≤ 1/5376`.  Covering margin `μ = 1/512`.
`hcov` is **[PROVISIONAL: covering]**, supporting the claim that the first lonely instant of this subject is the largest exit of the first alive component.
Result `inst_arr`: for such `v`, the subject has a first isolation (a least element over all `t > 0`).  Grades: [L].
-/

open Classical

namespace Fresh.CertRS.R06980

open Fresh Fresh.LandingCert Fresh.LandingRule

noncomputable def pr : Fin 7 → ℝ := ![(7 : ℝ), (6 : ℝ), (4 : ℝ), (3 : ℝ), (1 : ℝ), (3 : ℝ), (5 : ℝ)]
noncomputable def aV : Fin 3 → ℝ := ![(1 / 8 : ℝ), (3 / 8 : ℝ), (25 / 56 : ℝ)]
noncomputable def bV : Fin 3 → ℝ := ![(1 / 8 : ℝ), (3 / 8 : ℝ), (15 / 32 : ℝ)]
noncomputable def dV : Fin 3 → ℝ := ![(1 / 48 : ℝ), (1 / 48 : ℝ), (1 / 96 : ℝ)]
noncomputable def TV : Fin 3 → ℝ := ![(7 / 48 : ℝ), (19 / 48 : ℝ), (23 / 48 : ℝ)]
def ZV : Fin 3 → ℤ := ![3, 5, 6]
noncomputable def HV : ℝ := (91 / 192 : ℝ)
noncomputable def EXs (c : Fin 3) : Finset (Fin 7 × ℤ) :=
  (Finset.univ ×ˢ Finset.Icc 0 (ZV c)).filter (fun q => ((q.2 : ℝ) + 1 / 8) / pr q.1 = aV c)
noncomputable def ENs (c : Fin 3) : Finset (Fin 7 × ℤ) :=
  (Finset.univ ×ˢ Finset.Icc 0 (ZV c)).filter (fun q => ((q.2 : ℝ) - 1 / 8) / pr q.1 = bV c)

theorem fcases (c : Fin 3) : c = 0 ∨ c = 1 ∨ c = 2 := by revert c; decide
theorem hp : ∀ i, 1 ≤ pr i ∧ pr i ≤ (7 : ℝ) := by intro i; fin_cases i <;> norm_num [pr]
theorem hp1 : ∀ i, 1 ≤ pr i := fun i => (hp i).1
theorem pr_0 : pr (0 : Fin 7) = (7 : ℝ) := rfl
theorem pr_1 : pr (1 : Fin 7) = (6 : ℝ) := rfl
theorem pr_2 : pr (2 : Fin 7) = (4 : ℝ) := rfl
theorem pr_3 : pr (3 : Fin 7) = (3 : ℝ) := rfl
theorem pr_4 : pr (4 : Fin 7) = (1 : ℝ) := rfl
theorem pr_5 : pr (5 : Fin 7) = (3 : ℝ) := rfl
theorem pr_6 : pr (6 : Fin 7) = (5 : ℝ) := rfl
theorem aV_0 : aV (0 : Fin 3) = (1 / 8 : ℝ) := rfl
theorem bV_0 : bV (0 : Fin 3) = (1 / 8 : ℝ) := rfl
theorem dV_0 : dV (0 : Fin 3) = (1 / 48 : ℝ) := rfl
theorem TV_0 : TV (0 : Fin 3) = (7 / 48 : ℝ) := rfl
theorem ZV_0 : ZV (0 : Fin 3) = (3 : ℤ) := rfl
theorem aV_1 : aV (1 : Fin 3) = (3 / 8 : ℝ) := rfl
theorem bV_1 : bV (1 : Fin 3) = (3 / 8 : ℝ) := rfl
theorem dV_1 : dV (1 : Fin 3) = (1 / 48 : ℝ) := rfl
theorem TV_1 : TV (1 : Fin 3) = (19 / 48 : ℝ) := rfl
theorem ZV_1 : ZV (1 : Fin 3) = (5 : ℤ) := rfl
theorem aV_2 : aV (2 : Fin 3) = (25 / 56 : ℝ) := rfl
theorem bV_2 : bV (2 : Fin 3) = (15 / 32 : ℝ) := rfl
theorem dV_2 : dV (2 : Fin 3) = (1 / 96 : ℝ) := rfl
theorem TV_2 : TV (2 : Fin 3) = (23 / 48 : ℝ) := rfl
theorem ZV_2 : ZV (2 : Fin 3) = (6 : ℤ) := rfl
theorem hab : ∀ c, aV c ≤ bV c := by intro c; rcases fcases c with rfl | rfl | rfl <;> norm_num [aV_0, bV_0, dV_0, TV_0, ZV_0, aV_1, bV_1, dV_1, TV_1, ZV_1, aV_2, bV_2, dV_2, TV_2, ZV_2]
theorem hd0 : ∀ c, 0 < dV c := by intro c; rcases fcases c with rfl | rfl | rfl <;> norm_num [aV_0, bV_0, dV_0, TV_0, ZV_0, aV_1, bV_1, dV_1, TV_1, ZV_1, aV_2, bV_2, dV_2, TV_2, ZV_2]
theorem hdP : ∀ c, dV c ≤ 1 / (4 * (7 : ℝ)) := by intro c; rcases fcases c with rfl | rfl | rfl <;> norm_num [aV_0, bV_0, dV_0, TV_0, ZV_0, aV_1, bV_1, dV_1, TV_1, ZV_1, aV_2, bV_2, dV_2, TV_2, ZV_2]
theorem haP : ∀ c, dV c < aV c := by intro c; rcases fcases c with rfl | rfl | rfl <;> norm_num [aV_0, bV_0, dV_0, TV_0, ZV_0, aV_1, bV_1, dV_1, TV_1, ZV_1, aV_2, bV_2, dV_2, TV_2, ZV_2]
theorem hT : ∀ c, bV c + dV c ≤ TV c := by intro c; rcases fcases c with rfl | rfl | rfl <;> norm_num [aV_0, bV_0, dV_0, TV_0, ZV_0, aV_1, bV_1, dV_1, TV_1, ZV_1, aV_2, bV_2, dV_2, TV_2, ZV_2]
theorem hZ : ∀ c, ((7 : ℝ) + 1) * TV c + 1 ≤ (ZV c : ℝ) := by intro c; rcases fcases c with rfl | rfl | rfl <;> norm_num [aV_0, bV_0, dV_0, TV_0, ZV_0, aV_1, bV_1, dV_1, TV_1, ZV_1, aV_2, bV_2, dV_2, TV_2, ZV_2]
theorem hE (ε : ℝ) (hε : ε ≤ (1 / 5376 : ℝ)) : ∀ c, 8 * ((ZV c : ℝ) + 1) * ε ≤ dV c := by
  intro c; rcases fcases c with rfl | rfl | rfl <;> norm_num [aV_0, bV_0, dV_0, TV_0, ZV_0, aV_1, bV_1, dV_1, TV_1, ZV_1, aV_2, bV_2, dV_2, TV_2, ZV_2] <;> linarith
set_option maxHeartbeats 4000000 in
theorem hcls : ∀ c i, ∀ z : ℤ, 0 ≤ z → z ≤ ZV c →
    ((z : ℝ) + 1 / 8) / pr i ≤ aV c - dV c ∨ bV c + dV c ≤ ((z : ℝ) - 1 / 8) / pr i ∨
      ((z : ℝ) + 1 / 8) / pr i = aV c ∨ ((z : ℝ) - 1 / 8) / pr i = bV c := by
  intro c i z h0 h1
  rcases fcases c with rfl | rfl | rfl <;> rcases fin7_cases i with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [aV_0, bV_0, dV_0, TV_0, ZV_0, aV_1, bV_1, dV_1, TV_1, ZV_1, aV_2, bV_2, dV_2, TV_2, ZV_2] at h1 <;> interval_cases z <;> norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6, aV_0, bV_0, dV_0, TV_0, ZV_0, aV_1, bV_1, dV_1, TV_1, ZV_1, aV_2, bV_2, dV_2, TV_2, ZV_2]
theorem hEXne : ∀ c, (EXs c).Nonempty := by
  intro c
  rcases fcases c with rfl | rfl | rfl
  · exact ⟨(4, 0), by simp [EXs, ZV, pr, aV] <;> norm_num⟩
  · exact ⟨(3, 1), by simp [EXs, ZV, pr, aV] <;> norm_num⟩
  · exact ⟨(0, 3), by simp [EXs, ZV, pr, aV] <;> norm_num⟩
theorem hENne : ∀ c, (ENs c).Nonempty := by
  intro c
  rcases fcases c with rfl | rfl | rfl
  · exact ⟨(0, 1), by simp [ENs, ZV, pr, bV] <;> norm_num⟩
  · exact ⟨(6, 2), by simp [ENs, ZV, pr, bV] <;> norm_num⟩
  · exact ⟨(2, 2), by simp [ENs, ZV, pr, bV] <;> norm_num⟩
theorem hEXdef : ∀ c, ∀ q : Fin 7 × ℤ, q ∈ EXs c ↔ 0 ≤ q.2 ∧ q.2 ≤ ZV c ∧ ((q.2 : ℝ) + 1 / 8) / pr q.1 = aV c := by
  intro c q
  simp only [EXs, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, Finset.mem_Icc, true_and]
  tauto
theorem hENdef : ∀ c, ∀ q : Fin 7 × ℤ, q ∈ ENs c ↔ 0 ≤ q.2 ∧ q.2 ≤ ZV c ∧ ((q.2 : ℝ) - 1 / 8) / pr q.1 = bV c := by
  intro c q
  simp only [ENs, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, Finset.mem_Icc, true_and]
  tauto
theorem hsepL : ∀ c c' : Fin 3, c < c' → bV c + dV c / 2 < aV c' - dV c' / 2 := by
  intro c c' h
  rcases fcases c with rfl | rfl | rfl <;> rcases fcases c' with rfl | rfl | rfl <;> simp at h ⊢ <;> norm_num [aV_0, bV_0, dV_0, TV_0, ZV_0, aV_1, bV_1, dV_1, TV_1, ZV_1, aV_2, bV_2, dV_2, TV_2, ZV_2]
theorem hHL : ∀ c, bV c + dV c / 2 ≤ HV := by intro c; rcases fcases c with rfl | rfl | rfl <;> norm_num [aV_0, bV_0, dV_0, TV_0, ZV_0, aV_1, bV_1, dV_1, TV_1, ZV_1, aV_2, bV_2, dV_2, TV_2, ZV_2, HV]

theorem gap0 (x : Fin 7 → ℝ) (ε : ℝ) (hdev : ∀ i, |x i - pr i| ≤ ε) (hεH : ε * HV ≤ (1 / 512 : ℝ) / 2) (t : ℝ) (h0 : 0 ≤ t)
    (hHt : t ≤ HV) (h1 : (0 : ℝ) ≤ t) (h2 : t ≤ (11 / 96 : ℝ)) (hlon : ∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)) : False := by
  exact zone_kill_gen pr x ε HV (1 / 512 : ℝ) hp1 hdev hεH (by norm_num) (4 : Fin 7) 0 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (4 : Fin 7))
theorem gap1 (x : Fin 7 → ℝ) (ε : ℝ) (hdev : ∀ i, |x i - pr i| ≤ ε) (hεH : ε * HV ≤ (1 / 512 : ℝ) / 2) (t : ℝ) (h0 : 0 ≤ t)
    (hHt : t ≤ HV) (h1 : (13 / 96 : ℝ) ≤ t) (h2 : t ≤ (35 / 96 : ℝ)) (hlon : ∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)) : False := by
  rcases le_total t (569 / 3584 : ℝ) with hs0 | hs0
  · exact zone_kill_gen pr x ε HV (1 / 512 : ℝ) hp1 hdev hεH (by norm_num) (0 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (0 : Fin 7))
  rcases le_total t (95 / 512 : ℝ) with hs1 | hs1
  · exact zone_kill_gen pr x ε HV (1 / 512 : ℝ) hp1 hdev hεH (by norm_num) (1 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (1 : Fin 7))
  rcases le_total t (571 / 2560 : ℝ) with hs2 | hs2
  · exact zone_kill_gen pr x ε HV (1 / 512 : ℝ) hp1 hdev hεH (by norm_num) (6 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (6 : Fin 7))
  rcases le_total t (143 / 512 : ℝ) with hs3 | hs3
  · exact zone_kill_gen pr x ε HV (1 / 512 : ℝ) hp1 hdev hεH (by norm_num) (2 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (2 : Fin 7))
  rcases le_total t (1081 / 3584 : ℝ) with hs4 | hs4
  · exact zone_kill_gen pr x ε HV (1 / 512 : ℝ) hp1 hdev hεH (by norm_num) (0 : Fin 7) 2 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (0 : Fin 7))
  exact zone_kill_gen pr x ε HV (1 / 512 : ℝ) hp1 hdev hεH (by norm_num) (3 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (3 : Fin 7))
theorem gap2 (x : Fin 7 → ℝ) (ε : ℝ) (hdev : ∀ i, |x i - pr i| ≤ ε) (hεH : ε * HV ≤ (1 / 512 : ℝ) / 2) (t : ℝ) (h0 : 0 ≤ t)
    (hHt : t ≤ HV) (h1 : (37 / 96 : ℝ) ≤ t) (h2 : t ≤ (593 / 1344 : ℝ)) (hlon : ∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)) : False := by
  rcases le_total t (1083 / 2560 : ℝ) with hs0 | hs0
  · exact zone_kill_gen pr x ε HV (1 / 512 : ℝ) hp1 hdev hεH (by norm_num) (6 : Fin 7) 2 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (6 : Fin 7))
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
  have n0 := hnone (0 : Fin 3)
  rw [aV_0, bV_0, dV_0] at n0
  have n1 := hnone (1 : Fin 3)
  rw [aV_1, bV_1, dV_1] at n1
  have n2 := hnone (2 : Fin 3)
  rw [aV_2, bV_2, dV_2] at n2
  rcases lt_or_ge t (11 / 96 : ℝ) with c0 | c0
  · exact gap0 x ε hdev hεH t h0.le hHt h0.le (by linarith) hlon
  have d0 : (13 / 96 : ℝ) < t := by
    by_contra hc; push Not at hc; exact n0 ⟨by linarith, by linarith⟩
  rcases lt_or_ge t (35 / 96 : ℝ) with c1 | c1
  · exact gap1 x ε hdev hεH t h0.le hHt d0.le (by linarith) hlon
  have d1 : (37 / 96 : ℝ) < t := by
    by_contra hc; push Not at hc; exact n1 ⟨by linarith, by linarith⟩
  rcases lt_or_ge t (593 / 1344 : ℝ) with c2 | c2
  · exact gap2 x ε hdev hεH t h0.le hHt d1.le (by linarith) hlon
  have d2 : (91 / 192 : ℝ) < t := by
    by_contra hc; push Not at hc; exact n2 ⟨by linarith, by linarith⟩
  have hHv : HV = (91 / 192 : ℝ) := rfl
  exact absurd (by linarith : t ≤ (91 / 192 : ℝ)) (not_le.2 d2)

theorem inst (x : Fin 7 → ℝ) (ε : ℝ) (hε : ε ≤ (1 / 5376 : ℝ)) (hdev : ∀ i, |x i - pr i| ≤ ε) :
    ∃ c₀ : Fin 3, Alive (mxOf x EXs hEXne) (mnOf x ENs hENne) c₀ ∧
      (∀ c, c < c₀ → ¬ Alive (mxOf x EXs hEXne) (mnOf x ENs hENne) c) ∧
      IsLeast {t : ℝ | 0 < t ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)} (mxOf x EXs hEXne c₀) :=
  landing_cert 3 (7 : ℝ) (by norm_num) pr x hp ε hdev aV bV dV TV ZV hab hd0 hdP haP hT hZ (hE ε hε) hcls EXs ENs hEXne hENne
    hEXdef hENdef hsepL HV hHL (cov x ε hε hdev) (2 : Fin 3) (by rw [dV_2, bV_2, aV_2]; norm_num)

noncomputable def sv : Fin 8 → ℝ := ![(1 : ℝ), (2 : ℝ), (4 : ℝ), (5 : ℝ), (8 : ℝ), (9 : ℝ), (11 : ℝ), (13 : ℝ)]
def sg : Fin 7 → Fin 8 := ![0, 1, 2, 3, 5, 6, 7]

theorem sv_0 : sv (0 : Fin 8) = (1 : ℝ) := rfl
theorem sv_1 : sv (1 : Fin 8) = (2 : ℝ) := rfl
theorem sv_2 : sv (2 : Fin 8) = (4 : ℝ) := rfl
theorem sv_3 : sv (3 : Fin 8) = (5 : ℝ) := rfl
theorem sv_4 : sv (4 : Fin 8) = (8 : ℝ) := rfl
theorem sv_5 : sv (5 : Fin 8) = (9 : ℝ) := rfl
theorem sv_6 : sv (6 : Fin 8) = (11 : ℝ) := rfl
theorem sv_7 : sv (7 : Fin 8) = (13 : ℝ) := rfl
theorem sg_0 : sg (0 : Fin 7) = (0 : Fin 8) := rfl
theorem sg_1 : sg (1 : Fin 7) = (1 : Fin 8) := rfl
theorem sg_2 : sg (2 : Fin 7) = (2 : Fin 8) := rfl
theorem sg_3 : sg (3 : Fin 7) = (3 : Fin 8) := rfl
theorem sg_4 : sg (4 : Fin 7) = (5 : Fin 8) := rfl
theorem sg_5 : sg (5 : Fin 7) = (6 : Fin 8) := rfl
theorem sg_6 : sg (6 : Fin 7) = (7 : Fin 8) := rfl

theorem inst_arr (v : Fin 8 → ℝ) (η : ℝ) (hη : η ≤ (1 / 10752 : ℝ)) (hv : ∀ j, |v j - sv j| ≤ η) :
    ∃ c₀ : Fin 3, Alive (mxOf (fun i => |v (sg i) - v (4 : Fin 8)|) EXs hEXne) (mnOf (fun i => |v (sg i) - v (4 : Fin 8)|) ENs hENne) c₀ ∧
      (∀ c, c < c₀ → ¬ Alive (mxOf (fun i => |v (sg i) - v (4 : Fin 8)|) EXs hEXne) (mnOf (fun i => |v (sg i) - v (4 : Fin 8)|) ENs hENne) c) ∧
      IsLeast {t : ℝ | 0 < t ∧ IsolatedAt v (4 : Fin 8) t} (mxOf (fun i => |v (sg i) - v (4 : Fin 8)|) EXs hEXne c₀) := by
  have hσk : ∀ i, sg i ≠ (4 : Fin 8) := by decide
  have hσ : ∀ j : Fin 8, j ≠ (4 : Fin 8) → ∃ i, sg i = j := by decide
  have hpr : ∀ i, pr i = |sv (sg i) - sv (4 : Fin 8)| := by
    intro i; rcases fin7_cases i with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6, sv_0, sv_1, sv_2, sv_3, sv_4, sv_5, sv_6, sv_7, sg_0, sg_1, sg_2, sg_3, sg_4, sg_5, sg_6]
  have hdev : ∀ i, |(|v (sg i) - v (4 : Fin 8)| - pr i)| ≤ 2 * η := by
    intro i; rw [hpr i]; exact reading_dev v sv η hv (sg i) (4 : Fin 8)
  obtain ⟨c₀, hal, hbf, hT0⟩ := inst (fun i => |v (sg i) - v (4 : Fin 8)|) (2 * η) (by linarith) hdev
  have hset : {t : ℝ | 0 < t ∧ IsolatedAt v (4 : Fin 8) t} =
      {t : ℝ | 0 < t ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (|v (sg i) - v (4 : Fin 8)| * t)} := by
    ext t; simp only [Set.mem_setOf_eq]; rw [iso_iff_readings v (4 : Fin 8) sg hσk hσ t]
  rw [hset]; exact ⟨c₀, hal, hbf, hT0⟩

#print axioms inst_arr

end Fresh.CertRS.R06980



/-!
# Landing certificate `CertRS.R06981`: speeds (1, 2, 4, 5, 8, 9, 11, 13), subject index 5

Generated 2026-10-24 by `experiments/n8/cert_gen_v1.py` (exact Fractions).  Baseline readings [8, 7, 5, 4, 1, 2, 4].  Components up to the first wide one: 1.
Radius: speeds within `η ≤ 1/3186` of the baseline speeds, giving `ε = 2η ≤ 1/1593`.  Covering margin `μ = 1/128`.
`hcov` is **[PROVISIONAL: covering]**, supporting the claim that the first lonely instant of this subject is the largest exit of the first alive component.
Result `inst_arr`: for such `v`, the subject has a first isolation (a least element over all `t > 0`).  Grades: [L].
-/

open Classical

namespace Fresh.CertRS.R06981

open Fresh Fresh.LandingCert Fresh.LandingRule

noncomputable def pr : Fin 7 → ℝ := ![(8 : ℝ), (7 : ℝ), (5 : ℝ), (4 : ℝ), (1 : ℝ), (2 : ℝ), (4 : ℝ)]
noncomputable def aV : Fin 1 → ℝ := ![(9 / 56 : ℝ)]
noncomputable def bV : Fin 1 → ℝ := ![(7 / 40 : ℝ)]
noncomputable def dV : Fin 1 → ℝ := ![(9 / 448 : ℝ)]
noncomputable def TV : Fin 1 → ℝ := ![(437 / 2240 : ℝ)]
def ZV : Fin 1 → ℤ := ![3]
noncomputable def HV : ℝ := (829 / 4480 : ℝ)
noncomputable def EXs (c : Fin 1) : Finset (Fin 7 × ℤ) :=
  (Finset.univ ×ˢ Finset.Icc 0 (ZV c)).filter (fun q => ((q.2 : ℝ) + 1 / 8) / pr q.1 = aV c)
noncomputable def ENs (c : Fin 1) : Finset (Fin 7 × ℤ) :=
  (Finset.univ ×ˢ Finset.Icc 0 (ZV c)).filter (fun q => ((q.2 : ℝ) - 1 / 8) / pr q.1 = bV c)

theorem hp : ∀ i, 1 ≤ pr i ∧ pr i ≤ (8 : ℝ) := by intro i; fin_cases i <;> norm_num [pr]
theorem hp1 : ∀ i, 1 ≤ pr i := fun i => (hp i).1
theorem pr_0 : pr (0 : Fin 7) = (8 : ℝ) := rfl
theorem pr_1 : pr (1 : Fin 7) = (7 : ℝ) := rfl
theorem pr_2 : pr (2 : Fin 7) = (5 : ℝ) := rfl
theorem pr_3 : pr (3 : Fin 7) = (4 : ℝ) := rfl
theorem pr_4 : pr (4 : Fin 7) = (1 : ℝ) := rfl
theorem pr_5 : pr (5 : Fin 7) = (2 : ℝ) := rfl
theorem pr_6 : pr (6 : Fin 7) = (4 : ℝ) := rfl
theorem aV_0 : aV (0 : Fin 1) = (9 / 56 : ℝ) := rfl
theorem bV_0 : bV (0 : Fin 1) = (7 / 40 : ℝ) := rfl
theorem dV_0 : dV (0 : Fin 1) = (9 / 448 : ℝ) := rfl
theorem TV_0 : TV (0 : Fin 1) = (437 / 2240 : ℝ) := rfl
theorem ZV_0 : ZV (0 : Fin 1) = (3 : ℤ) := rfl
theorem hab : ∀ c, aV c ≤ bV c := by intro c; fin_cases c <;> norm_num [aV, bV]
theorem hd0 : ∀ c, 0 < dV c := by intro c; fin_cases c <;> norm_num [dV]
theorem hdP : ∀ c, dV c ≤ 1 / (4 * (8 : ℝ)) := by intro c; fin_cases c <;> norm_num [dV]
theorem haP : ∀ c, dV c < aV c := by intro c; fin_cases c <;> norm_num [dV, aV]
theorem hT : ∀ c, bV c + dV c ≤ TV c := by intro c; fin_cases c <;> norm_num [bV, dV, TV]
theorem hZ : ∀ c, ((8 : ℝ) + 1) * TV c + 1 ≤ (ZV c : ℝ) := by intro c; fin_cases c <;> norm_num [TV, ZV]
theorem hE (ε : ℝ) (hε : ε ≤ (1 / 1593 : ℝ)) : ∀ c, 8 * ((ZV c : ℝ) + 1) * ε ≤ dV c := by
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

theorem gap0 (x : Fin 7 → ℝ) (ε : ℝ) (hdev : ∀ i, |x i - pr i| ≤ ε) (hεH : ε * HV ≤ (1 / 128 : ℝ) / 2) (t : ℝ) (h0 : 0 ≤ t)
    (hHt : t ≤ HV) (h1 : (0 : ℝ) ≤ t) (h2 : t ≤ (135 / 896 : ℝ)) (hlon : ∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)) : False := by
  rcases le_total t (15 / 128 : ℝ) with hs0 | hs0
  · exact zone_kill_gen pr x ε HV (1 / 128 : ℝ) hp1 hdev hεH (by norm_num) (4 : Fin 7) 0 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (4 : Fin 7))
  rcases le_total t (17 / 128 : ℝ) with hs1 | hs1
  · exact zone_kill_gen pr x ε HV (1 / 128 : ℝ) hp1 hdev hεH (by norm_num) (0 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (0 : Fin 7))
  exact zone_kill_gen pr x ε HV (1 / 128 : ℝ) hp1 hdev hεH (by norm_num) (1 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (1 : Fin 7))
theorem cov (x : Fin 7 → ℝ) (ε : ℝ) (hε : ε ≤ (1 / 1593 : ℝ)) (hdev : ∀ i, |x i - pr i| ≤ ε) :
    ∀ t : ℝ, 0 < t → t ≤ HV → (∀ c, ¬ (aV c - dV c / 2 ≤ t ∧ t ≤ bV c + dV c / 2)) →
      ¬ (∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)) := by
  intro t h0 hHt hnone hlon
  have hεH : ε * HV ≤ (1 / 128 : ℝ) / 2 := by
    have hε0 : 0 ≤ ε := le_trans (abs_nonneg _) (hdev 0)
    have : ε * HV ≤ (1 / 1593 : ℝ) * HV := mul_le_mul_of_nonneg_right hε (by norm_num [HV])
    have h2 : (1 / 1593 : ℝ) * HV ≤ (1 / 128 : ℝ) / 2 := by norm_num [HV]
    linarith
  have n0 := hnone (0 : Fin 1)
  rw [aV_0, bV_0, dV_0] at n0
  rcases lt_or_ge t (135 / 896 : ℝ) with c0 | c0
  · exact gap0 x ε hdev hεH t h0.le hHt h0.le (by linarith) hlon
  have d0 : (829 / 4480 : ℝ) < t := by
    by_contra hc; push Not at hc; exact n0 ⟨by linarith, by linarith⟩
  have hHv : HV = (829 / 4480 : ℝ) := rfl
  exact absurd (by linarith : t ≤ (829 / 4480 : ℝ)) (not_le.2 d0)

theorem inst (x : Fin 7 → ℝ) (ε : ℝ) (hε : ε ≤ (1 / 1593 : ℝ)) (hdev : ∀ i, |x i - pr i| ≤ ε) :
    ∃ c₀ : Fin 1, Alive (mxOf x EXs hEXne) (mnOf x ENs hENne) c₀ ∧
      (∀ c, c < c₀ → ¬ Alive (mxOf x EXs hEXne) (mnOf x ENs hENne) c) ∧
      IsLeast {t : ℝ | 0 < t ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)} (mxOf x EXs hEXne c₀) :=
  landing_cert 1 (8 : ℝ) (by norm_num) pr x hp ε hdev aV bV dV TV ZV hab hd0 hdP haP hT hZ (hE ε hε) hcls EXs ENs hEXne hENne
    hEXdef hENdef hsepL HV hHL (cov x ε hε hdev) (0 : Fin 1) (by rw [dV_0, bV_0, aV_0]; norm_num)

noncomputable def sv : Fin 8 → ℝ := ![(1 : ℝ), (2 : ℝ), (4 : ℝ), (5 : ℝ), (8 : ℝ), (9 : ℝ), (11 : ℝ), (13 : ℝ)]
def sg : Fin 7 → Fin 8 := ![0, 1, 2, 3, 4, 6, 7]

theorem sv_0 : sv (0 : Fin 8) = (1 : ℝ) := rfl
theorem sv_1 : sv (1 : Fin 8) = (2 : ℝ) := rfl
theorem sv_2 : sv (2 : Fin 8) = (4 : ℝ) := rfl
theorem sv_3 : sv (3 : Fin 8) = (5 : ℝ) := rfl
theorem sv_4 : sv (4 : Fin 8) = (8 : ℝ) := rfl
theorem sv_5 : sv (5 : Fin 8) = (9 : ℝ) := rfl
theorem sv_6 : sv (6 : Fin 8) = (11 : ℝ) := rfl
theorem sv_7 : sv (7 : Fin 8) = (13 : ℝ) := rfl
theorem sg_0 : sg (0 : Fin 7) = (0 : Fin 8) := rfl
theorem sg_1 : sg (1 : Fin 7) = (1 : Fin 8) := rfl
theorem sg_2 : sg (2 : Fin 7) = (2 : Fin 8) := rfl
theorem sg_3 : sg (3 : Fin 7) = (3 : Fin 8) := rfl
theorem sg_4 : sg (4 : Fin 7) = (4 : Fin 8) := rfl
theorem sg_5 : sg (5 : Fin 7) = (6 : Fin 8) := rfl
theorem sg_6 : sg (6 : Fin 7) = (7 : Fin 8) := rfl

theorem inst_arr (v : Fin 8 → ℝ) (η : ℝ) (hη : η ≤ (1 / 3186 : ℝ)) (hv : ∀ j, |v j - sv j| ≤ η) :
    ∃ c₀ : Fin 1, Alive (mxOf (fun i => |v (sg i) - v (5 : Fin 8)|) EXs hEXne) (mnOf (fun i => |v (sg i) - v (5 : Fin 8)|) ENs hENne) c₀ ∧
      (∀ c, c < c₀ → ¬ Alive (mxOf (fun i => |v (sg i) - v (5 : Fin 8)|) EXs hEXne) (mnOf (fun i => |v (sg i) - v (5 : Fin 8)|) ENs hENne) c) ∧
      IsLeast {t : ℝ | 0 < t ∧ IsolatedAt v (5 : Fin 8) t} (mxOf (fun i => |v (sg i) - v (5 : Fin 8)|) EXs hEXne c₀) := by
  have hσk : ∀ i, sg i ≠ (5 : Fin 8) := by decide
  have hσ : ∀ j : Fin 8, j ≠ (5 : Fin 8) → ∃ i, sg i = j := by decide
  have hpr : ∀ i, pr i = |sv (sg i) - sv (5 : Fin 8)| := by
    intro i; rcases fin7_cases i with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6, sv_0, sv_1, sv_2, sv_3, sv_4, sv_5, sv_6, sv_7, sg_0, sg_1, sg_2, sg_3, sg_4, sg_5, sg_6]
  have hdev : ∀ i, |(|v (sg i) - v (5 : Fin 8)| - pr i)| ≤ 2 * η := by
    intro i; rw [hpr i]; exact reading_dev v sv η hv (sg i) (5 : Fin 8)
  obtain ⟨c₀, hal, hbf, hT0⟩ := inst (fun i => |v (sg i) - v (5 : Fin 8)|) (2 * η) (by linarith) hdev
  have hset : {t : ℝ | 0 < t ∧ IsolatedAt v (5 : Fin 8) t} =
      {t : ℝ | 0 < t ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (|v (sg i) - v (5 : Fin 8)| * t)} := by
    ext t; simp only [Set.mem_setOf_eq]; rw [iso_iff_readings v (5 : Fin 8) sg hσk hσ t]
  rw [hset]; exact ⟨c₀, hal, hbf, hT0⟩

#print axioms inst_arr

end Fresh.CertRS.R06981



/-!
# Landing certificate `CertRS.R06982`: speeds (1, 2, 4, 5, 8, 9, 11, 13), subject index 6

Generated 2026-10-24 by `experiments/n8/cert_gen_v1.py` (exact Fractions).  Baseline readings [10, 9, 7, 6, 3, 2, 2].  Components up to the first wide one: 1.
Radius: speeds within `η ≤ 1/6584` of the baseline speeds, giving `ε = 2η ≤ 1/3292`.  Covering margin `μ = 1/256`.
`hcov` is **[PROVISIONAL: covering]**, supporting the claim that the first lonely instant of this subject is the largest exit of the first alive component.
Result `inst_arr`: for such `v`, the subject has a first isolation (a least element over all `t > 0`).  Grades: [L].
-/

open Classical

namespace Fresh.CertRS.R06982

open Fresh Fresh.LandingCert Fresh.LandingRule

noncomputable def pr : Fin 7 → ℝ := ![(10 : ℝ), (9 : ℝ), (7 : ℝ), (6 : ℝ), (3 : ℝ), (2 : ℝ), (2 : ℝ)]
noncomputable def aV : Fin 1 → ℝ := ![(1 / 16 : ℝ)]
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
theorem pr_0 : pr (0 : Fin 7) = (10 : ℝ) := rfl
theorem pr_1 : pr (1 : Fin 7) = (9 : ℝ) := rfl
theorem pr_2 : pr (2 : Fin 7) = (7 : ℝ) := rfl
theorem pr_3 : pr (3 : Fin 7) = (6 : ℝ) := rfl
theorem pr_4 : pr (4 : Fin 7) = (3 : ℝ) := rfl
theorem pr_5 : pr (5 : Fin 7) = (2 : ℝ) := rfl
theorem pr_6 : pr (6 : Fin 7) = (2 : ℝ) := rfl
theorem aV_0 : aV (0 : Fin 1) = (1 / 16 : ℝ) := rfl
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
  · exact ⟨(5, 0), by simp [EXs, ZV, pr, aV] <;> norm_num⟩
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

theorem gap0 (x : Fin 7 → ℝ) (ε : ℝ) (hdev : ∀ i, |x i - pr i| ≤ ε) (hεH : ε * HV ≤ (1 / 256 : ℝ) / 2) (t : ℝ) (h0 : 0 ≤ t)
    (hHt : t ≤ HV) (h1 : (0 : ℝ) ≤ t) (h2 : t ≤ (83 / 1440 : ℝ)) (hlon : ∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)) : False := by
  exact zone_kill_gen pr x ε HV (1 / 256 : ℝ) hp1 hdev hεH (by norm_num) (5 : Fin 7) 0 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (5 : Fin 7))
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
  rcases lt_or_ge t (83 / 1440 : ℝ) with c0 | c0
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

noncomputable def sv : Fin 8 → ℝ := ![(1 : ℝ), (2 : ℝ), (4 : ℝ), (5 : ℝ), (8 : ℝ), (9 : ℝ), (11 : ℝ), (13 : ℝ)]
def sg : Fin 7 → Fin 8 := ![0, 1, 2, 3, 4, 5, 7]

theorem sv_0 : sv (0 : Fin 8) = (1 : ℝ) := rfl
theorem sv_1 : sv (1 : Fin 8) = (2 : ℝ) := rfl
theorem sv_2 : sv (2 : Fin 8) = (4 : ℝ) := rfl
theorem sv_3 : sv (3 : Fin 8) = (5 : ℝ) := rfl
theorem sv_4 : sv (4 : Fin 8) = (8 : ℝ) := rfl
theorem sv_5 : sv (5 : Fin 8) = (9 : ℝ) := rfl
theorem sv_6 : sv (6 : Fin 8) = (11 : ℝ) := rfl
theorem sv_7 : sv (7 : Fin 8) = (13 : ℝ) := rfl
theorem sg_0 : sg (0 : Fin 7) = (0 : Fin 8) := rfl
theorem sg_1 : sg (1 : Fin 7) = (1 : Fin 8) := rfl
theorem sg_2 : sg (2 : Fin 7) = (2 : Fin 8) := rfl
theorem sg_3 : sg (3 : Fin 7) = (3 : Fin 8) := rfl
theorem sg_4 : sg (4 : Fin 7) = (4 : Fin 8) := rfl
theorem sg_5 : sg (5 : Fin 7) = (5 : Fin 8) := rfl
theorem sg_6 : sg (6 : Fin 7) = (7 : Fin 8) := rfl

theorem inst_arr (v : Fin 8 → ℝ) (η : ℝ) (hη : η ≤ (1 / 6584 : ℝ)) (hv : ∀ j, |v j - sv j| ≤ η) :
    ∃ c₀ : Fin 1, Alive (mxOf (fun i => |v (sg i) - v (6 : Fin 8)|) EXs hEXne) (mnOf (fun i => |v (sg i) - v (6 : Fin 8)|) ENs hENne) c₀ ∧
      (∀ c, c < c₀ → ¬ Alive (mxOf (fun i => |v (sg i) - v (6 : Fin 8)|) EXs hEXne) (mnOf (fun i => |v (sg i) - v (6 : Fin 8)|) ENs hENne) c) ∧
      IsLeast {t : ℝ | 0 < t ∧ IsolatedAt v (6 : Fin 8) t} (mxOf (fun i => |v (sg i) - v (6 : Fin 8)|) EXs hEXne c₀) := by
  have hσk : ∀ i, sg i ≠ (6 : Fin 8) := by decide
  have hσ : ∀ j : Fin 8, j ≠ (6 : Fin 8) → ∃ i, sg i = j := by decide
  have hpr : ∀ i, pr i = |sv (sg i) - sv (6 : Fin 8)| := by
    intro i; rcases fin7_cases i with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6, sv_0, sv_1, sv_2, sv_3, sv_4, sv_5, sv_6, sv_7, sg_0, sg_1, sg_2, sg_3, sg_4, sg_5, sg_6]
  have hdev : ∀ i, |(|v (sg i) - v (6 : Fin 8)| - pr i)| ≤ 2 * η := by
    intro i; rw [hpr i]; exact reading_dev v sv η hv (sg i) (6 : Fin 8)
  obtain ⟨c₀, hal, hbf, hT0⟩ := inst (fun i => |v (sg i) - v (6 : Fin 8)|) (2 * η) (by linarith) hdev
  have hset : {t : ℝ | 0 < t ∧ IsolatedAt v (6 : Fin 8) t} =
      {t : ℝ | 0 < t ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (|v (sg i) - v (6 : Fin 8)| * t)} := by
    ext t; simp only [Set.mem_setOf_eq]; rw [iso_iff_readings v (6 : Fin 8) sg hσk hσ t]
  rw [hset]; exact ⟨c₀, hal, hbf, hT0⟩

#print axioms inst_arr

end Fresh.CertRS.R06982



/-!
# Landing certificate `CertRS.R06983`: speeds (1, 2, 4, 5, 8, 9, 11, 13), subject index 7

Generated 2026-10-24 by `experiments/n8/cert_gen_v1.py` (exact Fractions).  Baseline readings [12, 11, 9, 8, 5, 4, 2].  Components up to the first wide one: 1.
Radius: speeds within `η ≤ 1/9656` of the baseline speeds, giving `ε = 2η ≤ 1/4828`.  Covering margin `μ = 1/512`.
`hcov` is **[PROVISIONAL: covering]**, supporting the claim that the first lonely instant of this subject is the largest exit of the first alive component.
Result `inst_arr`: for such `v`, the subject has a first isolation (a least element over all `t > 0`).  Grades: [L].
-/

open Classical

namespace Fresh.CertRS.R06983

open Fresh Fresh.LandingCert Fresh.LandingRule

noncomputable def pr : Fin 7 → ℝ := ![(12 : ℝ), (11 : ℝ), (9 : ℝ), (8 : ℝ), (5 : ℝ), (4 : ℝ), (2 : ℝ)]
noncomputable def aV : Fin 1 → ℝ := ![(1 / 16 : ℝ)]
noncomputable def bV : Fin 1 → ℝ := ![(7 / 96 : ℝ)]
noncomputable def dV : Fin 1 → ℝ := ![(7 / 1056 : ℝ)]
noncomputable def TV : Fin 1 → ℝ := ![(7 / 88 : ℝ)]
def ZV : Fin 1 → ℤ := ![3]
noncomputable def HV : ℝ := (161 / 2112 : ℝ)
noncomputable def EXs (c : Fin 1) : Finset (Fin 7 × ℤ) :=
  (Finset.univ ×ˢ Finset.Icc 0 (ZV c)).filter (fun q => ((q.2 : ℝ) + 1 / 8) / pr q.1 = aV c)
noncomputable def ENs (c : Fin 1) : Finset (Fin 7 × ℤ) :=
  (Finset.univ ×ˢ Finset.Icc 0 (ZV c)).filter (fun q => ((q.2 : ℝ) - 1 / 8) / pr q.1 = bV c)

theorem hp : ∀ i, 1 ≤ pr i ∧ pr i ≤ (12 : ℝ) := by intro i; fin_cases i <;> norm_num [pr]
theorem hp1 : ∀ i, 1 ≤ pr i := fun i => (hp i).1
theorem pr_0 : pr (0 : Fin 7) = (12 : ℝ) := rfl
theorem pr_1 : pr (1 : Fin 7) = (11 : ℝ) := rfl
theorem pr_2 : pr (2 : Fin 7) = (9 : ℝ) := rfl
theorem pr_3 : pr (3 : Fin 7) = (8 : ℝ) := rfl
theorem pr_4 : pr (4 : Fin 7) = (5 : ℝ) := rfl
theorem pr_5 : pr (5 : Fin 7) = (4 : ℝ) := rfl
theorem pr_6 : pr (6 : Fin 7) = (2 : ℝ) := rfl
theorem aV_0 : aV (0 : Fin 1) = (1 / 16 : ℝ) := rfl
theorem bV_0 : bV (0 : Fin 1) = (7 / 96 : ℝ) := rfl
theorem dV_0 : dV (0 : Fin 1) = (7 / 1056 : ℝ) := rfl
theorem TV_0 : TV (0 : Fin 1) = (7 / 88 : ℝ) := rfl
theorem ZV_0 : ZV (0 : Fin 1) = (3 : ℤ) := rfl
theorem hab : ∀ c, aV c ≤ bV c := by intro c; fin_cases c <;> norm_num [aV, bV]
theorem hd0 : ∀ c, 0 < dV c := by intro c; fin_cases c <;> norm_num [dV]
theorem hdP : ∀ c, dV c ≤ 1 / (4 * (12 : ℝ)) := by intro c; fin_cases c <;> norm_num [dV]
theorem haP : ∀ c, dV c < aV c := by intro c; fin_cases c <;> norm_num [dV, aV]
theorem hT : ∀ c, bV c + dV c ≤ TV c := by intro c; fin_cases c <;> norm_num [bV, dV, TV]
theorem hZ : ∀ c, ((12 : ℝ) + 1) * TV c + 1 ≤ (ZV c : ℝ) := by intro c; fin_cases c <;> norm_num [TV, ZV]
theorem hE (ε : ℝ) (hε : ε ≤ (1 / 4828 : ℝ)) : ∀ c, 8 * ((ZV c : ℝ) + 1) * ε ≤ dV c := by
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
    (hHt : t ≤ HV) (h1 : (0 : ℝ) ≤ t) (h2 : t ≤ (125 / 2112 : ℝ)) (hlon : ∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)) : False := by
  exact zone_kill_gen pr x ε HV (1 / 512 : ℝ) hp1 hdev hεH (by norm_num) (6 : Fin 7) 0 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (6 : Fin 7))
theorem cov (x : Fin 7 → ℝ) (ε : ℝ) (hε : ε ≤ (1 / 4828 : ℝ)) (hdev : ∀ i, |x i - pr i| ≤ ε) :
    ∀ t : ℝ, 0 < t → t ≤ HV → (∀ c, ¬ (aV c - dV c / 2 ≤ t ∧ t ≤ bV c + dV c / 2)) →
      ¬ (∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)) := by
  intro t h0 hHt hnone hlon
  have hεH : ε * HV ≤ (1 / 512 : ℝ) / 2 := by
    have hε0 : 0 ≤ ε := le_trans (abs_nonneg _) (hdev 0)
    have : ε * HV ≤ (1 / 4828 : ℝ) * HV := mul_le_mul_of_nonneg_right hε (by norm_num [HV])
    have h2 : (1 / 4828 : ℝ) * HV ≤ (1 / 512 : ℝ) / 2 := by norm_num [HV]
    linarith
  have n0 := hnone (0 : Fin 1)
  rw [aV_0, bV_0, dV_0] at n0
  rcases lt_or_ge t (125 / 2112 : ℝ) with c0 | c0
  · exact gap0 x ε hdev hεH t h0.le hHt h0.le (by linarith) hlon
  have d0 : (161 / 2112 : ℝ) < t := by
    by_contra hc; push Not at hc; exact n0 ⟨by linarith, by linarith⟩
  have hHv : HV = (161 / 2112 : ℝ) := rfl
  exact absurd (by linarith : t ≤ (161 / 2112 : ℝ)) (not_le.2 d0)

theorem inst (x : Fin 7 → ℝ) (ε : ℝ) (hε : ε ≤ (1 / 4828 : ℝ)) (hdev : ∀ i, |x i - pr i| ≤ ε) :
    ∃ c₀ : Fin 1, Alive (mxOf x EXs hEXne) (mnOf x ENs hENne) c₀ ∧
      (∀ c, c < c₀ → ¬ Alive (mxOf x EXs hEXne) (mnOf x ENs hENne) c) ∧
      IsLeast {t : ℝ | 0 < t ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)} (mxOf x EXs hEXne c₀) :=
  landing_cert 1 (12 : ℝ) (by norm_num) pr x hp ε hdev aV bV dV TV ZV hab hd0 hdP haP hT hZ (hE ε hε) hcls EXs ENs hEXne hENne
    hEXdef hENdef hsepL HV hHL (cov x ε hε hdev) (0 : Fin 1) (by rw [dV_0, bV_0, aV_0]; norm_num)

noncomputable def sv : Fin 8 → ℝ := ![(1 : ℝ), (2 : ℝ), (4 : ℝ), (5 : ℝ), (8 : ℝ), (9 : ℝ), (11 : ℝ), (13 : ℝ)]
def sg : Fin 7 → Fin 8 := ![0, 1, 2, 3, 4, 5, 6]

theorem sv_0 : sv (0 : Fin 8) = (1 : ℝ) := rfl
theorem sv_1 : sv (1 : Fin 8) = (2 : ℝ) := rfl
theorem sv_2 : sv (2 : Fin 8) = (4 : ℝ) := rfl
theorem sv_3 : sv (3 : Fin 8) = (5 : ℝ) := rfl
theorem sv_4 : sv (4 : Fin 8) = (8 : ℝ) := rfl
theorem sv_5 : sv (5 : Fin 8) = (9 : ℝ) := rfl
theorem sv_6 : sv (6 : Fin 8) = (11 : ℝ) := rfl
theorem sv_7 : sv (7 : Fin 8) = (13 : ℝ) := rfl
theorem sg_0 : sg (0 : Fin 7) = (0 : Fin 8) := rfl
theorem sg_1 : sg (1 : Fin 7) = (1 : Fin 8) := rfl
theorem sg_2 : sg (2 : Fin 7) = (2 : Fin 8) := rfl
theorem sg_3 : sg (3 : Fin 7) = (3 : Fin 8) := rfl
theorem sg_4 : sg (4 : Fin 7) = (4 : Fin 8) := rfl
theorem sg_5 : sg (5 : Fin 7) = (5 : Fin 8) := rfl
theorem sg_6 : sg (6 : Fin 7) = (6 : Fin 8) := rfl

theorem inst_arr (v : Fin 8 → ℝ) (η : ℝ) (hη : η ≤ (1 / 9656 : ℝ)) (hv : ∀ j, |v j - sv j| ≤ η) :
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

end Fresh.CertRS.R06983



/-!
# Landing certificate `CertRS.R06984`: speeds (1, 2, 4, 5, 8, 9, 11, 15), subject index 0

Generated 2026-10-24 by `experiments/n8/cert_gen_v1.py` (exact Fractions).  Baseline readings [1, 3, 4, 7, 8, 10, 14].  Components up to the first wide one: 1.
Radius: speeds within `η ≤ 1/10752` of the baseline speeds, giving `ε = 2η ≤ 1/5376`.  Covering margin `μ = 1/256`.
`hcov` is **[PROVISIONAL: covering]**, supporting the claim that the first lonely instant of this subject is the largest exit of the first alive component.
Result `inst_arr`: for such `v`, the subject has a first isolation (a least element over all `t > 0`).  Grades: [L].
-/

open Classical

namespace Fresh.CertRS.R06984

open Fresh Fresh.LandingCert Fresh.LandingRule

noncomputable def pr : Fin 7 → ℝ := ![(1 : ℝ), (3 : ℝ), (4 : ℝ), (7 : ℝ), (8 : ℝ), (10 : ℝ), (14 : ℝ)]
noncomputable def aV : Fin 1 → ℝ := ![(9 / 56 : ℝ)]
noncomputable def bV : Fin 1 → ℝ := ![(3 / 16 : ℝ)]
noncomputable def dV : Fin 1 → ℝ := ![(1 / 112 : ℝ)]
noncomputable def TV : Fin 1 → ℝ := ![(11 / 56 : ℝ)]
def ZV : Fin 1 → ℤ := ![5]
noncomputable def HV : ℝ := (43 / 224 : ℝ)
noncomputable def EXs (c : Fin 1) : Finset (Fin 7 × ℤ) :=
  (Finset.univ ×ˢ Finset.Icc 0 (ZV c)).filter (fun q => ((q.2 : ℝ) + 1 / 8) / pr q.1 = aV c)
noncomputable def ENs (c : Fin 1) : Finset (Fin 7 × ℤ) :=
  (Finset.univ ×ˢ Finset.Icc 0 (ZV c)).filter (fun q => ((q.2 : ℝ) - 1 / 8) / pr q.1 = bV c)

theorem hp : ∀ i, 1 ≤ pr i ∧ pr i ≤ (14 : ℝ) := by intro i; fin_cases i <;> norm_num [pr]
theorem hp1 : ∀ i, 1 ≤ pr i := fun i => (hp i).1
theorem pr_0 : pr (0 : Fin 7) = (1 : ℝ) := rfl
theorem pr_1 : pr (1 : Fin 7) = (3 : ℝ) := rfl
theorem pr_2 : pr (2 : Fin 7) = (4 : ℝ) := rfl
theorem pr_3 : pr (3 : Fin 7) = (7 : ℝ) := rfl
theorem pr_4 : pr (4 : Fin 7) = (8 : ℝ) := rfl
theorem pr_5 : pr (5 : Fin 7) = (10 : ℝ) := rfl
theorem pr_6 : pr (6 : Fin 7) = (14 : ℝ) := rfl
theorem aV_0 : aV (0 : Fin 1) = (9 / 56 : ℝ) := rfl
theorem bV_0 : bV (0 : Fin 1) = (3 / 16 : ℝ) := rfl
theorem dV_0 : dV (0 : Fin 1) = (1 / 112 : ℝ) := rfl
theorem TV_0 : TV (0 : Fin 1) = (11 / 56 : ℝ) := rfl
theorem ZV_0 : ZV (0 : Fin 1) = (5 : ℤ) := rfl
theorem hab : ∀ c, aV c ≤ bV c := by intro c; fin_cases c <;> norm_num [aV, bV]
theorem hd0 : ∀ c, 0 < dV c := by intro c; fin_cases c <;> norm_num [dV]
theorem hdP : ∀ c, dV c ≤ 1 / (4 * (14 : ℝ)) := by intro c; fin_cases c <;> norm_num [dV]
theorem haP : ∀ c, dV c < aV c := by intro c; fin_cases c <;> norm_num [dV, aV]
theorem hT : ∀ c, bV c + dV c ≤ TV c := by intro c; fin_cases c <;> norm_num [bV, dV, TV]
theorem hZ : ∀ c, ((14 : ℝ) + 1) * TV c + 1 ≤ (ZV c : ℝ) := by intro c; fin_cases c <;> norm_num [TV, ZV]
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
  · exact ⟨(3, 1), by simp [EXs, ZV, pr, aV] <;> norm_num⟩
theorem hENne : ∀ c, (ENs c).Nonempty := by
  intro c
  fin_cases c
  · exact ⟨(5, 2), by simp [ENs, ZV, pr, bV] <;> norm_num⟩
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
    (hHt : t ≤ HV) (h1 : (0 : ℝ) ≤ t) (h2 : t ≤ (5 / 32 : ℝ)) (hlon : ∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)) : False := by
  rcases le_total t (31 / 256 : ℝ) with hs0 | hs0
  · exact zone_kill_gen pr x ε HV (1 / 256 : ℝ) hp1 hdev hεH (by norm_num) (0 : Fin 7) 0 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (0 : Fin 7))
  rcases le_total t (35 / 256 : ℝ) with hs1 | hs1
  · exact zone_kill_gen pr x ε HV (1 / 256 : ℝ) hp1 hdev hεH (by norm_num) (4 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (4 : Fin 7))
  exact zone_kill_gen pr x ε HV (1 / 256 : ℝ) hp1 hdev hεH (by norm_num) (3 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (3 : Fin 7))
theorem cov (x : Fin 7 → ℝ) (ε : ℝ) (hε : ε ≤ (1 / 5376 : ℝ)) (hdev : ∀ i, |x i - pr i| ≤ ε) :
    ∀ t : ℝ, 0 < t → t ≤ HV → (∀ c, ¬ (aV c - dV c / 2 ≤ t ∧ t ≤ bV c + dV c / 2)) →
      ¬ (∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)) := by
  intro t h0 hHt hnone hlon
  have hεH : ε * HV ≤ (1 / 256 : ℝ) / 2 := by
    have hε0 : 0 ≤ ε := le_trans (abs_nonneg _) (hdev 0)
    have : ε * HV ≤ (1 / 5376 : ℝ) * HV := mul_le_mul_of_nonneg_right hε (by norm_num [HV])
    have h2 : (1 / 5376 : ℝ) * HV ≤ (1 / 256 : ℝ) / 2 := by norm_num [HV]
    linarith
  have n0 := hnone (0 : Fin 1)
  rw [aV_0, bV_0, dV_0] at n0
  rcases lt_or_ge t (5 / 32 : ℝ) with c0 | c0
  · exact gap0 x ε hdev hεH t h0.le hHt h0.le (by linarith) hlon
  have d0 : (43 / 224 : ℝ) < t := by
    by_contra hc; push Not at hc; exact n0 ⟨by linarith, by linarith⟩
  have hHv : HV = (43 / 224 : ℝ) := rfl
  exact absurd (by linarith : t ≤ (43 / 224 : ℝ)) (not_le.2 d0)

theorem inst (x : Fin 7 → ℝ) (ε : ℝ) (hε : ε ≤ (1 / 5376 : ℝ)) (hdev : ∀ i, |x i - pr i| ≤ ε) :
    ∃ c₀ : Fin 1, Alive (mxOf x EXs hEXne) (mnOf x ENs hENne) c₀ ∧
      (∀ c, c < c₀ → ¬ Alive (mxOf x EXs hEXne) (mnOf x ENs hENne) c) ∧
      IsLeast {t : ℝ | 0 < t ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)} (mxOf x EXs hEXne c₀) :=
  landing_cert 1 (14 : ℝ) (by norm_num) pr x hp ε hdev aV bV dV TV ZV hab hd0 hdP haP hT hZ (hE ε hε) hcls EXs ENs hEXne hENne
    hEXdef hENdef hsepL HV hHL (cov x ε hε hdev) (0 : Fin 1) (by rw [dV_0, bV_0, aV_0]; norm_num)

noncomputable def sv : Fin 8 → ℝ := ![(1 : ℝ), (2 : ℝ), (4 : ℝ), (5 : ℝ), (8 : ℝ), (9 : ℝ), (11 : ℝ), (15 : ℝ)]
def sg : Fin 7 → Fin 8 := ![1, 2, 3, 4, 5, 6, 7]

theorem sv_0 : sv (0 : Fin 8) = (1 : ℝ) := rfl
theorem sv_1 : sv (1 : Fin 8) = (2 : ℝ) := rfl
theorem sv_2 : sv (2 : Fin 8) = (4 : ℝ) := rfl
theorem sv_3 : sv (3 : Fin 8) = (5 : ℝ) := rfl
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

theorem inst_arr (v : Fin 8 → ℝ) (η : ℝ) (hη : η ≤ (1 / 10752 : ℝ)) (hv : ∀ j, |v j - sv j| ≤ η) :
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

end Fresh.CertRS.R06984



/-!
# Landing certificate `CertRS.R06985`: speeds (1, 2, 4, 5, 8, 9, 11, 15), subject index 1

Generated 2026-10-24 by `experiments/n8/cert_gen_v1.py` (exact Fractions).  Baseline readings [1, 2, 3, 6, 7, 9, 13].  Components up to the first wide one: 2.
Radius: speeds within `η ≤ 1/7488` of the baseline speeds, giving `ε = 2η ≤ 1/3744`.  Covering margin `μ = 1/256`.
`hcov` is **[PROVISIONAL: covering]**, supporting the claim that the first lonely instant of this subject is the largest exit of the first alive component.
Result `inst_arr`: for such `v`, the subject has a first isolation (a least element over all `t > 0`).  Grades: [L].
-/

open Classical

namespace Fresh.CertRS.R06985

open Fresh Fresh.LandingCert Fresh.LandingRule

noncomputable def pr : Fin 7 → ℝ := ![(1 : ℝ), (2 : ℝ), (3 : ℝ), (6 : ℝ), (7 : ℝ), (9 : ℝ), (13 : ℝ)]
noncomputable def aV : Fin 2 → ℝ := ![(1 / 8 : ℝ), (3 / 16 : ℝ)]
noncomputable def bV : Fin 2 → ℝ := ![(1 / 8 : ℝ), (5 / 24 : ℝ)]
noncomputable def dV : Fin 2 → ℝ := ![(1 / 52 : ℝ), (1 / 78 : ℝ)]
noncomputable def TV : Fin 2 → ℝ := ![(15 / 104 : ℝ), (23 / 104 : ℝ)]
def ZV : Fin 2 → ℤ := ![4, 5]
noncomputable def HV : ℝ := (67 / 312 : ℝ)
noncomputable def EXs (c : Fin 2) : Finset (Fin 7 × ℤ) :=
  (Finset.univ ×ˢ Finset.Icc 0 (ZV c)).filter (fun q => ((q.2 : ℝ) + 1 / 8) / pr q.1 = aV c)
noncomputable def ENs (c : Fin 2) : Finset (Fin 7 × ℤ) :=
  (Finset.univ ×ˢ Finset.Icc 0 (ZV c)).filter (fun q => ((q.2 : ℝ) - 1 / 8) / pr q.1 = bV c)

theorem hp : ∀ i, 1 ≤ pr i ∧ pr i ≤ (13 : ℝ) := by intro i; fin_cases i <;> norm_num [pr]
theorem hp1 : ∀ i, 1 ≤ pr i := fun i => (hp i).1
theorem pr_0 : pr (0 : Fin 7) = (1 : ℝ) := rfl
theorem pr_1 : pr (1 : Fin 7) = (2 : ℝ) := rfl
theorem pr_2 : pr (2 : Fin 7) = (3 : ℝ) := rfl
theorem pr_3 : pr (3 : Fin 7) = (6 : ℝ) := rfl
theorem pr_4 : pr (4 : Fin 7) = (7 : ℝ) := rfl
theorem pr_5 : pr (5 : Fin 7) = (9 : ℝ) := rfl
theorem pr_6 : pr (6 : Fin 7) = (13 : ℝ) := rfl
theorem aV_0 : aV (0 : Fin 2) = (1 / 8 : ℝ) := rfl
theorem bV_0 : bV (0 : Fin 2) = (1 / 8 : ℝ) := rfl
theorem dV_0 : dV (0 : Fin 2) = (1 / 52 : ℝ) := rfl
theorem TV_0 : TV (0 : Fin 2) = (15 / 104 : ℝ) := rfl
theorem ZV_0 : ZV (0 : Fin 2) = (4 : ℤ) := rfl
theorem aV_1 : aV (1 : Fin 2) = (3 / 16 : ℝ) := rfl
theorem bV_1 : bV (1 : Fin 2) = (5 / 24 : ℝ) := rfl
theorem dV_1 : dV (1 : Fin 2) = (1 / 78 : ℝ) := rfl
theorem TV_1 : TV (1 : Fin 2) = (23 / 104 : ℝ) := rfl
theorem ZV_1 : ZV (1 : Fin 2) = (5 : ℤ) := rfl
theorem hab : ∀ c, aV c ≤ bV c := by intro c; fin_cases c <;> norm_num [aV, bV]
theorem hd0 : ∀ c, 0 < dV c := by intro c; fin_cases c <;> norm_num [dV]
theorem hdP : ∀ c, dV c ≤ 1 / (4 * (13 : ℝ)) := by intro c; fin_cases c <;> norm_num [dV]
theorem haP : ∀ c, dV c < aV c := by intro c; fin_cases c <;> norm_num [dV, aV]
theorem hT : ∀ c, bV c + dV c ≤ TV c := by intro c; fin_cases c <;> norm_num [bV, dV, TV]
theorem hZ : ∀ c, ((13 : ℝ) + 1) * TV c + 1 ≤ (ZV c : ℝ) := by intro c; fin_cases c <;> norm_num [TV, ZV]
theorem hE (ε : ℝ) (hε : ε ≤ (1 / 3744 : ℝ)) : ∀ c, 8 * ((ZV c : ℝ) + 1) * ε ≤ dV c := by
  intro c; fin_cases c <;> norm_num [ZV, dV] <;> linarith
theorem hcls : ∀ c i, ∀ z : ℤ, 0 ≤ z → z ≤ ZV c →
    ((z : ℝ) + 1 / 8) / pr i ≤ aV c - dV c ∨ bV c + dV c ≤ ((z : ℝ) - 1 / 8) / pr i ∨
      ((z : ℝ) + 1 / 8) / pr i = aV c ∨ ((z : ℝ) - 1 / 8) / pr i = bV c := by
  intro c i z h0 h1
  fin_cases c <;> fin_cases i <;> simp [ZV] at h1 <;> interval_cases z <;> norm_num [pr, aV, bV, dV]
theorem hEXne : ∀ c, (EXs c).Nonempty := by
  intro c
  fin_cases c
  · exact ⟨(0, 0), by simp [EXs, ZV, pr, aV] <;> norm_num⟩
  · exact ⟨(3, 1), by simp [EXs, ZV, pr, aV] <;> norm_num⟩
theorem hENne : ∀ c, (ENs c).Nonempty := by
  intro c
  fin_cases c
  · exact ⟨(4, 1), by simp [ENs, ZV, pr, bV] <;> norm_num⟩
  · exact ⟨(5, 2), by simp [ENs, ZV, pr, bV] <;> norm_num⟩
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
    (hHt : t ≤ HV) (h1 : (0 : ℝ) ≤ t) (h2 : t ≤ (3 / 26 : ℝ)) (hlon : ∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)) : False := by
  exact zone_kill_gen pr x ε HV (1 / 256 : ℝ) hp1 hdev hεH (by norm_num) (0 : Fin 7) 0 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (0 : Fin 7))
theorem gap1 (x : Fin 7 → ℝ) (ε : ℝ) (hdev : ∀ i, |x i - pr i| ≤ ε) (hεH : ε * HV ≤ (1 / 256 : ℝ) / 2) (t : ℝ) (h0 : 0 ≤ t)
    (hHt : t ≤ HV) (h1 : (7 / 52 : ℝ) ≤ t) (h2 : t ≤ (113 / 624 : ℝ)) (hlon : ∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)) : False := by
  rcases le_total t (281 / 1792 : ℝ) with hs0 | hs0
  · exact zone_kill_gen pr x ε HV (1 / 256 : ℝ) hp1 hdev hεH (by norm_num) (4 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (4 : Fin 7))
  exact zone_kill_gen pr x ε HV (1 / 256 : ℝ) hp1 hdev hεH (by norm_num) (3 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (3 : Fin 7))
theorem cov (x : Fin 7 → ℝ) (ε : ℝ) (hε : ε ≤ (1 / 3744 : ℝ)) (hdev : ∀ i, |x i - pr i| ≤ ε) :
    ∀ t : ℝ, 0 < t → t ≤ HV → (∀ c, ¬ (aV c - dV c / 2 ≤ t ∧ t ≤ bV c + dV c / 2)) →
      ¬ (∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)) := by
  intro t h0 hHt hnone hlon
  have hεH : ε * HV ≤ (1 / 256 : ℝ) / 2 := by
    have hε0 : 0 ≤ ε := le_trans (abs_nonneg _) (hdev 0)
    have : ε * HV ≤ (1 / 3744 : ℝ) * HV := mul_le_mul_of_nonneg_right hε (by norm_num [HV])
    have h2 : (1 / 3744 : ℝ) * HV ≤ (1 / 256 : ℝ) / 2 := by norm_num [HV]
    linarith
  have n0 := hnone (0 : Fin 2)
  rw [aV_0, bV_0, dV_0] at n0
  have n1 := hnone (1 : Fin 2)
  rw [aV_1, bV_1, dV_1] at n1
  rcases lt_or_ge t (3 / 26 : ℝ) with c0 | c0
  · exact gap0 x ε hdev hεH t h0.le hHt h0.le (by linarith) hlon
  have d0 : (7 / 52 : ℝ) < t := by
    by_contra hc; push Not at hc; exact n0 ⟨by linarith, by linarith⟩
  rcases lt_or_ge t (113 / 624 : ℝ) with c1 | c1
  · exact gap1 x ε hdev hεH t h0.le hHt d0.le (by linarith) hlon
  have d1 : (67 / 312 : ℝ) < t := by
    by_contra hc; push Not at hc; exact n1 ⟨by linarith, by linarith⟩
  have hHv : HV = (67 / 312 : ℝ) := rfl
  exact absurd (by linarith : t ≤ (67 / 312 : ℝ)) (not_le.2 d1)

theorem inst (x : Fin 7 → ℝ) (ε : ℝ) (hε : ε ≤ (1 / 3744 : ℝ)) (hdev : ∀ i, |x i - pr i| ≤ ε) :
    ∃ c₀ : Fin 2, Alive (mxOf x EXs hEXne) (mnOf x ENs hENne) c₀ ∧
      (∀ c, c < c₀ → ¬ Alive (mxOf x EXs hEXne) (mnOf x ENs hENne) c) ∧
      IsLeast {t : ℝ | 0 < t ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)} (mxOf x EXs hEXne c₀) :=
  landing_cert 2 (13 : ℝ) (by norm_num) pr x hp ε hdev aV bV dV TV ZV hab hd0 hdP haP hT hZ (hE ε hε) hcls EXs ENs hEXne hENne
    hEXdef hENdef hsepL HV hHL (cov x ε hε hdev) (1 : Fin 2) (by rw [dV_1, bV_1, aV_1]; norm_num)

noncomputable def sv : Fin 8 → ℝ := ![(1 : ℝ), (2 : ℝ), (4 : ℝ), (5 : ℝ), (8 : ℝ), (9 : ℝ), (11 : ℝ), (15 : ℝ)]
def sg : Fin 7 → Fin 8 := ![0, 2, 3, 4, 5, 6, 7]

theorem sv_0 : sv (0 : Fin 8) = (1 : ℝ) := rfl
theorem sv_1 : sv (1 : Fin 8) = (2 : ℝ) := rfl
theorem sv_2 : sv (2 : Fin 8) = (4 : ℝ) := rfl
theorem sv_3 : sv (3 : Fin 8) = (5 : ℝ) := rfl
theorem sv_4 : sv (4 : Fin 8) = (8 : ℝ) := rfl
theorem sv_5 : sv (5 : Fin 8) = (9 : ℝ) := rfl
theorem sv_6 : sv (6 : Fin 8) = (11 : ℝ) := rfl
theorem sv_7 : sv (7 : Fin 8) = (15 : ℝ) := rfl
theorem sg_0 : sg (0 : Fin 7) = (0 : Fin 8) := rfl
theorem sg_1 : sg (1 : Fin 7) = (2 : Fin 8) := rfl
theorem sg_2 : sg (2 : Fin 7) = (3 : Fin 8) := rfl
theorem sg_3 : sg (3 : Fin 7) = (4 : Fin 8) := rfl
theorem sg_4 : sg (4 : Fin 7) = (5 : Fin 8) := rfl
theorem sg_5 : sg (5 : Fin 7) = (6 : Fin 8) := rfl
theorem sg_6 : sg (6 : Fin 7) = (7 : Fin 8) := rfl

theorem inst_arr (v : Fin 8 → ℝ) (η : ℝ) (hη : η ≤ (1 / 7488 : ℝ)) (hv : ∀ j, |v j - sv j| ≤ η) :
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

end Fresh.CertRS.R06985



/-!
# Landing certificate `CertRS.R06986`: speeds (1, 2, 4, 5, 8, 9, 11, 15), subject index 2

Generated 2026-10-24 by `experiments/n8/cert_gen_v1.py` (exact Fractions).  Baseline readings [3, 2, 1, 4, 5, 7, 11].  Components up to the first wide one: 2.
Radius: speeds within `η ≤ 1/17600` of the baseline speeds, giving `ε = 2η ≤ 1/8800`.  Covering margin `μ = 1/512`.
`hcov` is **[PROVISIONAL: covering]**, supporting the claim that the first lonely instant of this subject is the largest exit of the first alive component.
Result `inst_arr`: for such `v`, the subject has a first isolation (a least element over all `t > 0`).  Grades: [L].
-/

open Classical

namespace Fresh.CertRS.R06986

open Fresh Fresh.LandingCert Fresh.LandingRule

noncomputable def pr : Fin 7 → ℝ := ![(3 : ℝ), (2 : ℝ), (1 : ℝ), (4 : ℝ), (5 : ℝ), (7 : ℝ), (11 : ℝ)]
noncomputable def aV : Fin 2 → ℝ := ![(1 / 8 : ℝ), (9 / 56 : ℝ)]
noncomputable def bV : Fin 2 → ℝ := ![(1 / 8 : ℝ), (15 / 88 : ℝ)]
noncomputable def dV : Fin 2 → ℝ := ![(1 / 56 : ℝ), (1 / 220 : ℝ)]
noncomputable def TV : Fin 2 → ℝ := ![(1 / 7 : ℝ), (7 / 40 : ℝ)]
def ZV : Fin 2 → ℤ := ![3, 4]
noncomputable def HV : ℝ := (19 / 110 : ℝ)
noncomputable def EXs (c : Fin 2) : Finset (Fin 7 × ℤ) :=
  (Finset.univ ×ˢ Finset.Icc 0 (ZV c)).filter (fun q => ((q.2 : ℝ) + 1 / 8) / pr q.1 = aV c)
noncomputable def ENs (c : Fin 2) : Finset (Fin 7 × ℤ) :=
  (Finset.univ ×ˢ Finset.Icc 0 (ZV c)).filter (fun q => ((q.2 : ℝ) - 1 / 8) / pr q.1 = bV c)

theorem hp : ∀ i, 1 ≤ pr i ∧ pr i ≤ (11 : ℝ) := by intro i; fin_cases i <;> norm_num [pr]
theorem hp1 : ∀ i, 1 ≤ pr i := fun i => (hp i).1
theorem pr_0 : pr (0 : Fin 7) = (3 : ℝ) := rfl
theorem pr_1 : pr (1 : Fin 7) = (2 : ℝ) := rfl
theorem pr_2 : pr (2 : Fin 7) = (1 : ℝ) := rfl
theorem pr_3 : pr (3 : Fin 7) = (4 : ℝ) := rfl
theorem pr_4 : pr (4 : Fin 7) = (5 : ℝ) := rfl
theorem pr_5 : pr (5 : Fin 7) = (7 : ℝ) := rfl
theorem pr_6 : pr (6 : Fin 7) = (11 : ℝ) := rfl
theorem aV_0 : aV (0 : Fin 2) = (1 / 8 : ℝ) := rfl
theorem bV_0 : bV (0 : Fin 2) = (1 / 8 : ℝ) := rfl
theorem dV_0 : dV (0 : Fin 2) = (1 / 56 : ℝ) := rfl
theorem TV_0 : TV (0 : Fin 2) = (1 / 7 : ℝ) := rfl
theorem ZV_0 : ZV (0 : Fin 2) = (3 : ℤ) := rfl
theorem aV_1 : aV (1 : Fin 2) = (9 / 56 : ℝ) := rfl
theorem bV_1 : bV (1 : Fin 2) = (15 / 88 : ℝ) := rfl
theorem dV_1 : dV (1 : Fin 2) = (1 / 220 : ℝ) := rfl
theorem TV_1 : TV (1 : Fin 2) = (7 / 40 : ℝ) := rfl
theorem ZV_1 : ZV (1 : Fin 2) = (4 : ℤ) := rfl
theorem hab : ∀ c, aV c ≤ bV c := by intro c; fin_cases c <;> norm_num [aV, bV]
theorem hd0 : ∀ c, 0 < dV c := by intro c; fin_cases c <;> norm_num [dV]
theorem hdP : ∀ c, dV c ≤ 1 / (4 * (11 : ℝ)) := by intro c; fin_cases c <;> norm_num [dV]
theorem haP : ∀ c, dV c < aV c := by intro c; fin_cases c <;> norm_num [dV, aV]
theorem hT : ∀ c, bV c + dV c ≤ TV c := by intro c; fin_cases c <;> norm_num [bV, dV, TV]
theorem hZ : ∀ c, ((11 : ℝ) + 1) * TV c + 1 ≤ (ZV c : ℝ) := by intro c; fin_cases c <;> norm_num [TV, ZV]
theorem hE (ε : ℝ) (hε : ε ≤ (1 / 8800 : ℝ)) : ∀ c, 8 * ((ZV c : ℝ) + 1) * ε ≤ dV c := by
  intro c; fin_cases c <;> norm_num [ZV, dV] <;> linarith
theorem hcls : ∀ c i, ∀ z : ℤ, 0 ≤ z → z ≤ ZV c →
    ((z : ℝ) + 1 / 8) / pr i ≤ aV c - dV c ∨ bV c + dV c ≤ ((z : ℝ) - 1 / 8) / pr i ∨
      ((z : ℝ) + 1 / 8) / pr i = aV c ∨ ((z : ℝ) - 1 / 8) / pr i = bV c := by
  intro c i z h0 h1
  fin_cases c <;> fin_cases i <;> simp [ZV] at h1 <;> interval_cases z <;> norm_num [pr, aV, bV, dV]
theorem hEXne : ∀ c, (EXs c).Nonempty := by
  intro c
  fin_cases c
  · exact ⟨(2, 0), by simp [EXs, ZV, pr, aV] <;> norm_num⟩
  · exact ⟨(5, 1), by simp [EXs, ZV, pr, aV] <;> norm_num⟩
theorem hENne : ∀ c, (ENs c).Nonempty := by
  intro c
  fin_cases c
  · exact ⟨(5, 1), by simp [ENs, ZV, pr, bV] <;> norm_num⟩
  · exact ⟨(6, 2), by simp [ENs, ZV, pr, bV] <;> norm_num⟩
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
    (hHt : t ≤ HV) (h1 : (0 : ℝ) ≤ t) (h2 : t ≤ (13 / 112 : ℝ)) (hlon : ∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)) : False := by
  exact zone_kill_gen pr x ε HV (1 / 512 : ℝ) hp1 hdev hεH (by norm_num) (2 : Fin 7) 0 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (2 : Fin 7))
theorem gap1 (x : Fin 7 → ℝ) (ε : ℝ) (hdev : ∀ i, |x i - pr i| ≤ ε) (hεH : ε * HV ≤ (1 / 512 : ℝ) / 2) (t : ℝ) (h0 : 0 ≤ t)
    (hHt : t ≤ HV) (h1 : (15 / 112 : ℝ) ≤ t) (h2 : t ≤ (61 / 385 : ℝ)) (hlon : ∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)) : False := by
  exact zone_kill_gen pr x ε HV (1 / 512 : ℝ) hp1 hdev hεH (by norm_num) (5 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (5 : Fin 7))
theorem cov (x : Fin 7 → ℝ) (ε : ℝ) (hε : ε ≤ (1 / 8800 : ℝ)) (hdev : ∀ i, |x i - pr i| ≤ ε) :
    ∀ t : ℝ, 0 < t → t ≤ HV → (∀ c, ¬ (aV c - dV c / 2 ≤ t ∧ t ≤ bV c + dV c / 2)) →
      ¬ (∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)) := by
  intro t h0 hHt hnone hlon
  have hεH : ε * HV ≤ (1 / 512 : ℝ) / 2 := by
    have hε0 : 0 ≤ ε := le_trans (abs_nonneg _) (hdev 0)
    have : ε * HV ≤ (1 / 8800 : ℝ) * HV := mul_le_mul_of_nonneg_right hε (by norm_num [HV])
    have h2 : (1 / 8800 : ℝ) * HV ≤ (1 / 512 : ℝ) / 2 := by norm_num [HV]
    linarith
  have n0 := hnone (0 : Fin 2)
  rw [aV_0, bV_0, dV_0] at n0
  have n1 := hnone (1 : Fin 2)
  rw [aV_1, bV_1, dV_1] at n1
  rcases lt_or_ge t (13 / 112 : ℝ) with c0 | c0
  · exact gap0 x ε hdev hεH t h0.le hHt h0.le (by linarith) hlon
  have d0 : (15 / 112 : ℝ) < t := by
    by_contra hc; push Not at hc; exact n0 ⟨by linarith, by linarith⟩
  rcases lt_or_ge t (61 / 385 : ℝ) with c1 | c1
  · exact gap1 x ε hdev hεH t h0.le hHt d0.le (by linarith) hlon
  have d1 : (19 / 110 : ℝ) < t := by
    by_contra hc; push Not at hc; exact n1 ⟨by linarith, by linarith⟩
  have hHv : HV = (19 / 110 : ℝ) := rfl
  exact absurd (by linarith : t ≤ (19 / 110 : ℝ)) (not_le.2 d1)

theorem inst (x : Fin 7 → ℝ) (ε : ℝ) (hε : ε ≤ (1 / 8800 : ℝ)) (hdev : ∀ i, |x i - pr i| ≤ ε) :
    ∃ c₀ : Fin 2, Alive (mxOf x EXs hEXne) (mnOf x ENs hENne) c₀ ∧
      (∀ c, c < c₀ → ¬ Alive (mxOf x EXs hEXne) (mnOf x ENs hENne) c) ∧
      IsLeast {t : ℝ | 0 < t ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)} (mxOf x EXs hEXne c₀) :=
  landing_cert 2 (11 : ℝ) (by norm_num) pr x hp ε hdev aV bV dV TV ZV hab hd0 hdP haP hT hZ (hE ε hε) hcls EXs ENs hEXne hENne
    hEXdef hENdef hsepL HV hHL (cov x ε hε hdev) (1 : Fin 2) (by rw [dV_1, bV_1, aV_1]; norm_num)

noncomputable def sv : Fin 8 → ℝ := ![(1 : ℝ), (2 : ℝ), (4 : ℝ), (5 : ℝ), (8 : ℝ), (9 : ℝ), (11 : ℝ), (15 : ℝ)]
def sg : Fin 7 → Fin 8 := ![0, 1, 3, 4, 5, 6, 7]

theorem sv_0 : sv (0 : Fin 8) = (1 : ℝ) := rfl
theorem sv_1 : sv (1 : Fin 8) = (2 : ℝ) := rfl
theorem sv_2 : sv (2 : Fin 8) = (4 : ℝ) := rfl
theorem sv_3 : sv (3 : Fin 8) = (5 : ℝ) := rfl
theorem sv_4 : sv (4 : Fin 8) = (8 : ℝ) := rfl
theorem sv_5 : sv (5 : Fin 8) = (9 : ℝ) := rfl
theorem sv_6 : sv (6 : Fin 8) = (11 : ℝ) := rfl
theorem sv_7 : sv (7 : Fin 8) = (15 : ℝ) := rfl
theorem sg_0 : sg (0 : Fin 7) = (0 : Fin 8) := rfl
theorem sg_1 : sg (1 : Fin 7) = (1 : Fin 8) := rfl
theorem sg_2 : sg (2 : Fin 7) = (3 : Fin 8) := rfl
theorem sg_3 : sg (3 : Fin 7) = (4 : Fin 8) := rfl
theorem sg_4 : sg (4 : Fin 7) = (5 : Fin 8) := rfl
theorem sg_5 : sg (5 : Fin 7) = (6 : Fin 8) := rfl
theorem sg_6 : sg (6 : Fin 7) = (7 : Fin 8) := rfl

theorem inst_arr (v : Fin 8 → ℝ) (η : ℝ) (hη : η ≤ (1 / 17600 : ℝ)) (hv : ∀ j, |v j - sv j| ≤ η) :
    ∃ c₀ : Fin 2, Alive (mxOf (fun i => |v (sg i) - v (2 : Fin 8)|) EXs hEXne) (mnOf (fun i => |v (sg i) - v (2 : Fin 8)|) ENs hENne) c₀ ∧
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

end Fresh.CertRS.R06986



/-!
# Landing certificate `CertRS.R06987`: speeds (1, 2, 4, 5, 8, 9, 11, 15), subject index 3

Generated 2026-10-24 by `experiments/n8/cert_gen_v1.py` (exact Fractions).  Baseline readings [4, 3, 1, 3, 4, 6, 10].  Components up to the first wide one: 1.
Radius: speeds within `η ≤ 1/5120` of the baseline speeds, giving `ε = 2η ≤ 1/2560`.  Covering margin `μ = 1/256`.
`hcov` is **[PROVISIONAL: covering]**, supporting the claim that the first lonely instant of this subject is the largest exit of the first alive component.
Result `inst_arr`: for such `v`, the subject has a first isolation (a least element over all `t > 0`).  Grades: [L].
-/

open Classical

namespace Fresh.CertRS.R06987

open Fresh Fresh.LandingCert Fresh.LandingRule

noncomputable def pr : Fin 7 → ℝ := ![(4 : ℝ), (3 : ℝ), (1 : ℝ), (3 : ℝ), (4 : ℝ), (6 : ℝ), (10 : ℝ)]
noncomputable def aV : Fin 1 → ℝ := ![(1 / 8 : ℝ)]
noncomputable def bV : Fin 1 → ℝ := ![(7 / 48 : ℝ)]
noncomputable def dV : Fin 1 → ℝ := ![(1 / 80 : ℝ)]
noncomputable def TV : Fin 1 → ℝ := ![(19 / 120 : ℝ)]
def ZV : Fin 1 → ℤ := ![3]
noncomputable def HV : ℝ := (73 / 480 : ℝ)
noncomputable def EXs (c : Fin 1) : Finset (Fin 7 × ℤ) :=
  (Finset.univ ×ˢ Finset.Icc 0 (ZV c)).filter (fun q => ((q.2 : ℝ) + 1 / 8) / pr q.1 = aV c)
noncomputable def ENs (c : Fin 1) : Finset (Fin 7 × ℤ) :=
  (Finset.univ ×ˢ Finset.Icc 0 (ZV c)).filter (fun q => ((q.2 : ℝ) - 1 / 8) / pr q.1 = bV c)

theorem hp : ∀ i, 1 ≤ pr i ∧ pr i ≤ (10 : ℝ) := by intro i; fin_cases i <;> norm_num [pr]
theorem hp1 : ∀ i, 1 ≤ pr i := fun i => (hp i).1
theorem pr_0 : pr (0 : Fin 7) = (4 : ℝ) := rfl
theorem pr_1 : pr (1 : Fin 7) = (3 : ℝ) := rfl
theorem pr_2 : pr (2 : Fin 7) = (1 : ℝ) := rfl
theorem pr_3 : pr (3 : Fin 7) = (3 : ℝ) := rfl
theorem pr_4 : pr (4 : Fin 7) = (4 : ℝ) := rfl
theorem pr_5 : pr (5 : Fin 7) = (6 : ℝ) := rfl
theorem pr_6 : pr (6 : Fin 7) = (10 : ℝ) := rfl
theorem aV_0 : aV (0 : Fin 1) = (1 / 8 : ℝ) := rfl
theorem bV_0 : bV (0 : Fin 1) = (7 / 48 : ℝ) := rfl
theorem dV_0 : dV (0 : Fin 1) = (1 / 80 : ℝ) := rfl
theorem TV_0 : TV (0 : Fin 1) = (19 / 120 : ℝ) := rfl
theorem ZV_0 : ZV (0 : Fin 1) = (3 : ℤ) := rfl
theorem hab : ∀ c, aV c ≤ bV c := by intro c; fin_cases c <;> norm_num [aV, bV]
theorem hd0 : ∀ c, 0 < dV c := by intro c; fin_cases c <;> norm_num [dV]
theorem hdP : ∀ c, dV c ≤ 1 / (4 * (10 : ℝ)) := by intro c; fin_cases c <;> norm_num [dV]
theorem haP : ∀ c, dV c < aV c := by intro c; fin_cases c <;> norm_num [dV, aV]
theorem hT : ∀ c, bV c + dV c ≤ TV c := by intro c; fin_cases c <;> norm_num [bV, dV, TV]
theorem hZ : ∀ c, ((10 : ℝ) + 1) * TV c + 1 ≤ (ZV c : ℝ) := by intro c; fin_cases c <;> norm_num [TV, ZV]
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
  · exact ⟨(2, 0), by simp [EXs, ZV, pr, aV] <;> norm_num⟩
theorem hENne : ∀ c, (ENs c).Nonempty := by
  intro c
  fin_cases c
  · exact ⟨(5, 1), by simp [ENs, ZV, pr, bV] <;> norm_num⟩
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
    (hHt : t ≤ HV) (h1 : (0 : ℝ) ≤ t) (h2 : t ≤ (19 / 160 : ℝ)) (hlon : ∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)) : False := by
  exact zone_kill_gen pr x ε HV (1 / 256 : ℝ) hp1 hdev hεH (by norm_num) (2 : Fin 7) 0 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (2 : Fin 7))
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
  rcases lt_or_ge t (19 / 160 : ℝ) with c0 | c0
  · exact gap0 x ε hdev hεH t h0.le hHt h0.le (by linarith) hlon
  have d0 : (73 / 480 : ℝ) < t := by
    by_contra hc; push Not at hc; exact n0 ⟨by linarith, by linarith⟩
  have hHv : HV = (73 / 480 : ℝ) := rfl
  exact absurd (by linarith : t ≤ (73 / 480 : ℝ)) (not_le.2 d0)

theorem inst (x : Fin 7 → ℝ) (ε : ℝ) (hε : ε ≤ (1 / 2560 : ℝ)) (hdev : ∀ i, |x i - pr i| ≤ ε) :
    ∃ c₀ : Fin 1, Alive (mxOf x EXs hEXne) (mnOf x ENs hENne) c₀ ∧
      (∀ c, c < c₀ → ¬ Alive (mxOf x EXs hEXne) (mnOf x ENs hENne) c) ∧
      IsLeast {t : ℝ | 0 < t ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)} (mxOf x EXs hEXne c₀) :=
  landing_cert 1 (10 : ℝ) (by norm_num) pr x hp ε hdev aV bV dV TV ZV hab hd0 hdP haP hT hZ (hE ε hε) hcls EXs ENs hEXne hENne
    hEXdef hENdef hsepL HV hHL (cov x ε hε hdev) (0 : Fin 1) (by rw [dV_0, bV_0, aV_0]; norm_num)

noncomputable def sv : Fin 8 → ℝ := ![(1 : ℝ), (2 : ℝ), (4 : ℝ), (5 : ℝ), (8 : ℝ), (9 : ℝ), (11 : ℝ), (15 : ℝ)]
def sg : Fin 7 → Fin 8 := ![0, 1, 2, 4, 5, 6, 7]

theorem sv_0 : sv (0 : Fin 8) = (1 : ℝ) := rfl
theorem sv_1 : sv (1 : Fin 8) = (2 : ℝ) := rfl
theorem sv_2 : sv (2 : Fin 8) = (4 : ℝ) := rfl
theorem sv_3 : sv (3 : Fin 8) = (5 : ℝ) := rfl
theorem sv_4 : sv (4 : Fin 8) = (8 : ℝ) := rfl
theorem sv_5 : sv (5 : Fin 8) = (9 : ℝ) := rfl
theorem sv_6 : sv (6 : Fin 8) = (11 : ℝ) := rfl
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

end Fresh.CertRS.R06987



/-!
# Landing certificate `CertRS.R06988`: speeds (1, 2, 4, 5, 8, 9, 11, 15), subject index 4

Generated 2026-10-24 by `experiments/n8/cert_gen_v1.py` (exact Fractions).  Baseline readings [7, 6, 4, 3, 1, 3, 7].  Components up to the first wide one: 2.
Radius: speeds within `η ≤ 1/3072` of the baseline speeds, giving `ε = 2η ≤ 1/1536`.  Covering margin `μ = 1/256`.
`hcov` is **[PROVISIONAL: covering]**, supporting the claim that the first lonely instant of this subject is the largest exit of the first alive component.
Result `inst_arr`: for such `v`, the subject has a first isolation (a least element over all `t > 0`).  Grades: [L].
-/

open Classical

namespace Fresh.CertRS.R06988

open Fresh Fresh.LandingCert Fresh.LandingRule

noncomputable def pr : Fin 7 → ℝ := ![(7 : ℝ), (6 : ℝ), (4 : ℝ), (3 : ℝ), (1 : ℝ), (3 : ℝ), (7 : ℝ)]
noncomputable def aV : Fin 2 → ℝ := ![(1 / 8 : ℝ), (3 / 16 : ℝ)]
noncomputable def bV : Fin 2 → ℝ := ![(1 / 8 : ℝ), (7 / 32 : ℝ)]
noncomputable def dV : Fin 2 → ℝ := ![(1 / 48 : ℝ), (3 / 112 : ℝ)]
noncomputable def TV : Fin 2 → ℝ := ![(7 / 48 : ℝ), (55 / 224 : ℝ)]
def ZV : Fin 2 → ℤ := ![3, 4]
noncomputable def HV : ℝ := (13 / 56 : ℝ)
noncomputable def EXs (c : Fin 2) : Finset (Fin 7 × ℤ) :=
  (Finset.univ ×ˢ Finset.Icc 0 (ZV c)).filter (fun q => ((q.2 : ℝ) + 1 / 8) / pr q.1 = aV c)
noncomputable def ENs (c : Fin 2) : Finset (Fin 7 × ℤ) :=
  (Finset.univ ×ˢ Finset.Icc 0 (ZV c)).filter (fun q => ((q.2 : ℝ) - 1 / 8) / pr q.1 = bV c)

theorem hp : ∀ i, 1 ≤ pr i ∧ pr i ≤ (7 : ℝ) := by intro i; fin_cases i <;> norm_num [pr]
theorem hp1 : ∀ i, 1 ≤ pr i := fun i => (hp i).1
theorem pr_0 : pr (0 : Fin 7) = (7 : ℝ) := rfl
theorem pr_1 : pr (1 : Fin 7) = (6 : ℝ) := rfl
theorem pr_2 : pr (2 : Fin 7) = (4 : ℝ) := rfl
theorem pr_3 : pr (3 : Fin 7) = (3 : ℝ) := rfl
theorem pr_4 : pr (4 : Fin 7) = (1 : ℝ) := rfl
theorem pr_5 : pr (5 : Fin 7) = (3 : ℝ) := rfl
theorem pr_6 : pr (6 : Fin 7) = (7 : ℝ) := rfl
theorem aV_0 : aV (0 : Fin 2) = (1 / 8 : ℝ) := rfl
theorem bV_0 : bV (0 : Fin 2) = (1 / 8 : ℝ) := rfl
theorem dV_0 : dV (0 : Fin 2) = (1 / 48 : ℝ) := rfl
theorem TV_0 : TV (0 : Fin 2) = (7 / 48 : ℝ) := rfl
theorem ZV_0 : ZV (0 : Fin 2) = (3 : ℤ) := rfl
theorem aV_1 : aV (1 : Fin 2) = (3 / 16 : ℝ) := rfl
theorem bV_1 : bV (1 : Fin 2) = (7 / 32 : ℝ) := rfl
theorem dV_1 : dV (1 : Fin 2) = (3 / 112 : ℝ) := rfl
theorem TV_1 : TV (1 : Fin 2) = (55 / 224 : ℝ) := rfl
theorem ZV_1 : ZV (1 : Fin 2) = (4 : ℤ) := rfl
theorem hab : ∀ c, aV c ≤ bV c := by intro c; fin_cases c <;> norm_num [aV, bV]
theorem hd0 : ∀ c, 0 < dV c := by intro c; fin_cases c <;> norm_num [dV]
theorem hdP : ∀ c, dV c ≤ 1 / (4 * (7 : ℝ)) := by intro c; fin_cases c <;> norm_num [dV]
theorem haP : ∀ c, dV c < aV c := by intro c; fin_cases c <;> norm_num [dV, aV]
theorem hT : ∀ c, bV c + dV c ≤ TV c := by intro c; fin_cases c <;> norm_num [bV, dV, TV]
theorem hZ : ∀ c, ((7 : ℝ) + 1) * TV c + 1 ≤ (ZV c : ℝ) := by intro c; fin_cases c <;> norm_num [TV, ZV]
theorem hE (ε : ℝ) (hε : ε ≤ (1 / 1536 : ℝ)) : ∀ c, 8 * ((ZV c : ℝ) + 1) * ε ≤ dV c := by
  intro c; fin_cases c <;> norm_num [ZV, dV] <;> linarith
theorem hcls : ∀ c i, ∀ z : ℤ, 0 ≤ z → z ≤ ZV c →
    ((z : ℝ) + 1 / 8) / pr i ≤ aV c - dV c ∨ bV c + dV c ≤ ((z : ℝ) - 1 / 8) / pr i ∨
      ((z : ℝ) + 1 / 8) / pr i = aV c ∨ ((z : ℝ) - 1 / 8) / pr i = bV c := by
  intro c i z h0 h1
  fin_cases c <;> fin_cases i <;> simp [ZV] at h1 <;> interval_cases z <;> norm_num [pr, aV, bV, dV]
theorem hEXne : ∀ c, (EXs c).Nonempty := by
  intro c
  fin_cases c
  · exact ⟨(4, 0), by simp [EXs, ZV, pr, aV] <;> norm_num⟩
  · exact ⟨(1, 1), by simp [EXs, ZV, pr, aV] <;> norm_num⟩
theorem hENne : ∀ c, (ENs c).Nonempty := by
  intro c
  fin_cases c
  · exact ⟨(0, 1), by simp [ENs, ZV, pr, bV] <;> norm_num⟩
  · exact ⟨(2, 1), by simp [ENs, ZV, pr, bV] <;> norm_num⟩
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
    (hHt : t ≤ HV) (h1 : (0 : ℝ) ≤ t) (h2 : t ≤ (11 / 96 : ℝ)) (hlon : ∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)) : False := by
  exact zone_kill_gen pr x ε HV (1 / 256 : ℝ) hp1 hdev hεH (by norm_num) (4 : Fin 7) 0 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (4 : Fin 7))
theorem gap1 (x : Fin 7 → ℝ) (ε : ℝ) (hdev : ∀ i, |x i - pr i| ≤ ε) (hεH : ε * HV ≤ (1 / 256 : ℝ) / 2) (t : ℝ) (h0 : 0 ≤ t)
    (hHt : t ≤ HV) (h1 : (13 / 96 : ℝ) ≤ t) (h2 : t ≤ (39 / 224 : ℝ)) (hlon : ∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)) : False := by
  rcases le_total t (281 / 1792 : ℝ) with hs0 | hs0
  · exact zone_kill_gen pr x ε HV (1 / 256 : ℝ) hp1 hdev hεH (by norm_num) (0 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (0 : Fin 7))
  exact zone_kill_gen pr x ε HV (1 / 256 : ℝ) hp1 hdev hεH (by norm_num) (1 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (1 : Fin 7))
theorem cov (x : Fin 7 → ℝ) (ε : ℝ) (hε : ε ≤ (1 / 1536 : ℝ)) (hdev : ∀ i, |x i - pr i| ≤ ε) :
    ∀ t : ℝ, 0 < t → t ≤ HV → (∀ c, ¬ (aV c - dV c / 2 ≤ t ∧ t ≤ bV c + dV c / 2)) →
      ¬ (∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)) := by
  intro t h0 hHt hnone hlon
  have hεH : ε * HV ≤ (1 / 256 : ℝ) / 2 := by
    have hε0 : 0 ≤ ε := le_trans (abs_nonneg _) (hdev 0)
    have : ε * HV ≤ (1 / 1536 : ℝ) * HV := mul_le_mul_of_nonneg_right hε (by norm_num [HV])
    have h2 : (1 / 1536 : ℝ) * HV ≤ (1 / 256 : ℝ) / 2 := by norm_num [HV]
    linarith
  have n0 := hnone (0 : Fin 2)
  rw [aV_0, bV_0, dV_0] at n0
  have n1 := hnone (1 : Fin 2)
  rw [aV_1, bV_1, dV_1] at n1
  rcases lt_or_ge t (11 / 96 : ℝ) with c0 | c0
  · exact gap0 x ε hdev hεH t h0.le hHt h0.le (by linarith) hlon
  have d0 : (13 / 96 : ℝ) < t := by
    by_contra hc; push Not at hc; exact n0 ⟨by linarith, by linarith⟩
  rcases lt_or_ge t (39 / 224 : ℝ) with c1 | c1
  · exact gap1 x ε hdev hεH t h0.le hHt d0.le (by linarith) hlon
  have d1 : (13 / 56 : ℝ) < t := by
    by_contra hc; push Not at hc; exact n1 ⟨by linarith, by linarith⟩
  have hHv : HV = (13 / 56 : ℝ) := rfl
  exact absurd (by linarith : t ≤ (13 / 56 : ℝ)) (not_le.2 d1)

theorem inst (x : Fin 7 → ℝ) (ε : ℝ) (hε : ε ≤ (1 / 1536 : ℝ)) (hdev : ∀ i, |x i - pr i| ≤ ε) :
    ∃ c₀ : Fin 2, Alive (mxOf x EXs hEXne) (mnOf x ENs hENne) c₀ ∧
      (∀ c, c < c₀ → ¬ Alive (mxOf x EXs hEXne) (mnOf x ENs hENne) c) ∧
      IsLeast {t : ℝ | 0 < t ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)} (mxOf x EXs hEXne c₀) :=
  landing_cert 2 (7 : ℝ) (by norm_num) pr x hp ε hdev aV bV dV TV ZV hab hd0 hdP haP hT hZ (hE ε hε) hcls EXs ENs hEXne hENne
    hEXdef hENdef hsepL HV hHL (cov x ε hε hdev) (1 : Fin 2) (by rw [dV_1, bV_1, aV_1]; norm_num)

noncomputable def sv : Fin 8 → ℝ := ![(1 : ℝ), (2 : ℝ), (4 : ℝ), (5 : ℝ), (8 : ℝ), (9 : ℝ), (11 : ℝ), (15 : ℝ)]
def sg : Fin 7 → Fin 8 := ![0, 1, 2, 3, 5, 6, 7]

theorem sv_0 : sv (0 : Fin 8) = (1 : ℝ) := rfl
theorem sv_1 : sv (1 : Fin 8) = (2 : ℝ) := rfl
theorem sv_2 : sv (2 : Fin 8) = (4 : ℝ) := rfl
theorem sv_3 : sv (3 : Fin 8) = (5 : ℝ) := rfl
theorem sv_4 : sv (4 : Fin 8) = (8 : ℝ) := rfl
theorem sv_5 : sv (5 : Fin 8) = (9 : ℝ) := rfl
theorem sv_6 : sv (6 : Fin 8) = (11 : ℝ) := rfl
theorem sv_7 : sv (7 : Fin 8) = (15 : ℝ) := rfl
theorem sg_0 : sg (0 : Fin 7) = (0 : Fin 8) := rfl
theorem sg_1 : sg (1 : Fin 7) = (1 : Fin 8) := rfl
theorem sg_2 : sg (2 : Fin 7) = (2 : Fin 8) := rfl
theorem sg_3 : sg (3 : Fin 7) = (3 : Fin 8) := rfl
theorem sg_4 : sg (4 : Fin 7) = (5 : Fin 8) := rfl
theorem sg_5 : sg (5 : Fin 7) = (6 : Fin 8) := rfl
theorem sg_6 : sg (6 : Fin 7) = (7 : Fin 8) := rfl

theorem inst_arr (v : Fin 8 → ℝ) (η : ℝ) (hη : η ≤ (1 / 3072 : ℝ)) (hv : ∀ j, |v j - sv j| ≤ η) :
    ∃ c₀ : Fin 2, Alive (mxOf (fun i => |v (sg i) - v (4 : Fin 8)|) EXs hEXne) (mnOf (fun i => |v (sg i) - v (4 : Fin 8)|) ENs hENne) c₀ ∧
      (∀ c, c < c₀ → ¬ Alive (mxOf (fun i => |v (sg i) - v (4 : Fin 8)|) EXs hEXne) (mnOf (fun i => |v (sg i) - v (4 : Fin 8)|) ENs hENne) c) ∧
      IsLeast {t : ℝ | 0 < t ∧ IsolatedAt v (4 : Fin 8) t} (mxOf (fun i => |v (sg i) - v (4 : Fin 8)|) EXs hEXne c₀) := by
  have hσk : ∀ i, sg i ≠ (4 : Fin 8) := by decide
  have hσ : ∀ j : Fin 8, j ≠ (4 : Fin 8) → ∃ i, sg i = j := by decide
  have hpr : ∀ i, pr i = |sv (sg i) - sv (4 : Fin 8)| := by
    intro i; rcases fin7_cases i with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6, sv_0, sv_1, sv_2, sv_3, sv_4, sv_5, sv_6, sv_7, sg_0, sg_1, sg_2, sg_3, sg_4, sg_5, sg_6]
  have hdev : ∀ i, |(|v (sg i) - v (4 : Fin 8)| - pr i)| ≤ 2 * η := by
    intro i; rw [hpr i]; exact reading_dev v sv η hv (sg i) (4 : Fin 8)
  obtain ⟨c₀, hal, hbf, hT0⟩ := inst (fun i => |v (sg i) - v (4 : Fin 8)|) (2 * η) (by linarith) hdev
  have hset : {t : ℝ | 0 < t ∧ IsolatedAt v (4 : Fin 8) t} =
      {t : ℝ | 0 < t ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (|v (sg i) - v (4 : Fin 8)| * t)} := by
    ext t; simp only [Set.mem_setOf_eq]; rw [iso_iff_readings v (4 : Fin 8) sg hσk hσ t]
  rw [hset]; exact ⟨c₀, hal, hbf, hT0⟩

#print axioms inst_arr

end Fresh.CertRS.R06988



/-!
# Landing certificate `CertRS.R06990`: speeds (1, 2, 4, 5, 8, 9, 11, 15), subject index 6

Generated 2026-10-24 by `experiments/n8/cert_gen_v1.py` (exact Fractions).  Baseline readings [10, 9, 7, 6, 3, 2, 4].  Components up to the first wide one: 1.
Radius: speeds within `η ≤ 1/6584` of the baseline speeds, giving `ε = 2η ≤ 1/3292`.  Covering margin `μ = 1/256`.
`hcov` is **[PROVISIONAL: covering]**, supporting the claim that the first lonely instant of this subject is the largest exit of the first alive component.
Result `inst_arr`: for such `v`, the subject has a first isolation (a least element over all `t > 0`).  Grades: [L].
-/

open Classical

namespace Fresh.CertRS.R06990

open Fresh Fresh.LandingCert Fresh.LandingRule

noncomputable def pr : Fin 7 → ℝ := ![(10 : ℝ), (9 : ℝ), (7 : ℝ), (6 : ℝ), (3 : ℝ), (2 : ℝ), (4 : ℝ)]
noncomputable def aV : Fin 1 → ℝ := ![(1 / 16 : ℝ)]
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
theorem pr_0 : pr (0 : Fin 7) = (10 : ℝ) := rfl
theorem pr_1 : pr (1 : Fin 7) = (9 : ℝ) := rfl
theorem pr_2 : pr (2 : Fin 7) = (7 : ℝ) := rfl
theorem pr_3 : pr (3 : Fin 7) = (6 : ℝ) := rfl
theorem pr_4 : pr (4 : Fin 7) = (3 : ℝ) := rfl
theorem pr_5 : pr (5 : Fin 7) = (2 : ℝ) := rfl
theorem pr_6 : pr (6 : Fin 7) = (4 : ℝ) := rfl
theorem aV_0 : aV (0 : Fin 1) = (1 / 16 : ℝ) := rfl
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
  · exact ⟨(5, 0), by simp [EXs, ZV, pr, aV] <;> norm_num⟩
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

theorem gap0 (x : Fin 7 → ℝ) (ε : ℝ) (hdev : ∀ i, |x i - pr i| ≤ ε) (hεH : ε * HV ≤ (1 / 256 : ℝ) / 2) (t : ℝ) (h0 : 0 ≤ t)
    (hHt : t ≤ HV) (h1 : (0 : ℝ) ≤ t) (h2 : t ≤ (83 / 1440 : ℝ)) (hlon : ∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)) : False := by
  exact zone_kill_gen pr x ε HV (1 / 256 : ℝ) hp1 hdev hεH (by norm_num) (5 : Fin 7) 0 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (5 : Fin 7))
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
  rcases lt_or_ge t (83 / 1440 : ℝ) with c0 | c0
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

noncomputable def sv : Fin 8 → ℝ := ![(1 : ℝ), (2 : ℝ), (4 : ℝ), (5 : ℝ), (8 : ℝ), (9 : ℝ), (11 : ℝ), (15 : ℝ)]
def sg : Fin 7 → Fin 8 := ![0, 1, 2, 3, 4, 5, 7]

theorem sv_0 : sv (0 : Fin 8) = (1 : ℝ) := rfl
theorem sv_1 : sv (1 : Fin 8) = (2 : ℝ) := rfl
theorem sv_2 : sv (2 : Fin 8) = (4 : ℝ) := rfl
theorem sv_3 : sv (3 : Fin 8) = (5 : ℝ) := rfl
theorem sv_4 : sv (4 : Fin 8) = (8 : ℝ) := rfl
theorem sv_5 : sv (5 : Fin 8) = (9 : ℝ) := rfl
theorem sv_6 : sv (6 : Fin 8) = (11 : ℝ) := rfl
theorem sv_7 : sv (7 : Fin 8) = (15 : ℝ) := rfl
theorem sg_0 : sg (0 : Fin 7) = (0 : Fin 8) := rfl
theorem sg_1 : sg (1 : Fin 7) = (1 : Fin 8) := rfl
theorem sg_2 : sg (2 : Fin 7) = (2 : Fin 8) := rfl
theorem sg_3 : sg (3 : Fin 7) = (3 : Fin 8) := rfl
theorem sg_4 : sg (4 : Fin 7) = (4 : Fin 8) := rfl
theorem sg_5 : sg (5 : Fin 7) = (5 : Fin 8) := rfl
theorem sg_6 : sg (6 : Fin 7) = (7 : Fin 8) := rfl

theorem inst_arr (v : Fin 8 → ℝ) (η : ℝ) (hη : η ≤ (1 / 6584 : ℝ)) (hv : ∀ j, |v j - sv j| ≤ η) :
    ∃ c₀ : Fin 1, Alive (mxOf (fun i => |v (sg i) - v (6 : Fin 8)|) EXs hEXne) (mnOf (fun i => |v (sg i) - v (6 : Fin 8)|) ENs hENne) c₀ ∧
      (∀ c, c < c₀ → ¬ Alive (mxOf (fun i => |v (sg i) - v (6 : Fin 8)|) EXs hEXne) (mnOf (fun i => |v (sg i) - v (6 : Fin 8)|) ENs hENne) c) ∧
      IsLeast {t : ℝ | 0 < t ∧ IsolatedAt v (6 : Fin 8) t} (mxOf (fun i => |v (sg i) - v (6 : Fin 8)|) EXs hEXne c₀) := by
  have hσk : ∀ i, sg i ≠ (6 : Fin 8) := by decide
  have hσ : ∀ j : Fin 8, j ≠ (6 : Fin 8) → ∃ i, sg i = j := by decide
  have hpr : ∀ i, pr i = |sv (sg i) - sv (6 : Fin 8)| := by
    intro i; rcases fin7_cases i with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6, sv_0, sv_1, sv_2, sv_3, sv_4, sv_5, sv_6, sv_7, sg_0, sg_1, sg_2, sg_3, sg_4, sg_5, sg_6]
  have hdev : ∀ i, |(|v (sg i) - v (6 : Fin 8)| - pr i)| ≤ 2 * η := by
    intro i; rw [hpr i]; exact reading_dev v sv η hv (sg i) (6 : Fin 8)
  obtain ⟨c₀, hal, hbf, hT0⟩ := inst (fun i => |v (sg i) - v (6 : Fin 8)|) (2 * η) (by linarith) hdev
  have hset : {t : ℝ | 0 < t ∧ IsolatedAt v (6 : Fin 8) t} =
      {t : ℝ | 0 < t ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (|v (sg i) - v (6 : Fin 8)| * t)} := by
    ext t; simp only [Set.mem_setOf_eq]; rw [iso_iff_readings v (6 : Fin 8) sg hσk hσ t]
  rw [hset]; exact ⟨c₀, hal, hbf, hT0⟩

#print axioms inst_arr

end Fresh.CertRS.R06990



/-!
# Landing certificate `CertRS.R06991`: speeds (1, 2, 4, 5, 8, 9, 11, 15), subject index 7

Generated 2026-10-24 by `experiments/n8/cert_gen_v1.py` (exact Fractions).  Baseline readings [14, 13, 11, 10, 7, 6, 4].  Components up to the first wide one: 1.
Radius: speeds within `η ≤ 1/13312` of the baseline speeds, giving `ε = 2η ≤ 1/6656`.  Covering margin `μ = 1/512`.
`hcov` is **[PROVISIONAL: covering]**, supporting the claim that the first lonely instant of this subject is the largest exit of the first alive component.
Result `inst_arr`: for such `v`, the subject has a first isolation (a least element over all `t > 0`).  Grades: [L].
-/

open Classical

namespace Fresh.CertRS.R06991

open Fresh Fresh.LandingCert Fresh.LandingRule

noncomputable def pr : Fin 7 → ℝ := ![(14 : ℝ), (13 : ℝ), (11 : ℝ), (10 : ℝ), (7 : ℝ), (6 : ℝ), (4 : ℝ)]
noncomputable def aV : Fin 1 → ℝ := ![(1 / 32 : ℝ)]
noncomputable def bV : Fin 1 → ℝ := ![(1 / 16 : ℝ)]
noncomputable def dV : Fin 1 → ℝ := ![(1 / 208 : ℝ)]
noncomputable def TV : Fin 1 → ℝ := ![(7 / 104 : ℝ)]
def ZV : Fin 1 → ℤ := ![3]
noncomputable def HV : ℝ := (27 / 416 : ℝ)
noncomputable def EXs (c : Fin 1) : Finset (Fin 7 × ℤ) :=
  (Finset.univ ×ˢ Finset.Icc 0 (ZV c)).filter (fun q => ((q.2 : ℝ) + 1 / 8) / pr q.1 = aV c)
noncomputable def ENs (c : Fin 1) : Finset (Fin 7 × ℤ) :=
  (Finset.univ ×ˢ Finset.Icc 0 (ZV c)).filter (fun q => ((q.2 : ℝ) - 1 / 8) / pr q.1 = bV c)

theorem hp : ∀ i, 1 ≤ pr i ∧ pr i ≤ (14 : ℝ) := by intro i; fin_cases i <;> norm_num [pr]
theorem hp1 : ∀ i, 1 ≤ pr i := fun i => (hp i).1
theorem pr_0 : pr (0 : Fin 7) = (14 : ℝ) := rfl
theorem pr_1 : pr (1 : Fin 7) = (13 : ℝ) := rfl
theorem pr_2 : pr (2 : Fin 7) = (11 : ℝ) := rfl
theorem pr_3 : pr (3 : Fin 7) = (10 : ℝ) := rfl
theorem pr_4 : pr (4 : Fin 7) = (7 : ℝ) := rfl
theorem pr_5 : pr (5 : Fin 7) = (6 : ℝ) := rfl
theorem pr_6 : pr (6 : Fin 7) = (4 : ℝ) := rfl
theorem aV_0 : aV (0 : Fin 1) = (1 / 32 : ℝ) := rfl
theorem bV_0 : bV (0 : Fin 1) = (1 / 16 : ℝ) := rfl
theorem dV_0 : dV (0 : Fin 1) = (1 / 208 : ℝ) := rfl
theorem TV_0 : TV (0 : Fin 1) = (7 / 104 : ℝ) := rfl
theorem ZV_0 : ZV (0 : Fin 1) = (3 : ℤ) := rfl
theorem hab : ∀ c, aV c ≤ bV c := by intro c; fin_cases c <;> norm_num [aV, bV]
theorem hd0 : ∀ c, 0 < dV c := by intro c; fin_cases c <;> norm_num [dV]
theorem hdP : ∀ c, dV c ≤ 1 / (4 * (14 : ℝ)) := by intro c; fin_cases c <;> norm_num [dV]
theorem haP : ∀ c, dV c < aV c := by intro c; fin_cases c <;> norm_num [dV, aV]
theorem hT : ∀ c, bV c + dV c ≤ TV c := by intro c; fin_cases c <;> norm_num [bV, dV, TV]
theorem hZ : ∀ c, ((14 : ℝ) + 1) * TV c + 1 ≤ (ZV c : ℝ) := by intro c; fin_cases c <;> norm_num [TV, ZV]
theorem hE (ε : ℝ) (hε : ε ≤ (1 / 6656 : ℝ)) : ∀ c, 8 * ((ZV c : ℝ) + 1) * ε ≤ dV c := by
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
    (hHt : t ≤ HV) (h1 : (0 : ℝ) ≤ t) (h2 : t ≤ (3 / 104 : ℝ)) (hlon : ∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)) : False := by
  exact zone_kill_gen pr x ε HV (1 / 512 : ℝ) hp1 hdev hεH (by norm_num) (6 : Fin 7) 0 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (6 : Fin 7))
theorem cov (x : Fin 7 → ℝ) (ε : ℝ) (hε : ε ≤ (1 / 6656 : ℝ)) (hdev : ∀ i, |x i - pr i| ≤ ε) :
    ∀ t : ℝ, 0 < t → t ≤ HV → (∀ c, ¬ (aV c - dV c / 2 ≤ t ∧ t ≤ bV c + dV c / 2)) →
      ¬ (∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)) := by
  intro t h0 hHt hnone hlon
  have hεH : ε * HV ≤ (1 / 512 : ℝ) / 2 := by
    have hε0 : 0 ≤ ε := le_trans (abs_nonneg _) (hdev 0)
    have : ε * HV ≤ (1 / 6656 : ℝ) * HV := mul_le_mul_of_nonneg_right hε (by norm_num [HV])
    have h2 : (1 / 6656 : ℝ) * HV ≤ (1 / 512 : ℝ) / 2 := by norm_num [HV]
    linarith
  have n0 := hnone (0 : Fin 1)
  rw [aV_0, bV_0, dV_0] at n0
  rcases lt_or_ge t (3 / 104 : ℝ) with c0 | c0
  · exact gap0 x ε hdev hεH t h0.le hHt h0.le (by linarith) hlon
  have d0 : (27 / 416 : ℝ) < t := by
    by_contra hc; push Not at hc; exact n0 ⟨by linarith, by linarith⟩
  have hHv : HV = (27 / 416 : ℝ) := rfl
  exact absurd (by linarith : t ≤ (27 / 416 : ℝ)) (not_le.2 d0)

theorem inst (x : Fin 7 → ℝ) (ε : ℝ) (hε : ε ≤ (1 / 6656 : ℝ)) (hdev : ∀ i, |x i - pr i| ≤ ε) :
    ∃ c₀ : Fin 1, Alive (mxOf x EXs hEXne) (mnOf x ENs hENne) c₀ ∧
      (∀ c, c < c₀ → ¬ Alive (mxOf x EXs hEXne) (mnOf x ENs hENne) c) ∧
      IsLeast {t : ℝ | 0 < t ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)} (mxOf x EXs hEXne c₀) :=
  landing_cert 1 (14 : ℝ) (by norm_num) pr x hp ε hdev aV bV dV TV ZV hab hd0 hdP haP hT hZ (hE ε hε) hcls EXs ENs hEXne hENne
    hEXdef hENdef hsepL HV hHL (cov x ε hε hdev) (0 : Fin 1) (by rw [dV_0, bV_0, aV_0]; norm_num)

noncomputable def sv : Fin 8 → ℝ := ![(1 : ℝ), (2 : ℝ), (4 : ℝ), (5 : ℝ), (8 : ℝ), (9 : ℝ), (11 : ℝ), (15 : ℝ)]
def sg : Fin 7 → Fin 8 := ![0, 1, 2, 3, 4, 5, 6]

theorem sv_0 : sv (0 : Fin 8) = (1 : ℝ) := rfl
theorem sv_1 : sv (1 : Fin 8) = (2 : ℝ) := rfl
theorem sv_2 : sv (2 : Fin 8) = (4 : ℝ) := rfl
theorem sv_3 : sv (3 : Fin 8) = (5 : ℝ) := rfl
theorem sv_4 : sv (4 : Fin 8) = (8 : ℝ) := rfl
theorem sv_5 : sv (5 : Fin 8) = (9 : ℝ) := rfl
theorem sv_6 : sv (6 : Fin 8) = (11 : ℝ) := rfl
theorem sv_7 : sv (7 : Fin 8) = (15 : ℝ) := rfl
theorem sg_0 : sg (0 : Fin 7) = (0 : Fin 8) := rfl
theorem sg_1 : sg (1 : Fin 7) = (1 : Fin 8) := rfl
theorem sg_2 : sg (2 : Fin 7) = (2 : Fin 8) := rfl
theorem sg_3 : sg (3 : Fin 7) = (3 : Fin 8) := rfl
theorem sg_4 : sg (4 : Fin 7) = (4 : Fin 8) := rfl
theorem sg_5 : sg (5 : Fin 7) = (5 : Fin 8) := rfl
theorem sg_6 : sg (6 : Fin 7) = (6 : Fin 8) := rfl

theorem inst_arr (v : Fin 8 → ℝ) (η : ℝ) (hη : η ≤ (1 / 13312 : ℝ)) (hv : ∀ j, |v j - sv j| ≤ η) :
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

end Fresh.CertRS.R06991



/-!
# Landing certificate `CertRS.R06992`: speeds (1, 2, 4, 5, 8, 9, 11, 16), subject index 0

Generated 2026-10-24 by `experiments/n8/cert_gen_v1.py` (exact Fractions).  Baseline readings [1, 3, 4, 7, 8, 10, 15].  Components up to the first wide one: 1.
Radius: speeds within `η ≤ 1/23040` of the baseline speeds, giving `ε = 2η ≤ 1/11520`.  Covering margin `μ = 1/512`.
`hcov` is **[PROVISIONAL: covering]**, supporting the claim that the first lonely instant of this subject is the largest exit of the first alive component.
Result `inst_arr`: for such `v`, the subject has a first isolation (a least element over all `t > 0`).  Grades: [L].
-/

open Classical

namespace Fresh.CertRS.R06992

open Fresh Fresh.LandingCert Fresh.LandingRule

noncomputable def pr : Fin 7 → ℝ := ![(1 : ℝ), (3 : ℝ), (4 : ℝ), (7 : ℝ), (8 : ℝ), (10 : ℝ), (15 : ℝ)]
noncomputable def aV : Fin 1 → ℝ := ![(9 / 56 : ℝ)]
noncomputable def bV : Fin 1 → ℝ := ![(3 / 16 : ℝ)]
noncomputable def dV : Fin 1 → ℝ := ![(1 / 240 : ℝ)]
noncomputable def TV : Fin 1 → ℝ := ![(23 / 120 : ℝ)]
def ZV : Fin 1 → ℤ := ![5]
noncomputable def HV : ℝ := (91 / 480 : ℝ)
noncomputable def EXs (c : Fin 1) : Finset (Fin 7 × ℤ) :=
  (Finset.univ ×ˢ Finset.Icc 0 (ZV c)).filter (fun q => ((q.2 : ℝ) + 1 / 8) / pr q.1 = aV c)
noncomputable def ENs (c : Fin 1) : Finset (Fin 7 × ℤ) :=
  (Finset.univ ×ˢ Finset.Icc 0 (ZV c)).filter (fun q => ((q.2 : ℝ) - 1 / 8) / pr q.1 = bV c)

theorem hp : ∀ i, 1 ≤ pr i ∧ pr i ≤ (15 : ℝ) := by intro i; fin_cases i <;> norm_num [pr]
theorem hp1 : ∀ i, 1 ≤ pr i := fun i => (hp i).1
theorem pr_0 : pr (0 : Fin 7) = (1 : ℝ) := rfl
theorem pr_1 : pr (1 : Fin 7) = (3 : ℝ) := rfl
theorem pr_2 : pr (2 : Fin 7) = (4 : ℝ) := rfl
theorem pr_3 : pr (3 : Fin 7) = (7 : ℝ) := rfl
theorem pr_4 : pr (4 : Fin 7) = (8 : ℝ) := rfl
theorem pr_5 : pr (5 : Fin 7) = (10 : ℝ) := rfl
theorem pr_6 : pr (6 : Fin 7) = (15 : ℝ) := rfl
theorem aV_0 : aV (0 : Fin 1) = (9 / 56 : ℝ) := rfl
theorem bV_0 : bV (0 : Fin 1) = (3 / 16 : ℝ) := rfl
theorem dV_0 : dV (0 : Fin 1) = (1 / 240 : ℝ) := rfl
theorem TV_0 : TV (0 : Fin 1) = (23 / 120 : ℝ) := rfl
theorem ZV_0 : ZV (0 : Fin 1) = (5 : ℤ) := rfl
theorem hab : ∀ c, aV c ≤ bV c := by intro c; fin_cases c <;> norm_num [aV, bV]
theorem hd0 : ∀ c, 0 < dV c := by intro c; fin_cases c <;> norm_num [dV]
theorem hdP : ∀ c, dV c ≤ 1 / (4 * (15 : ℝ)) := by intro c; fin_cases c <;> norm_num [dV]
theorem haP : ∀ c, dV c < aV c := by intro c; fin_cases c <;> norm_num [dV, aV]
theorem hT : ∀ c, bV c + dV c ≤ TV c := by intro c; fin_cases c <;> norm_num [bV, dV, TV]
theorem hZ : ∀ c, ((15 : ℝ) + 1) * TV c + 1 ≤ (ZV c : ℝ) := by intro c; fin_cases c <;> norm_num [TV, ZV]
theorem hE (ε : ℝ) (hε : ε ≤ (1 / 11520 : ℝ)) : ∀ c, 8 * ((ZV c : ℝ) + 1) * ε ≤ dV c := by
  intro c; fin_cases c <;> norm_num [ZV, dV] <;> linarith
theorem hcls : ∀ c i, ∀ z : ℤ, 0 ≤ z → z ≤ ZV c →
    ((z : ℝ) + 1 / 8) / pr i ≤ aV c - dV c ∨ bV c + dV c ≤ ((z : ℝ) - 1 / 8) / pr i ∨
      ((z : ℝ) + 1 / 8) / pr i = aV c ∨ ((z : ℝ) - 1 / 8) / pr i = bV c := by
  intro c i z h0 h1
  fin_cases c <;> fin_cases i <;> simp [ZV] at h1 <;> interval_cases z <;> norm_num [pr, aV, bV, dV]
theorem hEXne : ∀ c, (EXs c).Nonempty := by
  intro c
  fin_cases c
  · exact ⟨(3, 1), by simp [EXs, ZV, pr, aV] <;> norm_num⟩
theorem hENne : ∀ c, (ENs c).Nonempty := by
  intro c
  fin_cases c
  · exact ⟨(5, 2), by simp [ENs, ZV, pr, bV] <;> norm_num⟩
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
    (hHt : t ≤ HV) (h1 : (0 : ℝ) ≤ t) (h2 : t ≤ (533 / 3360 : ℝ)) (hlon : ∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)) : False := by
  rcases le_total t (63 / 512 : ℝ) with hs0 | hs0
  · exact zone_kill_gen pr x ε HV (1 / 512 : ℝ) hp1 hdev hεH (by norm_num) (0 : Fin 7) 0 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (0 : Fin 7))
  rcases le_total t (71 / 512 : ℝ) with hs1 | hs1
  · exact zone_kill_gen pr x ε HV (1 / 512 : ℝ) hp1 hdev hεH (by norm_num) (4 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (4 : Fin 7))
  exact zone_kill_gen pr x ε HV (1 / 512 : ℝ) hp1 hdev hεH (by norm_num) (3 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (3 : Fin 7))
theorem cov (x : Fin 7 → ℝ) (ε : ℝ) (hε : ε ≤ (1 / 11520 : ℝ)) (hdev : ∀ i, |x i - pr i| ≤ ε) :
    ∀ t : ℝ, 0 < t → t ≤ HV → (∀ c, ¬ (aV c - dV c / 2 ≤ t ∧ t ≤ bV c + dV c / 2)) →
      ¬ (∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)) := by
  intro t h0 hHt hnone hlon
  have hεH : ε * HV ≤ (1 / 512 : ℝ) / 2 := by
    have hε0 : 0 ≤ ε := le_trans (abs_nonneg _) (hdev 0)
    have : ε * HV ≤ (1 / 11520 : ℝ) * HV := mul_le_mul_of_nonneg_right hε (by norm_num [HV])
    have h2 : (1 / 11520 : ℝ) * HV ≤ (1 / 512 : ℝ) / 2 := by norm_num [HV]
    linarith
  have n0 := hnone (0 : Fin 1)
  rw [aV_0, bV_0, dV_0] at n0
  rcases lt_or_ge t (533 / 3360 : ℝ) with c0 | c0
  · exact gap0 x ε hdev hεH t h0.le hHt h0.le (by linarith) hlon
  have d0 : (91 / 480 : ℝ) < t := by
    by_contra hc; push Not at hc; exact n0 ⟨by linarith, by linarith⟩
  have hHv : HV = (91 / 480 : ℝ) := rfl
  exact absurd (by linarith : t ≤ (91 / 480 : ℝ)) (not_le.2 d0)

theorem inst (x : Fin 7 → ℝ) (ε : ℝ) (hε : ε ≤ (1 / 11520 : ℝ)) (hdev : ∀ i, |x i - pr i| ≤ ε) :
    ∃ c₀ : Fin 1, Alive (mxOf x EXs hEXne) (mnOf x ENs hENne) c₀ ∧
      (∀ c, c < c₀ → ¬ Alive (mxOf x EXs hEXne) (mnOf x ENs hENne) c) ∧
      IsLeast {t : ℝ | 0 < t ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)} (mxOf x EXs hEXne c₀) :=
  landing_cert 1 (15 : ℝ) (by norm_num) pr x hp ε hdev aV bV dV TV ZV hab hd0 hdP haP hT hZ (hE ε hε) hcls EXs ENs hEXne hENne
    hEXdef hENdef hsepL HV hHL (cov x ε hε hdev) (0 : Fin 1) (by rw [dV_0, bV_0, aV_0]; norm_num)

noncomputable def sv : Fin 8 → ℝ := ![(1 : ℝ), (2 : ℝ), (4 : ℝ), (5 : ℝ), (8 : ℝ), (9 : ℝ), (11 : ℝ), (16 : ℝ)]
def sg : Fin 7 → Fin 8 := ![1, 2, 3, 4, 5, 6, 7]

theorem sv_0 : sv (0 : Fin 8) = (1 : ℝ) := rfl
theorem sv_1 : sv (1 : Fin 8) = (2 : ℝ) := rfl
theorem sv_2 : sv (2 : Fin 8) = (4 : ℝ) := rfl
theorem sv_3 : sv (3 : Fin 8) = (5 : ℝ) := rfl
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

theorem inst_arr (v : Fin 8 → ℝ) (η : ℝ) (hη : η ≤ (1 / 23040 : ℝ)) (hv : ∀ j, |v j - sv j| ≤ η) :
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

end Fresh.CertRS.R06992



/-!
# Landing certificate `CertRS.R06993`: speeds (1, 2, 4, 5, 8, 9, 11, 16), subject index 1

Generated 2026-10-24 by `experiments/n8/cert_gen_v1.py` (exact Fractions).  Baseline readings [1, 2, 3, 6, 7, 9, 14].  Components up to the first wide one: 2.
Radius: speeds within `η ≤ 1/32256` of the baseline speeds, giving `ε = 2η ≤ 1/16128`.  Covering margin `μ = 1/1024`.
`hcov` is **[PROVISIONAL: covering]**, supporting the claim that the first lonely instant of this subject is the largest exit of the first alive component.
Result `inst_arr`: for such `v`, the subject has a first isolation (a least element over all `t > 0`).  Grades: [L].
-/

open Classical

namespace Fresh.CertRS.R06993

open Fresh Fresh.LandingCert Fresh.LandingRule

noncomputable def pr : Fin 7 → ℝ := ![(1 : ℝ), (2 : ℝ), (3 : ℝ), (6 : ℝ), (7 : ℝ), (9 : ℝ), (14 : ℝ)]
noncomputable def aV : Fin 2 → ℝ := ![(1 / 8 : ℝ), (3 / 16 : ℝ)]
noncomputable def bV : Fin 2 → ℝ := ![(1 / 8 : ℝ), (23 / 112 : ℝ)]
noncomputable def dV : Fin 2 → ℝ := ![(1 / 112 : ℝ), (1 / 336 : ℝ)]
noncomputable def TV : Fin 2 → ℝ := ![(15 / 112 : ℝ), (5 / 24 : ℝ)]
def ZV : Fin 2 → ℤ := ![4, 5]
noncomputable def HV : ℝ := (139 / 672 : ℝ)
noncomputable def EXs (c : Fin 2) : Finset (Fin 7 × ℤ) :=
  (Finset.univ ×ˢ Finset.Icc 0 (ZV c)).filter (fun q => ((q.2 : ℝ) + 1 / 8) / pr q.1 = aV c)
noncomputable def ENs (c : Fin 2) : Finset (Fin 7 × ℤ) :=
  (Finset.univ ×ˢ Finset.Icc 0 (ZV c)).filter (fun q => ((q.2 : ℝ) - 1 / 8) / pr q.1 = bV c)

theorem hp : ∀ i, 1 ≤ pr i ∧ pr i ≤ (14 : ℝ) := by intro i; fin_cases i <;> norm_num [pr]
theorem hp1 : ∀ i, 1 ≤ pr i := fun i => (hp i).1
theorem pr_0 : pr (0 : Fin 7) = (1 : ℝ) := rfl
theorem pr_1 : pr (1 : Fin 7) = (2 : ℝ) := rfl
theorem pr_2 : pr (2 : Fin 7) = (3 : ℝ) := rfl
theorem pr_3 : pr (3 : Fin 7) = (6 : ℝ) := rfl
theorem pr_4 : pr (4 : Fin 7) = (7 : ℝ) := rfl
theorem pr_5 : pr (5 : Fin 7) = (9 : ℝ) := rfl
theorem pr_6 : pr (6 : Fin 7) = (14 : ℝ) := rfl
theorem aV_0 : aV (0 : Fin 2) = (1 / 8 : ℝ) := rfl
theorem bV_0 : bV (0 : Fin 2) = (1 / 8 : ℝ) := rfl
theorem dV_0 : dV (0 : Fin 2) = (1 / 112 : ℝ) := rfl
theorem TV_0 : TV (0 : Fin 2) = (15 / 112 : ℝ) := rfl
theorem ZV_0 : ZV (0 : Fin 2) = (4 : ℤ) := rfl
theorem aV_1 : aV (1 : Fin 2) = (3 / 16 : ℝ) := rfl
theorem bV_1 : bV (1 : Fin 2) = (23 / 112 : ℝ) := rfl
theorem dV_1 : dV (1 : Fin 2) = (1 / 336 : ℝ) := rfl
theorem TV_1 : TV (1 : Fin 2) = (5 / 24 : ℝ) := rfl
theorem ZV_1 : ZV (1 : Fin 2) = (5 : ℤ) := rfl
theorem hab : ∀ c, aV c ≤ bV c := by intro c; fin_cases c <;> norm_num [aV, bV]
theorem hd0 : ∀ c, 0 < dV c := by intro c; fin_cases c <;> norm_num [dV]
theorem hdP : ∀ c, dV c ≤ 1 / (4 * (14 : ℝ)) := by intro c; fin_cases c <;> norm_num [dV]
theorem haP : ∀ c, dV c < aV c := by intro c; fin_cases c <;> norm_num [dV, aV]
theorem hT : ∀ c, bV c + dV c ≤ TV c := by intro c; fin_cases c <;> norm_num [bV, dV, TV]
theorem hZ : ∀ c, ((14 : ℝ) + 1) * TV c + 1 ≤ (ZV c : ℝ) := by intro c; fin_cases c <;> norm_num [TV, ZV]
theorem hE (ε : ℝ) (hε : ε ≤ (1 / 16128 : ℝ)) : ∀ c, 8 * ((ZV c : ℝ) + 1) * ε ≤ dV c := by
  intro c; fin_cases c <;> norm_num [ZV, dV] <;> linarith
theorem hcls : ∀ c i, ∀ z : ℤ, 0 ≤ z → z ≤ ZV c →
    ((z : ℝ) + 1 / 8) / pr i ≤ aV c - dV c ∨ bV c + dV c ≤ ((z : ℝ) - 1 / 8) / pr i ∨
      ((z : ℝ) + 1 / 8) / pr i = aV c ∨ ((z : ℝ) - 1 / 8) / pr i = bV c := by
  intro c i z h0 h1
  fin_cases c <;> fin_cases i <;> simp [ZV] at h1 <;> interval_cases z <;> norm_num [pr, aV, bV, dV]
theorem hEXne : ∀ c, (EXs c).Nonempty := by
  intro c
  fin_cases c
  · exact ⟨(0, 0), by simp [EXs, ZV, pr, aV] <;> norm_num⟩
  · exact ⟨(3, 1), by simp [EXs, ZV, pr, aV] <;> norm_num⟩
theorem hENne : ∀ c, (ENs c).Nonempty := by
  intro c
  fin_cases c
  · exact ⟨(4, 1), by simp [ENs, ZV, pr, bV] <;> norm_num⟩
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

theorem gap0 (x : Fin 7 → ℝ) (ε : ℝ) (hdev : ∀ i, |x i - pr i| ≤ ε) (hεH : ε * HV ≤ (1 / 1024 : ℝ) / 2) (t : ℝ) (h0 : 0 ≤ t)
    (hHt : t ≤ HV) (h1 : (0 : ℝ) ≤ t) (h2 : t ≤ (27 / 224 : ℝ)) (hlon : ∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)) : False := by
  exact zone_kill_gen pr x ε HV (1 / 1024 : ℝ) hp1 hdev hεH (by norm_num) (0 : Fin 7) 0 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (0 : Fin 7))
theorem gap1 (x : Fin 7 → ℝ) (ε : ℝ) (hdev : ∀ i, |x i - pr i| ≤ ε) (hεH : ε * HV ≤ (1 / 1024 : ℝ) / 2) (t : ℝ) (h0 : 0 ≤ t)
    (hHt : t ≤ HV) (h1 : (29 / 224 : ℝ) ≤ t) (h2 : t ≤ (125 / 672 : ℝ)) (hlon : ∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)) : False := by
  rcases le_total t (1145 / 7168 : ℝ) with hs0 | hs0
  · exact zone_kill_gen pr x ε HV (1 / 1024 : ℝ) hp1 hdev hεH (by norm_num) (4 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (4 : Fin 7))
  exact zone_kill_gen pr x ε HV (1 / 1024 : ℝ) hp1 hdev hεH (by norm_num) (3 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (3 : Fin 7))
theorem cov (x : Fin 7 → ℝ) (ε : ℝ) (hε : ε ≤ (1 / 16128 : ℝ)) (hdev : ∀ i, |x i - pr i| ≤ ε) :
    ∀ t : ℝ, 0 < t → t ≤ HV → (∀ c, ¬ (aV c - dV c / 2 ≤ t ∧ t ≤ bV c + dV c / 2)) →
      ¬ (∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)) := by
  intro t h0 hHt hnone hlon
  have hεH : ε * HV ≤ (1 / 1024 : ℝ) / 2 := by
    have hε0 : 0 ≤ ε := le_trans (abs_nonneg _) (hdev 0)
    have : ε * HV ≤ (1 / 16128 : ℝ) * HV := mul_le_mul_of_nonneg_right hε (by norm_num [HV])
    have h2 : (1 / 16128 : ℝ) * HV ≤ (1 / 1024 : ℝ) / 2 := by norm_num [HV]
    linarith
  have n0 := hnone (0 : Fin 2)
  rw [aV_0, bV_0, dV_0] at n0
  have n1 := hnone (1 : Fin 2)
  rw [aV_1, bV_1, dV_1] at n1
  rcases lt_or_ge t (27 / 224 : ℝ) with c0 | c0
  · exact gap0 x ε hdev hεH t h0.le hHt h0.le (by linarith) hlon
  have d0 : (29 / 224 : ℝ) < t := by
    by_contra hc; push Not at hc; exact n0 ⟨by linarith, by linarith⟩
  rcases lt_or_ge t (125 / 672 : ℝ) with c1 | c1
  · exact gap1 x ε hdev hεH t h0.le hHt d0.le (by linarith) hlon
  have d1 : (139 / 672 : ℝ) < t := by
    by_contra hc; push Not at hc; exact n1 ⟨by linarith, by linarith⟩
  have hHv : HV = (139 / 672 : ℝ) := rfl
  exact absurd (by linarith : t ≤ (139 / 672 : ℝ)) (not_le.2 d1)

theorem inst (x : Fin 7 → ℝ) (ε : ℝ) (hε : ε ≤ (1 / 16128 : ℝ)) (hdev : ∀ i, |x i - pr i| ≤ ε) :
    ∃ c₀ : Fin 2, Alive (mxOf x EXs hEXne) (mnOf x ENs hENne) c₀ ∧
      (∀ c, c < c₀ → ¬ Alive (mxOf x EXs hEXne) (mnOf x ENs hENne) c) ∧
      IsLeast {t : ℝ | 0 < t ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)} (mxOf x EXs hEXne c₀) :=
  landing_cert 2 (14 : ℝ) (by norm_num) pr x hp ε hdev aV bV dV TV ZV hab hd0 hdP haP hT hZ (hE ε hε) hcls EXs ENs hEXne hENne
    hEXdef hENdef hsepL HV hHL (cov x ε hε hdev) (1 : Fin 2) (by rw [dV_1, bV_1, aV_1]; norm_num)

noncomputable def sv : Fin 8 → ℝ := ![(1 : ℝ), (2 : ℝ), (4 : ℝ), (5 : ℝ), (8 : ℝ), (9 : ℝ), (11 : ℝ), (16 : ℝ)]
def sg : Fin 7 → Fin 8 := ![0, 2, 3, 4, 5, 6, 7]

theorem sv_0 : sv (0 : Fin 8) = (1 : ℝ) := rfl
theorem sv_1 : sv (1 : Fin 8) = (2 : ℝ) := rfl
theorem sv_2 : sv (2 : Fin 8) = (4 : ℝ) := rfl
theorem sv_3 : sv (3 : Fin 8) = (5 : ℝ) := rfl
theorem sv_4 : sv (4 : Fin 8) = (8 : ℝ) := rfl
theorem sv_5 : sv (5 : Fin 8) = (9 : ℝ) := rfl
theorem sv_6 : sv (6 : Fin 8) = (11 : ℝ) := rfl
theorem sv_7 : sv (7 : Fin 8) = (16 : ℝ) := rfl
theorem sg_0 : sg (0 : Fin 7) = (0 : Fin 8) := rfl
theorem sg_1 : sg (1 : Fin 7) = (2 : Fin 8) := rfl
theorem sg_2 : sg (2 : Fin 7) = (3 : Fin 8) := rfl
theorem sg_3 : sg (3 : Fin 7) = (4 : Fin 8) := rfl
theorem sg_4 : sg (4 : Fin 7) = (5 : Fin 8) := rfl
theorem sg_5 : sg (5 : Fin 7) = (6 : Fin 8) := rfl
theorem sg_6 : sg (6 : Fin 7) = (7 : Fin 8) := rfl

theorem inst_arr (v : Fin 8 → ℝ) (η : ℝ) (hη : η ≤ (1 / 32256 : ℝ)) (hv : ∀ j, |v j - sv j| ≤ η) :
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

end Fresh.CertRS.R06993



/-!
# Landing certificate `CertRS.R06994`: speeds (1, 2, 4, 5, 8, 9, 11, 16), subject index 2

Generated 2026-10-24 by `experiments/n8/cert_gen_v1.py` (exact Fractions).  Baseline readings [3, 2, 1, 4, 5, 7, 12].  Components up to the first wide one: 4.
Radius: speeds within `η ≤ 1/10752` of the baseline speeds, giving `ε = 2η ≤ 1/5376`.  Covering margin `μ = 1/1024`.
`hcov` is **[PROVISIONAL: covering]**, supporting the claim that the first lonely instant of this subject is the largest exit of the first alive component.
Result `inst_arr`: for such `v`, the subject has a first isolation (a least element over all `t > 0`).  Grades: [L].
-/

open Classical

namespace Fresh.CertRS.R06994

open Fresh Fresh.LandingCert Fresh.LandingRule

noncomputable def pr : Fin 7 → ℝ := ![(3 : ℝ), (2 : ℝ), (1 : ℝ), (4 : ℝ), (5 : ℝ), (7 : ℝ), (12 : ℝ)]
noncomputable def aV : Fin 4 → ℝ := ![(1 / 8 : ℝ), (3 / 8 : ℝ), (5 / 8 : ℝ), (7 / 8 : ℝ)]
noncomputable def bV : Fin 4 → ℝ := ![(1 / 8 : ℝ), (3 / 8 : ℝ), (5 / 8 : ℝ), (7 / 8 : ℝ)]
noncomputable def dV : Fin 4 → ℝ := ![(1 / 48 : ℝ), (1 / 48 : ℝ), (1 / 48 : ℝ), (1 / 48 : ℝ)]
noncomputable def TV : Fin 4 → ℝ := ![(7 / 48 : ℝ), (19 / 48 : ℝ), (31 / 48 : ℝ), (43 / 48 : ℝ)]
def ZV : Fin 4 → ℤ := ![3, 7, 10, 13]
noncomputable def HV : ℝ := (85 / 96 : ℝ)
noncomputable def EXs (c : Fin 4) : Finset (Fin 7 × ℤ) :=
  (Finset.univ ×ˢ Finset.Icc 0 (ZV c)).filter (fun q => ((q.2 : ℝ) + 1 / 8) / pr q.1 = aV c)
noncomputable def ENs (c : Fin 4) : Finset (Fin 7 × ℤ) :=
  (Finset.univ ×ˢ Finset.Icc 0 (ZV c)).filter (fun q => ((q.2 : ℝ) - 1 / 8) / pr q.1 = bV c)

theorem fcases (c : Fin 4) : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 := by revert c; decide
theorem hp : ∀ i, 1 ≤ pr i ∧ pr i ≤ (12 : ℝ) := by intro i; fin_cases i <;> norm_num [pr]
theorem hp1 : ∀ i, 1 ≤ pr i := fun i => (hp i).1
theorem pr_0 : pr (0 : Fin 7) = (3 : ℝ) := rfl
theorem pr_1 : pr (1 : Fin 7) = (2 : ℝ) := rfl
theorem pr_2 : pr (2 : Fin 7) = (1 : ℝ) := rfl
theorem pr_3 : pr (3 : Fin 7) = (4 : ℝ) := rfl
theorem pr_4 : pr (4 : Fin 7) = (5 : ℝ) := rfl
theorem pr_5 : pr (5 : Fin 7) = (7 : ℝ) := rfl
theorem pr_6 : pr (6 : Fin 7) = (12 : ℝ) := rfl
theorem aV_0 : aV (0 : Fin 4) = (1 / 8 : ℝ) := rfl
theorem bV_0 : bV (0 : Fin 4) = (1 / 8 : ℝ) := rfl
theorem dV_0 : dV (0 : Fin 4) = (1 / 48 : ℝ) := rfl
theorem TV_0 : TV (0 : Fin 4) = (7 / 48 : ℝ) := rfl
theorem ZV_0 : ZV (0 : Fin 4) = (3 : ℤ) := rfl
theorem aV_1 : aV (1 : Fin 4) = (3 / 8 : ℝ) := rfl
theorem bV_1 : bV (1 : Fin 4) = (3 / 8 : ℝ) := rfl
theorem dV_1 : dV (1 : Fin 4) = (1 / 48 : ℝ) := rfl
theorem TV_1 : TV (1 : Fin 4) = (19 / 48 : ℝ) := rfl
theorem ZV_1 : ZV (1 : Fin 4) = (7 : ℤ) := rfl
theorem aV_2 : aV (2 : Fin 4) = (5 / 8 : ℝ) := rfl
theorem bV_2 : bV (2 : Fin 4) = (5 / 8 : ℝ) := rfl
theorem dV_2 : dV (2 : Fin 4) = (1 / 48 : ℝ) := rfl
theorem TV_2 : TV (2 : Fin 4) = (31 / 48 : ℝ) := rfl
theorem ZV_2 : ZV (2 : Fin 4) = (10 : ℤ) := rfl
theorem aV_3 : aV (3 : Fin 4) = (7 / 8 : ℝ) := rfl
theorem bV_3 : bV (3 : Fin 4) = (7 / 8 : ℝ) := rfl
theorem dV_3 : dV (3 : Fin 4) = (1 / 48 : ℝ) := rfl
theorem TV_3 : TV (3 : Fin 4) = (43 / 48 : ℝ) := rfl
theorem ZV_3 : ZV (3 : Fin 4) = (13 : ℤ) := rfl
theorem hab : ∀ c, aV c ≤ bV c := by intro c; rcases fcases c with rfl | rfl | rfl | rfl <;> norm_num [aV_0, bV_0, dV_0, TV_0, ZV_0, aV_1, bV_1, dV_1, TV_1, ZV_1, aV_2, bV_2, dV_2, TV_2, ZV_2, aV_3, bV_3, dV_3, TV_3, ZV_3]
theorem hd0 : ∀ c, 0 < dV c := by intro c; rcases fcases c with rfl | rfl | rfl | rfl <;> norm_num [aV_0, bV_0, dV_0, TV_0, ZV_0, aV_1, bV_1, dV_1, TV_1, ZV_1, aV_2, bV_2, dV_2, TV_2, ZV_2, aV_3, bV_3, dV_3, TV_3, ZV_3]
theorem hdP : ∀ c, dV c ≤ 1 / (4 * (12 : ℝ)) := by intro c; rcases fcases c with rfl | rfl | rfl | rfl <;> norm_num [aV_0, bV_0, dV_0, TV_0, ZV_0, aV_1, bV_1, dV_1, TV_1, ZV_1, aV_2, bV_2, dV_2, TV_2, ZV_2, aV_3, bV_3, dV_3, TV_3, ZV_3]
theorem haP : ∀ c, dV c < aV c := by intro c; rcases fcases c with rfl | rfl | rfl | rfl <;> norm_num [aV_0, bV_0, dV_0, TV_0, ZV_0, aV_1, bV_1, dV_1, TV_1, ZV_1, aV_2, bV_2, dV_2, TV_2, ZV_2, aV_3, bV_3, dV_3, TV_3, ZV_3]
theorem hT : ∀ c, bV c + dV c ≤ TV c := by intro c; rcases fcases c with rfl | rfl | rfl | rfl <;> norm_num [aV_0, bV_0, dV_0, TV_0, ZV_0, aV_1, bV_1, dV_1, TV_1, ZV_1, aV_2, bV_2, dV_2, TV_2, ZV_2, aV_3, bV_3, dV_3, TV_3, ZV_3]
theorem hZ : ∀ c, ((12 : ℝ) + 1) * TV c + 1 ≤ (ZV c : ℝ) := by intro c; rcases fcases c with rfl | rfl | rfl | rfl <;> norm_num [aV_0, bV_0, dV_0, TV_0, ZV_0, aV_1, bV_1, dV_1, TV_1, ZV_1, aV_2, bV_2, dV_2, TV_2, ZV_2, aV_3, bV_3, dV_3, TV_3, ZV_3]
theorem hE (ε : ℝ) (hε : ε ≤ (1 / 5376 : ℝ)) : ∀ c, 8 * ((ZV c : ℝ) + 1) * ε ≤ dV c := by
  intro c; rcases fcases c with rfl | rfl | rfl | rfl <;> norm_num [aV_0, bV_0, dV_0, TV_0, ZV_0, aV_1, bV_1, dV_1, TV_1, ZV_1, aV_2, bV_2, dV_2, TV_2, ZV_2, aV_3, bV_3, dV_3, TV_3, ZV_3] <;> linarith
set_option maxHeartbeats 4000000 in
theorem hcls : ∀ c i, ∀ z : ℤ, 0 ≤ z → z ≤ ZV c →
    ((z : ℝ) + 1 / 8) / pr i ≤ aV c - dV c ∨ bV c + dV c ≤ ((z : ℝ) - 1 / 8) / pr i ∨
      ((z : ℝ) + 1 / 8) / pr i = aV c ∨ ((z : ℝ) - 1 / 8) / pr i = bV c := by
  intro c i z h0 h1
  rcases fcases c with rfl | rfl | rfl | rfl <;> rcases fin7_cases i with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [aV_0, bV_0, dV_0, TV_0, ZV_0, aV_1, bV_1, dV_1, TV_1, ZV_1, aV_2, bV_2, dV_2, TV_2, ZV_2, aV_3, bV_3, dV_3, TV_3, ZV_3] at h1 <;> interval_cases z <;> norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6, aV_0, bV_0, dV_0, TV_0, ZV_0, aV_1, bV_1, dV_1, TV_1, ZV_1, aV_2, bV_2, dV_2, TV_2, ZV_2, aV_3, bV_3, dV_3, TV_3, ZV_3]
theorem hEXne : ∀ c, (EXs c).Nonempty := by
  intro c
  rcases fcases c with rfl | rfl | rfl | rfl
  · exact ⟨(2, 0), by simp [EXs, ZV, pr, aV] <;> norm_num⟩
  · exact ⟨(0, 1), by simp [EXs, ZV, pr, aV] <;> norm_num⟩
  · exact ⟨(4, 3), by simp [EXs, ZV, pr, aV] <;> norm_num⟩
  · exact ⟨(5, 6), by simp [EXs, ZV, pr, aV] <;> norm_num⟩
theorem hENne : ∀ c, (ENs c).Nonempty := by
  intro c
  rcases fcases c with rfl | rfl | rfl | rfl
  · exact ⟨(5, 1), by simp [ENs, ZV, pr, bV] <;> norm_num⟩
  · exact ⟨(4, 2), by simp [ENs, ZV, pr, bV] <;> norm_num⟩
  · exact ⟨(0, 2), by simp [ENs, ZV, pr, bV] <;> norm_num⟩
  · exact ⟨(2, 1), by simp [ENs, ZV, pr, bV] <;> norm_num⟩
theorem hEXdef : ∀ c, ∀ q : Fin 7 × ℤ, q ∈ EXs c ↔ 0 ≤ q.2 ∧ q.2 ≤ ZV c ∧ ((q.2 : ℝ) + 1 / 8) / pr q.1 = aV c := by
  intro c q
  simp only [EXs, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, Finset.mem_Icc, true_and]
  tauto
theorem hENdef : ∀ c, ∀ q : Fin 7 × ℤ, q ∈ ENs c ↔ 0 ≤ q.2 ∧ q.2 ≤ ZV c ∧ ((q.2 : ℝ) - 1 / 8) / pr q.1 = bV c := by
  intro c q
  simp only [ENs, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, Finset.mem_Icc, true_and]
  tauto
theorem hsepL : ∀ c c' : Fin 4, c < c' → bV c + dV c / 2 < aV c' - dV c' / 2 := by
  intro c c' h
  rcases fcases c with rfl | rfl | rfl | rfl <;> rcases fcases c' with rfl | rfl | rfl | rfl <;> simp at h ⊢ <;> norm_num [aV_0, bV_0, dV_0, TV_0, ZV_0, aV_1, bV_1, dV_1, TV_1, ZV_1, aV_2, bV_2, dV_2, TV_2, ZV_2, aV_3, bV_3, dV_3, TV_3, ZV_3]
theorem hHL : ∀ c, bV c + dV c / 2 ≤ HV := by intro c; rcases fcases c with rfl | rfl | rfl | rfl <;> norm_num [aV_0, bV_0, dV_0, TV_0, ZV_0, aV_1, bV_1, dV_1, TV_1, ZV_1, aV_2, bV_2, dV_2, TV_2, ZV_2, aV_3, bV_3, dV_3, TV_3, ZV_3, HV]

theorem gap0 (x : Fin 7 → ℝ) (ε : ℝ) (hdev : ∀ i, |x i - pr i| ≤ ε) (hεH : ε * HV ≤ (1 / 1024 : ℝ) / 2) (t : ℝ) (h0 : 0 ≤ t)
    (hHt : t ≤ HV) (h1 : (0 : ℝ) ≤ t) (h2 : t ≤ (11 / 96 : ℝ)) (hlon : ∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)) : False := by
  exact zone_kill_gen pr x ε HV (1 / 1024 : ℝ) hp1 hdev hεH (by norm_num) (2 : Fin 7) 0 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (2 : Fin 7))
theorem gap1 (x : Fin 7 → ℝ) (ε : ℝ) (hdev : ∀ i, |x i - pr i| ≤ ε) (hεH : ε * HV ≤ (1 / 1024 : ℝ) / 2) (t : ℝ) (h0 : 0 ≤ t)
    (hHt : t ≤ HV) (h1 : (13 / 96 : ℝ) ≤ t) (h2 : t ≤ (35 / 96 : ℝ)) (hlon : ∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)) : False := by
  rcases le_total t (1145 / 7168 : ℝ) with hs0 | hs0
  · exact zone_kill_gen pr x ε HV (1 / 1024 : ℝ) hp1 hdev hεH (by norm_num) (5 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (5 : Fin 7))
  rcases le_total t (541 / 3072 : ℝ) with hs1 | hs1
  · exact zone_kill_gen pr x ε HV (1 / 1024 : ℝ) hp1 hdev hεH (by norm_num) (6 : Fin 7) 2 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (6 : Fin 7))
  rcases le_total t (1147 / 5120 : ℝ) with hs2 | hs2
  · exact zone_kill_gen pr x ε HV (1 / 1024 : ℝ) hp1 hdev hεH (by norm_num) (4 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (4 : Fin 7))
  rcases le_total t (287 / 1024 : ℝ) with hs3 | hs3
  · exact zone_kill_gen pr x ε HV (1 / 1024 : ℝ) hp1 hdev hεH (by norm_num) (3 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (3 : Fin 7))
  rcases le_total t (2169 / 7168 : ℝ) with hs4 | hs4
  · exact zone_kill_gen pr x ε HV (1 / 1024 : ℝ) hp1 hdev hεH (by norm_num) (5 : Fin 7) 2 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (5 : Fin 7))
  exact zone_kill_gen pr x ε HV (1 / 1024 : ℝ) hp1 hdev hεH (by norm_num) (0 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (0 : Fin 7))
theorem gap2 (x : Fin 7 → ℝ) (ε : ℝ) (hdev : ∀ i, |x i - pr i| ≤ ε) (hεH : ε * HV ≤ (1 / 1024 : ℝ) / 2) (t : ℝ) (h0 : 0 ≤ t)
    (hHt : t ≤ HV) (h1 : (37 / 96 : ℝ) ≤ t) (h2 : t ≤ (59 / 96 : ℝ)) (hlon : ∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)) : False := by
  rcases le_total t (2171 / 5120 : ℝ) with hs0 | hs0
  · exact zone_kill_gen pr x ε HV (1 / 1024 : ℝ) hp1 hdev hεH (by norm_num) (4 : Fin 7) 2 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (4 : Fin 7))
  rcases le_total t (3193 / 7168 : ℝ) with hs1 | hs1
  · exact zone_kill_gen pr x ε HV (1 / 1024 : ℝ) hp1 hdev hεH (by norm_num) (5 : Fin 7) 3 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (5 : Fin 7))
  rcases le_total t (575 / 1024 : ℝ) with hs2 | hs2
  · exact zone_kill_gen pr x ε HV (1 / 1024 : ℝ) hp1 hdev hεH (by norm_num) (1 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (1 : Fin 7))
  rcases le_total t (4217 / 7168 : ℝ) with hs3 | hs3
  · exact zone_kill_gen pr x ε HV (1 / 1024 : ℝ) hp1 hdev hεH (by norm_num) (5 : Fin 7) 4 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (5 : Fin 7))
  exact zone_kill_gen pr x ε HV (1 / 1024 : ℝ) hp1 hdev hεH (by norm_num) (4 : Fin 7) 3 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (4 : Fin 7))
theorem gap3 (x : Fin 7 → ℝ) (ε : ℝ) (hdev : ∀ i, |x i - pr i| ≤ ε) (hεH : ε * HV ≤ (1 / 1024 : ℝ) / 2) (t : ℝ) (h0 : 0 ≤ t)
    (hHt : t ≤ HV) (h1 : (61 / 96 : ℝ) ≤ t) (h2 : t ≤ (83 / 96 : ℝ)) (hlon : ∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)) : False := by
  rcases le_total t (2173 / 3072 : ℝ) with hs0 | hs0
  · exact zone_kill_gen pr x ε HV (1 / 1024 : ℝ) hp1 hdev hεH (by norm_num) (0 : Fin 7) 2 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (0 : Fin 7))
  rcases le_total t (5241 / 7168 : ℝ) with hs1 | hs1
  · exact zone_kill_gen pr x ε HV (1 / 1024 : ℝ) hp1 hdev hεH (by norm_num) (5 : Fin 7) 5 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (5 : Fin 7))
  rcases le_total t (799 / 1024 : ℝ) with hs2 | hs2
  · exact zone_kill_gen pr x ε HV (1 / 1024 : ℝ) hp1 hdev hεH (by norm_num) (3 : Fin 7) 3 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (3 : Fin 7))
  rcases le_total t (4219 / 5120 : ℝ) with hs3 | hs3
  · exact zone_kill_gen pr x ε HV (1 / 1024 : ℝ) hp1 hdev hεH (by norm_num) (4 : Fin 7) 4 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (4 : Fin 7))
  rcases le_total t (863 / 1024 : ℝ) with hs4 | hs4
  · exact zone_kill_gen pr x ε HV (1 / 1024 : ℝ) hp1 hdev hεH (by norm_num) (6 : Fin 7) 10 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (6 : Fin 7))
  exact zone_kill_gen pr x ε HV (1 / 1024 : ℝ) hp1 hdev hεH (by norm_num) (5 : Fin 7) 6 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (5 : Fin 7))
theorem cov (x : Fin 7 → ℝ) (ε : ℝ) (hε : ε ≤ (1 / 5376 : ℝ)) (hdev : ∀ i, |x i - pr i| ≤ ε) :
    ∀ t : ℝ, 0 < t → t ≤ HV → (∀ c, ¬ (aV c - dV c / 2 ≤ t ∧ t ≤ bV c + dV c / 2)) →
      ¬ (∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)) := by
  intro t h0 hHt hnone hlon
  have hεH : ε * HV ≤ (1 / 1024 : ℝ) / 2 := by
    have hε0 : 0 ≤ ε := le_trans (abs_nonneg _) (hdev 0)
    have : ε * HV ≤ (1 / 5376 : ℝ) * HV := mul_le_mul_of_nonneg_right hε (by norm_num [HV])
    have h2 : (1 / 5376 : ℝ) * HV ≤ (1 / 1024 : ℝ) / 2 := by norm_num [HV]
    linarith
  have n0 := hnone (0 : Fin 4)
  rw [aV_0, bV_0, dV_0] at n0
  have n1 := hnone (1 : Fin 4)
  rw [aV_1, bV_1, dV_1] at n1
  have n2 := hnone (2 : Fin 4)
  rw [aV_2, bV_2, dV_2] at n2
  have n3 := hnone (3 : Fin 4)
  rw [aV_3, bV_3, dV_3] at n3
  rcases lt_or_ge t (11 / 96 : ℝ) with c0 | c0
  · exact gap0 x ε hdev hεH t h0.le hHt h0.le (by linarith) hlon
  have d0 : (13 / 96 : ℝ) < t := by
    by_contra hc; push Not at hc; exact n0 ⟨by linarith, by linarith⟩
  rcases lt_or_ge t (35 / 96 : ℝ) with c1 | c1
  · exact gap1 x ε hdev hεH t h0.le hHt d0.le (by linarith) hlon
  have d1 : (37 / 96 : ℝ) < t := by
    by_contra hc; push Not at hc; exact n1 ⟨by linarith, by linarith⟩
  rcases lt_or_ge t (59 / 96 : ℝ) with c2 | c2
  · exact gap2 x ε hdev hεH t h0.le hHt d1.le (by linarith) hlon
  have d2 : (61 / 96 : ℝ) < t := by
    by_contra hc; push Not at hc; exact n2 ⟨by linarith, by linarith⟩
  rcases lt_or_ge t (83 / 96 : ℝ) with c3 | c3
  · exact gap3 x ε hdev hεH t h0.le hHt d2.le (by linarith) hlon
  have d3 : (85 / 96 : ℝ) < t := by
    by_contra hc; push Not at hc; exact n3 ⟨by linarith, by linarith⟩
  have hHv : HV = (85 / 96 : ℝ) := rfl
  exact absurd (by linarith : t ≤ (85 / 96 : ℝ)) (not_le.2 d3)
theorem EX0 : EXs (0 : Fin 4) = {(2, (0 : ℤ))} := by
  ext q; obtain ⟨i, z⟩ := q
  simp only [EXs, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, Finset.mem_Icc, true_and, Finset.mem_singleton, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨h0, h1⟩, h2⟩
    rw [ZV_0] at h1
    rw [aV_0] at h2
    rcases fin7_cases i with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> interval_cases z <;> first | (exfalso; norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6] at h2; done) | norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]
  · rintro ⟨rfl, rfl⟩
    refine ⟨⟨by norm_num, by rw [ZV_0]; norm_num⟩, ?_⟩
    rw [aV_0]; norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]

theorem EN0 : ENs (0 : Fin 4) = {(5, (1 : ℤ))} := by
  ext q; obtain ⟨i, z⟩ := q
  simp only [ENs, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, Finset.mem_Icc, true_and, Finset.mem_singleton, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨h0, h1⟩, h2⟩
    rw [ZV_0] at h1
    rw [bV_0] at h2
    rcases fin7_cases i with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> interval_cases z <;> first | (exfalso; norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6] at h2; done) | norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]
  · rintro ⟨rfl, rfl⟩
    refine ⟨⟨by norm_num, by rw [ZV_0]; norm_num⟩, ?_⟩
    rw [bV_0]; norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]

theorem EX3 : EXs (3 : Fin 4) = {(5, (6 : ℤ))} := by
  ext q; obtain ⟨i, z⟩ := q
  simp only [EXs, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, Finset.mem_Icc, true_and, Finset.mem_singleton, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨h0, h1⟩, h2⟩
    rw [ZV_3] at h1
    rw [aV_3] at h2
    rcases fin7_cases i with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> interval_cases z <;> first | (exfalso; norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6] at h2; done) | norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]
  · rintro ⟨rfl, rfl⟩
    refine ⟨⟨by norm_num, by rw [ZV_3]; norm_num⟩, ?_⟩
    rw [aV_3]; norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]

theorem EN3 : ENs (3 : Fin 4) = {(2, (1 : ℤ))} := by
  ext q; obtain ⟨i, z⟩ := q
  simp only [ENs, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, Finset.mem_Icc, true_and, Finset.mem_singleton, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨h0, h1⟩, h2⟩
    rw [ZV_3] at h1
    rw [bV_3] at h2
    rcases fin7_cases i with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> interval_cases z <;> first | (exfalso; norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6] at h2; done) | norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]
  · rintro ⟨rfl, rfl⟩
    refine ⟨⟨by norm_num, by rw [ZV_3]; norm_num⟩, ?_⟩
    rw [bV_3]; norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]

theorem hexl (x : Fin 7 → ℝ) (ε : ℝ) (hε : ε ≤ (1 / 5376 : ℝ)) (hdev : ∀ i, |x i - pr i| ≤ ε) :
    ∃ c : Fin 4, Alive (mxOf x EXs hEXne) (mnOf x ENs hENne) c := by
  have hxi : 0 < x (2 : Fin 7) := by
    have := abs_le.1 (hdev (2 : Fin 7)); have := hp1 (2 : Fin 7); norm_num at hε ⊢; linarith
  have hxj : 0 < x (5 : Fin 7) := by
    have := abs_le.1 (hdev (5 : Fin 7)); have := hp1 (5 : Fin 7); norm_num at hε ⊢; linarith
  have e1 : mxOf x EXs hEXne (0 : Fin 4) = (((0 : ℤ) : ℝ) + 1 / 8) / x (2 : Fin 7) := by
    unfold mxOf; exact sup'_of_eq_singleton _ _ _ EX0 _
  have e2 : mnOf x ENs hENne (0 : Fin 4) = (((1 : ℤ) : ℝ) - 1 / 8) / x (5 : Fin 7) := by
    unfold mnOf; exact inf'_of_eq_singleton _ _ _ EN0 _
  have e3 : mxOf x EXs hEXne (3 : Fin 4) = (((6 : ℤ) : ℝ) + 1 / 8) / x (5 : Fin 7) := by
    unfold mxOf; exact sup'_of_eq_singleton _ _ _ EX3 _
  have e4 : mnOf x ENs hENne (3 : Fin 4) = (((1 : ℤ) : ℝ) - 1 / 8) / x (2 : Fin 7) := by
    unfold mnOf; exact inf'_of_eq_singleton _ _ _ EN3 _
  rcases le_total ((((0 : ℤ) : ℝ) + 1 / 8) * x (5 : Fin 7)) ((((1 : ℤ) : ℝ) - 1 / 8) * x (2 : Fin 7)) with h | h
  · refine ⟨(0 : Fin 4), ?_⟩
    unfold Alive; rw [e1, e2, div_le_div_iff₀ hxi hxj]; linarith
  · refine ⟨(3 : Fin 4), ?_⟩
    unfold Alive; rw [e3, e4, div_le_div_iff₀ hxj hxi]; norm_num at h ⊢; linarith

theorem inst (x : Fin 7 → ℝ) (ε : ℝ) (hε : ε ≤ (1 / 5376 : ℝ)) (hdev : ∀ i, |x i - pr i| ≤ ε) :
    ∃ c₀ : Fin 4, Alive (mxOf x EXs hEXne) (mnOf x ENs hENne) c₀ ∧
      (∀ c, c < c₀ → ¬ Alive (mxOf x EXs hEXne) (mnOf x ENs hENne) c) ∧
      IsLeast {t : ℝ | 0 < t ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)} (mxOf x EXs hEXne c₀) :=
  landing_cert_alive 4 (12 : ℝ) (by norm_num) pr x hp ε hdev aV bV dV TV ZV hab hd0 hdP haP hT hZ (hE ε hε) hcls EXs ENs hEXne hENne
    hEXdef hENdef hsepL HV hHL (cov x ε hε hdev) (hexl x ε hε hdev)

noncomputable def sv : Fin 8 → ℝ := ![(1 : ℝ), (2 : ℝ), (4 : ℝ), (5 : ℝ), (8 : ℝ), (9 : ℝ), (11 : ℝ), (16 : ℝ)]
def sg : Fin 7 → Fin 8 := ![0, 1, 3, 4, 5, 6, 7]

theorem sv_0 : sv (0 : Fin 8) = (1 : ℝ) := rfl
theorem sv_1 : sv (1 : Fin 8) = (2 : ℝ) := rfl
theorem sv_2 : sv (2 : Fin 8) = (4 : ℝ) := rfl
theorem sv_3 : sv (3 : Fin 8) = (5 : ℝ) := rfl
theorem sv_4 : sv (4 : Fin 8) = (8 : ℝ) := rfl
theorem sv_5 : sv (5 : Fin 8) = (9 : ℝ) := rfl
theorem sv_6 : sv (6 : Fin 8) = (11 : ℝ) := rfl
theorem sv_7 : sv (7 : Fin 8) = (16 : ℝ) := rfl
theorem sg_0 : sg (0 : Fin 7) = (0 : Fin 8) := rfl
theorem sg_1 : sg (1 : Fin 7) = (1 : Fin 8) := rfl
theorem sg_2 : sg (2 : Fin 7) = (3 : Fin 8) := rfl
theorem sg_3 : sg (3 : Fin 7) = (4 : Fin 8) := rfl
theorem sg_4 : sg (4 : Fin 7) = (5 : Fin 8) := rfl
theorem sg_5 : sg (5 : Fin 7) = (6 : Fin 8) := rfl
theorem sg_6 : sg (6 : Fin 7) = (7 : Fin 8) := rfl

theorem inst_arr (v : Fin 8 → ℝ) (η : ℝ) (hη : η ≤ (1 / 10752 : ℝ)) (hv : ∀ j, |v j - sv j| ≤ η) :
    ∃ c₀ : Fin 4, Alive (mxOf (fun i => |v (sg i) - v (2 : Fin 8)|) EXs hEXne) (mnOf (fun i => |v (sg i) - v (2 : Fin 8)|) ENs hENne) c₀ ∧
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

end Fresh.CertRS.R06994



/-!
# Landing certificate `CertRS.R06995`: speeds (1, 2, 4, 5, 8, 9, 11, 16), subject index 3

Generated 2026-10-24 by `experiments/n8/cert_gen_v1.py` (exact Fractions).  Baseline readings [4, 3, 1, 3, 4, 6, 11].  Components up to the first wide one: 1.
Radius: speeds within `η ≤ 1/3520` of the baseline speeds, giving `ε = 2η ≤ 1/1760`.  Covering margin `μ = 1/128`.
`hcov` is **[PROVISIONAL: covering]**, supporting the claim that the first lonely instant of this subject is the largest exit of the first alive component.
Result `inst_arr`: for such `v`, the subject has a first isolation (a least element over all `t > 0`).  Grades: [L].
-/

open Classical

namespace Fresh.CertRS.R06995

open Fresh Fresh.LandingCert Fresh.LandingRule

noncomputable def pr : Fin 7 → ℝ := ![(4 : ℝ), (3 : ℝ), (1 : ℝ), (3 : ℝ), (4 : ℝ), (6 : ℝ), (11 : ℝ)]
noncomputable def aV : Fin 1 → ℝ := ![(1 / 8 : ℝ)]
noncomputable def bV : Fin 1 → ℝ := ![(7 / 48 : ℝ)]
noncomputable def dV : Fin 1 → ℝ := ![(1 / 44 : ℝ)]
noncomputable def TV : Fin 1 → ℝ := ![(89 / 528 : ℝ)]
def ZV : Fin 1 → ℤ := ![4]
noncomputable def HV : ℝ := (83 / 528 : ℝ)
noncomputable def EXs (c : Fin 1) : Finset (Fin 7 × ℤ) :=
  (Finset.univ ×ˢ Finset.Icc 0 (ZV c)).filter (fun q => ((q.2 : ℝ) + 1 / 8) / pr q.1 = aV c)
noncomputable def ENs (c : Fin 1) : Finset (Fin 7 × ℤ) :=
  (Finset.univ ×ˢ Finset.Icc 0 (ZV c)).filter (fun q => ((q.2 : ℝ) - 1 / 8) / pr q.1 = bV c)

theorem hp : ∀ i, 1 ≤ pr i ∧ pr i ≤ (11 : ℝ) := by intro i; fin_cases i <;> norm_num [pr]
theorem hp1 : ∀ i, 1 ≤ pr i := fun i => (hp i).1
theorem pr_0 : pr (0 : Fin 7) = (4 : ℝ) := rfl
theorem pr_1 : pr (1 : Fin 7) = (3 : ℝ) := rfl
theorem pr_2 : pr (2 : Fin 7) = (1 : ℝ) := rfl
theorem pr_3 : pr (3 : Fin 7) = (3 : ℝ) := rfl
theorem pr_4 : pr (4 : Fin 7) = (4 : ℝ) := rfl
theorem pr_5 : pr (5 : Fin 7) = (6 : ℝ) := rfl
theorem pr_6 : pr (6 : Fin 7) = (11 : ℝ) := rfl
theorem aV_0 : aV (0 : Fin 1) = (1 / 8 : ℝ) := rfl
theorem bV_0 : bV (0 : Fin 1) = (7 / 48 : ℝ) := rfl
theorem dV_0 : dV (0 : Fin 1) = (1 / 44 : ℝ) := rfl
theorem TV_0 : TV (0 : Fin 1) = (89 / 528 : ℝ) := rfl
theorem ZV_0 : ZV (0 : Fin 1) = (4 : ℤ) := rfl
theorem hab : ∀ c, aV c ≤ bV c := by intro c; fin_cases c <;> norm_num [aV, bV]
theorem hd0 : ∀ c, 0 < dV c := by intro c; fin_cases c <;> norm_num [dV]
theorem hdP : ∀ c, dV c ≤ 1 / (4 * (11 : ℝ)) := by intro c; fin_cases c <;> norm_num [dV]
theorem haP : ∀ c, dV c < aV c := by intro c; fin_cases c <;> norm_num [dV, aV]
theorem hT : ∀ c, bV c + dV c ≤ TV c := by intro c; fin_cases c <;> norm_num [bV, dV, TV]
theorem hZ : ∀ c, ((11 : ℝ) + 1) * TV c + 1 ≤ (ZV c : ℝ) := by intro c; fin_cases c <;> norm_num [TV, ZV]
theorem hE (ε : ℝ) (hε : ε ≤ (1 / 1760 : ℝ)) : ∀ c, 8 * ((ZV c : ℝ) + 1) * ε ≤ dV c := by
  intro c; fin_cases c <;> norm_num [ZV, dV] <;> linarith
theorem hcls : ∀ c i, ∀ z : ℤ, 0 ≤ z → z ≤ ZV c →
    ((z : ℝ) + 1 / 8) / pr i ≤ aV c - dV c ∨ bV c + dV c ≤ ((z : ℝ) - 1 / 8) / pr i ∨
      ((z : ℝ) + 1 / 8) / pr i = aV c ∨ ((z : ℝ) - 1 / 8) / pr i = bV c := by
  intro c i z h0 h1
  fin_cases c <;> fin_cases i <;> simp [ZV] at h1 <;> interval_cases z <;> norm_num [pr, aV, bV, dV]
theorem hEXne : ∀ c, (EXs c).Nonempty := by
  intro c
  fin_cases c
  · exact ⟨(2, 0), by simp [EXs, ZV, pr, aV] <;> norm_num⟩
theorem hENne : ∀ c, (ENs c).Nonempty := by
  intro c
  fin_cases c
  · exact ⟨(5, 1), by simp [ENs, ZV, pr, bV] <;> norm_num⟩
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

theorem gap0 (x : Fin 7 → ℝ) (ε : ℝ) (hdev : ∀ i, |x i - pr i| ≤ ε) (hεH : ε * HV ≤ (1 / 128 : ℝ) / 2) (t : ℝ) (h0 : 0 ≤ t)
    (hHt : t ≤ HV) (h1 : (0 : ℝ) ≤ t) (h2 : t ≤ (5 / 44 : ℝ)) (hlon : ∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)) : False := by
  exact zone_kill_gen pr x ε HV (1 / 128 : ℝ) hp1 hdev hεH (by norm_num) (2 : Fin 7) 0 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (2 : Fin 7))
theorem cov (x : Fin 7 → ℝ) (ε : ℝ) (hε : ε ≤ (1 / 1760 : ℝ)) (hdev : ∀ i, |x i - pr i| ≤ ε) :
    ∀ t : ℝ, 0 < t → t ≤ HV → (∀ c, ¬ (aV c - dV c / 2 ≤ t ∧ t ≤ bV c + dV c / 2)) →
      ¬ (∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)) := by
  intro t h0 hHt hnone hlon
  have hεH : ε * HV ≤ (1 / 128 : ℝ) / 2 := by
    have hε0 : 0 ≤ ε := le_trans (abs_nonneg _) (hdev 0)
    have : ε * HV ≤ (1 / 1760 : ℝ) * HV := mul_le_mul_of_nonneg_right hε (by norm_num [HV])
    have h2 : (1 / 1760 : ℝ) * HV ≤ (1 / 128 : ℝ) / 2 := by norm_num [HV]
    linarith
  have n0 := hnone (0 : Fin 1)
  rw [aV_0, bV_0, dV_0] at n0
  rcases lt_or_ge t (5 / 44 : ℝ) with c0 | c0
  · exact gap0 x ε hdev hεH t h0.le hHt h0.le (by linarith) hlon
  have d0 : (83 / 528 : ℝ) < t := by
    by_contra hc; push Not at hc; exact n0 ⟨by linarith, by linarith⟩
  have hHv : HV = (83 / 528 : ℝ) := rfl
  exact absurd (by linarith : t ≤ (83 / 528 : ℝ)) (not_le.2 d0)

theorem inst (x : Fin 7 → ℝ) (ε : ℝ) (hε : ε ≤ (1 / 1760 : ℝ)) (hdev : ∀ i, |x i - pr i| ≤ ε) :
    ∃ c₀ : Fin 1, Alive (mxOf x EXs hEXne) (mnOf x ENs hENne) c₀ ∧
      (∀ c, c < c₀ → ¬ Alive (mxOf x EXs hEXne) (mnOf x ENs hENne) c) ∧
      IsLeast {t : ℝ | 0 < t ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)} (mxOf x EXs hEXne c₀) :=
  landing_cert 1 (11 : ℝ) (by norm_num) pr x hp ε hdev aV bV dV TV ZV hab hd0 hdP haP hT hZ (hE ε hε) hcls EXs ENs hEXne hENne
    hEXdef hENdef hsepL HV hHL (cov x ε hε hdev) (0 : Fin 1) (by rw [dV_0, bV_0, aV_0]; norm_num)

noncomputable def sv : Fin 8 → ℝ := ![(1 : ℝ), (2 : ℝ), (4 : ℝ), (5 : ℝ), (8 : ℝ), (9 : ℝ), (11 : ℝ), (16 : ℝ)]
def sg : Fin 7 → Fin 8 := ![0, 1, 2, 4, 5, 6, 7]

theorem sv_0 : sv (0 : Fin 8) = (1 : ℝ) := rfl
theorem sv_1 : sv (1 : Fin 8) = (2 : ℝ) := rfl
theorem sv_2 : sv (2 : Fin 8) = (4 : ℝ) := rfl
theorem sv_3 : sv (3 : Fin 8) = (5 : ℝ) := rfl
theorem sv_4 : sv (4 : Fin 8) = (8 : ℝ) := rfl
theorem sv_5 : sv (5 : Fin 8) = (9 : ℝ) := rfl
theorem sv_6 : sv (6 : Fin 8) = (11 : ℝ) := rfl
theorem sv_7 : sv (7 : Fin 8) = (16 : ℝ) := rfl
theorem sg_0 : sg (0 : Fin 7) = (0 : Fin 8) := rfl
theorem sg_1 : sg (1 : Fin 7) = (1 : Fin 8) := rfl
theorem sg_2 : sg (2 : Fin 7) = (2 : Fin 8) := rfl
theorem sg_3 : sg (3 : Fin 7) = (4 : Fin 8) := rfl
theorem sg_4 : sg (4 : Fin 7) = (5 : Fin 8) := rfl
theorem sg_5 : sg (5 : Fin 7) = (6 : Fin 8) := rfl
theorem sg_6 : sg (6 : Fin 7) = (7 : Fin 8) := rfl

theorem inst_arr (v : Fin 8 → ℝ) (η : ℝ) (hη : η ≤ (1 / 3520 : ℝ)) (hv : ∀ j, |v j - sv j| ≤ η) :
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

end Fresh.CertRS.R06995



/-!
# Landing certificate `CertRS.R06996`: speeds (1, 2, 4, 5, 8, 9, 11, 16), subject index 4

Generated 2026-10-24 by `experiments/n8/cert_gen_v1.py` (exact Fractions).  Baseline readings [7, 6, 4, 3, 1, 3, 8].  Components up to the first wide one: 1.
Radius: speeds within `η ≤ 1/5120` of the baseline speeds, giving `ε = 2η ≤ 1/2560`.  Covering margin `μ = 1/256`.
`hcov` is **[PROVISIONAL: covering]**, supporting the claim that the first lonely instant of this subject is the largest exit of the first alive component.
Result `inst_arr`: for such `v`, the subject has a first isolation (a least element over all `t > 0`).  Grades: [L].
-/

open Classical

namespace Fresh.CertRS.R06996

open Fresh Fresh.LandingCert Fresh.LandingRule

noncomputable def pr : Fin 7 → ℝ := ![(7 : ℝ), (6 : ℝ), (4 : ℝ), (3 : ℝ), (1 : ℝ), (3 : ℝ), (8 : ℝ)]
noncomputable def aV : Fin 1 → ℝ := ![(3 / 16 : ℝ)]
noncomputable def bV : Fin 1 → ℝ := ![(7 / 32 : ℝ)]
noncomputable def dV : Fin 1 → ℝ := ![(1 / 64 : ℝ)]
noncomputable def TV : Fin 1 → ℝ := ![(15 / 64 : ℝ)]
def ZV : Fin 1 → ℤ := ![4]
noncomputable def HV : ℝ := (29 / 128 : ℝ)
noncomputable def EXs (c : Fin 1) : Finset (Fin 7 × ℤ) :=
  (Finset.univ ×ˢ Finset.Icc 0 (ZV c)).filter (fun q => ((q.2 : ℝ) + 1 / 8) / pr q.1 = aV c)
noncomputable def ENs (c : Fin 1) : Finset (Fin 7 × ℤ) :=
  (Finset.univ ×ˢ Finset.Icc 0 (ZV c)).filter (fun q => ((q.2 : ℝ) - 1 / 8) / pr q.1 = bV c)

theorem hp : ∀ i, 1 ≤ pr i ∧ pr i ≤ (8 : ℝ) := by intro i; fin_cases i <;> norm_num [pr]
theorem hp1 : ∀ i, 1 ≤ pr i := fun i => (hp i).1
theorem pr_0 : pr (0 : Fin 7) = (7 : ℝ) := rfl
theorem pr_1 : pr (1 : Fin 7) = (6 : ℝ) := rfl
theorem pr_2 : pr (2 : Fin 7) = (4 : ℝ) := rfl
theorem pr_3 : pr (3 : Fin 7) = (3 : ℝ) := rfl
theorem pr_4 : pr (4 : Fin 7) = (1 : ℝ) := rfl
theorem pr_5 : pr (5 : Fin 7) = (3 : ℝ) := rfl
theorem pr_6 : pr (6 : Fin 7) = (8 : ℝ) := rfl
theorem aV_0 : aV (0 : Fin 1) = (3 / 16 : ℝ) := rfl
theorem bV_0 : bV (0 : Fin 1) = (7 / 32 : ℝ) := rfl
theorem dV_0 : dV (0 : Fin 1) = (1 / 64 : ℝ) := rfl
theorem TV_0 : TV (0 : Fin 1) = (15 / 64 : ℝ) := rfl
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

theorem gap0 (x : Fin 7 → ℝ) (ε : ℝ) (hdev : ∀ i, |x i - pr i| ≤ ε) (hεH : ε * HV ≤ (1 / 256 : ℝ) / 2) (t : ℝ) (h0 : 0 ≤ t)
    (hHt : t ≤ HV) (h1 : (0 : ℝ) ≤ t) (h2 : t ≤ (23 / 128 : ℝ)) (hlon : ∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)) : False := by
  rcases le_total t (31 / 256 : ℝ) with hs0 | hs0
  · exact zone_kill_gen pr x ε HV (1 / 256 : ℝ) hp1 hdev hεH (by norm_num) (4 : Fin 7) 0 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (4 : Fin 7))
  rcases le_total t (35 / 256 : ℝ) with hs1 | hs1
  · exact zone_kill_gen pr x ε HV (1 / 256 : ℝ) hp1 hdev hεH (by norm_num) (6 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (6 : Fin 7))
  rcases le_total t (281 / 1792 : ℝ) with hs2 | hs2
  · exact zone_kill_gen pr x ε HV (1 / 256 : ℝ) hp1 hdev hεH (by norm_num) (0 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (0 : Fin 7))
  exact zone_kill_gen pr x ε HV (1 / 256 : ℝ) hp1 hdev hεH (by norm_num) (1 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (1 : Fin 7))
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
  rcases lt_or_ge t (23 / 128 : ℝ) with c0 | c0
  · exact gap0 x ε hdev hεH t h0.le hHt h0.le (by linarith) hlon
  have d0 : (29 / 128 : ℝ) < t := by
    by_contra hc; push Not at hc; exact n0 ⟨by linarith, by linarith⟩
  have hHv : HV = (29 / 128 : ℝ) := rfl
  exact absurd (by linarith : t ≤ (29 / 128 : ℝ)) (not_le.2 d0)

theorem inst (x : Fin 7 → ℝ) (ε : ℝ) (hε : ε ≤ (1 / 2560 : ℝ)) (hdev : ∀ i, |x i - pr i| ≤ ε) :
    ∃ c₀ : Fin 1, Alive (mxOf x EXs hEXne) (mnOf x ENs hENne) c₀ ∧
      (∀ c, c < c₀ → ¬ Alive (mxOf x EXs hEXne) (mnOf x ENs hENne) c) ∧
      IsLeast {t : ℝ | 0 < t ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)} (mxOf x EXs hEXne c₀) :=
  landing_cert 1 (8 : ℝ) (by norm_num) pr x hp ε hdev aV bV dV TV ZV hab hd0 hdP haP hT hZ (hE ε hε) hcls EXs ENs hEXne hENne
    hEXdef hENdef hsepL HV hHL (cov x ε hε hdev) (0 : Fin 1) (by rw [dV_0, bV_0, aV_0]; norm_num)

noncomputable def sv : Fin 8 → ℝ := ![(1 : ℝ), (2 : ℝ), (4 : ℝ), (5 : ℝ), (8 : ℝ), (9 : ℝ), (11 : ℝ), (16 : ℝ)]
def sg : Fin 7 → Fin 8 := ![0, 1, 2, 3, 5, 6, 7]

theorem sv_0 : sv (0 : Fin 8) = (1 : ℝ) := rfl
theorem sv_1 : sv (1 : Fin 8) = (2 : ℝ) := rfl
theorem sv_2 : sv (2 : Fin 8) = (4 : ℝ) := rfl
theorem sv_3 : sv (3 : Fin 8) = (5 : ℝ) := rfl
theorem sv_4 : sv (4 : Fin 8) = (8 : ℝ) := rfl
theorem sv_5 : sv (5 : Fin 8) = (9 : ℝ) := rfl
theorem sv_6 : sv (6 : Fin 8) = (11 : ℝ) := rfl
theorem sv_7 : sv (7 : Fin 8) = (16 : ℝ) := rfl
theorem sg_0 : sg (0 : Fin 7) = (0 : Fin 8) := rfl
theorem sg_1 : sg (1 : Fin 7) = (1 : Fin 8) := rfl
theorem sg_2 : sg (2 : Fin 7) = (2 : Fin 8) := rfl
theorem sg_3 : sg (3 : Fin 7) = (3 : Fin 8) := rfl
theorem sg_4 : sg (4 : Fin 7) = (5 : Fin 8) := rfl
theorem sg_5 : sg (5 : Fin 7) = (6 : Fin 8) := rfl
theorem sg_6 : sg (6 : Fin 7) = (7 : Fin 8) := rfl

theorem inst_arr (v : Fin 8 → ℝ) (η : ℝ) (hη : η ≤ (1 / 5120 : ℝ)) (hv : ∀ j, |v j - sv j| ≤ η) :
    ∃ c₀ : Fin 1, Alive (mxOf (fun i => |v (sg i) - v (4 : Fin 8)|) EXs hEXne) (mnOf (fun i => |v (sg i) - v (4 : Fin 8)|) ENs hENne) c₀ ∧
      (∀ c, c < c₀ → ¬ Alive (mxOf (fun i => |v (sg i) - v (4 : Fin 8)|) EXs hEXne) (mnOf (fun i => |v (sg i) - v (4 : Fin 8)|) ENs hENne) c) ∧
      IsLeast {t : ℝ | 0 < t ∧ IsolatedAt v (4 : Fin 8) t} (mxOf (fun i => |v (sg i) - v (4 : Fin 8)|) EXs hEXne c₀) := by
  have hσk : ∀ i, sg i ≠ (4 : Fin 8) := by decide
  have hσ : ∀ j : Fin 8, j ≠ (4 : Fin 8) → ∃ i, sg i = j := by decide
  have hpr : ∀ i, pr i = |sv (sg i) - sv (4 : Fin 8)| := by
    intro i; rcases fin7_cases i with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6, sv_0, sv_1, sv_2, sv_3, sv_4, sv_5, sv_6, sv_7, sg_0, sg_1, sg_2, sg_3, sg_4, sg_5, sg_6]
  have hdev : ∀ i, |(|v (sg i) - v (4 : Fin 8)| - pr i)| ≤ 2 * η := by
    intro i; rw [hpr i]; exact reading_dev v sv η hv (sg i) (4 : Fin 8)
  obtain ⟨c₀, hal, hbf, hT0⟩ := inst (fun i => |v (sg i) - v (4 : Fin 8)|) (2 * η) (by linarith) hdev
  have hset : {t : ℝ | 0 < t ∧ IsolatedAt v (4 : Fin 8) t} =
      {t : ℝ | 0 < t ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (|v (sg i) - v (4 : Fin 8)| * t)} := by
    ext t; simp only [Set.mem_setOf_eq]; rw [iso_iff_readings v (4 : Fin 8) sg hσk hσ t]
  rw [hset]; exact ⟨c₀, hal, hbf, hT0⟩

#print axioms inst_arr

end Fresh.CertRS.R06996



/-!
# Landing certificate `CertRS.R06997`: speeds (1, 2, 4, 5, 8, 9, 11, 16), subject index 5

Generated 2026-10-24 by `experiments/n8/cert_gen_v1.py` (exact Fractions).  Baseline readings [8, 7, 5, 4, 1, 2, 7].  Components up to the first wide one: 1.
Radius: speeds within `η ≤ 1/3186` of the baseline speeds, giving `ε = 2η ≤ 1/1593`.  Covering margin `μ = 1/128`.
`hcov` is **[PROVISIONAL: covering]**, supporting the claim that the first lonely instant of this subject is the largest exit of the first alive component.
Result `inst_arr`: for such `v`, the subject has a first isolation (a least element over all `t > 0`).  Grades: [L].
-/

open Classical

namespace Fresh.CertRS.R06997

open Fresh Fresh.LandingCert Fresh.LandingRule

noncomputable def pr : Fin 7 → ℝ := ![(8 : ℝ), (7 : ℝ), (5 : ℝ), (4 : ℝ), (1 : ℝ), (2 : ℝ), (7 : ℝ)]
noncomputable def aV : Fin 1 → ℝ := ![(9 / 56 : ℝ)]
noncomputable def bV : Fin 1 → ℝ := ![(7 / 40 : ℝ)]
noncomputable def dV : Fin 1 → ℝ := ![(9 / 448 : ℝ)]
noncomputable def TV : Fin 1 → ℝ := ![(437 / 2240 : ℝ)]
def ZV : Fin 1 → ℤ := ![3]
noncomputable def HV : ℝ := (829 / 4480 : ℝ)
noncomputable def EXs (c : Fin 1) : Finset (Fin 7 × ℤ) :=
  (Finset.univ ×ˢ Finset.Icc 0 (ZV c)).filter (fun q => ((q.2 : ℝ) + 1 / 8) / pr q.1 = aV c)
noncomputable def ENs (c : Fin 1) : Finset (Fin 7 × ℤ) :=
  (Finset.univ ×ˢ Finset.Icc 0 (ZV c)).filter (fun q => ((q.2 : ℝ) - 1 / 8) / pr q.1 = bV c)

theorem hp : ∀ i, 1 ≤ pr i ∧ pr i ≤ (8 : ℝ) := by intro i; fin_cases i <;> norm_num [pr]
theorem hp1 : ∀ i, 1 ≤ pr i := fun i => (hp i).1
theorem pr_0 : pr (0 : Fin 7) = (8 : ℝ) := rfl
theorem pr_1 : pr (1 : Fin 7) = (7 : ℝ) := rfl
theorem pr_2 : pr (2 : Fin 7) = (5 : ℝ) := rfl
theorem pr_3 : pr (3 : Fin 7) = (4 : ℝ) := rfl
theorem pr_4 : pr (4 : Fin 7) = (1 : ℝ) := rfl
theorem pr_5 : pr (5 : Fin 7) = (2 : ℝ) := rfl
theorem pr_6 : pr (6 : Fin 7) = (7 : ℝ) := rfl
theorem aV_0 : aV (0 : Fin 1) = (9 / 56 : ℝ) := rfl
theorem bV_0 : bV (0 : Fin 1) = (7 / 40 : ℝ) := rfl
theorem dV_0 : dV (0 : Fin 1) = (9 / 448 : ℝ) := rfl
theorem TV_0 : TV (0 : Fin 1) = (437 / 2240 : ℝ) := rfl
theorem ZV_0 : ZV (0 : Fin 1) = (3 : ℤ) := rfl
theorem hab : ∀ c, aV c ≤ bV c := by intro c; fin_cases c <;> norm_num [aV, bV]
theorem hd0 : ∀ c, 0 < dV c := by intro c; fin_cases c <;> norm_num [dV]
theorem hdP : ∀ c, dV c ≤ 1 / (4 * (8 : ℝ)) := by intro c; fin_cases c <;> norm_num [dV]
theorem haP : ∀ c, dV c < aV c := by intro c; fin_cases c <;> norm_num [dV, aV]
theorem hT : ∀ c, bV c + dV c ≤ TV c := by intro c; fin_cases c <;> norm_num [bV, dV, TV]
theorem hZ : ∀ c, ((8 : ℝ) + 1) * TV c + 1 ≤ (ZV c : ℝ) := by intro c; fin_cases c <;> norm_num [TV, ZV]
theorem hE (ε : ℝ) (hε : ε ≤ (1 / 1593 : ℝ)) : ∀ c, 8 * ((ZV c : ℝ) + 1) * ε ≤ dV c := by
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

theorem gap0 (x : Fin 7 → ℝ) (ε : ℝ) (hdev : ∀ i, |x i - pr i| ≤ ε) (hεH : ε * HV ≤ (1 / 128 : ℝ) / 2) (t : ℝ) (h0 : 0 ≤ t)
    (hHt : t ≤ HV) (h1 : (0 : ℝ) ≤ t) (h2 : t ≤ (135 / 896 : ℝ)) (hlon : ∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)) : False := by
  rcases le_total t (15 / 128 : ℝ) with hs0 | hs0
  · exact zone_kill_gen pr x ε HV (1 / 128 : ℝ) hp1 hdev hεH (by norm_num) (4 : Fin 7) 0 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (4 : Fin 7))
  rcases le_total t (17 / 128 : ℝ) with hs1 | hs1
  · exact zone_kill_gen pr x ε HV (1 / 128 : ℝ) hp1 hdev hεH (by norm_num) (0 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (0 : Fin 7))
  exact zone_kill_gen pr x ε HV (1 / 128 : ℝ) hp1 hdev hεH (by norm_num) (1 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (1 : Fin 7))
theorem cov (x : Fin 7 → ℝ) (ε : ℝ) (hε : ε ≤ (1 / 1593 : ℝ)) (hdev : ∀ i, |x i - pr i| ≤ ε) :
    ∀ t : ℝ, 0 < t → t ≤ HV → (∀ c, ¬ (aV c - dV c / 2 ≤ t ∧ t ≤ bV c + dV c / 2)) →
      ¬ (∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)) := by
  intro t h0 hHt hnone hlon
  have hεH : ε * HV ≤ (1 / 128 : ℝ) / 2 := by
    have hε0 : 0 ≤ ε := le_trans (abs_nonneg _) (hdev 0)
    have : ε * HV ≤ (1 / 1593 : ℝ) * HV := mul_le_mul_of_nonneg_right hε (by norm_num [HV])
    have h2 : (1 / 1593 : ℝ) * HV ≤ (1 / 128 : ℝ) / 2 := by norm_num [HV]
    linarith
  have n0 := hnone (0 : Fin 1)
  rw [aV_0, bV_0, dV_0] at n0
  rcases lt_or_ge t (135 / 896 : ℝ) with c0 | c0
  · exact gap0 x ε hdev hεH t h0.le hHt h0.le (by linarith) hlon
  have d0 : (829 / 4480 : ℝ) < t := by
    by_contra hc; push Not at hc; exact n0 ⟨by linarith, by linarith⟩
  have hHv : HV = (829 / 4480 : ℝ) := rfl
  exact absurd (by linarith : t ≤ (829 / 4480 : ℝ)) (not_le.2 d0)

theorem inst (x : Fin 7 → ℝ) (ε : ℝ) (hε : ε ≤ (1 / 1593 : ℝ)) (hdev : ∀ i, |x i - pr i| ≤ ε) :
    ∃ c₀ : Fin 1, Alive (mxOf x EXs hEXne) (mnOf x ENs hENne) c₀ ∧
      (∀ c, c < c₀ → ¬ Alive (mxOf x EXs hEXne) (mnOf x ENs hENne) c) ∧
      IsLeast {t : ℝ | 0 < t ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)} (mxOf x EXs hEXne c₀) :=
  landing_cert 1 (8 : ℝ) (by norm_num) pr x hp ε hdev aV bV dV TV ZV hab hd0 hdP haP hT hZ (hE ε hε) hcls EXs ENs hEXne hENne
    hEXdef hENdef hsepL HV hHL (cov x ε hε hdev) (0 : Fin 1) (by rw [dV_0, bV_0, aV_0]; norm_num)

noncomputable def sv : Fin 8 → ℝ := ![(1 : ℝ), (2 : ℝ), (4 : ℝ), (5 : ℝ), (8 : ℝ), (9 : ℝ), (11 : ℝ), (16 : ℝ)]
def sg : Fin 7 → Fin 8 := ![0, 1, 2, 3, 4, 6, 7]

theorem sv_0 : sv (0 : Fin 8) = (1 : ℝ) := rfl
theorem sv_1 : sv (1 : Fin 8) = (2 : ℝ) := rfl
theorem sv_2 : sv (2 : Fin 8) = (4 : ℝ) := rfl
theorem sv_3 : sv (3 : Fin 8) = (5 : ℝ) := rfl
theorem sv_4 : sv (4 : Fin 8) = (8 : ℝ) := rfl
theorem sv_5 : sv (5 : Fin 8) = (9 : ℝ) := rfl
theorem sv_6 : sv (6 : Fin 8) = (11 : ℝ) := rfl
theorem sv_7 : sv (7 : Fin 8) = (16 : ℝ) := rfl
theorem sg_0 : sg (0 : Fin 7) = (0 : Fin 8) := rfl
theorem sg_1 : sg (1 : Fin 7) = (1 : Fin 8) := rfl
theorem sg_2 : sg (2 : Fin 7) = (2 : Fin 8) := rfl
theorem sg_3 : sg (3 : Fin 7) = (3 : Fin 8) := rfl
theorem sg_4 : sg (4 : Fin 7) = (4 : Fin 8) := rfl
theorem sg_5 : sg (5 : Fin 7) = (6 : Fin 8) := rfl
theorem sg_6 : sg (6 : Fin 7) = (7 : Fin 8) := rfl

theorem inst_arr (v : Fin 8 → ℝ) (η : ℝ) (hη : η ≤ (1 / 3186 : ℝ)) (hv : ∀ j, |v j - sv j| ≤ η) :
    ∃ c₀ : Fin 1, Alive (mxOf (fun i => |v (sg i) - v (5 : Fin 8)|) EXs hEXne) (mnOf (fun i => |v (sg i) - v (5 : Fin 8)|) ENs hENne) c₀ ∧
      (∀ c, c < c₀ → ¬ Alive (mxOf (fun i => |v (sg i) - v (5 : Fin 8)|) EXs hEXne) (mnOf (fun i => |v (sg i) - v (5 : Fin 8)|) ENs hENne) c) ∧
      IsLeast {t : ℝ | 0 < t ∧ IsolatedAt v (5 : Fin 8) t} (mxOf (fun i => |v (sg i) - v (5 : Fin 8)|) EXs hEXne c₀) := by
  have hσk : ∀ i, sg i ≠ (5 : Fin 8) := by decide
  have hσ : ∀ j : Fin 8, j ≠ (5 : Fin 8) → ∃ i, sg i = j := by decide
  have hpr : ∀ i, pr i = |sv (sg i) - sv (5 : Fin 8)| := by
    intro i; rcases fin7_cases i with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6, sv_0, sv_1, sv_2, sv_3, sv_4, sv_5, sv_6, sv_7, sg_0, sg_1, sg_2, sg_3, sg_4, sg_5, sg_6]
  have hdev : ∀ i, |(|v (sg i) - v (5 : Fin 8)| - pr i)| ≤ 2 * η := by
    intro i; rw [hpr i]; exact reading_dev v sv η hv (sg i) (5 : Fin 8)
  obtain ⟨c₀, hal, hbf, hT0⟩ := inst (fun i => |v (sg i) - v (5 : Fin 8)|) (2 * η) (by linarith) hdev
  have hset : {t : ℝ | 0 < t ∧ IsolatedAt v (5 : Fin 8) t} =
      {t : ℝ | 0 < t ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (|v (sg i) - v (5 : Fin 8)| * t)} := by
    ext t; simp only [Set.mem_setOf_eq]; rw [iso_iff_readings v (5 : Fin 8) sg hσk hσ t]
  rw [hset]; exact ⟨c₀, hal, hbf, hT0⟩

#print axioms inst_arr

end Fresh.CertRS.R06997



/-!
# Landing certificate `CertRS.R06998`: speeds (1, 2, 4, 5, 8, 9, 11, 16), subject index 6

Generated 2026-10-24 by `experiments/n8/cert_gen_v1.py` (exact Fractions).  Baseline readings [10, 9, 7, 6, 3, 2, 5].  Components up to the first wide one: 1.
Radius: speeds within `η ≤ 1/6584` of the baseline speeds, giving `ε = 2η ≤ 1/3292`.  Covering margin `μ = 1/256`.
`hcov` is **[PROVISIONAL: covering]**, supporting the claim that the first lonely instant of this subject is the largest exit of the first alive component.
Result `inst_arr`: for such `v`, the subject has a first isolation (a least element over all `t > 0`).  Grades: [L].
-/

open Classical

namespace Fresh.CertRS.R06998

open Fresh Fresh.LandingCert Fresh.LandingRule

noncomputable def pr : Fin 7 → ℝ := ![(10 : ℝ), (9 : ℝ), (7 : ℝ), (6 : ℝ), (3 : ℝ), (2 : ℝ), (5 : ℝ)]
noncomputable def aV : Fin 1 → ℝ := ![(1 / 16 : ℝ)]
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
theorem pr_0 : pr (0 : Fin 7) = (10 : ℝ) := rfl
theorem pr_1 : pr (1 : Fin 7) = (9 : ℝ) := rfl
theorem pr_2 : pr (2 : Fin 7) = (7 : ℝ) := rfl
theorem pr_3 : pr (3 : Fin 7) = (6 : ℝ) := rfl
theorem pr_4 : pr (4 : Fin 7) = (3 : ℝ) := rfl
theorem pr_5 : pr (5 : Fin 7) = (2 : ℝ) := rfl
theorem pr_6 : pr (6 : Fin 7) = (5 : ℝ) := rfl
theorem aV_0 : aV (0 : Fin 1) = (1 / 16 : ℝ) := rfl
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
  · exact ⟨(5, 0), by simp [EXs, ZV, pr, aV] <;> norm_num⟩
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

theorem gap0 (x : Fin 7 → ℝ) (ε : ℝ) (hdev : ∀ i, |x i - pr i| ≤ ε) (hεH : ε * HV ≤ (1 / 256 : ℝ) / 2) (t : ℝ) (h0 : 0 ≤ t)
    (hHt : t ≤ HV) (h1 : (0 : ℝ) ≤ t) (h2 : t ≤ (83 / 1440 : ℝ)) (hlon : ∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)) : False := by
  exact zone_kill_gen pr x ε HV (1 / 256 : ℝ) hp1 hdev hεH (by norm_num) (5 : Fin 7) 0 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (5 : Fin 7))
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
  rcases lt_or_ge t (83 / 1440 : ℝ) with c0 | c0
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

noncomputable def sv : Fin 8 → ℝ := ![(1 : ℝ), (2 : ℝ), (4 : ℝ), (5 : ℝ), (8 : ℝ), (9 : ℝ), (11 : ℝ), (16 : ℝ)]
def sg : Fin 7 → Fin 8 := ![0, 1, 2, 3, 4, 5, 7]

theorem sv_0 : sv (0 : Fin 8) = (1 : ℝ) := rfl
theorem sv_1 : sv (1 : Fin 8) = (2 : ℝ) := rfl
theorem sv_2 : sv (2 : Fin 8) = (4 : ℝ) := rfl
theorem sv_3 : sv (3 : Fin 8) = (5 : ℝ) := rfl
theorem sv_4 : sv (4 : Fin 8) = (8 : ℝ) := rfl
theorem sv_5 : sv (5 : Fin 8) = (9 : ℝ) := rfl
theorem sv_6 : sv (6 : Fin 8) = (11 : ℝ) := rfl
theorem sv_7 : sv (7 : Fin 8) = (16 : ℝ) := rfl
theorem sg_0 : sg (0 : Fin 7) = (0 : Fin 8) := rfl
theorem sg_1 : sg (1 : Fin 7) = (1 : Fin 8) := rfl
theorem sg_2 : sg (2 : Fin 7) = (2 : Fin 8) := rfl
theorem sg_3 : sg (3 : Fin 7) = (3 : Fin 8) := rfl
theorem sg_4 : sg (4 : Fin 7) = (4 : Fin 8) := rfl
theorem sg_5 : sg (5 : Fin 7) = (5 : Fin 8) := rfl
theorem sg_6 : sg (6 : Fin 7) = (7 : Fin 8) := rfl

theorem inst_arr (v : Fin 8 → ℝ) (η : ℝ) (hη : η ≤ (1 / 6584 : ℝ)) (hv : ∀ j, |v j - sv j| ≤ η) :
    ∃ c₀ : Fin 1, Alive (mxOf (fun i => |v (sg i) - v (6 : Fin 8)|) EXs hEXne) (mnOf (fun i => |v (sg i) - v (6 : Fin 8)|) ENs hENne) c₀ ∧
      (∀ c, c < c₀ → ¬ Alive (mxOf (fun i => |v (sg i) - v (6 : Fin 8)|) EXs hEXne) (mnOf (fun i => |v (sg i) - v (6 : Fin 8)|) ENs hENne) c) ∧
      IsLeast {t : ℝ | 0 < t ∧ IsolatedAt v (6 : Fin 8) t} (mxOf (fun i => |v (sg i) - v (6 : Fin 8)|) EXs hEXne c₀) := by
  have hσk : ∀ i, sg i ≠ (6 : Fin 8) := by decide
  have hσ : ∀ j : Fin 8, j ≠ (6 : Fin 8) → ∃ i, sg i = j := by decide
  have hpr : ∀ i, pr i = |sv (sg i) - sv (6 : Fin 8)| := by
    intro i; rcases fin7_cases i with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6, sv_0, sv_1, sv_2, sv_3, sv_4, sv_5, sv_6, sv_7, sg_0, sg_1, sg_2, sg_3, sg_4, sg_5, sg_6]
  have hdev : ∀ i, |(|v (sg i) - v (6 : Fin 8)| - pr i)| ≤ 2 * η := by
    intro i; rw [hpr i]; exact reading_dev v sv η hv (sg i) (6 : Fin 8)
  obtain ⟨c₀, hal, hbf, hT0⟩ := inst (fun i => |v (sg i) - v (6 : Fin 8)|) (2 * η) (by linarith) hdev
  have hset : {t : ℝ | 0 < t ∧ IsolatedAt v (6 : Fin 8) t} =
      {t : ℝ | 0 < t ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (|v (sg i) - v (6 : Fin 8)| * t)} := by
    ext t; simp only [Set.mem_setOf_eq]; rw [iso_iff_readings v (6 : Fin 8) sg hσk hσ t]
  rw [hset]; exact ⟨c₀, hal, hbf, hT0⟩

#print axioms inst_arr

end Fresh.CertRS.R06998



/-!
# Landing certificate `CertRS.R07000`: speeds (1, 2, 4, 5, 8, 9, 12, 15), subject index 0

Generated 2026-10-24 by `experiments/n8/cert_gen_v1.py` (exact Fractions).  Baseline readings [1, 3, 4, 7, 8, 11, 14].  Components up to the first wide one: 1.
Radius: speeds within `η ≤ 1/8960` of the baseline speeds, giving `ε = 2η ≤ 1/4480`.  Covering margin `μ = 1/256`.
`hcov` is **[PROVISIONAL: covering]**, supporting the claim that the first lonely instant of this subject is the largest exit of the first alive component.
Result `inst_arr`: for such `v`, the subject has a first isolation (a least element over all `t > 0`).  Grades: [L].
-/

open Classical

namespace Fresh.CertRS.R07000

open Fresh Fresh.LandingCert Fresh.LandingRule

noncomputable def pr : Fin 7 → ℝ := ![(1 : ℝ), (3 : ℝ), (4 : ℝ), (7 : ℝ), (8 : ℝ), (11 : ℝ), (14 : ℝ)]
noncomputable def aV : Fin 1 → ℝ := ![(9 / 56 : ℝ)]
noncomputable def bV : Fin 1 → ℝ := ![(15 / 88 : ℝ)]
noncomputable def dV : Fin 1 → ℝ := ![(1 / 112 : ℝ)]
noncomputable def TV : Fin 1 → ℝ := ![(221 / 1232 : ℝ)]
def ZV : Fin 1 → ℤ := ![4]
noncomputable def HV : ℝ := (431 / 2464 : ℝ)
noncomputable def EXs (c : Fin 1) : Finset (Fin 7 × ℤ) :=
  (Finset.univ ×ˢ Finset.Icc 0 (ZV c)).filter (fun q => ((q.2 : ℝ) + 1 / 8) / pr q.1 = aV c)
noncomputable def ENs (c : Fin 1) : Finset (Fin 7 × ℤ) :=
  (Finset.univ ×ˢ Finset.Icc 0 (ZV c)).filter (fun q => ((q.2 : ℝ) - 1 / 8) / pr q.1 = bV c)

theorem hp : ∀ i, 1 ≤ pr i ∧ pr i ≤ (14 : ℝ) := by intro i; fin_cases i <;> norm_num [pr]
theorem hp1 : ∀ i, 1 ≤ pr i := fun i => (hp i).1
theorem pr_0 : pr (0 : Fin 7) = (1 : ℝ) := rfl
theorem pr_1 : pr (1 : Fin 7) = (3 : ℝ) := rfl
theorem pr_2 : pr (2 : Fin 7) = (4 : ℝ) := rfl
theorem pr_3 : pr (3 : Fin 7) = (7 : ℝ) := rfl
theorem pr_4 : pr (4 : Fin 7) = (8 : ℝ) := rfl
theorem pr_5 : pr (5 : Fin 7) = (11 : ℝ) := rfl
theorem pr_6 : pr (6 : Fin 7) = (14 : ℝ) := rfl
theorem aV_0 : aV (0 : Fin 1) = (9 / 56 : ℝ) := rfl
theorem bV_0 : bV (0 : Fin 1) = (15 / 88 : ℝ) := rfl
theorem dV_0 : dV (0 : Fin 1) = (1 / 112 : ℝ) := rfl
theorem TV_0 : TV (0 : Fin 1) = (221 / 1232 : ℝ) := rfl
theorem ZV_0 : ZV (0 : Fin 1) = (4 : ℤ) := rfl
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
  · exact ⟨(3, 1), by simp [EXs, ZV, pr, aV] <;> norm_num⟩
theorem hENne : ∀ c, (ENs c).Nonempty := by
  intro c
  fin_cases c
  · exact ⟨(5, 2), by simp [ENs, ZV, pr, bV] <;> norm_num⟩
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
    (hHt : t ≤ HV) (h1 : (0 : ℝ) ≤ t) (h2 : t ≤ (5 / 32 : ℝ)) (hlon : ∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)) : False := by
  rcases le_total t (31 / 256 : ℝ) with hs0 | hs0
  · exact zone_kill_gen pr x ε HV (1 / 256 : ℝ) hp1 hdev hεH (by norm_num) (0 : Fin 7) 0 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (0 : Fin 7))
  rcases le_total t (35 / 256 : ℝ) with hs1 | hs1
  · exact zone_kill_gen pr x ε HV (1 / 256 : ℝ) hp1 hdev hεH (by norm_num) (4 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (4 : Fin 7))
  exact zone_kill_gen pr x ε HV (1 / 256 : ℝ) hp1 hdev hεH (by norm_num) (3 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (3 : Fin 7))
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
  rcases lt_or_ge t (5 / 32 : ℝ) with c0 | c0
  · exact gap0 x ε hdev hεH t h0.le hHt h0.le (by linarith) hlon
  have d0 : (431 / 2464 : ℝ) < t := by
    by_contra hc; push Not at hc; exact n0 ⟨by linarith, by linarith⟩
  have hHv : HV = (431 / 2464 : ℝ) := rfl
  exact absurd (by linarith : t ≤ (431 / 2464 : ℝ)) (not_le.2 d0)

theorem inst (x : Fin 7 → ℝ) (ε : ℝ) (hε : ε ≤ (1 / 4480 : ℝ)) (hdev : ∀ i, |x i - pr i| ≤ ε) :
    ∃ c₀ : Fin 1, Alive (mxOf x EXs hEXne) (mnOf x ENs hENne) c₀ ∧
      (∀ c, c < c₀ → ¬ Alive (mxOf x EXs hEXne) (mnOf x ENs hENne) c) ∧
      IsLeast {t : ℝ | 0 < t ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)} (mxOf x EXs hEXne c₀) :=
  landing_cert 1 (14 : ℝ) (by norm_num) pr x hp ε hdev aV bV dV TV ZV hab hd0 hdP haP hT hZ (hE ε hε) hcls EXs ENs hEXne hENne
    hEXdef hENdef hsepL HV hHL (cov x ε hε hdev) (0 : Fin 1) (by rw [dV_0, bV_0, aV_0]; norm_num)

noncomputable def sv : Fin 8 → ℝ := ![(1 : ℝ), (2 : ℝ), (4 : ℝ), (5 : ℝ), (8 : ℝ), (9 : ℝ), (12 : ℝ), (15 : ℝ)]
def sg : Fin 7 → Fin 8 := ![1, 2, 3, 4, 5, 6, 7]

theorem sv_0 : sv (0 : Fin 8) = (1 : ℝ) := rfl
theorem sv_1 : sv (1 : Fin 8) = (2 : ℝ) := rfl
theorem sv_2 : sv (2 : Fin 8) = (4 : ℝ) := rfl
theorem sv_3 : sv (3 : Fin 8) = (5 : ℝ) := rfl
theorem sv_4 : sv (4 : Fin 8) = (8 : ℝ) := rfl
theorem sv_5 : sv (5 : Fin 8) = (9 : ℝ) := rfl
theorem sv_6 : sv (6 : Fin 8) = (12 : ℝ) := rfl
theorem sv_7 : sv (7 : Fin 8) = (15 : ℝ) := rfl
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

end Fresh.CertRS.R07000



/-!
# Landing certificate `CertRS.R07001`: speeds (1, 2, 4, 5, 8, 9, 12, 15), subject index 1

Generated 2026-10-24 by `experiments/n8/cert_gen_v1.py` (exact Fractions).  Baseline readings [1, 2, 3, 6, 7, 10, 13].  Components up to the first wide one: 3.
Radius: speeds within `η ≤ 1/9984` of the baseline speeds, giving `ε = 2η ≤ 1/4992`.  Covering margin `μ = 1/256`.
`hcov` is **[PROVISIONAL: covering]**, supporting the claim that the first lonely instant of this subject is the largest exit of the first alive component.
Result `inst_arr`: for such `v`, the subject has a first isolation (a least element over all `t > 0`).  Grades: [L].
-/

open Classical

namespace Fresh.CertRS.R07001

open Fresh Fresh.LandingCert Fresh.LandingRule

noncomputable def pr : Fin 7 → ℝ := ![(1 : ℝ), (2 : ℝ), (3 : ℝ), (6 : ℝ), (7 : ℝ), (10 : ℝ), (13 : ℝ)]
noncomputable def aV : Fin 3 → ℝ := ![(1 / 8 : ℝ), (3 / 16 : ℝ), (17 / 80 : ℝ)]
noncomputable def bV : Fin 3 → ℝ := ![(1 / 8 : ℝ), (3 / 16 : ℝ), (23 / 104 : ℝ)]
noncomputable def dV : Fin 3 → ℝ := ![(1 / 80 : ℝ), (1 / 80 : ℝ), (1 / 104 : ℝ)]
noncomputable def TV : Fin 3 → ℝ := ![(11 / 80 : ℝ), (1 / 5 : ℝ), (3 / 13 : ℝ)]
def ZV : Fin 3 → ℤ := ![4, 4, 5]
noncomputable def HV : ℝ := (47 / 208 : ℝ)
noncomputable def EXs (c : Fin 3) : Finset (Fin 7 × ℤ) :=
  (Finset.univ ×ˢ Finset.Icc 0 (ZV c)).filter (fun q => ((q.2 : ℝ) + 1 / 8) / pr q.1 = aV c)
noncomputable def ENs (c : Fin 3) : Finset (Fin 7 × ℤ) :=
  (Finset.univ ×ˢ Finset.Icc 0 (ZV c)).filter (fun q => ((q.2 : ℝ) - 1 / 8) / pr q.1 = bV c)

theorem fcases (c : Fin 3) : c = 0 ∨ c = 1 ∨ c = 2 := by revert c; decide
theorem hp : ∀ i, 1 ≤ pr i ∧ pr i ≤ (13 : ℝ) := by intro i; fin_cases i <;> norm_num [pr]
theorem hp1 : ∀ i, 1 ≤ pr i := fun i => (hp i).1
theorem pr_0 : pr (0 : Fin 7) = (1 : ℝ) := rfl
theorem pr_1 : pr (1 : Fin 7) = (2 : ℝ) := rfl
theorem pr_2 : pr (2 : Fin 7) = (3 : ℝ) := rfl
theorem pr_3 : pr (3 : Fin 7) = (6 : ℝ) := rfl
theorem pr_4 : pr (4 : Fin 7) = (7 : ℝ) := rfl
theorem pr_5 : pr (5 : Fin 7) = (10 : ℝ) := rfl
theorem pr_6 : pr (6 : Fin 7) = (13 : ℝ) := rfl
theorem aV_0 : aV (0 : Fin 3) = (1 / 8 : ℝ) := rfl
theorem bV_0 : bV (0 : Fin 3) = (1 / 8 : ℝ) := rfl
theorem dV_0 : dV (0 : Fin 3) = (1 / 80 : ℝ) := rfl
theorem TV_0 : TV (0 : Fin 3) = (11 / 80 : ℝ) := rfl
theorem ZV_0 : ZV (0 : Fin 3) = (4 : ℤ) := rfl
theorem aV_1 : aV (1 : Fin 3) = (3 / 16 : ℝ) := rfl
theorem bV_1 : bV (1 : Fin 3) = (3 / 16 : ℝ) := rfl
theorem dV_1 : dV (1 : Fin 3) = (1 / 80 : ℝ) := rfl
theorem TV_1 : TV (1 : Fin 3) = (1 / 5 : ℝ) := rfl
theorem ZV_1 : ZV (1 : Fin 3) = (4 : ℤ) := rfl
theorem aV_2 : aV (2 : Fin 3) = (17 / 80 : ℝ) := rfl
theorem bV_2 : bV (2 : Fin 3) = (23 / 104 : ℝ) := rfl
theorem dV_2 : dV (2 : Fin 3) = (1 / 104 : ℝ) := rfl
theorem TV_2 : TV (2 : Fin 3) = (3 / 13 : ℝ) := rfl
theorem ZV_2 : ZV (2 : Fin 3) = (5 : ℤ) := rfl
theorem hab : ∀ c, aV c ≤ bV c := by intro c; rcases fcases c with rfl | rfl | rfl <;> norm_num [aV_0, bV_0, dV_0, TV_0, ZV_0, aV_1, bV_1, dV_1, TV_1, ZV_1, aV_2, bV_2, dV_2, TV_2, ZV_2]
theorem hd0 : ∀ c, 0 < dV c := by intro c; rcases fcases c with rfl | rfl | rfl <;> norm_num [aV_0, bV_0, dV_0, TV_0, ZV_0, aV_1, bV_1, dV_1, TV_1, ZV_1, aV_2, bV_2, dV_2, TV_2, ZV_2]
theorem hdP : ∀ c, dV c ≤ 1 / (4 * (13 : ℝ)) := by intro c; rcases fcases c with rfl | rfl | rfl <;> norm_num [aV_0, bV_0, dV_0, TV_0, ZV_0, aV_1, bV_1, dV_1, TV_1, ZV_1, aV_2, bV_2, dV_2, TV_2, ZV_2]
theorem haP : ∀ c, dV c < aV c := by intro c; rcases fcases c with rfl | rfl | rfl <;> norm_num [aV_0, bV_0, dV_0, TV_0, ZV_0, aV_1, bV_1, dV_1, TV_1, ZV_1, aV_2, bV_2, dV_2, TV_2, ZV_2]
theorem hT : ∀ c, bV c + dV c ≤ TV c := by intro c; rcases fcases c with rfl | rfl | rfl <;> norm_num [aV_0, bV_0, dV_0, TV_0, ZV_0, aV_1, bV_1, dV_1, TV_1, ZV_1, aV_2, bV_2, dV_2, TV_2, ZV_2]
theorem hZ : ∀ c, ((13 : ℝ) + 1) * TV c + 1 ≤ (ZV c : ℝ) := by intro c; rcases fcases c with rfl | rfl | rfl <;> norm_num [aV_0, bV_0, dV_0, TV_0, ZV_0, aV_1, bV_1, dV_1, TV_1, ZV_1, aV_2, bV_2, dV_2, TV_2, ZV_2]
theorem hE (ε : ℝ) (hε : ε ≤ (1 / 4992 : ℝ)) : ∀ c, 8 * ((ZV c : ℝ) + 1) * ε ≤ dV c := by
  intro c; rcases fcases c with rfl | rfl | rfl <;> norm_num [aV_0, bV_0, dV_0, TV_0, ZV_0, aV_1, bV_1, dV_1, TV_1, ZV_1, aV_2, bV_2, dV_2, TV_2, ZV_2] <;> linarith
set_option maxHeartbeats 4000000 in
theorem hcls : ∀ c i, ∀ z : ℤ, 0 ≤ z → z ≤ ZV c →
    ((z : ℝ) + 1 / 8) / pr i ≤ aV c - dV c ∨ bV c + dV c ≤ ((z : ℝ) - 1 / 8) / pr i ∨
      ((z : ℝ) + 1 / 8) / pr i = aV c ∨ ((z : ℝ) - 1 / 8) / pr i = bV c := by
  intro c i z h0 h1
  rcases fcases c with rfl | rfl | rfl <;> rcases fin7_cases i with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [aV_0, bV_0, dV_0, TV_0, ZV_0, aV_1, bV_1, dV_1, TV_1, ZV_1, aV_2, bV_2, dV_2, TV_2, ZV_2] at h1 <;> interval_cases z <;> norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6, aV_0, bV_0, dV_0, TV_0, ZV_0, aV_1, bV_1, dV_1, TV_1, ZV_1, aV_2, bV_2, dV_2, TV_2, ZV_2]
theorem hEXne : ∀ c, (EXs c).Nonempty := by
  intro c
  rcases fcases c with rfl | rfl | rfl
  · exact ⟨(0, 0), by simp [EXs, ZV, pr, aV] <;> norm_num⟩
  · exact ⟨(3, 1), by simp [EXs, ZV, pr, aV] <;> norm_num⟩
  · exact ⟨(5, 2), by simp [EXs, ZV, pr, aV] <;> norm_num⟩
theorem hENne : ∀ c, (ENs c).Nonempty := by
  intro c
  rcases fcases c with rfl | rfl | rfl
  · exact ⟨(4, 1), by simp [ENs, ZV, pr, bV] <;> norm_num⟩
  · exact ⟨(5, 2), by simp [ENs, ZV, pr, bV] <;> norm_num⟩
  · exact ⟨(6, 3), by simp [ENs, ZV, pr, bV] <;> norm_num⟩
theorem hEXdef : ∀ c, ∀ q : Fin 7 × ℤ, q ∈ EXs c ↔ 0 ≤ q.2 ∧ q.2 ≤ ZV c ∧ ((q.2 : ℝ) + 1 / 8) / pr q.1 = aV c := by
  intro c q
  simp only [EXs, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, Finset.mem_Icc, true_and]
  tauto
theorem hENdef : ∀ c, ∀ q : Fin 7 × ℤ, q ∈ ENs c ↔ 0 ≤ q.2 ∧ q.2 ≤ ZV c ∧ ((q.2 : ℝ) - 1 / 8) / pr q.1 = bV c := by
  intro c q
  simp only [ENs, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, Finset.mem_Icc, true_and]
  tauto
theorem hsepL : ∀ c c' : Fin 3, c < c' → bV c + dV c / 2 < aV c' - dV c' / 2 := by
  intro c c' h
  rcases fcases c with rfl | rfl | rfl <;> rcases fcases c' with rfl | rfl | rfl <;> simp at h ⊢ <;> norm_num [aV_0, bV_0, dV_0, TV_0, ZV_0, aV_1, bV_1, dV_1, TV_1, ZV_1, aV_2, bV_2, dV_2, TV_2, ZV_2]
theorem hHL : ∀ c, bV c + dV c / 2 ≤ HV := by intro c; rcases fcases c with rfl | rfl | rfl <;> norm_num [aV_0, bV_0, dV_0, TV_0, ZV_0, aV_1, bV_1, dV_1, TV_1, ZV_1, aV_2, bV_2, dV_2, TV_2, ZV_2, HV]

theorem gap0 (x : Fin 7 → ℝ) (ε : ℝ) (hdev : ∀ i, |x i - pr i| ≤ ε) (hεH : ε * HV ≤ (1 / 256 : ℝ) / 2) (t : ℝ) (h0 : 0 ≤ t)
    (hHt : t ≤ HV) (h1 : (0 : ℝ) ≤ t) (h2 : t ≤ (19 / 160 : ℝ)) (hlon : ∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)) : False := by
  exact zone_kill_gen pr x ε HV (1 / 256 : ℝ) hp1 hdev hεH (by norm_num) (0 : Fin 7) 0 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (0 : Fin 7))
theorem gap1 (x : Fin 7 → ℝ) (ε : ℝ) (hdev : ∀ i, |x i - pr i| ≤ ε) (hεH : ε * HV ≤ (1 / 256 : ℝ) / 2) (t : ℝ) (h0 : 0 ≤ t)
    (hHt : t ≤ HV) (h1 : (21 / 160 : ℝ) ≤ t) (h2 : t ≤ (29 / 160 : ℝ)) (hlon : ∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)) : False := by
  rcases le_total t (281 / 1792 : ℝ) with hs0 | hs0
  · exact zone_kill_gen pr x ε HV (1 / 256 : ℝ) hp1 hdev hεH (by norm_num) (4 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (4 : Fin 7))
  exact zone_kill_gen pr x ε HV (1 / 256 : ℝ) hp1 hdev hεH (by norm_num) (3 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (3 : Fin 7))
theorem gap2 (x : Fin 7 → ℝ) (ε : ℝ) (hdev : ∀ i, |x i - pr i| ≤ ε) (hεH : ε * HV ≤ (1 / 256 : ℝ) / 2) (t : ℝ) (h0 : 0 ≤ t)
    (hHt : t ≤ HV) (h1 : (31 / 160 : ℝ) ≤ t) (h2 : t ≤ (27 / 130 : ℝ)) (hlon : ∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)) : False := by
  exact zone_kill_gen pr x ε HV (1 / 256 : ℝ) hp1 hdev hεH (by norm_num) (5 : Fin 7) 2 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (5 : Fin 7))
theorem cov (x : Fin 7 → ℝ) (ε : ℝ) (hε : ε ≤ (1 / 4992 : ℝ)) (hdev : ∀ i, |x i - pr i| ≤ ε) :
    ∀ t : ℝ, 0 < t → t ≤ HV → (∀ c, ¬ (aV c - dV c / 2 ≤ t ∧ t ≤ bV c + dV c / 2)) →
      ¬ (∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)) := by
  intro t h0 hHt hnone hlon
  have hεH : ε * HV ≤ (1 / 256 : ℝ) / 2 := by
    have hε0 : 0 ≤ ε := le_trans (abs_nonneg _) (hdev 0)
    have : ε * HV ≤ (1 / 4992 : ℝ) * HV := mul_le_mul_of_nonneg_right hε (by norm_num [HV])
    have h2 : (1 / 4992 : ℝ) * HV ≤ (1 / 256 : ℝ) / 2 := by norm_num [HV]
    linarith
  have n0 := hnone (0 : Fin 3)
  rw [aV_0, bV_0, dV_0] at n0
  have n1 := hnone (1 : Fin 3)
  rw [aV_1, bV_1, dV_1] at n1
  have n2 := hnone (2 : Fin 3)
  rw [aV_2, bV_2, dV_2] at n2
  rcases lt_or_ge t (19 / 160 : ℝ) with c0 | c0
  · exact gap0 x ε hdev hεH t h0.le hHt h0.le (by linarith) hlon
  have d0 : (21 / 160 : ℝ) < t := by
    by_contra hc; push Not at hc; exact n0 ⟨by linarith, by linarith⟩
  rcases lt_or_ge t (29 / 160 : ℝ) with c1 | c1
  · exact gap1 x ε hdev hεH t h0.le hHt d0.le (by linarith) hlon
  have d1 : (31 / 160 : ℝ) < t := by
    by_contra hc; push Not at hc; exact n1 ⟨by linarith, by linarith⟩
  rcases lt_or_ge t (27 / 130 : ℝ) with c2 | c2
  · exact gap2 x ε hdev hεH t h0.le hHt d1.le (by linarith) hlon
  have d2 : (47 / 208 : ℝ) < t := by
    by_contra hc; push Not at hc; exact n2 ⟨by linarith, by linarith⟩
  have hHv : HV = (47 / 208 : ℝ) := rfl
  exact absurd (by linarith : t ≤ (47 / 208 : ℝ)) (not_le.2 d2)

theorem inst (x : Fin 7 → ℝ) (ε : ℝ) (hε : ε ≤ (1 / 4992 : ℝ)) (hdev : ∀ i, |x i - pr i| ≤ ε) :
    ∃ c₀ : Fin 3, Alive (mxOf x EXs hEXne) (mnOf x ENs hENne) c₀ ∧
      (∀ c, c < c₀ → ¬ Alive (mxOf x EXs hEXne) (mnOf x ENs hENne) c) ∧
      IsLeast {t : ℝ | 0 < t ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)} (mxOf x EXs hEXne c₀) :=
  landing_cert 3 (13 : ℝ) (by norm_num) pr x hp ε hdev aV bV dV TV ZV hab hd0 hdP haP hT hZ (hE ε hε) hcls EXs ENs hEXne hENne
    hEXdef hENdef hsepL HV hHL (cov x ε hε hdev) (2 : Fin 3) (by rw [dV_2, bV_2, aV_2]; norm_num)

noncomputable def sv : Fin 8 → ℝ := ![(1 : ℝ), (2 : ℝ), (4 : ℝ), (5 : ℝ), (8 : ℝ), (9 : ℝ), (12 : ℝ), (15 : ℝ)]
def sg : Fin 7 → Fin 8 := ![0, 2, 3, 4, 5, 6, 7]

theorem sv_0 : sv (0 : Fin 8) = (1 : ℝ) := rfl
theorem sv_1 : sv (1 : Fin 8) = (2 : ℝ) := rfl
theorem sv_2 : sv (2 : Fin 8) = (4 : ℝ) := rfl
theorem sv_3 : sv (3 : Fin 8) = (5 : ℝ) := rfl
theorem sv_4 : sv (4 : Fin 8) = (8 : ℝ) := rfl
theorem sv_5 : sv (5 : Fin 8) = (9 : ℝ) := rfl
theorem sv_6 : sv (6 : Fin 8) = (12 : ℝ) := rfl
theorem sv_7 : sv (7 : Fin 8) = (15 : ℝ) := rfl
theorem sg_0 : sg (0 : Fin 7) = (0 : Fin 8) := rfl
theorem sg_1 : sg (1 : Fin 7) = (2 : Fin 8) := rfl
theorem sg_2 : sg (2 : Fin 7) = (3 : Fin 8) := rfl
theorem sg_3 : sg (3 : Fin 7) = (4 : Fin 8) := rfl
theorem sg_4 : sg (4 : Fin 7) = (5 : Fin 8) := rfl
theorem sg_5 : sg (5 : Fin 7) = (6 : Fin 8) := rfl
theorem sg_6 : sg (6 : Fin 7) = (7 : Fin 8) := rfl

theorem inst_arr (v : Fin 8 → ℝ) (η : ℝ) (hη : η ≤ (1 / 9984 : ℝ)) (hv : ∀ j, |v j - sv j| ≤ η) :
    ∃ c₀ : Fin 3, Alive (mxOf (fun i => |v (sg i) - v (1 : Fin 8)|) EXs hEXne) (mnOf (fun i => |v (sg i) - v (1 : Fin 8)|) ENs hENne) c₀ ∧
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

end Fresh.CertRS.R07001



/-!
# Landing certificate `CertRS.R07002`: speeds (1, 2, 4, 5, 8, 9, 12, 15), subject index 2

Generated 2026-10-24 by `experiments/n8/cert_gen_v1.py` (exact Fractions).  Baseline readings [3, 2, 1, 4, 5, 8, 11].  Components up to the first wide one: 1.
Radius: speeds within `η ≤ 1/17600` of the baseline speeds, giving `ε = 2η ≤ 1/8800`.  Covering margin `μ = 1/512`.
`hcov` is **[PROVISIONAL: covering]**, supporting the claim that the first lonely instant of this subject is the largest exit of the first alive component.
Result `inst_arr`: for such `v`, the subject has a first isolation (a least element over all `t > 0`).  Grades: [L].
-/

open Classical

namespace Fresh.CertRS.R07002

open Fresh Fresh.LandingCert Fresh.LandingRule

noncomputable def pr : Fin 7 → ℝ := ![(3 : ℝ), (2 : ℝ), (1 : ℝ), (4 : ℝ), (5 : ℝ), (8 : ℝ), (11 : ℝ)]
noncomputable def aV : Fin 1 → ℝ := ![(9 / 64 : ℝ)]
noncomputable def bV : Fin 1 → ℝ := ![(15 / 88 : ℝ)]
noncomputable def dV : Fin 1 → ℝ := ![(1 / 220 : ℝ)]
noncomputable def TV : Fin 1 → ℝ := ![(7 / 40 : ℝ)]
def ZV : Fin 1 → ℤ := ![4]
noncomputable def HV : ℝ := (19 / 110 : ℝ)
noncomputable def EXs (c : Fin 1) : Finset (Fin 7 × ℤ) :=
  (Finset.univ ×ˢ Finset.Icc 0 (ZV c)).filter (fun q => ((q.2 : ℝ) + 1 / 8) / pr q.1 = aV c)
noncomputable def ENs (c : Fin 1) : Finset (Fin 7 × ℤ) :=
  (Finset.univ ×ˢ Finset.Icc 0 (ZV c)).filter (fun q => ((q.2 : ℝ) - 1 / 8) / pr q.1 = bV c)

theorem hp : ∀ i, 1 ≤ pr i ∧ pr i ≤ (11 : ℝ) := by intro i; fin_cases i <;> norm_num [pr]
theorem hp1 : ∀ i, 1 ≤ pr i := fun i => (hp i).1
theorem pr_0 : pr (0 : Fin 7) = (3 : ℝ) := rfl
theorem pr_1 : pr (1 : Fin 7) = (2 : ℝ) := rfl
theorem pr_2 : pr (2 : Fin 7) = (1 : ℝ) := rfl
theorem pr_3 : pr (3 : Fin 7) = (4 : ℝ) := rfl
theorem pr_4 : pr (4 : Fin 7) = (5 : ℝ) := rfl
theorem pr_5 : pr (5 : Fin 7) = (8 : ℝ) := rfl
theorem pr_6 : pr (6 : Fin 7) = (11 : ℝ) := rfl
theorem aV_0 : aV (0 : Fin 1) = (9 / 64 : ℝ) := rfl
theorem bV_0 : bV (0 : Fin 1) = (15 / 88 : ℝ) := rfl
theorem dV_0 : dV (0 : Fin 1) = (1 / 220 : ℝ) := rfl
theorem TV_0 : TV (0 : Fin 1) = (7 / 40 : ℝ) := rfl
theorem ZV_0 : ZV (0 : Fin 1) = (4 : ℤ) := rfl
theorem hab : ∀ c, aV c ≤ bV c := by intro c; fin_cases c <;> norm_num [aV, bV]
theorem hd0 : ∀ c, 0 < dV c := by intro c; fin_cases c <;> norm_num [dV]
theorem hdP : ∀ c, dV c ≤ 1 / (4 * (11 : ℝ)) := by intro c; fin_cases c <;> norm_num [dV]
theorem haP : ∀ c, dV c < aV c := by intro c; fin_cases c <;> norm_num [dV, aV]
theorem hT : ∀ c, bV c + dV c ≤ TV c := by intro c; fin_cases c <;> norm_num [bV, dV, TV]
theorem hZ : ∀ c, ((11 : ℝ) + 1) * TV c + 1 ≤ (ZV c : ℝ) := by intro c; fin_cases c <;> norm_num [TV, ZV]
theorem hE (ε : ℝ) (hε : ε ≤ (1 / 8800 : ℝ)) : ∀ c, 8 * ((ZV c : ℝ) + 1) * ε ≤ dV c := by
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
    (hHt : t ≤ HV) (h1 : (0 : ℝ) ≤ t) (h2 : t ≤ (487 / 3520 : ℝ)) (hlon : ∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)) : False := by
  rcases le_total t (63 / 512 : ℝ) with hs0 | hs0
  · exact zone_kill_gen pr x ε HV (1 / 512 : ℝ) hp1 hdev hεH (by norm_num) (2 : Fin 7) 0 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (2 : Fin 7))
  exact zone_kill_gen pr x ε HV (1 / 512 : ℝ) hp1 hdev hεH (by norm_num) (5 : Fin 7) 1 t h0 hHt (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (by norm_num [pr_0, pr_1, pr_2, pr_3, pr_4, pr_5, pr_6]; linarith) (hlon (5 : Fin 7))
theorem cov (x : Fin 7 → ℝ) (ε : ℝ) (hε : ε ≤ (1 / 8800 : ℝ)) (hdev : ∀ i, |x i - pr i| ≤ ε) :
    ∀ t : ℝ, 0 < t → t ≤ HV → (∀ c, ¬ (aV c - dV c / 2 ≤ t ∧ t ≤ bV c + dV c / 2)) →
      ¬ (∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)) := by
  intro t h0 hHt hnone hlon
  have hεH : ε * HV ≤ (1 / 512 : ℝ) / 2 := by
    have hε0 : 0 ≤ ε := le_trans (abs_nonneg _) (hdev 0)
    have : ε * HV ≤ (1 / 8800 : ℝ) * HV := mul_le_mul_of_nonneg_right hε (by norm_num [HV])
    have h2 : (1 / 8800 : ℝ) * HV ≤ (1 / 512 : ℝ) / 2 := by norm_num [HV]
    linarith
  have n0 := hnone (0 : Fin 1)
  rw [aV_0, bV_0, dV_0] at n0
  rcases lt_or_ge t (487 / 3520 : ℝ) with c0 | c0
  · exact gap0 x ε hdev hεH t h0.le hHt h0.le (by linarith) hlon
  have d0 : (19 / 110 : ℝ) < t := by
    by_contra hc; push Not at hc; exact n0 ⟨by linarith, by linarith⟩
  have hHv : HV = (19 / 110 : ℝ) := rfl
  exact absurd (by linarith : t ≤ (19 / 110 : ℝ)) (not_le.2 d0)

theorem inst (x : Fin 7 → ℝ) (ε : ℝ) (hε : ε ≤ (1 / 8800 : ℝ)) (hdev : ∀ i, |x i - pr i| ≤ ε) :
    ∃ c₀ : Fin 1, Alive (mxOf x EXs hEXne) (mnOf x ENs hENne) c₀ ∧
      (∀ c, c < c₀ → ¬ Alive (mxOf x EXs hEXne) (mnOf x ENs hENne) c) ∧
      IsLeast {t : ℝ | 0 < t ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (x i * t)} (mxOf x EXs hEXne c₀) :=
  landing_cert 1 (11 : ℝ) (by norm_num) pr x hp ε hdev aV bV dV TV ZV hab hd0 hdP haP hT hZ (hE ε hε) hcls EXs ENs hEXne hENne
    hEXdef hENdef hsepL HV hHL (cov x ε hε hdev) (0 : Fin 1) (by rw [dV_0, bV_0, aV_0]; norm_num)

noncomputable def sv : Fin 8 → ℝ := ![(1 : ℝ), (2 : ℝ), (4 : ℝ), (5 : ℝ), (8 : ℝ), (9 : ℝ), (12 : ℝ), (15 : ℝ)]
def sg : Fin 7 → Fin 8 := ![0, 1, 3, 4, 5, 6, 7]

theorem sv_0 : sv (0 : Fin 8) = (1 : ℝ) := rfl
theorem sv_1 : sv (1 : Fin 8) = (2 : ℝ) := rfl
theorem sv_2 : sv (2 : Fin 8) = (4 : ℝ) := rfl
theorem sv_3 : sv (3 : Fin 8) = (5 : ℝ) := rfl
theorem sv_4 : sv (4 : Fin 8) = (8 : ℝ) := rfl
theorem sv_5 : sv (5 : Fin 8) = (9 : ℝ) := rfl
theorem sv_6 : sv (6 : Fin 8) = (12 : ℝ) := rfl
theorem sv_7 : sv (7 : Fin 8) = (15 : ℝ) := rfl
theorem sg_0 : sg (0 : Fin 7) = (0 : Fin 8) := rfl
theorem sg_1 : sg (1 : Fin 7) = (1 : Fin 8) := rfl
theorem sg_2 : sg (2 : Fin 7) = (3 : Fin 8) := rfl
theorem sg_3 : sg (3 : Fin 7) = (4 : Fin 8) := rfl
theorem sg_4 : sg (4 : Fin 7) = (5 : Fin 8) := rfl
theorem sg_5 : sg (5 : Fin 7) = (6 : Fin 8) := rfl
theorem sg_6 : sg (6 : Fin 7) = (7 : Fin 8) := rfl

theorem inst_arr (v : Fin 8 → ℝ) (η : ℝ) (hη : η ≤ (1 / 17600 : ℝ)) (hv : ∀ j, |v j - sv j| ≤ η) :
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

end Fresh.CertRS.R07002

