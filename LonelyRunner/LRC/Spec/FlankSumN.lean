import LonelyRunner.LRC.Cascade.Flanks
import LonelyRunner.LRC.Spec.MirrorCentreN

/-!
# The flank sum criterion, for rational movers (order eight)

2026-09-26 (running log E77).  `docs/n8/T4_FLANKS_v3.md` §3(d) proves, in the text, the **flank sum criterion**: at a live
flank `e`, if the runners whose ratio to `e` is not a whole number (the **movers**, ratio `a_j / c_j` in lowest terms)
satisfy `Σ (1/4 + 1/c_j) < 1`, then some opening of `e` is lonely.  This file proves it for rational ratios, which is
every whole-number arrangement (`EndRunnerN` reduces the conjecture to those).

At the `k`-th opening `(k + 1/8)/e` a runner of ratio `ρ` sits at `ρ·(k + 1/8)`.
* A runner of whole ratio `A` with `8 ∤ A` is clear at every opening (`Flanks.integer_ratio_clear_iff`): the grid part.
* A mover of ratio `a/c` sits at `a·k/c + a/(8c)`.  As `k` runs through `c` consecutive openings, `a·k mod c` runs through
  every residue once (`a`, `c` coprime), and an open arc of a quarter lap holds at most `c/4 + 1` of the points
  `i/c + β` (`arc_count`).  So among any `N` consecutive openings with `c ∣ N` the mover is in the way at most
  `N/4 + N/c` times (`mover_count`).
* Summing over the movers leaves a clear opening when `Σ (1/4 + 1/c_j) < 1` (`flank_sum`).

At order eight this seats up to three movers (`3·1/4 < 1`); four reach the sum `1`.  Everything here is proved; no
`sorry`, no `native_decide`.
-/

namespace LRC.FlankSum

open Flanks ConstructionN MomentIterationN

instance : Fact (2 ≤ 8) := ⟨by norm_num⟩

/-- Integers strictly inside an open interval of length `w ≥ 0`: at most `w + 1` of them. -/
theorem card_int_Ioo_le {x w : ℝ} (hw : 0 ≤ w) (s : Finset ℤ)
    (hs : ∀ i ∈ s, x < (i : ℝ) ∧ (i : ℝ) < x + w) : (s.card : ℝ) ≤ w + 1 := by
  have hsub : s ⊆ Finset.Ioo ⌊x⌋ ⌈x + w⌉ := by
    intro i hi
    obtain ⟨h1, h2⟩ := hs i hi
    rw [Finset.mem_Ioo]
    exact ⟨Int.floor_lt.mpr h1, Int.lt_ceil.mpr h2⟩
  have hcard := Finset.card_le_card hsub
  rw [Int.card_Ioo] at hcard
  have hc1 := Int.ceil_lt_add_one (x + w)
  have hf1 := Int.sub_one_lt_floor x
  have hmax : ((⌈x + w⌉ - ⌊x⌋ - 1).toNat : ℤ) = max (⌈x + w⌉ - ⌊x⌋ - 1) 0 := Int.toNat_eq_max _
  have hR : (((⌈x + w⌉ - ⌊x⌋ - 1).toNat : ℕ) : ℝ) ≤ w + 1 := by
    have : (((⌈x + w⌉ - ⌊x⌋ - 1).toNat : ℕ) : ℝ) = ((max (⌈x + w⌉ - ⌊x⌋ - 1) 0 : ℤ) : ℝ) := by
      rw [← hmax]; norm_cast
    rw [this]
    rcases le_total (⌈x + w⌉ - ⌊x⌋ - 1) 0 with h | h
    · rw [max_eq_right h]; push_cast; linarith
    · rw [max_eq_left h]; push_cast; linarith
  calc (s.card : ℝ) ≤ (((⌈x + w⌉ - ⌊x⌋ - 1).toNat : ℕ) : ℝ) := by exact_mod_cast hcard
    _ ≤ w + 1 := hR

/-- A position in `[-1/8, 7/8)` that is within `1/8` of an integer is within `1/8` of `0`. -/
theorem near_zero_of_window {y : ℝ} (h0 : -(1 / 8) ≤ y) (h1 : y < 7 / 8) (hb : circDist y < 1 / 8) :
    -(1 / 8) < y ∧ y < 1 / 8 := by
  constructor
  · rcases h0.lt_or_eq with h | h
    · exact h
    · exfalso
      have e : y + ((1 : ℤ) : ℝ) = 7 / 8 := by rw [← h]; push_cast; ring
      have := LRC.MirrorCentre.circDist_ge_of_window (x := y + ((1 : ℤ) : ℝ)) (a := 1 / 8) (m := 0)
        (by rw [e]; norm_num) (by rw [e]; norm_num) (by norm_num)
      rw [circDist_add_int] at this; linarith
  · by_contra hc
    push Not at hc
    have := LRC.MirrorCentre.circDist_ge_of_window (x := y) (a := 1 / 8) (m := 0)
      (by push_cast; linarith) (by push_cast; linarith) (by norm_num)
    linarith

/-- **Counting a periodic predicate over a shifted window.**  A `c`-periodic predicate on `ℤ` holds as often on
`0, …, c − 1` as on `s, …, s + c − 1`. -/
theorem card_filter_shift {Q : ℤ → Prop} [DecidablePred Q] {c : ℕ} (hc : 0 < c)
    (hQ : ∀ i m : ℤ, Q (i + m * c) ↔ Q i) (s : ℤ) :
    ((Finset.range c).filter (fun i : ℕ => Q (i : ℤ))).card ≤ ((Finset.Ico s (s + c)).filter Q).card := by
  have hcz : (0 : ℤ) < c := by exact_mod_cast hc
  refine Finset.card_le_card_of_injOn (fun i : ℕ => s + ((i : ℤ) - s) % c) ?_ ?_
  · intro i hi
    rw [Finset.mem_coe, Finset.mem_filter] at hi ⊢
    have h0 := Int.emod_nonneg ((i : ℤ) - s) hcz.ne'
    have h1 := Int.emod_lt_of_pos ((i : ℤ) - s) hcz
    refine ⟨Finset.mem_Ico.mpr ⟨by linarith, by linarith⟩, ?_⟩
    have e : s + ((i : ℤ) - s) % c = (i : ℤ) + (-(((i : ℤ) - s) / c)) * c := by
      have := Int.emod_add_mul_ediv ((i : ℤ) - s) c
      linarith [this, show ((i : ℤ) - s) / c * c = c * (((i : ℤ) - s) / c) by ring]
    show Q (s + ((i : ℤ) - s) % c)
    rw [e, hQ]; exact hi.2
  · intro i₁ hi₁ i₂ hi₂ heq
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hi₁ hi₂
    have hmod : ((i₁ : ℤ) - s) % c = ((i₂ : ℤ) - s) % c := by simpa using heq
    have hdvd : (c : ℤ) ∣ (i₁ : ℤ) - i₂ := by
      have := Int.ModEq.dvd hmod.symm
      simpa using this
    have hlt : |(i₁ : ℤ) - i₂| < c := by
      rw [abs_lt]; constructor <;> omega
    have := Int.eq_zero_of_abs_lt_dvd hdvd hlt
    omega

/-- **An open quarter-lap arc holds at most `c/4 + 1` of the points `i/c + β`.** -/
theorem arc_count {c : ℕ} (hc : 0 < c) (β : ℝ) :
    ((((Finset.range c).filter (fun i : ℕ => circDist (((i : ℤ) : ℝ) / c + β) < 1 / 8)).card : ℕ) : ℝ)
      ≤ (c : ℝ) / 4 + 1 := by
  have hcR : (0 : ℝ) < c := by exact_mod_cast hc
  set Q : ℤ → Prop := fun i => circDist ((i : ℝ) / c + β) < 1 / 8 with hQdef
  have hper : ∀ i m : ℤ, Q (i + m * c) ↔ Q i := by
    intro i m
    simp only [hQdef]
    have e : (((i + m * c : ℤ)) : ℝ) / c + β = ((i : ℝ) / c + β) + ((m : ℤ) : ℝ) := by
      push_cast; field_simp; ring
    rw [e, circDist_add_int]
  set s : ℤ := ⌈(c : ℝ) * (-(1 / 8) - β)⌉ with hs
  have hle := card_filter_shift (Q := Q) hc hper s
  have hbound : ((((Finset.Ico s (s + c)).filter Q).card : ℕ) : ℝ) ≤ (c : ℝ) / 4 + 1 := by
    have := card_int_Ioo_le (x := (c : ℝ) * (-(1 / 8) - β)) (w := (c : ℝ) / 4) (by positivity)
      ((Finset.Ico s (s + c)).filter Q) ?_
    · exact this
    intro i hi
    rw [Finset.mem_filter, Finset.mem_Ico] at hi
    obtain ⟨⟨hi1, hi2⟩, hq⟩ := hi
    have hs1 : (c : ℝ) * (-(1 / 8) - β) ≤ (s : ℝ) := Int.le_ceil _
    have hs2 : (s : ℝ) < (c : ℝ) * (-(1 / 8) - β) + 1 := Int.ceil_lt_add_one _
    have hiR1 : (s : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi1
    have hiR2 : (i : ℝ) + 1 ≤ (s : ℝ) + c := by exact_mod_cast hi2
    have hy0 : -(1 / 8) ≤ (i : ℝ) / c + β := by
      have : (c : ℝ) * (-(1 / 8) - β) ≤ (i : ℝ) := by linarith
      have h2 : -(1 / 8) - β ≤ (i : ℝ) / c := by rw [le_div_iff₀ hcR]; linarith
      linarith
    have hy1 : (i : ℝ) / c + β < 7 / 8 := by
      have : (i : ℝ) < (c : ℝ) * (7 / 8 - β) := by nlinarith
      have h2 : (i : ℝ) / c < 7 / 8 - β := by rw [div_lt_iff₀ hcR]; linarith
      linarith
    obtain ⟨hz1, hz2⟩ := near_zero_of_window hy0 hy1 hq
    constructor
    · have : -(1 / 8) - β < (i : ℝ) / c := by linarith
      rw [lt_div_iff₀ hcR] at this; linarith
    · have : (i : ℝ) / c < 1 / 8 - β := by linarith
      rw [div_lt_iff₀ hcR] at this; nlinarith
  have hle' : ((((Finset.range c).filter (fun i : ℕ => Q (i : ℤ))).card : ℕ) : ℝ)
      ≤ ((((Finset.Ico s (s + c)).filter Q).card : ℕ) : ℝ) := by exact_mod_cast hle
  simpa [hQdef] using le_trans hle' hbound

/-- A `c`-periodic predicate on `ℕ` holds `q` times as often on `0, …, c·q − 1` as on `0, …, c − 1`. -/
theorem count_mul {P : ℕ → Prop} [DecidablePred P] {c : ℕ} (hP : ∀ k, P (k + c) ↔ P k) :
    ∀ q : ℕ, Nat.count P (c * q) = q * Nat.count P c := by
  have hshift : ∀ q k, P (c * q + k) ↔ P k := by
    intro q; induction q with
    | zero => intro k; simp
    | succ q ih => intro k; rw [show c * (q + 1) + k = (c * q + k) + c by ring, hP, ih]
  intro q; induction q with
  | zero => simp
  | succ q ih =>
      rw [show c * (q + 1) = c * q + c by ring, Nat.count_add, ih]
      have : Nat.count (fun k => P (c * q + k)) c = Nat.count P c := by
        rw [Nat.count_eq_card_filter_range, Nat.count_eq_card_filter_range]
        congr 1
        exact Finset.filter_congr (fun k _ => hshift q k)
      rw [this]; ring

/-- **A mover of ratio `a/c` is in the way at most `N/4 + N/c` times** among the openings `0, …, N − 1`, `c ∣ N`. -/
theorem mover_count {a : ℤ} {c : ℕ} (hc : 0 < c) (hcop : IsCoprime (c : ℤ) a) (q : ℕ) :
    ((((Finset.range (c * q)).filter
        (fun k : ℕ => circDist ((a : ℝ) / c * ((k : ℝ) + (8 : ℝ)⁻¹)) < 1 / 8)).card : ℕ) : ℝ)
      ≤ ((c * q : ℕ) : ℝ) / 4 + q := by
  have hcR : (0 : ℝ) < c := by exact_mod_cast hc
  have hcz : (0 : ℤ) < c := by exact_mod_cast hc
  set P : ℕ → Prop := fun k => circDist ((a : ℝ) / c * ((k : ℝ) + (8 : ℝ)⁻¹)) < 1 / 8 with hPdef
  have hper : ∀ k, P (k + c) ↔ P k := by
    intro k; simp only [hPdef]
    have e : (a : ℝ) / c * (((k + c : ℕ) : ℝ) + (8 : ℝ)⁻¹)
        = (a : ℝ) / c * ((k : ℝ) + (8 : ℝ)⁻¹) + ((a : ℤ) : ℝ) := by
      push_cast; field_simp; ring
    rw [e, circDist_add_int]
  -- one period: inject k ↦ (a k) mod c into the residues, where the arc count applies
  set β : ℝ := (a : ℝ) / (8 * c) with hβ
  have hone : ((Finset.range c).filter P).card ≤
      ((Finset.range c).filter (fun i : ℕ => circDist (((i : ℤ) : ℝ) / c + β) < 1 / 8)).card := by
    refine Finset.card_le_card_of_injOn (fun k : ℕ => ((a * k) % (c : ℤ)).toNat) ?_ ?_
    · intro k hk
      rw [Finset.mem_coe, Finset.mem_filter] at hk ⊢
      have h0 := Int.emod_nonneg (a * k) hcz.ne'
      have h1 := Int.emod_lt_of_pos (a * k) hcz
      have htn : ((((a * k) % (c : ℤ)).toNat : ℕ) : ℤ) = (a * k) % (c : ℤ) := Int.toNat_of_nonneg h0
      have hlt : ((((a * k) % (c : ℤ)).toNat : ℕ) : ℤ) < c := by rw [htn]; exact h1
      refine ⟨Finset.mem_range.mpr (by exact_mod_cast hlt), ?_⟩
      have hdiv := Int.emod_add_mul_ediv (a * (k : ℤ)) c
      have e : (a : ℝ) / c * ((k : ℝ) + (8 : ℝ)⁻¹)
          = (((((a * k) % (c : ℤ)).toNat : ℕ) : ℤ) : ℝ) / c + β + ((((a * k) / (c : ℤ)) : ℤ) : ℝ) := by
        rw [htn, hβ]
        have : ((a * k : ℤ) : ℝ) = (((a * k) % (c : ℤ) : ℤ) : ℝ) + (c : ℝ) * (((a * k) / (c : ℤ) : ℤ) : ℝ) := by
          exact_mod_cast hdiv.symm
        field_simp
        push_cast at this ⊢
        linarith [this]
      have := hk.2
      simp only [hPdef] at this
      rw [e, circDist_add_int] at this
      exact this
    · intro k₁ hk₁ k₂ hk₂ heq
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hk₁ hk₂
      have h01 := Int.emod_nonneg (a * k₁) hcz.ne'
      have h02 := Int.emod_nonneg (a * k₂) hcz.ne'
      have hmod : (a * k₁) % (c : ℤ) = (a * k₂) % (c : ℤ) := by
        have := congrArg (fun m : ℕ => (m : ℤ)) heq
        simpa [Int.toNat_of_nonneg h01, Int.toNat_of_nonneg h02] using this
      have hdvd : (c : ℤ) ∣ ((k₁ : ℤ) - k₂) * a := by
        have := Int.ModEq.dvd hmod.symm
        rw [show ((k₁ : ℤ) - k₂) * a = a * k₁ - a * k₂ by ring]; exact this
      have hdvd' := hcop.dvd_of_dvd_mul_right hdvd
      have hlt : |(k₁ : ℤ) - k₂| < c := by rw [abs_lt]; constructor <;> omega
      have := Int.eq_zero_of_abs_lt_dvd hdvd' hlt
      omega
  have harc := arc_count hc β
  have hcount := count_mul hper q
  rw [Nat.count_eq_card_filter_range, Nat.count_eq_card_filter_range] at hcount
  have h1 : ((((Finset.range c).filter P).card : ℕ) : ℝ) ≤ (c : ℝ) / 4 + 1 :=
    le_trans (by exact_mod_cast hone) harc
  have : ((((Finset.range (c * q)).filter P).card : ℕ) : ℝ) = (q : ℝ) * (((Finset.range c).filter P).card : ℝ) := by
    rw [hcount]; push_cast; ring
  rw [this]
  have hq : (0 : ℝ) ≤ q := by positivity
  calc (q : ℝ) * (((Finset.range c).filter P).card : ℝ) ≤ (q : ℝ) * ((c : ℝ) / 4 + 1) :=
        mul_le_mul_of_nonneg_left h1 hq
    _ = ((c * q : ℕ) : ℝ) / 4 + q := by push_cast; ring

/-- **The flank sum criterion, rational movers.**  At a flank `e`, every runner of `ds` outside `M` has a whole ratio
`A` with `8 ∤ A`; every mover `d ∈ M` has ratio `a d / c d` in lowest terms.  If `Σ_{d ∈ M} (1/4 + 1/c d) < 1`, some
opening of `e` is lonely. -/
theorem flank_sum {ds M : Finset ℝ} {e : ℝ} (he : 0 < e) (a : ℝ → ℤ) (c : ℝ → ℕ)
    (hc : ∀ d ∈ M, 0 < c d) (hcop : ∀ d ∈ M, IsCoprime ((c d : ℕ) : ℤ) (a d))
    (hratio : ∀ d ∈ M, d / e = (a d : ℝ) / c d)
    (hint : ∀ d ∈ ds, d ∉ M → ∃ A : ℤ, d = A * e ∧ ¬ ((8 : ℕ) : ℤ) ∣ A)
    (hsum : ∑ d ∈ M, ((1 : ℝ) / 4 + 1 / (c d : ℝ)) < 1) :
    ∃ k : ℕ, Lonely 8 ds (flankOpening 8 e k) := by
  classical
  set N : ℕ := ∏ d ∈ M, c d with hN
  have hNpos : 0 < N := Finset.prod_pos (fun d hd => hc d hd)
  have hNR : (0 : ℝ) < N := by exact_mod_cast hNpos
  set B : ℝ → Finset ℕ := fun d => (Finset.range N).filter
    (fun k : ℕ => circDist (d * flankOpening 8 e k) < 1 / 8) with hB
  have hBcard : ∀ d ∈ M, ((B d).card : ℝ) ≤ (N : ℝ) * ((1 : ℝ) / 4 + 1 / (c d : ℝ)) := by
    intro d hd
    obtain ⟨q, hq⟩ := Finset.dvd_prod_of_mem c hd
    have hcR : (0 : ℝ) < c d := by exact_mod_cast hc d hd
    have hmc := mover_count (a := a d) (hc d hd) (hcop d hd) q
    have hfilt : B d = (Finset.range (c d * q)).filter
        (fun k : ℕ => circDist ((a d : ℝ) / c d * ((k : ℝ) + (8 : ℝ)⁻¹)) < 1 / 8) := by
      simp only [hB]
      rw [← hq]
      refine Finset.filter_congr (fun k _ => ?_)
      rw [position_at_flank he, hratio d hd]; norm_num
    rw [hfilt]
    have hNq' : N = c d * q := by rw [hN]; exact hq
    have hNq : (N : ℝ) = (c d : ℝ) * q := by rw [hNq']; push_cast; ring
    calc (((Finset.range (c d * q)).filter _).card : ℝ) ≤ ((c d * q : ℕ) : ℝ) / 4 + q := hmc
      _ = (N : ℝ) * ((1 : ℝ) / 4 + 1 / (c d : ℝ)) := by
          rw [hNq]; push_cast; field_simp; try ring
  have hU : ((M.biUnion B).card : ℝ) < (Finset.range N).card := by
    calc ((M.biUnion B).card : ℝ) ≤ ∑ d ∈ M, ((B d).card : ℝ) := by exact_mod_cast Finset.card_biUnion_le
      _ ≤ ∑ d ∈ M, (N : ℝ) * ((1 : ℝ) / 4 + 1 / (c d : ℝ)) := Finset.sum_le_sum hBcard
      _ = (N : ℝ) * ∑ d ∈ M, ((1 : ℝ) / 4 + 1 / (c d : ℝ)) := by rw [Finset.mul_sum]
      _ < (N : ℝ) * 1 := mul_lt_mul_of_pos_left hsum hNR
      _ = (Finset.range N).card := by simp
  obtain ⟨k, hkN, hkU⟩ := Finset.exists_mem_notMem_of_card_lt_card (by exact_mod_cast hU)
  refine ⟨k, fun d hd => ?_⟩
  by_cases hdM : d ∈ M
  · have : k ∉ B d := fun hk => hkU (Finset.mem_biUnion.mpr ⟨d, hdM, hk⟩)
    simp only [hB, Finset.mem_filter, not_and, not_lt] at this
    have := this hkN
    have h8 : ((8 : ℕ) : ℝ)⁻¹ = 1 / 8 := by norm_num
    rw [h8]; exact this
  · obtain ⟨A, hA, hnA⟩ := hint d hd hdM
    exact (integer_ratio_clear_iff he hA k).2 hnA

end LRC.FlankSum
