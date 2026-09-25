import LonelyRunner.LRC.Spec.RankTwoN
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Stepping in several directions: pigeonhole returns reach every target

2026-09-24.  Real speeds on `d + 1` independent directions `1, β₀, …, β_{d−1}` are read, at a
whole-number time `K`, through the errors `K βⱼ − round (K βⱼ)`.  This file proves, with no density
or measure, that whole-number times put those readings within any `η` of any target
(`exists_step_near`).  It is what carries a model instant to a real time on three or more
directions, as the single Dirichlet step does on two (`RankTwoN.lean`).

* **Returns.**  Pigeonhole on the boxes of side `1/N` gives a whole-number `K > 0` with every error
  below `1/N` (`exists_return`).  With no rational relation, a return's error is never zero, so
  the returns can be taken past any bound (`exists_return_gt`).
* **Returns span.**  The whole-number vectors `(K, round (K β))` of returns within `ε` span every
  direction: were they all on one rational hyperplane `n·ω = 0`, then `K·(n₀ + Σ nⱼ βⱼ)` would be
  the small quantity `Σ nⱼ · error`, and `n₀ + Σ nⱼ βⱼ ≠ 0` would bound `K` — against the returns
  past any bound (`span_returns`).
* **Rounding down.**  Take `d + 1` spanning returns, write the target in their errors, and round each
  coefficient down: the remainder is at most `d + 1` errors, each at most `ε`
  (`exists_step_near`).

Everything here is proved; no `sorry`, no `native_decide`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

namespace LRC.Stepping

open Module

variable {d : ℕ}

/-- `1, β₀, …, β_{d−1}` carry no rational relation. -/
def NoRelation (β : Fin d → ℝ) : Prop :=
  ∀ (c0 : ℚ) (c : Fin d → ℚ), (c0 : ℝ) + ∑ j, (c j : ℝ) * β j = 0 → c0 = 0 ∧ c = 0

/-- The error of the whole-number time `K` in direction `j`. -/
noncomputable def err (β : Fin d → ℝ) (K : ℤ) (j : Fin d) : ℝ := (K : ℝ) * β j - round ((K : ℝ) * β j)

/-- **Returns, by pigeonhole.**  Some `0 < K ≤ N^d` has every error below `1/N`. -/
theorem exists_return (β : Fin d → ℝ) {N : ℕ} (hN : 0 < N) :
    ∃ K : ℤ, 0 < K ∧ ∀ j, |err β K j| < 1 / N := by
  classical
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  -- the box of each time
  have hbox : ∀ (k : ℕ) (j : Fin d), ⌊(N : ℝ) * Int.fract ((k : ℝ) * β j)⌋₊ < N := by
    intro k j
    have h1 : (N : ℝ) * Int.fract ((k : ℝ) * β j) < N := by
      have := Int.fract_lt_one ((k : ℝ) * β j); nlinarith
    exact (Nat.floor_lt (by have := Int.fract_nonneg ((k : ℝ) * β j); positivity)).mpr h1
  let f : ℕ → (Fin d → Fin N) := fun k j => ⟨_, hbox k j⟩
  have hcard : (Finset.univ : Finset (Fin d → Fin N)).card < (Finset.range (N ^ d + 1)).card := by
    simp [Fintype.card_fin]
  obtain ⟨k1, -, k2, -, hne, hf⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard
    (f := f) (fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _))
  -- two times in the same box: their difference is a return
  have close : ∀ j, |Int.fract ((k2 : ℝ) * β j) - Int.fract ((k1 : ℝ) * β j)| < 1 / N := by
    intro j
    have hj := congrFun hf j
    simp only [f, Fin.mk.injEq] at hj
    set a := (N : ℝ) * Int.fract ((k1 : ℝ) * β j)
    set b := (N : ℝ) * Int.fract ((k2 : ℝ) * β j)
    have ha0 : 0 ≤ a := by have := Int.fract_nonneg ((k1 : ℝ) * β j); positivity
    have hb0 : 0 ≤ b := by have := Int.fract_nonneg ((k2 : ℝ) * β j); positivity
    have e1 := Nat.floor_le ha0
    have e2 := Nat.lt_floor_add_one a
    have e3 := Nat.floor_le hb0
    have e4 := Nat.lt_floor_add_one b
    rw [hj] at e1 e2
    have hab : |b - a| < 1 := by rw [abs_lt]; constructor <;> linarith
    rw [lt_div_iff₀ hN']
    calc |Int.fract ((k2 : ℝ) * β j) - Int.fract ((k1 : ℝ) * β j)| * N = |b - a| := by
          rw [show b - a = (Int.fract ((k2 : ℝ) * β j) - Int.fract ((k1 : ℝ) * β j)) * N by
            simp only [a, b]; ring, abs_mul, abs_of_pos hN']
      _ < 1 := hab
  have ret : ∀ K : ℤ, (∀ j, ∃ m : ℤ, |(K : ℝ) * β j - m| < 1 / N) → ∀ j, |err β K j| < 1 / N := by
    intro K h j
    obtain ⟨m, hm⟩ := h j
    exact lt_of_le_of_lt (round_le _ m) hm
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · refine ⟨(k2 : ℤ) - k1, by omega, ret _ fun j => ⟨⌊(k2 : ℝ) * β j⌋ - ⌊(k1 : ℝ) * β j⌋, ?_⟩⟩
    have := close j
    rw [Int.fract, Int.fract] at this
    push_cast
    convert this using 2; ring
  · refine ⟨(k1 : ℤ) - k2, by omega, ret _ fun j => ⟨⌊(k1 : ℝ) * β j⌋ - ⌊(k2 : ℝ) * β j⌋, ?_⟩⟩
    have := close j
    rw [Int.fract, Int.fract, abs_sub_comm] at this
    push_cast
    convert this using 2; ring

/-- With no rational relation, a non-zero time never returns exactly. -/
theorem err_ne_zero {β : Fin d → ℝ} (hβ : NoRelation β) (j0 : Fin d) {K : ℤ} (hK : K ≠ 0) :
    err β K j0 ≠ 0 := by
  intro h0
  have := hβ (-(round ((K : ℝ) * β j0) : ℚ)) (Pi.single j0 (K : ℚ)) (by
    rw [Finset.sum_eq_single j0 (fun j _ hj => by simp [hj]) (by simp)]
    simp only [Pi.single_eq_same]
    unfold err at h0; push_cast; linarith)
  have h2 := congrFun this.2 j0
  simp at h2
  exact hK h2

/-- **Returns past any bound.** -/
theorem exists_return_gt {β : Fin d → ℝ} (hβ : NoRelation β) (j0 : Fin d) {ε : ℝ} (hε : 0 < ε)
    (M : ℕ) : ∃ K : ℤ, (M : ℤ) < K ∧ ∀ j, |err β K j| ≤ ε := by
  classical
  -- the closest any early time comes back, in direction `j0`
  obtain ⟨δ, hδ, hδle⟩ : ∃ δ : ℝ, 0 < δ ∧ ∀ k ∈ Finset.Icc (1 : ℤ) M, δ ≤ |err β k j0| := by
    rcases (Finset.Icc (1 : ℤ) M).eq_empty_or_nonempty with he | hne
    · exact ⟨1, one_pos, by simp [he]⟩
    · obtain ⟨k0, hk0, hmin⟩ := (Finset.Icc (1 : ℤ) M).exists_min_image (fun k => |err β k j0|) hne
      refine ⟨|err β k0 j0|, abs_pos.mpr (err_ne_zero hβ j0 ?_), hmin⟩
      have := (Finset.mem_Icc.mp hk0).1; omega
  set μ : ℝ := min δ ε with hμ
  have hμ0 : 0 < μ := lt_min hδ hε
  set N : ℕ := ⌈1 / μ⌉₊ + 1 with hN
  have hN0 : 0 < N := by omega
  have hNμ : 1 / (N : ℝ) ≤ μ := by
    have h1 : 1 / μ ≤ (⌈1 / μ⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (N : ℝ) = (⌈1 / μ⌉₊ : ℝ) + 1 := by rw [hN]; push_cast; ring
    rw [div_le_iff₀ (by rw [h2]; positivity), h2]
    rw [div_le_iff₀ hμ0] at h1
    nlinarith
  obtain ⟨K, hK0, hK⟩ := exists_return β hN0
  refine ⟨K, ?_, fun j => le_trans (le_of_lt (lt_of_lt_of_le (hK j) hNμ)) (min_le_right _ _)⟩
  by_contra hle
  push Not at hle
  have hmem : K ∈ Finset.Icc (1 : ℤ) M := Finset.mem_Icc.mpr ⟨by omega, hle⟩
  have h1 := hδle K hmem
  have h2 := lt_of_lt_of_le (hK j0) (le_trans hNμ (min_le_left _ _))
  linarith

/-- The whole-number vector of a time: `(K, round (K β₀), …, round (K β_{d−1}))`. -/
noncomputable def omega (β : Fin d → ℝ) (K : ℤ) : Fin (d + 1) → ℚ :=
  Fin.cons (K : ℚ) (fun j => ((round ((K : ℝ) * β j) : ℤ) : ℚ))

/-- The whole-number vectors of the returns within `ε`. -/
def returns (β : Fin d → ℝ) (ε : ℝ) : Set (Fin (d + 1) → ℚ) :=
  {ω | ∃ K : ℤ, (∀ j, |err β K j| ≤ ε) ∧ ω = omega β K}

/-- **Returns span.**  With no rational relation, the returns within any `ε > 0` span every
direction: a rational hyperplane holding them all would bound their times. -/
theorem span_returns {β : Fin d → ℝ} (hβ : NoRelation β) (j0 : Fin d) {ε : ℝ} (hε : 0 < ε) :
    Submodule.span ℚ (returns β ε) = ⊤ := by
  classical
  by_contra hne
  obtain ⟨f, hf0, hmap⟩ :=
    Submodule.exists_dual_map_eq_bot_of_lt_top (lt_top_iff_ne_top.mpr hne) inferInstance
  set n : Fin (d + 1) → ℚ := fun i => f (fun j => if i = j then 1 else 0) with hn
  have hfω : ∀ ω, f ω = ∑ i, ω i * n i := by
    intro ω
    conv_lhs => rw [pi_eq_sum_univ ω]
    simp [map_sum, map_smul, n]
  have hvan : ∀ ω ∈ returns β ε, f ω = 0 := by
    intro ω hω
    have : f ω ∈ (Submodule.span ℚ (returns β ε)).map f :=
      Submodule.mem_map_of_mem (Submodule.subset_span hω)
    rw [hmap] at this
    simpa using this
  have hn0 : n ≠ 0 := by
    intro h
    apply hf0
    refine LinearMap.ext fun ω => ?_
    rw [hfω]
    simp [h]
  -- the hyperplane's reading of the direction `(1, β)`
  set γ : ℝ := (n 0 : ℝ) + ∑ j : Fin d, (n j.succ : ℝ) * β j with hγ
  have hγ0 : γ ≠ 0 := by
    intro h
    obtain ⟨h0, hc⟩ := hβ (n 0) (fun j : Fin d => n j.succ) h
    apply hn0
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa using h0
    · simpa using congrFun hc j
  set S : ℝ := ∑ j : Fin d, |(n j.succ : ℝ)| * ε with hS
  obtain ⟨K, hKM, hK⟩ := exists_return_gt hβ j0 hε ⌈S / |γ|⌉₊
  have h0 := hvan _ ⟨K, hK, rfl⟩
  rw [hfω] at h0
  have hq : ((∑ i, omega β K i * n i : ℚ) : ℝ) = 0 := by rw [h0]; simp
  rw [Fin.sum_univ_succ] at hq
  simp only [omega, Fin.cons_zero, Fin.cons_succ] at hq
  push_cast at hq
  -- `K·γ` is the small quantity `Σ nⱼ · error`
  have e1 : (K : ℝ) * γ = (K : ℝ) * n 0 + ∑ j, (K : ℝ) * ((n j.succ : ℝ) * β j) := by
    rw [hγ, mul_add, Finset.mul_sum]
  have e2 : ∑ j, (n j.succ : ℝ) * err β K j =
      ∑ j, (K : ℝ) * ((n j.succ : ℝ) * β j) - ∑ j, ((round ((K : ℝ) * β j) : ℤ) : ℝ) * n j.succ := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [err]; ring
  have hsum : (K : ℝ) * γ = ∑ j, (n j.succ : ℝ) * err β K j := by linarith
  have hbound : |(K : ℝ) * γ| ≤ S := by
    rw [hsum, hS]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun j _ => ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hK j) (abs_nonneg _)
  have hK0 : (0 : ℝ) < K := by
    have : (0 : ℤ) < K := lt_of_le_of_lt (by positivity) hKM
    exact_mod_cast this
  have hKbig : S / |γ| < K := by
    have h1 : S / |γ| ≤ (⌈S / |γ|⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : ((⌈S / |γ|⌉₊ : ℕ) : ℝ) < K := by exact_mod_cast hKM
    linarith
  have hγpos : 0 < |γ| := abs_pos.mpr hγ0
  rw [abs_mul, abs_of_pos hK0] at hbound
  rw [div_lt_iff₀ hγpos] at hKbig
  linarith

/-- **Stepping to any target.**  With no rational relation and at least one irrational direction,
whole-number times read within `η` of any target in every direction. -/
theorem exists_step_near {β : Fin d → ℝ} (hβ : NoRelation β) (j0 : Fin d) (x : Fin d → ℝ)
    {η : ℝ} (hη : 0 < η) :
    ∃ K : ℤ, ∃ P : Fin d → ℤ, ∀ j, |(K : ℝ) * β j - P j - x j| ≤ η := by
  classical
  set ε : ℝ := η / (d + 1) with hεdef
  have hε : 0 < ε := by positivity
  obtain ⟨b, hbT, hbspan, hli⟩ := exists_linearIndependent ℚ (returns β ε)
  rw [span_returns hβ j0 hε] at hbspan
  haveI : Fintype b := hli.setFinite.fintype
  have hcard : Fintype.card b ≤ d + 1 := by
    have := hli.fintype_card_le_finrank
    simpa [Module.finrank_fin_fun] using this
  -- each spanning vector is a return
  have hret : ∀ ω : b, ∃ K : ℤ, (∀ j, |err β K j| ≤ ε) ∧ (ω : Fin (d + 1) → ℚ) = omega β K :=
    fun ω => hbT ω.2
  choose Kof hKof hωof using hret
  -- the real reading of a whole-number vector: `ω₀ β − ω_tail`
  let L : (Fin (d + 1) → ℚ) →ₗ[ℚ] (Fin d → ℝ) :=
    { toFun := fun ω j => (ω 0 : ℝ) * β j - (ω j.succ : ℝ)
      map_add' := fun ω ω' => by funext j; simp; ring
      map_smul' := fun q ω => by funext j; simp [Rat.smul_def]; ring }
  have hLω : ∀ K : ℤ, ∀ k, L (omega β K) k = err β K k := by
    intro K k; simp [L, omega, err]
  have hLe : ∀ j k : Fin d, L (Pi.single j.succ 1) k = -(if k = j then 1 else 0) := by
    intro j k
    simp only [L, LinearMap.coe_mk, AddHom.coe_mk]
    rcases eq_or_ne k j with rfl | h
    · simp [Fin.succ_ne_zero]
    · simp [Fin.succ_ne_zero, h]
  -- write each direction in the spanning returns
  have hspan : ∀ j : Fin d, ∃ c : b → ℚ, ∑ ω, c ω • (ω : Fin (d + 1) → ℚ) = Pi.single j.succ 1 := by
    intro j
    have : (Pi.single j.succ (1 : ℚ) : Fin (d + 1) → ℚ) ∈
        Submodule.span ℚ (Set.range (Subtype.val : b → Fin (d + 1) → ℚ)) := by
      rw [Subtype.range_coe, hbspan]; trivial
    exact (Submodule.mem_span_range_iff_exists_fun ℚ).mp this
  choose c hc using hspan
  have hLc : ∀ j k : Fin d, ∑ ω, (c j ω : ℝ) * err β (Kof ω) k = -(if k = j then 1 else 0) := by
    intro j k
    have := congrArg (fun v => L v k) (hc j)
    simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, Rat.smul_def] at this
    rw [hLe] at this
    rw [← this]
    refine Finset.sum_congr rfl fun ω _ => ?_
    rw [hωof ω, hLω]
  -- the target in the returns' errors
  set lam : b → ℝ := fun ω => -∑ j, x j * (c j ω : ℝ) with hlam
  have hx : ∀ k, x k = ∑ ω, lam ω * err β (Kof ω) k := by
    intro k
    have : ∑ ω, lam ω * err β (Kof ω) k = -∑ j, x j * ∑ ω, (c j ω : ℝ) * err β (Kof ω) k := by
      simp only [hlam, neg_mul, Finset.sum_neg_distrib, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine congrArg _ (Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun ω _ => ?_)
      ring
    rw [this]
    simp only [hLc, mul_neg, mul_ite, mul_one, mul_zero, Finset.sum_neg_distrib, neg_neg,
      Finset.sum_ite_eq, Finset.mem_univ, if_true]
  -- round each coefficient down
  refine ⟨∑ ω, ⌊lam ω⌋ * Kof ω, fun k => ∑ ω, ⌊lam ω⌋ * round (((Kof ω : ℤ) : ℝ) * β k), fun k => ?_⟩
  have hrem : ((∑ ω, ⌊lam ω⌋ * Kof ω : ℤ) : ℝ) * β k -
      ((∑ ω, ⌊lam ω⌋ * round (((Kof ω : ℤ) : ℝ) * β k) : ℤ) : ℝ) - x k =
      -∑ ω, Int.fract (lam ω) * err β (Kof ω) k := by
    rw [hx k]
    push_cast
    rw [Finset.sum_mul, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun ω _ => ?_
    simp only [err, Int.fract]; ring
  rw [hrem, abs_neg]
  calc |∑ ω, Int.fract (lam ω) * err β (Kof ω) k|
      ≤ ∑ ω, |Int.fract (lam ω) * err β (Kof ω) k| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ω : b, ε := by
        refine Finset.sum_le_sum fun ω _ => ?_
        rw [abs_mul, abs_of_nonneg (Int.fract_nonneg _)]
        calc Int.fract (lam ω) * |err β (Kof ω) k| ≤ 1 * ε :=
              mul_le_mul (Int.fract_lt_one _).le (hKof ω k) (abs_nonneg _) zero_le_one
          _ = ε := one_mul _
    _ = Fintype.card b * ε := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ ≤ (d + 1) * ε := by
        apply mul_le_mul_of_nonneg_right _ hε.le
        exact_mod_cast hcard
    _ = η := by rw [hεdef]; field_simp

end LRC.Stepping
