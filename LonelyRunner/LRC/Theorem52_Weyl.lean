import LonelyRunner.LRC.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Topology.MetricSpace.Sequences

/-!
# Theorem 5.2 — Integer-Speed Equidistribution (CRT measure independence)

Source: `lrc_proof_v11_draft.md` §5.

**⚠️ CRITICAL DEPENDENCY — read carefully before attempting any other hard theorem.**

## What the manuscript calls "Weyl equidistribution"

The theorem as stated in the manuscript (Theorem 5.2) is **NOT** Weyl's classical
equidistribution theorem (which is an asymptotic/ergodic statement). Instead, it is
a **finite CRT measure-factorisation** result:

> If `G` has period `1/L` and `gcd(p, L) = 1`, then on the period `[0, 1/(L*p))`,
> the indicator `1_G(t)` depends only on `t mod 1/L`, and `1_{A}({p*t})` depends only
> on `t mod 1/p`.  By the Chinese Remainder Theorem, these are independent, so:
>   `μ({t ∈ G : {p*t} ∈ A}) = μ(G) * μ(A) > 0`.

## Mathlib assessment (2025)

- `ZMod.chineseRemainder` (integer CRT): EXISTS.
- `AddCircle` product decomposition: PARTIAL — the CRT for real circles when gcd=1
  is not directly stated as a measure-preserving map in this form.
- `MeasureTheory.Measure.prod` (product measure): EXISTS.
- `MeasureTheory.integral_prod` / Fubini: EXISTS.
- The specific bijection `φ : [0, 1/(Lp)) → [0,1/L) × [0,1/p)` as measure-preserving:
  NOT directly in Mathlib as a named lemma.

**Approach:** Use equidistribution (gcd-based) rather than explicit CRT bijection.
Shorter and avoids product measure machinery.
-/


open MeasureTheory Set Real

/-! ## §5.1  Classical Weyl theorem (reference, not used directly) -/

-- Classical Weyl equidistribution: for irrational α, the sequence {n*α} is
-- equidistributed mod 1.  This is Theorem 5.1 in the manuscript (stated for reference).
-- The actual engine is Theorem 5.2 below.
-- NOTE: Mathlib has `AddCircle.equidistributed_of_irrational` for irrational rotations.
-- We state this for completeness but do not use it in the proof.
-- Reference: Birkhoff ergodic theorem via MeasureTheory.tendsto_setAverage_atTop

/-! ## §5.2  The CRT independence lemma (Theorem 5.2) -/

/-- **Helper:** The period of `jointGoodSet speeds n` is `1 / Nat.lcm_of_speeds speeds`.

    Each `goodSet v_i n` has period `1/v_i`, so `jointGoodSet` has period
    `lcm(1/v_1, ..., 1/v_k) = 1 / lcm(v_1, ..., v_k)`. -/
noncomputable def lcmSpeeds {k : ℕ} (speeds : Fin k → ℕ) : ℕ :=
  Finset.lcm Finset.univ speeds

/-! ## §5.3  Periodicity of jointGoodSet -/

/-- Helper: if goodSet v n has period 1/v, then it also has period m * (1/v). -/
lemma goodSet_periodic_multiple
    (v n : ℕ) (hv : 0 < v) (t : ℝ) (m : ℕ) :
    t ∈ goodSet v n ↔ t + m * (1 / v : ℝ) ∈ goodSet v n := by
  induction m with
  | zero => simp
  | succ m' ih =>
    have hrw : t + (↑(m' + 1) : ℝ) * (1 / ↑v) = (t + ↑m' * (1 / ↑v)) + 1 / ↑v := by
      push_cast; ring
    rw [hrw, ← goodSet_periodic v n hv]
    exact ih

/-- The simultaneous good set is periodic with period `1`.

    Each `goodSet v_i n` has period `1/v_i`.  Since each `v_i` is a positive integer,
    `v_i * (1/v_i) = 1`, so `goodSet v_i n` also has period 1.  The intersection
    `jointGoodSet speeds n = ⋂ i, goodSet (speeds i) n` therefore has period 1. -/
theorem jointGoodSet_periodic
    {k : ℕ} (speeds : Fin k → ℕ) (n : ℕ)
    (hpos : ∀ j, 0 < speeds j) :
    ∀ t : ℝ, t ∈ jointGoodSet speeds n ↔ t + 1 ∈ jointGoodSet speeds n := by
  intro t
  simp only [jointGoodSet, Set.mem_iInter]
  apply forall_congr'
  intro i
  have hvi := hpos i
  have hshift : (↑(speeds i) : ℝ) * (1 / ↑(speeds i)) = 1 := by
    field_simp
  have step := goodSet_periodic_multiple (speeds i) n hvi t (speeds i)
  rw [hshift] at step
  exact step

/-- Helper: CRT bijection property for reals.
    When gcd(p,L)=1, the map φ(t) = (p*t, L*t) is a bijection from [0, 1/(Lp)) to [0,1/L)×[0,1/p). -/
lemma crt_bijection_structure
    (L p : ℕ) (hcop : Nat.Coprime p L) (hL_pos : 0 < L) (hp_pos : 0 < p) :
    ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) (1 / (L * p)) →
      ((p : ℝ) * t ∈ Set.Icc (0 : ℝ) (1 / L)) ∧
      ((L : ℝ) * t ∈ Set.Icc (0 : ℝ) (1 / p)) := by
  intro t ⟨ht_nonneg, ht_le⟩
  constructor
  · constructor
    · exact mul_nonneg (by norm_num : (0 : ℝ) ≤ p) ht_nonneg
    · calc (p : ℝ) * t ≤ p * (1 / (L * p)) := by
            apply mul_le_mul_of_nonneg_left ht_le
            norm_num
          _ = p / (L * p) := by ring
          _ = 1 / L := by
              have hL : (L : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hL_pos.ne'
              have hp : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hp_pos.ne'
              field_simp
  · constructor
    · exact mul_nonneg (by norm_num : (0 : ℝ) ≤ L) ht_nonneg
    · calc (L : ℝ) * t ≤ L * (1 / (L * p)) := by
            apply mul_le_mul_of_nonneg_left ht_le
            norm_num
          _ = L / (L * p) := by ring
          _ = 1 / p := by
              have hL : (L : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hL_pos.ne'
              have hp : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hp_pos.ne'
              field_simp

/-- Helper: Injectivity of the CRT map via coprimality.
    If p*t₁ ≡ p*t₂ (mod 1) and L*t₁ ≡ L*t₂ (mod 1) with gcd(p,L)=1,
    then t₁ ≡ t₂ (mod 1/(Lp)). -/
lemma crt_map_injective
    (L p : ℕ) (hcop : Nat.Coprime p L) (hL_pos : 0 < L) (hp_pos : 0 < p)
    (t₁ t₂ : ℝ) (ht₁ : t₁ ∈ Set.Ico (0 : ℝ) (1 / (L * p)))
    (ht₂ : t₂ ∈ Set.Ico (0 : ℝ) (1 / (L * p)))
    (hp_eq : Int.fract ((p : ℝ) * t₁) = Int.fract ((p : ℝ) * t₂))
    (hL_eq : Int.fract ((L : ℝ) * t₁) = Int.fract ((L : ℝ) * t₂)) :
    t₁ = t₂ := by
  obtain ⟨ht₁_nn, ht₁_lt⟩ := ht₁
  obtain ⟨ht₂_nn, ht₂_lt⟩ := ht₂
  have hp_cast : (0 : ℝ) < (p : ℝ) := Nat.cast_pos.mpr hp_pos
  have hL_cast : (0 : ℝ) < (L : ℝ) := Nat.cast_pos.mpr hL_pos
  -- Since t ∈ [0, 1/(L*p)), we have p*t ∈ [0, 1/L) ⊆ [0, 1), so Int.fract(p*t) = p*t.
  have hpLp : (p : ℝ) * (1 / ((L : ℝ) * p)) = 1 / L := by field_simp
  have h1L : (1 : ℝ) / L ≤ 1 := by
    rw [div_le_one hL_cast]; norm_cast
  have h1 : Int.fract ((p : ℝ) * t₁) = (p : ℝ) * t₁ := by
    apply Int.fract_eq_self.mpr
    refine ⟨mul_nonneg hp_cast.le ht₁_nn, ?_⟩
    have hbound : (p : ℝ) * t₁ < 1 / (L : ℝ) := by
      have := mul_lt_mul_of_pos_left ht₁_lt hp_cast
      linarith [hpLp]
    linarith
  have h2 : Int.fract ((p : ℝ) * t₂) = (p : ℝ) * t₂ := by
    apply Int.fract_eq_self.mpr
    refine ⟨mul_nonneg hp_cast.le ht₂_nn, ?_⟩
    have hbound : (p : ℝ) * t₂ < 1 / (L : ℝ) := by
      have := mul_lt_mul_of_pos_left ht₂_lt hp_cast
      linarith [hpLp]
    linarith
  have heq : (p : ℝ) * t₁ = (p : ℝ) * t₂ := by rw [← h1, ← h2]; exact hp_eq
  exact mul_left_cancel₀ hp_cast.ne' heq

/-- Helper: measure equivalence for indicator functions.
    If A is measurable, then the volume of the set where an indicator is 1 equals the volume of A. -/
lemma volume_indicator_eq (A : Set ℝ) (hA : MeasurableSet A) :
    MeasureTheory.volume {t | t ∈ A} = MeasureTheory.volume A := by
  rfl

/- **Route B: Discrete CRT approach via cell partition and index bijectivity**

   Core independence lemma: when gcd(L, p) = 1, the random variables
   {L*T} and {p*T} are independent on T uniform on [0,1).

   Proof strategy: Partition [0,1) into L·p cells of width 1/(L·p).
   On cell m, both {L*T} and {p*T} are determined by m mod L and m mod p respectively.
   By CRT, the map m ↦ (m mod L, m mod p) is a bijection, yielding independence.
-/

/-- Helper: Measure of a cell [a, b) in ℝ. -/
lemma volume_Ico_cell (a b : ℝ) (hab : a ≤ b) :
    MeasureTheory.volume (Set.Ico a b) = ENNReal.ofReal (b - a) := by
  exact Real.volume_Ico

/-- Helper: CRT bijectivity on indices.
    When gcd(L, p) = 1, the map m ↦ (m mod L, m mod p) is a bijection
    from Fin(L*p) to Fin(L) × Fin(p). -/
lemma crt_index_bijection (L p : ℕ) (hL : 0 < L) (hp : 0 < p) (hcop : Nat.Coprime L p) :
    Function.Bijective (fun m : Fin (L * p) =>
      ((⟨m.val % L, Nat.mod_lt _ hL⟩ : Fin L), (⟨m.val % p, Nat.mod_lt _ hp⟩ : Fin p))) := by
  constructor
  · -- Injectivity: if (m₁ % L, m₁ % p) = (m₂ % L, m₂ % p) then m₁ = m₂.
    intro m₁ m₂ h
    simp only [Prod.mk.injEq, Fin.mk.injEq] at h
    obtain ⟨hL_eq, hp_eq⟩ := h
    -- hL_eq : m₁.val % L = m₂.val % L  (i.e. m₁.val ≡ m₂.val [MOD L])
    -- hp_eq : m₁.val % p = m₂.val % p  (i.e. m₁.val ≡ m₂.val [MOD p])
    have hmodL : m₁.val ≡ m₂.val [MOD L] := hL_eq
    have hmodp : m₁.val ≡ m₂.val [MOD p] := hp_eq
    have hmodLp : m₁.val ≡ m₂.val [MOD L * p] :=
      (Nat.modEq_and_modEq_iff_modEq_mul hcop).mp ⟨hmodL, hmodp⟩
    exact Fin.ext (hmodLp.eq_of_lt_of_lt m₁.isLt m₂.isLt)
  · -- Surjectivity: given (a, b) : Fin L × Fin p, use chineseRemainder to find k.
    intro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    refine ⟨⟨(Nat.chineseRemainder hcop a b : ℕ),
              Nat.chineseRemainder_lt_mul hcop a b hL.ne' hp.ne'⟩, ?_⟩
    simp only [Prod.mk.injEq, Fin.mk.injEq]
    obtain ⟨hkL, hkp⟩ := (Nat.chineseRemainder hcop a b).prop
    -- hkL : k % L = a % L, and a % L = a since a < L
    have hkL_eq : (Nat.chineseRemainder hcop a b : ℕ) % L = a % L := hkL
    have hkp_eq : (Nat.chineseRemainder hcop a b : ℕ) % p = b % p := hkp
    exact ⟨hkL_eq.trans (Nat.mod_eq_of_lt ha), hkp_eq.trans (Nat.mod_eq_of_lt hb)⟩



/-- **Step 3 of Theorem 5.2** (compactness limit).

    Given a sequence `tSeq j ∈ G ∩ [0,B]` and `α j → p` with `circDist(α j * tSeq j) ≥ 1/n`,
    extract a subsequence converging to `t₀ ∈ G` with `circDist(p * t₀) ≥ 1/n`.

    This lemma isolates the Bolzano-Weierstrass + continuity argument from the
    Weyl equidistribution step (Step 1). -/
lemma compactness_limit_in_good
    {k : ℕ} (speeds : Fin k → ℕ) (n p : ℕ)
    (B : ℝ) (hB : 0 ≤ B)
    (α : ℕ → ℝ)
    (tSeq : ℕ → ℝ)
    (hα_conv : Filter.Tendsto α Filter.atTop (nhds (p : ℝ)))
    (htSeq_bdd : ∀ j, tSeq j ∈ Set.Icc 0 B)
    (htSeq_G : ∀ j, tSeq j ∈ jointGoodSet speeds n)
    (htSeq_circ : ∀ j, circDist ((α j) * (tSeq j)) ≥ (1 : ℝ) / n) :
    ∃ t₀ ∈ jointGoodSet speeds n, circDist ((p : ℝ) * t₀) ≥ (1 : ℝ) / n := by
  -- Step 3a: Extract convergent subsequence from compact [0, B]
  obtain ⟨t₀, ht₀_bdd, φ, hφ_mono, hφ_conv⟩ := isCompact_Icc.tendsto_subseq htSeq_bdd
  -- Step 3b: t₀ ∈ G since G is closed (jointGoodSet_isClosed) and tSeq φ j → t₀
  have hG_closed : IsClosed (jointGoodSet speeds n) :=
    jointGoodSet_isClosed speeds n
  have ht₀_G : t₀ ∈ jointGoodSet speeds n :=
    hG_closed.mem_of_tendsto hφ_conv (Filter.Eventually.of_forall (fun j => htSeq_G (φ j)))
  -- Step 3c: circDist(p * t₀) ≥ 1/n by continuity
  -- α(φ j) * tSeq(φ j) → p * t₀
  have hprod_conv : Filter.Tendsto (fun j => α (φ j) * tSeq (φ j)) Filter.atTop
      (nhds ((p : ℝ) * t₀)) :=
    hα_conv.comp hφ_mono.tendsto_atTop |>.mul hφ_conv
  -- circDist is continuous, so the composition converges
  have hcirc_conv : Filter.Tendsto (fun j => circDist (α (φ j) * tSeq (φ j))) Filter.atTop
      (nhds (circDist ((p : ℝ) * t₀))) :=
    circDist_continuous.continuousAt.tendsto.comp hprod_conv
  -- The limit inherits the ≥ 1/n lower bound from every term (ge_of_tendsto')
  have ht₀_circ : (1 : ℝ) / n ≤ circDist ((p : ℝ) * t₀) :=
    ge_of_tendsto' hcirc_conv (fun j => htSeq_circ (φ j))
  exact ⟨t₀, ht₀_G, ht₀_circ⟩

/-! ### Historical note (deleted): `theorem52_nonempty_correct`

    The previously-stated general form of Theorem 5.2 (∃ t ∈ G with fract(p·t) ∈ A
    for any closed positive-measure A) is **FALSE** — see `theorem52_counterexample_claim`
    in §5.5 (`n = 5`, `G_speeds = [1, 2]`, `p = 3`, `A = [9/20, 11/20]`).

    The replacement is `theorem52_nonempty_structured` (§5.6) which restricts `A`
    to be a `jointGoodSet A_speeds n`. Both downstream callers (Theorems 10.1 and
    11.1) supply such structured `A`, so the restriction loses nothing in practice. -/

/-! ## §5.4  Cell decomposition of `goodSet` (Route 3 foundation)

    The CRT cell-counting argument for Theorem 5.2 needs `goodSet v n` to be
    expressible as a finite union of intervals. The lemmas in this section
    provide the per-period characterisation that makes the cell decomposition
    explicit.

    **Mathematical content.** For one fundamental period `[0, 1/v)`,
    `circDist(v·t) = min(v·t, 1 - v·t)` (no wrap-around), so the condition
    `circDist(v·t) ≥ 1/n` reduces to `v·t ∈ [1/n, (n-1)/n]`, i.e.
    `t ∈ [1/(n·v), (n-1)/(n·v)]`. -/

/-- **Step 1 of Route 3.** Characterise `goodSet v n` on the fundamental period
    `[0, 1/v)` as a single closed interval `[1/(n·v), (n-1)/(n·v)]`.

    This is the per-period building block: combined with periodicity
    (`goodSet_periodic`), it expresses `goodSet v n ∩ [0, 1)` as a union of `v`
    closed intervals, each of measure `(n-2)/(n·v)`. -/
theorem goodSet_period_characterization (v n : ℕ) (hv : 0 < v) (hn : 2 ≤ n)
    (t : ℝ) (ht : t ∈ Set.Ico (0 : ℝ) (1 / (v : ℝ))) :
    t ∈ goodSet v n ↔
      t ∈ Set.Icc ((1 : ℝ) / ((n : ℝ) * v)) (((n : ℝ) - 1) / ((n : ℝ) * v)) := by
  obtain ⟨ht0, ht_v⟩ := ht
  have hv_r : (0 : ℝ) < (v : ℝ) := Nat.cast_pos.mpr hv
  have hn_r : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  have hnv_r : (0 : ℝ) < (n : ℝ) * v := mul_pos hn_r hv_r
  -- v·t ∈ [0, 1), so fract(v·t) = v·t.
  have hvt_lt1 : (v : ℝ) * t < 1 := by
    have h : (v : ℝ) * t < (v : ℝ) * (1 / v) := mul_lt_mul_of_pos_left ht_v hv_r
    rwa [mul_one_div, div_self hv_r.ne'] at h
  have hfract : Int.fract ((v : ℝ) * t) = (v : ℝ) * t :=
    Int.fract_eq_self.mpr ⟨mul_nonneg hv_r.le ht0, hvt_lt1⟩
  simp only [goodSet, Set.mem_setOf_eq, Set.mem_Icc, circDist, hfract, le_min_iff]
  -- Key arithmetic identities
  have hbound1 : (1 : ℝ) / ((n : ℝ) * v) * v = 1 / n := by field_simp
  have hbound2 : ((n : ℝ) - 1) / ((n : ℝ) * v) * v = ((n : ℝ) - 1) / n := by field_simp
  have hcompl : 1 - ((n : ℝ) - 1) / n = 1 / n := by
    field_simp; ring
  constructor
  · rintro ⟨h1, h2⟩
    -- From h1: 1/n ≤ v·t. Want 1/(n·v) ≤ t.
    -- Divide h1 by v (positive): 1/(n·v) ≤ t.
    have hL : (1 : ℝ) / ((n : ℝ) * v) ≤ t := by
      have hkey : (1 : ℝ) / ((n : ℝ) * v) * v ≤ (v : ℝ) * t := by
        rw [hbound1]; exact h1
      have hcomm : (1 : ℝ) / ((n : ℝ) * v) * v = v * (1 / ((n : ℝ) * v)) := by ring
      rw [hcomm] at hkey
      exact le_of_mul_le_mul_left (by linarith : (v : ℝ) * (1 / ((n : ℝ) * v)) ≤ v * t) hv_r
    -- From h2: 1/n ≤ 1 - v·t, i.e., v·t ≤ (n-1)/n. Divide by v.
    have hR : t ≤ ((n : ℝ) - 1) / ((n : ℝ) * v) := by
      have hvt_le : (v : ℝ) * t ≤ ((n : ℝ) - 1) / n := by linarith
      have hkey : (v : ℝ) * t ≤ ((n : ℝ) - 1) / ((n : ℝ) * v) * v := by
        rw [hbound2]; exact hvt_le
      have hcomm : ((n : ℝ) - 1) / ((n : ℝ) * v) * v = v * (((n : ℝ) - 1) / ((n : ℝ) * v)) := by
        ring
      rw [hcomm] at hkey
      exact le_of_mul_le_mul_left hkey hv_r
    exact ⟨hL, hR⟩
  · rintro ⟨h1, h2⟩
    -- From h1: 1/(n·v) ≤ t. Multiply by v: 1/n ≤ v·t.
    have hL : (1 : ℝ) / n ≤ (v : ℝ) * t := by
      have := mul_le_mul_of_nonneg_left h1 hv_r.le
      have hcomm : (v : ℝ) * (1 / ((n : ℝ) * v)) = 1 / n := by field_simp
      linarith [hcomm]
    -- From h2: t ≤ (n-1)/(n·v). Multiply by v: v·t ≤ (n-1)/n. Then 1/n ≤ 1 - v·t.
    have hR : (1 : ℝ) / n ≤ 1 - (v : ℝ) * t := by
      have := mul_le_mul_of_nonneg_left h2 hv_r.le
      have hcomm : (v : ℝ) * (((n : ℝ) - 1) / ((n : ℝ) * v)) = ((n : ℝ) - 1) / n := by
        field_simp
      linarith [hcomm]
    exact ⟨hL, hR⟩

/-- **Step 2 of Route 3 (forward direction).** Cell-decomposition forward inclusion.

    For `m < n·v` with `m mod n ∈ [1, n-2]`, the open cell `(m/(nv), (m+1)/(nv))`
    is contained in `goodSet v n`. These are the "good cells" in the partition
    of `[0, 1)` into `n·v` cells of width `1/(n·v)`.

    Proof uses periodicity to reduce to the fundamental period via
    `goodSet_periodic_multiple` and then applies `goodSet_period_characterization`. -/
theorem goodSet_contains_cell (v n m : ℕ) (hv : 0 < v) (hn : 2 ≤ n)
    (hm_lt : m < n * v) (h_lo : 1 ≤ m % n) (h_hi : m % n + 1 < n) :
    Set.Ioo ((m : ℝ) / ((n : ℝ) * v)) (((m : ℝ) + 1) / ((n : ℝ) * v)) ⊆ goodSet v n := by
  intro t ⟨ht_l, ht_r⟩
  have hv_r : (0 : ℝ) < (v : ℝ) := Nat.cast_pos.mpr hv
  have hn_r : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  have hnv_r : (0 : ℝ) < (n : ℝ) * v := mul_pos hn_r hv_r
  -- m = k·n + r where k = m/n, r = m%n.
  set k : ℕ := m / n with hk_def
  set r : ℕ := m % n with hr_def
  have hkr : m = k * n + r := by
    show m = (m / n) * n + m % n
    rw [Nat.mul_comm]
    exact (Nat.div_add_mod m n).symm
  have h_r_lt_n : r < n := by simp only [hr_def]; exact Nat.mod_lt m (by omega)
  -- s := t - k/v shifts the cell back to the fundamental period.
  set s : ℝ := t - (k : ℝ) / v with hs_def
  have h_t_eq : t = s + (k : ℝ) * (1 / v) := by
    rw [hs_def]; field_simp; ring
  -- Decompose m/(nv) = k/v + r/(nv) and similarly for (m+1)/(nv).
  have hmcast : (m : ℝ) = (k : ℝ) * n + r := by exact_mod_cast hkr
  have hm_eq : (m : ℝ) / ((n : ℝ) * v) = (k : ℝ) / v + (r : ℝ) / ((n : ℝ) * v) := by
    rw [hmcast]; field_simp
  have hm1_eq : ((m : ℝ) + 1) / ((n : ℝ) * v) =
      (k : ℝ) / v + ((r : ℝ) + 1) / ((n : ℝ) * v) := by
    rw [show (m : ℝ) + 1 = (k : ℝ) * n + (r + 1) from by linarith [hmcast]]
    field_simp
  have hs_l : (r : ℝ) / ((n : ℝ) * v) < s := by rw [hs_def]; linarith [hm_eq]
  have hs_r : s < ((r : ℝ) + 1) / ((n : ℝ) * v) := by rw [hs_def]; linarith [hm1_eq]
  -- s ∈ [0, 1/v).
  have hs_lo : (0 : ℝ) ≤ s := by
    have : (0 : ℝ) ≤ (r : ℝ) / ((n : ℝ) * v) :=
      div_nonneg (Nat.cast_nonneg r) hnv_r.le
    linarith
  have hs_hi : s < 1 / v := by
    have h_r1le : ((r : ℝ) + 1) / ((n : ℝ) * v) ≤ 1 / v := by
      rw [div_le_div_iff₀ hnv_r hv_r, one_mul]
      have hrn : (r : ℝ) + 1 ≤ n := by exact_mod_cast h_r_lt_n
      exact mul_le_mul_of_nonneg_right hrn hv_r.le
    linarith
  -- Periodicity: t ∈ goodSet ↔ s ∈ goodSet.
  rw [h_t_eq, ← goodSet_periodic_multiple v n hv s k]
  -- Per-period characterisation: s ∈ goodSet ↔ s ∈ [1/(nv), (n-1)/(nv)].
  rw [goodSet_period_characterization v n hv hn s ⟨hs_lo, hs_hi⟩]
  refine ⟨?_, ?_⟩
  · -- 1/(nv) ≤ r/(nv) < s.
    have h1_le_r : (1 : ℝ) / ((n : ℝ) * v) ≤ (r : ℝ) / ((n : ℝ) * v) := by
      rw [div_le_div_iff_of_pos_right hnv_r]
      exact_mod_cast h_lo
    linarith
  · -- s < (r+1)/(nv) ≤ (n-1)/(nv).
    have h_r1_le_n1 : ((r : ℝ) + 1) / ((n : ℝ) * v) ≤ ((n : ℝ) - 1) / ((n : ℝ) * v) := by
      rw [div_le_div_iff_of_pos_right hnv_r]
      have h_r_le : r + 2 ≤ n := h_hi
      have h1 : ((r : ℝ) + 2) ≤ (n : ℝ) := by exact_mod_cast h_r_le
      linarith
    linarith

/-- **Step 3 of Route 3 (reverse direction).** Cell-decomposition reverse inclusion.

    For `m < n·v` with `m mod n ∈ {0, n-1}`, the open cell
    `(m/(n·v), (m+1)/(n·v))` is **disjoint** from `goodSet v n`. These are the
    "bad cells" — the boundary cells of the partition where `fract(v·t)`
    lands in `(0, 1/n) ∪ ((n-1)/n, 1)`.

    Combined with Step 2 (`goodSet_contains_cell`), every open `1/(n·v)`-cell
    is either fully in or fully out of `goodSet v n`, giving the complete
    cell-decomposition. -/
theorem goodSet_disjoint_cell (v n m : ℕ) (hv : 0 < v) (hn : 2 ≤ n)
    (hm_lt : m < n * v) (h_bad : m % n = 0 ∨ m % n + 1 = n) :
    Disjoint (Set.Ioo ((m : ℝ) / ((n : ℝ) * v)) (((m : ℝ) + 1) / ((n : ℝ) * v)))
             (goodSet v n) := by
  rw [Set.disjoint_left]
  intro t ⟨ht_l, ht_r⟩ htg
  have hv_r : (0 : ℝ) < (v : ℝ) := Nat.cast_pos.mpr hv
  have hn_r : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  have hnv_r : (0 : ℝ) < (n : ℝ) * v := mul_pos hn_r hv_r
  -- Same periodicity reduction as Step 2.
  set k : ℕ := m / n with hk_def
  set r : ℕ := m % n with hr_def
  have hkr : m = k * n + r := by
    show m = (m / n) * n + m % n
    rw [Nat.mul_comm]
    exact (Nat.div_add_mod m n).symm
  have h_r_lt_n : r < n := Nat.mod_lt m (by omega)
  set s : ℝ := t - (k : ℝ) / v with hs_def
  have h_t_eq : t = s + (k : ℝ) * (1 / v) := by rw [hs_def]; field_simp; ring
  have hmcast : (m : ℝ) = (k : ℝ) * n + r := by exact_mod_cast hkr
  have hm_eq : (m : ℝ) / ((n : ℝ) * v) = (k : ℝ) / v + (r : ℝ) / ((n : ℝ) * v) := by
    rw [hmcast]; field_simp
  have hm1_eq : ((m : ℝ) + 1) / ((n : ℝ) * v) =
      (k : ℝ) / v + ((r : ℝ) + 1) / ((n : ℝ) * v) := by
    rw [show (m : ℝ) + 1 = (k : ℝ) * n + (r + 1) from by linarith [hmcast]]
    field_simp
  have hs_l : (r : ℝ) / ((n : ℝ) * v) < s := by rw [hs_def]; linarith [hm_eq]
  have hs_r : s < ((r : ℝ) + 1) / ((n : ℝ) * v) := by rw [hs_def]; linarith [hm1_eq]
  have hs_lo : (0 : ℝ) ≤ s := by
    have : (0 : ℝ) ≤ (r : ℝ) / ((n : ℝ) * v) :=
      div_nonneg (Nat.cast_nonneg r) hnv_r.le
    linarith
  have hs_hi : s < 1 / v := by
    have h_r1le : ((r : ℝ) + 1) / ((n : ℝ) * v) ≤ 1 / v := by
      rw [div_le_div_iff₀ hnv_r hv_r, one_mul]
      have hrn : (r : ℝ) + 1 ≤ n := by exact_mod_cast h_r_lt_n
      exact mul_le_mul_of_nonneg_right hrn hv_r.le
    linarith
  -- Apply periodicity and per-period characterisation to htg.
  rw [h_t_eq, ← goodSet_periodic_multiple v n hv s k] at htg
  rw [goodSet_period_characterization v n hv hn s ⟨hs_lo, hs_hi⟩] at htg
  obtain ⟨hgL, hgR⟩ := htg
  -- Case split on which bad-cell condition holds.
  rcases h_bad with h0 | hn1
  · -- r = 0: hs_r gives s < 1/(n·v); contradicts hgL : 1/(n·v) ≤ s.
    have hr0 : (r : ℝ) = 0 := by exact_mod_cast h0
    rw [hr0] at hs_r
    have : ((0 : ℝ) + 1) / ((n : ℝ) * v) = 1 / ((n : ℝ) * v) := by ring
    rw [this] at hs_r
    linarith
  · -- r + 1 = n (i.e., r = n-1): hs_l gives (n-1)/(n·v) < s; contradicts hgR.
    have hr1n : (r : ℝ) + 1 = (n : ℝ) := by exact_mod_cast hn1
    have hrn1 : (r : ℝ) = (n : ℝ) - 1 := by linarith
    rw [hrn1] at hs_l
    linarith

/-- **Helper for Step 4.** Cell-inclusion: if `v ∣ L`, then the `1/(n·L)`-cell
    at index `m` is contained in the `1/(n·v)`-cell at index `m / (L/v)`.

    This says the fine partition of width `1/(n·L)` refines the coarser
    partition of width `1/(n·v)` for each runner with `v ∣ L`. -/
lemma cell_inclusion (v L n : ℕ) (hv : 0 < v) (hL : 0 < L) (hn : 0 < n)
    (hdvd : v ∣ L) (m : ℕ) :
    Set.Ioo ((m : ℝ) / ((n : ℝ) * L)) (((m : ℝ) + 1) / ((n : ℝ) * L)) ⊆
    Set.Ioo (((m / (L / v) : ℕ) : ℝ) / ((n : ℝ) * v))
            ((((m / (L / v) : ℕ) : ℝ) + 1) / ((n : ℝ) * v)) := by
  intro t ⟨ht_l, ht_r⟩
  set q := L / v with hq_def
  set m' := m / q with hm'_def
  have hvq : v * q = L := Nat.mul_div_cancel' hdvd
  have hq_pos : 0 < q := Nat.div_pos (Nat.le_of_dvd hL hdvd) hv
  have hv_r : (0 : ℝ) < (v : ℝ) := Nat.cast_pos.mpr hv
  have hL_r : (0 : ℝ) < (L : ℝ) := Nat.cast_pos.mpr hL
  have hn_r : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hnv_r : (0 : ℝ) < (n : ℝ) * v := mul_pos hn_r hv_r
  have hnL_r : (0 : ℝ) < (n : ℝ) * L := mul_pos hn_r hL_r
  -- Nat-level arithmetic: m'*L ≤ m*v  and  (m+1)*v ≤ (m'+1)*L.
  have h_lower_nat : m' * L ≤ m * v := by
    have h : m' * q ≤ m := Nat.div_mul_le_self m q
    calc m' * L = (m' * q) * v := by rw [← hvq]; ring
      _ ≤ m * v := Nat.mul_le_mul_right v h
  have h_upper_nat : (m + 1) * v ≤ (m' + 1) * L := by
    have h1 : m = m' * q + m % q := by
      show m = (m / q) * q + m % q
      rw [Nat.mul_comm]; exact (Nat.div_add_mod m q).symm
    have h2 : m % q < q := Nat.mod_lt m hq_pos
    have h_m1 : m + 1 ≤ (m' + 1) * q := by
      have heq : (m' + 1) * q = m' * q + q := by ring
      omega
    calc (m + 1) * v ≤ ((m' + 1) * q) * v := Nat.mul_le_mul_right v h_m1
      _ = (m' + 1) * L := by rw [← hvq]; ring
  refine ⟨?_, ?_⟩
  · -- (m' : ℝ) / (n·v) ≤ m / (n·L) < t
    have h_le : (m' : ℝ) / ((n : ℝ) * v) ≤ (m : ℝ) / ((n : ℝ) * L) := by
      rw [div_le_div_iff₀ hnv_r hnL_r]
      have hkey : (m' : ℝ) * L ≤ (m : ℝ) * v := by exact_mod_cast h_lower_nat
      calc (m' : ℝ) * ((n : ℝ) * L) = (n : ℝ) * ((m' : ℝ) * L) := by ring
        _ ≤ (n : ℝ) * ((m : ℝ) * v) := mul_le_mul_of_nonneg_left hkey hn_r.le
        _ = (m : ℝ) * ((n : ℝ) * v) := by ring
    linarith
  · -- t < (m+1)/(n·L) ≤ (m'+1)/(n·v)
    have h_le : ((m : ℝ) + 1) / ((n : ℝ) * L) ≤ ((m' : ℝ) + 1) / ((n : ℝ) * v) := by
      rw [div_le_div_iff₀ hnL_r hnv_r]
      have hkey : ((m : ℝ) + 1) * v ≤ ((m' : ℝ) + 1) * L := by
        have h := h_upper_nat
        have : ((m + 1 : ℕ) : ℝ) * v ≤ ((m' + 1 : ℕ) : ℝ) * L := by exact_mod_cast h
        push_cast at this
        exact this
      calc ((m : ℝ) + 1) * ((n : ℝ) * v) = (n : ℝ) * (((m : ℝ) + 1) * v) := by ring
        _ ≤ (n : ℝ) * (((m' : ℝ) + 1) * L) := mul_le_mul_of_nonneg_left hkey hn_r.le
        _ = ((m' : ℝ) + 1) * ((n : ℝ) * L) := by ring
    linarith

/-- **Step 4 of Route 3 (forward direction).** Joint cell-decomposition.

    For `L = lcmSpeeds speeds` and `m < n·L`, if for every runner `j` the
    coarser cell containing the `1/(n·L)`-cell at `m` is a "good cell" (i.e.,
    `(m / (L / speeds j)) mod n ∈ [1, n-2]`), then the open cell
    `(m/(n·L), (m+1)/(n·L))` is contained in `jointGoodSet speeds n`.

    This lifts the per-runner Step 2 to all runners simultaneously via the
    cell-inclusion lemma. -/
theorem jointGoodSet_contains_cell
    {k : ℕ} (speeds : Fin k → ℕ) (n : ℕ) (hn : 2 ≤ n)
    (L : ℕ) (hL : L = lcmSpeeds speeds) (hL_pos : 0 < L)
    (hpos : ∀ j, 0 < speeds j)
    (m : ℕ) (hm_lt : m < n * L)
    (h_good : ∀ j : Fin k,
      1 ≤ (m / (L / speeds j)) % n ∧
      (m / (L / speeds j)) % n + 1 < n) :
    Set.Ioo ((m : ℝ) / ((n : ℝ) * L)) (((m : ℝ) + 1) / ((n : ℝ) * L)) ⊆
      jointGoodSet speeds n := by
  intro t ht
  simp only [jointGoodSet, Set.mem_iInter]
  intro j
  have hv_pos : 0 < speeds j := hpos j
  have hv_dvd : speeds j ∣ L := by
    rw [hL]; simp only [lcmSpeeds]
    exact Finset.dvd_lcm (Finset.mem_univ j)
  have hq_pos : 0 < L / speeds j :=
    Nat.div_pos (Nat.le_of_dvd hL_pos hv_dvd) hv_pos
  have hvq : speeds j * (L / speeds j) = L := Nat.mul_div_cancel' hv_dvd
  set m' := m / (L / speeds j) with hm'_def
  have hm'_lt : m' < n * speeds j := by
    rw [hm'_def, Nat.div_lt_iff_lt_mul hq_pos]
    rw [show (n * speeds j) * (L / speeds j) =
            n * (speeds j * (L / speeds j)) from by ring, hvq]
    exact hm_lt
  obtain ⟨h_lo, h_hi⟩ := h_good j
  -- Cell inclusion lifts t to runner j's coarser partition.
  have h_sub := cell_inclusion (speeds j) L n hv_pos hL_pos (by omega) hv_dvd m
  exact goodSet_contains_cell (speeds j) n m' hv_pos hn hm'_lt h_lo h_hi (h_sub ht)

/-- **Step 4 of Route 3 (reverse direction).** Joint cell-decomposition reverse.

    If *any* runner `j` has a "bad" coarser cell index (`(m / (L / speeds j)) mod n
    ∈ {0, n-1}`), then the open cell `(m/(n·L), (m+1)/(n·L))` is disjoint from
    `jointGoodSet speeds n`.

    Combined with `jointGoodSet_contains_cell`, this gives the complete cell
    dichotomy at the joint level: each open `1/(n·L)`-cell is either fully
    inside or fully outside `jointGoodSet`, determined by the per-runner
    coarser-cell indices. -/
theorem jointGoodSet_disjoint_cell
    {k : ℕ} (speeds : Fin k → ℕ) (n : ℕ) (hn : 2 ≤ n)
    (L : ℕ) (hL : L = lcmSpeeds speeds) (hL_pos : 0 < L)
    (hpos : ∀ j, 0 < speeds j)
    (m : ℕ) (hm_lt : m < n * L)
    (h_bad : ∃ j : Fin k,
      (m / (L / speeds j)) % n = 0 ∨ (m / (L / speeds j)) % n + 1 = n) :
    Disjoint (Set.Ioo ((m : ℝ) / ((n : ℝ) * L)) (((m : ℝ) + 1) / ((n : ℝ) * L)))
             (jointGoodSet speeds n) := by
  obtain ⟨j, h_bad_j⟩ := h_bad
  rw [Set.disjoint_left]
  intro t ht htj
  simp only [jointGoodSet, Set.mem_iInter] at htj
  have hv_pos : 0 < speeds j := hpos j
  have hv_dvd : speeds j ∣ L := by
    rw [hL]; simp only [lcmSpeeds]
    exact Finset.dvd_lcm (Finset.mem_univ j)
  have hq_pos : 0 < L / speeds j :=
    Nat.div_pos (Nat.le_of_dvd hL_pos hv_dvd) hv_pos
  have hvq : speeds j * (L / speeds j) = L := Nat.mul_div_cancel' hv_dvd
  set m' := m / (L / speeds j) with hm'_def
  have hm'_lt : m' < n * speeds j := by
    rw [hm'_def, Nat.div_lt_iff_lt_mul hq_pos]
    rw [show (n * speeds j) * (L / speeds j) =
            n * (speeds j * (L / speeds j)) from by ring, hvq]
    exact hm_lt
  -- t sits in runner j's coarser open cell at m', and Step 3 disjointness applies.
  have ht_big := cell_inclusion (speeds j) L n hv_pos hL_pos (by omega) hv_dvd m ht
  have hdisj := goodSet_disjoint_cell (speeds j) n m' hv_pos hn hm'_lt h_bad_j
  rw [Set.disjoint_left] at hdisj
  exact hdisj ht_big (htj j)

/-- **Step 5 of Route 3.** The good-cell index set.

    For `L = lcmSpeeds speeds` and the partition of `[0, 1)` into `n·L` cells
    of width `1/(n·L)`, this is the Finset of cell indices `m` for which the
    entire open cell is contained in `jointGoodSet speeds n` (per Step 4 fwd).

    Cell `m` is good iff for every runner `j`, the coarser-cell index
    `m / (L / speeds j)` has mod-n value in `[1, n-2]`. -/
def goodCellIdx {k : ℕ} (speeds : Fin k → ℕ) (n L : ℕ) : Finset ℕ :=
  (Finset.range (n * L)).filter (fun m =>
    ∀ j : Fin k, 1 ≤ (m / (L / speeds j)) % n ∧ (m / (L / speeds j)) % n + 1 < n)

/-- The open `1/(n·L)`-cell at index `m`. -/
private noncomputable def cellAt (n L m : ℕ) : Set ℝ :=
  Set.Ioo ((m : ℝ) / ((n : ℝ) * L)) (((m : ℝ) + 1) / ((n : ℝ) * L))

/-- The union of all good cells. -/
private noncomputable def goodCellsUnion {k : ℕ} (speeds : Fin k → ℕ)
    (n L : ℕ) : Set ℝ :=
  ⋃ m ∈ goodCellIdx speeds n L, cellAt n L m

/-- **Step 5 subset:** Every point in the union of good cells is in `jointGoodSet`. -/
theorem goodCellsUnion_subset_jointGoodSet
    {k : ℕ} (speeds : Fin k → ℕ) (n : ℕ) (hn : 2 ≤ n)
    (L : ℕ) (hL : L = lcmSpeeds speeds) (hL_pos : 0 < L)
    (hpos : ∀ j, 0 < speeds j) :
    goodCellsUnion speeds n L ⊆ jointGoodSet speeds n := by
  intro t ht
  simp only [goodCellsUnion, Set.mem_iUnion, cellAt] at ht
  obtain ⟨m, hm_in, ht_cell⟩ := ht
  simp only [goodCellIdx, Finset.mem_filter, Finset.mem_range] at hm_in
  exact jointGoodSet_contains_cell speeds n hn L hL hL_pos hpos m hm_in.1 hm_in.2 ht_cell

/-- The cells in the partition are pairwise disjoint: distinct indices give
    disjoint open intervals. -/
private theorem cellAt_pairwise_disjoint (n L : ℕ) (hn : 0 < n) (hL : 0 < L) :
    Pairwise (fun m m' : ℕ => Disjoint (cellAt n L m) (cellAt n L m')) := by
  -- Helper: when m < m', the cells are disjoint.
  have helper : ∀ a b : ℕ, a < b → Disjoint (cellAt n L a) (cellAt n L b) := by
    intro a b hab
    have hnL_r : (0 : ℝ) < (n : ℝ) * L :=
      mul_pos (Nat.cast_pos.mpr hn) (Nat.cast_pos.mpr hL)
    rw [Set.disjoint_left]
    intro t ht ht'
    simp only [cellAt, Set.mem_Ioo] at ht ht'
    -- ht.2 : t < (a+1)/(nL); ht'.1 : b/(nL) < t. So b/(nL) < (a+1)/(nL), i.e., b < a+1.
    have hlt : (b : ℝ) / ((n : ℝ) * L) < ((a : ℝ) + 1) / ((n : ℝ) * L) := by
      linarith [ht.2, ht'.1]
    rw [div_lt_div_iff_of_pos_right hnL_r] at hlt
    have hge : (a : ℝ) + 1 ≤ (b : ℝ) := by exact_mod_cast hab
    linarith
  intro m m' hmm
  rcases Nat.lt_or_ge m m' with hlt | hge
  · exact helper m m' hlt
  · exact (helper m' m (lt_of_le_of_ne hge hmm.symm)).symm

/-- Helper: each open cell has measure `1/(n·L)`. -/
private theorem cellAt_volume (n L m : ℕ) (hn : 0 < n) (hL : 0 < L) :
    MeasureTheory.volume (cellAt n L m) = ENNReal.ofReal (1 / ((n : ℝ) * L)) := by
  have hnL_r : (0 : ℝ) < (n : ℝ) * L :=
    mul_pos (Nat.cast_pos.mpr hn) (Nat.cast_pos.mpr hL)
  rw [cellAt, Real.volume_Ioo]
  congr 1
  field_simp; ring

/-- **Step 5 measure:** The union of good cells has measure `#goodCellIdx / (n·L)`.

    This is the count-to-measure bridge: the discrete count of good cell indices
    determines the measure of the union via `# cells × cell width`. -/
theorem goodCellsUnion_measure {k : ℕ} (speeds : Fin k → ℕ)
    (n L : ℕ) (hn : 0 < n) (hL : 0 < L) :
    MeasureTheory.volume (goodCellsUnion speeds n L) =
      (goodCellIdx speeds n L).card * ENNReal.ofReal (1 / ((n : ℝ) * L)) := by
  unfold goodCellsUnion
  rw [MeasureTheory.measure_biUnion_finset
        (fun a _ b _ hab => cellAt_pairwise_disjoint n L hn hL hab)
        (fun b _ => by exact measurableSet_Ioo)]
  -- Each cell has the same measure 1/(nL); sum = card * measure.
  calc ∑ p ∈ goodCellIdx speeds n L, MeasureTheory.volume (cellAt n L p)
      = ∑ _p ∈ goodCellIdx speeds n L, ENNReal.ofReal (1 / ((n : ℝ) * L)) :=
          Finset.sum_congr rfl (fun m _ => cellAt_volume n L m hn hL)
    _ = (goodCellIdx speeds n L).card • ENNReal.ofReal (1 / ((n : ℝ) * L)) :=
          Finset.sum_const _
    _ = (goodCellIdx speeds n L).card * ENNReal.ofReal (1 / ((n : ℝ) * L)) := by
          rw [nsmul_eq_mul]

/-- **Step 5 lower bound:** `jointGoodSet` has measure at least `#goodCellIdx / (n·L)`.

    Direct consequence of `goodCellsUnion ⊆ jointGoodSet` and `goodCellsUnion_measure`. -/
theorem jointGoodSet_measure_lower_bound
    {k : ℕ} (speeds : Fin k → ℕ) (n : ℕ) (hn : 2 ≤ n)
    (L : ℕ) (hL : L = lcmSpeeds speeds) (hL_pos : 0 < L)
    (hpos : ∀ j, 0 < speeds j) :
    (goodCellIdx speeds n L).card * ENNReal.ofReal (1 / ((n : ℝ) * L)) ≤
      MeasureTheory.volume (jointGoodSet speeds n) := by
  rw [← goodCellsUnion_measure speeds n L (by omega) hL_pos]
  exact MeasureTheory.measure_mono
    (goodCellsUnion_subset_jointGoodSet speeds n hn L hL hL_pos hpos)

/-- **Step 5 lower bound on `[0, 1)`:** the good cells fit inside `[0, 1)`, so
    `jointGoodSet ∩ [0, 1)` has measure at least `#goodCellIdx / (n·L)`.

    This is the period-restricted version needed for cell-counting. -/
theorem jointGoodSet_measure_lower_bound_in_unit
    {k : ℕ} (speeds : Fin k → ℕ) (n : ℕ) (hn : 2 ≤ n)
    (L : ℕ) (hL : L = lcmSpeeds speeds) (hL_pos : 0 < L)
    (hpos : ∀ j, 0 < speeds j) :
    (goodCellIdx speeds n L).card * ENNReal.ofReal (1 / ((n : ℝ) * L)) ≤
      MeasureTheory.volume (jointGoodSet speeds n ∩ Set.Ico (0 : ℝ) 1) := by
  rw [← goodCellsUnion_measure speeds n L (by omega) hL_pos]
  apply MeasureTheory.measure_mono
  intro t ht
  refine ⟨goodCellsUnion_subset_jointGoodSet speeds n hn L hL hL_pos hpos ht, ?_⟩
  -- t ∈ Ico 0 1 since t lies in some good cell (m/(nL), (m+1)/(nL)) with m < nL.
  simp only [goodCellsUnion, Set.mem_iUnion, cellAt, Set.mem_Ioo] at ht
  obtain ⟨m, hm_in, ht_l, ht_r⟩ := ht
  simp only [goodCellIdx, Finset.mem_filter, Finset.mem_range] at hm_in
  obtain ⟨hm_lt, _⟩ := hm_in
  have hnL_r : (0 : ℝ) < (n : ℝ) * L :=
    mul_pos (Nat.cast_pos.mpr (by omega)) (Nat.cast_pos.mpr hL_pos)
  refine ⟨?_, ?_⟩
  · have : (0 : ℝ) ≤ (m : ℝ) / ((n : ℝ) * L) :=
      div_nonneg (Nat.cast_nonneg m) hnL_r.le
    linarith
  · have h1 : ((m : ℝ) + 1) ≤ ((n : ℝ) * L) := by
      have h : m + 1 ≤ n * L := hm_lt
      exact_mod_cast h
    have h2 : ((m : ℝ) + 1) / ((n : ℝ) * L) ≤ 1 := by
      rw [div_le_one hnL_r]; exact h1
    linarith

/-- The boundary set: cell endpoints `{k/(n·L) : k ∈ [0, n·L]}`. Finite, hence
    Lebesgue-measure zero. -/
private noncomputable def boundarySet (n L : ℕ) : Set ℝ :=
  Set.range (fun k : Fin (n * L + 1) => ((k : ℕ) : ℝ) / ((n : ℝ) * L))

private theorem boundarySet_volume_zero (n L : ℕ) :
    MeasureTheory.volume (boundarySet n L) = 0 :=
  (Set.finite_range _).countable.measure_zero _

/-- **Step 5 upper bound:** Every t ∈ `jointGoodSet ∩ [0, 1)` either lies in a
    good cell or is a cell-boundary point.

    Proof: `m := ⌊t·n·L⌋ ∈ [0, n·L)`. Either `t = m/(n·L)` (boundary), or `t`
    lies strictly inside the open cell at `m`. In the latter case Step 4
    dichotomy forces `m ∈ goodCellIdx` (otherwise the cell would be disjoint
    from `jointGoodSet`, contradicting `t ∈ jointGoodSet`). -/
theorem jointGoodSet_inter_unit_subset
    {k : ℕ} (speeds : Fin k → ℕ) (n : ℕ) (hn : 2 ≤ n)
    (L : ℕ) (hL : L = lcmSpeeds speeds) (hL_pos : 0 < L)
    (hpos : ∀ j, 0 < speeds j) :
    jointGoodSet speeds n ∩ Set.Ico (0 : ℝ) 1 ⊆
      goodCellsUnion speeds n L ∪ boundarySet n L := by
  intro t ⟨htG, ht_lo, ht_hi⟩
  have hn_pos : 0 < n := by omega
  have hn_r : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn_pos
  have hL_r : (0 : ℝ) < (L : ℝ) := Nat.cast_pos.mpr hL_pos
  have hnL_r : (0 : ℝ) < (n : ℝ) * L := mul_pos hn_r hL_r
  set m : ℕ := Nat.floor (t * ((n : ℝ) * L)) with hm_def
  have h_tnL_nn : 0 ≤ t * ((n : ℝ) * L) := mul_nonneg ht_lo hnL_r.le
  have h_tnL_lt : t * ((n : ℝ) * L) < (n : ℝ) * L := by
    have := mul_lt_mul_of_pos_right ht_hi hnL_r; linarith
  have h_m_lt : m < n * L := by
    rw [hm_def, Nat.floor_lt h_tnL_nn]
    exact_mod_cast h_tnL_lt
  have h_m_le : (m : ℝ) ≤ t * ((n : ℝ) * L) := Nat.floor_le h_tnL_nn
  have h_m_lt_succ : t * ((n : ℝ) * L) < (m : ℝ) + 1 := Nat.lt_floor_add_one _
  have h_t_ge : (m : ℝ) / ((n : ℝ) * L) ≤ t := by
    rw [div_le_iff₀ hnL_r]; linarith
  have h_t_lt : t < ((m : ℝ) + 1) / ((n : ℝ) * L) := by
    rw [lt_div_iff₀ hnL_r]; linarith
  by_cases h_eq : t = (m : ℝ) / ((n : ℝ) * L)
  · -- Boundary case.
    right
    unfold boundarySet
    refine ⟨⟨m, by omega⟩, ?_⟩
    simp only [Fin.val_mk]; exact h_eq.symm
  · -- Open-cell case.
    left
    have h_open : t ∈ cellAt n L m := by
      refine ⟨?_, h_t_lt⟩
      exact lt_of_le_of_ne h_t_ge (Ne.symm h_eq)
    by_cases hgood : m ∈ goodCellIdx speeds n L
    · exact Set.mem_biUnion hgood h_open
    · exfalso
      simp only [goodCellIdx, Finset.mem_filter, Finset.mem_range, not_and] at hgood
      have h_negconj : ¬ ∀ j : Fin k,
          1 ≤ (m / (L / speeds j)) % n ∧ (m / (L / speeds j)) % n + 1 < n := hgood h_m_lt
      push_neg at h_negconj
      obtain ⟨j, hj⟩ := h_negconj
      -- After push_neg: hj : 1 ≤ r → n ≤ r + 1.
      have h_bad : (m / (L / speeds j)) % n = 0 ∨ (m / (L / speeds j)) % n + 1 = n := by
        rcases Nat.eq_zero_or_pos ((m / (L / speeds j)) % n) with h0 | h0
        · exact Or.inl h0
        · have h1 : n ≤ (m / (L / speeds j)) % n + 1 := hj h0
          have h2 : (m / (L / speeds j)) % n < n := Nat.mod_lt _ hn_pos
          exact Or.inr (by omega)
      have hdisj := jointGoodSet_disjoint_cell speeds n hn L hL hL_pos hpos m h_m_lt ⟨j, h_bad⟩
      rw [Set.disjoint_left] at hdisj
      exact hdisj h_open htG

/-- **Step 5 equality:** `jointGoodSet ∩ [0, 1)` has measure exactly
    `#goodCellIdx · (1/(n·L))`. Combines the lower bound with the upper bound
    via the measure-zero boundary set. -/
theorem jointGoodSet_measure_eq
    {k : ℕ} (speeds : Fin k → ℕ) (n : ℕ) (hn : 2 ≤ n)
    (L : ℕ) (hL : L = lcmSpeeds speeds) (hL_pos : 0 < L)
    (hpos : ∀ j, 0 < speeds j) :
    MeasureTheory.volume (jointGoodSet speeds n ∩ Set.Ico (0 : ℝ) 1) =
      (goodCellIdx speeds n L).card * ENNReal.ofReal (1 / ((n : ℝ) * L)) := by
  have hn_pos : 0 < n := by omega
  apply le_antisymm
  · calc MeasureTheory.volume (jointGoodSet speeds n ∩ Set.Ico (0 : ℝ) 1)
        ≤ MeasureTheory.volume (goodCellsUnion speeds n L ∪ boundarySet n L) :=
          MeasureTheory.measure_mono
            (jointGoodSet_inter_unit_subset speeds n hn L hL hL_pos hpos)
      _ ≤ MeasureTheory.volume (goodCellsUnion speeds n L) +
            MeasureTheory.volume (boundarySet n L) :=
          MeasureTheory.measure_union_le _ _
      _ = MeasureTheory.volume (goodCellsUnion speeds n L) := by
          rw [boundarySet_volume_zero, add_zero]
      _ = (goodCellIdx speeds n L).card * ENNReal.ofReal (1 / ((n : ℝ) * L)) :=
          goodCellsUnion_measure speeds n L hn_pos hL_pos
  · exact jointGoodSet_measure_lower_bound_in_unit speeds n hn L hL hL_pos hpos

/-- **Step 6 of Route 3.** Action of `fract(p·t)` on cells of width `1/(n·L·p)`.

    For `t` in the open fine cell at index `m''`, the value `fract(p·t)` lies
    in the open 1/(n·L) sub-interval at index `m'' mod (n·L)`. This is the
    "p-slot" of the fine cell.

    Proof: For `t ∈ (m''/(n·L·p), (m''+1)/(n·L·p))`, we have `p·t ∈
    (m''/(n·L), (m''+1)/(n·L))` — an open interval of length `1/(n·L)`
    containing no integer. Hence `⌊p·t⌋ = m'' / (n·L)` (Nat division), and
    `fract(p·t) = p·t - ⌊p·t⌋` lies in `((m'' mod n·L)/(n·L), ((m'' mod n·L)+1)/(n·L))`. -/
theorem fract_pt_on_fine_cell (n L p m'' : ℕ) (hn : 0 < n) (hL : 0 < L) (hp : 0 < p)
    (t : ℝ) (ht : t ∈ Set.Ioo ((m'' : ℝ) / ((n : ℝ) * L * p))
                              (((m'' : ℝ) + 1) / ((n : ℝ) * L * p))) :
    Int.fract ((p : ℝ) * t) ∈ Set.Ioo
      (((m'' % (n * L) : ℕ) : ℝ) / ((n : ℝ) * L))
      ((((m'' % (n * L) : ℕ) : ℝ) + 1) / ((n : ℝ) * L)) := by
  obtain ⟨ht_l, ht_r⟩ := ht
  have hn_r : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hL_r : (0 : ℝ) < (L : ℝ) := Nat.cast_pos.mpr hL
  have hp_r : (0 : ℝ) < (p : ℝ) := Nat.cast_pos.mpr hp
  have hnL_r : (0 : ℝ) < (n : ℝ) * L := mul_pos hn_r hL_r
  -- p·t ∈ (m''/(n·L), (m''+1)/(n·L))
  have hpt_l : (m'' : ℝ) / ((n : ℝ) * L) < (p : ℝ) * t := by
    have h := mul_lt_mul_of_pos_left ht_l hp_r
    have hsimp : (p : ℝ) * ((m'' : ℝ) / ((n : ℝ) * L * p)) =
                 (m'' : ℝ) / ((n : ℝ) * L) := by field_simp
    linarith
  have hpt_r : (p : ℝ) * t < ((m'' : ℝ) + 1) / ((n : ℝ) * L) := by
    have h := mul_lt_mul_of_pos_left ht_r hp_r
    have hsimp : (p : ℝ) * (((m'' : ℝ) + 1) / ((n : ℝ) * L * p)) =
                 ((m'' : ℝ) + 1) / ((n : ℝ) * L) := by field_simp
    linarith
  set k : ℕ := m'' / (n * L) with hk_def
  set r : ℕ := m'' % (n * L) with hr_def
  have hnL_pos : 0 < n * L := Nat.mul_pos hn hL
  have hkr : m'' = k * (n * L) + r := by
    show m'' = (m'' / (n * L)) * (n * L) + m'' % (n * L)
    rw [Nat.mul_comm]
    exact (Nat.div_add_mod m'' (n * L)).symm
  have h_r_lt : r < n * L := Nat.mod_lt m'' hnL_pos
  have hmcast : (m'' : ℝ) = (k : ℝ) * (n * L) + r := by exact_mod_cast hkr
  have hm_div_eq : (m'' : ℝ) / ((n : ℝ) * L) = (k : ℝ) + (r : ℝ) / ((n : ℝ) * L) := by
    rw [hmcast]; field_simp
  have hm1_div_eq : ((m'' : ℝ) + 1) / ((n : ℝ) * L) =
      (k : ℝ) + ((r : ℝ) + 1) / ((n : ℝ) * L) := by
    rw [show (m'' : ℝ) + 1 = (k : ℝ) * (n * L) + (r + 1) from by linarith [hmcast]]
    field_simp
  -- ⌊p·t⌋ = k.
  have hfloor : ⌊(p : ℝ) * t⌋ = (k : ℤ) := by
    apply Int.floor_eq_iff.mpr
    refine ⟨?_, ?_⟩
    · push_cast
      have h_rnn : (0 : ℝ) ≤ (r : ℝ) / ((n : ℝ) * L) :=
        div_nonneg (Nat.cast_nonneg r) hnL_r.le
      linarith [hpt_l, hm_div_eq]
    · push_cast
      have h_r1_le : ((r : ℝ) + 1) / ((n : ℝ) * L) ≤ 1 := by
        rw [div_le_one hnL_r]
        have hrn : (r : ℝ) + 1 ≤ (n : ℝ) * L := by
          have hh : r + 1 ≤ n * L := h_r_lt
          exact_mod_cast hh
        exact hrn
      linarith [hpt_r, hm1_div_eq]
  have hfract_eq : Int.fract ((p : ℝ) * t) = (p : ℝ) * t - (k : ℝ) := by
    simp [Int.fract, hfloor]
  refine ⟨?_, ?_⟩
  · rw [hfract_eq]
    linarith [hpt_l, hm_div_eq]
  · rw [hfract_eq]
    linarith [hpt_r, hm1_div_eq]

/-- **Step 6 corollary:** A fine cell of width `1/(n·L·p)` at index `m''` is
    contained in the coarser G-cell of width `1/(n·L)` at index `⌊m''/p⌋`.

    Direct application of `cell_inclusion` with `v := L`, `L' := L·p`. -/
theorem fine_cell_subset_G_cell (n L p m'' : ℕ) (hn : 0 < n) (hL : 0 < L) (hp : 0 < p) :
    Set.Ioo ((m'' : ℝ) / ((n : ℝ) * L * p)) (((m'' : ℝ) + 1) / ((n : ℝ) * L * p)) ⊆
    Set.Ioo (((m'' / p : ℕ) : ℝ) / ((n : ℝ) * L))
            ((((m'' / p : ℕ) : ℝ) + 1) / ((n : ℝ) * L)) := by
  have h_dvd : L ∣ L * p := dvd_mul_right L p
  have hLp_pos : 0 < L * p := Nat.mul_pos hL hp
  have h_div : (L * p) / L = p := Nat.mul_div_cancel_left p hL
  have h_inc := cell_inclusion L (L * p) n hL hLp_pos hn h_dvd m''
  rw [h_div] at h_inc
  intro t ⟨h1, h2⟩
  apply h_inc
  have h_par : (n : ℝ) * ((L * p : ℕ) : ℝ) = ((n : ℝ) * ↑L) * ↑p := by push_cast; ring
  refine ⟨?_, ?_⟩
  · rw [h_par]; exact h1
  · rw [h_par]; exact h2

/-- **Step 6 application:** If the G-cell at `⌊m''/p⌋` is a "good cell" (in
    `goodCellIdx`), then the fine cell of width `1/(n·L·p)` at index `m''` is
    contained in `jointGoodSet speeds n`.

    Combines `fine_cell_subset_G_cell` with `jointGoodSet_contains_cell`. -/
theorem jointGoodSet_contains_fine_cell
    {k : ℕ} (speeds : Fin k → ℕ) (n : ℕ) (hn : 2 ≤ n)
    (L : ℕ) (hL : L = lcmSpeeds speeds) (hL_pos : 0 < L)
    (hpos : ∀ j, 0 < speeds j)
    (p m'' : ℕ) (hp_pos : 0 < p)
    (h_good : m'' / p ∈ goodCellIdx speeds n L) :
    Set.Ioo ((m'' : ℝ) / ((n : ℝ) * L * p)) (((m'' : ℝ) + 1) / ((n : ℝ) * L * p)) ⊆
      jointGoodSet speeds n := by
  intro t ht
  have h_in_big := fine_cell_subset_G_cell n L p m'' (by omega) hL_pos hp_pos ht
  simp only [goodCellIdx, Finset.mem_filter, Finset.mem_range] at h_good
  obtain ⟨h_lt, h_cond⟩ := h_good
  exact jointGoodSet_contains_cell speeds n hn L hL hL_pos hpos
    (m'' / p) h_lt h_cond h_in_big

/-! ## §5.5  Counterexample: manuscript Theorem 5.2 is too general

    The manuscript's Theorem 5.2 (formalised as `theorem52_nonempty_correct`)
    claims: for any closed positive-measure `A` and `gcd(p, L) = 1`,
    `∃ t ∈ jointGoodSet, fract(p·t) ∈ A`.

    This is FALSE for arbitrary `A`. Counterexample (numerically verified in
    `theorem52_counterexample_verify.py`, 10M samples):

    - `n = 5`, `speeds = ![1, 2]`, `L = lcm(1, 2) = 2`, `p = 3` (so `1 < p`,
      `gcd(3, 2) = 1`).
    - `jointGoodSet ∩ [0, 1) = [1/5, 2/5] ∪ [3/5, 4/5]`, measure `2/5 > 0`.
    - `A = [9/20, 11/20] = [0.45, 0.55]`, closed, measure `0.1 > 0`.
    - But `fract(3·jointGoodSet) ⊆ [0, 2/5] ∪ [3/5, 1)`, which is **disjoint**
      from `A`. So no witness `t` exists.

    **Manuscript flaw:** the CRT-independence argument claims "G has period
    `1/L`, A-condition on `{p·t}` has period `1/p`, so by CRT they're
    independent." But under the gcd=1 normalisation, `G = jointGoodSet` has
    period **1**, not `1/L`. The CRT factorisation premise fails. -/
theorem theorem52_counterexample_claim :
    ∀ t : ℝ, t ∈ goodSet 1 5 → t ∈ goodSet 2 5 →
      Int.fract ((3 : ℝ) * t) ∉ Set.Icc (9/20 : ℝ) (11/20) := by
  intro t h1 h2 hf
  set a := Int.fract t with ha_def
  have ha_nn : 0 ≤ a := Int.fract_nonneg t
  have ha_lt1 : a < 1 := Int.fract_lt_one t
  -- Extract a ∈ [1/5, 4/5] from h1.
  have h_a_lo : (1:ℝ)/5 ≤ a ∧ a ≤ 4/5 := by
    have hh := h1
    simp only [goodSet, Set.mem_setOf_eq, circDist, Nat.cast_one, one_mul,
               le_min_iff, ← ha_def] at hh
    exact ⟨hh.1, by linarith [hh.2]⟩
  obtain ⟨ha15, ha45⟩ := h_a_lo
  -- Extract b = fract(2t) ∈ [1/5, 4/5] from h2.
  set b := Int.fract ((2:ℝ) * t) with hb_def
  have h_b_bnds : (1:ℝ)/5 ≤ b ∧ b ≤ 4/5 := by
    have hh := h2
    simp only [goodSet, Set.mem_setOf_eq, circDist, Nat.cast_ofNat,
               le_min_iff, ← hb_def] at hh
    exact ⟨hh.1, by linarith [hh.2]⟩
  obtain ⟨hb15, hb45⟩ := h_b_bnds
  -- b = fract(2 · a), via fract(x + int) = fract(x).
  have hb_eq : b = Int.fract (2 * a) := by
    rw [hb_def]
    have heq : (2 : ℝ) * t = 2 * a + ((2 * ⌊t⌋ : ℤ) : ℝ) := by
      have hfl : a + (⌊t⌋ : ℝ) = t := Int.fract_add_floor t
      push_cast; linarith
    rw [heq, Int.fract_add_intCast]
  -- fract(3t) = fract(3 · a) similarly.
  have h3_eq : Int.fract ((3:ℝ) * t) = Int.fract (3 * a) := by
    have heq : (3 : ℝ) * t = 3 * a + ((3 * ⌊t⌋ : ℤ) : ℝ) := by
      have hfl : a + (⌊t⌋ : ℝ) = t := Int.fract_add_floor t
      push_cast; linarith
    rw [heq, Int.fract_add_intCast]
  rw [h3_eq] at hf
  -- Case split on a < 1/2 vs a ≥ 1/2.
  by_cases ha_half : a < 1/2
  · -- b = 2a (no wrap), forces a ≤ 2/5.
    have hb_val : b = 2 * a := by
      rw [hb_eq]
      exact Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
    have ha25 : a ≤ 2/5 := by linarith
    -- 3a ∈ [3/5, 6/5]. Case: 3a < 1 vs ≥ 1.
    by_cases h_3a_lt1 : 3 * a < 1
    · have hfr : Int.fract (3 * a) = 3 * a :=
        Int.fract_eq_self.mpr ⟨by linarith, h_3a_lt1⟩
      rw [hfr] at hf
      linarith [hf.2]  -- 3a ≥ 3/5 > 11/20
    · push_neg at h_3a_lt1
      have hfr : Int.fract (3 * a) = 3 * a - 1 := by
        have h_int : ⌊(3:ℝ) * a⌋ = (1 : ℤ) := by
          apply Int.floor_eq_iff.mpr
          refine ⟨?_, ?_⟩
          · push_cast; linarith
          · push_cast; linarith  -- 3a < 3·(2/5) + epsilon = 6/5 < 2
        simp [Int.fract, h_int]
      rw [hfr] at hf
      linarith [hf.1]  -- 3a - 1 ≤ 1/5 < 9/20
  · push_neg at ha_half
    -- b = 2a - 1, forces a ≥ 3/5.
    have h_2a_ge1 : 1 ≤ 2 * a := by linarith
    have h_2a_lt2 : 2 * a < 2 := by linarith
    have hb_val : b = 2 * a - 1 := by
      rw [hb_eq]
      have h_int : ⌊(2:ℝ) * a⌋ = (1 : ℤ) := by
        apply Int.floor_eq_iff.mpr
        refine ⟨?_, ?_⟩
        · push_cast; linarith
        · push_cast; linarith
      simp [Int.fract, h_int]
    have ha35 : a ≥ 3/5 := by linarith
    -- 3a ∈ [9/5, 12/5]. Case: 3a < 2 vs ≥ 2.
    by_cases h_3a_lt2 : 3 * a < 2
    · have hfr : Int.fract (3 * a) = 3 * a - 1 := by
        have h_int : ⌊(3:ℝ) * a⌋ = (1 : ℤ) := by
          apply Int.floor_eq_iff.mpr
          refine ⟨?_, ?_⟩
          · push_cast; linarith
          · push_cast; linarith
        simp [Int.fract, h_int]
      rw [hfr] at hf
      linarith [hf.2]  -- 3a - 1 ≥ 4/5 > 11/20
    · push_neg at h_3a_lt2
      have h_3a_lt3 : 3 * a < 3 := by linarith
      have hfr : Int.fract (3 * a) = 3 * a - 2 := by
        have h_int : ⌊(3:ℝ) * a⌋ = (2 : ℤ) := by
          apply Int.floor_eq_iff.mpr
          refine ⟨?_, ?_⟩
          · push_cast; linarith
          · push_cast; linarith
        simp [Int.fract, h_int]
      rw [hfr] at hf
      linarith [hf.1]  -- 3a - 2 ≤ 2/5 < 9/20

/-- Helper: `goodSet 1 n` has positive measure for n ≥ 3.
    Witness: `[1/n, (n-1)/n] ⊆ {t | circDist t ≥ 1/n}` with measure `(n-2)/n > 0`. -/
private lemma goodSet_one_pos_measure (n : ℕ) (hn : 3 ≤ n) :
    0 < MeasureTheory.volume (goodSet 1 n) := by
  have hn_r : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hn3_r : (2 : ℝ) < n := by exact_mod_cast show 2 < n from by omega
  have hI_sub : Set.Icc ((1:ℝ)/n) (((n:ℝ)-1)/n) ⊆ goodSet 1 n :=
      fun t ⟨ht_lo, ht_hi⟩ => by
    simp only [goodSet, Set.mem_setOf_eq, Nat.cast_one, one_mul]
    have h01 : (0:ℝ) ≤ t := le_trans (div_nonneg one_pos.le hn_r.le) ht_lo
    have h1t : t < 1 := by
      have : ((n:ℝ)-1)/n < 1 := by rw [div_lt_one hn_r]; linarith
      linarith
    unfold circDist
    rw [Int.fract_eq_self.mpr ⟨h01, h1t⟩]
    exact le_min ht_lo
      (by linarith [show ((n:ℝ)-1)/n = 1 - 1/n from by field_simp [hn_r.ne']])
  have hI_pos : 0 < MeasureTheory.volume (Set.Icc ((1:ℝ)/n) (((n:ℝ)-1)/n)) := by
    rw [Real.volume_Icc]
    refine ENNReal.ofReal_pos.mpr ?_
    have h : ((n:ℝ)-1)/n - 1/n = ((n:ℝ)-2)/n := by field_simp [hn_r.ne']; ring
    rw [h]; exact div_pos (by linarith) hn_r
  exact hI_pos.trans_le (MeasureTheory.measure_mono hI_sub)

/-! ### Historical note (deleted): `theorem52_nonempty_good`

    Previously this gave `∃ t ∈ G, circDist(p·t) ≥ 1/n`, derived from the (now-deleted)
    false `theorem52_nonempty_correct` with `A = goodSet 1 n`. The conclusion was
    insufficient for both downstream callers anyway (they need `fract(p·t) ∈ A` for
    structured `A`, not just `circDist(p·t) ≥ 1/n`).

    The replacement chain is:
    `theorem52_nonempty_structured` → `theorem52_nonempty_DI` (for §10) or
    `theorem52_nonempty_ModDI` (for §11). -/

/-! ## §5.6  Restricted Theorem 5.2 (Option A): A = jointGoodSet structure

  The general `theorem52_nonempty_correct` is FALSE (see counterexample). The fix
  ("Option A"): restrict `A` to be a `jointGoodSet A_speeds n` — the form used
  by BOTH downstream callers:
    - Theorem 10.1 (DI): `A = setA_DI q n = goodSet q n = jointGoodSet ![q] n`.
    - Theorem 11.1 (ModDI): `A = setA_ModDI w q n = jointGoodSet (concat w ![q]) n`.

  The proof works at the fine cell partition of width `1/(n · L_G · L_A · p)`
  where `L_G = lcmSpeeds G_speeds`, `L_A = lcmSpeeds A_speeds`.
  At this resolution both G-membership and A-membership of `fract(p·t)` are
  determined by integer index conditions, reducing the analytic claim to a
  combinatorial joint count.

  STATUS: the joint-count-positivity step (`joint_fine_cell_exists`) is the
  remaining focused gap. The rest of the chain (cell decomposition for A,
  reduction of the analytic claim, downstream wiring) is fully proved here.
-/

/-- Generalised G-cell containment: if `L'` is a common multiple of all
    `speeds j` (not necessarily the exact `lcmSpeeds`), the same cell decomposition
    works because `cell_inclusion` only uses divisibility, not equality with lcm.

    This is the lift of `jointGoodSet_contains_cell` from `L = lcmSpeeds` to
    arbitrary `L'` with `lcmSpeeds | L'`. -/
theorem jointGoodSet_contains_cell_at_multiple
    {k : ℕ} (speeds : Fin k → ℕ) (n : ℕ) (hn : 2 ≤ n)
    (L' : ℕ) (hL'_pos : 0 < L')
    (hpos : ∀ j, 0 < speeds j)
    (hdvd : ∀ j, speeds j ∣ L')
    (m : ℕ) (hm_lt : m < n * L')
    (h_good : ∀ j : Fin k,
      1 ≤ (m / (L' / speeds j)) % n ∧
      (m / (L' / speeds j)) % n + 1 < n) :
    Set.Ioo ((m : ℝ) / ((n : ℝ) * L')) (((m : ℝ) + 1) / ((n : ℝ) * L')) ⊆
      jointGoodSet speeds n := by
  intro t ht
  simp only [jointGoodSet, Set.mem_iInter]
  intro j
  have hv_pos : 0 < speeds j := hpos j
  have hv_dvd : speeds j ∣ L' := hdvd j
  have hq_pos : 0 < L' / speeds j :=
    Nat.div_pos (Nat.le_of_dvd hL'_pos hv_dvd) hv_pos
  have hvq : speeds j * (L' / speeds j) = L' := Nat.mul_div_cancel' hv_dvd
  set m' := m / (L' / speeds j) with hm'_def
  have hm'_lt : m' < n * speeds j := by
    rw [hm'_def, Nat.div_lt_iff_lt_mul hq_pos]
    rw [show (n * speeds j) * (L' / speeds j) =
            n * (speeds j * (L' / speeds j)) from by ring, hvq]
    exact hm_lt
  obtain ⟨h_lo, h_hi⟩ := h_good j
  have h_sub := cell_inclusion (speeds j) L' n hv_pos hL'_pos (by omega) hv_dvd m
  exact goodSet_contains_cell (speeds j) n m' hv_pos hn hm'_lt h_lo h_hi (h_sub ht)

/-- The "joint good fine cell" predicate at the refined resolution
    `1/(n · L_G · L_A · p)`. A fine cell at index `m''` is joint-good when:
    - **G-condition:** `m'' / (L_A · p)` is a good G-cell index at `1/(n · L_G)`.
    - **A-condition:** `(m'' mod (n · L_G · L_A)) / L_G` is a good A-cell index
      at `1/(n · L_A)`.

    Together these guarantee any point in the open fine cell lies in `G` and
    its image under `t ↦ fract(p·t)` lies in `A`. -/
def isJointGoodFineCell {kG kA : ℕ}
    (G_speeds : Fin kG → ℕ) (A_speeds : Fin kA → ℕ)
    (n L_G L_A p m'' : ℕ) : Prop :=
  m'' / (L_A * p) ∈ goodCellIdx G_speeds n L_G ∧
  (m'' % (n * L_G * L_A)) / L_G ∈ goodCellIdx A_speeds n L_A

/-- **Key reduction.** If a joint-good fine cell exists, then the restricted
    Theorem 5.2 holds: pick any point of the open cell as the witness.

    Proof outline:
    1. Take `m''` joint-good; pick `t = (m'' + 1/2)/(n L_G L_A p)` in the open fine cell.
    2. The G-condition gives the fine cell ⊆ G via
       `jointGoodSet_contains_cell_at_multiple` with `L' = L_G * L_A`.
    3. `fract_pt_on_fine_cell` shows `fract(p·t)` lies in a 1/(n·L_G·L_A) sub-cell.
    4. The A-condition lifts this sub-cell to membership in A via the same
       generalised lemma applied to `A_speeds`. -/
theorem theorem52_structured_of_joint_exists
    {kG kA : ℕ}
    (G_speeds : Fin kG → ℕ) (A_speeds : Fin kA → ℕ)
    (n L_G L_A p : ℕ)
    (hn : 3 ≤ n)
    (hLG : L_G = lcmSpeeds G_speeds) (hLG_pos : 0 < L_G)
    (hLA : L_A = lcmSpeeds A_speeds) (hLA_pos : 0 < L_A)
    (hp : 1 < p)
    (hposG : ∀ j, 0 < G_speeds j) (hposA : ∀ k, 0 < A_speeds k)
    (h_exists : ∃ m'' < n * L_G * L_A * p,
                  isJointGoodFineCell G_speeds A_speeds n L_G L_A p m'') :
    ∃ t₀ ∈ jointGoodSet G_speeds n,
      Int.fract ((p : ℝ) * t₀) ∈ jointGoodSet A_speeds n := by
  obtain ⟨m'', hm''_lt, hm''_G, hm''_A⟩ := h_exists
  have hn_pos : 0 < n := by omega
  have hp_pos : 0 < p := by omega
  have hLG_LA_pos : 0 < L_G * L_A := Nat.mul_pos hLG_pos hLA_pos
  have hnLLp : (0 : ℝ) < (n : ℝ) * (L_G * L_A : ℕ) * p := by
    have h1 : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn_pos
    have h2 : (0 : ℝ) < ((L_G * L_A : ℕ) : ℝ) := Nat.cast_pos.mpr hLG_LA_pos
    have h3 : (0 : ℝ) < (p : ℝ) := Nat.cast_pos.mpr hp_pos
    positivity
  -- Pick witness: midpoint of fine cell.
  set t₀ : ℝ := ((m'' : ℝ) + 1/2) / ((n : ℝ) * (L_G * L_A : ℕ) * p) with ht₀_def
  have ht₀_in_fine :
      t₀ ∈ Set.Ioo ((m'' : ℝ) / ((n : ℝ) * (L_G * L_A : ℕ) * p))
                  (((m'' : ℝ) + 1) / ((n : ℝ) * (L_G * L_A : ℕ) * p)) := by
    refine ⟨?_, ?_⟩
    · rw [ht₀_def, div_lt_div_iff_of_pos_right hnLLp]; linarith
    · rw [ht₀_def, div_lt_div_iff_of_pos_right hnLLp]; linarith
  -- Step 1: t₀ ∈ G_s via the generalised cell-containment lemma.
  have ht₀_G : t₀ ∈ jointGoodSet G_speeds n := by
    have hdvd_G : ∀ j, G_speeds j ∣ L_G * L_A := fun j => by
      have hd : G_speeds j ∣ L_G := by
        rw [hLG]; simp only [lcmSpeeds]
        exact Finset.dvd_lcm (Finset.mem_univ j)
      exact hd.mul_right L_A
    have hposG_all : ∀ j, 0 < G_speeds j := hposG
    -- Apply the generalised lemma. m'' goodCellIdx condition is at index m''/(L_A p).
    -- We need the OPEN fine cell to be inside the OPEN coarse G-cell.
    have h_G_cell : Set.Ioo
        ((↑(m'' / (L_A * p)) : ℝ) / ((n : ℝ) * L_G))
        (((↑(m'' / (L_A * p)) : ℝ) + 1) / ((n : ℝ) * L_G)) ⊆
        jointGoodSet G_speeds n := by
      simp only [goodCellIdx, Finset.mem_filter, Finset.mem_range] at hm''_G
      exact jointGoodSet_contains_cell G_speeds n (by omega) L_G hLG hLG_pos hposG_all
        (m'' / (L_A * p)) hm''_G.1 hm''_G.2
    -- The fine cell is contained in the coarse G-cell via `cell_inclusion`.
    have hdvd : L_G ∣ L_G * L_A := dvd_mul_right L_G L_A
    have h_fine_in_coarse_G :
        Set.Ioo ((m'' : ℝ) / ((n : ℝ) * (L_G * L_A : ℕ) * p))
                (((m'' : ℝ) + 1) / ((n : ℝ) * (L_G * L_A : ℕ) * p)) ⊆
        Set.Ioo (((m'' / (L_A * p) : ℕ) : ℝ) / ((n : ℝ) * L_G))
                ((((m'' / (L_A * p) : ℕ) : ℝ) + 1) / ((n : ℝ) * L_G)) := by
      -- Step a: fine 1/(n·(L_G L_A)·p) cell at m'' is in 1/(n·(L_G L_A)) cell at m''/p
      have h_a := fine_cell_subset_G_cell n (L_G * L_A) p m'' hn_pos hLG_LA_pos hp_pos
      -- Step b: 1/(n·(L_G L_A)) cell at m''/p is in 1/(n·L_G) cell at (m''/p)/L_A
      have h_b := cell_inclusion L_G (L_G * L_A) n hLG_pos hLG_LA_pos hn_pos hdvd (m'' / p)
      have h_div_eq : (L_G * L_A) / L_G = L_A :=
        Nat.mul_div_cancel_left L_A hLG_pos
      rw [h_div_eq] at h_b
      have h_compose : m'' / p / L_A = m'' / (L_A * p) := by
        rw [Nat.div_div_eq_div_mul]; congr 1; ring
      rw [h_compose] at h_b
      exact h_a.trans h_b
    exact h_G_cell (h_fine_in_coarse_G ht₀_in_fine)
  -- Step 2: fract(p·t₀) ∈ A.
  have ht₀_A : Int.fract ((p : ℝ) * t₀) ∈ jointGoodSet A_speeds n := by
    -- 2a: fract(p·t₀) lies in 1/(n·L_G·L_A) sub-cell via fract_pt_on_fine_cell.
    have h_fract :=
      fract_pt_on_fine_cell n (L_G * L_A) p m'' hn_pos hLG_LA_pos hp_pos t₀ ht₀_in_fine
    -- 2b: That sub-cell sits inside the 1/(n·L_A) cell at (m''%(n L_G L_A))/L_G,
    --     via `cell_inclusion`.
    set b := m'' % (n * L_G * L_A) with hb_def
    set β := b / L_G with hβ_def
    have hb_lt : b < n * L_G * L_A :=
      Nat.mod_lt _ (Nat.mul_pos (Nat.mul_pos hn_pos hLG_pos) hLA_pos)
    have hβ_lt : β < n * L_A := by
      rw [hβ_def, Nat.div_lt_iff_lt_mul hLG_pos]
      rw [show n * L_A * L_G = n * L_G * L_A from by ring]; exact hb_lt
    have hdvd_LA : L_A ∣ L_G * L_A := dvd_mul_left L_A L_G
    have h_div_eq : (L_G * L_A) / L_A = L_G :=
      Nat.mul_div_cancel _ hLA_pos
    have h_sub : Set.Ioo ((b : ℝ) / ((n : ℝ) * (L_G * L_A : ℕ)))
                          (((b : ℝ) + 1) / ((n : ℝ) * (L_G * L_A : ℕ))) ⊆
                  Set.Ioo ((β : ℝ) / ((n : ℝ) * L_A))
                          (((β : ℝ) + 1) / ((n : ℝ) * L_A)) := by
      have h_inc := cell_inclusion L_A (L_G * L_A) n hLA_pos hLG_LA_pos hn_pos hdvd_LA b
      rw [h_div_eq] at h_inc
      simpa [hβ_def] using h_inc
    -- 2c: That 1/(n L_A) cell is good for A_speeds (by hm''_A) and hence ⊆ A.
    have h_β_good : β ∈ goodCellIdx A_speeds n L_A := hm''_A
    simp only [goodCellIdx, Finset.mem_filter, Finset.mem_range] at h_β_good
    have h_A_cell := jointGoodSet_contains_cell A_speeds n (by omega)
      L_A hLA hLA_pos hposA β h_β_good.1 h_β_good.2
    -- 2d: Push fract(p·t₀) through the inclusion.
    have h_in_LGLA : Int.fract ((p : ℝ) * t₀) ∈
        Set.Ioo (((m'' % (n * (L_G * L_A)) : ℕ) : ℝ) / ((n : ℝ) * (L_G * L_A : ℕ)))
                ((((m'' % (n * (L_G * L_A)) : ℕ) : ℝ) + 1) / ((n : ℝ) * (L_G * L_A : ℕ))) := by
      convert h_fract using 2 <;> push_cast <;> ring
    have hb_eq : m'' % (n * (L_G * L_A)) = b := by
      rw [hb_def]; congr 1; ring
    rw [hb_eq] at h_in_LGLA
    exact h_A_cell (h_sub h_in_LGLA)
  exact ⟨t₀, ht₀_G, ht₀_A⟩

/-- **Easy case** of joint cell existence: `p ≥ n · L_G`.

    Under this strong hypothesis, the range `[α₀·L_A·p, (α₀+1)·L_A·p)` (length
    `L_A·p`) has length ≥ `M_A = n·L_G·L_A`. So as `m''` varies over this range,
    `m'' mod M_A` covers all of `[0, M_A)`. In particular, it hits any target
    `β₀ · L_G` for `β₀ ∈ goodCellIdx_A`.

    Construction: `d := (β₀·L_G + M_A − r·L_A) mod M_A` where `r := α₀·p mod (n·L_G)`.
    Then `m'' := α₀·L_A·p + d` satisfies both joint conditions. -/
theorem joint_fine_cell_exists_easy
    {kG kA : ℕ}
    (G_speeds : Fin kG → ℕ) (A_speeds : Fin kA → ℕ)
    (n L_G L_A p : ℕ)
    (hn : 3 ≤ n)
    (hLG_pos : 0 < L_G) (hLA_pos : 0 < L_A) (hp : 1 < p)
    (hp_big : n * L_G ≤ p)
    (hG_idx : (goodCellIdx G_speeds n L_G).Nonempty)
    (hA_idx : (goodCellIdx A_speeds n L_A).Nonempty) :
    ∃ m'' < n * L_G * L_A * p,
      isJointGoodFineCell G_speeds A_speeds n L_G L_A p m'' := by
  obtain ⟨α₀, hα₀⟩ := hG_idx
  obtain ⟨β₀, hβ₀⟩ := hA_idx
  have hn_pos : 0 < n := by omega
  have hnLG_pos : 0 < n * L_G := Nat.mul_pos hn_pos hLG_pos
  have hMA_pos : 0 < n * L_G * L_A := Nat.mul_pos hnLG_pos hLA_pos
  have hLAp_pos : 0 < L_A * p := Nat.mul_pos hLA_pos (by omega)
  set M_A : ℕ := n * L_G * L_A with hMA_def
  -- α₀ < n · L_G from goodCellIdx membership.
  have hα₀_lt : α₀ < n * L_G := by
    simp [goodCellIdx, Finset.mem_filter, Finset.mem_range] at hα₀; exact hα₀.1
  -- β₀ < n · L_A from goodCellIdx membership.
  have hβ₀_lt : β₀ < n * L_A := by
    simp [goodCellIdx, Finset.mem_filter, Finset.mem_range] at hβ₀; exact hβ₀.1
  -- r := α₀ · p mod (n · L_G).  r < n · L_G.
  set r : ℕ := (α₀ * p) % (n * L_G) with hr_def
  have hr_lt : r < n * L_G := Nat.mod_lt _ hnLG_pos
  -- r * L_A < M_A.
  have hrLA_lt : r * L_A < M_A := by
    rw [hMA_def]
    calc r * L_A < (n * L_G) * L_A := Nat.mul_lt_mul_of_pos_right hr_lt hLA_pos
      _ = n * L_G * L_A := by ring
  -- β₀ * L_G < M_A.
  have hβ₀LG_lt : β₀ * L_G < M_A := by
    rw [hMA_def]
    calc β₀ * L_G < (n * L_A) * L_G := Nat.mul_lt_mul_of_pos_right hβ₀_lt hLG_pos
      _ = n * L_G * L_A := by ring
  -- M_A ≤ L_A * p (the easy-case hypothesis in product form).
  have hMA_le_LAp : M_A ≤ L_A * p := by
    rw [hMA_def, show n * L_G * L_A = L_A * (n * L_G) from by ring]
    exact Nat.mul_le_mul_left L_A hp_big
  -- d := (β₀·L_G + M_A − r·L_A) mod M_A.  Encodes (β₀·L_G − r·L_A) (mod M_A) in ℕ.
  set d : ℕ := (β₀ * L_G + M_A - r * L_A) % M_A with hd_def
  have hd_lt : d < M_A := Nat.mod_lt _ hMA_pos
  have hd_lt_LAp : d < L_A * p := lt_of_lt_of_le hd_lt hMA_le_LAp
  -- m'' := α₀ * L_A * p + d.
  refine ⟨α₀ * L_A * p + d, ?_, ?_, ?_⟩
  · -- m'' < n · L_G · L_A · p.
    -- α₀ ≤ n·L_G - 1, d < L_A·p, so α₀·L_A·p + d ≤ (n·L_G - 1)·L_A·p + L_A·p − 1
    --   = n·L_G·L_A·p − 1 < n·L_G·L_A·p.
    have hα₀_le : α₀ + 1 ≤ n * L_G := hα₀_lt
    nlinarith [hα₀_le, hd_lt_LAp, hLAp_pos, hLG_pos, hLA_pos, hn_pos]
  · -- (α₀ * L_A * p + d) / (L_A * p) ∈ goodCellIdx G_speeds n L_G.
    have h_div : (α₀ * L_A * p + d) / (L_A * p) = α₀ := by
      have h_eq : α₀ * L_A * p + d = d + L_A * p * α₀ := by ring
      rw [h_eq, Nat.add_mul_div_left _ _ hLAp_pos, Nat.div_eq_of_lt hd_lt_LAp,
          Nat.zero_add]
    rw [h_div]; exact hα₀
  · -- ((α₀ * L_A * p + d) mod M_A) / L_G ∈ goodCellIdx A_speeds n L_A.
    have h_mod : (α₀ * L_A * p + d) % (n * L_G * L_A) = β₀ * L_G := by
      -- (α₀ * L_A * p) mod M_A = r * L_A.
      have h_αLAp_mod : α₀ * L_A * p % M_A = r * L_A := by
        rw [hMA_def, hr_def]
        have heq : α₀ * L_A * p = α₀ * p * L_A := by ring
        rw [heq, Nat.mul_mod_mul_right]
      -- (α₀ * L_A * p + d) mod M_A = (r * L_A + d) mod M_A
      have h_add_mod : (α₀ * L_A * p + d) % M_A = (r * L_A + d) % M_A := by
        conv_lhs => rw [Nat.add_mod, h_αLAp_mod, Nat.mod_eq_of_lt hd_lt]
      rw [hMA_def] at h_add_mod
      rw [h_add_mod]
      -- (r·L_A + d) mod M_A = β₀ · L_G by direct arithmetic.
      have h_sum_eq : r * L_A + (β₀ * L_G + M_A - r * L_A) = β₀ * L_G + M_A := by omega
      have h_calc : (r * L_A + d) % M_A = β₀ * L_G := by
        have hd_unfold : d = (β₀ * L_G + M_A - r * L_A) % M_A := hd_def
        rw [hd_unfold, Nat.add_mod, Nat.mod_mod, ← Nat.add_mod, h_sum_eq]
        rw [show β₀ * L_G + M_A = β₀ * L_G + 1 * M_A from by ring,
            Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hβ₀LG_lt]
      rw [hMA_def] at h_calc
      exact h_calc
    rw [h_mod]
    rw [Nat.mul_div_cancel _ hLG_pos]; exact hβ₀

/-- **STATEMENT IS FALSE AS WRITTEN — see counterexample below.**

    Session 2026-05-26 (continued) finding: an exhaustive harness over
    `(n, G_speeds, A_speeds, p)` with `3 ≤ n ≤ 7`, `|speeds| ≤ 3`, `p prime ≤ 19`
    found **681 LRC-like counterexamples** (disjoint G/A, `gcd(p, L_G·L_A) = 1`,
    hard case `p < n · L_G`). The smallest:

    `n = 3, G_speeds = [3], A_speeds = [1, 5], p = 2`
    `L_G = 3, L_A = 5, M_A = 45, n·L_G·L_A·p = 90`
    `goodCellIdx_G = {1, 4, 7}` (nonempty)
    `goodCellIdx_A = {7}` (nonempty)
    `gcd(2, 3) = 1`; `p = 2 < n·L_G = 9` (hard case)
    Joint witnesses required: m'' < 90 with m''/10 ∈ {1,4,7} AND (m'' mod 45)/3 = 7.
    → m'' ∈ ([10,20) ∪ [40,50) ∪ [70,80)) ∩ ([21,24) ∪ [66,69)) = ∅.

    All hypotheses of the lemma hold; the conclusion fails.

    ROOT CAUSE. The "Option A" fine-cell reduction is sound, but the fine cells
    are a STRICTLY SUFFICIENT condition for joint G/fract(p·t)∈A occupancy — not
    necessary. The downstream conclusion of `theorem52_nonempty_structured`
    (existence of t₀ ∈ G with fract(p·t₀) ∈ A) may still hold via t₀'s that are
    NOT aligned to any fine cell. The harness/manuscript example above admits
    such a non-aligned t₀ (since LRC for the corresponding 4-runner instance
    {2, 3, 10} is true), but the fine-cell reduction misses it.

    The `joint_fine_cell_exists_easy` lemma (proved) handles `p ≥ n · L_G` and
    remains correct. The hard case `p < n · L_G` cannot be proved at all under
    these hypotheses.

    CONSEQUENCES.
    1. `theorem52_nonempty_structured` cannot be closed via this lemma.
    2. The Option A reformulation needs revisiting.
    3. The downstream LRC induction (Theorems 10.1 DI, 11.1 ModDI) does NOT
       depend on this lemma being closed — they cite it as a planned route,
       but the manuscript's actual analytic argument bypasses fine-cell
       alignment (it uses positive measure intersection in [0, 1), proved
       differently for prime p > some explicit threshold).

    NEXT STEPS. See `lean_joint_fine_cell_false_2026_05_26.md` in memory for
    the full counterexample table and proposed remediations:
      (a) Strengthen hypothesis to include cardinality bound
          `|goodCellIdx_G| · L_A · p + |goodCellIdx_A| · L_G > M_A`
          (provable in the easy case; rarely available in hard case).
      (b) Replace the joint-fine-cell reduction with a direct measure-theoretic
          argument bypassing alignment (needs different machinery in Mathlib).
      (c) Add structural hypothesis `gcd(p, n · L_G · L_A) = 1` (necessary
          but not sufficient — the counterexample above satisfies it). -/
theorem joint_fine_cell_exists
    {kG kA : ℕ}
    (G_speeds : Fin kG → ℕ) (A_speeds : Fin kA → ℕ)
    (n L_G L_A p : ℕ)
    (hn : 3 ≤ n)
    (hLG : L_G = lcmSpeeds G_speeds) (hLG_pos : 0 < L_G)
    (hLA : L_A = lcmSpeeds A_speeds) (hLA_pos : 0 < L_A)
    (hcop : Nat.Coprime p L_G) (hp : 1 < p)
    (hposG : ∀ j, 0 < G_speeds j) (hposA : ∀ k, 0 < A_speeds k)
    (hG_idx : (goodCellIdx G_speeds n L_G).Nonempty)
    (hA_idx : (goodCellIdx A_speeds n L_A).Nonempty) :
    ∃ m'' < n * L_G * L_A * p,
      isJointGoodFineCell G_speeds A_speeds n L_G L_A p m'' := by
  -- Easy case: p ≥ n · L_G.  Otherwise, the gap remains.
  by_cases hp_big : n * L_G ≤ p
  · exact joint_fine_cell_exists_easy G_speeds A_speeds n L_G L_A p hn
      hLG_pos hLA_pos hp hp_big hG_idx hA_idx
  · sorry

/-- **Periodicity (integer translates).** Direct proof via `circDist` invariance under
    addition of integers: for natural `v_j` and integer `m`, `v_j · (t + m) = v_j·t + v_j·m`
    and `circDist(x + integer) = circDist x`. -/
theorem jointGoodSet_periodic_int
    {k : ℕ} (speeds : Fin k → ℕ) (n : ℕ) (_hpos : ∀ j, 0 < speeds j)
    (t : ℝ) (m : ℤ) :
    t ∈ jointGoodSet speeds n ↔ t + (m : ℝ) ∈ jointGoodSet speeds n := by
  simp only [jointGoodSet, Set.mem_iInter, goodSet, Set.mem_setOf_eq]
  apply forall_congr'
  intro j
  -- circDist(v_j · (t + m)) = circDist(v_j · t + v_j · m) = circDist(v_j · t)
  -- since v_j · m is an integer.
  have hkey : (speeds j : ℝ) * (t + (m : ℝ)) = (speeds j : ℝ) * t + ((speeds j * m : ℤ) : ℝ) := by
    push_cast; ring
  rw [hkey]
  -- circDist is invariant under integer translation.
  unfold circDist
  rw [Int.fract_add_intCast]

/-- **Periodicity bridge.** Closed interval `Icc a b ⊆ G` of positive length translates
    via integer shift into `[0, 1)`, giving `μ(G ∩ Ico 0 1) > 0`. -/
theorem jointGoodSet_inter_unit_pos_of_Icc_subset
    {k : ℕ} (speeds : Fin k → ℕ) (n : ℕ) (hpos : ∀ j, 0 < speeds j)
    (a b : ℝ) (hab : a < b)
    (hsub : Set.Icc a b ⊆ jointGoodSet speeds n) :
    0 < MeasureTheory.volume (jointGoodSet speeds n ∩ Set.Ico (0 : ℝ) 1) := by
  -- Shift the interval so left endpoint is in [0, 1).
  set k_shift : ℤ := -⌊a⌋ with hk_def
  set a' : ℝ := a + k_shift with ha'_def
  have ha'_nn : 0 ≤ a' := by
    rw [ha'_def, hk_def]
    push_cast
    have h_floor : (⌊a⌋ : ℝ) ≤ a := Int.floor_le a
    linarith
  have ha'_lt1 : a' < 1 := by
    rw [ha'_def, hk_def]
    push_cast
    have h_lt : a < ⌊a⌋ + 1 := Int.lt_floor_add_one a
    linarith
  set b' : ℝ := b + k_shift with hb'_def
  have hab' : a' < b' := by rw [ha'_def, hb'_def]; linarith
  -- Translated interval is in G by periodicity.
  have hIcc_sub' : Set.Icc a' b' ⊆ jointGoodSet speeds n := by
    intro x hx
    obtain ⟨hxl, hxr⟩ := hx
    have : x - k_shift ∈ Set.Icc a b := by
      refine ⟨?_, ?_⟩
      · rw [ha'_def] at hxl; linarith
      · rw [hb'_def] at hxr; linarith
    have h_orig := hsub this
    have h_translate : x = (x - k_shift) + k_shift := by ring
    rw [h_translate]
    exact (jointGoodSet_periodic_int speeds n hpos (x - k_shift) k_shift).mp h_orig
  -- Choose the sub-interval inside [0, 1).
  set c : ℝ := min b' 1 with hc_def
  have ha'_lt_c : a' < c := by
    rw [hc_def]; exact lt_min hab' ha'_lt1
  have hc_le1 : c ≤ 1 := by rw [hc_def]; exact min_le_right _ _
  -- Ico a' c ⊆ G ∩ Ico 0 1.
  have h_in_G : Set.Ico a' c ⊆ jointGoodSet speeds n := by
    intro x ⟨hxl, hxr⟩
    apply hIcc_sub'
    refine ⟨hxl, ?_⟩
    rw [hc_def] at hxr
    have h_le : x ≤ c := le_of_lt hxr
    rw [hc_def] at h_le
    exact le_trans h_le (min_le_left _ _)
  have h_in_unit : Set.Ico a' c ⊆ Set.Ico (0 : ℝ) 1 := by
    intro x ⟨hxl, hxr⟩
    refine ⟨le_trans ha'_nn hxl, ?_⟩
    exact lt_of_lt_of_le hxr hc_le1
  -- Volume of Ico a' c is c - a' > 0.
  have h_vol_pos : 0 < MeasureTheory.volume (Set.Ico a' c) := by
    rw [Real.volume_Ico]
    exact ENNReal.ofReal_pos.mpr (by linarith)
  have h_sub : Set.Ico a' c ⊆ jointGoodSet speeds n ∩ Set.Ico (0 : ℝ) 1 :=
    Set.subset_inter h_in_G h_in_unit
  exact h_vol_pos.trans_le (MeasureTheory.measure_mono h_sub)

/-- **Helper:** μ(G ∩ [0,1)) > 0 implies `goodCellIdx` non-empty.

    Contrapositive: empty `goodCellIdx` makes `jointGoodSet_measure_eq` give
    `μ(G ∩ [0,1)) = 0`. Direct corollary of the existing measure formula. -/
theorem goodCellIdx_nonempty_of_volume_pos_in_unit
    {k : ℕ} (speeds : Fin k → ℕ) (n L : ℕ)
    (hn : 3 ≤ n) (hL : L = lcmSpeeds speeds) (hL_pos : 0 < L)
    (hpos : ∀ j, 0 < speeds j)
    (h_pos : 0 < MeasureTheory.volume (jointGoodSet speeds n ∩ Set.Ico (0 : ℝ) 1)) :
    (goodCellIdx speeds n L).Nonempty := by
  by_contra h
  rw [Finset.not_nonempty_iff_eq_empty] at h
  have hn2 : 2 ≤ n := by omega
  have : MeasureTheory.volume (jointGoodSet speeds n ∩ Set.Ico (0 : ℝ) 1) = 0 := by
    rw [jointGoodSet_measure_eq speeds n hn2 L hL hL_pos hpos, h,
        Finset.card_empty, Nat.cast_zero, zero_mul]
  exact (lt_irrefl _) (this ▸ h_pos)

/-- **Theorem 5.2 — Restricted (Option A).**

    If `A = jointGoodSet A_speeds n` for some structured family of speeds, and
    `gcd(p, L_G) = 1`, both `jointGoodSet`s have positive measure on `[0,1)`,
    then `∃ t ∈ G, fract(p·t) ∈ A`.

    This is the form needed by Theorems 10.1 (with `A_speeds = ![q]`) and 11.1
    (with `A_speeds = concat w [q]`). The original `theorem52_nonempty_correct`
    is FALSE for arbitrary closed `A`; this restriction recovers exactly what
    the manuscript ARGUMENT proves (the manuscript STATEMENT was too strong).

    The hypotheses use `μ(G ∩ [0,1)) > 0` directly (period-restricted volume),
    which is equivalent to `μ(G) > 0` by periodicity but avoids the periodicity
    side-argument inside this theorem.

    STATUS: proof reduces to `joint_fine_cell_exists`, the focused
    combinatorial gap. -/
theorem theorem52_nonempty_structured
    {kG kA : ℕ}
    (G_speeds : Fin kG → ℕ) (A_speeds : Fin kA → ℕ)
    (n L_G L_A p : ℕ)
    (hn : 3 ≤ n)
    (hLG : L_G = lcmSpeeds G_speeds) (hLG_pos : 0 < L_G)
    (hLA : L_A = lcmSpeeds A_speeds) (hLA_pos : 0 < L_A)
    (hcop : Nat.Coprime p L_G) (hp : 1 < p)
    (hposG : ∀ j, 0 < G_speeds j) (hposA : ∀ k, 0 < A_speeds k)
    (hG_unit_pos : 0 < MeasureTheory.volume
      (jointGoodSet G_speeds n ∩ Set.Ico (0 : ℝ) 1))
    (hA_unit_pos : 0 < MeasureTheory.volume
      (jointGoodSet A_speeds n ∩ Set.Ico (0 : ℝ) 1)) :
    ∃ t₀ ∈ jointGoodSet G_speeds n,
      Int.fract ((p : ℝ) * t₀) ∈ jointGoodSet A_speeds n := by
  have hG_idx := goodCellIdx_nonempty_of_volume_pos_in_unit
    G_speeds n L_G hn hLG hLG_pos hposG hG_unit_pos
  have hA_idx := goodCellIdx_nonempty_of_volume_pos_in_unit
    A_speeds n L_A hn hLA hLA_pos hposA hA_unit_pos
  have h_exists := joint_fine_cell_exists G_speeds A_speeds n L_G L_A p hn
    hLG hLG_pos hLA hLA_pos hcop hp hposG hposA hG_idx hA_idx
  exact theorem52_structured_of_joint_exists G_speeds A_speeds n L_G L_A p hn
    hLG hLG_pos hLA hLA_pos hp hposG hposA h_exists

/-- **ModDI convenience wrapper.** Tailored to Theorem 11.1's call shape:
    `A_speeds = Fin.snoc w q` (concatenation of `w : Fin r → ℕ` with `q : ℕ`),
    `A = jointGoodSet (Fin.snoc w q) n`.

    Drop-in replacement for the old `theorem52_nonempty_correct` call shape in
    `theorem111_ModDI`. Returns membership in `jointGoodSet (Fin.snoc w q) n` which
    equals `setA_ModDI w q n` (see `setA_ModDI_eq_jointGoodSet` in Theorem111). -/
theorem theorem52_nonempty_ModDI
    {kG r : ℕ} (G_speeds : Fin kG → ℕ)
    (w : Fin r → ℕ) (q : ℕ)
    (n L_G L_A p : ℕ)
    (hn : 3 ≤ n)
    (hLG : L_G = lcmSpeeds G_speeds) (hLG_pos : 0 < L_G)
    (hLA_def : L_A = lcmSpeeds (Fin.snoc w q))
    (hLA_pos : 0 < L_A)
    (hcop : Nat.Coprime p L_G) (hp : 1 < p)
    (hposG : ∀ j, 0 < G_speeds j)
    (hpos_w : ∀ k, 0 < w k) (hq_pos : 0 < q)
    (hG_unit_pos : 0 < MeasureTheory.volume
      (jointGoodSet G_speeds n ∩ Set.Ico (0 : ℝ) 1))
    (hA_unit_pos : 0 < MeasureTheory.volume
      (jointGoodSet (Fin.snoc w q) n ∩ Set.Ico (0 : ℝ) 1)) :
    ∃ t₀ ∈ jointGoodSet G_speeds n,
      Int.fract ((p : ℝ) * t₀) ∈ jointGoodSet (Fin.snoc w q) n := by
  have hposA : ∀ k : Fin (r + 1), 0 < (Fin.snoc w q : Fin (r + 1) → ℕ) k := by
    intro k
    induction k using Fin.lastCases with
    | last => simpa [Fin.snoc] using hq_pos
    | cast k => simpa [Fin.snoc] using hpos_w k
  exact theorem52_nonempty_structured
    G_speeds (Fin.snoc w q) n L_G L_A p hn hLG hLG_pos hLA_def hLA_pos
    hcop hp hposG hposA hG_unit_pos hA_unit_pos

/-- **DI convenience wrapper.** Tailored to Theorem 10.1's call shape:
    `A = goodSet q n` for a single integer speed `q`, with `q > 0`.

    Drop-in replacement for `theorem52_nonempty_correct` when `A = setA_DI q n
    = goodSet q n`. The structured proof goes through `theorem52_nonempty_structured`
    with `A_speeds = ![q]`. -/
theorem theorem52_nonempty_DI
    {kG : ℕ} (G_speeds : Fin kG → ℕ) (n L_G q p : ℕ)
    (hn : 3 ≤ n)
    (hLG : L_G = lcmSpeeds G_speeds) (hLG_pos : 0 < L_G)
    (hq_pos : 0 < q)
    (hcop : Nat.Coprime p L_G) (hp : 1 < p)
    (hposG : ∀ j, 0 < G_speeds j)
    (hG_unit_pos : 0 < MeasureTheory.volume
      (jointGoodSet G_speeds n ∩ Set.Ico (0 : ℝ) 1))
    (hA_unit_pos : 0 < MeasureTheory.volume
      (goodSet q n ∩ Set.Ico (0 : ℝ) 1)) :
    ∃ t₀ ∈ jointGoodSet G_speeds n, Int.fract ((p : ℝ) * t₀) ∈ goodSet q n := by
  -- Reduce to structured form with A_speeds = ![q].
  let A_speeds : Fin 1 → ℕ := ![q]
  have hLA_def : q = lcmSpeeds A_speeds := by
    have h_univ : (Finset.univ : Finset (Fin 1)) = {0} := by
      ext i; fin_cases i <;> simp
    show q = Finset.lcm Finset.univ A_speeds
    rw [h_univ, Finset.lcm_singleton]
    show q = normalize (A_speeds 0)
    simp [A_speeds]
  have hposA : ∀ k : Fin 1, 0 < A_speeds k := by
    intro k; fin_cases k; exact hq_pos
  -- goodSet q n = jointGoodSet ![q] n.
  have hA_eq : jointGoodSet A_speeds n = goodSet q n := by
    ext t
    simp only [jointGoodSet, A_speeds, Set.mem_iInter]
    constructor
    · intro h; exact h 0
    · intro h i; fin_cases i; exact h
  -- Volume identity follows.
  have hA_unit_pos' : 0 < MeasureTheory.volume
      (jointGoodSet A_speeds n ∩ Set.Ico (0 : ℝ) 1) := by
    rw [hA_eq]; exact hA_unit_pos
  obtain ⟨t₀, ht₀_G, ht₀_A⟩ := theorem52_nonempty_structured
    G_speeds A_speeds n L_G q p hn hLG hLG_pos hLA_def hq_pos
    hcop hp hposG hposA hG_unit_pos hA_unit_pos'
  rw [hA_eq] at ht₀_A
  exact ⟨t₀, ht₀_G, ht₀_A⟩

