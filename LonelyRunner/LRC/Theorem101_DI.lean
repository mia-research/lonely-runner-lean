import LonelyRunner.LRC.Defs
import LonelyRunner.LRC.Lemma21_FundamentalIdentity
import LonelyRunner.LRC.Lemma41_PositiveMeasure
import LonelyRunner.LRC.Theorem52_Weyl

/-!
# Theorem 10.1 — Divisor Induction

Source: `lrc_proof_v11_draft.md` §10.

**Statement:** In the hard case `(n-1)*v₁ < V ≤ (n-1)*v_{n-2}`, if the largest prime
factor `p` of `V` satisfies `gcd(p, lcm(slow runners)) = 1`, then `G_s ∩ G_V ≠ ∅`.

**Proof:**
1. `μ(G_s) > 0` from Lemma 4.1.
2. Write `V = p * q`.  By Lemma 2.1: `{V*t} = {q * {p*t}}`.
3. The condition `‖V*t‖ ≥ 1/n` is equivalent to `{p*t} ∈ A` where
   `A = {φ | ‖q*φ‖ ≥ 1/n}`, and `μ(A) = (n-2)/n > 0`.
4. `gcd(p, L) = 1` by hypothesis (where `L = lcm(slow runners)`).
5. Apply Theorem 5.2: ∃ `t₀ ∈ G_s` with `{p*t₀} ∈ A`, giving `t₀ ∈ G_s ∩ G_V`.

**Difficulty:** HARD (depends on Theorem 5.2).
-/


open MeasureTheory Set

/-! ## §10  Divisor Induction -/

/-- **Lemma 9.2a:** The largest prime factor of V does not divide lcm(slow runners) —
    this is the DI case. -/
def DI_case (V : ℕ) (slowSpeeds : Fin k → ℕ) : Prop :=
  ∃ p : ℕ, Nat.Prime p ∧ p ∣ V ∧ Nat.Coprime p (Finset.lcm Finset.univ slowSpeeds)

/-- The target set A for Divisor Induction: good set for a single runner of speed q. -/
noncomputable def setA_DI (q n : ℕ) : Set ℝ :=
  { φ : ℝ | circDist ((q : ℝ) * φ) ≥ (1 : ℝ) / (n : ℝ) }

/-- `setA_DI q n` equals `goodSet q n` (both are `{φ | circDist(q*φ) ≥ 1/n}`). -/
theorem setA_DI_eq_goodSet (q n : ℕ) : setA_DI q n = goodSet q n := rfl

/-- **Helper:** `setA_DI q n` is a closed set. -/
theorem setA_DI_isClosed (q n : ℕ) : IsClosed (setA_DI q n) := by
  rw [setA_DI_eq_goodSet]; exact goodSet_isClosed q n

/-- **Helper:** `setA_DI q n` has positive measure for `n ≥ 3` and `q ≥ 1`.

    Proof: the interval `I = [1/(q*n), (n-1)/(q*n)]` is contained in `setA_DI q n`
    and has measure `(n-2)/(q*n) > 0`.

    - For `t ∈ I`: `q*t ∈ [1/n, (n-1)/n] ⊆ [0,1)`, so `Int.fract(q*t) = q*t`.
    - `circDist(q*t) = min(q*t, 1 - q*t) ≥ min(1/n, 1/n) = 1/n`.

    MATHLIB_SEARCH: `Real.volume_Icc`, `measure_mono`, `Int.fract_eq_self`. -/
theorem setA_DI_pos_measure (q n : ℕ) (hn : 3 ≤ n) (hq : 0 < q) :
    0 < MeasureTheory.volume (setA_DI q n) := by
  rw [setA_DI_eq_goodSet]
  have hq_r : (0 : ℝ) < (q : ℝ) := Nat.cast_pos.mpr hq
  have hn_r : (0 : ℝ) < (n : ℝ) := by exact_mod_cast show 0 < n by omega
  have hn3_r : (2 : ℝ) < (n : ℝ) := by exact_mod_cast show 2 < n by omega
  -- Witness interval I = [1/(q*n), (n-1)/(q*n)]
  -- Step 1: I ⊆ goodSet q n
  have hI_sub : Set.Icc (1 / ((q : ℝ) * n)) (((n : ℝ) - 1) / ((q : ℝ) * n)) ⊆
      goodSet q n := by
    intro t ⟨hat, htb⟩
    simp only [goodSet, Set.mem_setOf_eq]
    -- Bounds on q*t: multiply both ends by q (q > 0)
    have hqt_lo : (1 : ℝ) / n ≤ (q : ℝ) * t := by
      have h : (q : ℝ) * (1 / ((q : ℝ) * n)) = 1 / n := by
        field_simp [hq_r.ne', hn_r.ne']
      linarith [mul_le_mul_of_nonneg_left hat hq_r.le]
    have hqt_hi : (q : ℝ) * t ≤ ((n : ℝ) - 1) / n := by
      have h : (q : ℝ) * (((n : ℝ) - 1) / ((q : ℝ) * n)) = ((n : ℝ) - 1) / n := by
        field_simp [hq_r.ne', hn_r.ne']
      linarith [mul_le_mul_of_nonneg_left htb hq_r.le]
    -- 0 ≤ q*t < 1
    have hqt_nn : (0 : ℝ) ≤ (q : ℝ) * t :=
      le_trans (div_nonneg one_pos.le hn_r.le) hqt_lo
    have hqt_lt1 : (q : ℝ) * t < 1 := by
      have h1n : ((n : ℝ) - 1) / n < 1 := by rw [div_lt_one hn_r]; linarith
      linarith
    -- ⌊q*t⌋ = 0 (since q*t ∈ [0,1))
    have hfract : Int.fract ((q : ℝ) * t) = (q : ℝ) * t := by
      have hfl : ⌊(q : ℝ) * t⌋ = (0 : ℤ) := by
        have h1 : (0 : ℤ) ≤ ⌊(q : ℝ) * t⌋ := Int.floor_nonneg.mpr hqt_nn
        have h2 : ⌊(q : ℝ) * t⌋ < (1 : ℤ) := by rw [Int.floor_lt]; exact_mod_cast hqt_lt1
        omega
      simp [Int.fract, hfl]
    -- circDist(q*t) = min(q*t, 1-q*t) ≥ 1/n
    -- key field identity: (n-1)/n = 1 - 1/n (needed for linarith below)
    have h_nm1 : ((n : ℝ) - 1) / n = 1 - 1 / n := by
      field_simp [hn_r.ne']
    unfold circDist
    rw [hfract]
    apply le_min hqt_lo
    linarith [hqt_hi, h_nm1]
  -- Step 2: I has positive measure  ((n-1)/(qn) - 1/(qn) = (n-2)/(qn) > 0)
  have hI_pos : (0 : ℝ) <
      ((n : ℝ) - 1) / ((q : ℝ) * n) - 1 / ((q : ℝ) * n) := by
    have : ((n : ℝ) - 1) / ((q : ℝ) * n) - 1 / ((q : ℝ) * n) =
           ((n : ℝ) - 2) / ((q : ℝ) * n) := by
      field_simp [hq_r.ne', hn_r.ne']; ring
    rw [this]
    exact div_pos (by linarith) (mul_pos hq_r hn_r)
  have hI_vol_pos : 0 < MeasureTheory.volume
      (Set.Icc (1 / ((q : ℝ) * n)) (((n : ℝ) - 1) / ((q : ℝ) * n))) := by
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_pos.mpr hI_pos
  -- Conclude by monotonicity of measure
  exact hI_vol_pos.trans_le (measure_mono hI_sub)

/-- Measure of `setA_DI q n` for `n ≥ 3`, `q ≥ 1`. Delegates to `setA_DI_pos_measure`. -/
theorem setA_DI_measure (q n : ℕ) (hn : 3 ≤ n) (hq : 0 < q) :
    0 < MeasureTheory.volume (setA_DI q n) :=
  setA_DI_pos_measure q n hn hq

/-- **Unit-interval variant** of `setA_DI_pos_measure`. The same witness interval
    `[1/(qn), (n-1)/(qn)]` lies inside `[0, 1)` (since `q ≥ 1, n ≥ 3` give
    `(n-1)/(qn) < 1`), so the existing proof bounds the measure on `Ico 0 1`
    directly. Used to feed `theorem52_nonempty_DI`. -/
theorem setA_DI_pos_measure_in_unit (q n : ℕ) (hn : 3 ≤ n) (hq : 0 < q) :
    0 < MeasureTheory.volume (setA_DI q n ∩ Set.Ico (0 : ℝ) 1) := by
  rw [setA_DI_eq_goodSet]
  have hq_r : (0 : ℝ) < (q : ℝ) := Nat.cast_pos.mpr hq
  have hn_r : (0 : ℝ) < (n : ℝ) := by exact_mod_cast show 0 < n by omega
  have hn3_r : (2 : ℝ) < (n : ℝ) := by exact_mod_cast show 2 < n by omega
  -- Same witness interval but now sliced into Ico 0 1.
  -- I = [1/(q*n), (n-1)/(q*n)] ⊆ Ico 0 1 since (n-1)/(qn) < 1 for q ≥ 1, n ≥ 3.
  have hI_sub_G : Set.Icc (1 / ((q : ℝ) * n)) (((n : ℝ) - 1) / ((q : ℝ) * n)) ⊆
      goodSet q n := by
    intro t ⟨hat, htb⟩
    simp only [goodSet, Set.mem_setOf_eq]
    have hqt_lo : (1 : ℝ) / n ≤ (q : ℝ) * t := by
      have h : (q : ℝ) * (1 / ((q : ℝ) * n)) = 1 / n := by
        field_simp [hq_r.ne', hn_r.ne']
      linarith [mul_le_mul_of_nonneg_left hat hq_r.le]
    have hqt_hi : (q : ℝ) * t ≤ ((n : ℝ) - 1) / n := by
      have h : (q : ℝ) * (((n : ℝ) - 1) / ((q : ℝ) * n)) = ((n : ℝ) - 1) / n := by
        field_simp [hq_r.ne', hn_r.ne']
      linarith [mul_le_mul_of_nonneg_left htb hq_r.le]
    have hqt_nn : (0 : ℝ) ≤ (q : ℝ) * t :=
      le_trans (div_nonneg one_pos.le hn_r.le) hqt_lo
    have hqt_lt1 : (q : ℝ) * t < 1 := by
      have h1n : ((n : ℝ) - 1) / n < 1 := by rw [div_lt_one hn_r]; linarith
      linarith
    have hfract : Int.fract ((q : ℝ) * t) = (q : ℝ) * t := by
      have hfl : ⌊(q : ℝ) * t⌋ = (0 : ℤ) := by
        have h1 : (0 : ℤ) ≤ ⌊(q : ℝ) * t⌋ := Int.floor_nonneg.mpr hqt_nn
        have h2 : ⌊(q : ℝ) * t⌋ < (1 : ℤ) := by rw [Int.floor_lt]; exact_mod_cast hqt_lt1
        omega
      simp [Int.fract, hfl]
    have h_nm1 : ((n : ℝ) - 1) / n = 1 - 1 / n := by field_simp [hn_r.ne']
    unfold circDist
    rw [hfract]
    apply le_min hqt_lo
    linarith [hqt_hi, h_nm1]
  -- Show the witness interval is inside Ico 0 1.
  have hI_sub_unit : Set.Icc (1 / ((q : ℝ) * n)) (((n : ℝ) - 1) / ((q : ℝ) * n)) ⊆
      Set.Ico (0 : ℝ) 1 := by
    intro t ⟨hat, htb⟩
    refine ⟨?_, ?_⟩
    · have h_lower_pos : (0 : ℝ) ≤ 1 / ((q : ℝ) * n) :=
        div_nonneg one_pos.le (mul_pos hq_r hn_r).le
      linarith
    · have h_upper_lt1 : ((n : ℝ) - 1) / ((q : ℝ) * n) < 1 := by
        rw [div_lt_one (mul_pos hq_r hn_r)]
        have h_q_ge1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
        have h_qn_ge : (q : ℝ) * n ≥ n := by
          calc (q : ℝ) * n ≥ 1 * n := mul_le_mul_of_nonneg_right h_q_ge1 hn_r.le
            _ = n := one_mul _
        linarith
      linarith
  -- Witness interval is in both G and unit interval, hence in their intersection.
  have hI_sub : Set.Icc (1 / ((q : ℝ) * n)) (((n : ℝ) - 1) / ((q : ℝ) * n)) ⊆
      goodSet q n ∩ Set.Ico (0 : ℝ) 1 := Set.subset_inter hI_sub_G hI_sub_unit
  -- Measure of the witness interval is (n-2)/(qn) > 0.
  have hI_pos : (0 : ℝ) <
      ((n : ℝ) - 1) / ((q : ℝ) * n) - 1 / ((q : ℝ) * n) := by
    have : ((n : ℝ) - 1) / ((q : ℝ) * n) - 1 / ((q : ℝ) * n) =
           ((n : ℝ) - 2) / ((q : ℝ) * n) := by
      field_simp [hq_r.ne', hn_r.ne']; ring
    rw [this]
    exact div_pos (by linarith) (mul_pos hq_r hn_r)
  have hI_vol_pos : 0 < MeasureTheory.volume
      (Set.Icc (1 / ((q : ℝ) * n)) (((n : ℝ) - 1) / ((q : ℝ) * n))) := by
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_pos.mpr hI_pos
  exact hI_vol_pos.trans_le (measure_mono hI_sub)

/-- **Key equivalence:** `t ∈ goodSet (p*q) n` iff `Int.fract (p*t) ∈ setA_DI q n`.

    Proof: direct from `goodSet_rewrite_via_fract` (Lemma 2.1 corollary) and the
    definition of `setA_DI`. -/
theorem DI_goodSet_rewrite (p q n : ℕ) (t : ℝ) :
    t ∈ goodSet (p * q) n ↔ Int.fract ((p : ℝ) * t) ∈ setA_DI q n := by
  rw [goodSet_rewrite_via_fract p q n t]
  simp only [setA_DI, Set.mem_setOf_eq]

/-- **Theorem 10.1** (Divisor Induction).

    In the hard case, if the largest prime `p` of `V` satisfies `gcd(p, L) = 1`
    (where `L = lcm(slow runners)`), then `G_s ∩ G_V ≠ ∅`.

    **Proof structure (matching manuscript §10):**
    1. `μ(G_s) > 0` from Lemma 4.1 (induction hypothesis H(n-1)).
    2. Write `V = p * q`. By Lemma 2.1: `circDist(V*t) = circDist(q * {p*t})`.
    3. So `t ∈ goodSet V n` iff `{p*t} ∈ setA_DI q n = goodSet q n`.
    4. `gcd(p, L) = 1` by hypothesis. Apply **Theorem 5.2 (correct form)**:
       `theorem52_nonempty_good` gives t₀ ∈ G_s with `circDist(p*t₀) ≥ 1/n`.
       But we need `circDist(V*t₀) ≥ 1/n`, not just `circDist(p*t₀) ≥ 1/n`.
       The DI rewrite (`DI_goodSet_rewrite`) gives the equivalence.

    **Dependency fix (from formalization team handover):**
    Previously this called `theorem52_nonempty` (derived from the false
    `theorem52_weyl`). The correct call is `theorem52_nonempty_good`, which is
    proved directly via irrational perturbation + compactness.
    Note: `theorem52_pos_measure` (positive measure) is FALSE — see its docstring.
    The set A in the application is `goodSet q n` (or equivalently `setA_DI q n`).

    BLOCKER: `theorem52_nonempty_good` has a sorry for the equidistribution step
    (Weyl's theorem for irrational α, absent from Mathlib 4.14). Once that sorry
    is filled, this theorem follows directly.
    STATUS: sorry — equidistribution is the bottleneck. -/
theorem theorem101_DI
    (n : ℕ) (hn : 3 ≤ n)
    (slowSpeeds : Fin (n - 2) → ℕ)
    (V : ℕ)
    (hpos : ∀ i, 0 < slowSpeeds i)
    (hmono : StrictMono slowSpeeds)
    (hV_hard_lo : (n - 1) * slowSpeeds ⟨0, by omega⟩ < V)
    (hV_hard_hi : V ≤ (n - 1) * slowSpeeds ⟨n - 3, by omega⟩)
    -- DI hypothesis: there exists a prime p | V with gcd(p, L) = 1
    (p q : ℕ) (hp : Nat.Prime p) (hpq : V = p * q)
    (hcop : Nat.Coprime p (Finset.lcm Finset.univ slowSpeeds))
    (Hn : H n) :
    ∃ t₀ : ℝ,
      (∀ i, circDist ((slowSpeeds i : ℝ) * t₀) ≥ (1 : ℝ) / n) ∧
      circDist ((V : ℝ) * t₀) ≥ (1 : ℝ) / n := by
  -- Derive V > 0 and q > 0
  have hV_pos : 0 < V :=
    Nat.lt_of_lt_of_le (Nat.mul_pos (by omega) (hpos ⟨0, by omega⟩)) (le_of_lt hV_hard_lo)
  have hq_pos : 0 < q := by
    rcases Nat.eq_zero_or_pos q with rfl | hq
    · simp [hpq] at hV_pos
    · exact hq
  -- Step 1: G_s = jointGoodSet slowSpeeds n has positive measure on [0,1) via Lemma 4.1
  --         (interval witness) + periodicity bridge.
  have hL_G_pos : 0 < lcmSpeeds slowSpeeds := by
    -- lcm of positives is positive.
    simp only [lcmSpeeds]
    rw [Nat.pos_iff_ne_zero]
    intro hzero
    rw [Finset.lcm_eq_zero_iff] at hzero
    obtain ⟨i, _, hi⟩ := hzero
    exact absurd hi (Nat.pos_iff_ne_zero.mp (hpos i))
  have hGs_unit_pos :
      0 < MeasureTheory.volume (jointGoodSet slowSpeeds n ∩ Set.Ico (0 : ℝ) 1) := by
    obtain ⟨t_star, δ, hδ_pos, _, hIcc_sub, _⟩ :=
      lemma41_positive_measure hn rfl slowSpeeds hpos hmono Hn
    exact jointGoodSet_inter_unit_pos_of_Icc_subset slowSpeeds n hpos
      (t_star - δ) (t_star + δ) (by linarith) hIcc_sub
  -- Step 2: A ∩ [0,1) has positive measure via the in-unit variant.
  have hA_unit_pos :
      0 < MeasureTheory.volume (goodSet q n ∩ Set.Ico (0 : ℝ) 1) := by
    have h := setA_DI_pos_measure_in_unit q n hn hq_pos
    rw [setA_DI_eq_goodSet] at h
    exact h
  -- Step 3: hcop restated in terms of lcmSpeeds (definitionally equal to Finset.lcm univ).
  have hcop' : Nat.Coprime p (lcmSpeeds slowSpeeds) := hcop
  -- Step 4: Apply theorem52_nonempty_DI (structured Option A form) with A = goodSet q n.
  -- Gives t₀ ∈ G_s with Int.fract(p·t₀) ∈ goodSet q n,
  -- i.e. circDist(q·fract(p·t₀)) ≥ 1/n.
  -- By Lemma 2.1: circDist(q·fract(p·t₀)) = circDist(V·t₀). ✓
  -- BLOCKER: theorem52_nonempty_DI reduces to `joint_fine_cell_exists` (focused
  -- combinatorial gap, replaces the unbounded equidistribution gap).
  obtain ⟨t₀, ht₀_G, ht₀_frac⟩ :=
    theorem52_nonempty_DI slowSpeeds n (lcmSpeeds slowSpeeds) q p
      hn rfl hL_G_pos hq_pos hcop' hp.one_lt hpos
      hGs_unit_pos hA_unit_pos
  -- Step 5: Assemble the witness t₀.
  refine ⟨t₀, ?_, ?_⟩
  · -- Slow runners: t₀ ∈ G_s = jointGoodSet slowSpeeds n.
    intro i
    exact Set.mem_iInter.mp ht₀_G i
  · -- Fast runner V: circDist(V·t₀) ≥ 1/n.
    -- DI_goodSet_rewrite: t₀ ∈ goodSet (p*q) n ↔ fract(p·t₀) ∈ setA_DI q n.
    have ht₀_frac' : Int.fract ((p : ℝ) * t₀) ∈ setA_DI q n := by
      rw [setA_DI_eq_goodSet]; exact ht₀_frac
    have hmem : t₀ ∈ goodSet V n := by
      rw [show V = p * q from hpq]
      exact (DI_goodSet_rewrite p q n t₀).mpr ht₀_frac'
    exact hmem

/-! ## §10  Connection to the hard case -/

/-- In the DI case, `p` is the largest prime factor of `V`.
    In particular, `p ≥ 2` (being prime). -/
theorem DI_prime_ge_two (p V : ℕ) (hp : Nat.Prime p) (hdvd : p ∣ V) : 2 ≤ p :=
  hp.two_le
