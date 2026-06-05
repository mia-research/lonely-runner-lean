import LonelyRunner.LRC.Defs

/-!
# Lemma 2.1 — Fundamental Identity

Source: `lrc_proof_v11_draft.md` §2.4.

**Statement:** For any integers `a ≥ 1`, `b ≥ 1`, and any real `t`:
  `Int.fract (a * Int.fract (b * t)) = Int.fract (a * b * t)`

**Proof idea:** `Int.fract (b * t) = b * t - ⌊b * t⌋`, so
  `a * Int.fract (b * t) = a * b * t - a * ⌊b * t⌋`.
Since `a * ⌊b * t⌋ ∈ ℤ`, taking fractional parts gives the result.

This is the key algebraic engine used in Theorems 10.1 and 11.1.
-/


/-! ## §2.4  Fundamental Identity -/

/-- **Lemma 2.1** (Fundamental Identity).
    For natural numbers `a`, `b` and any real `t`:
    `{a · {b·t}} = {a·b·t}` where `{·}` denotes `Int.fract`. -/
theorem fundamental_identity (a b : ℕ) (t : ℝ) :
    Int.fract ((a : ℝ) * Int.fract ((b : ℝ) * t)) =
    Int.fract ((a : ℝ) * ((b : ℝ) * t)) := by
  unfold Int.fract
  have h : (a : ℝ) * ((↑b * t) - ↑⌊↑b * t⌋) = (a : ℝ) * (↑b * t) - (a : ℝ) * ↑⌊↑b * t⌋ := by ring
  rw [h]
  have cast_floor : (a : ℝ) * ↑⌊↑b * t⌋ = ↑((a : ℤ) * ⌊↑b * t⌋) := by push_cast; ring
  rw [cast_floor]
  -- Key property: ⌊x - n⌋ = ⌊x⌋ - n for integer n
  have floor_prop : ⌊(a : ℝ) * (↑b * t) - ↑((a : ℤ) * ⌊↑b * t⌋)⌋ =
                    ⌊(a : ℝ) * (↑b * t)⌋ - (a : ℤ) * ⌊↑b * t⌋ := by
    calc ⌊(a : ℝ) * (↑b * t) - ↑((a : ℤ) * ⌊↑b * t⌋)⌋
        = ⌊(a : ℝ) * (↑b * t) + ↑(-(a : ℤ) * ⌊↑b * t⌋)⌋ := by congr 1; push_cast; ring
      _ = ⌊(a : ℝ) * (↑b * t)⌋ + (-(a : ℤ) * ⌊↑b * t⌋) := Int.floor_add_intCast _ _
      _ = ⌊(a : ℝ) * (↑b * t)⌋ - (a : ℤ) * ⌊↑b * t⌋ := by ring
  rw [floor_prop]
  simp only [Int.cast_sub]
  ring

/-- Alternate form of Lemma 2.1 with `V = a*b` written directly. -/
theorem fundamental_identity' (p q : ℕ) (t : ℝ) :
    Int.fract ((q : ℝ) * Int.fract ((p : ℝ) * t)) =
    Int.fract ((p : ℝ) * ((q : ℝ) * t)) := by
  have h := fundamental_identity q p t
  -- By commutativity of multiplication: (q : ℝ) * ((p : ℝ) * t) = (p : ℝ) * ((q : ℝ) * t)
  have comm : (q : ℝ) * ((p : ℝ) * t) = (p : ℝ) * ((q : ℝ) * t) := by ring
  rw [comm] at h
  exact h

/-- **Corollary 2.2.** For integers `a, b ≥ 1` and real `t`:
    `circDist (a * Int.fract (b * t)) = circDist (a * b * t)`. -/
theorem circDist_fundamental (a b : ℕ) (t : ℝ) :
    circDist ((a : ℝ) * Int.fract ((b : ℝ) * t)) =
    circDist ((a : ℝ) * ((b : ℝ) * t)) := by
  -- `circDist` depends only on `Int.fract`, and Lemma 2.1 equates the fracts.
  unfold circDist
  congr 1
  · exact fundamental_identity a b t
  · congr 1; exact fundamental_identity a b t

/-- **Corollary 2.2 (norm form).**
    `‖V·t‖ ≥ 1/n` iff `‖q · {p·t}‖ ≥ 1/n`, where `V = p*q`. -/
theorem goodSet_rewrite_via_fract (p q n : ℕ) (t : ℝ) :
    t ∈ goodSet (p * q) n ↔
    circDist ((q : ℝ) * Int.fract ((p : ℝ) * t)) ≥ (1 : ℝ) / (n : ℝ) := by
  unfold goodSet
  simp only [Set.mem_setOf_eq]
  constructor <;> intro h
  · rw [circDist_fundamental q p t]
    convert h using 2
    push_cast; ring
  · rw [circDist_fundamental q p t] at h
    convert h using 2
    push_cast; ring

/-- The set `A = {φ ∈ [0,1) | circDist (q * φ) ≥ 1/n}` appearing in Theorem 10.1. -/
noncomputable def setA (q n : ℕ) : Set ℝ :=
  { φ : ℝ | Int.fract φ = φ ∧ circDist ((q : ℝ) * φ) ≥ (1 : ℝ) / (n : ℝ) }

/-- Measure of `setA q n` is `(n-2)/n` (when `n ≥ 2`).

    The set decomposes into `q` intervals per period `[0,1)`, each of width `(n-2)/(n*q)`.
    Total measure: `q * (n-2)/(n*q) = (n-2)/n`. -/
theorem setA_measure (q n : ℕ) (hn : 2 ≤ n) (hq : 0 < q) :
    MeasureTheory.volume (setA q n) = ENNReal.ofReal ((n - 2 : ℝ) / n) := by
  -- Proof: decompose setA q n = ⋃_{k<q} Icc(k/q+1/(nq), k/q+(n-1)/(nq)).
  -- Each interval has measure (n-2)/(nq); q intervals total → (n-2)/n.
  have hn_r  : (0 : ℝ) < n := by exact_mod_cast show 0 < n by omega
  have hq_r  : (0 : ℝ) < q := Nat.cast_pos.mpr hq
  have hn_ne : (n : ℝ) ≠ 0 := hn_r.ne'
  have hq_ne : (q : ℝ) ≠ 0 := hq_r.ne'
  have hn2_nn : (0 : ℝ) ≤ (n : ℝ) - 2 := by
    have h2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  -- Step 1: prove the set equality
  have h_eq : setA q n = ⋃ k : Fin q,
      Set.Icc ((k : ℝ) / (q : ℝ) + 1 / ((n : ℝ) * (q : ℝ)))
               ((k : ℝ) / (q : ℝ) + ((n : ℝ) - 1) / ((n : ℝ) * (q : ℝ))) := by
    ext φ
    simp only [setA, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_Icc]
    constructor
    · -- Forward: φ ∈ setA → ∃ k, φ ∈ I_k
      rintro ⟨hfrac_eq, hcirc⟩
      -- φ ∈ [0, 1) from Int.fract φ = φ
      have h0φ : 0 ≤ φ := by
        have := Int.fract_nonneg φ; linarith [hfrac_eq.symm]
      have hφ1 : φ < 1 := by
        have := Int.fract_lt_one φ; linarith [hfrac_eq.symm]
      -- q·φ ∈ [0, q)
      have hqφ_nn : 0 ≤ (q : ℝ) * φ := mul_nonneg hq_r.le h0φ
      have hqφ_lt : (q : ℝ) * φ < (q : ℝ) := by
        have h := mul_lt_mul_of_pos_left hφ1 hq_r
        linarith [mul_one (q : ℝ)]
      -- ⌊q·φ⌋ ∈ {0,...,q-1}
      have hfl_nn : 0 ≤ ⌊(q : ℝ) * φ⌋ := Int.floor_nonneg.mpr hqφ_nn
      have hfl_lt  : ⌊(q : ℝ) * φ⌋ < (q : ℤ) := by
        rw [Int.floor_lt]; exact_mod_cast hqφ_lt
      -- k = ⌊q·φ⌋ as a Fin q (via toNat)
      have hfl_lt_n : ⌊(q : ℝ) * φ⌋.toNat < q := by
        have hcast : (⌊(q : ℝ) * φ⌋.toNat : ℤ) = ⌊(q : ℝ) * φ⌋ :=
          Int.toNat_of_nonneg hfl_nn
        have h : (⌊(q : ℝ) * φ⌋.toNat : ℤ) < (q : ℤ) := hcast.symm ▸ hfl_lt
        exact_mod_cast h
      -- (⌊q·φ⌋.toNat : ℝ) = (⌊q·φ⌋ : ℝ)
      have hkr : (⌊(q : ℝ) * φ⌋.toNat : ℝ) = (⌊(q : ℝ) * φ⌋ : ℝ) :=
        by exact_mod_cast Int.toNat_of_nonneg hfl_nn
      -- Int.fract(q·φ) = q·φ - ⌊q·φ⌋.toNat  (via definition of Int.fract)
      have hfr : Int.fract ((q : ℝ) * φ) = (q : ℝ) * φ - ⌊(q : ℝ) * φ⌋.toNat := by
        unfold Int.fract; linarith [hkr]
      -- circDist ≥ 1/n means fract ∈ [1/n, (n-1)/n]
      have hcirc' : 1 / (n : ℝ) ≤ Int.fract ((q : ℝ) * φ) ∧
                    Int.fract ((q : ℝ) * φ) ≤ ((n : ℝ) - 1) / (n : ℝ) := by
        unfold circDist at hcirc
        have hmin := le_min_iff.mp hcirc
        exact ⟨hmin.1, by linarith [hmin.2,
          show ((n : ℝ) - 1) / n = 1 - 1 / n from by field_simp [hn_ne]; try ring]⟩
      refine ⟨⟨⌊(q : ℝ) * φ⌋.toNat, hfl_lt_n⟩, ?_, ?_⟩
      -- Lower bound: φ ≥ k/q + 1/(nq)
      · rw [← sub_nonneg,
            show φ - ((⌊(q : ℝ) * φ⌋.toNat : ℝ) / (q : ℝ) + 1 / ((n : ℝ) * (q : ℝ))) =
                 ((q : ℝ) * φ - (⌊(q : ℝ) * φ⌋.toNat : ℝ) - 1 / (n : ℝ)) / (q : ℝ) from by
              field_simp [hn_ne, hq_ne]; try ring]
        apply div_nonneg _ hq_r.le
        linarith [hcirc'.1, hfr.symm]
      -- Upper bound: φ ≤ k/q + (n-1)/(nq)
      · rw [← sub_nonneg,
            show (⌊(q : ℝ) * φ⌋.toNat : ℝ) / (q : ℝ) + ((n : ℝ) - 1) / ((n : ℝ) * (q : ℝ)) - φ =
                 (((n : ℝ) - 1) / (n : ℝ) - ((q : ℝ) * φ - (⌊(q : ℝ) * φ⌋.toNat : ℝ))) / (q : ℝ) from by
              field_simp [hn_ne, hq_ne]; try ring]
        apply div_nonneg _ hq_r.le
        linarith [hcirc'.2, hfr.symm]
    · -- Backward: k ∈ Fin q, φ ∈ I_k → φ ∈ setA
      rintro ⟨k, h_lo, h_hi⟩
      have hk_nn : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg _
      -- (k : ℝ) < (q : ℝ), so (k : ℝ) ≤ (q : ℝ) - 1
      have hk_lt : (k : ℝ) ≤ (q : ℝ) - 1 := by
        have h : k.val + 1 ≤ q := k.isLt
        have h' : (k.val : ℝ) + 1 ≤ (q : ℝ) := by exact_mod_cast h
        linarith
      -- q·φ bounds: k + 1/n ≤ q·φ ≤ k + (n-1)/n
      have hqφ_lo : (k : ℝ) + 1 / (n : ℝ) ≤ (q : ℝ) * φ := by
        rw [← sub_nonneg,
            show (q : ℝ) * φ - ((k : ℝ) + 1 / n) =
                 (q : ℝ) * (φ - ((k : ℝ) / q + 1 / (n * q))) from by
              field_simp [hn_ne, hq_ne]; try ring]
        exact mul_nonneg hq_r.le (by linarith)
      have hqφ_hi : (q : ℝ) * φ ≤ (k : ℝ) + ((n : ℝ) - 1) / (n : ℝ) := by
        rw [← sub_nonneg,
            show (k : ℝ) + ((n : ℝ) - 1) / n - (q : ℝ) * φ =
                 (q : ℝ) * ((k : ℝ) / q + ((n : ℝ) - 1) / (n * q) - φ) from by
              field_simp [hn_ne, hq_ne]; try ring]
        exact mul_nonneg hq_r.le (by linarith)
      -- Int.fract(q·φ) = q·φ - k  (since ⌊q·φ⌋ = k)
      have hfl : ⌊(q : ℝ) * φ⌋ = (k : ℤ) := by
        apply Int.floor_eq_iff.mpr
        refine ⟨?_, ?_⟩
        · -- ↑k ≤ q·φ  (use exact_mod_cast to handle ℤ vs ℕ cast)
          have h1n : (0 : ℝ) < 1 / n := div_pos one_pos hn_r
          have hle : (k : ℝ) ≤ (q : ℝ) * φ := by linarith
          exact_mod_cast hle
        · -- q·φ < ↑k + 1
          have h_nm1 : ((n : ℝ) - 1) / n < 1 := by rw [div_lt_one hn_r]; linarith
          have hlt : (q : ℝ) * φ < (k : ℝ) + 1 := by linarith
          exact_mod_cast hlt
      -- Int.fract(q·φ) = q·φ - k  (unfold definition then use hfl)
      have hqφ_frac : Int.fract ((q : ℝ) * φ) = (q : ℝ) * φ - (k : ℝ) := by
        unfold Int.fract
        have h2 : (⌊(q : ℝ) * φ⌋ : ℝ) = (k : ℝ) := by exact_mod_cast hfl
        linarith
      constructor
      · -- Int.fract φ = φ  (i.e., φ ∈ [0, 1))
        apply Int.fract_eq_self.mpr
        constructor
        · -- 0 ≤ φ
          have hnn : 0 ≤ (k : ℝ) / q + 1 / (n * q) :=
            add_nonneg (div_nonneg hk_nn hq_r.le)
                       (div_nonneg one_pos.le (mul_pos hn_r hq_r).le)
          linarith
        · -- φ < 1:  φ ≤ k/q + (n-1)/(nq) < 1
          have h_ub : (k : ℝ) / q + ((n : ℝ) - 1) / (n * q) < 1 := by
            rw [show (k : ℝ) / q + ((n : ℝ) - 1) / (n * q) =
                      ((n : ℝ) * k + (n - 1)) / (n * q) from by
                  field_simp [hn_ne, hq_ne]; try ring,
                div_lt_one (mul_pos hn_r hq_r)]
            nlinarith [hk_lt, hn_r, hq_r]
          linarith
      · -- circDist(q·φ) ≥ 1/n
        unfold circDist
        rw [hqφ_frac]
        apply le_min
        · linarith  -- 1/n ≤ q·φ - k
        · have h_nm1 : ((n : ℝ) - 1) / n = 1 - 1 / n := by
            field_simp [hn_ne]; try ring
          linarith  -- 1/n ≤ 1 - (q·φ - k) from q·φ-k ≤ (n-1)/n
  -- Step 2: pairwise disjointness of the intervals
  -- Use explicit lambda to avoid `on` notation parse issues
  have hdisj : Pairwise (fun i j : Fin q => Disjoint
      (Set.Icc ((i : ℝ) / (q : ℝ) + 1 / ((n : ℝ) * (q : ℝ)))
                ((i : ℝ) / (q : ℝ) + ((n : ℝ) - 1) / ((n : ℝ) * (q : ℝ))))
      (Set.Icc ((j : ℝ) / (q : ℝ) + 1 / ((n : ℝ) * (q : ℝ)))
                ((j : ℝ) / (q : ℝ) + ((n : ℝ) - 1) / ((n : ℝ) * (q : ℝ))))) := by
    intro i j hij
    rw [Set.disjoint_left]
    intro x hxi hxj
    simp only [Set.mem_Icc] at hxi hxj
    have h_nq : (0 : ℝ) < n * q := mul_pos hn_r hq_r
    -- Key: 1/q - (n-1)/(nq) = 1/(nq) > 0, so hi_i < lo_j when i+1 ≤ j
    have h_n1_lt_1q : ((n : ℝ) - 1) / (n * q) < 1 / q := by
      have h_eq : (1 : ℝ) / q - ((n : ℝ) - 1) / (n * q) = 1 / (n * q) := by
        field_simp [hn_ne, hq_ne]; try ring
      linarith [div_pos one_pos h_nq]
    have h1nq : (0 : ℝ) ≤ 1 / ((n : ℝ) * q) :=
      div_nonneg one_pos.le h_nq.le
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with h | h
    · -- i.val < j.val → right end of I_i < left end of I_j
      have hji : (i : ℝ) + 1 ≤ (j : ℝ) := by
        have h' : i.val + 1 ≤ j.val := by omega
        exact_mod_cast h'
      -- i/q + 1/q ≤ j/q since j - i - 1 ≥ 0 → (j-i-1)/q ≥ 0
      have h_i1_le_j : (i : ℝ) / q + 1 / q ≤ (j : ℝ) / q := by
        have key : 0 ≤ ((j : ℝ) - (i : ℝ) - 1) / q :=
          div_nonneg (by linarith) hq_r.le
        linarith [show (j : ℝ) / q - ((i : ℝ) / q + 1 / q) =
                       ((j : ℝ) - (i : ℝ) - 1) / q from by ring]
      linarith
    · -- j.val < i.val (symmetric)
      have hij' : (j : ℝ) + 1 ≤ (i : ℝ) := by
        have h' : j.val + 1 ≤ i.val := by omega
        exact_mod_cast h'
      have h_j1_le_i : (j : ℝ) / q + 1 / q ≤ (i : ℝ) / q := by
        have key : 0 ≤ ((i : ℝ) - (j : ℝ) - 1) / q :=
          div_nonneg (by linarith) hq_r.le
        linarith [show (i : ℝ) / q - ((j : ℝ) / q + 1 / q) =
                       ((i : ℝ) - (j : ℝ) - 1) / q from by ring]
      linarith
  -- Step 3: measurability
  have hmeas : ∀ k : Fin q, MeasurableSet
      (Set.Icc ((k : ℝ) / (q : ℝ) + 1 / ((n : ℝ) * (q : ℝ)))
               ((k : ℝ) / (q : ℝ) + ((n : ℝ) - 1) / ((n : ℝ) * (q : ℝ)))) :=
    fun _ => measurableSet_Icc
  -- Step 4: measure computation
  rw [h_eq, MeasureTheory.measure_iUnion hdisj hmeas]
  simp_rw [Real.volume_Icc]
  -- Width of each interval = (n-2)/(nq), independent of k
  have hw : ∀ k : Fin q,
      (k : ℝ) / q + ((n : ℝ) - 1) / (n * q) - ((k : ℝ) / q + 1 / (n * q)) =
      ((n : ℝ) - 2) / (n * q) := fun _ => by field_simp [hn_ne, hq_ne]; try ring
  simp_rw [hw]
  -- Sum = q • ofReal((n-2)/(nq)); convert tsum over Fin q to smul
  have htsum : ∑' _k : Fin q, ENNReal.ofReal ((n - 2 : ℝ) / (n * q)) =
               q • ENNReal.ofReal ((n - 2 : ℝ) / (n * q)) := by
    simp [tsum_fintype, Finset.sum_const, Finset.card_univ]
  rw [htsum]
  -- Helper: m • ofReal c = ofReal (m * c) for c ≥ 0
  have nsmul_ofReal : ∀ (m : ℕ) (c : ℝ), 0 ≤ c →
      m • ENNReal.ofReal c = ENNReal.ofReal ((m : ℝ) * c) := by
    intro m
    induction m with
    | zero => intro c _; simp
    | succ m' ih =>
      intro c hc
      rw [add_smul, one_smul, ih c hc,
          ← ENNReal.ofReal_add (mul_nonneg (Nat.cast_nonneg _) hc) hc]
      congr 1; push_cast; ring
  rw [nsmul_ofReal q _ (div_nonneg hn2_nn (mul_pos hn_r hq_r).le)]
  congr 1
  -- q * ((n-2)/(nq)) = (n-2)/n
  field_simp [hn_ne, hq_ne]; try ring
