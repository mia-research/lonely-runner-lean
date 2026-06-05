import LonelyRunner.LRC.Defs
import LonelyRunner.LRC.Lemma41_PositiveMeasure

/-!
# Theorem 7.1 — Large Speed Ratio

Source: `lrc_proof_v11_draft.md` §7.

**Statement:** If `V > (n-1) * v_{n-2}` (where `v_{n-2}` is the second-largest speed),
then there exists `t` with `circDist(v_j * t) ≥ 1/n` for all `j`.

**Proof sketch:**
1. Get `t**` from `H(n-1)` with `circDist(v_j * t**) ≥ 1/(n-1)` for slow runners.
2. By Lemma 4.1, `I = [t** - δ, t** + δ] ⊆ G_s` with `δ = 1/(n(n-1)v_{n-2})`.
3. Each connected component of `B_V` (bad set for V) has width `2/(nV) < 2δ = |I|`.
4. No single bad component covers all of `I`, so `I ∩ G_V ≠ ∅`.

**Difficulty:** MODERATE — interval arithmetic, two sub-cases for the geometric argument.
-/


open MeasureTheory Set

/-! ## §7  Large Speed Ratio -/

/-- Width of a connected component of `badSet V n`: each component is an interval
    of length `2/(n*V)` centred at some integer multiple of `1/V`. -/
theorem badSet_component_width (V n : ℕ) (hV : 0 < V) (hn : 1 < n) :
    ∀ k : ℤ,
      (badSet V n) ∩ Set.Ioo ((k : ℝ) / V - 1 / (n * V)) ((k : ℝ) / V + 1 / (n * V)) =
      Set.Ioo ((k : ℝ) / V - 1 / (n * V)) ((k : ℝ) / V + 1 / (n * V)) := by
  intro k
  rw [Set.inter_eq_right]
  -- Show: every t in the open interval satisfies circDist(V*t) < 1/n (i.e. t ∈ badSet V n).
  intro t ht
  simp only [badSet, goodSet, Set.mem_compl_iff, Set.mem_setOf_eq, not_le]
  -- Reals positivity helpers
  have hV_r : (0 : ℝ) < V := Nat.cast_pos.mpr hV
  have hn_r : (0 : ℝ) < n := by exact_mod_cast show 0 < n by omega
  -- Key bound: 1/n ≤ 1/2 (since n ≥ 2, as hn : 1 < n)
  have h1n : (1 : ℝ) / n ≤ 1 / 2 :=
    one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast show 2 ≤ n by omega)
  -- Extract interval membership
  rw [Set.mem_Ioo] at ht
  -- V*t ∈ (k - 1/n, k + 1/n) via field arithmetic
  have ht_lo : (k : ℝ) - 1 / n < (V : ℝ) * t := by
    have h := ht.1
    have heq : (V : ℝ) * ((k : ℝ) / V - 1 / ((n : ℝ) * V)) = k - 1 / n := by
      field_simp [hV_r.ne', hn_r.ne']
    linarith [mul_lt_mul_of_pos_left h hV_r, heq.symm.le]
  have ht_hi : (V : ℝ) * t < (k : ℝ) + 1 / n := by
    have h := ht.2
    have heq : (V : ℝ) * ((k : ℝ) / V + 1 / ((n : ℝ) * V)) = k + 1 / n := by
      field_simp [hV_r.ne', hn_r.ne']
    linarith [mul_lt_mul_of_pos_left h hV_r, heq.le]
  -- Case split: V*t < k or V*t ≥ k
  unfold circDist
  rcases lt_or_ge ((V : ℝ) * t) k with h_lt | h_ge
  · -- V*t ∈ (k-1/n, k): floor(V*t) = k-1
    have hfl : ⌊(V : ℝ) * t⌋ = k - 1 := by
      apply Int.floor_eq_iff.mpr
      constructor
      · push_cast; linarith [h1n]   -- k-1 ≤ V*t: from ht_lo and 1/n ≤ 1/2 ≤ 1
      · push_cast; linarith         -- V*t < k: direct from h_lt
    rw [Int.fract, hfl]
    push_cast
    -- fract = V*t - (k-1) = V*t - k + 1 ∈ (1-1/n, 1)
    -- circDist = min(fract, 1-fract) = k - V*t (the smaller piece) < 1/n
    have hfrac_lo : (V : ℝ) * t - (↑k - 1) > 1 - 1 / n := by linarith
    have hfrac_hi : (V : ℝ) * t - (↑k - 1) < 1 := by linarith
    rw [show 1 - ((V : ℝ) * t - (↑k - 1)) = ↑k - (V : ℝ) * t by ring]
    -- min(V*t-(k-1), k-V*t): since k-V*t < 1/n ≤ 1/2 < V*t-(k-1), min = k-V*t
    rw [min_comm]
    rw [min_eq_left (by linarith [h1n])]  -- k-V*t ≤ V*t-(k-1): since k-V*t<1/2<V*t-(k-1)
    linarith                               -- k-V*t < 1/n from ht_lo
  · -- V*t ≥ k: floor(V*t) = k (since V*t < k + 1/n ≤ k+1)
    have hfl : ⌊(V : ℝ) * t⌋ = k := by
      apply Int.floor_eq_iff.mpr
      constructor
      · exact_mod_cast h_ge
      · push_cast; linarith [h1n]   -- V*t < k+1: from ht_hi and 1/n ≤ 1/2 ≤ 1
    rw [Int.fract, hfl]
    push_cast
    -- fract = V*t - k ∈ [0, 1/n) ⊆ [0, 1/2)
    have hfrac_nn : (V : ℝ) * t - k ≥ 0 := by linarith
    have hfrac_lt : (V : ℝ) * t - k < 1 / n := by linarith
    rw [min_eq_left (by linarith [h1n])]   -- V*t-k ≤ 1-(V*t-k): since V*t-k<1/n≤1/2
    linarith

/-- **Key geometric lemma:** Any interval `[a, b]` with length `> 2/(n*V)` intersects
    `goodSet V n`. Proof: if `a ∈ G_V` we are done; otherwise `a` lies inside a bad
    component centred at some integer `k/V`, and the right boundary `k/V + 1/(n*V)` lies
    strictly in `(a, b)` and has `circDist(V * (k/V + 1/(n*V))) = 1/n`. -/
theorem interval_escapes_bad
    (V n : ℕ) (hV : 0 < V) (hn : 1 < n)
    (a b : ℝ) (hlen : 2 / ((n : ℝ) * (V : ℝ)) < b - a) :
    (Set.Icc a b ∩ goodSet V n).Nonempty := by
  have hV_r : (0 : ℝ) < (V : ℝ) := Nat.cast_pos.mpr hV
  have hn_r : (0 : ℝ) < (n : ℝ) := by exact_mod_cast show 0 < n by omega
  have h1n : (1 : ℝ) / (n : ℝ) ≤ 1 / 2 :=
    one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast show 2 ≤ n by omega)
  have hab : a < b := by linarith [div_pos (by norm_num : (0:ℝ) < 2) (mul_pos hn_r hV_r)]
  -- Auxiliary: circDist(k + 1/n) ≥ 1/n for any integer k (it equals 1/n exactly).
  have boundary_good : ∀ k : ℤ, (k : ℝ) / (V : ℝ) + 1 / ((n : ℝ) * (V : ℝ)) ∈ goodSet V n := by
    intro k
    simp only [goodSet, Set.mem_setOf_eq, ge_iff_le]
    have hVc : (V : ℝ) * ((k : ℝ) / V + 1 / ((n : ℝ) * V)) = (k : ℝ) + 1 / (n : ℝ) := by
      field_simp [hV_r.ne', hn_r.ne']
    rw [hVc]; unfold circDist
    have h1n_pos : (0 : ℝ) < 1 / (n : ℝ) := div_pos one_pos hn_r
    have h1n_lt1 : (1 : ℝ) / (n : ℝ) < 1 := by
      rw [div_lt_one hn_r]; exact_mod_cast show 1 < n by omega
    have hfl : ⌊(k : ℝ) + 1 / (n : ℝ)⌋ = k := Int.floor_eq_iff.mpr
      ⟨by push_cast; linarith [h1n_pos.le], by push_cast; linarith⟩
    rw [Int.fract, hfl]; push_cast
    -- k + 1/n - k simplifies to 1/n; then le_min holds by le_rfl and h1n
    have hsimpl : (k : ℝ) + 1 / n - k = 1 / n := by ring
    rw [hsimpl]; exact le_min le_rfl (by linarith)
  -- Case: is a ∈ goodSet V n?
  by_cases ha : a ∈ goodSet V n
  · exact ⟨a, Set.left_mem_Icc.mpr hab.le, ha⟩
  -- a is bad: circDist(V*a) < 1/n. Split on which part of min is small.
  · simp only [goodSet, Set.mem_setOf_eq, not_le] at ha
    unfold circDist at ha
    rw [min_lt_iff] at ha
    rcases ha with h_frac | h_frac
    · -- Case A: Int.fract(V*a) < 1/n.
      -- k = ⌊V*a⌋; a ∈ [k/V, k/V + 1/(nV)); right boundary c = k/V + 1/(nV) is in (a,b).
      set k := ⌊(V : ℝ) * a⌋ with hk_def
      have hk_le : (k : ℝ) ≤ (V : ℝ) * a := Int.floor_le _
      -- hkr connects the ℝ-cast of k with ↑⌊V*a⌋ so linarith can use h_frac
      have hkr : (k : ℝ) = ↑⌊(V : ℝ) * a⌋ := by exact_mod_cast hk_def
      -- h_frac : Int.fract(V*a) < 1/n means V*a - ↑⌊V*a⌋ < 1/n, i.e. V*a - k < 1/n
      rw [Int.fract] at h_frac; push_cast at h_frac
      set c := (k : ℝ) / (V : ℝ) + 1 / ((n : ℝ) * (V : ℝ)) with hc_def
      -- a < c: V*a - k < 1/n (from h_frac via hkr) → V*a < k + 1/n = V*c → a < c
      have hca : a < c := by
        have hVc : (V : ℝ) * c = (k : ℝ) + 1 / (n : ℝ) := by
          simp only [hc_def]; field_simp [hV_r.ne', hn_r.ne']
        have hVa_lt_Vc : (V : ℝ) * a < (V : ℝ) * c := by rw [hVc]; linarith [hkr]
        exact lt_of_mul_lt_mul_left hVa_lt_Vc (le_of_lt hV_r)
      -- c < b: work in V-scaled world — V*c = k+1/n ≤ V*a+1/n < V*a+2/n < V*b
      have hcb : c < b := by
        have hVc : (V : ℝ) * c = (k : ℝ) + 1 / n := by
          simp only [hc_def]; field_simp [hV_r.ne', hn_r.ne']
        have hVak : (V : ℝ) * a - k < 1 / n := by linarith [hkr]
        have h12n : (1 : ℝ) / n + 1 / n = 2 / n := by ring
        have hmul := mul_lt_mul_of_pos_right hlen hV_r
        have h2nVV : (2 : ℝ) / ((n : ℝ) * V) * V = 2 / n := by
          field_simp [hV_r.ne', hn_r.ne']
        have hVba : (1 : ℝ) / n < (V : ℝ) * (b - a) := by
          linarith [mul_comm (b - a) (V : ℝ), h2nVV, h12n, div_pos one_pos hn_r]
        have hVab : (V : ℝ) * b = (V : ℝ) * a + V * (b - a) := by ring
        exact lt_of_mul_lt_mul_left
          (by linarith [hVc, hVak, hVba, hVab, hk_le] : (V : ℝ) * c < V * b)
          (le_of_lt hV_r)
      exact ⟨c, ⟨le_of_lt hca, le_of_lt hcb⟩, boundary_good k⟩
    · -- Case B: 1 - Int.fract(V*a) < 1/n, i.e., fract(V*a) > 1 - 1/n.
      -- k = ⌊V*a⌋ + 1; a ∈ (k/V - 1/(nV), k/V); right boundary c = k/V + 1/(nV) is in (a,b).
      set k := ⌊(V : ℝ) * a⌋ + 1 with hk_def
      -- hkr: real cast of k = ↑⌊V*a⌋ + 1; used in hk_lt and hk_lo
      have hkr : (k : ℝ) = ↑⌊(V : ℝ) * a⌋ + 1 := by exact_mod_cast hk_def
      have hk_lt : (V : ℝ) * a < (k : ℝ) := by
        linarith [Int.lt_floor_add_one ((V : ℝ) * a), hkr]
      -- h_frac says 1 - fract(V*a) < 1/n, i.e., k - V*a < 1/n, i.e., V*a > k - 1/n
      have hk_lo : (k : ℝ) - 1 / (n : ℝ) < (V : ℝ) * a := by
        rw [Int.fract] at h_frac; push_cast at h_frac
        linarith [hkr]
      set c := (k : ℝ) / (V : ℝ) + 1 / ((n : ℝ) * (V : ℝ)) with hc_def
      -- a < c: V*a < k < k + 1/n = V*c, so V*a < V*c, hence a < c
      have hca : a < c := by
        have hVc : (V : ℝ) * c = (k : ℝ) + 1 / (n : ℝ) := by
          simp only [hc_def]; field_simp [hV_r.ne', hn_r.ne']
        have hVa_lt_Vc : (V : ℝ) * a < (V : ℝ) * c := by
          rw [hVc]; linarith [hk_lt, div_pos one_pos hn_r]
        exact lt_of_mul_lt_mul_left hVa_lt_Vc (le_of_lt hV_r)
      -- c < b: k/V - 1/(nV) < a and c = (k/V - 1/(nV)) + 2/(nV) < a + (b-a) = b
      have hcb : c < b := by
        have heq : (V : ℝ) * ((k : ℝ) / V - 1 / (n * V)) = (k : ℝ) - 1 / n := by
          field_simp [hV_r.ne', hn_r.ne']
        have ha_lb : (k : ℝ) / (V : ℝ) - 1 / ((n : ℝ) * (V : ℝ)) < a := by
          have hmul : (V : ℝ) * ((k : ℝ) / V - 1 / (n * V)) < (V : ℝ) * a := by
            linarith [heq, hk_lo]
          exact lt_of_mul_lt_mul_left hmul (le_of_lt hV_r)
        -- spread: c = (k/V - 1/(nV)) + 2/(nV), so c - a < 2/(nV) < b - a
        have h2nV : (1 : ℝ) / ((n : ℝ) * V) + 1 / (n * V) = 2 / (n * V) := by ring
        linarith [ha_lb, hc_def, h2nV, hlen]
      exact ⟨c, ⟨le_of_lt hca, le_of_lt hcb⟩, boundary_good k⟩

/-- **Theorem 7.1** (Large Speed Ratio).

    Suppose `V > (n-1) * v_{n-2}` (where `v_{n-2}` is the second-largest slow runner's speed).
    Then under `H(n-1)`, there exists `t₀ ∈ G_s ∩ G_V`. -/
theorem theorem71_LargeSR
    (n : ℕ) (hn : 3 ≤ n)
    (slowSpeeds : Fin (n - 2) → ℕ)
    (V : ℕ)
    (hpos : ∀ i, 0 < slowSpeeds i)
    (hmono : StrictMono slowSpeeds)
    (hV_large : (n - 1) * slowSpeeds ⟨n - 3, by omega⟩ < V)
    (Hn : H n) :
    ∃ t₀ : ℝ,
      (∀ i, circDist ((slowSpeeds i : ℝ) * t₀) ≥ (1 : ℝ) / n) ∧
      circDist ((V : ℝ) * t₀) ≥ (1 : ℝ) / n := by
  -- Step 1: Apply Lemma 4.1 to get a good neighbourhood for the slow runners.
  have hpm := @lemma41_positive_measure (n - 2) n hn rfl slowSpeeds hpos hmono Hn
  obtain ⟨t_star, δ, hδ_pos, hδ_lb, hI_sub, _⟩ := hpm
  -- Basic positivity
  have hV_pos : 0 < V := by
    have h := Nat.mul_pos (show 0 < n - 1 by omega) (hpos ⟨n - 3, by omega⟩)
    omega
  have hn_1 : 1 < n := by omega
  -- Reconcile Fin indices: k=n-2 so speeds ⟨k-1, _⟩ = slowSpeeds ⟨n-2-1, _⟩ = slowSpeeds ⟨n-3, _⟩
  have h_idx : slowSpeeds ⟨n - 2 - 1, by omega⟩ = slowSpeeds ⟨n - 3, by omega⟩ := by
    simp_rw [show n - 2 - 1 = n - 3 from by omega]
  rw [h_idx] at hδ_lb
  -- hδ_lb : lemma41_delta n (slowSpeeds ⟨n-3, _⟩) ≤ δ
  -- Step 2: The interval [t** - δ, t** + δ] has length 2δ > 2/(n*V).
  have hlen : 2 / ((n : ℝ) * (V : ℝ)) < (t_star + δ) - (t_star - δ) := by
    rw [show (t_star + δ) - (t_star - δ) = 2 * δ from by ring]
    have hn_r : (0 : ℝ) < n := by exact_mod_cast show 0 < n by omega
    have hV_r : (0 : ℝ) < (V : ℝ) := by exact_mod_cast hV_pos
    have hn1_r : (0 : ℝ) < (n : ℝ) - 1 := by
      have h2n : (2 : ℝ) ≤ n := by exact_mod_cast show 2 ≤ n by omega
      linarith
    have hvmax_r : (0 : ℝ) < (slowSpeeds ⟨n - 3, by omega⟩ : ℝ) := by
      exact_mod_cast hpos ⟨n - 3, by omega⟩
    have h_large : ((n - 1 : ℕ) : ℝ) * (slowSpeeds ⟨n - 3, by omega⟩ : ℝ) < V := by
      exact_mod_cast hV_large
    have h_n1 : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
      push_cast [show 1 ≤ n from by omega]; ring
    rw [h_n1] at h_large
    -- 1/(n*V) < 1/(n*(n-1)*vmax) = lemma41_delta n vmax ≤ δ → 2/(n*V) < 2*δ
    have h_lt : 1 / ((n : ℝ) * V) < lemma41_delta n (slowSpeeds ⟨n - 3, by omega⟩) := by
      simp only [lemma41_delta]
      exact one_div_lt_one_div_of_lt
        (mul_pos (mul_pos hn_r hn1_r) hvmax_r)
        (by nlinarith)
    have h_combined : 1 / ((n : ℝ) * V) < δ := lt_of_lt_of_le h_lt hδ_lb
    have h_ring : 2 / ((n : ℝ) * V) = 2 * (1 / ((n : ℝ) * V)) := by ring
    linarith
  -- Step 3: The geometric lemma finds t₀ ∈ [t**-δ, t**+δ] ∩ goodSet V n.
  have hesc := interval_escapes_bad V n hV_pos hn_1 (t_star - δ) (t_star + δ) hlen
  obtain ⟨t₀, ht₀⟩ := hesc
  -- Step 4: Assemble the conclusion.
  refine ⟨t₀, ?_, ?_⟩
  · -- Slow runners: t₀ ∈ Icc ⊆ jointGoodSet slowSpeeds n → circDist ≥ 1/n for each.
    have ht₀_slow : t₀ ∈ jointGoodSet slowSpeeds n := hI_sub ht₀.1
    intro i
    simp only [jointGoodSet, Set.mem_iInter, goodSet, Set.mem_setOf_eq] at ht₀_slow
    exact ht₀_slow i
  · -- Fast runner V: t₀ ∈ goodSet V n from interval_escapes_bad.
    have ht₀_goodV := ht₀.2
    simp only [goodSet, Set.mem_setOf_eq] at ht₀_goodV
    exact ht₀_goodV

/-! ## §7  Boundary remark -/

-- At the boundary `V = (n-1) * v_{n-2}`, the LR argument breaks (equal widths).
-- This case falls into the hard case (§9) and is handled by Theorems 10.1 or 11.1.
-- No separate proof is needed here.
