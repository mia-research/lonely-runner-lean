import LonelyRunner.LRC.Defs

/-!
# Lemma 4.1 — Positive-Measure Lemma

Source: `lrc_proof_v11_draft.md` §4.

**Statement:** If LRC holds for `n-1` runners (i.e. `H(n-1)` holds), then the
simultaneous good set `G_s` for the `n-2` slow runners has positive Lebesgue measure.
Moreover, it contains a non-degenerate closed interval.

**Proof sketch:**
1. `H(n-1)` gives `t**` with `circDist(v_j * t**) ≥ 1/(n-1)` for all slow `j`.
2. Since `1/(n-1) > 1/n`, `t**` lies in the open interior of every `goodSet v_j n`.
3. By Lipschitz continuity of `t ↦ circDist(v_j * t)` (Lipschitz constant `v_j`),
   a neighbourhood `(t** - δ, t** + δ)` is contained in each `goodSet v_j n`.
4. Taking `δ = 1 / (n * (n-1) * v_{n-2})` yields the explicit bound.

This lemma converts the bare existence given by the inductive hypothesis into
the positive-measure input that Weyl equidistribution (Theorem 5.2) requires.
-/


open MeasureTheory Set

/-! ## §4  Positive-Measure Lemma -/

-- Note: `circDist_lipschitz : LipschitzWith 1 circDist` is proved in Defs.lean.
-- Here we record that the composition `t ↦ circDist(v*t)` satisfies the key
-- distance bound used in Lemma 4.1's neighbourhood argument.

/-- The neighbourhood radius from Lemma 4.1's explicit bound (★).
    Written with explicit ℝ coercions to avoid elaboration through ℤ. -/
noncomputable def lemma41_delta (n : ℕ) (vmax : ℕ) : ℝ :=
  1 / ((n : ℝ) * ((n : ℝ) - 1) * (vmax : ℝ))

/-- **Lemma 4.1** (Positive-Measure Lemma).

    Given `H(n-1)` (LRC for n-1 runners), and slow runners `v₁ < ... < v_{n-2}`,
    the simultaneous good set `G_s = ⋂_j goodSet v_j n` has positive measure.
    Specifically, it contains the closed interval `[t** - δ, t** + δ]`
    where `δ = 1 / (n * (n-1) * v_{n-2})`. -/
theorem lemma41_positive_measure
    {k n : ℕ} (hn : 3 ≤ n) (hk : k = n - 2)
    (speeds : Fin k → ℕ)
    (hpos : ∀ i, 0 < speeds i)
    (hmono : StrictMono speeds)
    (Hn : H n) :
    ∃ (t_star : ℝ) (δ : ℝ), 0 < δ ∧
      lemma41_delta n (speeds ⟨k - 1, by omega⟩) ≤ δ ∧
      Icc (t_star - δ) (t_star + δ) ⊆ jointGoodSet speeds n ∧
      0 < MeasureTheory.volume (jointGoodSet speeds n) := by
  -- Step 1: intLRC (n-1) from H n (since n-1 < n).
  -- intLRC (n-1) gives a good time for Fin (n-2) = Fin k runners at threshold 1/(n-1).
  -- NORMALISATION: intLRC requires Finset.gcd = 1; we normalise by dividing by the gcd
  -- and scale the witness by 1/d.
  have Hn1_applied : ∃ t : ℝ, ∀ i : Fin k,
      circDist ((speeds i : ℝ) * t) ≥ (1 : ℝ) / ((n - 1 : ℕ) : ℝ) := by
    have hLRC : intLRC (n - 1) := Hn (n - 1) (by omega)
    have h_eq : n - 1 - 1 = k := by omega
    set slowK : Fin (n - 1 - 1) → ℕ := speeds ∘ Fin.cast h_eq with hslowK_def
    have hslowK_pos : ∀ i, 0 < slowK i := fun i => hpos (Fin.cast h_eq i)
    set d : ℕ := Finset.gcd Finset.univ slowK with hd_def
    have hd_pos : 0 < d := by
      rw [hd_def, Nat.pos_iff_ne_zero, Finset.gcd_ne_zero_iff]
      exact ⟨⟨0, by omega⟩, Finset.mem_univ _, (hslowK_pos _).ne'⟩
    have hd_dvd : ∀ i, d ∣ slowK i := fun i => Finset.gcd_dvd (Finset.mem_univ i)
    let normalSpeeds : Fin (n - 1 - 1) → ℕ := fun i => slowK i / d
    have hnorm_mul : ∀ i, d * normalSpeeds i = slowK i :=
      fun i => Nat.mul_div_cancel' (hd_dvd i)
    have hnorm_pos : ∀ i, 0 < normalSpeeds i := fun i =>
      Nat.div_pos (Nat.le_of_dvd (hslowK_pos i) (hd_dvd i)) hd_pos
    have hnorm_mono : StrictMono normalSpeeds := by
      intro a b hab
      have h1 : slowK a < slowK b := hmono hab
      have h2 : d * normalSpeeds a < d * normalSpeeds b := by
        rw [hnorm_mul, hnorm_mul]; exact h1
      exact Nat.lt_of_mul_lt_mul_left h2
    have hnorm_gcd : Finset.gcd Finset.univ normalSpeeds = 1 :=
      Finset.gcd_div_eq_one (Finset.mem_univ (⟨0, by omega⟩ : Fin (n - 1 - 1)))
        (hslowK_pos _).ne'
    obtain ⟨t, ht⟩ := hLRC normalSpeeds hnorm_mono hnorm_pos hnorm_gcd
    refine ⟨t / d, fun i => ?_⟩
    set i' : Fin (n - 1 - 1) := Fin.cast h_eq.symm i with hi'_def
    have h_cast : Fin.cast h_eq i' = i := Fin.ext rfl
    have hs : slowK i' = speeds i := by
      show speeds (Fin.cast h_eq i') = speeds i
      rw [h_cast]
    have h_speeds : (speeds i : ℝ) = (d : ℝ) * (normalSpeeds i' : ℝ) := by
      have hn : d * normalSpeeds i' = slowK i' := hnorm_mul i'
      have : (speeds i : ℕ) = d * normalSpeeds i' := by rw [← hs]; exact hn.symm
      exact_mod_cast this
    have hd_ne : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hd_pos.ne'
    have h_mul : (speeds i : ℝ) * (t / d) = (normalSpeeds i' : ℝ) * t := by
      rw [h_speeds]; field_simp
    rw [h_mul]; exact ht i'
  obtain ⟨t_star, ht_star⟩ := Hn1_applied
  -- Step 2: t** is in the strict interior of each goodSet speeds_i n.
  have h_strict : ∀ i : Fin k,
      circDist ((speeds i : ℝ) * t_star) > (1 : ℝ) / (n : ℝ) := by
    intro i
    have h1 : circDist ((speeds i : ℝ) * t_star) ≥ 1 / ((n - 1 : ℕ) : ℝ) := ht_star i
    have h2 : (1 : ℝ) / ((n - 1 : ℕ) : ℝ) > 1 / (n : ℝ) := by
      -- ((n-1 : ℕ) : ℝ) = (n : ℝ) - 1 when 1 ≤ n.
      have h_cast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
        push_cast [show 1 ≤ n from by omega]; ring
      have hn1_pos : (0 : ℝ) < (n : ℝ) - 1 := by
        have := show (2 : ℝ) ≤ n by exact_mod_cast show 2 ≤ n by omega
        linarith
      rw [h_cast, gt_iff_lt]
      -- 1/(n : ℝ) < 1/((n : ℝ) - 1) since 0 < n-1 < n.
      exact one_div_lt_one_div_of_lt hn1_pos (by linarith)
    linarith
  -- Step 3: Lipschitz → explicit neighbourhood.
  -- For each i: circDist(v_i * t) > 1/n for t in (t** - δ_i, t** + δ_i)
  -- where δ_i = (circDist(v_i * t**) - 1/n) / v_i ≥ (1/(n-1) - 1/n) / v_i
  --           = 1/(n(n-1)v_i).
  -- Taking minimum over i gives δ ≥ 1/(n(n-1) * v_{n-2}).
  let vmax : ℕ := if k = 0 then 1 else speeds ⟨k - 1, by omega⟩
  let δ := lemma41_delta n vmax
  -- Common positivity facts reused across goals
  have hn_r   : (0 : ℝ) < n := by exact_mod_cast show 0 < n by omega
  have hn1_r  : (0 : ℝ) < (n : ℝ) - 1 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast show 2 ≤ n by omega
    linarith
  have hvmax_pos : 0 < vmax := by
    simp only [vmax]; split_ifs with hk0
    · exact Nat.one_pos
    · exact hpos ⟨k - 1, by omega⟩
  have hvmax_r : (0 : ℝ) < vmax := by exact_mod_cast hvmax_pos
  have hδ_pos : 0 < δ := by
    dsimp only [lemma41_delta]
    exact div_pos one_pos (mul_pos (mul_pos hn_r hn1_r) hvmax_r)
  -- Key arithmetic: 1/(n-1) - vmax * δ = 1/n
  have h_arith : 1 / ((n : ℝ) - 1) - (vmax : ℝ) * δ = 1 / (n : ℝ) := by
    simp only [lemma41_delta, δ]
    field_simp [hn_r.ne', hn1_r.ne', hvmax_r.ne']
  -- Interval containment: [t* - δ, t* + δ] ⊆ jointGoodSet speeds n
  have h_sub : Set.Icc (t_star - δ) (t_star + δ) ⊆ jointGoodSet speeds n := by
    intro t ht
    simp only [jointGoodSet, Set.mem_iInter, goodSet, Set.mem_setOf_eq]
    intro i
    -- |t - t*| ≤ δ
    have ht_abs : |t - t_star| ≤ δ := by
      rw [abs_le]; exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
    -- speeds i ≤ vmax (by strict monotonicity of speeds)
    have hvi_le : speeds i ≤ vmax := by
      simp only [vmax]
      split_ifs with hk0
      · exact absurd i.isLt (by omega)
      · have hi := i.isLt
        apply hmono.monotone
        -- i ≤ ⟨k-1, _⟩ as Fin k is definitionally i.val ≤ k-1
        change i.val ≤ k - 1
        omega
    -- Lipschitz: dist(circDist(v*t), circDist(v*t*)) ≤ v * |t - t*| ≤ v * δ
    have h_combined :
        dist (circDist ((speeds i : ℝ) * t)) (circDist ((speeds i : ℝ) * t_star)) ≤
        (speeds i : ℝ) * δ := by
      -- Step 1: 1-Lipschitz of circDist gives dist(circDist a, circDist b) ≤ dist a b
      have h1 : dist (circDist ((speeds i : ℝ) * t)) (circDist ((speeds i : ℝ) * t_star)) ≤
                dist ((speeds i : ℝ) * t) ((speeds i : ℝ) * t_star) := by
        have := circDist_lipschitz.dist_le_mul
                   ((speeds i : ℝ) * t) ((speeds i : ℝ) * t_star)
        simpa [NNReal.coe_one, one_mul] using this
      -- Step 2: dist(v*t, v*t*) = v * |t - t*| ≤ v * δ
      have h2 : dist ((speeds i : ℝ) * t) ((speeds i : ℝ) * t_star) ≤ (speeds i : ℝ) * δ := by
        rw [Real.dist_eq,
            show (speeds i : ℝ) * t - (speeds i : ℝ) * t_star =
                 (speeds i : ℝ) * (t - t_star) from by ring,
            abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
        exact mul_le_mul_of_nonneg_left ht_abs (Nat.cast_nonneg _)
      exact h1.trans h2
    -- Extract lower bound: circDist(v*t) ≥ circDist(v*t*) - v * δ
    have h_lower : circDist ((speeds i : ℝ) * t) ≥
                   circDist ((speeds i : ℝ) * t_star) - (speeds i : ℝ) * δ := by
      have habs : |circDist ((speeds i : ℝ) * t) - circDist ((speeds i : ℝ) * t_star)| ≤
                  (speeds i : ℝ) * δ := by rwa [← Real.dist_eq]
      linarith [(abs_le.mp habs).1]
    -- circDist(v*t*) ≥ 1/(n-1)
    have h_tstar : circDist ((speeds i : ℝ) * t_star) ≥ 1 / ((n : ℝ) - 1) := by
      have hi := ht_star i
      have h_cast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
        push_cast [show 1 ≤ n from by omega]; ring
      rwa [ge_iff_le, ← h_cast]
    -- v_i * δ ≤ vmax * δ
    have hvi_delta : (speeds i : ℝ) * δ ≤ (vmax : ℝ) * δ :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hvi_le) (le_of_lt hδ_pos)
    -- Combine: circDist(v*t) ≥ 1/(n-1) - vmax*δ = 1/n
    linarith [h_lower, h_tstar, hvi_delta, h_arith]
  have hδ_lb : lemma41_delta n (speeds ⟨k - 1, by omega⟩) ≤ δ := by
    have hk_ne : k ≠ 0 := by omega
    change lemma41_delta n (speeds ⟨k - 1, by omega⟩) ≤
           lemma41_delta n (if k = 0 then 1 else speeds ⟨k - 1, by omega⟩)
    simp [hk_ne]
  refine ⟨t_star, δ, hδ_pos, hδ_lb, h_sub, ?_⟩
  -- μ(jointGoodSet) > 0 (from interval containment + δ > 0)
  apply lt_of_lt_of_le _ (MeasureTheory.measure_mono h_sub)
  rw [Real.volume_Icc]
  apply ENNReal.ofReal_pos.mpr
  linarith

/-- Quantitative form: the measure of `jointGoodSet` is at least `2 * δ`. -/
theorem lemma41_measure_lower_bound
    {k n : ℕ} (hn : 3 ≤ n) (hk : k = n - 2)
    (speeds : Fin k → ℕ)
    (hpos : ∀ i, 0 < speeds i)
    (hmono : StrictMono speeds)
    (Hn : H n) :
    MeasureTheory.volume (jointGoodSet speeds n) ≥
      ENNReal.ofReal (2 * lemma41_delta n (speeds ⟨k - 1, by omega⟩)) := by
  obtain ⟨t_star, δ, hδ_pos, hδ_lb, h_sub, _⟩ :=
    lemma41_positive_measure hn hk speeds hpos hmono Hn
  calc ENNReal.ofReal (2 * lemma41_delta n (speeds ⟨k - 1, by omega⟩))
      ≤ ENNReal.ofReal (2 * δ) := by
        apply ENNReal.ofReal_le_ofReal; linarith
    _ = MeasureTheory.volume (Set.Icc (t_star - δ) (t_star + δ)) := by
        rw [Real.volume_Icc]; congr 1; ring
    _ ≤ MeasureTheory.volume (jointGoodSet speeds n) :=
        MeasureTheory.measure_mono h_sub
