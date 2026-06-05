import LonelyRunner.LRC.Defs
import LonelyRunner.LRC.Theorem61_BSR
import LonelyRunner.LRC.Theorem71_LargeSR
import LonelyRunner.LRC.Theorem101_DI
import LonelyRunner.LRC.Theorem111_ModDI

/-!
# Theorem 12.1 — Main Theorem: The Lonely Runner Conjecture

Source: `lrc_proof_v11_draft.md` §12.

**Statement:** For all `n ≥ 3` and any `n-1` distinct positive real speeds, there
exists `t ≥ 0` such that every runner is at distance ≥ `1/n` from the origin.

**Proof structure:**
1. By §2.2, reduce to integer speeds with gcd = 1.
2. Strong induction on `n`.
3. Base case `n = 3`: BSR or LR (§3.1).
4. Inductive step: exactly one of BSR / LR / Hard Case (Lemma 9.1).
   - BSR: Theorem 6.1. ✓
   - LR: Theorem 7.1. ✓
   - Hard case: exactly one of DI / DI-MOD (Lemma 9.2).
     - DI: Theorem 10.1. ✓
     - DI-MOD: Theorem 11.1. ✓

**Assembly difficulty:** MODERATE — the induction structure is clear, but
connecting all the sub-theorems with the correct hypotheses requires care.
-/


open MeasureTheory Set

/-! ## §9.1  Case Exhaustion (Lemma 9.1) -/

/-- **Lemma 9.1** (Case Exhaustion).
    For `n ≥ 3` and integer speeds, exactly one of BSR, LR, Hard Case holds. -/
theorem lemma91_case_exhaustion (n v₁ V v_n2 : ℕ) (hn : 3 ≤ n)
    (hv1_le_vn2 : v₁ ≤ v_n2) (hvn2_le_V : v_n2 ≤ V) :
    (V ≤ (n - 1) * v₁) ∨                          -- BSR
    ((n - 1) * v_n2 < V) ∨                         -- LR
    ((n - 1) * v₁ < V ∧ V ≤ (n - 1) * v_n2) := by  -- Hard case
  by_cases h1 : V ≤ (n - 1) * v₁
  · left; exact h1
  · push_neg at h1
    by_cases h2 : (n - 1) * v_n2 < V
    · right; left; exact h2
    · push_neg at h2
      right; right; exact ⟨h1, h2⟩

/-! ## §9.2  Hard-case partition (Lemma 9.2) -/

/-- **Lemma 9.2** (Hard-Case Partition).
    For any prime `p` and lcm `L`, either `gcd(p, L) = 1` (DI case) or `p ∣ L` (DI-MOD case). -/
theorem lemma92_DI_partition (p L : ℕ) (hp : Nat.Prime p) :
    Nat.Coprime p L ∨ p ∣ L := by
  rcases Nat.Prime.eq_one_or_self_of_dvd hp (Nat.gcd p L) (Nat.gcd_dvd_left p L) with h | h
  · left; exact h    -- Nat.Coprime p L = (Nat.gcd p L = 1), so h closes directly.
  · right; rw [← h]; exact Nat.gcd_dvd_right p L

/-! ## §12  Main Theorem -/

/-- **Theorem 12.1** (Lonely Runner Conjecture).
    `LRC` holds for all `n ≥ 3` as `intLRC n`. -/
theorem theorem121_LRC : ∀ n : ℕ, 3 ≤ n → intLRC n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih => ?_
  intro hn
  -- Build the strong induction hypothesis H n from ih
  have Hn : H n := fun m hm => by
    by_cases hm3 : 3 ≤ m
    · exact ih m hm hm3
    · -- m < 3: base cases for intLRC m
      push_neg at hm3
      intro speeds _ hpos _
      interval_cases m
      · -- m = 0: speeds : Fin 0 → ℕ; vacuously true
        exact ⟨0, fun i => i.elim0⟩
      · -- m = 1: speeds : Fin 0 → ℕ; vacuously true
        exact ⟨0, fun i => i.elim0⟩
      · -- m = 2: speeds : Fin 1 → ℕ; one runner v > 0; use t = 1/(2v)
        refine ⟨1 / (2 * (speeds ⟨0, by omega⟩ : ℝ)), fun i => ?_⟩
        have hi : i = ⟨0, by omega⟩ := Fin.ext (by omega)
        subst hi
        have hv : (0 : ℝ) < speeds ⟨0, by omega⟩ := by exact_mod_cast hpos ⟨0, by omega⟩
        rw [show (speeds ⟨0, by omega⟩ : ℝ) * (1 / (2 * speeds ⟨0, by omega⟩)) = 1 / 2
          from by field_simp [hv.ne']]
        have h_floor : ⌊(1 / 2 : ℝ)⌋ = (0 : ℤ) := Int.floor_eq_zero_iff.mpr (by norm_num)
        have h_frac : Int.fract (1 / 2 : ℝ) = 1 / 2 := by
          simp only [Int.fract, h_floor, Int.cast_zero, sub_zero]
        show circDist (1 / 2 : ℝ) ≥ (1 : ℝ) / 2
        unfold circDist; rw [h_frac]; norm_num
  -- Unfold intLRC n: given speeds, find t satisfying all runners
  intro speeds hmono hpos hgcd
  -- Decompose speeds into V (fastest) and slowSpeeds (remaining n-2 speeds)
  let V := speeds ⟨n - 2, by omega⟩
  let slowSpeeds : Fin (n - 2) → ℕ := fun i => speeds ⟨i.val, by omega⟩
  have hpos_slow : ∀ i, 0 < slowSpeeds i := fun i => hpos ⟨i.val, by omega⟩
  have hmono_slow : StrictMono slowSpeeds := by
    intro a b hab
    simp only [slowSpeeds]
    exact hmono (show (⟨a.val, by omega⟩ : Fin (n - 1)) < ⟨b.val, by omega⟩ from hab)
  -- Apply Lemma 9.1 case exhaustion: BSR / LR / Hard
  have hv1_vn2 : speeds ⟨0, by omega⟩ ≤ speeds ⟨n - 3, by omega⟩ :=
    hmono.monotone (show (⟨0, by omega⟩ : Fin (n - 1)) ≤ ⟨n - 3, by omega⟩ from by simp [Fin.le_iff_val_le_val])
  have hvn2_V : speeds ⟨n - 3, by omega⟩ ≤ V :=
    hmono.monotone (show (⟨n - 3, by omega⟩ : Fin (n - 1)) ≤ ⟨n - 2, by omega⟩ from by simp [Fin.le_iff_val_le_val]; omega)
  rcases lemma91_case_exhaustion n (speeds ⟨0, by omega⟩) V (speeds ⟨n - 3, by omega⟩) hn
           hv1_vn2 hvn2_V with hBSR | hLR | ⟨hV_hard_lo, hV_hard_hi⟩
  · -- BSR Case: V ≤ (n-1)*v₁ → explicit time t* = 1/(n*v₁)
    exact ⟨bsr_time n (speeds ⟨0, by omega⟩), theorem61_BSR n hn speeds hpos hmono hBSR⟩
  · -- LR Case: (n-1)*v_{n-2} < V → Theorem 7.1
    have hV_large : (n - 1) * slowSpeeds ⟨n - 3, by omega⟩ < V := hLR
    obtain ⟨t₀, ht₀_slow, ht₀_V⟩ :=
      theorem71_LargeSR n hn slowSpeeds V hpos_slow hmono_slow hV_large Hn
    refine ⟨t₀, fun i => ?_⟩
    rcases Nat.lt_or_eq_of_le (show i.val ≤ n - 2 by omega) with hi | hi
    · -- Slow runner: speeds i = slowSpeeds ⟨i.val, hi⟩
      have h := ht₀_slow ⟨i.val, hi⟩
      simp only [slowSpeeds] at h
      have heq : (speeds ⟨i.val, by omega⟩ : ℝ) = (speeds i : ℝ) := by
        congr 1
      rwa [heq] at h
    · -- Fast runner: speeds i = V
      have heq : (speeds i : ℝ) = (V : ℝ) := by
        norm_cast; congr 1; exact Fin.ext hi
      rw [heq]; exact ht₀_V
  · -- Hard Case: (n-1)*v₁ < V ≤ (n-1)*v_{n-2}
    -- hV_hard_lo : (n-1) * speeds ⟨0, _⟩ < V
    -- hV_hard_hi : V ≤ (n-1) * speeds ⟨n-3, _⟩
    -- V ≥ 2 (from hard-case lower bound)
    have hV_pos : 0 < V :=
      Nat.lt_of_lt_of_le (Nat.mul_pos (by omega) (hpos ⟨0, by omega⟩)) (le_of_lt hV_hard_lo)
    have hV_ne1 : 1 < V := by
      have h := Nat.mul_pos (show 0 < n - 1 by omega) (hpos ⟨0, by omega⟩)
      omega
    -- p = smallest prime factor of V, q = V / p
    let p := V.minFac
    have hp : Nat.Prime p := Nat.minFac_prime hV_ne1.ne'
    have hpV : p ∣ V := Nat.minFac_dvd V
    let q := V / p
    have hpq : V = p * q := (Nat.mul_div_cancel' hpV).symm
    -- Case split: DI (gcd(p, lcm(slowSpeeds)) = 1) vs DI-MOD (p | lcm)
    let L := Finset.lcm Finset.univ slowSpeeds
    rcases lemma92_DI_partition p L hp with hDI | hDIMOD
    · -- DI case: Nat.Coprime p (lcm of slow runners) → Theorem 10.1
      -- hV_hard_lo/hi are definitionally equal after unfolding slowSpeeds
      have hV_lo' : (n - 1) * slowSpeeds ⟨0, by omega⟩ < V := hV_hard_lo
      have hV_hi' : V ≤ (n - 1) * slowSpeeds ⟨n - 3, by omega⟩ := hV_hard_hi
      obtain ⟨t₀, ht₀_slow, ht₀_V⟩ :=
        theorem101_DI n hn slowSpeeds V hpos_slow hmono_slow
          hV_lo' hV_hi' p q hp hpq hDI Hn
      refine ⟨t₀, fun i => ?_⟩
      rcases Nat.lt_or_eq_of_le (show i.val ≤ n - 2 from by omega) with hi | hi
      · -- Slow runner: i.val < n-2
        have h := ht₀_slow ⟨i.val, hi⟩
        simp only [slowSpeeds] at h
        exact h
      · -- Fast runner: i.val = n-2, speeds i = V
        have hVi : speeds i = V := by
          have : speeds i = speeds ⟨n - 2, by omega⟩ :=
            congr_arg speeds (Fin.ext hi)
          exact this
        rw [show (speeds i : ℝ) = (V : ℝ) from by exact_mod_cast hVi]
        exact ht₀_V
    · -- DI-MOD case: p | L where L = Finset.lcm Finset.univ slowSpeeds → Theorem 11.1
      -- **Construction overview:**
      -- 1. h_some_not_p from `hgcd + hpV + hp.prime` (if all speeds were divisible by p,
      --    then p | gcd = 1, contradiction).
      -- 2. r := #{i | p ∣ slowSpeeds i}; r ≥ 1 from hDIMOD via prime-dvd-lcm helper.
      -- 3. r ≤ n - 3 via `lemma93_r_le` from h_some_not_p.
      -- 4. pDiv, indRun, w, hindSpeeds from Finset.orderEmbOfFin on filter and complement.
      -- 5. Hn1r := H(n-r), Hr3 := H(r+3) from Hn.
      -- 6. Apply theorem111_ModDI, map result back to speeds.
      -- Step 1: derive h_some_not_p
      have h_some_not_p : ∃ i : Fin (n - 2), ¬(p ∣ slowSpeeds i) := by
        by_contra hcon
        push_neg at hcon
        -- ∀ i : Fin (n-2), p ∣ slowSpeeds i; also p ∣ V (hpV); so p ∣ all speeds.
        have hp_dvd_all : ∀ i : Fin (n - 1), p ∣ speeds i := by
          intro i
          rcases Nat.lt_or_eq_of_le (show i.val ≤ n - 2 from by omega) with hi | hi
          · -- slow runner: speeds i = slowSpeeds ⟨i.val, hi⟩
            have h := hcon ⟨i.val, hi⟩
            show p ∣ speeds i
            have heq : (slowSpeeds ⟨i.val, hi⟩ : ℕ) = speeds i := by
              show speeds ⟨i.val, by omega⟩ = speeds i
              congr 1
            rw [← heq]; exact h
          · -- fast runner: speeds i = V
            have : speeds i = V := by
              show speeds i = speeds ⟨n - 2, by omega⟩
              congr 1; exact Fin.ext hi
            rw [this]; exact hpV
        have hp_dvd_gcd : p ∣ Finset.gcd Finset.univ speeds :=
          Finset.dvd_gcd (fun i _ => hp_dvd_all i)
        rw [hgcd] at hp_dvd_gcd
        exact absurd (Nat.dvd_one.mp hp_dvd_gcd) hp.one_lt.ne'
      -- Step 2: build pDivSet, r, r ≥ 1.
      let pDivSet : Finset (Fin (n - 2)) := Finset.univ.filter (fun i => p ∣ slowSpeeds i)
      let r : ℕ := pDivSet.card
      have hr_def : r = pDivSet.card := rfl
      have h_p_dvd_some : 0 < r := by
        rw [hr_def, Finset.card_pos]
        -- hDIMOD : p ∣ Finset.lcm Finset.univ slowSpeeds. Apply prime-dvd-lcm helper.
        have ⟨x, _, hxd⟩ : ∃ x ∈ (Finset.univ : Finset (Fin (n - 2))), p ∣ slowSpeeds x := by
          have h : p ∣ Finset.univ.lcm slowSpeeds := hDIMOD
          clear_value L
          -- Inline induction on (Finset.univ : Finset (Fin (n - 2))).
          generalize hS : (Finset.univ : Finset (Fin (n - 2))) = S at h
          clear hS
          induction S using Finset.induction_on with
          | empty =>
            simp only [Finset.lcm_empty] at h
            exact absurd (Nat.dvd_one.mp h) hp.one_lt.ne'
          | @insert a s' ha' ih =>
            rw [Finset.lcm_insert] at h
            have h_mul : (slowSpeeds a) * (s'.lcm slowSpeeds) ∣ _ := dvd_refl _
            have h_lcm_dvd : Nat.lcm (slowSpeeds a) (s'.lcm slowSpeeds)
                              ∣ slowSpeeds a * s'.lcm slowSpeeds :=
              Nat.lcm_dvd_mul _ _
            have h_p_mul : p ∣ slowSpeeds a * s'.lcm slowSpeeds := dvd_trans h h_lcm_dvd
            rcases hp.dvd_or_dvd h_p_mul with h1 | h2
            · exact ⟨a, Finset.mem_insert.mpr (Or.inl rfl), h1⟩
            · obtain ⟨x, hxs, hxd⟩ := ih h2
              exact ⟨x, Finset.mem_insert.mpr (Or.inr hxs), hxd⟩
        exact ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxd⟩⟩
      -- Step 3: r ≤ n - 3 via lemma93_r_le.
      have hr_le : r ≤ n - 3 :=
        lemma93_r_le n hn slowSpeeds p hp r hr_def h_p_dvd_some h_some_not_p
      -- Step 4: pDiv, indRun via orderEmbOfFin.
      let pDiv : Fin r → Fin (n - 2) := fun k =>
        pDivSet.orderEmbOfFin hr_def.symm k
      have hpDiv_dvd : ∀ k, p ∣ slowSpeeds (pDiv k) := fun k => by
        have hk_mem : pDiv k ∈ pDivSet := pDivSet.orderEmbOfFin_mem hr_def.symm k
        exact (Finset.mem_filter.mp hk_mem).2
      -- Complement: independent runners.
      let indSet : Finset (Fin (n - 2)) := pDivSet ᶜ
      have hindSet_card : indSet.card = n - 2 - r := by
        simp only [indSet, Finset.card_compl, Fintype.card_fin]
        rfl
      let indRun : Fin (n - 2 - r) → Fin (n - 2) := fun j =>
        indSet.orderEmbOfFin hindSet_card j
      have hind_not_dvd : ∀ j, ¬(p ∣ slowSpeeds (indRun j)) := fun j => by
        have hj_mem : indRun j ∈ indSet := indSet.orderEmbOfFin_mem hindSet_card j
        simp only [indSet, Finset.mem_compl] at hj_mem
        intro hd
        exact hj_mem (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hd⟩)
      have hind_part : ∀ i : Fin (n - 2),
          (∃ k, pDiv k = i) ∨ (∃ j, indRun j = i) := fun i => by
        by_cases hi : i ∈ pDivSet
        · left
          have hi_range : i ∈ Set.range (pDivSet.orderEmbOfFin hr_def.symm) := by
            rw [pDivSet.range_orderEmbOfFin hr_def.symm]; exact hi
          obtain ⟨k, hk⟩ := hi_range
          exact ⟨k, hk⟩
        · right
          have hi' : i ∈ indSet := Finset.mem_compl.mpr hi
          have hi_range : i ∈ Set.range (indSet.orderEmbOfFin hindSet_card) := by
            rw [indSet.range_orderEmbOfFin hindSet_card]; exact hi'
          obtain ⟨j, hj⟩ := hi_range
          exact ⟨j, hj⟩
      -- Step 5: w (reduced speeds), hindSpeeds.
      let w : Fin r → ℕ := fun k => slowSpeeds (pDiv k) / p
      have hw_def : ∀ k, slowSpeeds (pDiv k) = p * w k := fun k => by
        simp only [w]
        exact (Nat.mul_div_cancel' (hpDiv_dvd k)).symm
      have hmono_w : StrictMono w := by
        intro a b hab
        simp only [w]
        have hpDiv_mono : StrictMono pDiv := fun a b hab => by
          simp only [pDiv]
          exact (pDivSet.orderEmbOfFin hr_def.symm).strictMono hab
        have hs_lt : slowSpeeds (pDiv a) < slowSpeeds (pDiv b) := hmono_slow (hpDiv_mono hab)
        have hp_pos : 0 < p := hp.pos
        have h_div_lt : slowSpeeds (pDiv a) / p < slowSpeeds (pDiv b) / p := by
          rw [Nat.div_lt_iff_lt_mul hp_pos]
          calc slowSpeeds (pDiv a) < slowSpeeds (pDiv b) := hs_lt
            _ = p * (slowSpeeds (pDiv b) / p) := hw_def b ▸ rfl
            _ = slowSpeeds (pDiv b) / p * p := Nat.mul_comm _ _
        exact h_div_lt
      have hwq : ∀ k, w k ≠ q := fun k hk => by
        -- If w k = q, then slowSpeeds (pDiv k) = p * w k = p * q = V. But slowSpeeds < V.
        have hs_eq : slowSpeeds (pDiv k) = V := by
          rw [hw_def k, hk, ← hpq]
        have hs_lt_V : slowSpeeds (pDiv k) < V := by
          have h_mono : StrictMono speeds := hmono
          have : speeds ⟨(pDiv k).val, by omega⟩ < speeds ⟨n - 2, by omega⟩ :=
            h_mono (show (⟨(pDiv k).val, by omega⟩ : Fin (n - 1)) < ⟨n - 2, by omega⟩
                    from Fin.mk_lt_mk.mpr (by have := (pDiv k).2; omega))
          show slowSpeeds (pDiv k) < V
          simp only [slowSpeeds]; exact this
        omega
      let hindSpeeds : Fin (n - 2 - r) → ℕ := fun j => slowSpeeds (indRun j)
      have hindSpeeds_def : ∀ j, hindSpeeds j = slowSpeeds (indRun j) := fun _ => rfl
      have hmono_hind : StrictMono hindSpeeds := by
        intro a b hab
        simp only [hindSpeeds]
        have hindRun_mono : StrictMono indRun := fun a b hab => by
          simp only [indRun]
          exact (indSet.orderEmbOfFin hindSet_card).strictMono hab
        exact hmono_slow (hindRun_mono hab)
      -- Step 6: derive Hn1r and Hr3 from Hn.
      have Hn1r : H (n - r) := fun m hm => Hn m (by omega)
      have Hr3 : H (r + 3) := fun m hm => Hn m (by omega)
      -- Step 7: apply theorem111_ModDI.
      obtain ⟨t₀, ht₀_slow, ht₀_V⟩ :=
        theorem111_ModDI n hn slowSpeeds V hpos_slow hmono_slow
          hV_hard_lo hV_hard_hi p q hp hpq r h_p_dvd_some hr_le pDiv hpDiv_dvd
          indRun hind_not_dvd hind_part w hw_def hmono_w hwq
          hindSpeeds hindSpeeds_def hmono_hind Hn1r Hr3
      -- Step 8: map back to original speeds.
      refine ⟨t₀, fun i => ?_⟩
      rcases Nat.lt_or_eq_of_le (show i.val ≤ n - 2 from by omega) with hi | hi
      · -- Slow runner: i.val < n - 2
        have h := ht₀_slow ⟨i.val, hi⟩
        simp only [slowSpeeds] at h
        exact h
      · -- Fast runner: i.val = n - 2, speeds i = V
        have hVi : speeds i = V := by
          have : speeds i = speeds ⟨n - 2, by omega⟩ :=
            congr_arg speeds (Fin.ext hi)
          exact this
        rw [show (speeds i : ℝ) = (V : ℝ) from by exact_mod_cast hVi]
        exact ht₀_V

/-! ## §12  The full LRC (real speeds) -/

/-- **Remark on the real-speed reduction (§2.2).** The full LRC for real speeds follows
    from `intLRC` by:
    1. For rational speeds: scale to integers.
    2. For real speeds: strict witnesses (from `intLRC` + strict inequality 1/(n-1) > 1/n)
       persist under small perturbation (continuity + Lipschitz).
    3. Rational tuples are dense → extend to all real tuples by approximation.
    This is a standard argument (Bienia et al. 1998); we state it without full proof. -/
-- The full real-speed version is stated here for completeness.
theorem theorem121_LRC_real (n : ℕ) (hn : 3 ≤ n)
    (speeds : Fin (n - 1) → ℝ)
    (hpos : ∀ i, 0 < speeds i)
    (hdist : Function.Injective speeds) :
    ∃ t : ℝ, ∀ i, circDist (speeds i * t) ≥ (1 : ℝ) / n := by
  -- BLOCKER: The reduction from real to integer speeds (§2.2) is standard but lengthy.
  -- Key steps: rational approximation + continuity + strict witness.
  -- MATHLIB_SEARCH: `Rat.dense_iUnion`, `ContinuousAt.tendsto`, `Filter.Tendsto`
  -- STATUS: sorry
  sorry
