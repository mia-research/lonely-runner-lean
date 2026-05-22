import LonelyRunner.LRC.Defs
import LonelyRunner.LRC.Lemma21_FundamentalIdentity
import LonelyRunner.LRC.Lemma41_PositiveMeasure
import LonelyRunner.LRC.Theorem52_Weyl

/-!
# Theorem 11.1 — Modified Divisor Induction (Highly Smooth Case)

Source: `lrc_proof_v11_draft.md` §11.

**This is the key new theorem in the v11 proof — the most complex section.**

**Statement:** In the hard case, suppose the largest prime `p` of `V` divides some
slow runner speeds.  Let `r ≥ 1` be the number of slow runners divisible by `p`,
with speeds `v_{j_k} = p * w_k` (k = 1..r), and write `q = V/p`.
Then `G_s ∩ G_V ≠ ∅`.

**Proof structure:**
1. `S_ind = {slow runners NOT divisible by p}`.  `S_ind ≠ ∅` (Lemma 9.3: r ≤ n-3).
2. `G_ind = jointGoodSet S_ind n`.  `μ(G_ind) > 0` from `H(n-1-r)`.
3. `A = {φ | ‖w_k φ‖ ≥ 1/n ∀k, ‖q φ‖ ≥ 1/n}`.  `μ(A) > 0` from `H(r+2)`.
4. `gcd(p, L_ind) = 1` (since p does not divide any element of S_ind).
5. Theorem 5.2: ∃ `t₀ ∈ G_ind` with `{p t₀} ∈ A`.
6. Verification:
   - S_ind runners: t₀ ∈ G_ind. ✓
   - p-divisible slow runners: `{v_{j_k} t₀} = {p w_k t₀} = {w_k {p t₀}}` (Lemma 2.1) ✓
   - V: `{V t₀} = {pq t₀} = {q {p t₀}}` (Lemma 2.1) ✓

**Key insight:** By writing `φ₀ = {p t₀}`, the conditions on the p-divisible runners
and on V are re-expressed as conditions on φ₀, which is guaranteed by φ₀ ∈ A.

**Difficulty:** HARD — tracks two sets of inductive hypotheses at different n-values,
uses Lemma 2.1 twice with different (a,b) pairs.
-/


open MeasureTheory Set

/-! ## §9.3  r ≤ n-3 (Lemma 9.3) -/

/-- **Lemma 9.3.** In case (b) of the hard case partition (p divides some slow runner),
    the number `r` of slow runners divisible by `p` satisfies `r ≤ n - 3`.
    In particular, `S_ind` (the runners NOT divisible by p) is non-empty. -/
theorem lemma93_r_le
    (n : ℕ) (hn : 3 ≤ n)
    (slowSpeeds : Fin (n - 2) → ℕ)
    (hcop : Nat.Coprime (Finset.prod Finset.univ slowSpeeds) 1)  -- gcd(all speeds) = 1 placeholder
    (p : ℕ) (hp : Nat.Prime p)
    (r : ℕ) (hr_def : r = (Finset.univ.filter (fun i => p ∣ slowSpeeds i)).card)
    (h_p_dvd_some : 0 < r) :
    r ≤ n - 3 := by
  -- If r = n-2 (all slow runners divisible by p), then p | gcd(all speeds),
  -- contradicting gcd = 1 (since p ≥ 2).
  by_contra h
  push_neg at h
  have hr_eq : r = n - 2 := by omega
  -- Then p divides every slow runner.
  have hall : ∀ i : Fin (n - 2), p ∣ slowSpeeds i := by
    intro i
    have : i ∈ Finset.univ.filter (fun i => p ∣ slowSpeeds i) := by
      simp [hr_def] at *
      -- BLOCKER: Connecting |r| = n-2 to "all elements" requires card argument.
      -- STATUS: sorry
      sorry
    simp at this; exact this
  -- Then p | lcm(slow runners), and p | V (given in the DI-MOD case),
  -- so p | gcd(all speeds) = 1. Contradiction.
  -- BLOCKER: Need to derive a contradiction from p | gcd.
  -- STATUS: sorry
  sorry

/-! ## §11  Modified Divisor Induction -/

/-- The target set `A` for Modified Divisor Induction:
    good set for the speeds `(w₁, ..., w_r, q)`. -/
noncomputable def setA_ModDI
    {r : ℕ} (w : Fin r → ℕ) (q n : ℕ) : Set ℝ :=
  { φ : ℝ |
    (∀ k : Fin r, circDist ((w k : ℝ) * φ) ≥ (1 : ℝ) / n) ∧
    circDist ((q : ℝ) * φ) ≥ (1 : ℝ) / n }

/-- `setA_ModDI` has positive measure, given `H(r+2)`. -/
theorem setA_ModDI_measure_pos
    {r : ℕ} (w : Fin r → ℕ) (q n : ℕ)
    (hn : 3 ≤ n) (hr : r + 2 ≤ n - 1)
    (hpos_w : ∀ k, 0 < w k) (hpos_q : 0 < q)
    (hw_dist : StrictMono w)
    (hwq : ∀ k, w k ≠ q)  -- q is not one of the w_k
    (Hr2 : H (r + 2)) :
    0 < MeasureTheory.volume (setA_ModDI w q n) := by
  -- By H(r+2): there exists φ** with circDist(w_k * φ**) ≥ 1/(r+2) > 1/n for all k,
  -- and circDist(q * φ**) ≥ 1/(r+2) > 1/n.
  -- By the Lipschitz/neighbourhood argument (Lemma 4.1 analogue), an interval around φ**
  -- is contained in setA_ModDI, giving positive measure.
  -- BLOCKER: Need to apply intLRC from H(r+2) to the r+1 speeds (w₁,...,w_r,q).
  --          This is a smaller inductive instance (r+2 ≤ n-1 < n).
  -- MATHLIB_SEARCH: same as Lemma 4.1
  -- STATUS: sorry
  sorry

/-- **Theorem 11.1** (Modified Divisor Induction).

    In the hard case, suppose the largest prime `p` of `V` divides exactly `r` slow runners
    (with `r ≥ 1`). Write the p-divisible slow runners as `p * w_k` (k = 1..r), and `q = V/p`.
    Then under `H(n-1-r)` and `H(r+2)`, we have `G_s ∩ G_V ≠ ∅`. -/
theorem theorem111_ModDI
    (n : ℕ) (hn : 3 ≤ n)
    -- The slow runners (all n-2 of them):
    (slowSpeeds : Fin (n - 2) → ℕ)
    (V : ℕ)
    (hpos : ∀ i, 0 < slowSpeeds i)
    (hmono : StrictMono slowSpeeds)
    (hV_hard_lo : (n - 1) * slowSpeeds ⟨0, by omega⟩ < V)
    (hV_hard_hi : V ≤ (n - 1) * slowSpeeds ⟨n - 3, by omega⟩)
    -- The largest prime p of V, with V = p*q:
    (p q : ℕ) (hp : Nat.Prime p) (hpq : V = p * q)
    -- The p-divisible slow runners: r of them, indexed by pDiv:
    (r : ℕ) (hr_pos : 0 < r) (hr_le : r ≤ n - 3)
    (pDiv : Fin r → Fin (n - 2))  -- indices of p-divisible slow runners
    (hpDiv_dvd : ∀ k, p ∣ slowSpeeds (pDiv k))
    -- The independent runners: S_ind ≠ ∅ (n-2-r ≥ 1):
    (indRun : Fin (n - 2 - r) → Fin (n - 2))  -- indices of non-p-divisible slow runners
    (hind_not_dvd : ∀ j, ¬(p ∣ slowSpeeds (indRun j)))
    (hind_part : ∀ i : Fin (n - 2), (∃ k, pDiv k = i) ∨ (∃ j, indRun j = i))  -- partition
    -- Reduced speeds:
    (w : Fin r → ℕ) (hw_def : ∀ k, slowSpeeds (pDiv k) = p * w k)
    (hindSpeeds : Fin (n - 2 - r) → ℕ)
    (hindSpeeds_def : ∀ j, hindSpeeds j = slowSpeeds (indRun j))
    -- Inductive hypotheses:
    (Hn1r : H (n - 1 - r))   -- for G_ind (n-2-r ≥ 1 runners)
    (Hr2 : H (r + 2)) :       -- for set A (r+1 runners: w₁..w_r and q)
    ∃ t₀ : ℝ,
      (∀ i : Fin (n - 2), circDist ((slowSpeeds i : ℝ) * t₀) ≥ (1 : ℝ) / n) ∧
      circDist ((V : ℝ) * t₀) ≥ (1 : ℝ) / n := by
  -- Step 1: G_ind = jointGoodSet hindSpeeds n has positive measure.
  have hcop_ind : Nat.Coprime p (Finset.lcm Finset.univ hindSpeeds) := by
    apply Nat.Coprime.symm
    apply Nat.Coprime.lcm_right
    · intro j
      apply Nat.Coprime.symm
      apply (Nat.Coprime.prime_iff hp).mpr
      exact hind_not_dvd j
  have hG_ind_pos : 0 < MeasureTheory.volume (jointGoodSet hindSpeeds n) := by
    -- Apply Hn1r to hindSpeeds (which has n-2-r elements, forming an (n-1-r)-runner problem).
    -- BLOCKER: Matching the Fin indexing.
    -- STATUS: sorry
    sorry
  -- Step 2: A = setA_ModDI w q n has positive measure.
  have hw_pos : ∀ k, 0 < w k := by
    intro k
    have := hpos (pDiv k)
    rw [hw_def k] at this
    exact Nat.pos_of_mul_pos_left this (Nat.zero_le _)
  have hq_pos : 0 < q := by
    have hV_pos : 0 < V := by
      calc 0 < slowSpeeds ⟨0, by omega⟩ := hpos _
        _ < V := by calc slowSpeeds ⟨0, by omega⟩ ≤ (n-1) * slowSpeeds ⟨0, by omega⟩ := Nat.le_mul_of_pos_left _ (by omega)
                     _ < V := hV_hard_lo
    rw [hpq] at hV_pos
    exact Nat.pos_of_mul_pos_left hV_pos (Nat.zero_le _)
  have hA_pos : 0 < MeasureTheory.volume (setA_ModDI w q n) := by
    apply setA_ModDI_measure_pos w q n hn
    · omega
    · exact hw_pos
    · exact hq_pos
    · -- StrictMono w follows from StrictMono slowSpeeds and pDiv being injective
      -- BLOCKER: Need injectivity of pDiv and strict increase of w.
      -- STATUS: sorry
      sorry
    · -- w k ≠ q for all k: since v_{j_k} = p*w_k is a SLOW runner and V = p*q,
      -- w_k < q would follow from v_{j_k} < V, i.e., p*w_k < p*q, i.e., w_k < q ≤ q.
      intro k
      intro heq
      have : slowSpeeds (pDiv k) = V := by rw [hw_def k, heq, ← hpq]
      -- But slowSpeeds (pDiv k) is a slow runner, so it's strictly less than V.
      -- BLOCKER: Need slow runner < V.
      -- STATUS: sorry
      sorry
    · exact Hr2
  have hA_meas : MeasurableSet (setA_ModDI w q n) := by
    -- BLOCKER: Measurability of {φ | ‖w_k φ‖ ≥ 1/n ∀k, ‖q φ‖ ≥ 1/n}
    -- STATUS: sorry
    sorry
  -- Step 3: gcd(p, L_ind) = 1 (established above as hcop_ind).
  -- Step 4: Apply Theorem 5.2.
  have hweyl := theorem52_nonempty hindSpeeds n
    (Finset.lcm Finset.univ hindSpeeds) p
    rfl hcop_ind (Nat.Prime.pos hp)
    (by positivity)  -- L_ind > 0
    (setA_ModDI w q n) hA_meas hA_pos hG_ind_pos
  obtain ⟨t₀, ht₀_Gind, ht₀_A⟩ := hweyl
  -- Step 5: Verify all conditions.
  refine ⟨t₀, ?_, ?_⟩
  · -- All n-2 slow runners.
    intro i
    -- Case 1: i is an independent runner.
    -- Case 2: i is a p-divisible runner.
    by_cases h_case : ∃ j : Fin (n - 2 - r), indRun j = i
    · -- Case 1: independent runner — from t₀ ∈ G_ind
      obtain ⟨j, hj⟩ := h_case
      have := ht₀_Gind j
      rwa [hindSpeeds_def, hj] at this
    · -- Case 2: p-divisible runner — use Lemma 2.1
      have h_pdiv : ∃ k : Fin r, pDiv k = i := by
        have := hind_part i
        tauto
      obtain ⟨k, hk⟩ := h_pdiv
      -- circDist(v_{j_k} * t₀) = circDist(p * w_k * t₀)
      --   = circDist(w_k * {p * t₀})   (by Lemma 2.1)
      --   ≥ 1/n                          (since {p*t₀} ∈ A)
      rw [← hk, hw_def k]
      have φ₀ := ht₀_A
      -- {p * w_k * t₀} = {w_k * {p * t₀}} by Lemma 2.1
      -- BLOCKER: Apply circDist_fundamental with appropriate types.
      -- STATUS: sorry
      sorry
  · -- Fast runner V = p*q: circDist(V * t₀) = circDist(q * {p * t₀}) ≥ 1/n.
    rw [hpq]
    -- circDist(p * q * t₀) = circDist(q * {p * t₀}) by Lemma 2.1
    have φ₀ := ht₀_A
    rw [show (p : ℝ) * q * t₀ = q * (p * t₀) by ring]
    -- Apply circDist_fundamental
    -- BLOCKER: circDist(q * {p * t₀}) = circDist(q * (p * t₀)) via Lemma 2.1
    -- STATUS: sorry
    sorry
