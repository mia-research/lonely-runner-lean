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
    In particular, `S_ind` (the runners NOT divisible by p) is non-empty.

    **Proof:** Since ∃ slow runner i₀ NOT divisible by p, the filter set is a subset of
    `univ \ {i₀}`, which has cardinality n-2-1 = n-3. -/
theorem lemma93_r_le
    (n : ℕ) (hn : 3 ≤ n)
    (slowSpeeds : Fin (n - 2) → ℕ)
    (p : ℕ) (hp : Nat.Prime p)
    (r : ℕ) (hr_def : r = (Finset.univ.filter (fun i => p ∣ slowSpeeds i)).card)
    (h_p_dvd_some : 0 < r)
    (h_some_not_p : ∃ i : Fin (n - 2), ¬(p ∣ slowSpeeds i)) :
    r ≤ n - 3 := by
  obtain ⟨i₀, hi₀⟩ := h_some_not_p
  -- The filter set avoids i₀ (since p ∤ slowSpeeds i₀)
  have h_sub : Finset.univ.filter (fun i => p ∣ slowSpeeds i) ⊆
               Finset.univ (α := Fin (n - 2)) \ {i₀} := by
    intro x hx
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_singleton]
    intro hx_eq
    exact hi₀ (hx_eq ▸ (Finset.mem_filter.mp hx).2)
  -- card(filter) ≤ card(univ \ {i₀}) = (n-2) - 1
  have h_card_le : (Finset.univ.filter (fun i => p ∣ slowSpeeds i)).card ≤
                   (Finset.univ (α := Fin (n - 2)) \ {i₀}).card :=
    Finset.card_le_card h_sub
  -- card(univ \ {i₀}) = (n-2) - 1
  -- Finset.card_sdiff : (A \ B).card = A.card - (B ∩ A).card  (no subset hypothesis in Lean 4)
  have h_sdiff : (Finset.univ (α := Fin (n - 2)) \ {i₀}).card = n - 2 - 1 := by
    simp only [Finset.card_sdiff, Finset.inter_univ, Finset.card_singleton,
               Finset.card_univ, Fintype.card_fin]
  -- r ≤ n-2-1 = n-3
  omega

/-! ## §11  Modified Divisor Induction -/

/-- The target set `A` for Modified Divisor Induction:
    good set for the speeds `(w₁, ..., w_r, q)`. -/
noncomputable def setA_ModDI
    {r : ℕ} (w : Fin r → ℕ) (q n : ℕ) : Set ℝ :=
  { φ : ℝ |
    (∀ k : Fin r, circDist ((w k : ℝ) * φ) ≥ (1 : ℝ) / n) ∧
    circDist ((q : ℝ) * φ) ≥ (1 : ℝ) / n }

/-- `setA_ModDI` has positive measure, given `H(r+3)`.

    We need H(r+3) (not H(r+2)) because:
    `setA_ModDI w q n` is the good set for r+1 runners (w₁,…,w_r and q) at threshold 1/n.
    `intLRC(r+2)` gives a witness for r+1 = (r+2)-1 runners.
    `H(m) = ∀ m' < m, intLRC m'`, so H(r+3) gives intLRC(r+2). H(r+2) only gives
    intLRC up to r+1, which covers r runners — one short. -/
theorem setA_ModDI_measure_pos
    {r : ℕ} (w : Fin r → ℕ) (q n : ℕ)
    (hn : 3 ≤ n) (hr : r + 2 ≤ n - 1)
    (hpos_w : ∀ k, 0 < w k) (hpos_q : 0 < q)
    (hw_dist : StrictMono w)
    (hwq : ∀ k, w k ≠ q)  -- q is not one of the w_k
    (Hr3 : H (r + 3)) :
    0 < MeasureTheory.volume (setA_ModDI w q n) := by
  -- Build S = image(w) ∪ {q} with card r+1
  let wSet : Finset ℕ := Finset.univ.image w
  let S : Finset ℕ := wSet ∪ {q}
  have hwSet_card : wSet.card = r := by
    show (Finset.univ.image w).card = r
    rw [Finset.card_image_of_injective _ hw_dist.injective, Finset.card_univ, Fintype.card_fin]
  have hq_notin : q ∉ wSet := by
    simp only [wSet, Finset.mem_image, Finset.mem_univ, true_and]
    rintro ⟨k, rfl⟩; exact absurd rfl (hwq k)
  have hS_card : S.card = r + 1 := by
    have hdisj : Disjoint wSet {q} := by
      rw [Finset.disjoint_left]
      intro x hx hxq
      exact hq_notin (Finset.mem_singleton.mp hxq ▸ hx)
    rw [Finset.card_union_of_disjoint hdisj, hwSet_card, Finset.card_singleton]
  -- Sorted StrictMono enumeration f : Fin (r+1) ↪o ℕ
  let f := S.orderEmbOfFin hS_card
  have hf_pos : ∀ i, 0 < (f i : ℕ) := fun i => by
    have hmem := Finset.orderEmbOfFin_mem S hS_card i
    simp only [S, wSet, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and,
               Finset.mem_singleton] at hmem
    rcases hmem with ⟨k, hk⟩ | hq_eq
    · rw [← hk]; exact hpos_w k
    · rw [hq_eq]; exact hpos_q
  -- Apply lemma41_positive_measure with Hr3 to the sorted speeds (r+1 of them = (r+3)-2)
  have hr3_le_n : r + 3 ≤ n := by omega
  have h_hk : r + 1 = (r + 3) - 2 := by omega
  -- f.strictMono : StrictMono (fun i => f i)
  have hf_mono : StrictMono (fun i => (f i : ℕ)) := f.strictMono
  obtain ⟨t_star, δ, hδ_pos, _, hI_sub, hGs_pos⟩ :=
    lemma41_positive_measure (show 3 ≤ r + 3 by omega) h_hk
      (fun i => (f i : ℕ)) hf_pos hf_mono Hr3
  have hr3_pos : (0 : ℝ) < r + 3 := by positivity
  have h_thresh : (1 : ℝ) / n ≤ 1 / (r + 3) :=
    one_div_le_one_div_of_le hr3_pos (by exact_mod_cast hr3_le_n)
  -- Helper: for any x ∈ S, find i with f i = x
  have h_surj : ∀ x ∈ S, ∃ i : Fin (r + 1), f i = x := by
    intro x hx
    have hmem : x ∈ Set.range (S.orderEmbOfFin hS_card) := by
      rw [Finset.range_orderEmbOfFin]; exact Finset.mem_coe.mpr hx
    exact Set.mem_range.mp hmem
  -- Helper: ht gives the threshold for each f-index
  have hf_thresh : jointGoodSet (fun i => (f i : ℕ)) (r + 3) ⊆
      setA_ModDI w q n := by
    intro t ht
    simp only [setA_ModDI, Set.mem_setOf_eq]
    refine ⟨fun k => ?_, ?_⟩
    · -- w k ∈ S so ∃ i, f i = w k
      have hwk_S : w k ∈ S :=
        Finset.mem_union_left _ (Finset.mem_image_of_mem w (Finset.mem_univ k))
      obtain ⟨i, hi⟩ := h_surj (w k) hwk_S
      have hti : circDist ((f i : ℝ) * t) ≥ 1 / (r + 3 : ℝ) := by
        have hmem := Set.mem_iInter.mp ht i
        simp only [goodSet, Set.mem_setOf_eq] at hmem; exact_mod_cast hmem
      have heq : (f i : ℝ) = (w k : ℝ) := by exact_mod_cast hi
      linarith [heq ▸ hti]
    · -- q ∈ S so ∃ i, f i = q
      have hq_S : q ∈ S := Finset.mem_union_right _ (Finset.mem_singleton_self _)
      obtain ⟨i, hi⟩ := h_surj q hq_S
      have hti : circDist ((f i : ℝ) * t) ≥ 1 / (r + 3 : ℝ) := by
        have hmem := Set.mem_iInter.mp ht i
        simp only [goodSet, Set.mem_setOf_eq] at hmem; exact_mod_cast hmem
      have heq : (f i : ℝ) = (q : ℝ) := by exact_mod_cast hi
      linarith [heq ▸ hti]
  -- Positive measure: μ(G_s) > 0 and G_s ⊆ setA_ModDI, so μ(setA_ModDI) > 0
  exact hGs_pos.trans_le (MeasureTheory.measure_mono hf_thresh)

/-- `setA_ModDI w q n` is a closed set.

    It equals `(⋂ k, goodSet (w k) n) ∩ goodSet q n`, a finite intersection of closed sets. -/
theorem setA_ModDI_isClosed {r : ℕ} (w : Fin r → ℕ) (q n : ℕ) :
    IsClosed (setA_ModDI w q n) := by
  have h_eq : setA_ModDI w q n =
      (⋂ k : Fin r, goodSet (w k) n) ∩ goodSet q n := by
    ext φ
    simp only [setA_ModDI, goodSet, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
  rw [h_eq]
  exact IsClosed.inter
    (isClosed_iInter (fun k => goodSet_isClosed (w k) n))
    (goodSet_isClosed q n)

/-- **Equivalence:** `setA_ModDI w q n = jointGoodSet (Fin.snoc w q) n`.

    Direct rewriting: `Fin.snoc w q` at `Fin.castSucc k` is `w k`, at `Fin.last r` is `q`,
    so the intersection over all snoc'd indices is exactly the AND of w-conditions and
    the q-condition. -/
theorem setA_ModDI_eq_jointGoodSet {r : ℕ} (w : Fin r → ℕ) (q n : ℕ) :
    setA_ModDI w q n = jointGoodSet (Fin.snoc w q) n := by
  ext φ
  simp only [setA_ModDI, jointGoodSet, goodSet, Set.mem_setOf_eq, Set.mem_iInter]
  constructor
  · rintro ⟨hw_all, hq⟩
    intro i
    induction i using Fin.lastCases with
    | last => simpa [Fin.snoc] using hq
    | cast k => simpa [Fin.snoc] using hw_all k
  · intro h
    refine ⟨fun k => ?_, ?_⟩
    · have := h (Fin.castSucc k); simpa [Fin.snoc] using this
    · have := h (Fin.last r); simpa [Fin.snoc] using this

/-- **Unit-interval variant** of `setA_ModDI_measure_pos`.

    Uses `lemma41_positive_measure`'s closed-interval witness `Icc (t* - δ) (t* + δ) ⊆
    jointGoodSet (sorted speeds) (r+3)`, lifts to `Icc ⊆ jointGoodSet (Fin.snoc w q) n`
    (containment + threshold drop), then applies the periodicity bridge to extract
    positive measure on `[0, 1)`. -/
theorem setA_ModDI_pos_measure_in_unit
    {r : ℕ} (w : Fin r → ℕ) (q n : ℕ)
    (hn : 3 ≤ n) (hr : r + 2 ≤ n - 1)
    (hpos_w : ∀ k, 0 < w k) (hpos_q : 0 < q)
    (hw_dist : StrictMono w)
    (hwq : ∀ k, w k ≠ q)
    (Hr3 : H (r + 3)) :
    0 < MeasureTheory.volume
      (jointGoodSet (Fin.snoc w q) n ∩ Set.Ico (0 : ℝ) 1) := by
  -- Use the same sorted-enumeration construction as `setA_ModDI_measure_pos`.
  let wSet : Finset ℕ := Finset.univ.image w
  let S : Finset ℕ := wSet ∪ {q}
  have hwSet_card : wSet.card = r := by
    show (Finset.univ.image w).card = r
    rw [Finset.card_image_of_injective _ hw_dist.injective, Finset.card_univ, Fintype.card_fin]
  have hq_notin : q ∉ wSet := by
    simp only [wSet, Finset.mem_image, Finset.mem_univ, true_and]
    rintro ⟨k, rfl⟩; exact absurd rfl (hwq k)
  have hS_card : S.card = r + 1 := by
    have hdisj : Disjoint wSet {q} := by
      rw [Finset.disjoint_left]
      intro x hx hxq
      exact hq_notin (Finset.mem_singleton.mp hxq ▸ hx)
    rw [Finset.card_union_of_disjoint hdisj, hwSet_card, Finset.card_singleton]
  let f := S.orderEmbOfFin hS_card
  have hf_pos : ∀ i, 0 < (f i : ℕ) := fun i => by
    have hmem := Finset.orderEmbOfFin_mem S hS_card i
    simp only [S, wSet, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and,
               Finset.mem_singleton] at hmem
    rcases hmem with ⟨k, hk⟩ | hq_eq
    · rw [← hk]; exact hpos_w k
    · rw [hq_eq]; exact hpos_q
  have hr3_le_n : r + 3 ≤ n := by omega
  have h_hk : r + 1 = (r + 3) - 2 := by omega
  have hf_mono : StrictMono (fun i => (f i : ℕ)) := f.strictMono
  obtain ⟨t_star, δ, hδ_pos, _, hI_sub, _⟩ :=
    lemma41_positive_measure (show 3 ≤ r + 3 by omega) h_hk
      (fun i => (f i : ℕ)) hf_pos hf_mono Hr3
  have hr3_pos : (0 : ℝ) < r + 3 := by positivity
  have h_thresh : (1 : ℝ) / n ≤ 1 / (r + 3) :=
    one_div_le_one_div_of_le hr3_pos (by exact_mod_cast hr3_le_n)
  -- Containment: jointGoodSet sorted (r+3) ⊆ setA_ModDI w q n.
  have h_surj : ∀ x ∈ S, ∃ i : Fin (r + 1), f i = x := by
    intro x hx
    have hmem : x ∈ Set.range (S.orderEmbOfFin hS_card) := by
      rw [Finset.range_orderEmbOfFin]; exact Finset.mem_coe.mpr hx
    exact Set.mem_range.mp hmem
  have hf_thresh : jointGoodSet (fun i => (f i : ℕ)) (r + 3) ⊆
      setA_ModDI w q n := by
    intro t ht
    simp only [setA_ModDI, Set.mem_setOf_eq]
    refine ⟨fun k => ?_, ?_⟩
    · have hwk_S : w k ∈ S :=
        Finset.mem_union_left _ (Finset.mem_image_of_mem w (Finset.mem_univ k))
      obtain ⟨i, hi⟩ := h_surj (w k) hwk_S
      have hti : circDist ((f i : ℝ) * t) ≥ 1 / (r + 3 : ℝ) := by
        have hmem := Set.mem_iInter.mp ht i
        simp only [goodSet, Set.mem_setOf_eq] at hmem; exact_mod_cast hmem
      have heq : (f i : ℝ) = (w k : ℝ) := by exact_mod_cast hi
      linarith [heq ▸ hti]
    · have hq_S : q ∈ S := Finset.mem_union_right _ (Finset.mem_singleton_self _)
      obtain ⟨i, hi⟩ := h_surj q hq_S
      have hti : circDist ((f i : ℝ) * t) ≥ 1 / (r + 3 : ℝ) := by
        have hmem := Set.mem_iInter.mp ht i
        simp only [goodSet, Set.mem_setOf_eq] at hmem; exact_mod_cast hmem
      have heq : (f i : ℝ) = (q : ℝ) := by exact_mod_cast hi
      linarith [heq ▸ hti]
  -- Compose containment to land in jointGoodSet (Fin.snoc w q) n.
  have h_snoc : setA_ModDI w q n = jointGoodSet (Fin.snoc w q) n :=
    setA_ModDI_eq_jointGoodSet w q n
  have hI_sub' : Set.Icc (t_star - δ) (t_star + δ) ⊆
      jointGoodSet (Fin.snoc w q) n := by
    intro t ht
    rw [← h_snoc]; exact hf_thresh (hI_sub ht)
  -- Apply periodicity bridge for the snoc'd family.
  have hposA : ∀ i : Fin (r + 1), 0 < (Fin.snoc w q : Fin (r + 1) → ℕ) i := by
    intro i
    induction i using Fin.lastCases with
    | last => simpa [Fin.snoc] using hpos_q
    | cast k => simpa [Fin.snoc] using hpos_w k
  exact jointGoodSet_inter_unit_pos_of_Icc_subset (Fin.snoc w q) n hposA
    (t_star - δ) (t_star + δ) (by linarith) hI_sub'

/-- **Theorem 11.1** (Modified Divisor Induction).

    In the hard case, suppose the largest prime `p` of `V` divides exactly `r` slow runners
    (with `r ≥ 1`). Write the p-divisible slow runners as `p * w_k` (k = 1..r), and `q = V/p`.
    Then under `H(n-r)` and `H(r+3)`, we have `G_s ∩ G_V ≠ ∅`.

    **Proof structure:**
    1. G_ind = jointGoodSet hindSpeeds n has positive measure — via lemma41 at threshold n-r
       (H(n-r) gives intLRC(n-1-r) for n-2-r runners), then containment to threshold n.
    2. A = setA_ModDI w q n has positive measure — via setA_ModDI_measure_pos with H(r+3).
    3. gcd(p, lcm(hindSpeeds)) = 1 — p prime, p ∤ any hindSpeed.
    4. Apply theorem52_nonempty_correct: ∃ t₀ ∈ G_ind with Int.fract(p·t₀) ∈ A.
    5. Verify p-divisible runners: circDist(p·wₖ·t₀) = circDist(wₖ·{p·t₀}) ≥ 1/n (Lemma 2.1).
    6. Verify independent runners: t₀ ∈ G_ind gives circDist ≥ 1/n directly.
    7. Verify V = p·q: circDist(V·t₀) = circDist(q·{p·t₀}) ≥ 1/n (Lemma 2.1).

    **NOTE on H-index fix:** The correct hypothesis is `H(n-r)` (not `H(n-1-r)` as in earlier
    drafts). `H(n-r)` gives `intLRC(n-1-r)` which handles `n-2-r` = (n-1-r)-1 runners.
    With `r ≤ n-3`, `n-r ≥ 3`, so `lemma41_positive_measure` applies. -/
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
    (pDiv : Fin r → Fin (n - 2))
    (hpDiv_dvd : ∀ k, p ∣ slowSpeeds (pDiv k))
    -- The independent runners (not divisible by p):
    (indRun : Fin (n - 2 - r) → Fin (n - 2))
    (hind_not_dvd : ∀ j, ¬(p ∣ slowSpeeds (indRun j)))
    (hind_part : ∀ i : Fin (n - 2), (∃ k, pDiv k = i) ∨ (∃ j, indRun j = i))
    -- Reduced speeds w (with w k = slowSpeeds(pDiv k) / p):
    (w : Fin r → ℕ) (hw_def : ∀ k, slowSpeeds (pDiv k) = p * w k)
    (hmono_w : StrictMono w)          -- w is strictly increasing
    (hwq : ∀ k, w k ≠ q)             -- q is not among the w_k
    -- Independent speeds:
    (hindSpeeds : Fin (n - 2 - r) → ℕ)
    (hindSpeeds_def : ∀ j, hindSpeeds j = slowSpeeds (indRun j))
    (hmono_hind : StrictMono hindSpeeds)  -- hindSpeeds is strictly increasing
    -- Inductive hypotheses:
    (Hn1r : H (n - r))    -- FIXED: was H(n-1-r); H(n-r) gives intLRC(n-1-r) for n-2-r runners
    (Hr3 : H (r + 3)) :   -- for set A (r+1 runners: w₁..w_r and q)
    ∃ t₀ : ℝ,
      (∀ i : Fin (n - 2), circDist ((slowSpeeds i : ℝ) * t₀) ≥ (1 : ℝ) / n) ∧
      circDist ((V : ℝ) * t₀) ≥ (1 : ℝ) / n := by
  -- ── Derived arithmetic facts ──────────────────────────────────────────────
  have hn_pos : 0 < n := by omega
  have hn_minus_r_pos : 0 < n - r := by omega
  have h3_le_n_r : 3 ≤ n - r := by omega  -- from hr_le : r ≤ n-3
  have hr2_le : r + 2 ≤ n - 1 := by omega  -- from hr_le
  have hq_pos : 0 < q := by
    rcases Nat.eq_zero_or_pos q with rfl | hq
    · simp [hpq] at hV_hard_lo  -- p*0=0 < (n-1)*v₁ is False in ℕ
    · exact hq
  -- hpos_w: w k > 0 (from hpos + hw_def; can't use rcases rfl on function application)
  have hpos_w : ∀ k, 0 < w k := fun k => by
    have h : 0 < p * w k := hw_def k ▸ hpos (pDiv k)
    exact Nat.pos_of_ne_zero (fun h0 => by simp [h0] at h)
  -- hpos_hind: hindSpeeds j > 0
  have hpos_hind : ∀ j, 0 < hindSpeeds j :=
    fun j => hindSpeeds_def j ▸ hpos (indRun j)
  -- ── Step 1: G_ind ∩ [0,1) has positive measure (via lemma41 + periodicity bridge) ──
  have hk_eq : n - 2 - r = (n - r) - 2 := by omega
  obtain ⟨t_star, δ, hδ_pos, _, hIcc_sub_nr, _⟩ :=
    lemma41_positive_measure h3_le_n_r hk_eq hindSpeeds hpos_hind hmono_hind Hn1r
  -- Containment: jointGoodSet hindSpeeds (n-r) ⊆ jointGoodSet hindSpeeds n
  -- because 1/(n-r) ≥ 1/n (smaller denominator = larger threshold).
  have hGind_sub : jointGoodSet hindSpeeds (n - r) ⊆ jointGoodSet hindSpeeds n := by
    intro t ht
    simp only [jointGoodSet, Set.mem_iInter, goodSet, Set.mem_setOf_eq] at *
    intro j
    have hn_nr_pos : (0 : ℝ) < ((n - r : ℕ) : ℝ) := by exact_mod_cast hn_minus_r_pos
    have h_thresh : (1 : ℝ) / (n : ℕ) ≤ 1 / ((n - r : ℕ) : ℝ) :=
      one_div_le_one_div_of_le hn_nr_pos (by exact_mod_cast Nat.sub_le n r)
    linarith [ht j]
  -- Lift the Icc witness to threshold n.
  have hIcc_sub_n : Set.Icc (t_star - δ) (t_star + δ) ⊆ jointGoodSet hindSpeeds n :=
    fun t ht => hGind_sub (hIcc_sub_nr ht)
  have hGind_unit_pos :
      0 < MeasureTheory.volume (jointGoodSet hindSpeeds n ∩ Set.Ico (0 : ℝ) 1) :=
    jointGoodSet_inter_unit_pos_of_Icc_subset hindSpeeds n hpos_hind
      (t_star - δ) (t_star + δ) (by linarith) hIcc_sub_n
  -- ── Step 2: A = setA_ModDI w q n ∩ [0,1) has positive measure ─────────────
  have hA_unit_pos :
      0 < MeasureTheory.volume
        (jointGoodSet (Fin.snoc w q) n ∩ Set.Ico (0 : ℝ) 1) :=
    setA_ModDI_pos_measure_in_unit w q n hn hr2_le hpos_w hq_pos hmono_w hwq Hr3
  -- ── Step 3: positivity of the two lcm's ──────────────────────────────────
  have hL_G_pos : 0 < lcmSpeeds hindSpeeds := by
    simp only [lcmSpeeds]
    rw [Nat.pos_iff_ne_zero]
    intro hzero
    rw [Finset.lcm_eq_zero_iff] at hzero
    obtain ⟨i, _, hi⟩ := hzero
    exact absurd hi (Nat.pos_iff_ne_zero.mp (hpos_hind i))
  have hL_A_pos : 0 < lcmSpeeds (Fin.snoc w q) := by
    simp only [lcmSpeeds]
    rw [Nat.pos_iff_ne_zero]
    intro hzero
    rw [Finset.lcm_eq_zero_iff] at hzero
    obtain ⟨i, _, hi⟩ := hzero
    induction i using Fin.lastCases with
    | last => exact absurd hi (Nat.pos_iff_ne_zero.mp (by simpa [Fin.snoc] using hq_pos))
    | cast k => exact absurd hi (Nat.pos_iff_ne_zero.mp (by simpa [Fin.snoc] using hpos_w k))
  -- ── Step 4: Coprimality gcd(p, lcm(hindSpeeds)) = 1 ──────────────────────
  -- p is prime and p does not divide any hindSpeeds j → p ∤ lcm(hindSpeeds).
  have hcop : Nat.Coprime p (lcmSpeeds hindSpeeds) := by
    -- Step 4a: ¬(p ∣ Finset.lcm univ hindSpeeds) by finset induction.
    -- Key lemma used: Prime.not_dvd_lcm (GCDMonoid) — takes hp : _root_.Prime p.
    -- Induction: p ∤ every hindSpeeds j → p ∤ insert-step lcm → p ∤ full lcm.
    have h_not_dvd : ¬(p ∣ lcmSpeeds hindSpeeds) := by
      simp only [lcmSpeeds]
      have key : ∀ (s : Finset (Fin (n - 2 - r))),
          (∀ j ∈ s, ¬(p ∣ hindSpeeds j)) → ¬(p ∣ s.lcm hindSpeeds) := by
        intro s
        induction s using Finset.induction_on with
        | empty =>
          intro _ h
          simp only [Finset.lcm_empty] at h
          exact hp.one_lt.ne' (Nat.dvd_one.mp h)
        | insert a s _ ih =>
          intro h_all h_dvd
          rw [Finset.lcm_insert] at h_dvd
          exact hp.prime.not_dvd_lcm
            (h_all a (Finset.mem_insert_self a s))
            (ih (fun j hj => h_all j (Finset.mem_insert_of_mem hj)))
            h_dvd
      -- hind_not_dvd j : ¬p ∣ slowSpeeds (indRun j); hindSpeeds_def j rewrites to hindSpeeds j
      exact key Finset.univ (fun j _ => hindSpeeds_def j ▸ hind_not_dvd j)
    -- Step 4b: ¬dvd → Coprime via primality: gcd(lcm, p) divides p → = 1 or p; not p.
    rw [Nat.Coprime, Nat.gcd_comm]
    rcases hp.eq_one_or_self_of_dvd
        (Nat.gcd (lcmSpeeds hindSpeeds) p) (Nat.gcd_dvd_right _ _) with h | h
    · exact h
    · exact absurd (h ▸ Nat.gcd_dvd_left _ _) h_not_dvd
  -- ── Step 5: Apply Theorem 5.2 (structured Option A form) ─────────────────
  obtain ⟨t₀, ht₀_G, ht₀_A_raw⟩ :=
    theorem52_nonempty_ModDI hindSpeeds w q n (lcmSpeeds hindSpeeds)
      (lcmSpeeds (Fin.snoc w q)) p hn rfl hL_G_pos rfl hL_A_pos hcop hp.one_lt
      hpos_hind hpos_w hq_pos hGind_unit_pos hA_unit_pos
  -- Convert from jointGoodSet (Fin.snoc w q) n to setA_ModDI w q n form.
  have ht₀_A : Int.fract ((p : ℝ) * t₀) ∈ setA_ModDI w q n := by
    rw [setA_ModDI_eq_jointGoodSet]; exact ht₀_A_raw
  simp only [setA_ModDI, Set.mem_setOf_eq] at ht₀_A
  -- ── Step 6: Verify all slow runners and V ────────────────────────────────
  refine ⟨t₀, fun i => ?_, ?_⟩
  · -- Slow runner i: either p-divisible (= p*w k) or independent (= hindSpeeds j)
    rcases hind_part i with ⟨k, hk⟩ | ⟨j, hj⟩
    · -- Case: i = pDiv k, so slowSpeeds i = p * w k
      have hspeed_eq : slowSpeeds i = p * w k := hk ▸ hw_def k
      -- circDist((p*wₖ)*t₀) = circDist(wₖ*{p*t₀}) ≥ 1/n  (Lemma 2.1 + ht₀_A)
      rw [show (slowSpeeds i : ℝ) = (p * w k : ℝ) from by exact_mod_cast hspeed_eq,
          show (p * w k : ℝ) * t₀ = (w k : ℝ) * ((p : ℝ) * t₀) from by ring,
          ← circDist_fundamental (w k) p t₀]
      exact ht₀_A.1 k
    · -- Case: i = indRun j, so slowSpeeds i = hindSpeeds j
      have hspeed_eq : slowSpeeds i = hindSpeeds j := by
        conv_lhs => rw [← hj]
        exact (hindSpeeds_def j).symm
      rw [show (slowSpeeds i : ℝ) = (hindSpeeds j : ℝ) from by exact_mod_cast hspeed_eq]
      -- t₀ ∈ G_ind = jointGoodSet hindSpeeds n → circDist(hindSpeeds j * t₀) ≥ 1/n
      have hj_good := Set.mem_iInter.mp ht₀_G j
      simp only [goodSet, Set.mem_setOf_eq] at hj_good
      exact hj_good
  · -- Fast runner V = p * q
    -- circDist(V*t₀) = circDist(q*{p*t₀}) ≥ 1/n  (Lemma 2.1 + ht₀_A)
    rw [show (V : ℝ) = (p * q : ℝ) from by exact_mod_cast hpq,
        show (p * q : ℝ) * t₀ = (q : ℝ) * ((p : ℝ) * t₀) from by ring,
        ← circDist_fundamental q p t₀]
    exact ht₀_A.2
