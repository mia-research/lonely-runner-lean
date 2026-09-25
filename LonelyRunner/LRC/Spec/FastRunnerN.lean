import LonelyRunner.LRC.Spec.OrdersThreeFourN

/-!
# R8, the fast runner: order `n − 1` carries order `n` when one runner is fast

2026-09-24.  Split a subject's disparities into a slow set `S` and one fast disparity `V`, with
`V > (n − 1)·s` for every `s ∈ S`.  Suppose the slow set is lonely at the threshold of the order
below, `1/(n − 1)`, at some instant `τ`.  That is the framework's own obligation at order `n − 1`.

* **The slow runners keep clear of `1/n` on a cell around `τ`.**  At `τ` each slow reading is at
  least `1/(n − 1)` from the integers, and `1/(n − 1) − 1/n = 1/(n (n − 1))`.  A slow runner's
  reading moves by at most `s_max·|t − τ|`, so on `[τ − δ, τ + δ]`, `δ = 1/(n (n − 1) s_max)`, every
  slow runner stays clear at `1/n`.
* **The fast runner cannot block the whole cell.**  Across it the fast reading `V t` moves by
  `2 V δ > 2/n`, more than one in-the-way zone.  So either `τ − δ` is already clear of `V`, or the
  fast runner's own next opening `(K + 1/n)/V`, `K` the integer it is passing, lies inside the cell.

The lonely instant is named: `τ − δ`, or the fast runner's opening (`lonely_of_fast_runner`).
With the order below settled, this carries it up one order for every set whose largest disparity
exceeds `n − 1` times the next (`lonely_of_fast_of_existence`).

Everything here is proved; no `sorry`, no `native_decide`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

namespace LRC.SpecN

open MomentIterationN

variable {n : ℕ} [Fact (2 ≤ n)]

/-- **R8, the fast runner.**  If the slow set `S` is lonely at `1/(n − 1)` at `τ > 0`, and
`V > (n − 1)·s` for every `s ∈ S`, then `S ∪ {V}` is lonely at `1/n`, at `τ − δ` or at an opening of
`V` inside `[τ − δ, τ + δ]`, `δ = 1/(n (n − 1) s_max)`. -/
theorem lonely_of_fast_runner {S : Finset ℝ} (hpos : ∀ s ∈ S, 0 < s) {V : ℝ} (hV0 : 0 < V)
    (hV : ∀ s ∈ S, ((n : ℝ) - 1) * s < V) {τ : ℝ} (hτ : 0 < τ)
    (hlow : ∀ s ∈ S, ((n : ℝ) - 1)⁻¹ ≤ circDist (s * τ)) :
    ∃ t : ℝ, 0 < t ∧ Lonely n (insert V S) t := by
  classical
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast (Fact.out : 2 ≤ n)
  have hn0 : (0 : ℝ) < n := by linarith
  have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  rcases Finset.eq_empty_or_nonempty S with rfl | hne
  · -- no slow runners: the fast runner's first opening
    refine ⟨(n : ℝ)⁻¹ / V, by positivity, fun d hd => ?_⟩
    rw [insert_empty_eq, Finset.mem_singleton] at hd
    subst hd
    rw [show d * ((n : ℝ)⁻¹ / d) = (n : ℝ)⁻¹ by field_simp, circDist_one_eighth]
  · set m := S.max' hne with hm
    have hmS : m ∈ S := S.max'_mem hne
    have hm0 : 0 < m := hpos m hmS
    have hle : ∀ s ∈ S, s ≤ m := fun s hs => S.le_max' s hs
    set δ : ℝ := 1 / ((n : ℝ) * ((n : ℝ) - 1) * m) with hδ
    have hδ0 : 0 < δ := by positivity
    -- the fast runner sweeps more than one zone across the cell
    have hVδ : (n : ℝ)⁻¹ < V * δ := by
      have h := hV m hmS
      show (n : ℝ)⁻¹ < V * (1 / ((n : ℝ) * ((n : ℝ) - 1) * m))
      rw [show V * (1 / ((n : ℝ) * ((n : ℝ) - 1) * m)) = V / ((n : ℝ) * ((n : ℝ) - 1) * m) by ring,
        lt_div_iff₀ (by positivity)]
      calc (n : ℝ)⁻¹ * ((n : ℝ) * ((n : ℝ) - 1) * m) = ((n : ℝ) - 1) * m := by field_simp
        _ < V := h
    -- `τ − δ` is positive: the slowest-clearing runner has already left
    have hτδ : δ < τ := by
      have h1 := hlow m hmS
      have h2 : circDist (m * τ) ≤ m * τ := by
        have := ConstructionN.circDist_le_abs_sub_int (m * τ) 0
        simpa [abs_of_pos (mul_pos hm0 hτ)] using this
      have h3 : ((n : ℝ) - 1)⁻¹ ≤ m * τ := le_trans h1 h2
      have h4 : δ < ((n : ℝ) - 1)⁻¹ / m := by
        rw [hδ, div_lt_div_iff₀ (by positivity) hm0]
        field_simp
        nlinarith
      calc δ < ((n : ℝ) - 1)⁻¹ / m := h4
        _ ≤ τ := by rw [div_le_iff₀ hm0]; linarith
    -- every point of the cell keeps the slow runners clear at `1/n`
    have hslow : ∀ t, |t - τ| ≤ δ → ∀ s ∈ S, (n : ℝ)⁻¹ ≤ circDist (s * t) := by
      intro t ht s hs
      have hs0 := hpos s hs
      have hlip := circDist_lipschitz.dist_le_mul (s * t) (s * τ)
      simp only [NNReal.coe_one, one_mul, Real.dist_eq] at hlip
      have hdiff : |s * t - s * τ| ≤ m * δ := by
        rw [← mul_sub, abs_mul, abs_of_pos hs0]
        exact mul_le_mul (hle s hs) ht (abs_nonneg _) hm0.le
      have hmδ : m * δ = ((n : ℝ) - 1)⁻¹ - (n : ℝ)⁻¹ := by
        rw [hδ]; field_simp; ring
      have := abs_sub_le_iff.mp hlip
      have h5 := hlow s hs
      linarith [this.2]
    -- the fast runner is clear somewhere on the cell: at `τ − δ`, or at its next opening
    by_cases hclear : (n : ℝ)⁻¹ ≤ circDist (V * (τ - δ))
    · refine ⟨τ - δ, by linarith, fun d hd => ?_⟩
      rcases Finset.mem_insert.mp hd with rfl | hdS
      · exact hclear
      · exact hslow (τ - δ) (by rw [show τ - δ - τ = -δ by ring, abs_neg, abs_of_pos hδ0]) d hdS
    · push Not at hclear
      obtain ⟨K, hK⟩ := ConstructionN.circDist_eq_abs_sub_some_int (V * (τ - δ))
      rw [hK] at hclear
      have hK1 := (abs_lt.mp hclear)
      set t := ((K : ℝ) + (n : ℝ)⁻¹) / V with ht
      have hVt : V * t = (K : ℝ) + (n : ℝ)⁻¹ := by rw [ht]; field_simp
      -- the opening sits inside the cell
      have hlo : τ - δ < t := by
        rw [ht, lt_div_iff₀ hV0]; nlinarith [hK1.2]
      have hhi : t ≤ τ + δ := by
        rw [ht, div_le_iff₀ hV0]; nlinarith [hK1.1, hVδ]
      refine ⟨t, by linarith, fun d hd => ?_⟩
      rcases Finset.mem_insert.mp hd with rfl | hdS
      · rw [hVt, add_comm, ConstructionN.circDist_add_int, circDist_one_eighth]
      · exact hslow t (by rw [abs_le]; constructor <;> linarith) d hdS

/-- **R8 with the order below settled.**  If every set of at most `n − 2` positive disparities is
lonely at `1/(n − 1)`, then any set of at most `n − 1` positive disparities whose largest member
exceeds `n − 1` times every other is lonely at `1/n`. -/
theorem lonely_of_fast_of_existence (hn3 : 3 ≤ n)
    (hbelow : ∀ S : Finset ℝ, (∀ s ∈ S, 0 < s) → S.card ≤ n - 2 →
      ∃ τ : ℝ, 0 < τ ∧ ∀ s ∈ S, ((n : ℝ) - 1)⁻¹ ≤ circDist (s * τ))
    {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d) (hcard : ds.card ≤ n - 1)
    {V : ℝ} (hVds : V ∈ ds) (hV : ∀ s ∈ ds.erase V, ((n : ℝ) - 1) * s < V) :
    ∃ t : ℝ, 0 < t ∧ Lonely n ds t := by
  classical
  have hcardS : (ds.erase V).card ≤ n - 2 := by
    rw [Finset.card_erase_of_mem hVds]; omega
  obtain ⟨τ, hτ, hlow⟩ := hbelow (ds.erase V) (fun s hs => hpos s (Finset.mem_of_mem_erase hs)) hcardS
  obtain ⟨t, ht, hl⟩ := lonely_of_fast_runner (fun s hs => hpos s (Finset.mem_of_mem_erase hs))
    (hpos V hVds) hV hτ hlow
  rw [Finset.insert_erase hVds] at hl
  exact ⟨t, ht, hl⟩

/-- **R8 at order five.**  Order four is settled inside the framework (`existenceAtN_four`), so every
set of at most four positive disparities whose largest member exceeds four times every other is
lonely at `1/5`. -/
theorem lonely_five_of_fast {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d) (hcard : ds.card ≤ 4)
    {V : ℝ} (hVds : V ∈ ds) (hV : ∀ s ∈ ds.erase V, 4 * s < V) :
    ∃ t : ℝ, 0 < t ∧ Lonely 5 ds t := by
  haveI : Fact (2 ≤ 5) := ⟨by norm_num⟩
  have h54 : ((5 : ℕ) : ℝ) - 1 = ((4 : ℕ) : ℝ) := by norm_num
  refine lonely_of_fast_of_existence (n := 5) (by norm_num) (fun S hS hc => ?_) hpos hcard hVds
    (fun s hs => by rw [h54]; exact_mod_cast hV s hs)
  obtain ⟨τ, hτ, hl⟩ := existenceAtN_four S hS (by simpa using hc)
  exact ⟨τ, hτ, fun s hs => by rw [h54]; exact hl s hs⟩

end LRC.SpecN
