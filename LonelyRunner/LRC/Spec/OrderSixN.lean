import LonelyRunner.LRC.Spec.OrderFiveResidualN
import LonelyRunner.LRC.Spec.NamedFlankN

/-!
# Order six, whole-number disparities: the framework's rules, and the case they leave

2026-09-24.  A subject at order six has at most five disparities.  Split them by divisibility
by `6`: `M` the multiples, `E` the non-multiples.  A non-multiple `e` costs
`max 2 (gcd e 6)`, which is `3` when `3 ∣ e` and `2` otherwise (`cost_six`).

* **At most four disparities**: settled at `1/6` by the four-difference result, which reaches
  order six (`lonely_six_of_card_le_four`).  So everything below is about five.
* **`M = 0`**: the instant `1/6` is lonely — R6 at `q = 6` (`lonely_six_of_no_multiple`).  More
  generally `1/q` is lonely for any `q ≤ 6` dividing no disparity (`lonely_six_of_no_multiple_of`);
  at order six the new conditions are `q = 4` and `q = 5`, since `q = 2, 3` imply `q = 6`.
* **The first reading**: if every disparity lies in `[m, 5m]`, the instant `1/(6m)` is lonely
  (`lonely_six_of_spread`).
* **The descent**: if `∑_{e ∈ E} max 2 (gcd e 6) < 6` — one non-multiple, or two not both divisible
  by `3` — the shift budget passes the set to the cofactors of its multiples, at most four of
  them, which the four-difference result settles at `1/6` (`lonely_six_of_descent`).
* **The divisible flank**: at a multiple `e` of `6`, with the other multiples already in the band
  at the flank's first opening, a shift `k < 6` that no non-multiple blocks exhibits the lonely
  opening `(6kE + 1)/(6e)`, `e = 6E` (`lonely_six_of_freeFlank`).  This is the exact condition
  behind R4, R4b, the overlap rule and the named unit: each of them produces such a `k`.  R4 is
  stated on its own (`lonely_six_of_largest_multiple`, budget `φ(6) = 2`).  R4b's budget is the
  descent's, so at order six it settles nothing the descent does not.
* **R8, the fast runner**: if the largest disparity exceeds five times every other, the four slow
  ones are lonely at `1/5` by the order-five whole-number theorem (`lonely_five_nat`), and the fast
  runner carries that up (`lonely_six_of_fast`).  Only whole-number order five is used.

What is left (`lonely_six_or_residual`) is `SixResidual`: five disparities, each of `4`, `5`, `6`
dividing one of them, spread wider than a factor of five, with the multiples of `6` split as
`(M, |E|) = (1, 4)` or `(2, 3)`, or `(3, 2)` with every disparity divisible by `3`; no multiple of
`6` a free flank; and no fast runner.

Everything here is proved; no `sorry`, no `native_decide`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

namespace LRC.OrderSixN

open MomentIterationN LRC.SpecN LRC.Descent LRC.Resonance LRC.FlankFinite

instance fact_two_le_six : Fact (2 ≤ 6) := ⟨by norm_num⟩

/-! ## 1. the cost of a non-multiple -/

/-- **The cost of a non-multiple of six**: `3` when `3` divides it, `2` otherwise. -/
theorem cost_six {e : ℕ} (h : ¬ 6 ∣ e) :
    max 2 (Nat.gcd e 6) = 2 + if 3 ∣ e then 1 else 0 := by
  have h6 : e % 6 ≠ 0 := fun h0 => h (Nat.dvd_of_mod_eq_zero h0)
  rw [Nat.gcd_comm, Nat.gcd_rec]
  by_cases h3 : 3 ∣ e
  · rw [if_pos h3, show e % 6 = 3 by omega]
    decide
  · rw [if_neg h3]
    have : e % 6 = 1 ∨ e % 6 = 2 ∨ e % 6 = 4 ∨ e % 6 = 5 := by omega
    rcases this with h' | h' | h' | h' <;> rw [h'] <;> decide

/-- **The total cost** of a set of non-multiples is twice its size, plus one for each member
divisible by `3`. -/
theorem cost_sum_six {E : Finset ℕ} (hE : ∀ e ∈ E, ¬ 6 ∣ e) :
    ∑ e ∈ E, max 2 (Nat.gcd e 6) = 2 * E.card + (E.filter (fun e => 3 ∣ e)).card := by
  rw [Finset.sum_congr rfl (fun e he => cost_six (hE e he)), Finset.sum_add_distrib,
    Finset.sum_const, smul_eq_mul, Finset.card_filter, mul_comm]

/-! ## 2. the rules -/

/-- At most four positive disparities are lonely at `1/6`. -/
theorem lonely_six_of_card_le_four {S : Finset ℕ} (hpos : ∀ d ∈ S, 0 < d) (hc : S.card ≤ 4) :
    ∃ t : ℝ, 0 < t ∧ ∀ d ∈ S, (6 : ℝ)⁻¹ ≤ circDist ((d : ℝ) * t) := by
  obtain ⟨t, ht, hl⟩ := exists_lonely_of_card_le_four (n := 6)
    (ds := S.image (fun d : ℕ => (d : ℝ))) (by norm_num)
    (by
      intro x hx
      obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hx
      exact_mod_cast hpos d hd)
    (le_trans Finset.card_image_le hc)
  refine ⟨t, ht, fun d hd => ?_⟩
  have := hl (d : ℝ) (Finset.mem_image_of_mem _ hd)
  simpa using this

/-- **No multiple of `q`, for some `q ≤ 6`**: the instant `1/q` is lonely at `1/6`. -/
theorem lonely_six_of_no_multiple_of {S : Finset ℕ} {q : ℕ} (hq : 0 < q) (hq6 : q ≤ 6)
    (h : ∀ d ∈ S, ¬ q ∣ d) :
    ∃ t : ℝ, 0 < t ∧ ∀ d ∈ S, (6 : ℝ)⁻¹ ≤ circDist ((d : ℝ) * t) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  refine ⟨1 / q, by positivity, fun d hd => ?_⟩
  have hnd : ¬ ((q : ℕ) : ℤ) ∣ (d : ℤ) := by exact_mod_cast h d hd
  have hc := ConstructionN.circDist_int_div (n := q) hq hnd
  have heq : ((d : ℤ) : ℝ) / ((q : ℕ) : ℝ) = (d : ℝ) * (1 / q) := by push_cast; ring
  rw [heq] at hc
  have hle : (6 : ℝ)⁻¹ ≤ (q : ℝ)⁻¹ := inv_anti₀ hq0 (by exact_mod_cast hq6)
  exact le_trans hle hc

/-- **No multiple of six**: the instant `1/6` is lonely (R6 at `q = 6`). -/
theorem lonely_six_of_no_multiple {S : Finset ℕ} (h : ∀ d ∈ S, ¬ 6 ∣ d) :
    ∃ t : ℝ, 0 < t ∧ ∀ d ∈ S, (6 : ℝ)⁻¹ ≤ circDist ((d : ℝ) * t) :=
  lonely_six_of_no_multiple_of (by norm_num) le_rfl h

/-- A point in `[1/6, 5/6]` is clear at `1/6`. -/
theorem sixth_le_circDist_of_band {z : ℝ} (h1 : 1 / 6 ≤ z) (h2 : z ≤ 5 / 6) :
    (6 : ℝ)⁻¹ ≤ circDist z := by
  unfold circDist
  rw [Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩]
  exact le_min (by linarith) (by linarith)

/-- **The first reading.**  If every disparity lies in `[m, 5m]`, the instant `1/(6m)` is lonely:
each disparity reads between `1/6` and `5/6`. -/
theorem lonely_six_of_spread {S : Finset ℕ} {m : ℕ} (hm : 0 < m) (hmin : ∀ d ∈ S, m ≤ d)
    (hmax : ∀ d ∈ S, d ≤ 5 * m) :
    ∃ t : ℝ, 0 < t ∧ ∀ d ∈ S, (6 : ℝ)⁻¹ ≤ circDist ((d : ℝ) * t) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  refine ⟨1 / (6 * m), by positivity, fun d hd => ?_⟩
  have h1 : (m : ℝ) ≤ d := by exact_mod_cast hmin d hd
  have h2 : (d : ℝ) ≤ 5 * m := by exact_mod_cast hmax d hd
  apply sixth_le_circDist_of_band
  · rw [mul_one_div, le_div_iff₀ (by positivity)]; linarith
  · rw [mul_one_div, div_le_iff₀ (by positivity)]; linarith

/-- **The descent.**  If the non-multiples of `6` cost less than `6` in all and there are at most
four multiples, the set is lonely at `1/6`: the shift budget passes it to the cofactors. -/
theorem lonely_six_of_descent {S : Finset ℕ} (hpos : ∀ d ∈ S, 0 < d)
    (hcost : ∑ e ∈ S.filter (fun d => ¬ 6 ∣ d), max 2 (Nat.gcd e 6) < 6)
    (hM : (S.filter (fun d => 6 ∣ d)).card ≤ 4) :
    ∃ t : ℝ, 0 < t ∧ ∀ d ∈ S, (6 : ℝ)⁻¹ ≤ circDist ((d : ℝ) * t) := by
  classical
  set E := S.filter (fun d => ¬ 6 ∣ d) with hEdef
  set C : Finset ℕ := (S.filter (fun d => 6 ∣ d)).image (fun d => d / 6) with hCdef
  have hCpos : ∀ m ∈ C, 0 < m := by
    intro m hm
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hm
    obtain ⟨hdS, h6⟩ := Finset.mem_filter.mp hd
    exact Nat.div_pos (Nat.le_of_dvd (hpos d hdS) h6) (by norm_num)
  obtain ⟨τ, hτ, hC⟩ := lonely_six_of_card_le_four hCpos (le_trans Finset.card_image_le hM)
  obtain ⟨t, ht, hEt, hMt⟩ := (lonely_multi_descent_iff (n := 6) (by norm_num) E C.toList hcost).mpr
    ⟨τ, hτ, fun m hm => by simpa using hC m (Finset.mem_toList.mp hm)⟩
  refine ⟨t, ht, fun d hd => ?_⟩
  by_cases h6 : 6 ∣ d
  · obtain ⟨m, rfl⟩ := h6
    have hmC : m ∈ C.toList := Finset.mem_toList.mpr (Finset.mem_image.mpr
      ⟨6 * m, Finset.mem_filter.mpr ⟨hd, dvd_mul_right 6 m⟩, by omega⟩)
    simpa using hMt m hmC
  · simpa using hEt d (Finset.mem_filter.mpr ⟨hd, h6⟩)

/-- **A free flank at a multiple of six.**  The multiple `e = 6E` is a free flank when every other
multiple of `6` reads in the band `[e, 5e]` modulo `6e` at the first opening, and some shift
`k < 6` is blocked by no non-multiple `d`: `(d·k + ⌊d/e⌋) mod 6` is neither `0` nor `5`. -/
def FreeFlank (S : Finset ℕ) (e : ℕ) : Prop :=
  (∀ d ∈ S, d ≠ e → 6 ∣ d → e ≤ d % (6 * e) ∧ d % (6 * e) ≤ 5 * e) ∧
    ∃ k, k < 6 ∧ ∀ d ∈ S, ¬ 6 ∣ d → (d * k + d / e) % 6 ≠ 0 ∧ (d * k + d / e) % 6 ≠ 5

/-- **The divisible flank, exact form.**  A free flank hosts a lonely opening, at
`t = (6·k·E + 1)/(6e)` for the free shift `k`. -/
theorem lonely_six_of_freeFlank {S : Finset ℕ} (hpos : ∀ d ∈ S, 0 < d) {e : ℕ} (heS : e ∈ S)
    (he6 : 6 ∣ e) (hfree : FreeFlank S e) :
    ∃ t : ℝ, 0 < t ∧ ∀ d ∈ S, (6 : ℝ)⁻¹ ≤ circDist ((d : ℝ) * t) := by
  classical
  obtain ⟨hmult, k, hk, hks⟩ := hfree
  set L := (S.erase e).toList with hL
  have hmemL : ∀ d ∈ L, d ∈ S ∧ d ≠ e := fun d hd => by
    have := Finset.mem_toList.mp hd
    exact ⟨Finset.mem_of_mem_erase this, Finset.ne_of_mem_erase this⟩
  have hfw : flankWorks 6 (e :: L) e = true :=
    flankWorks_of_free_shift (n := 6) L e (hpos e heS) he6
      (fun d hd h6 => hmult d (hmemL d hd).1 (hmemL d hd).2 h6) k hk
      (fun d hd h6 => hks d (hmemL d hd).1 h6)
  obtain ⟨j, hj⟩ := lonely_of_flankWorks (n := 6) (e :: L) e (hpos e heS) hfw
  refine ⟨Flanks.flankOpening 6 (e : ℝ) j,
    Flanks.flankOpening_pos (n := 6) (by exact_mod_cast hpos e heS) j, fun d hd => ?_⟩
  have hdL : d ∈ e :: L := by
    by_cases h : d = e
    · rw [h]; exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (Finset.mem_toList.mpr (Finset.mem_erase.mpr ⟨h, hd⟩))
  simpa using hj d hdL

/-- **R4 at order six.**  One multiple of `6`, the largest disparity, and at most one of the
others coprime to `6` (the budget `φ(6) = 2`): the divisible flank opens. -/
theorem lonely_six_of_largest_multiple {S : Finset ℕ} (hpos : ∀ d ∈ S, 0 < d)
    {e : ℕ} (heS : e ∈ S) (he6 : 6 ∣ e)
    (hothers : ∀ d ∈ S, d ≠ e → ¬ 6 ∣ d) (hlarg : ∀ d ∈ S, d ≤ e)
    (hcop : ((S.erase e).filter (fun d => Nat.Coprime d 6)).card ≤ 1) :
    ∃ t : ℝ, 0 < t ∧ ∀ d ∈ S, (6 : ℝ)⁻¹ ≤ circDist ((d : ℝ) * t) := by
  classical
  set L := (S.erase e).toList with hL
  have hmemL : ∀ d ∈ L, d ∈ S ∧ d ≠ e := fun d hd => by
    have := Finset.mem_toList.mp hd
    exact ⟨Finset.mem_of_mem_erase this, Finset.ne_of_mem_erase this⟩
  have hlen : (L.filter (fun d => Nat.Coprime d 6)).length
      = ((S.erase e).filter (fun d => Nat.Coprime d 6)).card := by
    rw [hL, ← Multiset.coe_card, ← Multiset.filter_coe, Finset.coe_toList, Finset.card_def,
      Finset.filter_val]
  have htot : Nat.totient 6 = 2 := by decide
  have hfw : flankWorks 6 (e :: L) e = true :=
    flankWorks_of_dvd_totient (n := 6) L e (hpos e heS) he6
      (fun d hd => hothers d (hmemL d hd).1 (hmemL d hd).2)
      (fun d hd => lt_of_le_of_ne (hlarg d (hmemL d hd).1) (hmemL d hd).2)
      (by rw [htot, hlen]; omega)
  obtain ⟨j, hj⟩ := lonely_of_flankWorks (n := 6) (e :: L) e (hpos e heS) hfw
  refine ⟨Flanks.flankOpening 6 (e : ℝ) j,
    Flanks.flankOpening_pos (n := 6) (by exact_mod_cast hpos e heS) j, fun d hd => ?_⟩
  have hdL : d ∈ e :: L := by
    by_cases h : d = e
    · rw [h]; exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (Finset.mem_toList.mpr (Finset.mem_erase.mpr ⟨h, hd⟩))
  simpa using hj d hdL

/-- **R8, the fast runner, at order six.**  If one disparity `V` exceeds five times every other,
the slow ones — at most four whole numbers — are lonely at `1/5` (`lonely_five_nat`), and the fast
runner carries that to a lonely instant at `1/6`. -/
theorem lonely_six_of_fast {S : Finset ℕ} (hpos : ∀ d ∈ S, 0 < d) (hcard : S.card ≤ 5)
    {V : ℕ} (hVS : V ∈ S) (hfast : ∀ s ∈ S, s ≠ V → 5 * s < V) :
    ∃ t : ℝ, 0 < t ∧ ∀ d ∈ S, (6 : ℝ)⁻¹ ≤ circDist ((d : ℝ) * t) := by
  classical
  set W := S.erase V with hW
  have hWc : W.card ≤ 4 := by rw [hW, Finset.card_erase_of_mem hVS]; omega
  obtain ⟨τ, hτ, hlow⟩ := OrderFiveN.lonely_five_nat W
    (fun d hd => hpos d (Finset.mem_of_mem_erase hd)) hWc
  have h65 : ((6 : ℕ) : ℝ) - 1 = 5 := by norm_num
  obtain ⟨t, ht, hl⟩ := lonely_of_fast_runner (n := 6) (S := W.image (fun d : ℕ => (d : ℝ)))
    (by
      intro x hx
      obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hx
      exact_mod_cast hpos d (Finset.mem_of_mem_erase hd))
    (V := (V : ℝ)) (by exact_mod_cast hpos V hVS)
    (by
      intro x hx
      obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hx
      rw [h65]
      exact_mod_cast hfast d (Finset.mem_of_mem_erase hd) (Finset.ne_of_mem_erase hd))
    hτ
    (by
      intro x hx
      obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hx
      rw [h65]
      exact hlow d hd)
  refine ⟨t, ht, fun d hd => ?_⟩
  have hmem : (d : ℝ) ∈ insert (V : ℝ) (W.image (fun d : ℕ => (d : ℝ))) := by
    by_cases h : d = V
    · rw [h]; exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_erase.mpr ⟨h, hd⟩))
  simpa using hl (d : ℝ) hmem

/-! ## 3. the case analysis -/

/-- **The order-six residual**, stated by its divisibility structure: five disparities; `4`, `5`
and `6` each divide one of them (so no `1/q` rule applies); not all within a factor of five of
the least (so the first reading fails); the multiples of `6` split as `(M, |E|) = (1, 4)` or
`(2, 3)`, or `(3, 2)` with every disparity divisible by `3` (so the descent's budget is spent); no
multiple of `6` is a free flank; and no disparity is more than five times every other. -/
structure SixResidual (S : Finset ℕ) : Prop where
  card_eq : S.card = 5
  four : ∃ d ∈ S, 4 ∣ d
  five : ∃ d ∈ S, 5 ∣ d
  spread : ∃ a ∈ S, ∃ b ∈ S, 5 * a < b
  shape : ((S.filter (fun d => 6 ∣ d)).card = 1 ∧ (S.filter (fun d => ¬ 6 ∣ d)).card = 4) ∨
    ((S.filter (fun d => 6 ∣ d)).card = 2 ∧ (S.filter (fun d => ¬ 6 ∣ d)).card = 3) ∨
    ((S.filter (fun d => 6 ∣ d)).card = 3 ∧ ∀ d ∈ S, 3 ∣ d)
  no_free_flank : ∀ e ∈ S, 6 ∣ e → ¬ FreeFlank S e
  not_fast : ∀ V ∈ S, ∃ s ∈ S, s ≠ V ∧ V ≤ 5 * s

/-- **Order six, whole numbers.**  A set of at most five positive disparities, not all divisible
by `6`, is lonely at `1/6`, or it is in `SixResidual`. -/
theorem lonely_six_or_residual {S : Finset ℕ} (hpos : ∀ d ∈ S, 0 < d) (hcard : S.card ≤ 5)
    (hprim : ∃ d ∈ S, ¬ 6 ∣ d) :
    (∃ t : ℝ, 0 < t ∧ ∀ d ∈ S, (6 : ℝ)⁻¹ ≤ circDist ((d : ℝ) * t)) ∨ SixResidual S := by
  classical
  by_cases hc4 : S.card ≤ 4
  · exact Or.inl (lonely_six_of_card_le_four hpos hc4)
  have hc5 : S.card = 5 := by omega
  by_cases h4 : ∃ d ∈ S, 4 ∣ d
  swap
  · push Not at h4
    exact Or.inl (lonely_six_of_no_multiple_of (by norm_num) (by norm_num) h4)
  by_cases h5 : ∃ d ∈ S, 5 ∣ d
  swap
  · push Not at h5
    exact Or.inl (lonely_six_of_no_multiple_of (by norm_num) (by norm_num) h5)
  by_cases h6 : ∃ d ∈ S, 6 ∣ d
  swap
  · push Not at h6
    exact Or.inl (lonely_six_of_no_multiple h6)
  by_cases hsp : ∃ a ∈ S, ∃ b ∈ S, 5 * a < b
  swap
  · push Not at hsp
    have hne : S.Nonempty := Finset.card_pos.mp (by omega)
    set m := S.min' hne with hm
    exact Or.inl (lonely_six_of_spread (hpos m (S.min'_mem hne)) (fun d hd => S.min'_le d hd)
      (fun d hd => hsp m (S.min'_mem hne) d hd))
  have hsplit : (S.filter (fun d => 6 ∣ d)).card + (S.filter (fun d => ¬ 6 ∣ d)).card = 5 := by
    rw [Finset.card_filter_add_card_filter_not, hc5]
  have hE1 : 1 ≤ (S.filter (fun d => ¬ 6 ∣ d)).card := by
    obtain ⟨d, hd, h⟩ := hprim
    exact Finset.card_pos.mpr ⟨d, Finset.mem_filter.mpr ⟨hd, h⟩⟩
  have hM1 : 1 ≤ (S.filter (fun d => 6 ∣ d)).card := by
    obtain ⟨d, hd, h⟩ := h6
    exact Finset.card_pos.mpr ⟨d, Finset.mem_filter.mpr ⟨hd, h⟩⟩
  by_cases hcost : ∑ e ∈ S.filter (fun d => ¬ 6 ∣ d), max 2 (Nat.gcd e 6) < 6
  · exact Or.inl (lonely_six_of_descent hpos hcost (by omega))
  by_cases hff : ∃ e ∈ S, 6 ∣ e ∧ FreeFlank S e
  · obtain ⟨e, heS, he6, hfree⟩ := hff
    exact Or.inl (lonely_six_of_freeFlank hpos heS he6 hfree)
  by_cases hfast : ∃ V ∈ S, ∀ s ∈ S, s ≠ V → 5 * s < V
  · obtain ⟨V, hVS, hV⟩ := hfast
    exact Or.inl (lonely_six_of_fast hpos hcard hVS hV)
  right
  push Not at hcost hff hfast
  have hsum := cost_sum_six (E := S.filter (fun d => ¬ 6 ∣ d)) (fun e he => (Finset.mem_filter.mp he).2)
  rw [hsum] at hcost
  have h3le : ((S.filter (fun d => ¬ 6 ∣ d)).filter (fun e => 3 ∣ e)).card
      ≤ (S.filter (fun d => ¬ 6 ∣ d)).card := Finset.card_filter_le _ _
  refine ⟨hc5, h4, h5, hsp, ?_, hff, hfast⟩
  rcases (show (S.filter (fun d => ¬ 6 ∣ d)).card = 4 ∨ (S.filter (fun d => ¬ 6 ∣ d)).card = 3 ∨
      (S.filter (fun d => ¬ 6 ∣ d)).card = 2 by omega) with hE | hE | hE
  · exact Or.inl ⟨by omega, hE⟩
  · exact Or.inr (Or.inl ⟨by omega, hE⟩)
  · refine Or.inr (Or.inr ⟨by omega, fun d hd => ?_⟩)
    by_cases hd6 : 6 ∣ d
    · exact (show 3 ∣ 6 by norm_num).trans hd6
    · have hall := Finset.filter_card_eq
        (show ((S.filter (fun d => ¬ 6 ∣ d)).filter (fun e => 3 ∣ e)).card
          = (S.filter (fun d => ¬ 6 ∣ d)).card by omega)
      exact hall d (Finset.mem_filter.mpr ⟨hd, hd6⟩)

end LRC.OrderSixN
