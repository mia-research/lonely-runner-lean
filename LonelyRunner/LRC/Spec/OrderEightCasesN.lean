import LonelyRunner.LRC.Spec.RealEightN
import LonelyRunner.LRC.Spec.OrderSixN
import LonelyRunner.LRC.Spec.FastRunnerN
import LonelyRunner.LRC.Spec.ShiftedTotientN
import LonelyRunner.LRC.Spec.MirrorN
import LonelyRunner.LRC.Spec.FastPairEightN
import LonelyRunner.LRC.Spec.BlockSplitEightN

/-!
# Order eight, whole-number disparities: the framework's rules, and the case they leave

2026-09-25.  A subject at order eight has at most seven disparities.  By `RealEightN` the real
target `LRC.Spec.ExistenceAt8` is equivalent to its whole-number case, so this file works with
positive whole numbers only.  It is `OrderSixN` one order up, with one difference that makes it
stronger: order seven is native, so every set of at most **six** disparities is lonely at
`1/7 ≥ 1/8`, and every step that passes to cofactors lands there.

* **At most six disparities**: order seven (`lonely_eight_of_card_le_six`).  So the open part is
  `card = 7` exactly.
* **Halving**: if every disparity is even, a lonely instant `τ` of the halves gives `τ/2`
  (`lonely_eight_of_half`), and generally any common factor `g ≥ 2` divides out, `τ` giving `τ/g`
  (`lonely_eight_of_common_factor`).  So every case below may take the disparities with no common
  factor — which is a rule not applying, not a primitivity hypothesis.
* **R6**: `1/q` is lonely for any `q ≤ 8` dividing no disparity (`lonely_eight_of_no_multiple_of`).
  Since `2 ∣ 6`, `3 ∣ 6` and `4 ∣ 8`, the conditions that remain are `q = 5, 6, 7, 8`.
* **R1, the first reading**: every disparity in `[m, 7m]` gives `1/(8m)` (`lonely_eight_of_spread`).
* **The descent**: if the non-multiples `e` of `8` cost `∑ max 2 (gcd e 8) < 8`, the shift budget
  passes the set to the cofactors of its multiples, at most six of them, which order seven
  settles (`lonely_eight_of_descent`).  The cost is `4` when `e ≡ 4 (mod 8)` and `2` otherwise.
* **The free flank**: at a multiple `e = 8E` of `8`, with the other multiples of `8` in the band at
  the flank's first opening, a shift `k < 8` that no non-multiple blocks exhibits the lonely
  opening at `j = k·E` (`lonely_eight_of_freeFlank`).
* **R4, the shifted flank**: one multiple of `8`, the largest disparity, and at most three odd
  disparities among the others — the budget `φ(8) = 4` (`lonely_eight_of_largest_multiple`).
* **R8, the fast runner**: a disparity more than seven times every other; the six slow ones are
  lonely at `1/7` by order seven (`lonely_eight_of_fast`).
* **§15, first-lap clearance** (manuscript Theorems 15.40–15.43): at a flank `e` and an index `k`,
  every other disparity `d` has `e ≤ d·(8k + 1) ≤ 7e` — no wraparound — and the opening
  `(8k + 1)/(8e)` is lonely (`lonely_eight_of_firstLap`).  R1 is its `k = 0` case at the least flank.
  **Standing (author, 2026-09-25): kept provisionally; its nativeness is in doubt.**  No lower order
  used it — orders five to seven needed only R1 — and on the 7-subsets of `[1, 30]` it removes 13
  residual sets the `−7` opening does not (`experiments/nN/eight_residual_count_v1.py`).  It stays
  only if an order-eight proof needs it; nothing else here depends on it.
* **§15, the `−7` opening** (Theorems 15.31–15.35, 15.70): at the index `k = e − 1` every reading
  is `−7d mod 8e`, whatever the index; if all of them lie in `[e, 7e]` the opening is lonely
  (`lonely_eight_of_minusSeven`).  At the largest flank this is R1 (the tiny-mover law, 15.33).
* **§15, the last class** (Theorems 15.27–15.30): movers `p/q < 1` with every `q ≤ 7` at the
  largest flank.  At order eight this is **inside R1** (`lastClass_is_spread`): `q ≤ 7` gives
  `e ≤ 7·gcd(d, e) ≤ 7d`.  So it adds no case; it is recorded as the inclusion.
* **The rational opening**: at a flank `e = N·M` and the index `i·M`, the instant is
  `t = i/N + 1/(8e)` — R6's rational `i/N` moved to the flank's first opening.  The reading of `d` is
  `M·((8·(i·d mod N) + ⌊d/M⌋) mod 8N) + (d mod M)` (`rationalOpening_reading`, every order), so the
  condition is a residue condition moving affinely in `i` with slope `d` (`RationalOpening8`,
  `lonely_eight_at_rationalOpening`, which names the instant).  The case taken here is `N ∣ gcd(e, 8)`:
  a flank has `gcd(e, 8)` such openings, which is where even and odd flanks part — an odd flank has
  only `1/(8e)`.  The free flank is its `N = 8` case at a multiple of `8`.  On the 7-subsets of
  `[1, 30]` it takes the residual from 12,309 sets to 5,816
  (`experiments/nN/eight_residual_count_v2.py`).  Larger `N` are left as later cases: at `N = e`
  the condition is Theorem 10 itself, so an unbounded `N` would make the residual the bare
  obligation.
* **Thirds**, the rational opening at `N = 3`: `t = i/3 + 1/(8e)` at a flank `e = 3M`.  The multiples
  of `3` do not see `i` and need the flank's band; each non-multiple blocks at most one of the two
  units (`thirds_clear_one_or_two`), so the budget is `φ(3) = 2` (`lonely_eight_of_thirds`: the
  multiples in the band and at most one non-multiple blocking).  As a case it takes the residual
  from 5,816 sets to 1,151 (`experiments/nN/eight_residual_count_v3.py`).
* **Fifths**, `N = 5`: `t = i/5 + 1/(8e)` at a flank `e = 5M`.  Each non-multiple of `5` blocks at
  most two of the `φ(5) = 4` units (`fifths_clear_one_of_three`); at most one blocking non-multiple
  leaves a unit free (`lonely_eight_of_fifths`).  As a case it takes the residual from 1,151 sets
  to 100 (`experiments/nN/eight_residual_count_v4.py`).
* **Sixths, sevenths, ninths** (§2f), by their exact conditions, with the common factor divided
  out: on the 7-subsets of `[1, 30]` and of `[1, 36]` the residual is **empty**, and on `[1, 40]`
  seven sets remain, needing `N = 12, 15, 16` (`experiments/nN/eight_residual_count_v5.py`).  The
  counts are of a finite window; the residual itself is infinite, and what closes it is a proof,
  not a range.

Every §15 condition is a certificate at a named opening, and all of them go through one bridge,
`lonely_eight_of_opening`: the band `d·(8k + 1) mod 8e ∈ [e, 7e]` at every disparity is the lonely
opening `(8k + 1)/(8e)` (the residue-band rule `lonely_of_mirror_band` at `q = 8e`).

What is left is `EightResidual` (`lonely_eight_or_residual`), and the conjecture at eight runners
for every real arrangement is **equivalent** to every residual set being lonely
(`existenceAt8_iff_residual`, `lonelyRunnerAt8_of_residual`).

Everything here is proved; no `sorry`, no `native_decide`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

namespace LRC.OrderEightN

open MomentIterationN LRC.SpecN LRC.Descent LRC.Resonance LRC.FlankFinite

instance fact_two_le_eight : Fact (2 ≤ 8) := ⟨by norm_num⟩

/-! ## 1. the cost of a non-multiple of eight -/

/-- **The cost of a non-multiple of eight**: `4` when it is `4 mod 8`, `2` otherwise. -/
theorem cost_eight {e : ℕ} (h : ¬ 8 ∣ e) :
    max 2 (Nat.gcd e 8) = 2 + if 4 ∣ e then 2 else 0 := by
  have h8 : e % 8 ≠ 0 := fun h0 => h (Nat.dvd_of_mod_eq_zero h0)
  rw [Nat.gcd_comm, Nat.gcd_rec]
  by_cases h4 : 4 ∣ e
  · rw [if_pos h4, show e % 8 = 4 by omega]
    decide
  · rw [if_neg h4]
    have : e % 8 = 1 ∨ e % 8 = 2 ∨ e % 8 = 3 ∨ e % 8 = 5 ∨ e % 8 = 6 ∨ e % 8 = 7 := by omega
    rcases this with h' | h' | h' | h' | h' | h' <;> rw [h'] <;> decide

/-! ## 2. the rules -/

/-- **At most six disparities**: lonely at `1/7` by order seven, hence at `1/8`. -/
theorem lonely_eight_of_card_le_six {S : Finset ℕ} (hpos : ∀ d ∈ S, 0 < d) (hc : S.card ≤ 6) :
    ∃ t : ℝ, 0 < t ∧ ∀ d ∈ S, (8 : ℝ)⁻¹ ≤ circDist ((d : ℝ) * t) := by
  obtain ⟨t, ht, hl⟩ := LRC.OrderSevenN.lonely_seven_nat S hpos hc
  exact ⟨t, ht, fun d hd => le_trans (by norm_num) (hl d hd)⟩

/-- **Halving.**  If every disparity is even, a lonely instant `τ` of the halves gives `τ/2`. -/
theorem lonely_eight_of_half {S : Finset ℕ} (h2 : ∀ d ∈ S, 2 ∣ d) {τ : ℝ} (hτ : 0 < τ)
    (hl : ∀ d ∈ S.image (fun d : ℕ => d / 2), (8 : ℝ)⁻¹ ≤ circDist ((d : ℝ) * τ)) :
    ∃ t : ℝ, 0 < t ∧ ∀ d ∈ S, (8 : ℝ)⁻¹ ≤ circDist ((d : ℝ) * t) := by
  refine ⟨τ / 2, by positivity, fun d hd => ?_⟩
  have := hl (d / 2 : ℕ) (Finset.mem_image_of_mem _ hd)
  rw [Nat.cast_div (h2 d hd) (by norm_num), div_mul_eq_mul_div] at this
  rwa [mul_div_assoc] at this

/-- **A common factor**, generalising halving: if `g` divides every disparity, a lonely instant `τ`
of the quotients gives `τ/g`.  No primitivity is assumed anywhere; this is the rule that divides a
common factor out, and the residual records only that it does not apply. -/
theorem lonely_eight_of_common_factor {S : Finset ℕ} {g : ℕ} (hg : 0 < g) (hgd : ∀ d ∈ S, g ∣ d)
    {τ : ℝ} (hτ : 0 < τ)
    (hl : ∀ d ∈ S.image (fun d : ℕ => d / g), (8 : ℝ)⁻¹ ≤ circDist ((d : ℝ) * τ)) :
    ∃ t : ℝ, 0 < t ∧ ∀ d ∈ S, (8 : ℝ)⁻¹ ≤ circDist ((d : ℝ) * t) := by
  have hg' : (0 : ℝ) < g := by exact_mod_cast hg
  refine ⟨τ / g, by positivity, fun d hd => ?_⟩
  have := hl (d / g : ℕ) (Finset.mem_image_of_mem _ hd)
  rw [Nat.cast_div (hgd d hd) hg'.ne', div_mul_eq_mul_div] at this
  rwa [mul_div_assoc] at this

/-- **R6: no multiple of `q`, for some `q ≤ 8`**: the instant `1/q` is lonely at `1/8`. -/
theorem lonely_eight_of_no_multiple_of {S : Finset ℕ} {q : ℕ} (hq : 0 < q) (hq8 : q ≤ 8)
    (h : ∀ d ∈ S, ¬ q ∣ d) :
    ∃ t : ℝ, 0 < t ∧ ∀ d ∈ S, (8 : ℝ)⁻¹ ≤ circDist ((d : ℝ) * t) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  refine ⟨1 / q, by positivity, fun d hd => ?_⟩
  have hnd : ¬ ((q : ℕ) : ℤ) ∣ (d : ℤ) := by exact_mod_cast h d hd
  have hc := ConstructionN.circDist_int_div (n := q) hq hnd
  have heq : ((d : ℤ) : ℝ) / ((q : ℕ) : ℝ) = (d : ℝ) * (1 / q) := by push_cast; ring
  rw [heq] at hc
  have hle : (8 : ℝ)⁻¹ ≤ (q : ℝ)⁻¹ := inv_anti₀ hq0 (by exact_mod_cast hq8)
  exact le_trans hle hc

/-- A point in `[1/8, 7/8]` is clear at `1/8`. -/
theorem eighth_le_circDist_of_band {z : ℝ} (h1 : 1 / 8 ≤ z) (h2 : z ≤ 7 / 8) :
    (8 : ℝ)⁻¹ ≤ circDist z := by
  unfold circDist
  rw [Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩]
  exact le_min (by linarith) (by linarith)

/-- **R1, the first reading.**  If every disparity lies in `[m, 7m]`, the instant `1/(8m)` is
lonely: each disparity reads between `1/8` and `7/8`. -/
theorem lonely_eight_of_spread {S : Finset ℕ} {m : ℕ} (hm : 0 < m) (hmin : ∀ d ∈ S, m ≤ d)
    (hmax : ∀ d ∈ S, d ≤ 7 * m) :
    ∃ t : ℝ, 0 < t ∧ ∀ d ∈ S, (8 : ℝ)⁻¹ ≤ circDist ((d : ℝ) * t) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  refine ⟨1 / (8 * m), by positivity, fun d hd => ?_⟩
  have h1 : (m : ℝ) ≤ d := by exact_mod_cast hmin d hd
  have h2 : (d : ℝ) ≤ 7 * m := by exact_mod_cast hmax d hd
  apply eighth_le_circDist_of_band
  · rw [mul_one_div, le_div_iff₀ (by positivity)]; linarith
  · rw [mul_one_div, div_le_iff₀ (by positivity)]; linarith

/-- **The descent.**  If the non-multiples of `8` cost less than `8` in all and there are at most
six multiples, the set is lonely at `1/8`: the shift budget passes it to the cofactors, which
order seven settles. -/
theorem lonely_eight_of_descent {S : Finset ℕ} (hpos : ∀ d ∈ S, 0 < d)
    (hcost : ∑ e ∈ S.filter (fun d => ¬ 8 ∣ d), max 2 (Nat.gcd e 8) < 8)
    (hM : (S.filter (fun d => 8 ∣ d)).card ≤ 6) :
    ∃ t : ℝ, 0 < t ∧ ∀ d ∈ S, (8 : ℝ)⁻¹ ≤ circDist ((d : ℝ) * t) := by
  classical
  set E := S.filter (fun d => ¬ 8 ∣ d) with hEdef
  set C : Finset ℕ := (S.filter (fun d => 8 ∣ d)).image (fun d => d / 8) with hCdef
  have hCpos : ∀ m ∈ C, 0 < m := by
    intro m hm
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hm
    obtain ⟨hdS, h8⟩ := Finset.mem_filter.mp hd
    exact Nat.div_pos (Nat.le_of_dvd (hpos d hdS) h8) (by norm_num)
  obtain ⟨τ, hτ, hC⟩ := lonely_eight_of_card_le_six hCpos (le_trans Finset.card_image_le hM)
  obtain ⟨t, ht, hEt, hMt⟩ := (lonely_multi_descent_iff (n := 8) (by norm_num) E C.toList hcost).mpr
    ⟨τ, hτ, fun m hm => by simpa using hC m (Finset.mem_toList.mp hm)⟩
  refine ⟨t, ht, fun d hd => ?_⟩
  by_cases h8 : 8 ∣ d
  · obtain ⟨m, rfl⟩ := h8
    have hmC : m ∈ C.toList := Finset.mem_toList.mpr (Finset.mem_image.mpr
      ⟨8 * m, Finset.mem_filter.mpr ⟨hd, dvd_mul_right 8 m⟩, by omega⟩)
    simpa using hMt m hmC
  · simpa using hEt d (Finset.mem_filter.mpr ⟨hd, h8⟩)

/-- **A free flank at a multiple of eight.**  The multiple `e = 8E` is a free flank when every
other multiple of `8` reads in the band `[e, 7e]` modulo `8e` at the first opening, and some shift
`k < 8` is blocked by no non-multiple `d`: `(d·k + ⌊d/e⌋) mod 8` is neither `0` nor `7`. -/
def FreeFlank8 (S : Finset ℕ) (e : ℕ) : Prop :=
  (∀ d ∈ S, d ≠ e → 8 ∣ d → e ≤ d % (8 * e) ∧ d % (8 * e) ≤ 7 * e) ∧
    ∃ k, k < 8 ∧ ∀ d ∈ S, ¬ 8 ∣ d → (d * k + d / e) % 8 ≠ 0 ∧ (d * k + d / e) % 8 ≠ 7

/-- **The divisible flank, exact form.**  A free flank hosts a lonely opening, at `j = k·E` for
the free shift `k`. -/
theorem lonely_eight_of_freeFlank {S : Finset ℕ} (hpos : ∀ d ∈ S, 0 < d) {e : ℕ} (heS : e ∈ S)
    (he8 : 8 ∣ e) (hfree : FreeFlank8 S e) :
    ∃ t : ℝ, 0 < t ∧ ∀ d ∈ S, (8 : ℝ)⁻¹ ≤ circDist ((d : ℝ) * t) := by
  classical
  obtain ⟨hmult, k, hk, hks⟩ := hfree
  set L := (S.erase e).toList with hL
  have hmemL : ∀ d ∈ L, d ∈ S ∧ d ≠ e := fun d hd => by
    have := Finset.mem_toList.mp hd
    exact ⟨Finset.mem_of_mem_erase this, Finset.ne_of_mem_erase this⟩
  have hfw : flankWorks 8 (e :: L) e = true :=
    flankWorks_of_free_shift (n := 8) L e (hpos e heS) he8
      (fun d hd h8 => hmult d (hmemL d hd).1 (hmemL d hd).2 h8) k hk
      (fun d hd h8 => hks d (hmemL d hd).1 h8)
  obtain ⟨j, hj⟩ := lonely_of_flankWorks (n := 8) (e :: L) e (hpos e heS) hfw
  refine ⟨Flanks.flankOpening 8 (e : ℝ) j,
    Flanks.flankOpening_pos (n := 8) (by exact_mod_cast hpos e heS) j, fun d hd => ?_⟩
  have hdL : d ∈ e :: L := by
    by_cases h : d = e
    · rw [h]; exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (Finset.mem_toList.mpr (Finset.mem_erase.mpr ⟨h, hd⟩))
  simpa using hj d hdL

/-- **R4 at order eight.**  One multiple of `8`, the largest disparity, and at most three of the
others coprime to `8` (the budget `φ(8) = 4`): the divisible flank opens. -/
theorem lonely_eight_of_largest_multiple {S : Finset ℕ} (hpos : ∀ d ∈ S, 0 < d)
    {e : ℕ} (heS : e ∈ S) (he8 : 8 ∣ e)
    (hothers : ∀ d ∈ S, d ≠ e → ¬ 8 ∣ d) (hlarg : ∀ d ∈ S, d ≤ e)
    (hcop : ((S.erase e).filter (fun d => Nat.Coprime d 8)).card ≤ 3) :
    ∃ t : ℝ, 0 < t ∧ ∀ d ∈ S, (8 : ℝ)⁻¹ ≤ circDist ((d : ℝ) * t) := by
  classical
  set L := (S.erase e).toList with hL
  have hmemL : ∀ d ∈ L, d ∈ S ∧ d ≠ e := fun d hd => by
    have := Finset.mem_toList.mp hd
    exact ⟨Finset.mem_of_mem_erase this, Finset.ne_of_mem_erase this⟩
  have hlen : (L.filter (fun d => Nat.Coprime d 8)).length
      = ((S.erase e).filter (fun d => Nat.Coprime d 8)).card := by
    rw [hL, ← Multiset.coe_card, ← Multiset.filter_coe, Finset.coe_toList, Finset.card_def,
      Finset.filter_val]
  have htot : Nat.totient 8 = 4 := by decide
  have hfw : flankWorks 8 (e :: L) e = true :=
    flankWorks_of_dvd_totient (n := 8) L e (hpos e heS) he8
      (fun d hd => hothers d (hmemL d hd).1 (hmemL d hd).2)
      (fun d hd => lt_of_le_of_ne (hlarg d (hmemL d hd).1) (hmemL d hd).2)
      (by rw [htot, hlen]; omega)
  obtain ⟨j, hj⟩ := lonely_of_flankWorks (n := 8) (e :: L) e (hpos e heS) hfw
  refine ⟨Flanks.flankOpening 8 (e : ℝ) j,
    Flanks.flankOpening_pos (n := 8) (by exact_mod_cast hpos e heS) j, fun d hd => ?_⟩
  have hdL : d ∈ e :: L := by
    by_cases h : d = e
    · rw [h]; exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (Finset.mem_toList.mpr (Finset.mem_erase.mpr ⟨h, hd⟩))
  simpa using hj d hdL

/-- **R8, the fast runner, at order eight.**  If one disparity `V` exceeds seven times every
other, the slow ones — at most six whole numbers — are lonely at `1/7` by order seven, and the
fast runner carries that to a lonely instant at `1/8`. -/
theorem lonely_eight_of_fast {S : Finset ℕ} (hpos : ∀ d ∈ S, 0 < d) (hcard : S.card ≤ 7)
    {V : ℕ} (hVS : V ∈ S) (hfast : ∀ s ∈ S, s ≠ V → 7 * s < V) :
    ∃ t : ℝ, 0 < t ∧ ∀ d ∈ S, (8 : ℝ)⁻¹ ≤ circDist ((d : ℝ) * t) := by
  classical
  set W := S.erase V with hW
  have hWc : W.card ≤ 6 := by rw [hW, Finset.card_erase_of_mem hVS]; omega
  obtain ⟨τ, hτ, hlow⟩ := LRC.OrderSevenN.lonely_seven_nat W
    (fun d hd => hpos d (Finset.mem_of_mem_erase hd)) hWc
  have h87 : ((8 : ℕ) : ℝ) - 1 = 7 := by norm_num
  obtain ⟨t, ht, hl⟩ := lonely_of_fast_runner (n := 8) (S := W.image (fun d : ℕ => (d : ℝ)))
    (by
      intro x hx
      obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hx
      exact_mod_cast hpos d (Finset.mem_of_mem_erase hd))
    (V := (V : ℝ)) (by exact_mod_cast hpos V hVS)
    (by
      intro x hx
      obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hx
      rw [h87]
      exact_mod_cast hfast d (Finset.mem_of_mem_erase hd) (Finset.ne_of_mem_erase hd))
    hτ
    (by
      intro x hx
      obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hx
      rw [h87]
      exact hlow d hd)
  refine ⟨t, ht, fun d hd => ?_⟩
  have hmem : (d : ℝ) ∈ insert (V : ℝ) (W.image (fun d : ℕ => (d : ℝ))) := by
    by_cases h : d = V
    · rw [h]; exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_erase.mpr ⟨h, hd⟩))
  simpa using hl (d : ℝ) hmem

/-! ## 2b. the §15 conditions: certificates at named openings -/

/-- **The bridge.**  If every reading `d·(8k + 1) mod 8e` lies in `[e, 7e]`, the opening
`(8k + 1)/(8e)` of the flank `e` is lonely. -/
theorem lonely_eight_of_opening {S : Finset ℕ} {e : ℕ} (he : 0 < e) (k : ℕ)
    (h : ∀ d ∈ S, e ≤ d * (8 * k + 1) % (8 * e) ∧ d * (8 * k + 1) % (8 * e) ≤ 7 * e) :
    ∃ t : ℝ, 0 < t ∧ ∀ d ∈ S, (8 : ℝ)⁻¹ ≤ circDist ((d : ℝ) * t) := by
  have hl := lonely_of_mirror_band (n := 8) (q := 8 * e) (K := 8 * k + 1) (by omega) (by norm_num)
    (S := S) (fun d hd => by
      obtain ⟨h1, h2⟩ := h d hd
      constructor <;> omega)
  refine ⟨((8 * k + 1 : ℕ) : ℝ) / ((8 * e : ℕ) : ℝ), by positivity, fun d hd => ?_⟩
  simpa using hl d hd

/-- The flank's own reading at any of its openings is `e`: `e·(8k + 1) = 8e·k + e`. -/
theorem flank_reading (e k : ℕ) (he : 0 < e) : e * (8 * k + 1) % (8 * e) = e := by
  rw [show e * (8 * k + 1) = e + 8 * e * k by ring, Nat.add_mul_mod_self_left]
  exact Nat.mod_eq_of_lt (by omega)

/-- **First-lap clearance** (Theorems 15.40–15.43).  At a flank `e` and an index `k`, if every
other disparity has `e ≤ d·(8k + 1) ≤ 7e`, there is no wraparound and the opening `(8k + 1)/(8e)`
is lonely. -/
theorem lonely_eight_of_firstLap {S : Finset ℕ} {e : ℕ} (heS : e ∈ S) (he : 0 < e) (k : ℕ)
    (h : ∀ d ∈ S, d ≠ e → e ≤ d * (8 * k + 1) ∧ d * (8 * k + 1) ≤ 7 * e) :
    ∃ t : ℝ, 0 < t ∧ ∀ d ∈ S, (8 : ℝ)⁻¹ ≤ circDist ((d : ℝ) * t) := by
  refine lonely_eight_of_opening he k fun d hd => ?_
  by_cases hde : d = e
  · rw [hde, flank_reading e k he]; omega
  · obtain ⟨h1, h2⟩ := h d hd hde
    rw [Nat.mod_eq_of_lt (by omega)]
    exact ⟨h1, h2⟩

/-- At the index `k = e − 1` the numerator is `8e − 7`, and the reading of `d` is `8e·d − 7d`. -/
theorem minusSeven_numerator (d e : ℕ) (he : 0 < e) :
    d * (8 * (e - 1) + 1) = 8 * e * d - 7 * d := by
  obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  rw [show 8 * (e' + 1) * d = d * (8 * e' + 1) + 7 * d by ring, Nat.add_sub_cancel]

/-- **The `−7` opening** (Theorems 15.31–15.35, 15.70).  At the index `k = e − 1` every reading is
`8e·d − 7d ≡ −7d (mod 8e)`; if all of them lie in `[e, 7e]` the opening `(8e − 7)/(8e)` is
lonely. -/
theorem lonely_eight_of_minusSeven {S : Finset ℕ} {e : ℕ} (he : 0 < e)
    (h : ∀ d ∈ S, e ≤ (8 * e * d - 7 * d) % (8 * e) ∧ (8 * e * d - 7 * d) % (8 * e) ≤ 7 * e) :
    ∃ t : ℝ, 0 < t ∧ ∀ d ∈ S, (8 : ℝ)⁻¹ ≤ circDist ((d : ℝ) * t) :=
  lonely_eight_of_opening he (e - 1) fun d hd => by
    rw [minusSeven_numerator d e he]; exact h d hd

/-- **The last class is inside R1 at order eight** (Theorems 15.27–15.30).  At the largest flank
`e`, if every other disparity's denominator `e / gcd(d, e)` is at most `7`, then `e ≤ 7d` for every
disparity: `e = gcd(d, e)·(e / gcd(d, e)) ≤ 7·gcd(d, e) ≤ 7d`. -/
theorem lastClass_is_spread {S : Finset ℕ} (hpos : ∀ d ∈ S, 0 < d) {e : ℕ}
    (hq : ∀ d ∈ S, d ≠ e → e / Nat.gcd d e ≤ 7) : ∀ d ∈ S, e ≤ 7 * d := by
  intro d hd
  by_cases hde : d = e
  · subst hde; omega
  have hg : Nat.gcd d e ≤ d := Nat.le_of_dvd (hpos d hd) (Nat.gcd_dvd_left d e)
  have he : e = Nat.gcd d e * (e / Nat.gcd d e) := (Nat.mul_div_cancel' (Nat.gcd_dvd_right d e)).symm
  have := hq d hd hde
  calc e = Nat.gcd d e * (e / Nat.gcd d e) := he
    _ ≤ Nat.gcd d e * 7 := Nat.mul_le_mul_left _ this
    _ ≤ 7 * d := by omega

/-- **The last class, as a case**: settled by R1 at the least disparity. -/
theorem lonely_eight_of_lastClass {S : Finset ℕ} (hpos : ∀ d ∈ S, 0 < d) {e : ℕ} (heS : e ∈ S)
    (hlarg : ∀ d ∈ S, d ≤ e) (hq : ∀ d ∈ S, d ≠ e → e / Nat.gcd d e ≤ 7) :
    ∃ t : ℝ, 0 < t ∧ ∀ d ∈ S, (8 : ℝ)⁻¹ ≤ circDist ((d : ℝ) * t) := by
  have hne : S.Nonempty := ⟨e, heS⟩
  have h7 := lastClass_is_spread hpos hq
  exact lonely_eight_of_spread (hpos _ (S.min'_mem hne)) (fun d hd => S.min'_le d hd)
    (fun d hd => le_trans (hlarg d hd) (h7 _ (S.min'_mem hne)))

/-! ## 2c. the rational opening: `t = i/N + 1/(8e)` at a flank `e = N·M` -/

/-- Scaling a residue: `(b·a + c) mod b·d = b·(a mod d) + c` when `c < b`. -/
theorem mul_add_mod_mul {a b c d : ℕ} (h : c < b) :
    (b * a + c) % (b * d) = b * (a % d) + c := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp
  have e : b * a + c = (b * (a % d) + c) + (b * d) * (a / d) := by
    conv_lhs => rw [← Nat.mod_add_div a d]
    ring
  have hlt : b * (a % d) + c < b * d := by
    have := Nat.mod_lt a hd
    have : b * (a % d + 1) ≤ b * d := Nat.mul_le_mul_left b this
    nlinarith
  rw [e, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]

/-- **The reading at a rational opening**, at every order.  At the flank `N·M` and the index
`i·M`, the numerator is `n·(i·M) + 1`, and the disparity `d` reads
`M·((n·(i·d mod N) + ⌊d/M⌋) mod n·N) + (d mod M)`.  So the reading depends on `d` only through
`i·d mod N`, `⌊d/M⌋` and `d mod M`, and it moves affinely in `i` with slope `d`. -/
theorem rationalOpening_reading (n N M d i : ℕ) (hM : 0 < M) :
    d * (n * (i * M) + 1) % (n * (N * M)) =
      M * ((n * (i * d % N) + d / M) % (n * N)) + d % M := by
  have hX : d * (n * (i * M) + 1) =
      M * ((n * (i * d % N) + d / M) + (n * N) * (i * d / N)) + d % M := by
    calc d * (n * (i * M) + 1) = n * M * (i * d) + d := by ring
      _ = n * M * (N * (i * d / N) + i * d % N) + (M * (d / M) + d % M) := by
          rw [Nat.div_add_mod, Nat.div_add_mod]
      _ = _ := by ring
  rw [hX, show n * (N * M) = M * (n * N) by ring, mul_add_mod_mul (Nat.mod_lt d hM),
    Nat.add_mul_mod_self_left]

/-- The class condition puts the reading `M·c + r` in the band `[N·M, m·N·M]`. -/
theorem band_of_class {m N M c r : ℕ} (hr : r < M) (h1 : N ≤ c)
    (h2 : c < m * N ∨ (c = m * N ∧ r = 0)) :
    N * M ≤ M * c + r ∧ M * c + r ≤ m * (N * M) := by
  refine ⟨by nlinarith, ?_⟩
  rcases h2 with h2 | ⟨rfl, rfl⟩
  · have : M * (c + 1) ≤ M * (m * N) := Nat.mul_le_mul_left M h2
    nlinarith
  · nlinarith

/-- **One disparity's class condition** at the rational opening `(N, M, i)`: the class
`c = (8·(i·d mod N) + ⌊d/M⌋) mod 8N` lies in `[N, 7N)`, or equals `7N` with `M ∣ d`. -/
def ClassClear8 (N M i d : ℕ) : Prop :=
  N ≤ (8 * (i * d % N) + d / M) % (8 * N) ∧
    ((8 * (i * d % N) + d / M) % (8 * N) < 7 * N ∨
      ((8 * (i * d % N) + d / M) % (8 * N) = 7 * N ∧ d % M = 0))

/-- **The rational opening at order eight.**  At the flank `e = N·M` and the index `i·M`, the
class `c = (8·(i·d mod N) + ⌊d/M⌋) mod 8N` of every disparity lies in `[N, 7N)`, or equals `7N`
with `M ∣ d`. -/
def RationalOpening8 (S : Finset ℕ) (N M i : ℕ) : Prop :=
  ∀ d ∈ S, ClassClear8 N M i d

/-- The instant of the rational opening is `i/N + 1/(8·N·M)`: the rational `i/N` of R6, moved to
the flank's first opening. -/
theorem rationalOpening_instant (N M i : ℕ) (hN : 0 < N) (hM : 0 < M) :
    ((8 * (i * M) + 1 : ℕ) : ℝ) / ((8 * (N * M) : ℕ) : ℝ) = (i : ℝ) / N + 1 / (8 * (N * M)) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  push_cast
  field_simp

/-- **A rational opening is lonely**, at the named instant `t = i/N + 1/(8·N·M)`.  No hypothesis
that `N·M` is a disparity: the instant is lonely whenever the class condition holds.  The free flank
is the case `N = 8`; `N = 1` is the flank's first opening `1/(8e)`. -/
theorem lonely_eight_at_rationalOpening {S : Finset ℕ} {N M i : ℕ} (hN : 0 < N) (hM : 0 < M)
    (h : RationalOpening8 S N M i) :
    ∀ d ∈ S, (8 : ℝ)⁻¹ ≤ circDist ((d : ℝ) * ((i : ℝ) / N + 1 / (8 * (N * M)))) := by
  have hl := lonely_of_mirror_band (n := 8) (q := 8 * (N * M)) (K := 8 * (i * M) + 1)
    (Nat.mul_pos (by norm_num) (Nat.mul_pos hN hM)) (by norm_num) (S := S) (fun d hd => by
      rw [rationalOpening_reading 8 N M d i hM]
      obtain ⟨h1, h2⟩ := h d hd
      obtain ⟨b1, b2⟩ := band_of_class (m := 7) (Nat.mod_lt d hM) h1 h2
      generalize N * M = e at b1 b2
      constructor <;> omega)
  intro d hd
  have := hl d hd
  rwa [rationalOpening_instant N M i hN hM] at this

/-- **The rational opening, as a case.** -/
theorem lonely_eight_of_rationalOpening {S : Finset ℕ} {N M i : ℕ} (hN : 0 < N) (hM : 0 < M)
    (h : RationalOpening8 S N M i) :
    ∃ t : ℝ, 0 < t ∧ ∀ d ∈ S, (8 : ℝ)⁻¹ ≤ circDist ((d : ℝ) * t) :=
  ⟨(i : ℝ) / N + 1 / (8 * (N * M)), by positivity, lonely_eight_at_rationalOpening hN hM h⟩

/-! ## 2d. thirds: the rational opening at `N = 3`, and its `φ(3)` budget

At a flank `e = 3M` the instant is `t = i/3 + 1/(8e)`.  A multiple of `3` reads as at the flank's
first opening whatever `i` is, so it needs the flank's band, `d mod 8e ∈ [e, 7e]`.  A non-multiple
`d` with `s = i·d mod 3` reads `s/3` further on, and it is blocked only when its first-opening
reading falls within `1/8` of `−s/3`.  Those two arcs are disjoint, so **each non-multiple blocks
at most one of the two units `i = 1, 2`** (`thirds_clear_one_or_two`), and a non-multiple below the
flank blocks neither.  So the budget is `φ(3) = 2`, as `φ(8) = 4` is R4's: the multiples of `3` in
the band, and at most one non-multiple blocking, give a lonely instant (`lonely_eight_of_thirds`).
-/

/-- **Each non-multiple of `3` clears at `i = 1` or at `i = 2`.**  The classes at the two units are
`q + 8s` and `q − 8s` mod `24`, eight apart, and a blocked class is within three of `0`. -/
theorem thirds_clear_one_or_two {M d : ℕ} (hd : ¬ 3 ∣ d) :
    ClassClear8 3 M 1 d ∨ ClassClear8 3 M 2 d := by
  unfold ClassClear8
  generalize d / M = P
  generalize d % M = r
  omega

/-- **A multiple of `3` does not see the unit.**  Its class is `⌊d/M⌋ mod 24` at every `i`, which is
the band `d mod 8e ∈ [e, 7e]` of the flank `e = 3M`. -/
theorem thirds_multiple {M d : ℕ} (h3 : 3 ∣ d) (i : ℕ) :
    ClassClear8 3 M i d ↔ ClassClear8 3 M 0 d := by
  unfold ClassClear8
  rw [Nat.mod_eq_zero_of_dvd (Dvd.dvd.mul_left h3 i), zero_mul, Nat.zero_mod]

/-- **Thirds, with the `φ(3)` budget.**  At the flank `e = 3M` (not required to be a disparity):
if every multiple of `3` sits in the flank's band and every non-multiple but at most one, `d₀`,
blocks neither unit, then `t = i/3 + 1/(8e)` is lonely at the unit `d₀` leaves clear. -/
theorem lonely_eight_of_thirds {S : Finset ℕ} {M : ℕ} (hM : 0 < M) (d₀ : ℕ)
    (hmult : ∀ d ∈ S, 3 ∣ d → ClassClear8 3 M 0 d)
    (hfree : ∀ d ∈ S, ¬ 3 ∣ d → d ≠ d₀ → ClassClear8 3 M 1 d ∧ ClassClear8 3 M 2 d) :
    ∃ t : ℝ, 0 < t ∧ ∀ d ∈ S, (8 : ℝ)⁻¹ ≤ circDist ((d : ℝ) * t) := by
  have key : ∀ i, (i = 1 ∨ i = 2) → (¬ 3 ∣ d₀ → ClassClear8 3 M i d₀) →
      RationalOpening8 S 3 M i := by
    intro i hi h0 d hd
    by_cases h3 : 3 ∣ d
    · exact (thirds_multiple h3 i).mpr (hmult d hd h3)
    by_cases hd0 : d = d₀
    · subst hd0; exact h0 h3
    · rcases hi with rfl | rfl
      · exact (hfree d hd h3 hd0).1
      · exact (hfree d hd h3 hd0).2
  by_cases h3 : 3 ∣ d₀
  · exact lonely_eight_of_rationalOpening (by norm_num) hM
      (key 1 (Or.inl rfl) fun h => absurd h3 h)
  rcases thirds_clear_one_or_two (M := M) h3 with h | h
  · exact lonely_eight_of_rationalOpening (by norm_num) hM (key 1 (Or.inl rfl) fun _ => h)
  · exact lonely_eight_of_rationalOpening (by norm_num) hM (key 2 (Or.inr rfl) fun _ => h)

/-! ## 2e. fifths: the rational opening at `N = 5`, and its `φ(5)` budget

At a flank `e = 5M` the instant is `t = i/5 + 1/(8e)`.  As at thirds, a multiple of `5` does not see
the unit and needs the flank's band (`classClear_multiple`, every `N`).  A non-multiple has, at the
four units, the classes `q + 8`, `q + 16`, `q + 24`, `q + 32` mod `40`; a blocked class lies in a
window of ten about `0`, which holds at most two of them.  So **each non-multiple blocks at most two
of the `φ(5) = 4` units** (`fifths_clear_one_of_three`), and at most one blocking non-multiple
leaves a unit free (`lonely_eight_of_fifths`).
-/

/-- **A multiple of `N` does not see the unit**, at every `N`: its class is `⌊d/M⌋ mod 8N`. -/
theorem classClear_multiple {N M d : ℕ} (hN : N ∣ d) (i : ℕ) :
    ClassClear8 N M i d ↔ ClassClear8 N M 0 d := by
  unfold ClassClear8
  rw [Nat.mod_eq_zero_of_dvd (Dvd.dvd.mul_left hN i), zero_mul, Nat.zero_mod]

/-- **Each non-multiple of `5` blocks at most two of the four units**: of any three units it clears
at one. -/
theorem fifths_clear_one_of_three {M d : ℕ} (hd : ¬ 5 ∣ d) :
    (ClassClear8 5 M 1 d ∨ ClassClear8 5 M 2 d ∨ ClassClear8 5 M 3 d) ∧
    (ClassClear8 5 M 1 d ∨ ClassClear8 5 M 2 d ∨ ClassClear8 5 M 4 d) ∧
    (ClassClear8 5 M 1 d ∨ ClassClear8 5 M 3 d ∨ ClassClear8 5 M 4 d) ∧
    (ClassClear8 5 M 2 d ∨ ClassClear8 5 M 3 d ∨ ClassClear8 5 M 4 d) := by
  unfold ClassClear8
  generalize d / M = P
  generalize d % M = r
  refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

/-- **Fifths, with the `φ(5)` budget.**  At the flank `e = 5M` (not required to be a disparity): if
every multiple of `5` sits in the flank's band and every non-multiple but at most one, `d₀`, blocks
no unit, then `t = i/5 + 1/(8e)` is lonely at a unit `d₀` leaves clear. -/
theorem lonely_eight_of_fifths {S : Finset ℕ} {M : ℕ} (hM : 0 < M) (d₀ : ℕ)
    (hmult : ∀ d ∈ S, 5 ∣ d → ClassClear8 5 M 0 d)
    (hfree : ∀ d ∈ S, ¬ 5 ∣ d → d ≠ d₀ → ∀ i, 1 ≤ i → i ≤ 4 → ClassClear8 5 M i d) :
    ∃ t : ℝ, 0 < t ∧ ∀ d ∈ S, (8 : ℝ)⁻¹ ≤ circDist ((d : ℝ) * t) := by
  have key : ∀ i, 1 ≤ i → i ≤ 4 → (¬ 5 ∣ d₀ → ClassClear8 5 M i d₀) →
      RationalOpening8 S 5 M i := by
    intro i hi1 hi4 h0 d hd
    by_cases h5 : 5 ∣ d
    · exact (classClear_multiple h5 i).mpr (hmult d hd h5)
    by_cases hd0 : d = d₀
    · subst hd0; exact h0 h5
    · exact hfree d hd h5 hd0 i hi1 hi4
  have go : ∀ i, 1 ≤ i → i ≤ 4 → (¬ 5 ∣ d₀ → ClassClear8 5 M i d₀) →
      ∃ t : ℝ, 0 < t ∧ ∀ d ∈ S, (8 : ℝ)⁻¹ ≤ circDist ((d : ℝ) * t) :=
    fun i hi1 hi4 h0 => lonely_eight_of_rationalOpening (by norm_num) hM (key i hi1 hi4 h0)
  by_cases h5 : 5 ∣ d₀
  · exact go 1 le_rfl (by norm_num) fun h => absurd h5 h
  rcases (fifths_clear_one_of_three (M := M) h5).1 with h | h | h
  · exact go 1 le_rfl (by norm_num) fun _ => h
  · exact go 2 (by norm_num) (by norm_num) fun _ => h
  · exact go 3 (by norm_num) (by norm_num) fun _ => h

/-! ## 2f. sixths, sevenths and ninths

**The new instants at `N` are its units.**  An index `i` with `g = gcd(i, N) > 1` gives the instant
`(i/g)/(N/g) + 1/(8e)`, a rational opening at the smaller `N/g`; so `N` adds `φ(N)` instants per flank.

*Sevenths.*  At the six units a non-multiple of `7` has the classes `q + 8s` mod `56`, `s = 1, …, 6`,
and a blocked class lies in a window of fourteen about `0`, which holds at most two of them
(`sevenths_window`).  So each non-multiple blocks at most two of the `φ(7) = 6` units.  On the
residual this budget is **not** what certifies: the sets there have four to six blocking
non-multiples at every flank divisible by `7`, and their blocked units overlap.  Why they overlap
is open; the case enters the residual by its exact condition.

*Sixths.*  The units are `1` and `5`.  A disparity with `3 ∣ d` does not see the unit: `i·d mod 6` is
`0` or `3` for both (`sixths_blind`) — the `gcd(d, 6)` decides it.  A non-multiple of `3` blocks at
most one of the two units (`sixths_clear_one_or_five`).  So the budget is `φ(6) = 2`, with the
multiples of `3` as fixed conditions (`lonely_eight_of_sixths`).

*Ninths* enter by their exact condition: on `[1, 36]` they are what the last six sets need, at a
flank divisible by `9` (`experiments/nN/eight_residual_count_v5.py`).
-/

/-- **Sevenths: at most two of the six classes are blocked.**  Of any three distinct classes
`s ∈ {1, …, 6}`, the class `(8s + P) mod 56` clears at one. -/
theorem sevenths_window {P r s₁ s₂ s₃ : ℕ} (h1 : 1 ≤ s₁ ∧ s₁ ≤ 6) (h2 : 1 ≤ s₂ ∧ s₂ ≤ 6)
    (h3 : 1 ≤ s₃ ∧ s₃ ≤ 6) (h12 : s₁ ≠ s₂) (h13 : s₁ ≠ s₃) (h23 : s₂ ≠ s₃) :
    ∃ s ∈ [s₁, s₂, s₃], 7 ≤ (8 * s + P) % 56 ∧
      ((8 * s + P) % 56 < 49 ∨ ((8 * s + P) % 56 = 49 ∧ r = 0)) := by
  by_contra hc
  simp only [List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left,
    not_or, not_and, not_or] at hc
  omega

/-- **Sixths: a multiple of `3` does not see the unit.** -/
theorem sixths_blind {M d : ℕ} (h3 : 3 ∣ d) : ClassClear8 6 M 1 d ↔ ClassClear8 6 M 5 d := by
  unfold ClassClear8
  obtain ⟨k, rfl⟩ := h3
  have : 5 * (3 * k) % 6 = 1 * (3 * k) % 6 := by omega
  rw [this]

/-- **Sixths: a non-multiple of `3` clears at `i = 1` or at `i = 5`.** -/
theorem sixths_clear_one_or_five {M d : ℕ} (hd : ¬ 3 ∣ d) :
    ClassClear8 6 M 1 d ∨ ClassClear8 6 M 5 d := by
  unfold ClassClear8
  generalize d / M = P
  generalize d % M = r
  omega

/-- **Sixths, with the `φ(6)` budget.**  At the flank `e = 6M` (not required to be a disparity): if
every multiple of `3` clears (for these the unit does not matter) and every non-multiple of `3` but
at most one, `d₀`, clears at both units, then `t = i/6 + 1/(8e)` is lonely at a unit `d₀` leaves
clear. -/
theorem lonely_eight_of_sixths {S : Finset ℕ} {M : ℕ} (hM : 0 < M) (d₀ : ℕ)
    (hmult : ∀ d ∈ S, 3 ∣ d → ClassClear8 6 M 1 d)
    (hfree : ∀ d ∈ S, ¬ 3 ∣ d → d ≠ d₀ → ClassClear8 6 M 1 d ∧ ClassClear8 6 M 5 d) :
    ∃ t : ℝ, 0 < t ∧ ∀ d ∈ S, (8 : ℝ)⁻¹ ≤ circDist ((d : ℝ) * t) := by
  have key : ∀ i, (i = 1 ∨ i = 5) → (¬ 3 ∣ d₀ → ClassClear8 6 M i d₀) →
      RationalOpening8 S 6 M i := by
    intro i hi h0 d hd
    by_cases h3 : 3 ∣ d
    · rcases hi with rfl | rfl
      · exact hmult d hd h3
      · exact (sixths_blind h3).mp (hmult d hd h3)
    by_cases hd0 : d = d₀
    · subst hd0; exact h0 h3
    · rcases hi with rfl | rfl
      · exact (hfree d hd h3 hd0).1
      · exact (hfree d hd h3 hd0).2
  by_cases h3 : 3 ∣ d₀
  · exact lonely_eight_of_rationalOpening (by norm_num) hM
      (key 1 (Or.inl rfl) fun h => absurd h3 h)
  rcases sixths_clear_one_or_five (M := M) h3 with h | h
  · exact lonely_eight_of_rationalOpening (by norm_num) hM (key 1 (Or.inl rfl) fun _ => h)
  · exact lonely_eight_of_rationalOpening (by norm_num) hM (key 5 (Or.inr rfl) fun _ => h)

/-! ## 2g. resolutions that are not disparities (the `L_0` ladder)

The fields of §2c–§2f take the resolution to be a disparity (`e ∈ S`).  The ladder of the manuscript
line (`docs/n8/PROOF_REQUIREMENTS_v2.md` §7) does not: at a resolution `D` it tries the `D` numerators
`8j + 1` and the instant `(8j + 1)/(8D)`, with the same band test.  Nothing in the certificate needs
`D ∈ S` (`lonely_eight_of_opening` already takes any `e > 0`).  On the seven `EightResidual` sets of
`[1, 40]` the least such `D` is `3` (six sets, `t = 1/24`) or `5` (one set, `t = 9/40`), where the
flank fields need `N = 12, 15, 16` (`experiments/nN/ladder_vs_fields_v1.out`).

The case below takes `D ≤ resolutionCap8`.  The cap is a case boundary, not a claim: no fixed cap
closes the residual, since a disparity divisible by `8·lcm(1..C)` kills every `D ≤ C`
(`experiments/nN/ladder_live_steps_v1.out`). -/

/-- **The case boundary for §2g.**  Resolutions up to this value are tried. -/
def resolutionCap8 : ℕ := 64

/-- **A resolution clears** at the numerator `8j + 1`: every reading `d·(8j + 1) mod 8D` lies in
`[D, 7D]`.  `D` need not be a disparity. -/
def ResolutionClears8 (S : Finset ℕ) (D j : ℕ) : Prop :=
  ∀ d ∈ S, D ≤ d * (8 * j + 1) % (8 * D) ∧ d * (8 * j + 1) % (8 * D) ≤ 7 * D

/-- **The instant, named.**  A clearing resolution exhibits `(8j + 1)/(8D)`. -/
theorem lonely_eight_at_resolution {S : Finset ℕ} {D j : ℕ} (hD : 0 < D)
    (h : ResolutionClears8 S D j) :
    ∀ d ∈ S, (8 : ℝ)⁻¹ ≤ circDist ((d : ℝ) * (((8 * j + 1 : ℕ) : ℝ) / ((8 * D : ℕ) : ℝ))) := by
  have hl := lonely_of_mirror_band (n := 8) (q := 8 * D) (K := 8 * j + 1) (by omega) (by norm_num)
    (S := S) (fun d hd => by
      obtain ⟨h1, h2⟩ := h d hd
      constructor <;> omega)
  intro d hd
  simpa using hl d hd

/-- A clearing resolution gives loneliness at `1/8`. -/
theorem lonely_eight_of_resolution {S : Finset ℕ} {D j : ℕ} (hD : 0 < D)
    (h : ResolutionClears8 S D j) :
    ∃ t : ℝ, 0 < t ∧ ∀ d ∈ S, (8 : ℝ)⁻¹ ≤ circDist ((d : ℝ) * t) :=
  lonely_eight_of_opening hD j h

/-! ## 2h. the fast pair (separation of scale)

Two disparities `a < b` with every other at most `a/9`: the other five are lonely at `1/6` by order
six, and `LRC.FastPairEight.lonely_eight_of_fast_pair` puts the pair clear inside that window.  R8
is the same rule for a block of one.  Every `EightResidual` member built with two large runners and
no large common factor is settled by it (`experiments/nN/fast_pair_window_v1.out`, 163 of 163). -/

/-- **A fast pair**: two disparities `a < b` with `9c ≤ a` for every other disparity `c`. -/
def FastPair8 (S : Finset ℕ) : Prop :=
  ∃ a ∈ S, ∃ b ∈ S, a < b ∧ ∀ c ∈ S, c ≠ a → c ≠ b → 9 * c ≤ a

/-- A fast pair over seven disparities gives loneliness at `1/8`. -/
theorem lonely_eight_of_fastPair {S : Finset ℕ} (hpos : ∀ d ∈ S, 0 < d) (hc7 : S.card = 7)
    (h : FastPair8 S) : ∃ t : ℝ, 0 < t ∧ ∀ d ∈ S, (8 : ℝ)⁻¹ ≤ circDist ((d : ℝ) * t) := by
  classical
  obtain ⟨a, ha, b, hb, hab, hc⟩ := h
  set C := (S.erase b).erase a with hC
  have hab' : a ≠ b := ne_of_lt hab
  have haC : a ∈ S.erase b := Finset.mem_erase.mpr ⟨hab', ha⟩
  have hCcard : C.card = 5 := by
    rw [hC, Finset.card_erase_of_mem haC, Finset.card_erase_of_mem hb, hc7]
  have hCne : C.Nonempty := Finset.card_pos.mp (by omega)
  have hCpos : ∀ c ∈ C, 0 < c := fun c hc' =>
    hpos c (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hc'))
  have hCm : ∀ c ∈ C, c ≤ a / 9 := by
    intro c hc'
    have hca : c ≠ a := (Finset.mem_erase.mp hc').1
    have hcb : c ≠ b := (Finset.mem_erase.mp (Finset.mem_erase.mp hc').2).1
    have hcS : c ∈ S := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hc')
    rw [Nat.le_div_iff_mul_le (by norm_num)]
    have := hc c hcS hca hcb
    omega
  obtain ⟨t, ht, hCl, hal, hbl⟩ := LRC.FastPairEight.lonely_eight_of_fast_pair hCpos hCcard.le hCne
    hCm hab.le (Nat.mul_div_le a 9)
  refine ⟨t, ht, fun d hd => ?_⟩
  by_cases hda : d = a
  · rw [hda]; exact hal
  by_cases hdb : d = b
  · rw [hdb]; exact hbl
  exact hCl d (Finset.mem_erase.mpr ⟨hda, Finset.mem_erase.mpr ⟨hdb, hd⟩⟩)

/-! ## 2i. the block split (separation of scale with a common factor)

A block `F` of disparities sharing a factor `g ≥ 28·c` for every other disparity `c`: the block
repeats with period `1/g`, order seven clears it once per period, and the rest is clear at `1/8`
on a window of length `1/(28·max)` by order seven's margin
(`LRC.BlockSplitEight.lonely_eight_of_block_split`).  Every `EightResidual` member built with a
large common block is settled by it (`experiments/nN/block_split_v1.out`, 162 of 162). -/

/-- **A block split**: a nonempty proper part `F` of the set whose members share a factor `g` with
`28c ≤ g` for every disparity `c` outside `F`. -/
def BlockSplit8 (S : Finset ℕ) : Prop :=
  ∃ F ⊆ S, ∃ g : ℕ, F.Nonempty ∧ (S \ F).Nonempty ∧ (∀ f ∈ F, g ∣ f) ∧ ∀ c ∈ S \ F, 28 * c ≤ g

/-- A block split over seven disparities gives loneliness at `1/8`. -/
theorem lonely_eight_of_blockSplit {S : Finset ℕ} (hpos : ∀ d ∈ S, 0 < d) (hc7 : S.card = 7)
    (h : BlockSplit8 S) : ∃ t : ℝ, 0 < t ∧ ∀ d ∈ S, (8 : ℝ)⁻¹ ≤ circDist ((d : ℝ) * t) := by
  classical
  obtain ⟨F, hFS, g, hFne, hCne, hg, hc⟩ := h
  have hsplit : (S \ F).card + F.card = 7 := by
    rw [Finset.card_sdiff_add_card_eq_card hFS, hc7]
  have hFcard : F.card ≤ 6 := by have := Finset.card_pos.mpr hCne; omega
  have hCcard : (S \ F).card ≤ 6 := by have := Finset.card_pos.mpr hFne; omega
  have hCm : ∀ c ∈ S \ F, c ≤ g / 28 := by
    intro c hc'
    rw [Nat.le_div_iff_mul_le (by norm_num)]
    have := hc c hc'
    omega
  obtain ⟨t, ht, hCl, hFl⟩ := LRC.BlockSplitEight.lonely_eight_of_block_split
    (C := S \ F) (F := F) (fun c hc' => hpos c (Finset.mem_sdiff.mp hc').1)
    (fun f hf => hpos f (hFS hf)) hCcard hFcard hCne hCm hg (Nat.mul_div_le g 28)
  refine ⟨t, ht, fun d hd => ?_⟩
  by_cases hdF : d ∈ F
  · exact hFl d hdF
  · exact hCl d (Finset.mem_sdiff.mpr ⟨hd, hdF⟩)

/-! ## 3. the case analysis -/

/-- **The shifted flank applies** (R4's condition). -/
def ShiftedApplies8 (S : Finset ℕ) : Prop :=
  ∃ e ∈ S, 8 ∣ e ∧ (∀ d ∈ S, d ≠ e → ¬ 8 ∣ d) ∧ (∀ d ∈ S, d ≤ e) ∧
    ((S.erase e).filter (fun d => Nat.Coprime d 8)).card ≤ 3

/-- **The order-eight residual**, stated by the rules that fail on it: seven disparities, one of
them odd (else halve); `5`, `6`, `7` and `8` each divide one of them (so no `1/q` rule applies,
`q ≤ 8`); not all within a factor of seven of the least (so the first reading fails); the
non-multiples of `8` cost at least `8` (so the descent's budget is spent); no multiple of `8` is a
free flank; the shifted flank's condition fails; and no disparity is more than seven times every
other; and neither §15 opening applies — first-lap clearance at any flank and index, or the `−7`
opening at any flank.  The last class needs no field: it is inside `spread` (`lastClass_is_spread`).
Since §2g, also no clearing resolution `D ≤ resolutionCap8`, disparity or not.

Since one disparity is odd and some is a multiple of `8`, the cost condition leaves exactly the
shapes `(multiples of 8, non-multiples) = (1, 6), (2, 5), (3, 4)`, and `(4, 3)` with one of the
three `≡ 4 (mod 8)`. -/
structure EightResidual (S : Finset ℕ) : Prop where
  card_eq : S.card = 7
  odd : ∃ d ∈ S, ¬ 2 ∣ d
  no_common_factor : ∀ g, 2 ≤ g → ∃ d ∈ S, ¬ g ∣ d
  five : ∃ d ∈ S, 5 ∣ d
  six : ∃ d ∈ S, 6 ∣ d
  seven : ∃ d ∈ S, 7 ∣ d
  eight : ∃ d ∈ S, 8 ∣ d
  spread : ∃ a ∈ S, ∃ b ∈ S, 7 * a < b
  cost : 8 ≤ ∑ e ∈ S.filter (fun d => ¬ 8 ∣ d), max 2 (Nat.gcd e 8)
  no_free_flank : ∀ e ∈ S, 8 ∣ e → ¬ FreeFlank8 S e
  not_shifted : ¬ ShiftedApplies8 S
  not_fast : ∀ V ∈ S, ∃ s ∈ S, s ≠ V ∧ V ≤ 7 * s
  no_first_lap : ∀ e ∈ S, ∀ k : ℕ, ¬ ∀ d ∈ S, d ≠ e → e ≤ d * (8 * k + 1) ∧ d * (8 * k + 1) ≤ 7 * e
  no_minus_seven : ∀ e ∈ S,
    ¬ ∀ d ∈ S, e ≤ (8 * e * d - 7 * d) % (8 * e) ∧ (8 * e * d - 7 * d) % (8 * e) ≤ 7 * e
  no_rational_opening : ∀ e ∈ S, ∀ N, N ∣ 8 → N ∣ e → ∀ i, ¬ RationalOpening8 S N (e / N) i
  no_thirds : ∀ e ∈ S, 3 ∣ e → ∀ i, ¬ RationalOpening8 S 3 (e / 3) i
  no_fifths : ∀ e ∈ S, 5 ∣ e → ∀ i, ¬ RationalOpening8 S 5 (e / 5) i
  no_six_seven_nine : ∀ e ∈ S, ∀ N, (N = 6 ∨ N = 7 ∨ N = 9) → N ∣ e →
    ∀ i, ¬ RationalOpening8 S N (e / N) i
  no_small_resolution : ∀ D, 0 < D → D ≤ resolutionCap8 → ∀ j, ¬ ResolutionClears8 S D j
  no_fast_pair : ¬ FastPair8 S
  no_block_split : ¬ BlockSplit8 S

/-- **Order eight, whole numbers.**  A set of at most seven positive disparities, one of them odd,
is lonely at `1/8`, or it is in `EightResidual`. -/
theorem lonely_eight_or_residual {S : Finset ℕ} (hpos : ∀ d ∈ S, 0 < d) (hcard : S.card ≤ 7)
    (hcf : ∀ g, 2 ≤ g → ∃ d ∈ S, ¬ g ∣ d) :
    (∃ t : ℝ, 0 < t ∧ ∀ d ∈ S, (8 : ℝ)⁻¹ ≤ circDist ((d : ℝ) * t)) ∨ EightResidual S := by
  classical
  have hodd := hcf 2 le_rfl
  by_cases hc6 : S.card ≤ 6
  · exact Or.inl (lonely_eight_of_card_le_six hpos hc6)
  have hc7 : S.card = 7 := by omega
  have rule_q : ∀ q, 0 < q → q ≤ 8 → (∃ d ∈ S, q ∣ d) ∨
      ∃ t : ℝ, 0 < t ∧ ∀ d ∈ S, (8 : ℝ)⁻¹ ≤ circDist ((d : ℝ) * t) := by
    intro q hq hq8
    by_cases h : ∃ d ∈ S, q ∣ d
    · exact Or.inl h
    · push Not at h
      exact Or.inr (lonely_eight_of_no_multiple_of hq hq8 h)
  rcases rule_q 5 (by norm_num) (by norm_num) with h5 | h
  swap; · exact Or.inl h
  rcases rule_q 6 (by norm_num) (by norm_num) with h6 | h
  swap; · exact Or.inl h
  rcases rule_q 7 (by norm_num) (by norm_num) with h7 | h
  swap; · exact Or.inl h
  rcases rule_q 8 (by norm_num) (by norm_num) with h8 | h
  swap; · exact Or.inl h
  by_cases hsp : ∃ a ∈ S, ∃ b ∈ S, 7 * a < b
  swap
  · push Not at hsp
    have hne : S.Nonempty := Finset.card_pos.mp (by omega)
    set m := S.min' hne with hm
    exact Or.inl (lonely_eight_of_spread (hpos m (S.min'_mem hne)) (fun d hd => S.min'_le d hd)
      (fun d hd => hsp m (S.min'_mem hne) d hd))
  have hsplit : (S.filter (fun d => 8 ∣ d)).card + (S.filter (fun d => ¬ 8 ∣ d)).card = 7 := by
    rw [Finset.card_filter_add_card_filter_not, hc7]
  have hE1 : 1 ≤ (S.filter (fun d => ¬ 8 ∣ d)).card := by
    obtain ⟨d, hd, h⟩ := hodd
    exact Finset.card_pos.mpr ⟨d, Finset.mem_filter.mpr ⟨hd, fun h8 => h ((by norm_num : 2 ∣ 8).trans h8)⟩⟩
  by_cases hcost : ∑ e ∈ S.filter (fun d => ¬ 8 ∣ d), max 2 (Nat.gcd e 8) < 8
  · exact Or.inl (lonely_eight_of_descent hpos hcost (by omega))
  by_cases hff : ∃ e ∈ S, 8 ∣ e ∧ FreeFlank8 S e
  · obtain ⟨e, heS, he8, hfree⟩ := hff
    exact Or.inl (lonely_eight_of_freeFlank hpos heS he8 hfree)
  by_cases hsh : ShiftedApplies8 S
  · obtain ⟨e, heS, he8, hothers, hlarg, hcop⟩ := hsh
    exact Or.inl (lonely_eight_of_largest_multiple hpos heS he8 hothers hlarg hcop)
  by_cases hfast : ∃ V ∈ S, ∀ s ∈ S, s ≠ V → 7 * s < V
  · obtain ⟨V, hVS, hV⟩ := hfast
    exact Or.inl (lonely_eight_of_fast hpos hcard hVS hV)
  by_cases hfl : ∃ e ∈ S, ∃ k : ℕ, ∀ d ∈ S, d ≠ e → e ≤ d * (8 * k + 1) ∧ d * (8 * k + 1) ≤ 7 * e
  · obtain ⟨e, heS, k, hk⟩ := hfl
    exact Or.inl (lonely_eight_of_firstLap heS (hpos e heS) k hk)
  by_cases hm7 : ∃ e ∈ S,
      ∀ d ∈ S, e ≤ (8 * e * d - 7 * d) % (8 * e) ∧ (8 * e * d - 7 * d) % (8 * e) ≤ 7 * e
  · obtain ⟨e, heS, he⟩ := hm7
    exact Or.inl (lonely_eight_of_minusSeven (hpos e heS) he)
  by_cases hro : ∃ e ∈ S, ∃ N, N ∣ 8 ∧ N ∣ e ∧ ∃ i, RationalOpening8 S N (e / N) i
  · obtain ⟨e, heS, N, hN8, hNe, i, hi⟩ := hro
    have hN : 0 < N := Nat.pos_of_dvd_of_pos hN8 (by norm_num)
    exact Or.inl (lonely_eight_of_rationalOpening hN
      (Nat.div_pos (Nat.le_of_dvd (hpos e heS) hNe) hN) hi)
  by_cases hth : ∃ e ∈ S, 3 ∣ e ∧ ∃ i, RationalOpening8 S 3 (e / 3) i
  · obtain ⟨e, heS, he3, i, hi⟩ := hth
    exact Or.inl (lonely_eight_of_rationalOpening (by norm_num)
      (Nat.div_pos (Nat.le_of_dvd (hpos e heS) he3) (by norm_num)) hi)
  by_cases hfi : ∃ e ∈ S, 5 ∣ e ∧ ∃ i, RationalOpening8 S 5 (e / 5) i
  · obtain ⟨e, heS, he5, i, hi⟩ := hfi
    exact Or.inl (lonely_eight_of_rationalOpening (by norm_num)
      (Nat.div_pos (Nat.le_of_dvd (hpos e heS) he5) (by norm_num)) hi)
  by_cases hsn : ∃ e ∈ S, ∃ N, (N = 6 ∨ N = 7 ∨ N = 9) ∧ N ∣ e ∧ ∃ i, RationalOpening8 S N (e / N) i
  · obtain ⟨e, heS, N, hN, hNe, i, hi⟩ := hsn
    have hN0 : 0 < N := by omega
    exact Or.inl (lonely_eight_of_rationalOpening hN0
      (Nat.div_pos (Nat.le_of_dvd (hpos e heS) hNe) hN0) hi)
  by_cases hres : ∃ D, 0 < D ∧ D ≤ resolutionCap8 ∧ ∃ j, ResolutionClears8 S D j
  · obtain ⟨D, hD, -, j, hj⟩ := hres
    exact Or.inl (lonely_eight_of_resolution hD hj)
  by_cases hfp : FastPair8 S
  · exact Or.inl (lonely_eight_of_fastPair hpos hc7 hfp)
  by_cases hbs : BlockSplit8 S
  · exact Or.inl (lonely_eight_of_blockSplit hpos hc7 hbs)
  right
  push Not at hcost hff hfast
  refine ⟨hc7, hodd, hcf, h5, h6, h7, h8, hsp, hcost, hff, hsh, hfast, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hfp, hbs⟩
  · intro e heS k hk; exact hfl ⟨e, heS, k, hk⟩
  · intro e heS he; exact hm7 ⟨e, heS, he⟩
  · intro e heS N hN8 hNe i hi; exact hro ⟨e, heS, N, hN8, hNe, i, hi⟩
  · intro e heS he3 i hi; exact hth ⟨e, heS, he3, i, hi⟩
  · intro e heS he5 i hi; exact hfi ⟨e, heS, he5, i, hi⟩
  · intro e heS N hN hNe i hi; exact hsn ⟨e, heS, N, hN, hNe, i, hi⟩
  · intro D hD hDc j hj; exact hres ⟨D, hD, hDc, j, hj⟩

/-! ## 4. what order eight reduces to -/

/-- **Every positive whole-number set, by halving and the case list**, is lonely at `1/8` once the
residual sets are. -/
theorem lonely_eight_nat_of_residual
    (hres : ∀ R : Finset ℕ, (∀ d ∈ R, 0 < d) → EightResidual R →
      ∃ t : ℝ, 0 < t ∧ ∀ d ∈ R, (8 : ℝ)⁻¹ ≤ circDist ((d : ℝ) * t)) :
    ∀ N : ℕ, ∀ S : Finset ℕ, (∑ d ∈ S, d) = N → (∀ d ∈ S, 0 < d) → S.card ≤ 7 →
      ∃ t : ℝ, 0 < t ∧ ∀ d ∈ S, (8 : ℝ)⁻¹ ≤ circDist ((d : ℝ) * t) := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro S hN hpos hcard
    classical
    rcases Finset.eq_empty_or_nonempty S with rfl | hne
    · exact ⟨1, one_pos, by simp⟩
    by_cases hg : ∃ g, 2 ≤ g ∧ ∀ d ∈ S, g ∣ d
    · obtain ⟨g, hg2, hgd⟩ := hg
      obtain ⟨hc, hs, hp⟩ := LRC.OrderSevenN.quotient_card_sum hg2 hpos hgd hne
      obtain ⟨τ, hτ, hl⟩ := ih _ (hN ▸ hs) _ rfl hp (hc.trans_le hcard)
      exact lonely_eight_of_common_factor (by omega) hgd hτ hl
    have hcf : ∀ g, 2 ≤ g → ∃ d ∈ S, ¬ g ∣ d := by
      intro g hg2
      by_contra h
      push Not at h
      exact hg ⟨g, hg2, h⟩
    rcases lonely_eight_or_residual hpos hcard hcf with h | h
    · exact h
    · exact hres S hpos h

/-- **The conjecture at eight runners, for every arrangement of real speeds, is equivalent to the
residual.**  `ExistenceAt8` holds exactly when every set in `EightResidual` is lonely at `1/8`. -/
theorem existenceAt8_iff_residual :
    LRC.Spec.ExistenceAt8 ↔
      ∀ R : Finset ℕ, (∀ d ∈ R, 0 < d) → EightResidual R →
        ∃ t : ℝ, 0 < t ∧ ∀ d ∈ R, (8 : ℝ)⁻¹ ≤ circDist ((d : ℝ) * t) := by
  constructor
  · intro h R hpos hR
    classical
    obtain ⟨s, hs, hl⟩ := h (R.image (fun d : ℕ => (d : ℝ)))
      (by
        intro x hx
        obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hx
        exact_mod_cast hpos d hd)
      (le_trans Finset.card_image_le hR.card_eq.le)
    exact ⟨s, hs, fun d hd => hl _ (Finset.mem_image_of_mem _ hd)⟩
  · intro hres
    exact existenceAt8_of_nat (fun S hpos hcard => lonely_eight_nat_of_residual hres _ S rfl hpos hcard)

/-- **The conjecture at eight runners from the residual.** -/
theorem lonelyRunnerAt8_of_residual
    (hres : ∀ R : Finset ℕ, (∀ d ∈ R, 0 < d) → EightResidual R →
      ∃ t : ℝ, 0 < t ∧ ∀ d ∈ R, (8 : ℝ)⁻¹ ≤ circDist ((d : ℝ) * t)) :
    LRC.Spec.LonelyRunnerAt8 :=
  LRC.Spec.lonelyRunnerAt8_of_existence (existenceAt8_iff_residual.mpr hres)

/-- **The residual statement asks nothing beyond the conjecture.**  A residual set `R` is the
disparity set of the arrangement `(0, r₁, …, r₇)` for its subject, the runner of speed `0`; the
conjecture at eight runners, applied to that one subject, gives the residual statement back.  No
runner is pinned in the target: `0` is simply one of the eight speeds of this particular
arrangement. -/
theorem residual_of_lonelyRunnerAt8 (h : LRC.Spec.LonelyRunnerAt8) :
    ∀ R : Finset ℕ, (∀ d ∈ R, 0 < d) → EightResidual R →
      ∃ t : ℝ, 0 < t ∧ ∀ d ∈ R, (8 : ℝ)⁻¹ ≤ circDist ((d : ℝ) * t) := by
  intro R hpos hR
  classical
  set f := R.orderEmbOfFin hR.card_eq with hf
  set v : Fin 8 → ℝ := Fin.cons 0 (fun i : Fin 7 => ((f i : ℕ) : ℝ)) with hv
  have hinj : Function.Injective v := by
    refine Fin.cons_injective_iff.mpr ⟨?_, ?_⟩
    · rintro ⟨i, hi⟩
      have hmem : f i ∈ R := Finset.orderEmbOfFin_mem R hR.card_eq i
      have h0 : ((f i : ℕ) : ℝ) = 0 := hi
      have : f i = 0 := by exact_mod_cast h0
      exact absurd (hpos _ hmem) (by omega)
    · intro a b hab
      have hab' : ((f a : ℕ) : ℝ) = ((f b : ℕ) : ℝ) := hab
      have : (f a : ℕ) = f b := by exact_mod_cast hab'
      exact f.injective this
  obtain ⟨t, ht, hl⟩ := h v hinj 0
  refine ⟨t, ht, fun d hd => ?_⟩
  obtain ⟨i, hi⟩ : ∃ i, f i = d := by
    have : d ∈ Set.range f := by
      rw [hf, Finset.range_orderEmbOfFin]; exact hd
    exact this
  have := hl i.succ (Fin.succ_ne_zero i)
  simpa [hv, hi] using this

/-- **The owed statement is the conjecture at eight runners, exactly.** -/
theorem lonelyRunnerAt8_iff_residual :
    LRC.Spec.LonelyRunnerAt8 ↔
      ∀ R : Finset ℕ, (∀ d ∈ R, 0 < d) → EightResidual R →
        ∃ t : ℝ, 0 < t ∧ ∀ d ∈ R, (8 : ℝ)⁻¹ ≤ circDist ((d : ℝ) * t) :=
  ⟨residual_of_lonelyRunnerAt8, lonelyRunnerAt8_of_residual⟩

end LRC.OrderEightN
