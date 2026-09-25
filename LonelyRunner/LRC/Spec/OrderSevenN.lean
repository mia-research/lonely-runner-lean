import LonelyRunner.LRC.Spec.OrderSevenReductionN
import LonelyRunner.LRC.Spec.MirrorN
import LonelyRunner.LRC.Spec.OrderSixSevenN

/-!
# Order seven, whole numbers, inside the framework (Barajas–Serra)

2026-09-25.  Every set of at most six positive whole-number disparities is lonely at `1/7`
(`lonely_seven_nat`), so every subject of every whole-number or commensurable arrangement of seven
runners has a lonely opening (`doorFlank_seven_int`, through `orderSeven_obligation`).

The argument is Barajas–Serra 2008, ported into `OrderSeven*N.lean`.  In the framework's terms:

* **The instant is named.**  Every case ends at `t = K/(7P)` with `0 < K < 7P`: every reading
  `d·K mod 7P` lies in `[P, 6P]`, which is the residue-band rule `lonely_of_mirror_band` at
  `q = 7P` (`lonely_seven_of_band`).  `P = 7^m` except in §7, where `P = 14` (modulus `98`).
* **The multiplier.**  On the power-of-`7` moduli (`P = 7^m`) the multiplier `λ` is coprime to
  `7` — a unit — built level by level on the `7`-adic levels `7^j ∥ d`, one coefficient in
  `ZMod 7` per level, by pigeonhole (`unit_filtering`, `corollary3`); `corollary3`, `four_band`
  and `five_band` each return `¬ 7 ∣ λ`.  The pigeonhole is a tool and the witness it returns is
  bounded.  The hard levels (four or five disparities on one level) are exact residue tables over
  `ZMod 7` (`OrderSevenA4N`, `OrderSevenA5N`).  At `m = 1` the witness is found in a finite table
  over `ℤ/49` or `ℤ/98` (`OrderSevenS7*N`), checked in the kernel; at `98` the table returns some
  `0 < λ < 98` and no unit property is claimed there.
* **No `gcd` hypothesis.**  The source assumed `gcd = 1`.  It used two consequences only: some
  disparity off the `7`-lattice, and (in §7, at `p = 2`) some disparity odd.  Both are reached by
  descent (`lonely_seven_card_six`): if every disparity is a multiple of `7`, the set is
  `7·M` and a lonely instant `τ` of `M` gives `τ/7` — this is R5's descent `n·M → M` — and the
  same for `2`.
* **No lower-order result is imported.**  The source's dispatcher also used the ratio branch and a
  fast-runner branch over an order-six set; neither is needed, since Barajas–Serra covers every
  six-disparity set, and the second would import order six.

Real speeds with more than one commensurability class are not here: the `RealFiveN` template
needs whole-number order six at `1/6` for its merged model.

Everything here is proved; no `sorry`, no `native_decide`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

namespace LRC.OrderSevenN

open MomentIterationN LRC.SpecN

/-! ## 1. the named instant -/

/-- **The residue-band instant at `7P`.**  If every reading `λ·d mod 7P` lies in `[P, 6P]`, then at
`t = K/(7P)` with `K = λ mod 7P` every disparity is at least `1/7` from the integers.  This is
`lonely_of_mirror_band` with `q = 7P`, `n = 7`. -/
theorem lonely_seven_of_band {S : Finset ℕ} {P : ℕ} (hP : 0 < P) (lam : ℤ)
    (hband : ∀ d ∈ S, (P : ℤ) ≤ lam * d % (7 * P : ℤ) ∧ lam * d % (7 * P : ℤ) ≤ 6 * P) :
    ∀ d ∈ S, (7 : ℝ)⁻¹ ≤
      circDist ((d : ℝ) * (((lam % (7 * P : ℤ)).toNat : ℝ) / ((7 * P : ℕ) : ℝ))) := by
  set q : ℕ := 7 * P with hq
  set K : ℕ := (lam % (7 * P : ℤ)).toNat with hK
  have hq0 : (0 : ℤ) < (q : ℤ) := by rw [hq]; push_cast; omega
  have hKz : (K : ℤ) = lam % (q : ℤ) := by
    rw [hK, Int.toNat_of_nonneg (Int.emod_nonneg _ (by omega))]; rw [hq]; push_cast; ring_nf
  have hread : ∀ d : ℕ, (((d * K) % q : ℕ) : ℤ) = lam * d % (7 * P : ℤ) := by
    intro d
    have h7P : (7 * P : ℤ) = (q : ℤ) := by rw [hq]; push_cast; ring
    rw [h7P, Int.natCast_mod, Nat.cast_mul, hKz, Int.mul_emod, Int.emod_emod_of_dvd _ dvd_rfl,
      ← Int.mul_emod, mul_comm]
  refine lonely_of_mirror_band (n := 7) (q := q) (K := K) (by omega) (by norm_num) ?_
  intro d hd
  obtain ⟨h1, h2⟩ := hband d hd
  rw [← hread d] at h1 h2
  have h1' : P ≤ (d * K) % q := by exact_mod_cast h1
  have h2' : (d * K) % q ≤ 6 * P := by exact_mod_cast h2
  omega

/-- The instant `K/(7P)` of `lonely_seven_of_band` is positive once one disparity is present:
a disparity reading in `[P, 6P]` cannot read `0`. -/
theorem band_instant_pos {S : Finset ℕ} {P : ℕ} (hP : 0 < P) (lam : ℤ) {d : ℕ} (hd : d ∈ S)
    (hband : ∀ d ∈ S, (P : ℤ) ≤ lam * d % (7 * P : ℤ) ∧ lam * d % (7 * P : ℤ) ≤ 6 * P) :
    0 < (((lam % (7 * P : ℤ)).toNat : ℝ) / ((7 * P : ℕ) : ℝ)) := by
  have hq : (0 : ℝ) < ((7 * P : ℕ) : ℝ) := by exact_mod_cast (show 0 < 7 * P by omega)
  refine div_pos ?_ hq
  have hK : 0 < (lam % (7 * P : ℤ)).toNat := by
    by_contra h0
    have hz : lam % (7 * P : ℤ) = 0 := by
      have := Int.emod_nonneg lam (show (7 * P : ℤ) ≠ 0 by omega)
      omega
    have hdvd : (7 * P : ℤ) ∣ lam * d := Dvd.dvd.mul_right (Int.dvd_of_emod_eq_zero hz) _
    have := (hband d hd).1
    rw [Int.emod_eq_zero_of_dvd hdvd] at this
    omega
  exact_mod_cast hK

/-! ## 2. six disparities on the two lattices -/

/-- **Barajas–Serra, six disparities.**  Six distinct positive whole numbers, one of them off the
`7`-lattice and one of them odd, are lonely at `1/7` at the named instant `K/(7P)`. -/
theorem lonely_seven_six (D : Fin 6 → ℕ) (hpos : ∀ i, 0 < D i) (hinj : Function.Injective D)
    (h7 : ∃ i, ¬ 7 ∣ D i) (h2 : ∃ i, ¬ 2 ∣ D i) :
    ∃ t : ℝ, 0 < t ∧ ∀ i, (7 : ℝ)⁻¹ ≤ circDist ((D i : ℝ) * t) := by
  classical
  obtain ⟨P, lam, hP, hq⟩ := bs_discrete_q D hpos hinj h7 h2
  set S : Finset ℕ := Finset.univ.image D with hS
  have hband : ∀ d ∈ S, (P : ℤ) ≤ lam * d % (7 * P : ℤ) ∧ lam * d % (7 * P : ℤ) ≤ 6 * P := by
    intro d hd
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hd
    exact hq i
  have hmem : ∀ i, D i ∈ S := fun i => Finset.mem_image_of_mem _ (Finset.mem_univ i)
  exact ⟨_, band_instant_pos hP lam (hmem 0) hband,
    fun i => lonely_seven_of_band hP lam hband (D i) (hmem i)⟩

/-! ## 3. descent: dividing out the common power of `7`, and of `2` -/

/-- **Descent by a common factor.**  If every disparity is a multiple of `g`, a lonely instant
`τ` of the quotients gives the lonely instant `τ/g` of the set.  At `g = 7` this is R5's
`n·M → M`. -/
theorem lonely_of_quotient {S : Finset ℕ} {g : ℕ} (hg : 0 < g) (hgd : ∀ d ∈ S, g ∣ d) {τ : ℝ}
    (hτ : 0 < τ) (hl : ∀ d ∈ S.image (fun d => d / g), (7 : ℝ)⁻¹ ≤ circDist ((d : ℝ) * τ)) :
    0 < τ / g ∧ ∀ d ∈ S, (7 : ℝ)⁻¹ ≤ circDist ((d : ℝ) * (τ / g)) := by
  have hg0 : (g : ℝ) ≠ 0 := by exact_mod_cast hg.ne'
  refine ⟨div_pos hτ (by exact_mod_cast hg), fun d hd => ?_⟩
  have := hl (d / g) (Finset.mem_image_of_mem _ hd)
  rw [Nat.cast_div (hgd d hd) hg0, div_mul_eq_mul_div] at this
  rwa [mul_div_assoc] at this

/-- Division by a common factor `g ≥ 2` keeps the count and lowers the sum. -/
theorem quotient_card_sum {S : Finset ℕ} {g : ℕ} (hg : 2 ≤ g) (hpos : ∀ d ∈ S, 0 < d)
    (hgd : ∀ d ∈ S, g ∣ d) (hne : S.Nonempty) :
    (S.image (fun d => d / g)).card = S.card ∧
      ∑ d ∈ S.image (fun d => d / g), d < ∑ d ∈ S, d ∧
      ∀ x ∈ S.image (fun d => d / g), 0 < x := by
  have hinj : Set.InjOn (fun d => d / g) (S : Set ℕ) := by
    intro x hx y hy hxy
    simp only at hxy
    rw [← Nat.div_mul_cancel (hgd x hx), ← Nat.div_mul_cancel (hgd y hy), hxy]
  refine ⟨Finset.card_image_of_injOn hinj, ?_, ?_⟩
  · rw [Finset.sum_image hinj]
    exact Finset.sum_lt_sum_of_nonempty hne fun d hd => Nat.div_lt_self (hpos d hd) (by omega)
  · intro x hx
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hx
    exact Nat.div_pos (Nat.le_of_dvd (hpos d hd) (hgd d hd)) (by omega)

theorem lonely_seven_card_six_aux : ∀ N : ℕ, ∀ S : Finset ℕ, (∑ d ∈ S, d) = N →
    (∀ d ∈ S, 0 < d) → S.card = 6 →
    ∃ t : ℝ, 0 < t ∧ ∀ d ∈ S, (7 : ℝ)⁻¹ ≤ circDist ((d : ℝ) * t) := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro S hN hpos hcard
    classical
    have hne : S.Nonempty := Finset.card_pos.mp (by omega)
    -- a common factor `g ∈ {7, 2}`: descend
    have descend : ∀ g, 2 ≤ g → (∀ d ∈ S, g ∣ d) →
        ∃ t : ℝ, 0 < t ∧ ∀ d ∈ S, (7 : ℝ)⁻¹ ≤ circDist ((d : ℝ) * t) := by
      intro g hg hgd
      obtain ⟨hc, hs, hp⟩ := quotient_card_sum hg hpos hgd hne
      obtain ⟨τ, hτ, hl⟩ := ih _ (hN ▸ hs) _ rfl hp (hc.trans hcard)
      exact ⟨_, lonely_of_quotient (by omega) hgd hτ hl⟩
    by_cases h7 : ∀ d ∈ S, 7 ∣ d
    · exact descend 7 (by norm_num) h7
    by_cases h2 : ∀ d ∈ S, 2 ∣ d
    · exact descend 2 (by norm_num) h2
    -- both lattices missed: Barajas–Serra on the six disparities, enumerated
    push Not at h7 h2
    set e := S.orderIsoOfFin hcard with he
    set D : Fin 6 → ℕ := fun i => (e i : ℕ) with hD
    have hDmem : ∀ i, D i ∈ S := fun i => (e i).2
    have hDinj : Function.Injective D := fun a b h => e.injective (Subtype.val_injective h)
    have hDof : ∀ d ∈ S, ∃ i, D i = d := fun d hd => ⟨e.symm ⟨d, hd⟩, by simp [hD]⟩
    obtain ⟨d7, hd7, hn7⟩ := h7
    obtain ⟨d2, hd2, hn2⟩ := h2
    obtain ⟨i7, hi7⟩ := hDof d7 hd7
    obtain ⟨i2, hi2⟩ := hDof d2 hd2
    obtain ⟨t, ht, hl⟩ := lonely_seven_six D (fun i => hpos _ (hDmem i)) hDinj
      ⟨i7, hi7 ▸ hn7⟩ ⟨i2, hi2 ▸ hn2⟩
    refine ⟨t, ht, fun d hd => ?_⟩
    obtain ⟨i, rfl⟩ := hDof d hd
    exact hl i

/-- **Six disparities, whole numbers, no further hypothesis.** -/
theorem lonely_seven_card_six {S : Finset ℕ} (hpos : ∀ d ∈ S, 0 < d) (hcard : S.card = 6) :
    ∃ t : ℝ, 0 < t ∧ ∀ d ∈ S, (7 : ℝ)⁻¹ ≤ circDist ((d : ℝ) * t) :=
  lonely_seven_card_six_aux _ S rfl hpos hcard

/-! ## 4. at most six -/

/-- A set of at most six positive whole numbers sits inside one of exactly six: add runners past
the fastest. -/
theorem exists_six_superset {S : Finset ℕ} (hpos : ∀ d ∈ S, 0 < d) (hcard : S.card ≤ 6) :
    ∃ T : Finset ℕ, S ⊆ T ∧ (∀ d ∈ T, 0 < d) ∧ T.card = 6 := by
  classical
  set M := S.sup id with hM
  set E : Finset ℕ := Finset.Icc (M + 1) (M + (6 - S.card)) with hE
  have hdisj : Disjoint S E := by
    rw [Finset.disjoint_left]
    intro d hd hdE
    have hle : d ≤ M := Finset.le_sup (f := id) hd
    have := (Finset.mem_Icc.mp hdE).1
    omega
  refine ⟨S ∪ E, Finset.subset_union_left, fun d hd => ?_, ?_⟩
  · rcases Finset.mem_union.mp hd with h | h
    · exact hpos d h
    · have := (Finset.mem_Icc.mp h).1; omega
  · rw [Finset.card_union_of_disjoint hdisj, hE, Nat.card_Icc]
    omega

/-- **Order seven, whole numbers, inside the framework.**  Every set of at most six positive
whole-number disparities is lonely at `1/7`. -/
theorem lonely_seven_nat (S : Finset ℕ) (hpos : ∀ d ∈ S, 0 < d) (hcard : S.card ≤ 6) :
    ∃ t : ℝ, 0 < t ∧ ∀ d ∈ S, (7 : ℝ)⁻¹ ≤ circDist ((d : ℝ) * t) := by
  obtain ⟨T, hST, hTpos, hT⟩ := exists_six_superset hpos hcard
  obtain ⟨t, ht, hl⟩ := lonely_seven_card_six hTpos hT
  exact ⟨t, ht, fun d hd => hl d (hST hd)⟩

/-- **Commensurable real disparities at order seven.**  If every disparity is a positive whole
multiple of one unit `u > 0`, the set is lonely at `1/7`: read it in that unit and rescale. -/
theorem lonely_seven_commensurable {ds : Finset ℝ} {u : ℝ} (hu : 0 < u) (hcard : ds.card ≤ 6)
    (hcomm : ∀ d ∈ ds, ∃ m : ℕ, 0 < m ∧ d = u * m) :
    ∃ t : ℝ, 0 < t ∧ ∀ d ∈ ds, (7 : ℝ)⁻¹ ≤ circDist (d * t) := by
  classical
  set S : Finset ℕ := ds.image (fun d => ⌊d / u⌋₊) with hS
  have hunit : ∀ d ∈ ds, d = u * (⌊d / u⌋₊ : ℝ) ∧ 0 < ⌊d / u⌋₊ := by
    intro d hd
    obtain ⟨m, hm, rfl⟩ := hcomm d hd
    rw [mul_div_cancel_left₀ _ hu.ne', Nat.floor_natCast]
    exact ⟨rfl, hm⟩
  obtain ⟨τ, hτ, hl⟩ := lonely_seven_nat S
    (by
      intro m hm
      obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hm
      exact (hunit d hd).2)
    (le_trans Finset.card_image_le hcard)
  refine ⟨τ / u, by positivity, fun d hd => ?_⟩
  have h := hl _ (Finset.mem_image_of_mem _ hd)
  have heq : d * (τ / u) = (⌊d / u⌋₊ : ℝ) * τ := by
    conv_lhs => rw [(hunit d hd).1]
    field_simp
  rw [heq]; exact h

/-! ## 5. the obligation at order seven, for whole-number arrangements -/

/-- **Every subject of every whole-number arrangement of seven runners is lonely.** -/
theorem lonelyForSubject_seven_int (v : Fin 7 → ℤ) (hv : Function.Injective v) (k : Fin 7) :
    LonelyForSubject (fun i => (v i : ℝ)) k := by
  classical
  have hvR : Function.Injective (fun i => (v i : ℝ)) := Int.cast_injective.comp hv
  rw [lonelyForSubject_iff_diffSet]
  apply lonely_seven_commensurable (u := 1) one_pos (diffSet_card_le k)
  intro d hd
  obtain ⟨i, hik, rfl⟩ := mem_diffSet.mp hd
  have hpos := diffSet_pos hvR k _ hd
  refine ⟨(v i - v k).natAbs, ?_, ?_⟩
  · exact Int.natAbs_pos.mpr (sub_ne_zero.mpr fun h => hik (hv h))
  · rw [one_mul, Nat.cast_natAbs, Int.cast_abs, Int.cast_sub]

/-- **The flank door at order seven, for whole-number arrangements.**  By `orderSeven_obligation`
(`DoorFlank ↔ LonelyForSubject`, both directions, no hypothesis beyond injectivity), every subject
has a flank and an opening index at which it is lonely. -/
theorem doorFlank_seven_int (v : Fin 7 → ℤ) (hv : Function.Injective v) (k : Fin 7) :
    DoorFlank (fun i => (v i : ℝ)) k :=
  (LRC.OrderSixSeven.orderSeven_obligation _ (Int.cast_injective.comp hv) k).mpr (lonelyForSubject_seven_int v hv k)

end LRC.OrderSevenN
