import LonelyRunner.LRC.Spec.OrderEightCasesN

/-!
# The parity descent: the shift budget read by parity classes (order eight)

2026-10-05 (running log E400).  `DescentMultiN.lonely_multi_descent_iff` tries the eight shifts
`t = (τ + k)/8`, `k = 0, …, 7`, at an instant `τ` clearing the cofactors of the multiples of `8`.
Each multiple `8m` reads `m·(τ + k)`, unchanged mod 1; a non-multiple `e` reads `e·τ/8 + e·k/8` and
blocks at most `max 2 (gcd e 8)` shifts (`card_bad_le`), so a total below `8` leaves a shift free.
The residual has that total at least `8` (`EightResidual.cost`).  This file reads the same blocked
shifts by parity.

* An **odd** non-multiple blocks at most one even and at most one odd shift
  (`odd_blocked_same_parity`): two blocked shifts of one parity differ by an even step, and a
  step of size at most `1` that is even is `0`.
* An **even** non-multiple blocks shifts of one parity only (`even_blocked_parity`): an odd
  difference of two blocked shifts would force `8 ∣ e`.

So the four even shifts are blocked by at most `#odd + ∑_{e ∈ A} gcd e 8` of the non-multiples,
`A` the even ones whose blocked shifts are even, and the four odd shifts by at most
`#odd + ∑_{e ∉ A} gcd e 8`.  **The parity split** (`ParitySplit8`): however the even non-multiples
are divided into two groups, one side's total is below `4`.  Under it some shift is free at every
`τ` (`exists_free_shift`), and `E ∪ 8·M` is lonely at `1/8` exactly when `M` is
(`lonely_parity_descent_iff`).  The descent's cost condition implies the split
(`paritySplit_of_cost`), so this extends the descent.  A count inside each parity class, used as a
tool.

Shapes of the residual's crowded level it settles (by the residue types of the non-multiples:
`o` odd, `t ≡ 2 mod 4`, `f ≡ 4 mod 8`): with four multiples of `8`, `(o, o, f)` and `(o, t, f)`;
with three, `(o, o, o, t)`, `(o, o, o, f)` and `(o, t, t, t)`.  `(o, f, f)` and the shapes with
more non-multiples are not settled by it.
-/

set_option linter.style.longLine false

namespace LRC.ParityDescent

open ConstructionN LRC.Descent

/-- A non-multiple `e` is **in the way at shift `k`** for the offset `τ` when
`circDist (e·τ/8 + e·k/8) < 1/8`. -/
def Blocked (τ : ℝ) (e k : ℕ) : Prop :=
  circDist ((e : ℝ) * τ / 8 + (e : ℝ) * (k : ℝ) / 8) < (8 : ℝ)⁻¹

noncomputable instance (τ : ℝ) (e k : ℕ) : Decidable (Blocked τ e k) := by
  unfold Blocked; infer_instance

/-- `2` is coprime to an odd integer. -/
theorem isCoprime_two_of_odd {z : ℤ} (hz : ¬ (2 : ℤ) ∣ z) : IsCoprime (2 : ℤ) z := by
  have h : z % 2 = 1 := by omega
  refine ⟨-(z / 2), 1, ?_⟩
  omega

/-- `8` is coprime to an odd integer. -/
theorem isCoprime_eight_of_odd {z : ℤ} (hz : ¬ (2 : ℤ) ∣ z) : IsCoprime (8 : ℤ) z := by
  have h := (isCoprime_two_of_odd hz).pow_left (m := 3)
  norm_num at h
  exact h

/-- Two blocked shifts give an integer step of size at most `1` (the descent's `bad_step`, at `8`). -/
theorem blocked_step {τ : ℝ} {e k₁ k₂ : ℕ} (h₁ : Blocked τ e k₁) (h₂ : Blocked τ e k₂) :
    ∃ w : ℤ, |(e : ℤ) * ((k₁ : ℤ) - k₂) - 8 * w| ≤ 1 := by
  obtain ⟨K₁, hK₁⟩ := circDist_eq_abs_sub_some_int ((e : ℝ) * τ / 8 + (e : ℝ) * (k₁ : ℝ) / 8)
  obtain ⟨K₂, hK₂⟩ := circDist_eq_abs_sub_some_int ((e : ℝ) * τ / 8 + (e : ℝ) * (k₂ : ℝ) / 8)
  have a₁ : |(e : ℝ) * τ / 8 + (e : ℝ) * (k₁ : ℝ) / ((8 : ℕ) : ℝ) - K₁| < ((8 : ℕ) : ℝ)⁻¹ := by
    have := h₁; unfold Blocked at this; rw [hK₁] at this; push_cast; exact this
  have a₂ : |(e : ℝ) * τ / 8 + (e : ℝ) * (k₂ : ℝ) / ((8 : ℕ) : ℝ) - K₂| < ((8 : ℕ) : ℝ)⁻¹ := by
    have := h₂; unfold Blocked at this; rw [hK₂] at this; push_cast; exact this
  refine ⟨K₁ - K₂, ?_⟩
  have := bad_step (n := 8) (by norm_num) ((e : ℝ) * τ / 8) e a₁ a₂
  push_cast at this
  exact this

/-- **An odd non-multiple blocks at most one shift of each parity.** -/
theorem odd_blocked_same_parity {τ : ℝ} {e k₁ k₂ : ℕ} (he : ¬ 2 ∣ e) (hk₁ : k₁ < 8) (hk₂ : k₂ < 8)
    (h₁ : Blocked τ e k₁) (h₂ : Blocked τ e k₂) (hpar : k₁ % 2 = k₂ % 2) : k₁ = k₂ := by
  obtain ⟨w, hw⟩ := blocked_step h₁ h₂
  have hD : (2 : ℤ) ∣ ((k₁ : ℤ) - k₂) := by omega
  obtain ⟨q, hq⟩ := hD
  set u : ℤ := (e : ℤ) * q with hu
  have hσ : (e : ℤ) * ((k₁ : ℤ) - k₂) - 8 * w = 2 * u - 8 * w := by rw [hq, hu]; ring
  rw [hσ, abs_le] at hw
  have hzero : 2 * u - 8 * w = 0 := by omega
  have hdvd : (8 : ℤ) ∣ (e : ℤ) * ((k₁ : ℤ) - k₂) := ⟨w, by rw [hq, ← mul_assoc, mul_comm (e : ℤ) 2, mul_assoc, ← hu]; linarith⟩
  have he' : ¬ (2 : ℤ) ∣ (e : ℤ) := by exact_mod_cast he
  have h8 : (8 : ℤ) ∣ ((k₁ : ℤ) - k₂) := (isCoprime_eight_of_odd he').dvd_of_dvd_mul_left hdvd
  omega

/-- **An even non-multiple blocks shifts of one parity only.** -/
theorem even_blocked_parity {τ : ℝ} {e k₁ k₂ : ℕ} (he2 : 2 ∣ e) (he8 : ¬ 8 ∣ e)
    (h₁ : Blocked τ e k₁) (h₂ : Blocked τ e k₂) : k₁ % 2 = k₂ % 2 := by
  by_contra hne
  obtain ⟨w, hw⟩ := blocked_step h₁ h₂
  obtain ⟨e', he'⟩ := he2
  set u : ℤ := (e' : ℤ) * ((k₁ : ℤ) - k₂) with hu
  have hσ : (e : ℤ) * ((k₁ : ℤ) - k₂) - 8 * w = 2 * u - 8 * w := by rw [hu, he']; push_cast; ring
  rw [hσ, abs_le] at hw
  have hzero : 2 * u - 8 * w = 0 := by omega
  have hdvd : (8 : ℤ) ∣ ((k₁ : ℤ) - k₂) * (e : ℤ) := ⟨w, by rw [he']; push_cast; rw [hu] at hzero; linarith⟩
  have hodd : ¬ (2 : ℤ) ∣ ((k₁ : ℤ) - k₂) := by omega
  have h8 : (8 : ℤ) ∣ (e : ℤ) := (isCoprime_eight_of_odd hodd).dvd_of_dvd_mul_left hdvd
  exact he8 (by exact_mod_cast h8)

/-- **The parity split.**  Divide the even non-multiples of `E` into two groups `A` and the rest:
one side's total `#odd + ∑ gcd e 8` is below `4`. -/
def ParitySplit8 (E : Finset ℕ) : Prop :=
  ∀ A ∈ (E.filter (fun e => 2 ∣ e)).powerset,
    (E.filter (fun e => ¬ 2 ∣ e)).card + ∑ e ∈ A, Nat.gcd e 8 < 4 ∨
      (E.filter (fun e => ¬ 2 ∣ e)).card + ∑ e ∈ (E.filter (fun e => 2 ∣ e)) \ A, Nat.gcd e 8 < 4

instance (E : Finset ℕ) : Decidable (ParitySplit8 E) := by
  unfold ParitySplit8; infer_instance

/-- An even non-multiple of `8` has `gcd e 8 ≥ 2`, so `max 2 (gcd e 8) = gcd e 8`. -/
theorem two_le_gcd_of_even {e : ℕ} (he2 : 2 ∣ e) : 2 ≤ Nat.gcd e 8 :=
  Nat.le_of_dvd (Nat.gcd_pos_of_pos_right e (by norm_num)) (Nat.dvd_gcd he2 (by norm_num))

/-- An even non-multiple blocks at most `gcd e 8` shifts. -/
theorem card_blocked_le_gcd (τ : ℝ) {e : ℕ} (he2 : 2 ∣ e) :
    ((Finset.range 8).filter (fun k => Blocked τ e k)).card ≤ Nat.gcd e 8 := by
  classical
  have h := card_bad_le (n := 8) (by norm_num) ((e : ℝ) * τ / 8) e
  have hm : max 2 (Nat.gcd e 8) = Nat.gcd e 8 := max_eq_right (two_le_gcd_of_even he2)
  rw [hm] at h
  convert h using 3

/-- **Some shift is free.**  Under the parity split, at every offset `τ` some shift `k < 8` is
blocked by no member of `E`. -/
theorem exists_free_shift (E : Finset ℕ) (hE : ∀ e ∈ E, ¬ 8 ∣ e) (hsplit : ParitySplit8 E)
    (τ : ℝ) : ∃ k, k < 8 ∧ ∀ e ∈ E, ¬ Blocked τ e k := by
  classical
  set Od := E.filter (fun e => ¬ 2 ∣ e) with hOd
  set Ev := E.filter (fun e => 2 ∣ e) with hEv
  set Bad : ℕ → Finset ℕ := fun e => (Finset.range 8).filter (fun k => Blocked τ e k) with hBad
  set A := Ev.filter (fun e => ∃ k ∈ Bad e, k % 2 = 0) with hA
  set Evens := (Finset.range 8).filter (fun k => k % 2 = 0) with hEvens
  set Odds := (Finset.range 8).filter (fun k => k % 2 = 1) with hOdds
  have hEvc : Evens.card = 4 := by rw [hEvens]; decide
  have hOdc : Odds.card = 4 := by rw [hOdds]; decide
  -- an odd member blocks at most one shift of a given parity
  have hodd_one : ∀ e ∈ Od, ∀ p, ((Bad e).filter (fun k => k % 2 = p)).card ≤ 1 := by
    intro e he p
    apply Finset.card_le_one.mpr
    intro a ha b hb
    obtain ⟨ha1, ha2⟩ := Finset.mem_filter.mp ha
    obtain ⟨hb1, hb2⟩ := Finset.mem_filter.mp hb
    obtain ⟨ha3, ha4⟩ := Finset.mem_filter.mp ha1
    obtain ⟨hb3, hb4⟩ := Finset.mem_filter.mp hb1
    exact odd_blocked_same_parity (Finset.mem_filter.mp he).2 (Finset.mem_range.mp ha3)
      (Finset.mem_range.mp hb3) ha4 hb4 (by rw [ha2, hb2])
  have hev_le : ∀ e ∈ Ev, (Bad e).card ≤ Nat.gcd e 8 :=
    fun e he => card_blocked_le_gcd τ (Finset.mem_filter.mp he).2
  -- the blocked even shifts
  set BE := Evens.filter (fun k => ∃ e ∈ E, Blocked τ e k) with hBE
  set BO := Odds.filter (fun k => ∃ e ∈ E, Blocked τ e k) with hBO
  have hBEsub : BE ⊆ (Od.biUnion (fun e => (Bad e).filter (fun k => k % 2 = 0))) ∪ A.biUnion Bad := by
    intro k hk
    obtain ⟨hk1, e, he, hb⟩ := Finset.mem_filter.mp hk
    obtain ⟨hkr, hk0⟩ := Finset.mem_filter.mp hk1
    have hkB : k ∈ Bad e := Finset.mem_filter.mpr ⟨hkr, hb⟩
    by_cases h2 : 2 ∣ e
    · refine Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨e, ?_, hkB⟩)
      exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨he, h2⟩, ⟨k, hkB, hk0⟩⟩
    · exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr
        ⟨e, Finset.mem_filter.mpr ⟨he, h2⟩, Finset.mem_filter.mpr ⟨hkB, hk0⟩⟩)
  have hBOsub : BO ⊆ (Od.biUnion (fun e => (Bad e).filter (fun k => k % 2 = 1))) ∪ (Ev \ A).biUnion Bad := by
    intro k hk
    obtain ⟨hk1, e, he, hb⟩ := Finset.mem_filter.mp hk
    obtain ⟨hkr, hk1'⟩ := Finset.mem_filter.mp hk1
    have hkB : k ∈ Bad e := Finset.mem_filter.mpr ⟨hkr, hb⟩
    by_cases h2 : 2 ∣ e
    · refine Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨e, ?_, hkB⟩)
      refine Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨he, h2⟩, fun hA' => ?_⟩
      obtain ⟨-, k', hk'B, hk'0⟩ := Finset.mem_filter.mp hA'
      have := even_blocked_parity h2 (hE e he) (Finset.mem_filter.mp hk'B).2 hb
      omega
    · exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr
        ⟨e, Finset.mem_filter.mpr ⟨he, h2⟩, Finset.mem_filter.mpr ⟨hkB, hk1'⟩⟩)
  have hBEcard : BE.card ≤ Od.card + ∑ e ∈ A, Nat.gcd e 8 := by
    calc BE.card ≤ ((Od.biUnion (fun e => (Bad e).filter (fun k => k % 2 = 0))) ∪ A.biUnion Bad).card :=
          Finset.card_le_card hBEsub
      _ ≤ (Od.biUnion (fun e => (Bad e).filter (fun k => k % 2 = 0))).card + (A.biUnion Bad).card :=
          Finset.card_union_le _ _
      _ ≤ (∑ e ∈ Od, ((Bad e).filter (fun k => k % 2 = 0)).card) + ∑ e ∈ A, (Bad e).card :=
          Nat.add_le_add Finset.card_biUnion_le Finset.card_biUnion_le
      _ ≤ (∑ _e ∈ Od, 1) + ∑ e ∈ A, Nat.gcd e 8 :=
          Nat.add_le_add (Finset.sum_le_sum fun e he => hodd_one e he 0)
            (Finset.sum_le_sum fun e he => hev_le e (Finset.mem_filter.mp he).1)
      _ = Od.card + ∑ e ∈ A, Nat.gcd e 8 := by simp
  have hBOcard : BO.card ≤ Od.card + ∑ e ∈ Ev \ A, Nat.gcd e 8 := by
    calc BO.card ≤ ((Od.biUnion (fun e => (Bad e).filter (fun k => k % 2 = 1))) ∪ (Ev \ A).biUnion Bad).card :=
          Finset.card_le_card hBOsub
      _ ≤ (Od.biUnion (fun e => (Bad e).filter (fun k => k % 2 = 1))).card + ((Ev \ A).biUnion Bad).card :=
          Finset.card_union_le _ _
      _ ≤ (∑ e ∈ Od, ((Bad e).filter (fun k => k % 2 = 1)).card) + ∑ e ∈ Ev \ A, (Bad e).card :=
          Nat.add_le_add Finset.card_biUnion_le Finset.card_biUnion_le
      _ ≤ (∑ _e ∈ Od, 1) + ∑ e ∈ Ev \ A, Nat.gcd e 8 :=
          Nat.add_le_add (Finset.sum_le_sum fun e he => hodd_one e he 1)
            (Finset.sum_le_sum fun e he => hev_le e (Finset.mem_sdiff.mp he).1)
      _ = Od.card + ∑ e ∈ Ev \ A, Nat.gcd e 8 := by simp
  have hAsub : A ∈ Ev.powerset := Finset.mem_powerset.mpr (Finset.filter_subset _ _)
  rcases hsplit A hAsub with h | h
  · have hlt : BE.card < Evens.card := by rw [hEvc]; exact lt_of_le_of_lt hBEcard h
    obtain ⟨k, hk, hkn⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
    refine ⟨k, Finset.mem_range.mp (Finset.mem_filter.mp hk).1, fun e he hb => hkn ?_⟩
    exact Finset.mem_filter.mpr ⟨hk, e, he, hb⟩
  · have hlt : BO.card < Odds.card := by rw [hOdc]; exact lt_of_le_of_lt hBOcard h
    obtain ⟨k, hk, hkn⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
    refine ⟨k, Finset.mem_range.mp (Finset.mem_filter.mp hk).1, fun e he hb => hkn ?_⟩
    exact Finset.mem_filter.mpr ⟨hk, e, he, hb⟩

/-- **The parity descent.**  Let `E` be non-multiples of `8` satisfying the parity split, and `M`
the cofactors of the multiples.  `E ∪ 8·M` is lonely at `1/8` exactly when `M` is. -/
theorem lonely_parity_descent_iff (E : Finset ℕ) (M : List ℕ) (hE : ∀ e ∈ E, ¬ 8 ∣ e)
    (hsplit : ParitySplit8 E) :
    (∃ t : ℝ, 0 < t ∧ (∀ e ∈ E, (8 : ℝ)⁻¹ ≤ circDist ((e : ℝ) * t)) ∧
        ∀ m ∈ M, (8 : ℝ)⁻¹ ≤ circDist (((8 * m : ℕ) : ℝ) * t)) ↔
      (∃ τ : ℝ, 0 < τ ∧ ∀ m ∈ M, (8 : ℝ)⁻¹ ≤ circDist ((m : ℝ) * τ)) := by
  constructor
  · rintro ⟨t, ht, -, hM⟩
    refine ⟨8 * t, by positivity, fun m hm => ?_⟩
    have h := hM m hm
    have heq : ((8 * m : ℕ) : ℝ) * t = (m : ℝ) * (8 * t) := by push_cast; ring
    rwa [heq] at h
  · rintro ⟨τ, hτ, hM⟩
    obtain ⟨k, -, hk⟩ := exists_free_shift E hE hsplit τ
    refine ⟨(τ + k) / 8, by positivity, fun e he => ?_, fun m hm => ?_⟩
    · have hclear := hk e he
      unfold Blocked at hclear
      have heq : (e : ℝ) * ((τ + k) / 8) = (e : ℝ) * τ / 8 + (e : ℝ) * (k : ℝ) / 8 := by ring
      rw [heq]
      exact not_lt.mp hclear
    · have heq : ((8 * m : ℕ) : ℝ) * ((τ + k) / 8) = (m : ℝ) * τ + (((m * k : ℕ) : ℤ) : ℝ) := by
        push_cast; ring
      rw [heq, circDist_add_int]
      exact hM m hm

/-- **The split extends the descent's budget.**  `∑ max 2 (gcd e 8) < 8` implies the parity
split. -/
theorem paritySplit_of_cost (E : Finset ℕ)
    (hcost : ∑ e ∈ E, max 2 (Nat.gcd e 8) < 8) : ParitySplit8 E := by
  classical
  intro A hA
  rw [Finset.mem_powerset] at hA
  set Od := E.filter (fun e => ¬ 2 ∣ e)
  set Ev := E.filter (fun e => 2 ∣ e)
  have hsplitsum : ∑ e ∈ E, max 2 (Nat.gcd e 8) =
      ∑ e ∈ Ev, max 2 (Nat.gcd e 8) + ∑ e ∈ Od, max 2 (Nat.gcd e 8) :=
    (Finset.sum_filter_add_sum_filter_not E (fun e => 2 ∣ e) _).symm
  have hOd : ∑ e ∈ Od, max 2 (Nat.gcd e 8) = 2 * Od.card := by
    rw [Finset.card_eq_sum_ones, Finset.mul_sum]
    refine Finset.sum_congr rfl fun e he => ?_
    have hodd := (Finset.mem_filter.mp he).2
    have hg : Nat.gcd e 8 ≤ 1 := by
      have hdvd : Nat.gcd e 8 ∣ 8 := Nat.gcd_dvd_right e 8
      have hdvd' : Nat.gcd e 8 ∣ e := Nat.gcd_dvd_left e 8
      have hpos : 0 < Nat.gcd e 8 := Nat.gcd_pos_of_pos_right e (by norm_num)
      have hle : Nat.gcd e 8 ≤ 8 := Nat.le_of_dvd (by norm_num) hdvd
      interval_cases h : Nat.gcd e 8 <;> omega
    omega
  have hEv : ∑ e ∈ Ev, max 2 (Nat.gcd e 8) = ∑ e ∈ Ev, Nat.gcd e 8 :=
    Finset.sum_congr rfl fun e he => max_eq_right (two_le_gcd_of_even (Finset.mem_filter.mp he).2)
  have hsd : ∑ e ∈ Ev, Nat.gcd e 8 = ∑ e ∈ Ev \ A, Nat.gcd e 8 + ∑ e ∈ A, Nat.gcd e 8 :=
    (Finset.sum_sdiff hA).symm
  rw [hsplitsum, hOd, hEv, hsd] at hcost
  omega

/-! ## Quarter shifts

At `t + j/4`, `j = 0, 1, 2, 3`, a multiple of `4` keeps its position (it moves by whole laps) and an odd
reading `b` visits four points `b·t + b·j/4`, one quarter apart.  Two of them in the open blocked arc
of length `1/4` would differ by less than `1/4`, so an odd reading is in the way at most once among
the four shifts (`odd_quarter_once`), and at most three odd readings leave a shift free
(`exists_quarter_shift`).  A count of equally spaced points against an arc, used as a tool. -/

/-- **An odd reading is in the way at most once among the four quarter shifts.** -/
theorem odd_quarter_once {b : ℕ} (hb : ¬ 2 ∣ b) (t : ℝ) {j₁ j₂ : ℕ} (hj₁ : j₁ < 4) (hj₂ : j₂ < 4)
    (h₁ : circDist ((b : ℝ) * (t + (j₁ : ℝ) / 4)) < (8 : ℝ)⁻¹)
    (h₂ : circDist ((b : ℝ) * (t + (j₂ : ℝ) / 4)) < (8 : ℝ)⁻¹) : j₁ = j₂ := by
  obtain ⟨K₁, hK₁⟩ := circDist_eq_abs_sub_some_int ((b : ℝ) * (t + (j₁ : ℝ) / 4))
  obtain ⟨K₂, hK₂⟩ := circDist_eq_abs_sub_some_int ((b : ℝ) * (t + (j₂ : ℝ) / 4))
  rw [hK₁, abs_lt] at h₁
  rw [hK₂, abs_lt] at h₂
  have hlt : |(((b : ℤ) * ((j₁ : ℤ) - j₂) - 4 * (K₁ - K₂) : ℤ) : ℝ)| < 1 := by
    have heq : (((b : ℤ) * ((j₁ : ℤ) - j₂) - 4 * (K₁ - K₂) : ℤ) : ℝ)
        = 4 * (((b : ℝ) * (t + (j₁ : ℝ) / 4) - K₁) - ((b : ℝ) * (t + (j₂ : ℝ) / 4) - K₂)) := by
      push_cast; ring
    rw [heq, abs_lt]
    constructor <;> linarith [h₁.1, h₁.2, h₂.1, h₂.2]
  have hlt' : |((b : ℤ) * ((j₁ : ℤ) - j₂) - 4 * (K₁ - K₂) : ℤ)| < 1 := by exact_mod_cast hlt
  have h0 : (b : ℤ) * ((j₁ : ℤ) - j₂) - 4 * (K₁ - K₂) = 0 := by rw [abs_lt] at hlt'; omega
  have h4 : (4 : ℤ) ∣ (b : ℤ) * ((j₁ : ℤ) - j₂) := ⟨K₁ - K₂, by linarith⟩
  have hb' : ¬ (2 : ℤ) ∣ (b : ℤ) := by exact_mod_cast hb
  have hcop : IsCoprime (4 : ℤ) (b : ℤ) := by
    have h := (isCoprime_two_of_odd hb').pow_left (m := 2)
    norm_num at h
    exact h
  have hd : (4 : ℤ) ∣ ((j₁ : ℤ) - j₂) := by
    have h4' : (4 : ℤ) ∣ ((j₁ : ℤ) - j₂) * (b : ℤ) := by rw [mul_comm]; exact h4
    exact hcop.dvd_of_dvd_mul_right h4'
  omega

/-- **Quarter shifts.**  If the readings of `A` are multiples of `4` and clear at `t`, and `B` is a set
of at most three odd readings, some `t + j/4`, `j < 4`, clears every reading of `A` and of `B`. -/
theorem exists_quarter_shift (A B : Finset ℕ) (hA : ∀ a ∈ A, 4 ∣ a) (hB : ∀ b ∈ B, ¬ 2 ∣ b)
    (hB3 : B.card ≤ 3) (t : ℝ) (hAt : ∀ a ∈ A, (8 : ℝ)⁻¹ ≤ circDist ((a : ℝ) * t)) :
    ∃ j : ℕ, j < 4 ∧ (∀ a ∈ A, (8 : ℝ)⁻¹ ≤ circDist ((a : ℝ) * (t + (j : ℝ) / 4))) ∧
      ∀ b ∈ B, (8 : ℝ)⁻¹ ≤ circDist ((b : ℝ) * (t + (j : ℝ) / 4)) := by
  classical
  set Bad : ℕ → Finset ℕ := fun b => (Finset.range 4).filter
    (fun j : ℕ => circDist ((b : ℝ) * (t + (j : ℝ) / 4)) < (8 : ℝ)⁻¹) with hBad
  have hone : ∀ b ∈ B, (Bad b).card ≤ 1 := by
    intro b hb
    apply Finset.card_le_one.mpr
    intro x hx y hy
    obtain ⟨hx1, hx2⟩ := Finset.mem_filter.mp hx
    obtain ⟨hy1, hy2⟩ := Finset.mem_filter.mp hy
    exact odd_quarter_once (hB b hb) t (Finset.mem_range.mp hx1) (Finset.mem_range.mp hy1) hx2 hy2
  have hcard : (B.biUnion Bad).card < (Finset.range 4).card := by
    rw [Finset.card_range]
    calc (B.biUnion Bad).card ≤ ∑ b ∈ B, (Bad b).card := Finset.card_biUnion_le
      _ ≤ ∑ _b ∈ B, 1 := Finset.sum_le_sum hone
      _ = B.card := by simp
      _ < 4 := by omega
  obtain ⟨j, hj, hjn⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  refine ⟨j, Finset.mem_range.mp hj, fun a ha => ?_, fun b hb => ?_⟩
  · obtain ⟨c, hc⟩ := hA a ha
    have heq : (a : ℝ) * (t + (j : ℝ) / 4) = (a : ℝ) * t + (((c * j : ℕ) : ℤ) : ℝ) := by
      rw [hc]; push_cast; ring
    rw [heq, circDist_add_int]
    exact hAt a ha
  · by_contra h
    push Not at h
    exact hjn (Finset.mem_biUnion.mpr ⟨b, hb, Finset.mem_filter.mpr ⟨hj, h⟩⟩)

/-! ## A silent reading `≡ 4 (mod 8)`

A reading `f = 4u`, `u` odd, reads `u·τ/2 + u·k/2` at the shift `k`: two positions half a lap apart.
When `‖u·τ‖ ≥ 1/4` both lie in `[1/8, 3/8] ∪ [5/8, 7/8]`, so `f` blocks no shift (`silent_of_quarter`).
Of `x` and `x + 1/2` one is at least `1/4` from the integers (`half_or_quarter`), and an odd `u` moves
by exactly half a lap when `τ` moves by `1/2`.  So from an instant `σ` at which the numbers `c/2`
(`c` even) and `c` (`c` odd) are clear at `1/4`, one of `σ/2`, `σ/2 + 1/2` clears the cofactors at
`1/8` and silences `f` (`exists_silent_offset`). -/

/-- Of `x` and `x + 1/2`, one is at least `1/4` from the integers. -/
theorem half_or_quarter (x : ℝ) : (4 : ℝ)⁻¹ ≤ circDist x ∨ (4 : ℝ)⁻¹ ≤ circDist (x + 1 / 2) := by
  by_contra h
  push Not at h
  obtain ⟨h1, h2⟩ := h
  obtain ⟨K₁, hK₁⟩ := circDist_eq_abs_sub_some_int x
  obtain ⟨K₂, hK₂⟩ := circDist_eq_abs_sub_some_int (x + 1 / 2)
  rw [hK₁, abs_lt] at h1
  rw [hK₂, abs_lt] at h2
  have hlo : ((K₂ : ℝ) - K₁) > 0 := by linarith [h1.1, h1.2, h2.1, h2.2]
  have hhi : ((K₂ : ℝ) - K₁) < 1 := by linarith [h1.1, h1.2, h2.1, h2.2]
  have hlo' : (K₂ - K₁ : ℤ) > 0 := by exact_mod_cast hlo
  have hhi' : (K₂ - K₁ : ℤ) < 1 := by exact_mod_cast hhi
  omega

/-- If `2y` is at least `1/4` from the integers, then `y` and `y + 1/2` are at least `1/8` from them. -/
theorem eighth_of_double {y : ℝ} (h : (4 : ℝ)⁻¹ ≤ circDist (2 * y)) :
    (8 : ℝ)⁻¹ ≤ circDist y ∧ (8 : ℝ)⁻¹ ≤ circDist (y + 1 / 2) := by
  constructor
  · by_contra hc
    push Not at hc
    obtain ⟨K, hK⟩ := circDist_eq_abs_sub_some_int y
    rw [hK, abs_lt] at hc
    have hle := circDist_le_abs_sub_int (2 * y) (2 * K)
    have : |2 * y - ((2 * K : ℤ) : ℝ)| < (4 : ℝ)⁻¹ := by
      push_cast; rw [abs_lt]; constructor <;> linarith [hc.1, hc.2]
    linarith
  · by_contra hc
    push Not at hc
    obtain ⟨K, hK⟩ := circDist_eq_abs_sub_some_int (y + 1 / 2)
    rw [hK, abs_lt] at hc
    have hle := circDist_le_abs_sub_int (2 * y) (2 * K - 1)
    have : |2 * y - ((2 * K - 1 : ℤ) : ℝ)| < (4 : ℝ)⁻¹ := by
      push_cast; rw [abs_lt]; constructor <;> linarith [hc.1, hc.2]
    linarith

/-- **A reading `4u`, `u` odd, with `‖u·τ‖ ≥ 1/4` blocks no shift.** -/
theorem silent_of_quarter {u : ℕ} (hu : ¬ 2 ∣ u) {τ : ℝ} (h : (4 : ℝ)⁻¹ ≤ circDist ((u : ℝ) * τ)) (k : ℕ) :
    ¬ Blocked τ (4 * u) k := by
  unfold Blocked
  push Not
  obtain ⟨m, hm⟩ : ∃ m : ℕ, u = 2 * m + 1 := ⟨u / 2, by omega⟩
  have h2 := eighth_of_double (y := (u : ℝ) * τ / 2) (by
    have : 2 * ((u : ℝ) * τ / 2) = (u : ℝ) * τ := by ring
    rw [this]; exact h)
  rcases Nat.even_or_odd k with ⟨j, hj⟩ | ⟨j, hj⟩
  · have heq : ((4 * u : ℕ) : ℝ) * τ / 8 + ((4 * u : ℕ) : ℝ) * (k : ℝ) / 8
        = (u : ℝ) * τ / 2 + (((u * j : ℕ) : ℤ) : ℝ) := by
      rw [hj]; push_cast; ring
    rw [heq, circDist_add_int]; exact h2.1
  · have heq : ((4 * u : ℕ) : ℝ) * τ / 8 + ((4 * u : ℕ) : ℝ) * (k : ℝ) / 8
        = ((u : ℝ) * τ / 2 + 1 / 2) + (((2 * m * j + m + j : ℕ) : ℤ) : ℝ) := by
      rw [hj, hm]; push_cast; ring
    rw [heq, circDist_add_int]; exact h2.2

end LRC.ParityDescent

namespace LRC.OrderEightN

open ConstructionN LRC.Descent LRC.ParityDescent

/-- **Order eight, the parity descent.**  A set of positive whole numbers with at most six
multiples of `8` whose non-multiples satisfy the parity split is lonely at `1/8`: the cofactors go
to order seven (`lonely_eight_of_card_le_six`, as in `lonely_eight_of_descent`) and a free shift
carries the non-multiples. -/
theorem lonely_eight_of_parity_descent {S : Finset ℕ} (hpos : ∀ d ∈ S, 0 < d)
    (hsplit : ParitySplit8 (S.filter (fun d => ¬ 8 ∣ d)))
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
  have hE : ∀ e ∈ E, ¬ 8 ∣ e := fun e he => (Finset.mem_filter.mp he).2
  obtain ⟨t, ht, hEt, hMt⟩ := (lonely_parity_descent_iff E C.toList hE hsplit).mpr
    ⟨τ, hτ, fun m hm => by simpa using hC m (Finset.mem_toList.mp hm)⟩
  refine ⟨t, ht, fun d hd => ?_⟩
  by_cases h8 : 8 ∣ d
  · obtain ⟨m, rfl⟩ := h8
    have hmC : m ∈ C.toList := Finset.mem_toList.mpr (Finset.mem_image.mpr
      ⟨8 * m, Finset.mem_filter.mpr ⟨hd, dvd_mul_right 8 m⟩, by omega⟩)
    simpa using hMt m hmC
  · simpa using hEt d (Finset.mem_filter.mpr ⟨hd, h8⟩)

/-- **The split holds when at most one non-multiple is even and at most three are odd**: one of
the two groups is empty, and its side is `#odd ≤ 3`. -/
theorem paritySplit_of_even_le_one (E : Finset ℕ)
    (hEv : (E.filter (fun e => 2 ∣ e)).card ≤ 1) (hOd : (E.filter (fun e => ¬ 2 ∣ e)).card ≤ 3) :
    ParitySplit8 E := by
  classical
  intro A hA
  rw [Finset.mem_powerset] at hA
  rcases Finset.card_le_one.mp hEv |> fun h => (Finset.eq_empty_or_nonempty A) with hA0 | ⟨a, ha⟩
  · left; rw [hA0, Finset.sum_empty]; omega
  · right
    have hsd : (E.filter (fun e => 2 ∣ e)) \ A = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro x hx
      obtain ⟨hx1, hx2⟩ := Finset.mem_sdiff.mp hx
      exact hx2 (by rw [Finset.card_le_one.mp hEv x hx1 a (hA ha)]; exact ha)
    rw [hsd, Finset.sum_empty]; omega

/-- **A residual set has at least two odd readings**: one is `EightResidual.odd`, and if it were
the only one the other six would all be even, against `no_one_free` at `g = 2`. -/
theorem two_le_odd_of_residual {S : Finset ℕ} (hres : EightResidual S) :
    2 ≤ (S.filter (fun d => ¬ 2 ∣ d)).card := by
  classical
  by_contra hlt
  push Not at hlt
  obtain ⟨x, hxS, hx⟩ := hres.odd
  have hxmem : x ∈ S.filter (fun d => ¬ 2 ∣ d) := Finset.mem_filter.mpr ⟨hxS, hx⟩
  have hle : (S.filter (fun d => ¬ 2 ∣ d)).card ≤ 1 := by omega
  have hall : ∀ d ∈ S, d ≠ x → 2 ∣ d := by
    intro d hd hdx
    by_contra hd2
    exact hdx (Finset.card_le_one.mp hle d (Finset.mem_filter.mpr ⟨hd, hd2⟩) x hxmem)
  exact hx (hres.no_one_free x hxS 2 le_rfl hall)

/-- The odd members of the non-multiples are the odd members of the set. -/
theorem odd_filter_nonmult (S : Finset ℕ) :
    (S.filter (fun d => ¬ 8 ∣ d)).filter (fun e => ¬ 2 ∣ e) = S.filter (fun d => ¬ 2 ∣ d) := by
  classical
  rw [Finset.filter_filter]
  refine Finset.filter_congr fun d _ => ⟨fun h => h.2, fun h => ⟨fun h8 => h (dvd_trans (by norm_num) h8), h⟩⟩

/-- **Shape `(4, 3)` of the residual is settled.**  A residual set with four multiples of `8` has
three non-multiples, at least two of them odd, so at most one even: the parity split holds and the
parity descent gives a lonely instant. -/
theorem lonely_eight_of_residual_four_multiples {S : Finset ℕ} (hpos : ∀ d ∈ S, 0 < d)
    (hres : EightResidual S) (h4 : (S.filter (fun d => 8 ∣ d)).card = 4) :
    ∃ t : ℝ, 0 < t ∧ ∀ d ∈ S, (8 : ℝ)⁻¹ ≤ circDist ((d : ℝ) * t) := by
  classical
  have hE3 : (S.filter (fun d => ¬ 8 ∣ d)).card = 3 := by
    have := Finset.card_filter_add_card_filter_not (s := S) (fun d => 8 ∣ d)
    rw [hres.card_eq, h4] at this; omega
  have hodd2 := two_le_odd_of_residual hres
  rw [← odd_filter_nonmult S] at hodd2
  have hsum := Finset.card_filter_add_card_filter_not (s := S.filter (fun d => ¬ 8 ∣ d)) (fun e => 2 ∣ e)
  refine lonely_eight_of_parity_descent hpos ?_ (by omega)
  exact paritySplit_of_even_le_one _ (by omega) (by omega)

/-- **Shape `(3, 4)` with exactly three odd non-multiples is settled** the same way: the fourth
non-multiple is the only even one. -/
theorem lonely_eight_of_three_multiples_three_odd {S : Finset ℕ} (hpos : ∀ d ∈ S, 0 < d)
    (hc7 : S.card = 7) (h3 : (S.filter (fun d => 8 ∣ d)).card = 3)
    (hodd3 : (S.filter (fun d => ¬ 2 ∣ d)).card = 3) :
    ∃ t : ℝ, 0 < t ∧ ∀ d ∈ S, (8 : ℝ)⁻¹ ≤ circDist ((d : ℝ) * t) := by
  classical
  have hE4 : (S.filter (fun d => ¬ 8 ∣ d)).card = 4 := by
    have := Finset.card_filter_add_card_filter_not (s := S) (fun d => 8 ∣ d)
    rw [hc7, h3] at this; omega
  rw [← odd_filter_nonmult S] at hodd3
  have hsum := Finset.card_filter_add_card_filter_not (s := S.filter (fun d => ¬ 8 ∣ d)) (fun e => 2 ∣ e)
  refine lonely_eight_of_parity_descent hpos ?_ (by omega)
  exact paritySplit_of_even_le_one _ (by omega) (by omega)

/-- **No reading `≡ 2 (mod 4)` and at most three odd ones.**  The multiples of `4` (at most six) are
lonely at some `t` by order seven (`lonely_eight_of_card_le_six`), and a quarter shift carries the odd
readings. -/
theorem lonely_eight_of_quarter_shift {S : Finset ℕ} (hpos : ∀ d ∈ S, 0 < d)
    (hno2 : ∀ d ∈ S, 2 ∣ d → 4 ∣ d) (hodd : (S.filter (fun d => ¬ 2 ∣ d)).card ≤ 3)
    (h4 : (S.filter (fun d => 4 ∣ d)).card ≤ 6) :
    ∃ t : ℝ, 0 < t ∧ ∀ d ∈ S, (8 : ℝ)⁻¹ ≤ circDist ((d : ℝ) * t) := by
  classical
  set A := S.filter (fun d => 4 ∣ d) with hAdef
  set B := S.filter (fun d => ¬ 2 ∣ d) with hBdef
  have hApos : ∀ a ∈ A, 0 < a := fun a ha => hpos a (Finset.mem_filter.mp ha).1
  obtain ⟨t, ht, hAt⟩ := lonely_eight_of_card_le_six hApos h4
  obtain ⟨j, -, hAj, hBj⟩ := exists_quarter_shift A B (fun a ha => (Finset.mem_filter.mp ha).2)
    (fun b hb => (Finset.mem_filter.mp hb).2) hodd t hAt
  refine ⟨t + (j : ℝ) / 4, by positivity, fun d hd => ?_⟩
  by_cases h2 : 2 ∣ d
  · exact hAj d (Finset.mem_filter.mpr ⟨hd, hno2 d hd h2⟩)
  · exact hBj d (Finset.mem_filter.mpr ⟨hd, h2⟩)

/-- **The residual with no reading `≡ 2 (mod 4)` and at most three odd readings is settled.**  At least
two readings are odd (`two_le_odd_of_residual`), so at most five are multiples of `4`. -/
theorem lonely_eight_of_residual_no_two_mod_four {S : Finset ℕ} (hpos : ∀ d ∈ S, 0 < d)
    (hres : EightResidual S) (hno2 : ∀ d ∈ S, 2 ∣ d → 4 ∣ d)
    (hodd : (S.filter (fun d => ¬ 2 ∣ d)).card ≤ 3) :
    ∃ t : ℝ, 0 < t ∧ ∀ d ∈ S, (8 : ℝ)⁻¹ ≤ circDist ((d : ℝ) * t) := by
  classical
  have h2 := two_le_odd_of_residual hres
  have hsub : S.filter (fun d => 4 ∣ d) ⊆ S.filter (fun d => 2 ∣ d) :=
    Finset.monotone_filter_right S (fun d _ h => dvd_trans (by norm_num : 2 ∣ 4) h)
  have hsum := Finset.card_filter_add_card_filter_not (s := S) (fun d => 2 ∣ d)
  have hle := Finset.card_le_card hsub
  rw [hres.card_eq] at hsum
  exact lonely_eight_of_quarter_shift hpos hno2 hodd (by omega)

/-- A non-multiple of `8` that is not `≡ 4 (mod 8)` costs `2`. -/
theorem max_gcd_eq_two {e : ℕ} (h8 : ¬ 8 ∣ e) (h4 : e % 8 ≠ 4) : max 2 (Nat.gcd e 8) = 2 := by
  have hdvd : Nat.gcd e 8 ∣ 8 := Nat.gcd_dvd_right e 8
  have hdvd' : Nat.gcd e 8 ∣ e := Nat.gcd_dvd_left e 8
  have hpos : 0 < Nat.gcd e 8 := Nat.gcd_pos_of_pos_right e (by norm_num)
  have hle : Nat.gcd e 8 ≤ 8 := Nat.le_of_dvd (by norm_num) hdvd
  have hg : Nat.gcd e 8 ≤ 2 := by
    interval_cases h : Nat.gcd e 8 <;> omega
  omega

/-- **One silent reading `≡ 4 (mod 8)`.**  A set of positive whole numbers with at most three
multiples of `8`, at most one reading `≡ 4 (mod 8)` and at most three other non-multiples is lonely at
`1/8`.  Order four clears `c/2` (`c` even) and `c` (`c` odd) at `1/4` at some `σ`
(`SpecN.existenceAtN_four`); one of `σ/2`, `σ/2 + 1/2` clears the cofactors at `1/8` and silences the
reading `≡ 4 (mod 8)`; the others block at most six of the eight shifts. -/
theorem lonely_eight_of_silent_four {S : Finset ℕ} (hpos : ∀ d ∈ S, 0 < d)
    (hM : (S.filter (fun d => 8 ∣ d)).card ≤ 3)
    (hF : (S.filter (fun d => d % 8 = 4)).card ≤ 1)
    (hR : (S.filter (fun d => ¬ 8 ∣ d ∧ d % 8 ≠ 4)).card ≤ 3) :
    ∃ t : ℝ, 0 < t ∧ ∀ d ∈ S, (8 : ℝ)⁻¹ ≤ circDist ((d : ℝ) * t) := by
  classical
  set C : Finset ℕ := (S.filter (fun d => 8 ∣ d)).image (fun d => d / 8) with hCdef
  have hCpos : ∀ c ∈ C, 0 < c := by
    intro c hc
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hc
    obtain ⟨hdS, h8⟩ := Finset.mem_filter.mp hd
    exact Nat.div_pos (Nat.le_of_dvd (hpos d hdS) h8) (by norm_num)
  set g : ℕ → ℝ := fun c => if 2 ∣ c then (c : ℝ) / 2 else (c : ℝ) with hg
  set C' : Finset ℝ := C.image g with hC'def
  have hC'pos : ∀ x ∈ C', 0 < x := by
    intro x hx
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hx
    have := hCpos c hc
    simp only [hg]
    split_ifs <;> positivity
  have hC'card : C'.card ≤ 4 - 1 := by
    have h1 : C'.card ≤ C.card := Finset.card_image_le
    have h2 : C.card ≤ (S.filter (fun d => 8 ∣ d)).card := Finset.card_image_le
    omega
  obtain ⟨σ, hσ, hσC⟩ := LRC.SpecN.existenceAtN_four C' hC'pos hC'card
  -- the reading `≡ 4 (mod 8)`, if any, and the choice of the half step
  obtain ⟨ε, hε01, hεf⟩ : ∃ ε : ℕ, ε < 2 ∧ ∀ f ∈ S, f % 8 = 4 →
      (4 : ℝ)⁻¹ ≤ circDist (((f / 4 : ℕ) : ℝ) * (σ / 2 + (ε : ℝ) / 2)) := by
    rcases Finset.eq_empty_or_nonempty (S.filter (fun d => d % 8 = 4)) with hE | ⟨f, hf⟩
    · refine ⟨0, by norm_num, fun f hfS hf4 => ?_⟩
      exact absurd (Finset.mem_filter.mpr ⟨hfS, hf4⟩) (by rw [hE]; exact Finset.notMem_empty _)
    · obtain ⟨hfS, hf4⟩ := Finset.mem_filter.mp hf
      have huniq : ∀ f' ∈ S, f' % 8 = 4 → f' = f := fun f' hf'S hf'4 =>
        Finset.card_le_one.mp hF f' (Finset.mem_filter.mpr ⟨hf'S, hf'4⟩) f hf
      obtain ⟨m, hm⟩ : ∃ m : ℕ, f / 4 = 2 * m + 1 := ⟨f / 8, by omega⟩
      rcases half_or_quarter (((f / 4 : ℕ) : ℝ) * σ / 2) with h0 | h1
      · refine ⟨0, by norm_num, fun f' hf'S hf'4 => ?_⟩
        rw [huniq f' hf'S hf'4]
        have : ((f / 4 : ℕ) : ℝ) * (σ / 2 + ((0 : ℕ) : ℝ) / 2) = ((f / 4 : ℕ) : ℝ) * σ / 2 := by push_cast; ring
        rw [this]; exact h0
      · refine ⟨1, by norm_num, fun f' hf'S hf'4 => ?_⟩
        rw [huniq f' hf'S hf'4]
        have : ((f / 4 : ℕ) : ℝ) * (σ / 2 + ((1 : ℕ) : ℝ) / 2)
            = (((f / 4 : ℕ) : ℝ) * σ / 2 + 1 / 2) + ((m : ℤ) : ℝ) := by rw [hm]; push_cast; ring
        rw [this, circDist_add_int]; exact h1
  set τ : ℝ := σ / 2 + (ε : ℝ) / 2 with hτ
  -- the cofactors are clear at `τ`
  have hCτ : ∀ c ∈ C, (8 : ℝ)⁻¹ ≤ circDist ((c : ℝ) * τ) := by
    intro c hc
    have hσc := hσC (g c) (Finset.mem_image_of_mem g hc)
    by_cases h2 : 2 ∣ c
    · obtain ⟨c', rfl⟩ := h2
      have hgc : g (2 * c') = ((2 * c' : ℕ) : ℝ) / 2 := by simp [hg]
      rw [hgc] at hσc
      have heq : ((2 * c' : ℕ) : ℝ) * τ = ((2 * c' : ℕ) : ℝ) / 2 * σ + (((c' * ε : ℕ) : ℤ) : ℝ) := by
        rw [hτ]; push_cast; ring
      rw [heq, circDist_add_int]
      exact le_trans (by norm_num) hσc
    · have hgc : g c = (c : ℝ) := by simp [hg, h2]
      rw [hgc] at hσc
      have hd := eighth_of_double (y := (c : ℝ) * σ / 2) (by
        have : 2 * ((c : ℝ) * σ / 2) = (c : ℝ) * σ := by ring
        rw [this]; exact hσc)
      obtain ⟨m, hm⟩ : ∃ m : ℕ, c = 2 * m + 1 := ⟨c / 2, by omega⟩
      rcases (show ε = 0 ∨ ε = 1 by omega) with he | he
      · have heq : (c : ℝ) * τ = (c : ℝ) * σ / 2 := by rw [hτ, he]; push_cast; ring
        rw [heq]; exact hd.1
      · have heq : (c : ℝ) * τ = ((c : ℝ) * σ / 2 + 1 / 2) + (((m * 1 : ℕ) : ℤ) : ℝ) := by
          rw [hτ, he, hm]; push_cast; ring
        rw [heq, circDist_add_int]; exact hd.2
  -- the other non-multiples leave a shift free
  set R := S.filter (fun d => ¬ 8 ∣ d ∧ d % 8 ≠ 4) with hRdef
  have hR8 : ∀ e ∈ R, ¬ 8 ∣ e := fun e he => (Finset.mem_filter.mp he).2.1
  have hcost : ∑ e ∈ R, max 2 (Nat.gcd e 8) < 8 := by
    have : ∑ e ∈ R, max 2 (Nat.gcd e 8) = ∑ _e ∈ R, 2 :=
      Finset.sum_congr rfl fun e he => max_gcd_eq_two (Finset.mem_filter.mp he).2.1 (Finset.mem_filter.mp he).2.2
    rw [this, Finset.sum_const, smul_eq_mul]
    omega
  obtain ⟨k, -, hk⟩ := exists_free_shift R hR8 (paritySplit_of_cost R hcost) τ
  have hτpos : 0 < τ := by rw [hτ]; positivity
  refine ⟨(τ + k) / 8, by positivity, fun d hd => ?_⟩
  by_cases h8 : 8 ∣ d
  · obtain ⟨c, rfl⟩ := h8
    have hcC : c ∈ C := Finset.mem_image.mpr ⟨8 * c, Finset.mem_filter.mpr ⟨hd, dvd_mul_right 8 c⟩, by omega⟩
    have heq : ((8 * c : ℕ) : ℝ) * ((τ + k) / 8) = (c : ℝ) * τ + (((c * k : ℕ) : ℤ) : ℝ) := by
      push_cast; ring
    rw [heq, circDist_add_int]
    exact hCτ c hcC
  · by_cases h4 : d % 8 = 4
    · obtain ⟨u, hu, hd4⟩ : ∃ u : ℕ, ¬ 2 ∣ u ∧ d = 4 * u := ⟨d / 4, by omega, by omega⟩
      have hsil := silent_of_quarter hu (τ := τ) (by
        have := hεf d hd h4
        rw [hd4, show 4 * u / 4 = u by omega] at this
        exact this) k
      unfold Blocked at hsil
      push Not at hsil
      have heq : (d : ℝ) * ((τ + k) / 8) = ((4 * u : ℕ) : ℝ) * τ / 8 + ((4 * u : ℕ) : ℝ) * (k : ℝ) / 8 := by
        rw [hd4]; ring
      rw [heq]; exact hsil
    · have hdR : d ∈ R := Finset.mem_filter.mpr ⟨hd, h8, h4⟩
      have hb := hk d hdR
      unfold Blocked at hb
      push Not at hb
      have heq : (d : ℝ) * ((τ + k) / 8) = (d : ℝ) * τ / 8 + (d : ℝ) * (k : ℝ) / 8 := by ring
      rw [heq]; exact hb

/-- A shape `(4, 3)` set of the residual's crowded level that the cost condition leaves
(`∑ max 2 (gcd e 8) = 8`) and the parity split settles: non-multiples `1, 3, 4`. -/
example : ParitySplit8 ({1, 3, 4} : Finset ℕ) := by decide

/-- Shape `(3, 4)` with non-multiples `1, 2, 6, 10` (types `o, t, t, t`, cost `8`). -/
example : ParitySplit8 ({1, 2, 6, 10} : Finset ℕ) := by decide

end LRC.OrderEightN
