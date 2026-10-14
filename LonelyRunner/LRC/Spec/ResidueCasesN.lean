import LonelyRunner.LRC.Spec.ParityMixedTwoTwoN
import LonelyRunner.LRC.Spec.ParityCoverN

set_option linter.style.longLine false

/-!
# The residue cases as one statement (order eight)

2026-10-07.  Each case below takes the isolation at the grid shifts `j/4` (quarter level) or `k/8`
(eighth level), displaced by an offset: the offset clears the readings the shifts hold still, and a
free shift carries the others.  This file composes eight such cases, each already a Lean theorem,
into one statement on the residue counts of a set `S` of positive whole numbers: `m` multiples of
`8`, `o` odd readings, `t` readings `≡ 2 (mod 4)`, `f` readings `≡ 4 (mod 8)`.  It adds no
existence step.

* `paritySplit8_iff_counts`: for a set with no multiple of `8`, the parity split `ParitySplit8 E`
  holds exactly when the count condition `CountSplit8 od a b` holds, with `od` the odd members, `a`
  the members `≡ 2 (mod 4)`, `b` the members `≡ 4 (mod 8)`.  Every pair of sub-counts `(a', b')` is
  realised by a subset of the even part, and `gcd e 8` is `2` or `4` there.
  [PROVISIONAL: counting tool; supports: the count form of the parity split]
* `SettledCounts8 m o t f`: the disjunction of the count forms of seven cases:
  - T1 `lonely_eight_of_parity_descent`: `CountSplit8 o t f` and `m ≤ 6`;
  - T2 `lonely_eight_of_quarter_shift`: `t = 0`, `o ≤ 3`, `m + f ≤ 6`;
  - T3 `lonely_eight_of_silent_four`: `m ≤ 3`, `f ≤ 1`, `o + t ≤ 3`;
  - T4 `lonely_eight_of_quarter_three_one`: `o ≤ 3`, `m + f ≤ 3`, `t ≤ 1`;
  - T5 `lonely_eight_of_eighth_le_three`: `CountSplit8 o t 0` and `m + f ≤ 3`;
  - T7 `lonely_eight_of_quarter_two_two`: `o ≤ 3`, `m + f ≤ 2`, `t ≤ 2`;
  - T8 `lonely_eight_of_eighth_two_two`: `CountSplit8 o t 0`, `m ≤ 2`, `f ≤ 2`.
* `OottCase8 S`: the hypotheses of T6 `lonely_eight_of_oott`.  `oottCase8_iff_counts`: they hold
  exactly when at most one reading is `≡ ±1 (mod 8)`, at most one is `≡ ±3 (mod 8)`, at most two
  are `≡ 2 (mod 4)`, and `m + f ≤ 3` (`OottCounts8`).
* `lonely_eight_of_settled_counts`: `SettledCounts8` of the counts of `S`, or `OottCase8 S`, makes
  `S` lonely at `1/8`.
* `lonely_eight_or_open_counts` (and `lonely_eight_or_open_counts_five`, in counts only): `S` is
  lonely at `1/8`, or neither condition holds.
* `crowded_counts_m1` … `crowded_counts_m4`, by `decide +kernel`: on the multisets of `7 − m`
  residues in `[1, 7]` with at least two odd and `∑ max 2 (gcd r 8) ≥ 8`, the number of patterns
  and the number settled by `SettledCounts8` or `OottCounts8`.  This is a consistency check between
  the Lean predicate and the script `experiments/nN/redo/lean_case_reach_v3.py`, not a cascade
  statement.

**Lower-order inputs** (read in the proofs of the cases):
* T1 and T2 rest on order seven: `OrderEightN.lonely_eight_of_card_le_six` (`OrderEightCasesN`),
  which calls `OrderSevenN.lonely_seven_nat`, for the cofactors of the multiples of `8` (T1) and for
  the multiples of `4` (T2).
* T3 calls `SpecN.existenceAtN_four` (order four) directly.
* T4 goes through `exists_mixed_le_three` (no reading `≡ 2 (mod 4)`) and `exists_mixed_three_one`
  (one such reading), both on `existenceAtN_four`.
* T5 and T6 go through `exists_mixed_le_three`.
* T7 and T8 go through `exists_mixed_two_two`, which reaches `exists_mixed_le_three` only in the
  branch where the two groups together have at most three elements.
The owner's ruling on such inputs (compilation ground rule 4) is owed.  T7 and T8 also rest on
M(2,2), whose counting steps carry their own tags in `ParityMixedTwoTwoN`.

Everything here is proved; no `sorry`, no `native_decide`.
-/

namespace LRC.ParityDescent

open ConstructionN LRC.Descent

/-! ## The count form of the parity split -/

/-- **The parity split on counts.**  `od` odd members, `a` members `≡ 2 (mod 4)`, `b` members
`≡ 4 (mod 8)`: for every choice of `a' ≤ a` and `b' ≤ b`, one side `od + 2a' + 4b'` or
`od + 2(a − a') + 4(b − b')` is below `4`. -/
def CountSplit8 (od a b : ℕ) : Prop :=
  ∀ a' ≤ a, ∀ b' ≤ b, od + 2 * a' + 4 * b' < 4 ∨ od + 2 * (a - a') + 4 * (b - b') < 4

instance (od a b : ℕ) : Decidable (CountSplit8 od a b) := by
  unfold CountSplit8; infer_instance

/-- A reading `≡ 2 (mod 4)` has `gcd e 8 = 2`. -/
theorem gcd_eight_of_mod_four_two {e : ℕ} (h : e % 4 = 2) : Nat.gcd e 8 = 2 := by
  rw [Nat.gcd_comm, Nat.gcd_rec]
  have : e % 8 = 2 ∨ e % 8 = 6 := by omega
  rcases this with h' | h' <;> rw [h'] <;> decide

/-- A reading `≡ 4 (mod 8)` has `gcd e 8 = 4`. -/
theorem gcd_eight_of_mod_eight_four {e : ℕ} (h : e % 8 = 4) : Nat.gcd e 8 = 4 := by
  rw [Nat.gcd_comm, Nat.gcd_rec, h]
  decide

/-- **The even non-multiples' total by counts**: `∑ gcd e 8 = 2·#(≡ 2 mod 4) + 4·#(≡ 4 mod 8)`. -/
theorem sum_gcd_eight (A : Finset ℕ) (hA : ∀ e ∈ A, 2 ∣ e ∧ ¬ 8 ∣ e) :
    ∑ e ∈ A, Nat.gcd e 8 =
      2 * (A.filter (fun e => e % 4 = 2)).card + 4 * (A.filter (fun e => e % 8 = 4)).card := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not A (fun e => e % 4 = 2)]
  have hf : A.filter (fun e => ¬ e % 4 = 2) = A.filter (fun e => e % 8 = 4) := by
    refine Finset.filter_congr fun e he => ?_
    obtain ⟨h2, h8⟩ := hA e he
    constructor <;> intro h <;> omega
  have h1 : ∑ e ∈ A.filter (fun e => e % 4 = 2), Nat.gcd e 8
      = ∑ _e ∈ A.filter (fun e => e % 4 = 2), (2 : ℕ) :=
    Finset.sum_congr rfl fun e he => gcd_eight_of_mod_four_two (Finset.mem_filter.mp he).2
  have h2 : ∑ e ∈ A.filter (fun e => e % 8 = 4), Nat.gcd e 8
      = ∑ _e ∈ A.filter (fun e => e % 8 = 4), (4 : ℕ) :=
    Finset.sum_congr rfl fun e he => gcd_eight_of_mod_eight_four (Finset.mem_filter.mp he).2
  rw [hf, h1, h2, Finset.sum_const, Finset.sum_const, smul_eq_mul, smul_eq_mul]
  ring

/-- **The parity split is a count condition.**  For a set `E` with no multiple of `8`,
`ParitySplit8 E` holds exactly when `CountSplit8` holds of its numbers of odd members, members
`≡ 2 (mod 4)` and members `≡ 4 (mod 8)`.
[PROVISIONAL: counting tool; supports: the count form of the parity split] -/
theorem paritySplit8_iff_counts (E : Finset ℕ) (hE : ∀ e ∈ E, ¬ 8 ∣ e) :
    ParitySplit8 E ↔ CountSplit8 (E.filter (fun e => ¬ 2 ∣ e)).card
      (E.filter (fun e => e % 4 = 2)).card (E.filter (fun e => e % 8 = 4)).card := by
  classical
  unfold ParitySplit8 CountSplit8
  set Ev := E.filter (fun e => 2 ∣ e) with hEv
  have hEvp : ∀ e ∈ Ev, 2 ∣ e ∧ ¬ 8 ∣ e := fun e he =>
    ⟨(Finset.mem_filter.mp he).2, hE e (Finset.mem_filter.mp he).1⟩
  have hT : Ev.filter (fun e => e % 4 = 2) = E.filter (fun e => e % 4 = 2) := by
    ext x
    simp only [hEv, Finset.mem_filter]
    exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, by omega⟩, h.2⟩⟩
  have hF : Ev.filter (fun e => e % 8 = 4) = E.filter (fun e => e % 8 = 4) := by
    ext x
    simp only [hEv, Finset.mem_filter]
    exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, by omega⟩, h.2⟩⟩
  have hsumEv := sum_gcd_eight Ev hEvp
  rw [hT, hF] at hsumEv
  constructor
  · intro hsplit a' ha' b' hb'
    obtain ⟨T', hT'sub, hT'card⟩ := Finset.exists_subset_card_eq ha'
    obtain ⟨F', hF'sub, hF'card⟩ := Finset.exists_subset_card_eq hb'
    have hT'p : ∀ x ∈ T', x ∈ E ∧ x % 4 = 2 := fun x hx => Finset.mem_filter.mp (hT'sub hx)
    have hF'p : ∀ x ∈ F', x ∈ E ∧ x % 8 = 4 := fun x hx => Finset.mem_filter.mp (hF'sub hx)
    have hAsub : T' ∪ F' ⊆ Ev := by
      intro x hx
      rcases Finset.mem_union.mp hx with h | h
      · obtain ⟨hxE, hx4⟩ := hT'p x h
        exact Finset.mem_filter.mpr ⟨hxE, by omega⟩
      · obtain ⟨hxE, hx8⟩ := hF'p x h
        exact Finset.mem_filter.mpr ⟨hxE, by omega⟩
    have hAT : (T' ∪ F').filter (fun e => e % 4 = 2) = T' := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_union]
      constructor
      · rintro ⟨h | h, hx⟩
        · exact h
        · have := (hF'p x h).2
          omega
      · intro h
        exact ⟨Or.inl h, (hT'p x h).2⟩
    have hAF : (T' ∪ F').filter (fun e => e % 8 = 4) = F' := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_union]
      constructor
      · rintro ⟨h | h, hx⟩
        · have := (hT'p x h).2
          omega
        · exact h
      · intro h
        exact ⟨Or.inr h, (hF'p x h).2⟩
    have hsumA := sum_gcd_eight (T' ∪ F') (fun e he => hEvp e (hAsub he))
    rw [hAT, hAF, hT'card, hF'card] at hsumA
    have hs : ∑ e ∈ Ev \ (T' ∪ F'), Nat.gcd e 8 + ∑ e ∈ T' ∪ F', Nat.gcd e 8 = ∑ e ∈ Ev, Nat.gcd e 8 :=
      Finset.sum_sdiff hAsub
    rcases hsplit (T' ∪ F') (Finset.mem_powerset.mpr hAsub) with h | h
    · left; omega
    · right; omega
  · intro hc A hA
    rw [Finset.mem_powerset] at hA
    have hsumA := sum_gcd_eight A (fun e he => hEvp e (hA he))
    have hAE : A ⊆ E := hA.trans (Finset.filter_subset _ _)
    have ha' : (A.filter (fun e => e % 4 = 2)).card ≤ (E.filter (fun e => e % 4 = 2)).card :=
      Finset.card_le_card (Finset.filter_subset_filter _ hAE)
    have hb' : (A.filter (fun e => e % 8 = 4)).card ≤ (E.filter (fun e => e % 8 = 4)).card :=
      Finset.card_le_card (Finset.filter_subset_filter _ hAE)
    have hs : ∑ e ∈ Ev \ A, Nat.gcd e 8 + ∑ e ∈ A, Nat.gcd e 8 = ∑ e ∈ Ev, Nat.gcd e 8 :=
      Finset.sum_sdiff hA
    rcases hc _ ha' _ hb' with h | h
    · left; omega
    · right; omega

/-! ## The counts of a set -/

/-- Filtering a filter by a stronger predicate. -/
theorem filter_filter_eq_of_imp (S : Finset ℕ) (p q : ℕ → Prop) [DecidablePred p] [DecidablePred q]
    (h : ∀ d, q d → p d) : (S.filter p).filter q = S.filter q := by
  ext d
  simp only [Finset.mem_filter]
  exact ⟨fun h' => ⟨h'.1.1, h'.2⟩, fun h' => ⟨⟨h'.1, h d h'.2⟩, h'.2⟩⟩

/-- Filtering a filter by an excluded predicate leaves nothing. -/
theorem card_filter_filter_eq_zero (S : Finset ℕ) (p q : ℕ → Prop) [DecidablePred p] [DecidablePred q]
    (h : ∀ d, p d → ¬ q d) : ((S.filter p).filter q).card = 0 := by
  rw [Finset.card_eq_zero]
  apply Finset.eq_empty_of_forall_notMem
  intro d hd
  simp only [Finset.mem_filter] at hd
  exact h d hd.1.2 hd.2

/-- The multiples of `4` are the multiples of `8` and the readings `≡ 4 (mod 8)`. -/
theorem card_four_dvd_eq (S : Finset ℕ) :
    (S.filter (fun d => 4 ∣ d)).card
      = (S.filter (fun d => 8 ∣ d)).card + (S.filter (fun d => d % 8 = 4)).card := by
  classical
  have heq : S.filter (fun d => 4 ∣ d) = S.filter (fun d => 8 ∣ d ∨ d % 8 = 4) :=
    Finset.filter_congr fun d _ => ⟨fun h => by omega, fun h => by omega⟩
  rw [heq, Finset.filter_or, Finset.card_union_of_disjoint]
  exact Finset.disjoint_filter.mpr fun d _ h8 h4 => by omega

/-- The non-multiples of `8` not `≡ 4 (mod 8)` are the odd readings and the readings `≡ 2 (mod 4)`. -/
theorem card_rest_eq (S : Finset ℕ) :
    (S.filter (fun d => ¬ 8 ∣ d ∧ d % 8 ≠ 4)).card
      = (S.filter (fun d => ¬ 2 ∣ d)).card + (S.filter (fun d => d % 4 = 2)).card := by
  classical
  have heq : S.filter (fun d => ¬ 8 ∣ d ∧ d % 8 ≠ 4) = S.filter (fun d => ¬ 2 ∣ d ∨ d % 4 = 2) :=
    Finset.filter_congr fun d _ => ⟨fun h => by omega, fun h => by omega⟩
  rw [heq, Finset.filter_or, Finset.card_union_of_disjoint]
  exact Finset.disjoint_filter.mpr fun d _ h2 h4 => by omega

/-- **The parity split of the non-multiples of `8`, on the counts of `S`.**
[PROVISIONAL: counting tool; supports: the count form of the parity split] -/
theorem paritySplit8_nonmult_iff (S : Finset ℕ) :
    ParitySplit8 (S.filter (fun d => ¬ 8 ∣ d)) ↔
      CountSplit8 (S.filter (fun d => ¬ 2 ∣ d)).card (S.filter (fun d => d % 4 = 2)).card
        (S.filter (fun d => d % 8 = 4)).card := by
  rw [paritySplit8_iff_counts _ (fun e he => (Finset.mem_filter.mp he).2),
    filter_filter_eq_of_imp S (fun d => ¬ 8 ∣ d) (fun d => ¬ 2 ∣ d) (fun d h => by omega),
    filter_filter_eq_of_imp S (fun d => ¬ 8 ∣ d) (fun d => d % 4 = 2) (fun d h => by omega),
    filter_filter_eq_of_imp S (fun d => ¬ 8 ∣ d) (fun d => d % 8 = 4) (fun d h => by omega)]

/-- **The parity split of the non-multiples of `8` not `≡ 4 (mod 8)`, on the counts of `S`.**
[PROVISIONAL: counting tool; supports: the count form of the parity split] -/
theorem paritySplit8_rest_iff (S : Finset ℕ) :
    ParitySplit8 (S.filter (fun d => ¬ 8 ∣ d ∧ d % 8 ≠ 4)) ↔
      CountSplit8 (S.filter (fun d => ¬ 2 ∣ d)).card (S.filter (fun d => d % 4 = 2)).card 0 := by
  rw [paritySplit8_iff_counts _ (fun e he => (Finset.mem_filter.mp he).2.1),
    filter_filter_eq_of_imp S (fun d => ¬ 8 ∣ d ∧ d % 8 ≠ 4) (fun d => ¬ 2 ∣ d) (fun d h => by omega),
    filter_filter_eq_of_imp S (fun d => ¬ 8 ∣ d ∧ d % 8 ≠ 4) (fun d => d % 4 = 2) (fun d h => by omega),
    card_filter_filter_eq_zero S (fun d => ¬ 8 ∣ d ∧ d % 8 ≠ 4) (fun d => d % 8 = 4) (fun d h => by omega)]

/-! ## The cases on counts -/

/-- **The settled counts.**  `m` multiples of `8`, `o` odd readings, `t` readings `≡ 2 (mod 4)`,
`f` readings `≡ 4 (mod 8)`: the disjunction of the count forms of T1, T2, T3, T4, T5, T7, T8. -/
def SettledCounts8 (m o t f : ℕ) : Prop :=
  (CountSplit8 o t f ∧ m ≤ 6) ∨
  (t = 0 ∧ o ≤ 3 ∧ m + f ≤ 6) ∨
  (m ≤ 3 ∧ f ≤ 1 ∧ o + t ≤ 3) ∨
  (o ≤ 3 ∧ m + f ≤ 3 ∧ t ≤ 1) ∨
  (CountSplit8 o t 0 ∧ m + f ≤ 3) ∨
  (o ≤ 3 ∧ m + f ≤ 2 ∧ t ≤ 2) ∨
  (CountSplit8 o t 0 ∧ m ≤ 2 ∧ f ≤ 2)

instance (m o t f : ℕ) : Decidable (SettledCounts8 m o t f) := by
  unfold SettledCounts8; infer_instance

/-- **The hypotheses of T6** (`lonely_eight_of_oott`) on `S`. -/
def OottCase8 (S : Finset ℕ) : Prop :=
  ∃ w₁ w₂ t₁ t₂ : ℕ, (∀ e ∈ S, ¬ 8 ∣ e → e % 8 ≠ 4 → e = w₁ ∨ e = w₂ ∨ e = t₁ ∨ e = t₂) ∧
    ¬ 2 ∣ w₁ ∧ ¬ 2 ∣ w₂ ∧ t₁ % 4 = 2 ∧ t₂ % 4 = 2 ∧ w₁ % 8 ≠ w₂ % 8 ∧ (w₁ + w₂) % 8 ≠ 0 ∧
    (S.filter (fun d => 8 ∣ d)).card + (S.filter (fun d => d % 8 = 4)).card ≤ 3

/-- **T6 on counts**: `p` readings `≡ ±1 (mod 8)`, `q` readings `≡ ±3 (mod 8)`, `t` readings
`≡ 2 (mod 4)`, `m` multiples of `8`, `f` readings `≡ 4 (mod 8)`. -/
def OottCounts8 (m p q t f : ℕ) : Prop := p ≤ 1 ∧ q ≤ 1 ∧ t ≤ 2 ∧ m + f ≤ 3

instance (m p q t f : ℕ) : Decidable (OottCounts8 m p q t f) := by
  unfold OottCounts8; infer_instance

/-- A set of at most one element satisfying `P` lies in `{y}` for some `y` satisfying `P`. -/
theorem exists_cover_one (T : Finset ℕ) (hT : T.card ≤ 1) (P : ℕ → Prop) (hP : ∀ x ∈ T, P x)
    (x₀ : ℕ) (hx₀ : P x₀) : ∃ y, P y ∧ ∀ x ∈ T, x = y := by
  rcases Finset.eq_empty_or_nonempty T with rfl | ⟨y, hy⟩
  · exact ⟨x₀, hx₀, fun x hx => absurd hx (Finset.notMem_empty x)⟩
  · exact ⟨y, hP y hy, fun x hx => Finset.card_le_one.mp hT x hx y hy⟩

/-- A set of at most two elements satisfying `P` lies in `{y₁, y₂}` for some `y₁, y₂` satisfying `P`. -/
theorem exists_cover_two (T : Finset ℕ) (hT : T.card ≤ 2) (P : ℕ → Prop) (hP : ∀ x ∈ T, P x)
    (x₀ : ℕ) (hx₀ : P x₀) : ∃ y₁ y₂, P y₁ ∧ P y₂ ∧ ∀ x ∈ T, x = y₁ ∨ x = y₂ := by
  classical
  rcases Finset.eq_empty_or_nonempty T with rfl | ⟨y, hy⟩
  · exact ⟨x₀, x₀, hx₀, hx₀, fun x hx => absurd hx (Finset.notMem_empty x)⟩
  · have hE : (T.erase y).card ≤ 1 := by rw [Finset.card_erase_of_mem hy]; omega
    obtain ⟨z, hz, hZ⟩ := exists_cover_one (T.erase y) hE P
      (fun x hx => hP x (Finset.mem_of_mem_erase hx)) y (hP y hy)
    refine ⟨y, z, hP y hy, hz, fun x hx => ?_⟩
    by_cases hxy : x = y
    · exact Or.inl hxy
    · exact Or.inr (hZ x (Finset.mem_erase.mpr ⟨hxy, hx⟩))

/-- **T6's hypotheses are a count condition.**  They hold exactly when at most one reading is
`≡ ±1 (mod 8)`, at most one is `≡ ±3 (mod 8)`, at most two are `≡ 2 (mod 4)`, and the multiples of `8`
and the readings `≡ 4 (mod 8)` number at most three. -/
theorem oottCase8_iff_counts (S : Finset ℕ) :
    OottCase8 S ↔ OottCounts8 (S.filter (fun d => 8 ∣ d)).card
      (S.filter (fun d => d % 8 = 1 ∨ d % 8 = 7)).card (S.filter (fun d => d % 8 = 3 ∨ d % 8 = 5)).card
      (S.filter (fun d => d % 4 = 2)).card (S.filter (fun d => d % 8 = 4)).card := by
  classical
  unfold OottCase8 OottCounts8
  constructor
  · rintro ⟨w₁, w₂, t₁, t₂, hR, hw₁, hw₂, ht₁, ht₂, hne, hneg, hmf⟩
    refine ⟨?_, ?_, ?_, hmf⟩
    · apply Finset.card_le_one.mpr
      intro a ha b hb
      obtain ⟨haS, ha'⟩ := Finset.mem_filter.mp ha
      obtain ⟨hbS, hb'⟩ := Finset.mem_filter.mp hb
      have h1 := hR a haS (by omega) (by omega)
      have h2 := hR b hbS (by omega) (by omega)
      omega
    · apply Finset.card_le_one.mpr
      intro a ha b hb
      obtain ⟨haS, ha'⟩ := Finset.mem_filter.mp ha
      obtain ⟨hbS, hb'⟩ := Finset.mem_filter.mp hb
      have h1 := hR a haS (by omega) (by omega)
      have h2 := hR b hbS (by omega) (by omega)
      omega
    · have hsub : S.filter (fun d => d % 4 = 2) ⊆ {t₁, t₂} := by
        intro x hx
        obtain ⟨hxS, hx'⟩ := Finset.mem_filter.mp hx
        have := hR x hxS (by omega) (by omega)
        simp only [Finset.mem_insert, Finset.mem_singleton]
        omega
      exact (Finset.card_le_card hsub).trans Finset.card_le_two
  · rintro ⟨hp, hq, ht, hmf⟩
    obtain ⟨w₁, hw₁, hW₁⟩ := exists_cover_one _ hp (fun x => x % 8 = 1 ∨ x % 8 = 7)
      (fun x hx => (Finset.mem_filter.mp hx).2) 1 (by norm_num)
    obtain ⟨w₂, hw₂, hW₂⟩ := exists_cover_one _ hq (fun x => x % 8 = 3 ∨ x % 8 = 5)
      (fun x hx => (Finset.mem_filter.mp hx).2) 3 (by norm_num)
    obtain ⟨t₁, t₂, ht₁, ht₂, hT⟩ := exists_cover_two _ ht (fun x => x % 4 = 2)
      (fun x hx => (Finset.mem_filter.mp hx).2) 2 (by norm_num)
    have hw₁' : w₁ % 8 = 1 ∨ w₁ % 8 = 7 := hw₁
    have hw₂' : w₂ % 8 = 3 ∨ w₂ % 8 = 5 := hw₂
    have ht₁' : t₁ % 4 = 2 := ht₁
    have ht₂' : t₂ % 4 = 2 := ht₂
    refine ⟨w₁, w₂, t₁, t₂, fun e he h8 h4 => ?_, by omega, by omega, ht₁', ht₂', by omega,
      by omega, hmf⟩
    have hcase : (e % 8 = 1 ∨ e % 8 = 7) ∨ (e % 8 = 3 ∨ e % 8 = 5) ∨ e % 4 = 2 := by omega
    rcases hcase with h | h | h
    · exact Or.inl (hW₁ e (Finset.mem_filter.mpr ⟨he, h⟩))
    · exact Or.inr (Or.inl (hW₂ e (Finset.mem_filter.mpr ⟨he, h⟩)))
    · exact Or.inr (Or.inr (hT e (Finset.mem_filter.mpr ⟨he, h⟩)))

end LRC.ParityDescent

namespace LRC.OrderEightN

open ConstructionN LRC.Descent LRC.ParityDescent

/-! ## The composed statement -/

/-- **The residue cases, composed.**  A set `S` of positive whole numbers is lonely at `1/8` when
`SettledCounts8` holds of its counts (`m` multiples of `8`, `o` odd readings, `t` readings
`≡ 2 (mod 4)`, `f` readings `≡ 4 (mod 8)`), or when T6's hypotheses `OottCase8 S` hold.  Each
disjunct is one case: T1 `lonely_eight_of_parity_descent`, T2 `lonely_eight_of_quarter_shift`,
T3 `lonely_eight_of_silent_four`, T4 `lonely_eight_of_quarter_three_one`,
T5 `lonely_eight_of_eighth_le_three`, T7 `lonely_eight_of_quarter_two_two`,
T8 `lonely_eight_of_eighth_two_two`, and T6 `lonely_eight_of_oott`.  Each takes the isolation at
the grid shifts `j/4` or `k/8`, displaced by an offset.

Tags inherited from the cases: the free shifts of T1–T5, T7 and T8 are counts
[PROVISIONAL: counting tool; supports: the free shift of each case], and T6's free shift is a
non-cover [PROVISIONAL: covering; supports: `free_shift_oott`].  The count form of the parity split
used for T1, T5 and T8 is [PROVISIONAL: counting tool; supports: the count form of the parity
split].  Lower-order inputs: see the file header. -/
theorem lonely_eight_of_settled_counts {S : Finset ℕ} (hpos : ∀ d ∈ S, 0 < d)
    (h : SettledCounts8 (S.filter (fun d => 8 ∣ d)).card (S.filter (fun d => ¬ 2 ∣ d)).card
        (S.filter (fun d => d % 4 = 2)).card (S.filter (fun d => d % 8 = 4)).card ∨ OottCase8 S) :
    ∃ t : ℝ, 0 < t ∧ ∀ d ∈ S, (8 : ℝ)⁻¹ ≤ circDist ((d : ℝ) * t) := by
  classical
  have h4c := card_four_dvd_eq S
  have hRc := card_rest_eq S
  rcases h with h | hO
  · unfold SettledCounts8 at h
    rcases h with ⟨hs, hm⟩ | ⟨ht, ho, hmf⟩ | ⟨hm, hf, hot⟩ | ⟨ho, hmf, ht⟩ | ⟨hs, hmf⟩ |
      ⟨ho, hmf, ht⟩ | ⟨hs, hm, hf⟩
    · exact lonely_eight_of_parity_descent hpos ((paritySplit8_nonmult_iff S).mpr hs) hm
    · refine lonely_eight_of_quarter_shift hpos (fun d hd h2 => ?_) ho (by omega)
      by_contra h4
      exact absurd (Finset.mem_filter.mpr ⟨hd, (by omega : d % 4 = 2)⟩)
        (by rw [Finset.card_eq_zero.mp ht]; exact Finset.notMem_empty _)
    · exact lonely_eight_of_silent_four hpos hm hf (by omega)
    · exact lonely_eight_of_quarter_three_one hpos ho (by omega) ht
    · exact lonely_eight_of_eighth_le_three hpos ((paritySplit8_rest_iff S).mpr hs) hmf
    · exact lonely_eight_of_quarter_two_two hpos ho (by omega) ht
    · exact lonely_eight_of_eighth_two_two hpos ((paritySplit8_rest_iff S).mpr hs) hm hf
  · obtain ⟨w₁, w₂, t₁, t₂, hR, hw₁, hw₂, ht₁, ht₂, hne, hneg, hmf⟩ := hO
    exact lonely_eight_of_oott hpos hR hw₁ hw₂ ht₁ ht₂ hne hneg hmf

/-- **The residual of the residue cases.**  A set of positive whole numbers is lonely at `1/8`, or
`SettledCounts8` fails on its counts and T6's hypotheses fail.  The complement of
`lonely_eight_of_settled_counts`; it carries the same tags. -/
theorem lonely_eight_or_open_counts {S : Finset ℕ} (hpos : ∀ d ∈ S, 0 < d) :
    (∃ t : ℝ, 0 < t ∧ ∀ d ∈ S, (8 : ℝ)⁻¹ ≤ circDist ((d : ℝ) * t)) ∨
      (¬ SettledCounts8 (S.filter (fun d => 8 ∣ d)).card (S.filter (fun d => ¬ 2 ∣ d)).card
          (S.filter (fun d => d % 4 = 2)).card (S.filter (fun d => d % 8 = 4)).card ∧
        ¬ OottCase8 S) := by
  classical
  by_cases h : SettledCounts8 (S.filter (fun d => 8 ∣ d)).card (S.filter (fun d => ¬ 2 ∣ d)).card
      (S.filter (fun d => d % 4 = 2)).card (S.filter (fun d => d % 8 = 4)).card ∨ OottCase8 S
  · exact Or.inl (lonely_eight_of_settled_counts hpos h)
  · exact Or.inr (not_or.mp h)

/-- **The residual in counts only.**  As `lonely_eight_or_open_counts`, with T6's hypotheses read
as the count condition `OottCounts8` (`oottCase8_iff_counts`). -/
theorem lonely_eight_or_open_counts_five {S : Finset ℕ} (hpos : ∀ d ∈ S, 0 < d) :
    (∃ t : ℝ, 0 < t ∧ ∀ d ∈ S, (8 : ℝ)⁻¹ ≤ circDist ((d : ℝ) * t)) ∨
      (¬ SettledCounts8 (S.filter (fun d => 8 ∣ d)).card (S.filter (fun d => ¬ 2 ∣ d)).card
          (S.filter (fun d => d % 4 = 2)).card (S.filter (fun d => d % 8 = 4)).card ∧
        ¬ OottCounts8 (S.filter (fun d => 8 ∣ d)).card
          (S.filter (fun d => d % 8 = 1 ∨ d % 8 = 7)).card
          (S.filter (fun d => d % 8 = 3 ∨ d % 8 = 5)).card
          (S.filter (fun d => d % 4 = 2)).card (S.filter (fun d => d % 8 = 4)).card) := by
  rcases lonely_eight_or_open_counts hpos with h | ⟨h1, h2⟩
  · exact Or.inl h
  · exact Or.inr ⟨h1, fun h => h2 ((oottCase8_iff_counts S).mpr h)⟩

/-! ## A consistency check on residue patterns

The multisets of `7 − m` residues in `[1, 7]` (the non-multiples of `8`, read mod `8`) with at least
two odd residues and `∑ max 2 (gcd r 8) ≥ 8`, for `m = 1, 2, 3, 4`.  For each `m`, the number of
such patterns and the number settled by `SettledCounts8` or `OottCounts8` on the pattern's counts.
This compares two encodings of the same case split, this file's predicate and
`experiments/nN/redo/lean_case_reach_v3.py`; it is not a cascade statement and not a measure of
progress. -/

/-- The multisets of residues: nondecreasing lists of length `n` with entries in `[lo, 7]`. -/
def residuePatterns : ℕ → ℕ → List (List ℕ)
  | 0, _ => [[]]
  | n + 1, lo => (List.range' lo (8 - lo)).flatMap fun r => (residuePatterns n r).map (r :: ·)

/-- The patterns at `m` multiples of `8`: `7 − m` residues in `[1, 7]`, at least two odd, and
`∑ max 2 (gcd r 8) ≥ 8`. -/
def crowdedPatterns (m : ℕ) : List (List ℕ) :=
  (residuePatterns (7 - m) 1).filter fun p =>
    decide (2 ≤ p.countP (fun r => decide (¬ 2 ∣ r))) &&
      decide (8 ≤ (p.map fun r => max 2 (Nat.gcd r 8)).sum)

/-- A pattern is settled when `SettledCounts8` or `OottCounts8` holds of its counts. -/
def PatternSettled8 (m : ℕ) (p : List ℕ) : Prop :=
  SettledCounts8 m (p.countP fun r => decide (¬ 2 ∣ r)) (p.countP fun r => decide (r % 4 = 2))
      (p.countP fun r => decide (r % 8 = 4)) ∨
    OottCounts8 m (p.countP fun r => decide (r % 8 = 1 ∨ r % 8 = 7))
      (p.countP fun r => decide (r % 8 = 3 ∨ r % 8 = 5)) (p.countP fun r => decide (r % 4 = 2))
      (p.countP fun r => decide (r % 8 = 4))

instance (m : ℕ) (p : List ℕ) : Decidable (PatternSettled8 m p) := by
  unfold PatternSettled8; infer_instance

/-- `m = 4`: 10 patterns, 10 settled. -/
theorem crowded_counts_m4 : (crowdedPatterns 4).length = 10 ∧
    ((crowdedPatterns 4).filter fun p => decide (PatternSettled8 4 p)).length = 10 := by
  decide +kernel

/-- `m = 3`: 155 patterns, 102 settled. -/
theorem crowded_counts_m3 : (crowdedPatterns 3).length = 155 ∧
    ((crowdedPatterns 3).filter fun p => decide (PatternSettled8 3 p)).length = 102 := by
  decide +kernel

/-- `m = 2`: 381 patterns, 162 settled. -/
theorem crowded_counts_m2 : (crowdedPatterns 2).length = 381 ∧
    ((crowdedPatterns 2).filter fun p => decide (PatternSettled8 2 p)).length = 162 := by
  decide +kernel

/-- `m = 1`: 812 patterns, 142 settled. -/
theorem crowded_counts_m1 : (crowdedPatterns 1).length = 812 ∧
    ((crowdedPatterns 1).filter fun p => decide (PatternSettled8 1 p)).length = 142 := by
  decide +kernel

end LRC.OrderEightN
