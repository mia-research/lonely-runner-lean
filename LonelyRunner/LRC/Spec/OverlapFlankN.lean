import LonelyRunner.LRC.Spec.DivisibleFlankN

/-!
# The divisible flank, counted on the boundary: rigid blocks and the shared first opening

2026-09-24.  Let `n ∣ e`, `e = n·E`.  The openings `j = k·E`, `k < n`, are the boundary points
`t_k = k/n + 1/(n e)`, at which the flank sits at exactly `1/n`.  A disparity `d = q·e + r` not
divisible by `n` reads `e·((d·k + q) mod n) + r` there, so it blocks `t_k` exactly when
`d·k + q ≡ 0` or `d·k + (q + 1) ≡ 0 (mod n)`.

Record each such disparity by the two pairs `(d mod n, q mod n)` and `(d mod n, (q + 1) mod n)`
(`shiftPairs`).  Two effects make blocked points coincide, and both are counted by the pairs:

* **rigid blocks** — if `d' ≡ d (mod n)`, then at every `t_k` the reading of `d'` is that of `d`
  moved by the fixed amount `(d' − d)/(n e)`, so their blocked points are translates of each
  other; disparities of one residue class whose offsets overlap produce the *same* pair, and a
  `Finset` of pairs counts it once;
* **the shared first opening** — `t_0` is blocked by every disparity whose pair has offset `0`
  (every `d < e`, for instance), and it is counted once, not once per disparity.

A pair `(c, x)` blocks the points `k` with `c·k + x ≡ 0 (mod n)`: none unless `gcd(c, n) ∣ x`, and
at most `gcd(c, n)` otherwise (`card_congr_le`), one of them `k = 0` when `x = 0` (`pairWeight`).
If the first opening's `1` plus the pair weights come to less than `n`, some boundary point is
blocked by nothing, and the flank's certificate is exhibited there (`flankWorks_of_overlap`,
through `flankWorks_of_free_shift`).

Everything here is proved; no `sorry`, no `native_decide`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

namespace LRC.Resonance

open Flanks MomentIterationN LRC.SpecN LRC.FlankFinite

variable {n : ℕ} [Fact (2 ≤ n)]

/-- **Exhibition at a free boundary point.**  If the shift `k < n` is blocked by no disparity
not divisible by `n`, and every other multiple of `n` is clear at `j = 0`, then the flank `e`
hosts a lonely opening at `j = k·(e/n)`. -/
theorem flankWorks_of_free_shift (L : List ℕ) (e : ℕ) (he : 0 < e) (hen : n ∣ e)
    (hmult : ∀ d ∈ L, n ∣ d → e ≤ d % (n * e) ∧ d % (n * e) ≤ (n - 1) * e)
    (k : ℕ) (hkn : k < n)
    (hfree : ∀ d ∈ L, ¬ n ∣ d →
      (d * k + d / e) % n ≠ 0 ∧ (d * k + d / e) % n ≠ n - 1) :
    flankWorks n (e :: L) e = true := by
  have hn2 : 2 ≤ n := Fact.out
  obtain ⟨E, hE⟩ := hen
  set j : ℕ := k * E with hj
  have hkey : n * j + 1 = k * e + 1 := by rw [hj, hE]; ring
  have hjlt : j < e := by
    have hE0 : 0 < E := by
      rcases Nat.eq_zero_or_pos E with h | h
      · exfalso; rw [h, Nat.mul_zero] at hE; omega
      · exact h
    have : k * E < n * E := (Nat.mul_lt_mul_right hE0).mpr hkn
    rw [hj, hE]; omega
  unfold flankWorks
  rw [List.any_eq_true]
  refine ⟨j, List.mem_range.mpr hjlt, ?_⟩
  rw [List.all_eq_true]
  intro d hd
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  rw [hkey]
  rcases List.mem_cons.mp hd with rfl | hdL
  · have hflank : d * (k * d + 1) = d + (n * d) * (k * E) := by
      have hd : n * E = d := hE.symm
      calc d * (k * d + 1) = d + d * (k * d) := by ring
        _ = d + (n * E) * (k * d) := by rw [hd]
        _ = d + (n * d) * (k * E) := by rw [← hd]; ring
    have hlt1 : d < n * d := by
      have := (Nat.mul_lt_mul_right he).mpr (show 1 < n by omega)
      simpa using this
    rw [hflank, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt1]
    exact ⟨le_refl d, Nat.le_mul_of_pos_left d (by omega)⟩
  · by_cases hnd : n ∣ d
    · obtain ⟨m, hm⟩ := hnd
      have hsplit : d * (k * e + 1) = d + (n * e) * (m * k) := by rw [hm]; ring
      rw [hsplit, Nat.add_mul_mod_self_left]
      exact hmult d hdL ⟨m, hm⟩
    · set q : ℕ := d / e with hq
      set r : ℕ := d % e with hr
      have hdqr : e * q + r = d := Nat.div_add_mod d e
      have hr0 : r ≠ 0 := by
        intro h0
        apply hnd
        have : e ∣ d := Nat.dvd_of_mod_eq_zero h0
        exact (show n ∣ e from ⟨E, hE⟩).trans this
      have hrlt : r < e := Nat.mod_lt d he
      set c : ℕ := (d * k + q) % n with hc
      have hc0 : c ≠ 0 := (hfree d hdL hnd).1
      have hc1 : c ≠ n - 1 := (hfree d hdL hnd).2
      have hclt : c < n := Nat.mod_lt _ (by omega)
      have hsplit : d * (k * e + 1) = (e * c + r) + (n * e) * ((d * k + q) / n) := by
        have h := Nat.div_add_mod (d * k + q) n
        calc d * (k * e + 1) = e * (d * k) + d := by ring
          _ = e * (d * k) + (e * q + r) := by rw [hdqr]
          _ = e * (d * k + q) + r := by ring
          _ = e * (n * ((d * k + q) / n) + c) + r := by rw [hc, h]
          _ = (e * c + r) + (n * e) * ((d * k + q) / n) := by ring
      rw [hsplit, Nat.add_mul_mod_self_left]
      have hub : e * c + r < n * e := by nlinarith
      rw [Nat.mod_eq_of_lt hub]
      constructor
      · nlinarith [Nat.one_le_iff_ne_zero.mpr hc0]
      · have hcle : c ≤ n - 2 := by omega
        have h1 : e * c ≤ e * (n - 2) := Nat.mul_le_mul_left e hcle
        have hne : e * (n - 2) + e = (n - 1) * e := by
          have hstep : n - 1 = (n - 2) + 1 := by omega
          rw [hstep, Nat.succ_mul, mul_comm]
        omega

/-- The pairs `(d mod n, q mod n)` and `(d mod n, (q + 1) mod n)`, `q = ⌊d/e⌋`, of the
disparities not divisible by `n`.  Disparities of one rigid block with overlapping offsets give
the same pair. -/
def shiftPairs (n e : ℕ) (L : List ℕ) : Finset (ℕ × ℕ) :=
  ((L.toFinset.filter (fun d => ¬ n ∣ d)).image (fun d => (d % n, (d / e) % n))) ∪
  ((L.toFinset.filter (fun d => ¬ n ∣ d)).image (fun d => (d % n, (d / e + 1) % n)))

/-- The number of boundary points other than the first that a pair `(c, x)` can block:
`gcd(c, n)` when `gcd(c, n) ∣ x`, less one when `x = 0` (the first opening, counted apart), and
`0` otherwise. -/
def pairWeight (n : ℕ) (p : ℕ × ℕ) : ℕ :=
  if Nat.gcd p.1 n ∣ p.2 then Nat.gcd p.1 n - (if p.2 = 0 then 1 else 0) else 0

open Classical in
/-- The overlap count: the first opening once, if any pair can block it, plus the pair weights. -/
noncomputable def overlapCost (n e : ℕ) (L : List ℕ) : ℕ :=
  (if ∃ p ∈ shiftPairs n e L, p.2 = 0 then 1 else 0) + ∑ p ∈ shiftPairs n e L, pairWeight n p

/-- Every pair's offset is a residue mod `n`. -/
theorem shiftPairs_snd_lt {e : ℕ} {L : List ℕ} {p : ℕ × ℕ} (hp : p ∈ shiftPairs n e L) :
    p.2 < n := by
  have hn2 : 2 ≤ n := Fact.out
  unfold shiftPairs at hp
  rcases Finset.mem_union.mp hp with h | h <;>
  · obtain ⟨d, -, rfl⟩ := Finset.mem_image.mp h
    exact Nat.mod_lt _ (by omega)

/-- The points other than the first that one pair blocks number at most its weight. -/
theorem card_pair_erase_le (p : ℕ × ℕ) :
    (((Finset.range n).filter (fun k => (p.1 * k + p.2) % n = 0)).erase 0).card
      ≤ pairWeight n p := by
  classical
  have hn2 : 2 ≤ n := Fact.out
  set S := (Finset.range n).filter (fun k => (p.1 * k + p.2) % n = 0) with hS
  have hcS : S.card ≤ Nat.gcd p.1 n := card_congr_le p.1 p.2 0
  unfold pairWeight
  by_cases hg : Nat.gcd p.1 n ∣ p.2
  · rw [if_pos hg]
    by_cases hx : p.2 = 0
    · rw [if_pos hx]
      have h0 : (0 : ℕ) ∈ S := by
        rw [hS, Finset.mem_filter, Finset.mem_range]
        exact ⟨by omega, by rw [hx]; simp⟩
      rw [Finset.card_erase_of_mem h0]
      omega
    · rw [if_neg hx, Nat.sub_zero]
      exact le_trans (Finset.card_erase_le) hcS
  · rw [if_neg hg]
    have hempty : S = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro k hk
      apply hg
      have hdvd : n ∣ p.1 * k + p.2 := Nat.dvd_of_mod_eq_zero (Finset.mem_filter.mp hk).2
      have h1 : Nat.gcd p.1 n ∣ p.1 * k + p.2 := (Nat.gcd_dvd_right p.1 n).trans hdvd
      exact (Nat.dvd_add_right (Dvd.dvd.mul_right (Nat.gcd_dvd_left p.1 n) k)).mp h1
    rw [hempty]
    simp

/-- **The overlap rule.**  Let `n ∣ e`, and let every other multiple of `n` be clear at `j = 0`.
If the overlap count — the first opening once, plus the pair weights — is below `n`, the flank
`e` hosts a lonely opening, exhibited at a boundary point that nothing blocks. -/
theorem flankWorks_of_overlap (L : List ℕ) (e : ℕ) (he : 0 < e) (hen : n ∣ e)
    (hmult : ∀ d ∈ L, n ∣ d → e ≤ d % (n * e) ∧ d % (n * e) ≤ (n - 1) * e)
    (hcost : overlapCost n e L < n) :
    flankWorks n (e :: L) e = true := by
  classical
  have hn2 : 2 ≤ n := Fact.out
  set P := shiftPairs n e L with hP
  set S : ℕ × ℕ → Finset ℕ := fun p => (Finset.range n).filter (fun k => (p.1 * k + p.2) % n = 0)
    with hSdef
  set H := (Finset.range n).filter (fun k => ∃ p ∈ P, (p.1 * k + p.2) % n = 0) with hH
  -- the blocked points, counted
  have hsub : H.erase 0 ⊆ P.biUnion (fun p => (S p).erase 0) := by
    intro k hk
    obtain ⟨hk0, hkH⟩ := Finset.mem_erase.mp hk
    obtain ⟨hkr, p, hp, hpk⟩ := Finset.mem_filter.mp hkH
    exact Finset.mem_biUnion.mpr ⟨p, hp, Finset.mem_erase.mpr ⟨hk0, Finset.mem_filter.mpr ⟨hkr, hpk⟩⟩⟩
  have herase : (H.erase 0).card ≤ ∑ p ∈ P, pairWeight n p :=
    calc (H.erase 0).card ≤ (P.biUnion (fun p => (S p).erase 0)).card := Finset.card_le_card hsub
      _ ≤ ∑ p ∈ P, ((S p).erase 0).card := Finset.card_biUnion_le
      _ ≤ ∑ p ∈ P, pairWeight n p := Finset.sum_le_sum fun p _ => card_pair_erase_le p
  have hzero : (0 : ℕ) ∈ H → ∃ p ∈ P, p.2 = 0 := by
    intro h0
    obtain ⟨-, p, hp, hpk⟩ := Finset.mem_filter.mp h0
    refine ⟨p, hp, ?_⟩
    have hlt := shiftPairs_snd_lt hp
    simpa [Nat.mod_eq_of_lt hlt] using hpk
  have hcardH : H.card < (Finset.range n).card := by
    rw [Finset.card_range]
    have hc := hcost
    unfold overlapCost at hc
    rw [← hP] at hc
    by_cases h0 : (0 : ℕ) ∈ H
    · have := Finset.card_erase_add_one h0
      rw [if_pos (hzero h0)] at hc
      omega
    · rw [Finset.erase_eq_of_notMem h0] at herase
      split_ifs at hc <;> omega
  obtain ⟨k, hk, hkH⟩ := Finset.exists_mem_notMem_of_card_lt_card hcardH
  have hkn : k < n := Finset.mem_range.mp hk
  -- a point that no pair blocks is blocked by no disparity
  have hmodeq : ∀ d x : ℕ, ((d % n) * k + x % n) % n = (d * k + x) % n := by
    intro d x
    rw [Nat.add_mod, Nat.mod_mod, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, ← Nat.add_mod]
  refine flankWorks_of_free_shift L e he hen hmult k hkn fun d hdL hnd => ⟨?_, ?_⟩
  · intro h
    apply hkH
    refine Finset.mem_filter.mpr ⟨hk, (d % n, (d / e) % n), ?_, ?_⟩
    · rw [hP]; unfold shiftPairs
      exact Finset.mem_union_left _ (Finset.mem_image.mpr
        ⟨d, Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hdL, hnd⟩, rfl⟩)
    · simpa [hmodeq] using h
  · intro h
    apply hkH
    refine Finset.mem_filter.mpr ⟨hk, (d % n, (d / e + 1) % n), ?_, ?_⟩
    · rw [hP]; unfold shiftPairs
      exact Finset.mem_union_right _ (Finset.mem_image.mpr
        ⟨d, Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hdL, hnd⟩, rfl⟩)
    · have h1 : (d * k + (d / e + 1)) % n = 0 := by
        rw [← add_assoc, Nat.add_mod, h, Nat.mod_eq_of_lt (show 1 < n by omega),
          Nat.sub_add_cancel (by omega), Nat.mod_self]
      simpa [hmodeq] using h1

end LRC.Resonance
