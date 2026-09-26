import LonelyRunner.LRC.Spec.Order8SkeletonN

/-!
# The off-lattice rule: one reading off the lattice of the others, at every order

2026-09-26.  Found in session and checked on the owner's instruction not to dismiss it.  A subject's readings are split
into one reading `x` and the rest `D`, with `h` dividing every element of `D` and not `x`.

* **General order** (`lonely_of_off_lattice`, every `n ≥ 4`).  If `D` is lonely at threshold `1/n` at some `τ > 0`, then
  so are `D` and `x` together at a named instant `τ + k/h`: every `t = τ + k/h` leaves each `d ∈ D` exactly where it was
  (`d/h` whole laps per step), and `x` advances by `frac(x/h) ∈ (0, 1)` of a lap per step, so some `k` puts `x` clear
  (`Flanks.exists_clear_step`, no density, no count).
* **At order eight** (`lonely_eight_of_off_lattice`).  With `D` of at most six elements, native order seven supplies the
  instant (`lonely_seven_nat`, at `1/7 ≥ 1/8`).  So a set of at most seven positive whole-number readings is lonely at
  `1/8` as soon as one reading does not share the gcd of the others.

It does not trivialise the conjecture: the sets it leaves are those in which every reading is a multiple of the gcd of
the rest -- for a reduced set, every six of the seven are coprime.  Checked before formalising: 164 of 164 applicable
random reduced sets lonely at the constructed instant; it closes 3 of the 7 residual sets of `MANUSCRIPT_v21` §17D
(`experiments/nN/redo/off_lattice_v1.out`).  The general-order form is the step `LRC(n−1) ⇒ LRC(n)` on every set with an
off-lattice reading.

Everything here is proved; no `sorry`, no `native_decide`.
-/

namespace LRC.OffLattice

open LRC.Order8Skeleton

/-- **The off-lattice rule, at every order `n ≥ 4`.** -/
theorem lonely_of_off_lattice {n : ℕ} (hn : 4 ≤ n) {D : Finset ℕ} {x h : ℕ} (hh : 0 < h)
    (hD : ∀ d ∈ D, h ∣ d) (hx : ¬ h ∣ x) {τ : ℝ} (hτ : 0 < τ)
    (hlon : ∀ d ∈ D, (n : ℝ)⁻¹ ≤ circDist ((d : ℝ) * τ)) :
    ∃ t : ℝ, 0 < t ∧ (∀ d ∈ D, (n : ℝ)⁻¹ ≤ circDist ((d : ℝ) * t)) ∧ (n : ℝ)⁻¹ ≤ circDist ((x : ℝ) * t) := by
  haveI : Fact (2 ≤ n) := ⟨by omega⟩
  have hhR : (0 : ℝ) < h := by exact_mod_cast hh
  set f := Int.fract ((x : ℝ) / h) with hf
  have hf0 : 0 < f := by
    rcases (Int.fract_nonneg ((x : ℝ) / h)).lt_or_eq with hlt | heq
    · exact hlt
    · exfalso
      have hint : (x : ℝ) / h = (⌊(x : ℝ) / h⌋ : ℝ) := by
        have := Int.floor_add_fract ((x : ℝ) / h); rw [← heq] at this; linarith
      apply hx
      have hxh : (x : ℝ) = h * (⌊(x : ℝ) / h⌋ : ℝ) := by rw [← hint]; field_simp
      have hfl0 : 0 ≤ ⌊(x : ℝ) / h⌋ := Int.floor_nonneg.mpr (by positivity)
      refine ⟨(⌊(x : ℝ) / h⌋).toNat, ?_⟩
      have : ((⌊(x : ℝ) / h⌋.toNat : ℕ) : ℝ) = (⌊(x : ℝ) / h⌋ : ℝ) := by
        rw [show ((⌊(x : ℝ) / h⌋.toNat : ℕ) : ℝ) = ((⌊(x : ℝ) / h⌋.toNat : ℤ) : ℝ) by norm_cast,
          Int.toNat_of_nonneg hfl0]
      exact_mod_cast (show (x : ℝ) = (h : ℝ) * ((⌊(x : ℝ) / h⌋.toNat : ℕ) : ℝ) by rw [this]; exact hxh)
  have hf1 : f < 1 := Int.fract_lt_one _
  obtain ⟨k, hk⟩ := Flanks.exists_clear_step (n := n) hn hf0 hf1 (c := (x : ℝ) * τ)
  refine ⟨τ + k / h, by positivity, ?_, ?_⟩
  · intro d hd
    obtain ⟨m, rfl⟩ := hD d hd
    have e : ((h * m : ℕ) : ℝ) * (τ + k / h) = ((h * m : ℕ) : ℝ) * τ + ((k * m : ℕ) : ℤ) := by
      push_cast; field_simp
    rw [e, ConstructionN.circDist_add_int]; exact hlon _ hd
  · set q := ⌊(x : ℝ) / h⌋ with hq
    have hsplit : (x : ℝ) / h = (q : ℝ) + f := (Int.floor_add_fract _).symm
    have e : (x : ℝ) * (τ + k / h) = ((k : ℝ) * f + (x : ℝ) * τ) + ((k : ℤ) * q : ℤ) := by
      have h1 : (x : ℝ) * (τ + k / h) = (x : ℝ) * τ + (k : ℝ) * ((x : ℝ) / h) := by field_simp
      rw [h1, hsplit]; push_cast; ring
    rw [e, ConstructionN.circDist_add_int]; exact hk

/-- **At order eight.**  A set of at most seven positive whole-number readings is lonely at `1/8` if some reading `x` is
not divisible by the gcd of the others. -/
theorem lonely_eight_of_off_lattice {S : Finset ℕ} (hpos : ∀ d ∈ S, 0 < d) (hcard : S.card ≤ 7) {x : ℕ}
    (hxS : x ∈ S) (hne : (S.erase x).Nonempty) (hoff : ¬ (S.erase x).gcd id ∣ x) : Lonely8 S := by
  classical
  set D := S.erase x with hDdef
  have hDpos : ∀ d ∈ D, 0 < d := fun d hd => hpos d (Finset.mem_of_mem_erase hd)
  have hDcard : D.card ≤ 6 := by rw [Finset.card_erase_of_mem hxS]; omega
  have hh : 0 < D.gcd id := by
    obtain ⟨d0, hd0⟩ := hne
    exact Nat.pos_of_ne_zero fun h0 => by
      have := (Finset.gcd_eq_zero_iff.mp h0) d0 hd0; simp at this; exact absurd this (hDpos d0 hd0).ne'
  obtain ⟨τ, hτ, hl⟩ := LRC.OrderSevenN.lonely_seven_nat D hDpos hDcard
  obtain ⟨t, ht, hDt, hxt⟩ := lonely_of_off_lattice (n := 8) (by norm_num) hh
    (fun d hd => Finset.gcd_dvd hd) hoff hτ (fun d hd => le_trans (by norm_num) (hl d hd))
  refine ⟨t, ht, fun d hd => ?_⟩
  by_cases hdx : d = x
  · rw [hdx]; simpa using hxt
  · simpa using hDt d (Finset.mem_erase.mpr ⟨hdx, hd⟩)

end LRC.OffLattice
