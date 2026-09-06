import LonelyRunner.LRC.SmallN.IntLRC_7_BS.Section7_Bridge
import LonelyRunner.LRC.SmallN.IntLRC_7_BS.Section5

/-!
# n = 7 (Barajas–Serra) — wiring §7 into the §4 reduction

`m1_six_witness` (`Section7_Bridge`) proves BS §7 for five level-0 units already
normalized to residues `{1,2,4}`. The §4 reduction hands over arbitrary positive
units, so this file supplies the normalization step, mirroring what `five_band`
does for `m ≥ 2`.

`band_neg` and `normalize7_band` in `Section5.lean` are stated at `N = 7^(m+1)`.
Their proofs use only `N = 7·P` with `P > 0`, so both generalize; the §7 case
needs the general form because it may return `P = 14`.
-/

namespace IntLRC7BS

open Finset

/-- **`band_neg` at an arbitrary modulus `7P`.** Negation preserves the band,
because `|x|_N = |-x|_N`. -/
theorem band_neg_gen (P : ℕ) (hP : 0 < P) (x : ℤ) :
    ((P : ℤ) ≤ x % (7 * (P : ℤ)) ∧ x % (7 * (P : ℤ)) ≤ 6 * (P : ℤ)) ↔
    ((P : ℤ) ≤ (-x) % (7 * (P : ℤ)) ∧ (-x) % (7 * (P : ℤ)) ≤ 6 * (P : ℤ)) := by
  have hPz : (0 : ℤ) < (P : ℤ) := by exact_mod_cast hP
  set N : ℤ := 7 * (P : ℤ) with hN_def
  have hN : 0 < N := by rw [hN_def]; linarith
  have hNne : N ≠ 0 := ne_of_gt hN
  set R := x % N; set R' := (-x) % N
  have hR0 : 0 ≤ R := Int.emod_nonneg x hNne
  have hRN : R < N := Int.emod_lt_of_pos x hN
  have hR'0 : 0 ≤ R' := Int.emod_nonneg (-x) hNne
  have hR'N : R' < N := Int.emod_lt_of_pos (-x) hN
  have hmod0 : (R + R') % N = 0 := by
    show (x % N + (-x) % N) % N = 0
    rw [← Int.add_emod, Int.add_right_neg, Int.zero_emod]
  obtain ⟨c, hc⟩ := Int.dvd_of_emod_eq_zero hmod0
  have hc0 : 0 ≤ c := by nlinarith
  have hc1 : c ≤ 1 := by nlinarith
  rcases eq_or_lt_of_le hc0 with hc_zero | hc_pos
  · have hR_z : R = 0 := by nlinarith
    have hR'_z : R' = 0 := by nlinarith
    simp only [hR_z, hR'_z]
  · have hc1' : c = 1 := by omega
    have hR'eq : R' = N - R := by subst hc1'; linarith
    rw [hR'eq, hN_def]; constructor
    · intro ⟨hlo, hhi⟩; exact ⟨by nlinarith, by nlinarith⟩
    · intro ⟨hlo, hhi⟩; exact ⟨by nlinarith, by nlinarith⟩

/-- **`normalize7_band` at an arbitrary modulus `7P`.** -/
theorem normalize7_band_gen (P : ℕ) (hP : 0 < P) (lam x : ℤ) :
    ((P : ℤ) ≤ (lam * normalize7 x) % (7 * (P : ℤ)) ∧
     (lam * normalize7 x) % (7 * (P : ℤ)) ≤ 6 * (P : ℤ)) →
    ((P : ℤ) ≤ (lam * x) % (7 * (P : ℤ)) ∧
     (lam * x) % (7 * (P : ℤ)) ≤ 6 * (P : ℤ)) := by
  unfold normalize7; split_ifs with h
  · exact id
  · rw [mul_neg]; exact (band_neg_gen P hP (lam * x)).mpr

/-- **BS §7, as the §4 reduction needs it.** Five positive units at level 0 and a
sixth element at level 1, with `gcd = 1`, admit a modulus `7P` and a multiplier
placing all six in the central band.

This is `m1_six_witness` composed with the `normalize7` step, which is exactly
what `five_band` does for `m ≥ 2`. `normalize7` only flips sign, so it preserves
divisibility (hence the `gcd` hypothesis transfers) and preserves the band in
both directions (`normalize7_band_gen`). -/
theorem five_band_m1 (d : Fin 5 → ℤ) (d6 : ℤ)
    (hpos : ∀ i, 0 < d i)
    (hnotdvd : ∀ i, ¬ (7 : ℤ) ∣ d i)
    (hinj : Function.Injective d)
    (h6 : (7 : ℤ) ∣ d6) (h6' : ¬ ((7 : ℤ) ^ 2 ∣ d6))
    (hgcd : ∀ p : ℕ, p.Prime → (∀ i, (p : ℤ) ∣ d i) → ¬ ((p : ℤ) ∣ d6)) :
    ∃ (P : ℕ) (lam : ℤ), 0 < P ∧
      (∀ i, (P : ℤ) ≤ (lam * d i) % (7 * (P : ℤ)) ∧
            (lam * d i) % (7 * (P : ℤ)) ≤ 6 * (P : ℤ)) ∧
      ((P : ℤ) ≤ (lam * d6) % (7 * (P : ℤ)) ∧
       (lam * d6) % (7 * (P : ℤ)) ≤ 6 * (P : ℤ)) := by
  classical
  set d' : Fin 5 → ℤ := fun i => normalize7 (d i) with hd'_def
  have hd'_ndvd : ∀ i, ¬ (7 : ℤ) ∣ d' i := fun i => normalize7_ndvd _ (hnotdvd i)
  have hd'_res : ∀ i, (d' i : ZMod 7) ∈ ({1, 2, 4} : Finset (ZMod 7)) :=
    fun i => normalize7_res _ (hnotdvd i)
  have hd'_inj : Function.Injective d' := normalize7_injOn_pos d hpos hinj
  -- `normalize7` only flips sign, so divisibility is unchanged in both directions.
  have hdvd_iff : ∀ (p : ℤ) (i : Fin 5), p ∣ d' i ↔ p ∣ d i := by
    intro p i
    show p ∣ normalize7 (d i) ↔ p ∣ d i
    unfold normalize7; split_ifs with h
    · exact Iff.rfl
    · exact dvd_neg
  have hgcd' : ∀ p : ℕ, p.Prime → (∀ i, (p : ℤ) ∣ d' i) → ¬ ((p : ℤ) ∣ d6) := by
    intro p hp hall
    exact hgcd p hp (fun i => (hdvd_iff (p : ℤ) i).mp (hall i))
  -- `normalize7` may flip a sign, so the normalized tuple need not be positive;
  -- `m1_six_witness` does not require positivity (everything is mod arithmetic).
  obtain ⟨P, lam, hP, hband5, hband6⟩ :=
    m1_six_witness d' d6 hd'_ndvd hd'_res h6 h6' hgcd'
  exact ⟨P, lam, hP, fun i => normalize7_band_gen P hP lam (d i) (hband5 i), hband6⟩

end IntLRC7BS
