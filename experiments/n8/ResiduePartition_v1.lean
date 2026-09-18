import LonelyRunner.LRC.ConstructionN.LemmaPass

/-! # The residue partition

`MANUSCRIPT` §2.3 leaves open *"how the fit decides which runners then need the cascade"*.
For commensurable speeds the answer is already proved and was never connected to that question:
`FRAME_FREE_RESTATEMENT_v1` §2A, and in Lean `ConstructionN.spine_all_or_nothing`.

Reduce by `g = gcd` of the differences, so the speeds are integers `w`.  At a spine instant
`t = p/n` with `p` a unit mod `n`, runner `j` sits at `(w j − w i)·p/n` relative to subject `i`,
and `spine_all_or_nothing` says that is clear exactly when `n ∤ (w j − w i)`.  Hence:

* **unique residue mod `n` → lonely at every one of the `φ(n)` grid instants**, no cascade needed;
* **shared residue → lonely at none of them**, so the subject must change scale.

Verified 32,000 of 32,000 in `experiments/n8/residue_partition_v1.py`.  Development file; nothing
here is new mathematics, it is `spine_all_or_nothing` read as a partition of the pack. -/

namespace ResiduePartition
open ConstructionN

variable {n : ℕ} {m : ℕ}

/-- **The partition.**  Subject `i` is clear of every other runner at the spine instant `p/n`
exactly when no other runner shares its residue mod `n`. -/
theorem lonely_at_spine_iff_residue_unique (hn : 0 < n) (w : Fin m → ℤ) (i : Fin m)
    {p : ℤ} (hcop : IsCoprime (n : ℤ) p) :
    (∀ j : Fin m, j ≠ i → (n : ℝ)⁻¹ ≤ circDist ((((w j - w i) * p : ℤ) : ℝ) / n))
      ↔ ∀ j : Fin m, j ≠ i → ¬ ((n : ℤ) ∣ (w j - w i)) := by
  constructor
  · intro h j hj; exact (spine_all_or_nothing hn hcop).mp (h j hj)
  · intro h j hj; exact (spine_all_or_nothing hn hcop).mpr (h j hj)

/-- **The verdict does not depend on which spine instant.**  The right-hand side above mentions no
`p`, so a subject is lonely at *all* `φ(n)` grid instants or at *none*: the residues partition the
pack once and for all. -/
theorem spine_verdict_independent (hn : 0 < n) (w : Fin m → ℤ) (i : Fin m)
    {p q : ℤ} (hp : IsCoprime (n : ℤ) p) (hq : IsCoprime (n : ℤ) q) :
    (∀ j : Fin m, j ≠ i → (n : ℝ)⁻¹ ≤ circDist ((((w j - w i) * p : ℤ) : ℝ) / n))
      ↔ (∀ j : Fin m, j ≠ i → (n : ℝ)⁻¹ ≤ circDist ((((w j - w i) * q : ℤ) : ℝ) / n)) := by
  rw [lonely_at_spine_iff_residue_unique hn w i hp,
      lonely_at_spine_iff_residue_unique hn w i hq]

/-- **The residue form**, for reading off an arrangement: `n ∤ (w j − w i)` is exactly
`w j % n ≠ w i % n`, so the partition is computed by taking residues. -/
theorem not_dvd_sub_iff_emod_ne (a b : ℤ) :
    ¬ ((n : ℤ) ∣ (a - b)) ↔ a % (n : ℤ) ≠ b % (n : ℤ) := by
  have h : ((n : ℤ) ∣ (a - b)) ↔ b % (n : ℤ) = a % (n : ℤ) := Int.modEq_iff_dvd.symm
  rw [h]
  constructor
  · intro hh he; exact hh he.symm
  · intro hh he; exact hh he.symm

end ResiduePartition
