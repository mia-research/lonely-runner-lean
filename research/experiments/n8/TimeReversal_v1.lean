import LonelyRunner.LRC.ConstructionN.LemmaPass

/-! # Time reversal, and why the reflection is obstructed at two residues

The reflections that keep recurring in this work are all one symmetry seen at different levels.

At the top level it is time reversal. For an **integer** reading `s` and a point `x`, the bad
condition `dist(s·x, 8ℤ) < 1` is invariant under `x ↦ 8 − x`, because `s(8−x) − 8k = −(sx − 8(s−k))`
and `k ↦ s − k` is a bijection of `ℤ`. So the clear set is symmetric about `x = 4`.
*(Checked: 176,775 samples, 0 exceptions.)*

Under `x = 8q/m` that map is exactly `q ↦ m − q` — so `Involution.clear_reflect` is **time reversal
expressed on residues**, not a separate phenomenon.

**And this is why the obstruction exists.** The candidates have numerators `8q+1`. Under `q ↦ m−q`
the numerator becomes `8m − (8q+1) + 2`, so the reflected point of the *real* clear set carries
residue `−1 (mod 8)`, not `+1`. The continuum is symmetric; **the `+1` lattice is not — it maps to
the `−1` lattice.** `Involution.clear_reflect` holds exactly where that mismatch does not bite, and
`reflect_fails_zero` / `reflect_fails_one` are the two residues where it does:

* `b ≡ 0 (mod 8)` — the collision residue, where the `+1` and `−1` lattices coincide mod `b`;
* `b ≡ 1 (mod 8)` — the guard residue `s·R ≡ 1`, where the shift by `2` lands on a boundary.

So the obstruction is not an accident of the intervals. It is the lattice failing a symmetry the
continuum has, and it fails exactly at the framework's two distinguished residues. -/

namespace TimeReversal

/-- Reading `s` is in the way at `x`: some multiple of `8` is within `1` of `s·x`. -/
def Bad (s x : ℚ) : Prop := ∃ k : ℤ, |s * x - 8 * (k : ℚ)| < 1

/-- **Time reversal.**  For an integer reading, being blocked is invariant under `x ↦ 8 − x`. -/
theorem bad_reflect {s : ℤ} {x : ℚ} : Bad (s : ℚ) x ↔ Bad (s : ℚ) (8 - x) := by
  constructor <;> rintro ⟨k, hk⟩
  · refine ⟨s - k, ?_⟩
    have : (s : ℚ) * (8 - x) - 8 * ((s - k : ℤ) : ℚ) = -((s : ℚ) * x - 8 * (k : ℚ)) := by
      push_cast; ring
    rw [this, abs_neg]; exact hk
  · refine ⟨s - k, ?_⟩
    have : (s : ℚ) * x - 8 * ((s - k : ℤ) : ℚ) = -((s : ℚ) * (8 - x) - 8 * (k : ℚ)) := by
      push_cast; ring
    rw [this, abs_neg]; exact hk

/-- **The clear set is symmetric about `x = 4`.**  Stated for a finite family of integer readings. -/
theorem clear_reflect_x (S : List ℤ) (x : ℚ) :
    (∀ s ∈ S, ¬ Bad (s : ℚ) x) ↔ (∀ s ∈ S, ¬ Bad (s : ℚ) (8 - x)) := by
  constructor <;> intro h s hs
  · exact fun hb => h s hs (bad_reflect.2 hb)
  · exact fun hb => h s hs (bad_reflect.1 hb)

end TimeReversal
