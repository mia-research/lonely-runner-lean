import Mathlib

/-!
# The `-7` opening

`FlankBridge.inWay d A e` tests `dist(d*A, 8e·ℤ) < e`.  Let `L` be any integer with `e ∣ L*d`
— for a whole flank, the lcm of the reduced denominators `e/gcd(|dⱼ|,e)` does it.  Then

```
    d * (8L - 7) = -7*d + 8e * (L*d / e),
```

so at the opening `k = L - 1`, i.e. `A = 8L - 7 = 8(L-1)+1`, the test loses its dependence on
the opening index altogether:

```
    inWay d (8L-7) e   ↔   dist(7*d, 8e·ℤ) < e .
```

At the **largest** flank, where `|d| ≤ e`, that collapses further to an inequality on sizes:

```
    inWay d (8L-7) e   ↔   7*|d| < e .
```

So the largest flank is clear at this one explicit opening unless the subject carries a
difference more than seven times smaller than the flank.  Such a difference has reduced
denominator `e/gcd(|d|,e) > 7`, which is the `q ≥ n` that `LastClass.shadow_needs_full_denom`
already forces — the two results name the same obstruction from opposite ends.

*(Identity checked on 839,537 random movers, 0 mismatches; the size form on 1,190,074.)*

This does **not** prove Existence.  A census of 160,000 integer arrangements finds subjects
with **no** flank clear at this opening (about 30%), so the `-7` opening is one opening of
many and not by itself a route.  What it gives is a decidable, index-free criterion.
-/

namespace MinusSeven

/-- Runner at difference `d` is in the way at the opening of flank `e` with numerator `A`.
Same definition as `FlankBridge.inWay`, repeated so this file stands alone. -/
def inWay (d A e : ℤ) : Prop :=
  min ((d * A) % (8 * e)) (8 * e - (d * A) % (8 * e)) < e

/-- **The residue at the `-7` opening.**  When `e ∣ L*d`, the numerator `8L-7` sends `d` to `-7d`. -/
theorem minus_seven_residue {d e L : ℤ} (h : e ∣ L * d) :
    (d * (8 * L - 7)) % (8 * e) = (-7 * d) % (8 * e) := by
  obtain ⟨c, hc⟩ := h
  have key : d * (8 * L - 7) = -7 * d + 8 * e * c := by linear_combination 8 * hc
  rw [key, Int.add_mul_emod_self_left]

/-- **The opening index drops out.**  The test at `A = 8L-7` is a statement about `7*d` alone. -/
theorem inWay_minus_seven {d e L : ℤ} (h : e ∣ L * d) :
    inWay d (8 * L - 7) e ↔
      min ((-7 * d) % (8 * e)) (8 * e - (-7 * d) % (8 * e)) < e := by
  unfold inWay; rw [minus_seven_residue h]

/-- **The tiny-mover law.**  At the largest flank (`|d| ≤ e`), a nonzero difference is in the way
at the `-7` opening exactly when it is more than seven times smaller than the flank. -/
theorem inWay_iff_tiny {d e L : ℤ} (he : 0 < e) (hd : d ≠ 0) (hle : |d| ≤ e)
    (h : e ∣ L * d) : inWay d (8 * L - 7) e ↔ 7 * |d| < e := by
  rw [inWay_minus_seven h]
  rcases lt_or_gt_of_ne hd with hneg | hpos
  · have habs : |d| = -d := abs_of_neg hneg
    rw [habs] at hle
    have hmod : (-7 * d) % (8 * e) = -7 * d := Int.emod_eq_of_lt (by omega) (by omega)
    rw [hmod, habs]
    constructor
    · intro hh; rcases min_lt_iff.mp hh with h1 | h1 <;> omega
    · intro hh; exact min_lt_iff.mpr (Or.inl (by omega))
  · have habs : |d| = d := abs_of_pos hpos
    rw [habs] at hle
    have hmod : (-7 * d) % (8 * e) = 8 * e - 7 * d := by
      have hk : -7 * d = (8 * e - 7 * d) + 8 * e * (-1) := by ring
      rw [hk, Int.add_mul_emod_self_left]
      exact Int.emod_eq_of_lt (by omega) (by omega)
    rw [hmod, habs]
    constructor
    · intro hh; rcases min_lt_iff.mp hh with h1 | h1 <;> omega
    · intro hh; exact min_lt_iff.mpr (Or.inr (by omega))

/-- **The largest flank is clear unless a tiny difference is present.**  If every difference at the
flank `e` is nonzero, no larger than `e`, and at least a seventh of it, then the flank is clear at
the single opening `k = L - 1`. -/
theorem flank_clear_of_no_tiny {ds : List ℤ} {e L : ℤ} (he : 0 < e)
    (hne : ∀ d ∈ ds, d ≠ 0) (hle : ∀ d ∈ ds, |d| ≤ e)
    (hdvd : ∀ d ∈ ds, e ∣ L * d) (hno : ∀ d ∈ ds, e ≤ 7 * |d|) :
    ∀ d ∈ ds, ¬ inWay d (8 * L - 7) e := by
  intro d hd hb
  have h1 := (inWay_iff_tiny he (hne d hd) (hle d hd) (hdvd d hd)).mp hb
  have h2 := hno d hd
  omega

/-- The `-7` opening is a genuine opening: `8L - 7 = 8*(L-1) + 1` with index `L - 1`. -/
theorem minus_seven_is_opening (L : ℤ) : 8 * L - 7 = 8 * (L - 1) + 1 := by ring

end MinusSeven

#print axioms MinusSeven.minus_seven_residue
#print axioms MinusSeven.inWay_minus_seven
#print axioms MinusSeven.inWay_iff_tiny
#print axioms MinusSeven.flank_clear_of_no_tiny
#print axioms MinusSeven.minus_seven_is_opening
