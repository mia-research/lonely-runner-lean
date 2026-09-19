import LonelyRunner.LRC.ConstructionN.LemmaPass

/-! # The reflection obstruction, at every order — proved

`Involution.clear_reflect` holds for `b mod 8 ∈ [2,7]`, and `reflect_fails_zero` / `reflect_fails_one`
exhibit the two failures. Computation said the same two residues govern **every** order `4 ≤ n ≤ 13`
(`degenerate_range_v1.py`), but that was `[VERIFIED]`, not proved.

It is proved here by the separation used for `SplitLaw`. At order `n` the clear interval is

```
    Iₙ(b) = [ ⌈(b−1)/n⌉ , ⌊((n−1)b−1)/n⌋ ]
```

and the reflection `r ↦ b − r` preserves it exactly when the endpoints sum to `b`. Writing
`b = n·j + r` with `0 ≤ r < n`, both endpoints separate — the lower as `j + ⌈(r−1)/n⌉`, the upper as
`(n−1)j + r − 1` — so the sum is `n·j + ⌈(r−1)/n⌉ + r − 1`, and it equals `b = n·j + r` precisely when
`⌈(r−1)/n⌉ = 1`, i.e. when `r ≥ 2`.

> **The two obstructing residues are `0` and `1` modulo `n`, at every order.** They are the collision
> residue and the guard residue, and nothing else can obstruct the reflection. -/

namespace GeneralReflect

/-- Lower edge of the clear interval at order `n`. -/
def L (n b : ℤ) : ℤ := (b - 1 + (n - 1)) / n
/-- Upper edge of the clear interval at order `n`. -/
def U (n b : ℤ) : ℤ := ((n - 1) * b - 1) / n

/-- **The lower edge separates.** -/
theorem L_split {n : ℤ} (hn : 0 < n) (j r : ℤ) : L n (n * j + r) = j + L n r := by
  unfold L
  have h : n * j + r - 1 + (n - 1) = (r - 1 + (n - 1)) + n * j := by ring
  rw [h, Int.add_mul_ediv_left _ _ hn.ne']
  omega

/-- **The upper edge separates.** -/
theorem U_split {n : ℤ} (hn : 0 < n) (j r : ℤ) :
    U n (n * j + r) = (n - 1) * j + U n r := by
  unfold U
  have h : (n - 1) * (n * j + r) - 1 = ((n - 1) * r - 1) + n * ((n - 1) * j) := by ring
  rw [h, Int.add_mul_ediv_left _ _ hn.ne']
  omega

/-- **The endpoint sum, separated.**  The `j` part contributes exactly `b`'s own `n·j`, so whether the
sum reaches `b` is decided by `r` alone. -/
theorem sum_split {n : ℤ} (hn : 0 < n) (j r : ℤ) :
    L n (n * j + r) + U n (n * j + r) = n * j + (L n r + U n r) := by
  rw [L_split hn, U_split hn]; ring

/-- **The obstruction is exactly `r ∈ {0,1}`.**  For `0 ≤ r < n` and `n ≥ 2`, the endpoints of `Iₙ`
sum to `b` if and only if `r ≥ 2`. -/
theorem obstruction_iff {n r : ℤ} (hn : 2 ≤ n) (h0 : 0 ≤ r) (hr : r < n) :
    L n r + U n r = r ↔ 2 ≤ r := by
  unfold L U
  -- the upper quotient is `r - 1` for every admissible `r`
  have hhi : ((n - 1) * r - 1) / n = r - 1 := by
    have hid : (n - 1) * r - 1 = (n - 1 - r) + n * (r - 1) := by ring
    rw [hid, Int.add_mul_ediv_left _ _ (by omega : n ≠ 0)]
    have : (n - 1 - r) / n = 0 := Int.ediv_eq_zero_of_lt (by omega) (by omega)
    omega
  -- the lower quotient is `1` exactly when `r ≥ 2`
  have hlo : (r - 1 + (n - 1)) / n = (r - 2) / n + 1 := by
    have hid : r - 1 + (n - 1) = (r - 2) + n * 1 := by ring
    rw [hid, Int.add_mul_ediv_left _ _ (by omega : n ≠ 0)]
  rw [hhi, hlo]
  constructor
  · intro h
    by_contra hlt
    push_neg at hlt
    have : (r - 2) / n = -1 := by
      have : r - 2 = (r - 2 + n) + n * (-1) := by ring
      rw [this, Int.add_mul_ediv_left _ _ (by omega : n ≠ 0)]
      have : (r - 2 + n) / n = 0 := Int.ediv_eq_zero_of_lt (by omega) (by omega)
      omega
    omega
  · intro h2
    have : (r - 2) / n = 0 := Int.ediv_eq_zero_of_lt (by omega) (by omega)
    omega


/-! ## The degenerate modulus, and the orders where the claim is false

`Degenerate2` proves `L 2 = U 2 = 1` at order 8, and computation reported `b = 2` as the **only**
modulus with `L = U`, at every order `4 ≤ n ≤ 13`.

**That range mattered.** Extending the computation downward: at `n = 3` both `b = 2` **and `b = 3`**
degenerate, and at `n = 2` every odd `b` does. The uniqueness claim is false at `n = 2, 3` and true
from `n = 4` on — which is what is proved here.

The mechanism is the same separation. For `2 ≤ b < n` the interval is `[1, b−1]`, so it collapses
exactly at `b = 2`. For `b ≥ n`, writing `b = n·j + r` with `j ≥ 1`, the width is
`(n−2)·j + (U(r) − L(r)) ≥ (n−2) − 1 = n − 3`, which is positive precisely when `n ≥ 4`. At `n = 3`
that bound is `0`, and `b = 3` is the case that attains it. -/

/-- The clear interval at `0 ≤ r < n` has lower edge `1` when `r ≥ 2` and `0` otherwise. -/
theorem L_small {n r : ℤ} (hn : 2 ≤ n) (h0 : 0 ≤ r) (hr : r < n) :
    L n r = if 2 ≤ r then 1 else 0 := by
  unfold L
  have hid : r - 1 + (n - 1) = (r - 2) + n * 1 := by ring
  rw [hid, Int.add_mul_ediv_left _ _ (by omega : n ≠ 0)]
  by_cases h : 2 ≤ r
  · have : (r - 2) / n = 0 := Int.ediv_eq_zero_of_lt (by omega) (by omega)
    simp [h, this]
  · push_neg at h
    have hz : (r - 2) / n = -1 := by
      have he : r - 2 = (r - 2 + n) + n * (-1) := by ring
      rw [he, Int.add_mul_ediv_left _ _ (by omega : n ≠ 0)]
      have : (r - 2 + n) / n = 0 := Int.ediv_eq_zero_of_lt (by omega) (by omega)
      omega
    simp [Int.not_le.2 h, hz]

/-- The clear interval at `0 ≤ r < n` has upper edge `r − 1`. -/
theorem U_small {n r : ℤ} (hn : 2 ≤ n) (h0 : 0 ≤ r) (hr : r < n) : U n r = r - 1 := by
  unfold U
  have hid : (n - 1) * r - 1 = (n - 1 - r) + n * (r - 1) := by ring
  rw [hid, Int.add_mul_ediv_left _ _ (by omega : n ≠ 0)]
  have : (n - 1 - r) / n = 0 := Int.ediv_eq_zero_of_lt (by omega) (by omega)
  omega

/-- **The interval is never degenerate above `b = 2`, once `n ≥ 4`.**  The width is at least `1` for
every `b ≥ 3`. False at `n = 3`, where `b = 3` attains width `0`. -/
theorem width_pos {n b : ℤ} (hn : 4 ≤ n) (hb : 3 ≤ b) : L n b + 1 ≤ U n b := by
  rcases lt_or_ge b n with h | h
  · rw [L_small (by omega) (by omega) h, U_small (by omega) (by omega) h]
    simp only [if_pos (show (2:ℤ) ≤ b by omega)]; omega
  · obtain ⟨j, r, hj, hr0, hrn, rfl⟩ :
        ∃ j r, 1 ≤ j ∧ 0 ≤ r ∧ r < n ∧ b = n * j + r :=
      ⟨b / n, b % n, by
        have := Int.ediv_le_ediv (by omega : (0:ℤ) < n) h
        have h1 : n / n = 1 := Int.ediv_self (by omega)
        omega, Int.emod_nonneg b (by omega), Int.emod_lt_of_pos b (by omega),
        by have := Int.mul_ediv_add_emod b n; omega⟩
    rw [L_split (by omega), U_split (by omega),
        L_small (by omega) hr0 hrn, U_small (by omega) hr0 hrn]
    by_cases h2 : 2 ≤ r <;> simp [h2] <;> nlinarith

end GeneralReflect
