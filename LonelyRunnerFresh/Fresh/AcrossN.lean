import Mathlib
import Fresh.Framework

/-!
# The n = 8 boundary arithmetic at a general number of runners `n` (Task AP)

Written 2026-10-09.  Imports Mathlib and `Fresh.Framework` only.  Nothing is imported from the existing `LonelyRunner`
repo.  Data: `experiments/n8/across_n_v1.py` and `.out` (exact integer arithmetic, populations at n = 5, 6, 7, 8, 9, 10).

Scope.  `n` runners: `n - 1` disparities; a runner of disparity `d` is clear at `t` iff `1/n ≤ distInt (d t)`.  This is
DATA IN OUR OWN FRAMEWORK at other `n` (the cascade with gap `1/n`).  It does not use any published proof of the lonely
runner conjecture for any `n`, and nothing here is a step in the n = 8 proof; it states which of the n = 8 identities of
`Boundaries.lean` (E440) are statements about every `n` and which are statements about `n ∣ 24`.

Provenance (existing declarations whose idea is re-derived here, each proof written afresh; I did not copy a proof I did
not understand):
* `unit_lonely_general`, `lonely_iff_not_dvd`        <-> `Boundaries.unit_lonely` (this folder; n = 8) / `Grid` unit law;
* `opener_cofactor`, `entry_cofactor`               <-> `Boundaries.opener_unit`, `Boundaries.entry_unit`;
* `touch_cofactors`, `touch_sum_dvd`                <-> `Boundaries.touch_units`;
* `width_congruence_general`                        <-> `Boundaries.width_congruence`;
* `units_separated`                                 <-> `Boundaries.four_cells` (the separation half);
* `gate_blocks`                                     <-> `Gate` (the (7,9) window), at `(n-1, n+1)`;
* `conj_integer`                                    <-> `TouchTheory.wholeset_conjugate` restricted to integer disparities.

Counting tool: none is used.  No density, coverage, cap or move budget appears in any statement.
-/

open Classical

namespace Fresh

namespace AcrossN

/-! ## Helpers on `distInt` -/

theorem distInt_intCast' (z : ℤ) : distInt (z : ℝ) = 0 := by
  unfold distInt
  simp [round_intCast]

#print axioms distInt_intCast'

theorem distInt_add_int' (x : ℝ) (z : ℤ) : distInt (x + z) = distInt x := by
  unfold distInt
  rw [round_add_intCast]
  push_cast
  congr 1
  ring

#print axioms distInt_add_int'

theorem distInt_neg' (x : ℝ) : distInt (-x) = distInt x := by
  have key : ∀ y : ℝ, distInt (-y) ≤ distInt y := by
    intro y
    unfold distInt
    have h : |(-y) - (round (-y) : ℝ)| ≤ |(-y) - ((-(round y) : ℤ) : ℝ)| := by
      have := round_le (-y) (-(round y))
      simpa [distInt] using this
    have e : |(-y) - ((-(round y) : ℤ) : ℝ)| = |y - (round y : ℝ)| := by
      push_cast
      rw [show -y - -(round y : ℝ) = -(y - round y) by ring, abs_neg]
    exact e ▸ h
  exact le_antisymm (key x) (by simpa using key (-x))

#print axioms distInt_neg'

theorem distInt_int_sub' (m : ℤ) (x : ℝ) : distInt ((m : ℝ) - x) = distInt x := by
  have : (m : ℝ) - x = -x + m := by ring
  rw [this, distInt_add_int', distInt_neg']

#print axioms distInt_int_sub'

theorem distInt_le_abs (x : ℝ) (z : ℤ) : distInt x ≤ |x - z| := round_le x z

/-! ## (1) Units: the instants `a/n` -/

/-- A whole number `r` of `n`-ths that is not a whole number of laps is at distance at least `1/n` from a lap. -/
theorem distInt_div_ge (n : ℕ) (hn : 0 < n) (r : ℤ) (h : ¬ (n : ℤ) ∣ r) :
    (1 / n : ℝ) ≤ distInt ((r : ℝ) / n) := by
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  unfold distInt
  set m : ℤ := round ((r : ℝ) / n) with hm
  have hne : r - m * n ≠ 0 := by
    intro h0
    apply h
    exact ⟨m, by linarith⟩
  have h1 : (1 : ℝ) ≤ |((r - m * n : ℤ) : ℝ)| := by
    have := Int.one_le_abs hne
    exact_mod_cast this
  have e : |(r : ℝ) / n - (m : ℝ)| = |((r - m * n : ℤ) : ℝ)| / n := by
    rw [show (r : ℝ) / n - (m : ℝ) = ((r - m * n : ℤ) : ℝ) / n by push_cast; field_simp, abs_div, abs_of_pos hnr]
  rw [e, div_eq_mul_inv, div_eq_mul_inv]
  have : (0 : ℝ) < (n : ℝ)⁻¹ := inv_pos.mpr hnr
  nlinarith

#print axioms distInt_div_ge

/-- A whole number of laps is at distance 0. -/
theorem distInt_div_eq_zero (n : ℕ) (hn : 0 < n) (r : ℤ) (h : (n : ℤ) ∣ r) :
    distInt ((r : ℝ) / n) = 0 := by
  obtain ⟨c, hc⟩ := h
  have hnr : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have : (r : ℝ) / n = (c : ℝ) := by
    rw [hc]; push_cast; field_simp
  rw [this]; exact distInt_intCast' c

#print axioms distInt_div_eq_zero

/-- **The lonely test at `a/n`, for every `n`, `d`, `a`** (clear iff `n ∤ d a`). -/
theorem lonely_iff_not_dvd (n : ℕ) (hn : 0 < n) (d a : ℤ) :
    (1 / n : ℝ) ≤ distInt ((d : ℝ) * ((a : ℝ) / n)) ↔ ¬ (n : ℤ) ∣ d * a := by
  have e : (d : ℝ) * ((a : ℝ) / n) = ((d * a : ℤ) : ℝ) / n := by push_cast; ring
  rw [e]
  constructor
  · intro h hd
    have := distInt_div_eq_zero n hn (d * a) hd
    have hpos : (0 : ℝ) < 1 / n := by positivity
    linarith
  · exact distInt_div_ge n hn (d * a)

#print axioms lonely_iff_not_dvd

/-- **unit_lonely, every `n`**: if `n ∤ d` and `a` is a unit mod `n`, the instant `a/n` is clear for `d`. -/
theorem unit_lonely_general (n : ℕ) (hn : 0 < n) (d a : ℤ) (hd : ¬ (n : ℤ) ∣ d) (ha : IsCoprime a (n : ℤ)) :
    (1 / n : ℝ) ≤ distInt ((d : ℝ) * ((a : ℝ) / n)) := by
  rw [lonely_iff_not_dvd n hn]
  intro h
  exact hd (ha.symm.dvd_of_dvd_mul_right h)

#print axioms unit_lonely_general

/-- A multiple of `n` blocks every instant `a/n`. -/
theorem multiple_blocks (n : ℕ) (hn : 0 < n) (d a : ℤ) (hd : (n : ℤ) ∣ d) :
    distInt ((d : ℝ) * ((a : ℝ) / n)) = 0 := by
  have e : (d : ℝ) * ((a : ℝ) / n) = ((d * a : ℤ) : ℝ) / n := by push_cast; ring
  rw [e]
  exact distInt_div_eq_zero n hn _ (dvd_mul_of_dvd_left hd a)

#print axioms multiple_blocks

/-! ## (1) Cofactor arithmetic at a boundary instant, general `n`

At `t = p/q` (reduced) a runner `x` standing exactly `1/n` past lap `k` has `n x = q c`, `c p = n k + 1`:
the cofactor `c` is the INVERSE of `p` mod `n`, not `p`.  The n = 8 statement `c ≡ p` is the special case in which every unit
is its own inverse (`n ∣ 24`). -/

theorem opener_cofactor (n : ℕ) (hn : 0 < n) (p q x k : ℤ) (hq : q ≠ 0) (hpq : IsCoprime p q)
    (h : (x : ℝ) * ((p : ℝ) / q) = (k : ℝ) + 1 / n) :
    ∃ c : ℤ, (n : ℤ) * x = q * c ∧ c * p = n * k + 1 ∧ IsCoprime c (n : ℤ) ∧ IsCoprime p (n : ℤ) ∧
      (n : ℤ) ∣ q ∧ (n : ℤ) ∣ (c * p - 1) := by
  have hqr : (q : ℝ) ≠ 0 := by exact_mod_cast hq
  have hnr : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hz : (n : ℤ) * x * p = q * (n * k + 1) := by
    have : ((n : ℤ) * x * p : ℝ) = q * (n * k + 1) := by
      field_simp at h; push_cast; linarith
    exact_mod_cast this
  have hdvd : q ∣ (n : ℤ) * x := by
    have : q ∣ ((n : ℤ) * x) * p := ⟨n * k + 1, hz⟩
    exact hpq.symm.dvd_of_dvd_mul_right this
  obtain ⟨c, hc⟩ := hdvd
  have hcp : c * p = n * k + 1 := by
    have : q * (c * p) = q * (n * k + 1) := by rw [← hz, hc]; ring
    exact mul_left_cancel₀ hq this
  have hcop : IsCoprime (c * p) (n : ℤ) := ⟨1, -k, by rw [hcp]; ring⟩
  have h1 : IsCoprime c (n : ℤ) := hcop.of_mul_left_left
  have h2 : IsCoprime p (n : ℤ) := hcop.of_mul_left_right
  have h8q : (n : ℤ) ∣ q := by
    have : (n : ℤ) ∣ q * c := ⟨x, by rw [← hc]⟩
    exact h1.symm.dvd_of_dvd_mul_right this
  exact ⟨c, hc, hcp, h1, h2, h8q, ⟨k, by rw [hcp]; ring⟩⟩

#print axioms opener_cofactor

theorem entry_cofactor (n : ℕ) (hn : 0 < n) (p q x k : ℤ) (hq : q ≠ 0) (hpq : IsCoprime p q)
    (h : (x : ℝ) * ((p : ℝ) / q) = (k : ℝ) + ((n : ℝ) - 1) / n) :
    ∃ c : ℤ, (n : ℤ) * x = q * c ∧ c * p = n * k + (n - 1) ∧ IsCoprime c (n : ℤ) ∧ IsCoprime p (n : ℤ) ∧
      (n : ℤ) ∣ q ∧ (n : ℤ) ∣ (c * p + 1) := by
  have hqr : (q : ℝ) ≠ 0 := by exact_mod_cast hq
  have hnr : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hz : (n : ℤ) * x * p = q * (n * k + (n - 1)) := by
    have : ((n : ℤ) * x * p : ℝ) = q * (n * k + (n - 1)) := by
      field_simp at h; push_cast; linarith
    exact_mod_cast this
  have hdvd : q ∣ (n : ℤ) * x := by
    have : q ∣ ((n : ℤ) * x) * p := ⟨n * k + (n - 1), hz⟩
    exact hpq.symm.dvd_of_dvd_mul_right this
  obtain ⟨c, hc⟩ := hdvd
  have hcp : c * p = n * k + (n - 1) := by
    have : q * (c * p) = q * (n * k + (n - 1)) := by rw [← hz, hc]; ring
    exact mul_left_cancel₀ hq this
  have hcop : IsCoprime (c * p) (n : ℤ) := ⟨-1, k + 1, by rw [hcp]; ring⟩
  have h1 : IsCoprime c (n : ℤ) := hcop.of_mul_left_left
  have h2 : IsCoprime p (n : ℤ) := hcop.of_mul_left_right
  have h8q : (n : ℤ) ∣ q := by
    have : (n : ℤ) ∣ q * c := ⟨x, by rw [← hc]⟩
    exact h1.symm.dvd_of_dvd_mul_right this
  exact ⟨c, hc, hcp, h1, h2, h8q, ⟨k + 1, by rw [hcp]; ring⟩⟩

#print axioms entry_cofactor

/-- `c ≡ p (mod n)` for an opener's cofactor iff `p` is its own inverse mod `n`. -/
theorem cofactor_eq_iff_selfinverse (n : ℕ) (p c : ℤ) (hp : IsCoprime p (n : ℤ)) (hc : (n : ℤ) ∣ (c * p - 1)) :
    (n : ℤ) ∣ (c - p) ↔ (n : ℤ) ∣ (p * p - 1) := by
  constructor
  · intro h
    have : p * p - 1 = (p - c) * p + (c * p - 1) := by ring
    rw [this]
    exact dvd_add (dvd_mul_of_dvd_left (by simpa using (dvd_neg.mpr h : (n : ℤ) ∣ -(c - p))) _) hc
  · intro h
    have h1 : (n : ℤ) ∣ (c - p) * p := by
      have : (c - p) * p = (c * p - 1) - (p * p - 1) := by ring
      rw [this]; exact dvd_sub hc h
    exact hp.symm.dvd_of_dvd_mul_right h1

#print axioms cofactor_eq_iff_selfinverse

/-- `c' ≡ -p (mod n)` for an entry's cofactor iff `p` is its own inverse mod `n`. -/
theorem entry_cofactor_eq_iff_selfinverse (n : ℕ) (p c : ℤ) (hp : IsCoprime p (n : ℤ)) (hc : (n : ℤ) ∣ (c * p + 1)) :
    (n : ℤ) ∣ (c + p) ↔ (n : ℤ) ∣ (p * p - 1) := by
  constructor
  · intro h
    have : p * p - 1 = (p + c) * p - (c * p + 1) := by ring
    rw [this]
    exact dvd_sub (dvd_mul_of_dvd_left (by rwa [add_comm]) _) hc
  · intro h
    have h1 : (n : ℤ) ∣ (c + p) * p := by
      have : (c + p) * p = (c * p + 1) + (p * p - 1) := by ring
      rw [this]; exact dvd_add hc h
    exact hp.symm.dvd_of_dvd_mul_right h1

#print axioms entry_cofactor_eq_iff_selfinverse

/-- **Touch, general `n`.**  An opener's cofactor and an entry's cofactor at the same reduced instant sum to `0 (mod n)`:
the units `p⁻¹` and `-p⁻¹`.  This holds for EVERY `n`; the n = 8 reading "they are `p` and `-p`" needs `p² ≡ 1`. -/
theorem touch_cofactors (n : ℕ) (hn : 0 < n) (p q x y k k' : ℤ) (hq : q ≠ 0) (hpq : IsCoprime p q)
    (hx : (x : ℝ) * ((p : ℝ) / q) = (k : ℝ) + 1 / n)
    (hy : (y : ℝ) * ((p : ℝ) / q) = (k' : ℝ) + ((n : ℝ) - 1) / n) :
    ∃ c c' : ℤ, (n : ℤ) * x = q * c ∧ (n : ℤ) * y = q * c' ∧ (n : ℤ) ∣ (c + c') := by
  obtain ⟨c, hc, -, -, hp, -, h1⟩ := opener_cofactor n hn p q x k hq hpq hx
  obtain ⟨c', hc', -, -, -, -, h2⟩ := entry_cofactor n hn p q y k' hq hpq hy
  refine ⟨c, c', hc, hc', ?_⟩
  have h3 : (n : ℤ) ∣ (c + c') * p := by
    have : (c + c') * p = (c * p - 1) + (c' * p + 1) := by ring
    rw [this]; exact dvd_add h1 h2
  exact hp.symm.dvd_of_dvd_mul_right h3

#print axioms touch_cofactors

/-- **Touch ratio congruence, general `n`, no rational instant needed.**  If an integer `x` stands exactly `1/n` past
lap `k` and an integer `y` stands exactly `1/n` before lap `k'+1` at the same instant `t ≠ 0`, then
`x (n k' + n - 1) = y (n k + 1)` and `n ∣ x + y`. -/
theorem touch_sum_dvd (n : ℕ) (hn : 0 < n) (x y k k' : ℤ) (t : ℝ) (_ht : t ≠ 0)
    (hx : (x : ℝ) * t = (k : ℝ) + 1 / n) (hy : (y : ℝ) * t = (k' : ℝ) + ((n : ℝ) - 1) / n) :
    (x * (n * k' + n - 1) = y * (n * k + 1)) ∧ (n : ℤ) ∣ x + y := by
  have hnr : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have h1 : (n : ℝ) * (x * t) = n * k + 1 := by rw [hx]; field_simp
  have h2 : (n : ℝ) * (y * t) = n * k' + n - 1 := by rw [hy]; field_simp; ring
  have key : ((x * (n * k' + n - 1) : ℤ) : ℝ) = ((y * (n * k + 1) : ℤ) : ℝ) := by
    push_cast
    rw [← h2, ← h1]; ring
  have hk : x * (n * k' + n - 1) = y * (n * k + 1) := by exact_mod_cast key
  refine ⟨hk, ?_⟩
  refine ⟨(k' + 1) * x - k * y, ?_⟩
  linarith [hk]

#print axioms touch_sum_dvd

/-- **Width congruence, general `n`.**  The width of a cell with opener `(x,k)` and entry `(y,k')` is `m/(n x y)` with
`m = (n k' + n - 1) x - (n k + 1) y`, and `n ∣ m + x + y`. -/
theorem width_congruence_general (n : ℕ) (hn : 0 < n) (x y k k' : ℤ) (hx : 0 < x) (hy : 0 < y) :
    (((n * k' + n - 1 : ℝ)) / (n * y) - (n * k + 1 : ℝ) / (n * x)
      = (((n * k' + n - 1) * x - (n * k + 1) * y : ℤ) : ℝ) / (n * x * y)) ∧
    (n : ℤ) ∣ (((n * k' + n - 1) * x - (n * k + 1) * y) + (x + y)) := by
  have hnr : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  constructor
  · have hx' : (x : ℝ) ≠ 0 := by exact_mod_cast hx.ne'
    have hy' : (y : ℝ) ≠ 0 := by exact_mod_cast hy.ne'
    push_cast; field_simp
  · exact ⟨(k' + 1) * x - k * y, by ring⟩

#print axioms width_congruence_general

/-! ## Self-inverse units: exactly where the n = 8 form `c ≡ p` is the general form -/

/-- For `n ∣ 24`, every unit mod `n` is its own inverse: `n ∣ a² - 1` for `a` coprime to `n`. -/
theorem sq_one_of_dvd_24 (n : ℕ) (hn : n ∣ 24) (a : ℤ) (ha : IsCoprime a (n : ℤ)) : (n : ℤ) ∣ a * a - 1 := by
  have h2 : ∀ m : ℤ, m ∣ 24 → IsCoprime a m → ¬ (2 ∣ m ∧ 2 ∣ a) := by
    intro m _ hm ⟨h1, h2⟩
    have := hm.isUnit_of_dvd' h2 h1
    have : ¬ IsUnit (2 : ℤ) := by decide
    contradiction
  have h3 : ∀ m : ℤ, m ∣ 24 → IsCoprime a m → ¬ (3 ∣ m ∧ 3 ∣ a) := by
    intro m _ hm ⟨h1, h2⟩
    have := hm.isUnit_of_dvd' h2 h1
    have : ¬ IsUnit (3 : ℤ) := by decide
    contradiction
  -- n ∈ {1,2,3,4,6,8,12,24}
  have hn' : n ∈ Nat.divisors 24 := by simp [hn]
  have hlist : n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 6 ∨ n = 8 ∨ n = 12 ∨ n = 24 := by
    have : Nat.divisors 24 = {1, 2, 3, 4, 6, 8, 12, 24} := by decide
    rw [this] at hn'
    simpa using hn'
  have hm24 : (n : ℤ) ∣ 24 := by exact_mod_cast hn
  have a2 := h2 n hm24 ha
  have a3 := h3 n hm24 ha
  have key : (24 : ℤ) ∣ a * a - 1 ∨ ¬ ((2 ∣ (n : ℤ)) ∧ 2 ∣ a) := by
    right; exact a2
  rcases hlist with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp
  · -- n = 2: a odd
    have : ¬ (2 ∣ a) := fun h => a2 ⟨by norm_num, h⟩
    have h : a % 2 = 1 := by omega
    have : (a * a - 1) % 2 = 0 := by
      have := Int.mul_emod a a 2
      rw [h] at this; omega
    exact Int.dvd_of_emod_eq_zero (by simpa using this)
  · have : ¬ (3 ∣ a) := fun h => a3 ⟨by norm_num, h⟩
    have h : a % 3 = 1 ∨ a % 3 = 2 := by omega
    have : (a * a - 1) % 3 = 0 := by
      have := Int.mul_emod a a 3
      rcases h with h | h <;> rw [h] at this <;> omega
    exact Int.dvd_of_emod_eq_zero (by simpa using this)
  · have : ¬ (2 ∣ a) := fun h => a2 ⟨by norm_num, h⟩
    have h : a % 4 = 1 ∨ a % 4 = 3 := by omega
    have : (a * a - 1) % 4 = 0 := by
      have := Int.mul_emod a a 4
      rcases h with h | h <;> rw [h] at this <;> omega
    exact Int.dvd_of_emod_eq_zero (by simpa using this)
  · have n2 : ¬ (2 ∣ a) := fun h => a2 ⟨by norm_num, h⟩
    have n3 : ¬ (3 ∣ a) := fun h => a3 ⟨by norm_num, h⟩
    have h : a % 6 = 1 ∨ a % 6 = 5 := by omega
    have : (a * a - 1) % 6 = 0 := by
      have := Int.mul_emod a a 6
      rcases h with h | h <;> rw [h] at this <;> omega
    exact Int.dvd_of_emod_eq_zero (by simpa using this)
  · have n2 : ¬ (2 ∣ a) := fun h => a2 ⟨by norm_num, h⟩
    have h : a % 8 = 1 ∨ a % 8 = 3 ∨ a % 8 = 5 ∨ a % 8 = 7 := by omega
    have : (a * a - 1) % 8 = 0 := by
      have := Int.mul_emod a a 8
      rcases h with h | h | h | h <;> rw [h] at this <;> omega
    exact Int.dvd_of_emod_eq_zero (by simpa using this)
  · have n2 : ¬ (2 ∣ a) := fun h => a2 ⟨by norm_num, h⟩
    have n3 : ¬ (3 ∣ a) := fun h => a3 ⟨by norm_num, h⟩
    have h : a % 12 = 1 ∨ a % 12 = 5 ∨ a % 12 = 7 ∨ a % 12 = 11 := by omega
    have : (a * a - 1) % 12 = 0 := by
      have := Int.mul_emod a a 12
      rcases h with h | h | h | h <;> rw [h] at this <;> omega
    exact Int.dvd_of_emod_eq_zero (by simpa using this)
  · have n2 : ¬ (2 ∣ a) := fun h => a2 ⟨by norm_num, h⟩
    have n3 : ¬ (3 ∣ a) := fun h => a3 ⟨by norm_num, h⟩
    have h : a % 24 = 1 ∨ a % 24 = 5 ∨ a % 24 = 7 ∨ a % 24 = 11 ∨ a % 24 = 13 ∨ a % 24 = 17 ∨ a % 24 = 19 ∨
        a % 24 = 23 := by omega
    have : (a * a - 1) % 24 = 0 := by
      have := Int.mul_emod a a 24
      rcases h with h | h | h | h | h | h | h | h <;> rw [h] at this <;> omega
    exact Int.dvd_of_emod_eq_zero (by simpa using this)

#print axioms sq_one_of_dvd_24

/-- The self-inverse property fails at `n = 5, 7, 9, 10`: a unit whose square is not 1.  (So `c ≡ p` is false there:
`cofactor_eq_iff_selfinverse`.)  For `n` not dividing 24 such a unit always exists (reasoned: an odd prime `≥ 5`, or `9`,
or `16` divides `n`; not formalised for general `n`). -/
theorem not_selfinverse_examples :
    (IsCoprime (2 : ℤ) 5 ∧ ¬ (5 : ℤ) ∣ 2 * 2 - 1) ∧ (IsCoprime (2 : ℤ) 7 ∧ ¬ (7 : ℤ) ∣ 2 * 2 - 1) ∧
    (IsCoprime (2 : ℤ) 9 ∧ ¬ (9 : ℤ) ∣ 2 * 2 - 1) ∧ (IsCoprime (3 : ℤ) 10 ∧ ¬ (10 : ℤ) ∣ 3 * 3 - 1) := by
  refine ⟨⟨?_, by decide⟩, ⟨?_, by decide⟩, ⟨?_, by decide⟩, ⟨?_, by decide⟩⟩
  · exact ⟨-2, 1, by norm_num⟩
  · exact ⟨-3, 1, by norm_num⟩
  · exact ⟨5, -1, by norm_num⟩
  · exact ⟨-3, 1, by norm_num⟩

#print axioms not_selfinverse_examples

/-! ## Separation of the unit instants: at least `φ(n)` cells, every `n` -/

/-- If an integer `d > 0` has `d (a' - a) ≥ n` then some `t` in `[a/n, a'/n]` has `d t` a whole number (a lap line of `d`). -/
theorem lapline_between (n : ℕ) (hn : 0 < n) (d a a' : ℤ) (hd : 0 < d) (hle : (n : ℤ) ≤ d * (a' - a)) :
    ∃ t : ℝ, (a : ℝ) / n ≤ t ∧ t ≤ (a' : ℝ) / n ∧ distInt ((d : ℝ) * t) = 0 := by
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd
  set z : ℤ := ⌈(d : ℝ) * a / n⌉ with hz
  have h1 : (d : ℝ) * a / n ≤ z := Int.le_ceil _
  have h2 : (z : ℝ) < (d : ℝ) * a / n + 1 := Int.ceil_lt_add_one _
  have h3 : (1 : ℝ) ≤ (d : ℝ) * (a' - a) / n := by
    rw [le_div_iff₀ hnr]
    have : ((n : ℤ) : ℝ) ≤ ((d * (a' - a) : ℤ) : ℝ) := by exact_mod_cast hle
    push_cast at this; linarith
  refine ⟨(z : ℝ) / d, ?_, ?_, ?_⟩
  · rw [le_div_iff₀ hdr]
    have : (d : ℝ) * a / n = a / n * d := by ring
    nlinarith
  · rw [div_le_div_iff₀ hdr hnr]
    have : (z : ℝ) * n ≤ a' * d := by
      have e : (d : ℝ) * a' / n = (d : ℝ) * a / n + (d : ℝ) * (a' - a) / n := by ring
      have : (z : ℝ) ≤ (d : ℝ) * a' / n := by linarith
      rw [le_div_iff₀ hnr] at this
      linarith
    linarith
  · have : (d : ℝ) * ((z : ℝ) / d) = z := by field_simp
    rw [this]; exact distInt_intCast' z

#print axioms lapline_between

/-- For the AP-like case `d = n - 1`: every `t = a/(n-1)` with `a ≤ a'`-adjacent lies between. -/
theorem lapline_between_ap (n : ℕ) (hn : 2 ≤ n) (a a' : ℤ) (ha : 1 ≤ a) (haa : a < a') (ha' : a' ≤ n - 1) :
    ∃ t : ℝ, (a : ℝ) / n ≤ t ∧ t ≤ (a' : ℝ) / n ∧ distInt (((n - 1 : ℤ) : ℝ) * t) = 0 := by
  have hnr : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have har : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have haa' : (a : ℝ) + 1 ≤ a' := by exact_mod_cast haa
  have ha'n : (a' : ℝ) ≤ (n : ℝ) - 1 := by exact_mod_cast ha'
  refine ⟨(a : ℝ) / ((n : ℝ) - 1), ?_, ?_, ?_⟩
  · rw [div_le_div_iff₀ hnr hn1]; nlinarith
  · rw [div_le_div_iff₀ hn1 hnr]; nlinarith
  · have : (((n - 1 : ℤ) : ℝ)) * ((a : ℝ) / ((n : ℝ) - 1)) = (a : ℝ) := by
      push_cast; field_simp
    rw [this]; exact distInt_intCast' a

#print axioms lapline_between_ap

/-- **The unit instants lie in distinct cells, every `n`.**  For `n - 1` distinct positive integers none a multiple of `n`
and any two units `a < a'` (integers in `[1, n-1]`), the segment `[a/n, a'/n]` contains an instant at which some runner is
exactly on a lap line, so is not lonely.  With `unit_lonely_general` this gives at least `φ(n)` lonely cells for every `n`
(the case `n = 8` is `Boundaries.four_cells`).  The only way the largest disparity can be `≤ n` is the AP itself. -/
theorem units_separated (n : ℕ) (hn : 2 ≤ n) (D : Finset ℤ) (hpos : ∀ d ∈ D, 0 < d)
    (hmult : ∀ d ∈ D, ¬ (n : ℤ) ∣ d) (hcard : D.card = n - 1) (a a' : ℤ) (ha : 1 ≤ a) (haa : a < a')
    (ha' : a' ≤ n - 1) :
    ∃ d ∈ D, ∃ t : ℝ, (a : ℝ) / n ≤ t ∧ t ≤ (a' : ℝ) / n ∧ distInt ((d : ℝ) * t) = 0 := by
  have hn0 : 0 < n := by omega
  by_cases hbig : ∃ d ∈ D, (n : ℤ) < d
  · obtain ⟨d, hdD, hd⟩ := hbig
    obtain ⟨t, h1, h2, h3⟩ := lapline_between n hn0 d a a' (hpos d hdD) (by nlinarith)
    exact ⟨d, hdD, t, h1, h2, h3⟩
  · push Not at hbig
    -- [PROVISIONAL: counting tool] pigeonhole: D ⊆ Icc 1 (n-1) and |D| = n-1 force D = Icc 1 (n-1); supports `units_separated`
    -- (the case in which no disparity exceeds n is the AP itself).
    have hsub : D ⊆ Finset.Icc (1 : ℤ) ((n : ℤ) - 1) := by
      intro d hd
      have h1 := hpos d hd
      have h2 := hbig d hd
      have h3 : d ≠ n := fun h => hmult d hd (h ▸ dvd_refl _)
      simp only [Finset.mem_Icc]; omega
    have hcard' : (Finset.Icc (1 : ℤ) ((n : ℤ) - 1)).card = n - 1 := by
      simp only [Int.card_Icc]; omega
    have heq : D = Finset.Icc (1 : ℤ) ((n : ℤ) - 1) :=
      Finset.eq_of_subset_of_card_le hsub (by rw [hcard, hcard'])
    have hmem : ((n : ℤ) - 1) ∈ D := by
      rw [heq]; simp only [Finset.mem_Icc]; omega
    obtain ⟨t, h1, h2, h3⟩ := lapline_between_ap n hn a a' ha haa ha'
    exact ⟨(n : ℤ) - 1, hmem, t, h1, h2, h3⟩

#print axioms units_separated

/-! ## The gate, every `n` -/

/-- **Gate lemma, general `n`.**  With `R = n m t`: for `R` in the open window `(n - 1, n + 1)` the runner of disparity `m`
is within `1/n` of lap 1, so it is in the way.  Hence a set containing `m` has no lonely instant with `R` in the window. -/
theorem gate_blocks (n : ℕ) (hn : 0 < n) (m t : ℝ) (h1 : (n : ℝ) - 1 < n * m * t) (h2 : n * m * t < n + 1) :
    distInt (m * t) < 1 / n := by
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have e1 : ((n : ℝ) - 1) / n = 1 - 1 / n := by field_simp
  have e2 : ((n : ℝ) + 1) / n = 1 + 1 / n := by field_simp
  have h3 : ((n : ℝ) - 1) / n < m * t := by
    rw [div_lt_iff₀ hnr]; linarith
  have h4 : m * t < ((n : ℝ) + 1) / n := by
    rw [lt_div_iff₀ hnr]; linarith
  have : |m * t - ((1 : ℤ) : ℝ)| < 1 / n := by
    rw [abs_lt]; push_cast
    constructor <;> linarith
  exact lt_of_le_of_lt (distInt_le_abs _ _) this

#print axioms gate_blocks

theorem no_lonely_in_gate (n : ℕ) (hn : 0 < n) (ds : Finset ℝ) (m : ℝ) (hm : m ∈ ds) (t : ℝ)
    (h1 : (n : ℝ) - 1 < n * m * t) (h2 : n * m * t < n + 1) :
    ¬ (∀ d ∈ ds, (1 / n : ℝ) ≤ distInt (d * t)) := by
  intro h
  have := h m hm
  have := gate_blocks n hn m t h1 h2
  linarith

#print axioms no_lonely_in_gate

/-! ## Whole-set conjugate for integer disparities, every `n` -/

/-- For integer disparities and a rational instant `t0 = r/q`, the multiplier `N = n q - 1 ≡ -1 (mod n)` sends `t0` to an
instant whose readings are the negatives mod 1 of the old ones: the same distance from a lap. -/
theorem conj_integer (n q : ℕ) (hq : 0 < q) (r d : ℤ) :
    distInt ((d : ℝ) * ((((n : ℤ) * q - 1 : ℤ) : ℝ) * ((r : ℝ) / q))) = distInt ((d : ℝ) * ((r : ℝ) / q)) := by
  have hqr : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have e : (d : ℝ) * ((((n : ℤ) * q - 1 : ℤ) : ℝ) * ((r : ℝ) / q))
      = (((n : ℤ) * d * r : ℤ) : ℝ) - (d : ℝ) * ((r : ℝ) / q) := by
    push_cast; field_simp
  rw [e, distInt_int_sub']

#print axioms conj_integer

/-- An opener becomes an entry under the conjugate multiplier: if `d t0 = k + 1/n` then `d N t0 = m + (n-1)/n`. -/
theorem conj_integer_opener (n q : ℕ) (hn : 0 < n) (hq : 0 < q) (r d k : ℤ)
    (h : (d : ℝ) * ((r : ℝ) / q) = (k : ℝ) + 1 / n) :
    ∃ m : ℤ, (d : ℝ) * ((((n : ℤ) * q - 1 : ℤ) : ℝ) * ((r : ℝ) / q)) = (m : ℝ) + ((n : ℝ) - 1) / n := by
  have hqr : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hnr : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  refine ⟨(n : ℤ) * d * r - k - 1, ?_⟩
  have e : (d : ℝ) * ((((n : ℤ) * q - 1 : ℤ) : ℝ) * ((r : ℝ) / q))
      = (((n : ℤ) * d * r : ℤ) : ℝ) - (d : ℝ) * ((r : ℝ) / q) := by
    push_cast; field_simp
  rw [e, h]; push_cast; field_simp; ring

#print axioms conj_integer_opener

end AcrossN

end Fresh
