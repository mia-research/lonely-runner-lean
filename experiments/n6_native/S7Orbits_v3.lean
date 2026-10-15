import Mathlib
import LonelyRunner.LRC.Spec.GlobalIsolationTwoN

/-!
# BHK §7: which meeting-time orbits miss the parallelogram, for every order (n6_native, E55)

At the meeting times `k/D` of BHK §7 runners 2 and 3 coincide; the point `({k c₃/n}, {k c₁/n})` of the orbit
`⟨(c₃, c₁)⟩ ⊂ (ℤ/n)²` lies in BHK's parallelogram `P` (a full 3-gap that is a 123-gap) for the ratio `ρ = v₁/v₃`
exactly when `ρ` is at most a bound attached to the point. In §7, `ρ < 1/3`, so the main route can fail only
for an orbit with no point in `P_{1/3}`. In whole numbers, a point `(x/n, y/n)` lies in `P_{1/3}` iff
`n ≤ 6x ≤ 5n` and `6x + 2n ≤ 18y ≤ 10n + 6x` (`inP`).

`check_orbits`: for every order `2 ≤ n ≤ 35` and generator `(a, b)` off the axes with `gcd(a, b, n) = 1`, the
orbit has a point in `P_{1/3}` unless it is `G₄` (`n = 4`, `a ≡ 2`, `b` odd) or `G₇` (`n = 7`, `a ≡ 2b`,
`b ≢ 0`). One kernel computation. For `n ≥ 36`, `orbit_isolation_two_bhk` (framework) with the short-step
bounds of E55 leaves no failure.
-/

namespace N6Native

/-- The point `(x/n, y/n)` lies in BHK's parallelogram at ratio `1/3`. -/
def inP (n x y : ℕ) : Bool := n ≤ 6 * x && 6 * x ≤ 5 * n && 6 * x + 2 * n ≤ 18 * y && 18 * y ≤ 10 * n + 6 * x

/-- BHK's two exceptional orbits. -/
def isExc (n a b : ℕ) : Bool :=
  (n == 4 && a % 4 == 2 && b % 2 == 1) || (n == 7 && b % 7 != 0 && a % 7 == (2 * b) % 7)

def orbitHits (n a b : ℕ) : Bool := (List.range n).any fun k => inP n ((a * k) % n) ((b * k) % n)

def check (N : ℕ) : Bool :=
  (List.range (N + 1)).all fun n => (List.range n).all fun a => (List.range n).all fun b =>
    !(2 ≤ n && 1 ≤ a && 1 ≤ b && Nat.gcd (Nat.gcd a b) n == 1) || isExc n a b || orbitHits n a b

set_option maxHeartbeats 0 in
theorem check_orbits : check 35 = true := by decide +kernel

/-- The finite check, unpacked. -/
theorem orbit_hits_or_exc {n a b : ℕ} (hn2 : 2 ≤ n) (hn : n ≤ 35) (ha : 1 ≤ a) (han : a < n) (hb : 1 ≤ b)
    (hbn : b < n) (hg : Nat.gcd (Nat.gcd a b) n = 1) :
    isExc n a b = true ∨ ∃ k < n, inP n ((a * k) % n) ((b * k) % n) = true := by
  have h := check_orbits
  simp only [check, List.all_eq_true, List.mem_range] at h
  have := h n (by omega) a han b hbn
  simp only [Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not,
    not_le, beq_eq_false_iff_ne, ne_eq] at this
  rcases this with ((((h1 | h1) | h1) | h1) | h1) | h1
  · omega
  · omega
  · omega
  · exact absurd hg h1
  · exact Or.inl h1
  · right
    simp only [orbitHits, List.any_eq_true, List.mem_range] at h1
    obtain ⟨k, hk, hk'⟩ := h1
    exact ⟨k, hk, hk'⟩

/-- The exceptional orbits really miss `P_{1/3}`. -/
theorem g4_misses : orbitHits 4 2 1 = false := by decide
theorem g7_misses : orbitHits 7 2 1 = false := by decide

/-- **The bounded short steps.** For a step `(i, j)` allowed by `orbit_isolation_two_bhk`
(`0 ≤ i ≤ 4`, `|6j| < 9 + 2i`) with `i, j ≠ 0` and `(i, j) ≠ (1, ±1)`, the step inequality
`2/9·i + 2/3·|j| − 2/n·i·|j| < 1` forces `n < 36`. The steps left for `n ≥ 36` are `(1, ±1)`, `(i, 0)`
and the axis steps `(0, ±1)`, `(1, 0)`. -/
theorem short_step_bounded {i j : ℤ} {n : ℝ} (hn : 36 ≤ n) (hi0 : 0 ≤ i) (hi4 : i ≤ 4)
    (hj1 : -(9 + 2 * i) < 6 * j) (hj2 : 6 * j < 9 + 2 * i) (hi : i ≠ 0) (hj : j ≠ 0)
    (hd : ¬ (i = 1 ∧ (j = 1 ∨ j = -1))) :
    1 ≤ 2 / 9 * |(i : ℝ)| + 2 / 3 * |(j : ℝ)| - 2 / n * |(i : ℝ)| * |(j : ℝ)| := by
  have hn0 : 0 < n := by linarith
  have hjb : -2 ≤ j ∧ j ≤ 2 := by constructor <;> omega
  obtain ⟨hjl, hju⟩ := hjb
  interval_cases i <;> interval_cases j <;> simp at hj hi hd ⊢ <;>
    (rw [div_mul_eq_mul_div, div_mul_eq_mul_div]; rw [← sub_nonneg]; field_simp; nlinarith)

open LRC.OrderSixN

/-- A point of the orbit, read back in whole numbers. -/
theorem point_of_mem {n c₃ c₁ x y : ℕ} (hn : 0 < n) (hx : x < n) (hy : y < n)
    (h : ((x : ZMod n), (y : ZMod n)) ∈ meetingOrbit n c₃ c₁) :
    ∃ k < n, (c₃ * k) % n = x ∧ (c₁ * k) % n = y := by
  have h' : (((x : ℤ) : ZMod n), ((y : ℤ) : ZMod n)) ∈ meetingOrbit n c₃ c₁ := by
    simpa only [Int.cast_natCast] using h
  obtain ⟨k, hk, h1, h2⟩ := (mem_meetingOrbit_iff n c₃ c₁ hn x y).mp h'
  have e1 : ((x : ℤ) % n) = x := Int.emod_eq_of_lt (by positivity) (by exact_mod_cast hx)
  have e2 : ((y : ℤ) % n) = y := Int.emod_eq_of_lt (by positivity) (by exact_mod_cast hy)
  refine ⟨k, hk, ?_, ?_⟩
  · have := h1.symm.trans e1; exact_mod_cast this
  · have := h2.symm.trans e2; exact_mod_cast this

/-- An orbit step in `ZMod n` terms. -/
theorem step_of_onOrbit {n c₃ c₁ : ℕ} (hn : 0 < n) {i j : ℤ} (h : OnOrbit n c₃ c₁ i j) :
    ∃ z : ℤ, z * (c₃ : ZMod n) = (i : ZMod n) ∧ z * (c₁ : ZMod n) = (j : ZMod n) := by
  have hm := (mem_meetingOrbit_iff n c₃ c₁ hn i j).mpr h
  obtain ⟨z, hz⟩ := AddSubgroup.mem_zmultiples_iff.mp hm
  refine ⟨z, ?_, ?_⟩
  · have := congrArg Prod.fst hz; simpa [zsmul_eq_mul] using this
  · have := congrArg Prod.snd hz; simpa [zsmul_eq_mul] using this

theorem natCast_zmod_ne_zero {n c : ℕ} (h : c % n ≠ 0) : (c : ZMod n) ≠ 0 := by
  intro h0; rw [ZMod.natCast_eq_zero_iff] at h0; exact h (Nat.mod_eq_zero_of_dvd h0)

/-- Membership of `z • (c₃, c₁)`. -/
theorem zsmul_mem_orbit (n c₃ c₁ : ℕ) (z : ℤ) :
    (z * (c₃ : ZMod n), z * (c₁ : ZMod n)) ∈ meetingOrbit n c₃ c₁ := by
  have := (meetingOrbit n c₃ c₁).zsmul_mem (AddSubgroup.mem_zmultiples ((c₃ : ZMod n), (c₁ : ZMod n))) z
  simpa [zsmul_eq_mul] using this

/-- **Axis steps cannot occur off the axes**: `(0, ±1)` on the orbit forces `c₃ ≡ 0`; `(1, 0)` forces
`c₁ ≡ 0`. -/
theorem axis_step_c3 {n c₃ c₁ : ℕ} (hn : 0 < n) {j : ℤ} (hj : j = 1 ∨ j = -1)
    (h : OnOrbit n c₃ c₁ 0 j) : (c₃ : ZMod n) = 0 := by
  obtain ⟨z, h3, h1⟩ := step_of_onOrbit hn h
  push_cast at h3
  rcases hj with rfl | rfl
  · push_cast at h1
    calc (c₃ : ZMod n) = c₃ * (z * c₁) := by rw [h1, mul_one]
      _ = c₁ * (z * c₃) := by ring
      _ = 0 := by rw [h3, mul_zero]
  · push_cast at h1
    calc (c₃ : ZMod n) = -(c₃ * (z * c₁)) := by rw [h1]; ring
      _ = -(c₁ * (z * c₃)) := by ring
      _ = 0 := by rw [h3]; ring

theorem axis_step_c1 {n c₃ c₁ : ℕ} (hn : 0 < n) (h : OnOrbit n c₃ c₁ 1 0) : (c₁ : ZMod n) = 0 := by
  obtain ⟨z, h3, h1⟩ := step_of_onOrbit hn h
  push_cast at h3 h1
  calc (c₁ : ZMod n) = c₁ * (z * c₃) := by rw [h3, mul_one]
    _ = c₃ * (z * c₁) := by ring
    _ = 0 := by rw [h1, mul_zero]

/-- **The diagonal step** `(1, ±1)`: the orbit contains `(m, ±m)` for every `m`, and `m = ⌊n/2⌋` lies in
`P_{1/3}`. -/
theorem diag_step_hits {n c₃ c₁ : ℕ} (hn : 2 ≤ n) {j : ℤ} (hj : j = 1 ∨ j = -1)
    (h : OnOrbit n c₃ c₁ 1 j) : ∃ k < n, inP n ((c₃ * k) % n) ((c₁ * k) % n) = true := by
  have hn0 : 0 < n := by omega
  obtain ⟨z, h3, h1⟩ := step_of_onOrbit hn0 h
  push_cast at h3
  set m := n / 2 with hm
  have hm1 : 1 ≤ m := by omega
  have hmn : m < n := by omega
  have hmem := zsmul_mem_orbit n c₃ c₁ ((m : ℤ) * z)
  rcases hj with rfl | rfl
  · push_cast at h1
    have e : (((m : ℤ) * z : ℤ) * (c₃ : ZMod n), ((m : ℤ) * z : ℤ) * (c₁ : ZMod n)) =
        ((m : ZMod n), (m : ZMod n)) := by
      push_cast; rw [mul_assoc, mul_assoc, h3, h1, mul_one]
    rw [e] at hmem
    obtain ⟨k, hk, hx, hy⟩ := point_of_mem hn0 hmn hmn hmem
    refine ⟨k, hk, ?_⟩
    rw [hx, hy]; simp only [inP, Bool.and_eq_true, decide_eq_true_eq]; omega
  · push_cast at h1
    have e : (((m : ℤ) * z : ℤ) * (c₃ : ZMod n), ((m : ℤ) * z : ℤ) * (c₁ : ZMod n)) =
        ((m : ZMod n), ((n - m : ℕ) : ZMod n)) := by
      push_cast
      rw [Nat.cast_sub hmn.le, ZMod.natCast_self, mul_assoc, mul_assoc, h3, h1]; ring
    rw [e] at hmem
    obtain ⟨k, hk, hx, hy⟩ := point_of_mem hn0 hmn (by omega) hmem
    refine ⟨k, hk, ?_⟩
    rw [hx, hy]; simp only [inP, Bool.and_eq_true, decide_eq_true_eq]; omega

/-- **Walking by a step.** The least `t` with `L ≤ 3(X + t·i)`: below it every `t'` falls short, and it
overshoots by less than `3i` unless `t = 0`. -/
theorem walk {X i L : ℕ} (hi : 0 < i) :
    ∃ t, L ≤ 3 * (X + t * i) ∧ (∀ t' < t, 3 * (X + t' * i) < L) ∧ (t = 0 ∨ 3 * (X + t * i) < L + 3 * i) := by
  classical
  have hex : ∃ t, L ≤ 3 * (X + t * i) := ⟨L, by nlinarith⟩
  refine ⟨Nat.find hex, Nat.find_spec hex, fun t' ht' => by
    have := Nat.find_min hex ht'; omega, ?_⟩
  rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
  · exact Or.inl h0
  · right
    have h1 := Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega)
    have e : (Nat.find hex - 1) * i + i = Nat.find hex * i := by
      rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel hpos]
    omega

/-- **The horizontal step** `(i, 0)`, `1 ≤ i ≤ 4`, off the axes: an orbit point at height in `[n/3, 2n/3]`
(Bézout on `c₁`), walked by the step `(i, 0)` into `x ∈ [n/3, 2n/3]`, lies in `P_{1/3}`. -/
theorem horiz_step_hits {n c₃ c₁ : ℕ} (hn : 12 ≤ n) (h1 : c₁ % n ≠ 0) {i : ℕ} (hi1 : 1 ≤ i) (hi4 : i ≤ 4)
    (h : OnOrbit n c₃ c₁ i 0) : ∃ k < n, inP n ((c₃ * k) % n) ((c₁ * k) % n) = true := by
  classical
  have hn0 : 0 < n := by omega
  haveI : NeZero n := ⟨by omega⟩
  obtain ⟨z₀, h3, h1'⟩ := step_of_onOrbit hn0 h
  push_cast at h3 h1'
  set g := Nat.gcd c₁ n with hg
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_right _ hn0
  have hgn : g ∣ n := Nat.gcd_dvd_right _ _
  have hg1 : g ∣ c₁ := Nat.gcd_dvd_left _ _
  have hg2 : 2 * g ≤ n := by
    obtain ⟨q, hq⟩ := hgn
    have hq2 : 2 ≤ q := by
      rcases Nat.lt_or_ge q 2 with hq2 | hq2
      · interval_cases q
        · omega
        · exfalso; apply h1; rw [hq, mul_one] at *; exact Nat.mod_eq_zero_of_dvd hg1
      · exact hq2
    nlinarith
  -- the height y = s·g ∈ [n/3, 2n/3]
  obtain ⟨s, hs1, hsmin, hs2⟩ := walk (X := 0) (L := n) hgpos
  have hy1 : n ≤ 3 * (s * g) := by simpa using hs1
  have hy2 : 3 * (s * g) ≤ 2 * n := by
    rcases hs2 with h0 | h0
    · subst h0; simp at hs1; omega
    · by_cases hbig : n ≤ 3 * g
      · have : ¬ (1 < s) := fun h' => by have := hsmin 1 h'; simp at this; omega
        have hs1' : s = 1 := by
          rcases Nat.lt_or_ge s 2 with h'' | h''
          · interval_cases s <;> simp_all
          · omega
        subst hs1'; omega
      · simp at h0; omega
  set y := s * g with hy
  have hyn : y < n := by omega
  have hbez : (g : ZMod n) = (c₁ : ZMod n) * (Nat.gcdA c₁ n : ZMod n) := by
    have := Nat.gcd_eq_gcd_ab c₁ n
    have h' : ((g : ℤ) : ZMod n) = ((c₁ * Nat.gcdA c₁ n + n * Nat.gcdB c₁ n : ℤ) : ZMod n) := by
      rw [hg, this]
    push_cast at h'; rw [ZMod.natCast_self, zero_mul, add_zero] at h'; exact h'
  set zA : ℤ := (s : ℤ) * Nat.gcdA c₁ n with hzA
  set X : ℕ := ((zA : ZMod n) * c₃).val with hX
  have hXn : X < n := ZMod.val_lt _
  -- walk x into [n/3, 2n/3]
  obtain ⟨t, ht⟩ : ∃ t, n ≤ 3 * ((X + t * i) % n) ∧ 3 * ((X + t * i) % n) ≤ 2 * n := by
    by_cases hA : n ≤ 3 * X ∧ 3 * X ≤ 2 * n
    · exact ⟨0, by simpa [Nat.mod_eq_of_lt hXn] using hA⟩
    · rcases Nat.lt_or_ge (3 * X) n with hB | hB
      · obtain ⟨t, ht1, -, ht2⟩ := walk (X := X) (L := n) (i := i) (by omega)
        rcases ht2 with h0 | h0
        · subst h0; simp at ht1; omega
        · have hlt : X + t * i < n := by omega
          refine ⟨t, ?_, ?_⟩ <;> rw [Nat.mod_eq_of_lt hlt] <;> omega
      · obtain ⟨t, ht1, -, ht2⟩ := walk (X := X) (L := 4 * n) (i := i) (by omega)
        rcases ht2 with h0 | h0
        · subst h0; simp at ht1; omega
        · have hrng : n ≤ X + t * i ∧ X + t * i < 2 * n := by omega
          have hm : (X + t * i) % n = X + t * i - n := by
            rw [Nat.mod_eq_sub_mod hrng.1, Nat.mod_eq_of_lt (by omega)]
          refine ⟨t, ?_, ?_⟩ <;> rw [hm] <;> omega
  set x := (X + t * i) % n with hx
  have hmem := zsmul_mem_orbit n c₃ c₁ (zA + (t : ℤ) * z₀)
  have e : (((zA + (t : ℤ) * z₀ : ℤ) : ZMod n) * c₃, ((zA + (t : ℤ) * z₀ : ℤ) : ZMod n) * c₁) =
      ((x : ZMod n), (y : ZMod n)) := by
    have hXc : ((X : ℕ) : ZMod n) = (zA : ZMod n) * c₃ := by rw [hX]; exact ZMod.natCast_zmod_val _
    have ex : ((x : ℕ) : ZMod n) = (X : ZMod n) + t * i := by rw [hx, ZMod.natCast_mod]; push_cast; ring
    refine Prod.ext ?_ ?_
    · show ((zA + (t : ℤ) * z₀ : ℤ) : ZMod n) * c₃ = (x : ZMod n)
      rw [ex, hXc]; push_cast; rw [add_mul, mul_assoc, h3]
    · show ((zA + (t : ℤ) * z₀ : ℤ) : ZMod n) * c₁ = (y : ZMod n)
      rw [hy]; push_cast; rw [add_mul, mul_assoc (t : ZMod n), h1', mul_zero, add_zero, hzA]
      push_cast; rw [mul_assoc, mul_comm (Nat.gcdA c₁ n : ZMod n), ← hbez]
  rw [e] at hmem
  obtain ⟨k, hk, hkx, hky⟩ := point_of_mem hn0 (Nat.mod_lt _ hn0) hyn hmem
  refine ⟨k, hk, ?_⟩
  rw [hkx, hky]; simp only [inP, Bool.and_eq_true, decide_eq_true_eq]; omega

/-- **BHK §7's main route fails only on `G₄` and `G₇`, for every order.** An orbit `⟨(c₃, c₁)⟩ ⊂ (ℤ/n)²`
off the axes (`c₃, c₁ ≢ 0`) with `gcd(n, c₃, c₁) = 1` has a meeting time whose point lies in `P_{1/3}`
(so the main route works for every ratio `v₁/v₃ ≤ 1/3`), unless it is BHK's `G₄` or `G₇`. Order `n ≤ 35`:
`check_orbits`; `n ≥ 36`: the framework's two-dimensional global isolation `orbit_isolation_two_bhk`, its
box inside `P_{1/3}`, and the short steps: axis steps impossible, diagonal and horizontal steps hit, the rest
bounded (`short_step_bounded`). -/
theorem s7_main_route (n c₃ c₁ : ℕ) (hn : 2 ≤ n) (hg : Nat.gcd n (Nat.gcd c₃ c₁) = 1)
    (h3 : c₃ % n ≠ 0) (h1 : c₁ % n ≠ 0) (hx : isExc n (c₃ % n) (c₁ % n) = false) :
    ∃ k < n, inP n ((c₃ * k) % n) ((c₁ * k) % n) = true := by
  have hn0 : 0 < n := by omega
  rcases Nat.lt_or_ge n 36 with hsmall | hbig
  · -- the finite check, on residues
    have hg' : Nat.gcd (Nat.gcd (c₃ % n) (c₁ % n)) n = 1 := by
      set d := Nat.gcd (Nat.gcd (c₃ % n) (c₁ % n)) n
      have hdn : d ∣ n := Nat.gcd_dvd_right _ _
      have hd3 : d ∣ c₃ := (Nat.dvd_mod_iff hdn).mp ((Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_left _ _))
      have hd1 : d ∣ c₁ := (Nat.dvd_mod_iff hdn).mp ((Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_right _ _))
      exact Nat.dvd_one.mp (hg ▸ Nat.dvd_gcd hdn (Nat.dvd_gcd hd3 hd1))
    rcases orbit_hits_or_exc hn (by omega) (by omega) (Nat.mod_lt _ hn0) (by omega) (Nat.mod_lt _ hn0) hg'
      with h | ⟨k, hk, hk'⟩
    · rw [hx] at h; exact absurd h (by simp)
    · refine ⟨k, hk, ?_⟩; rwa [Nat.mod_mul_mod, Nat.mod_mul_mod] at hk'
  · rcases orbit_isolation_two_bhk n c₃ c₁ (by omega) hg with
      ⟨k, hk, a1, a2, b1, b2⟩ | ⟨i, j, hne, hon, hi0, hi4, hj1, hj2, -, hineq, -, -⟩
    · exact ⟨k, hk, by simp only [inP, Bool.and_eq_true, decide_eq_true_eq]; omega⟩
    · have h3' : (c₃ : ZMod n) ≠ 0 := natCast_zmod_ne_zero h3
      have h1' : (c₁ : ZMod n) ≠ 0 := natCast_zmod_ne_zero h1
      by_cases hi : i = 0
      · subst hi
        have hj : j = 1 ∨ j = -1 := by
          have : j ≠ 0 := fun h => hne (by simp [h])
          omega
        exact absurd (axis_step_c3 hn0 hj hon) h3'
      by_cases hj : j = 0
      · subst hj
        by_cases hi1 : i = 1
        · subst hi1; exact absurd (axis_step_c1 hn0 hon) h1'
        · obtain ⟨i', rfl⟩ : ∃ i' : ℕ, i = i' := ⟨i.toNat, by omega⟩
          exact horiz_step_hits (by omega) h1 (by omega) (by omega) hon
      by_cases hd : i = 1 ∧ (j = 1 ∨ j = -1)
      · obtain ⟨rfl, hj'⟩ := hd
        exact diag_step_hits hn hj' hon
      · have hb := short_step_bounded (n := (n : ℝ)) (by exact_mod_cast hbig) hi0 hi4 hj1 hj2 hi hj hd
        linarith

end N6Native

#print axioms N6Native.check_orbits
#print axioms N6Native.orbit_hits_or_exc
#print axioms N6Native.g4_misses
#print axioms N6Native.g7_misses
#print axioms N6Native.short_step_bounded
#print axioms N6Native.s7_main_route
