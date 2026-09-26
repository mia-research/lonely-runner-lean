import LonelyRunner.LRC.Spec.MirrorCentreN

/-!
# The progression's isolation pairs, and why a deformation displaces them rather than destroying them

2026-09-26 (running log E69).  At the progression, readings `j·c` (`j = 1, …, 7`), the subject is lonely at the four
instants `t = a/(8c)`, `a ∈ {1, 3, 5, 7}`, and at each of them every runner sits on an odd multiple of `1/8`.  Exactly
two are on the edge of their zone: runner `a` is leaving it (`a·a ≡ 1 mod 8`) and runner `8 − a` is entering it
(`a(8 − a) ≡ 7`); the other five sit at `2/8 … 6/8` of a lap, a clear margin of at least `1/8`.

Deform the readings to any `d j` with `|d j − j·c| ≤ c/20`.  Instant `a` survives as the interval
`[a²/(8·d a), a(8 − a)/(8·d (8 − a))]`, which is nonempty exactly when `a·d (8 − a) ≤ (8 − a)·d a`
(`instant_lonely`).  The four instants come in two complementary pairs, `(1, 7)` and `(3, 5)`: for `(1, 7)` the
conditions are `d 7 ≤ 7·d 1` and `7·d 1 ≤ d 7`, for `(3, 5)` they are `3·d 5 ≤ 5·d 3` and `5·d 3 ≤ 3·d 5`.  One of each
pair always holds, so **every deformation in the neighbourhood keeps one instant of each pair lonely**
(`pair_law`): the isolation is displaced within its pair, never destroyed.  `a = 1` is the first spine instant
`1/(8·d 1)`; its condition `d 7 ≤ 7·d 1` is R1.

Exact, not first order.  Everything here is proved; no `sorry`, no `native_decide`.
-/

namespace LRC.ProgressionPair

open LRC.MirrorCentre

/-- A position within `1/8` of `n/8` with `n mod 8 ∈ [2, 6]` is clear. -/
theorem clear_mid {x : ℝ} (n : ℕ) (hr : 2 ≤ n % 8 ∧ n % 8 ≤ 6) (h : |x - (n : ℝ) / 8| ≤ 1 / 8) :
    (8 : ℝ)⁻¹ ≤ circDist x := by
  have hn : (n : ℝ) = 8 * ((n / 8 : ℕ) : ℝ) + ((n % 8 : ℕ) : ℝ) := by exact_mod_cast (Nat.div_add_mod n 8).symm
  have hr1 : (2 : ℝ) ≤ ((n % 8 : ℕ) : ℝ) := by exact_mod_cast hr.1
  have hr2 : ((n % 8 : ℕ) : ℝ) ≤ 6 := by exact_mod_cast hr.2
  obtain ⟨h1, h2⟩ := abs_le.mp h
  rw [show (8 : ℝ)⁻¹ = 1 / 8 by norm_num]
  generalize n / 8 = k at hn
  refine circDist_ge_of_window (m := (k : ℤ)) ?_ ?_ (by norm_num) <;> simp only [Int.cast_natCast] <;> linarith

/-- The runner leaving its zone: exactly at `n/8` with `n ≡ 1 mod 8`. -/
theorem clear_leave {x : ℝ} (n : ℕ) (hr : n % 8 = 1) (h : x = (n : ℝ) / 8) : (8 : ℝ)⁻¹ ≤ circDist x := by
  have hn : (n : ℝ) = 8 * ((n / 8 : ℕ) : ℝ) + ((n % 8 : ℕ) : ℝ) := by exact_mod_cast (Nat.div_add_mod n 8).symm
  rw [hr] at hn
  rw [show (8 : ℝ)⁻¹ = 1 / 8 by norm_num]
  generalize n / 8 = k at hn
  push_cast at hn
  refine circDist_ge_of_window (m := (k : ℤ)) ?_ ?_ (by norm_num) <;> simp only [Int.cast_natCast] <;> linarith

/-- The runner entering its zone: within `1/8` below `n/8` with `n ≡ 7 mod 8`. -/
theorem clear_enter {x : ℝ} (n : ℕ) (hr : n % 8 = 7) (h1 : |x - (n : ℝ) / 8| ≤ 1 / 8) (h2 : x ≤ (n : ℝ) / 8) :
    (8 : ℝ)⁻¹ ≤ circDist x := by
  have hn : (n : ℝ) = 8 * ((n / 8 : ℕ) : ℝ) + ((n % 8 : ℕ) : ℝ) := by exact_mod_cast (Nat.div_add_mod n 8).symm
  rw [hr] at hn
  obtain ⟨h3, -⟩ := abs_le.mp h1
  rw [show (8 : ℝ)⁻¹ = 1 / 8 by norm_num]
  generalize n / 8 = k at hn
  push_cast at hn
  refine circDist_ge_of_window (m := (k : ℤ)) ?_ ?_ (by norm_num) <;> simp only [Int.cast_natCast] <;> linarith

/-- **The deviation bound.**  With every reading within `c/20` of the progression, runner `j` at the instant
`a²/(8·d a)` sits within `1/8` of its progression position `j·a/8`. -/
theorem dev_bound {c a j da dj : ℝ} (hc : 0 < c) (ha1 : 1 ≤ a) (ha7 : a ≤ 7) (hj0 : 0 ≤ j) (hj7 : j ≤ 7)
    (hda : |da - a * c| ≤ c / 20) (hdj : |dj - j * c| ≤ c / 20) :
    |dj * (a ^ 2 / (8 * da)) - j * a / 8| ≤ 1 / 8 := by
  have hda' := abs_le.mp hda
  have hlow : 19 / 20 * (a * c) ≤ da := by nlinarith
  have hpos : 0 < da := by nlinarith
  have e : dj * (a ^ 2 / (8 * da)) - j * a / 8 = a * (a * dj - j * da) / (8 * da) := by
    field_simp
  have hnum : |a * dj - j * da| ≤ 14 * c / 20 := by
    have e2 : a * dj - j * da = a * (dj - j * c) - j * (da - a * c) := by ring
    rw [e2]
    calc |a * (dj - j * c) - j * (da - a * c)| ≤ |a * (dj - j * c)| + |j * (da - a * c)| := abs_sub _ _
      _ = a * |dj - j * c| + j * |da - a * c| := by
          rw [abs_mul, abs_mul, abs_of_pos (by linarith : (0 : ℝ) < a), abs_of_nonneg hj0]
      _ ≤ a * (c / 20) + j * (c / 20) := by
          gcongr
      _ ≤ 14 * c / 20 := by nlinarith
  rw [e, abs_div, abs_mul, abs_of_pos (by linarith : (0 : ℝ) < a), abs_of_pos (by linarith : (0 : ℝ) < 8 * da),
    div_le_iff₀ (by linarith)]
  have := mul_le_mul_of_nonneg_left hnum (by linarith : (0 : ℝ) ≤ a)
  nlinarith

/-- **One instant of the progression, deformed.**  For `a ∈ {1, 3, 5, 7}`, readings within `c/20` of `j·c`, and
`a·d (8 − a) ≤ (8 − a)·d a`, all seven readings are clear at `a²/(8·d a)`. -/
theorem instant_lonely {c : ℝ} (hc : 0 < c) {d : ℕ → ℝ} (hd : ∀ j, 1 ≤ j → j ≤ 7 → |d j - j * c| ≤ c / 20)
    {a : ℕ} (ha : a = 1 ∨ a = 3 ∨ a = 5 ∨ a = 7)
    (hcond : (a : ℝ) * d (8 - a) ≤ ((8 - a : ℕ) : ℝ) * d a) :
    ∀ j, 1 ≤ j → j ≤ 7 → (8 : ℝ)⁻¹ ≤ circDist (d j * ((a : ℝ) ^ 2 / (8 * d a))) := by
  have ha1 : 1 ≤ a := by omega
  have ha7 : a ≤ 7 := by omega
  have hdev : ∀ j, 1 ≤ j → j ≤ 7 → |d j * ((a : ℝ) ^ 2 / (8 * d a)) - ((j * a : ℕ) : ℝ) / 8| ≤ 1 / 8 := by
    intro j hj1 hj7
    have := dev_bound (a := (a : ℝ)) (j := (j : ℝ)) hc (by exact_mod_cast ha1) (by exact_mod_cast ha7)
      (by positivity) (by exact_mod_cast hj7) (hd a ha1 ha7) (hd j hj1 hj7)
    push_cast; linarith [this, show (j : ℝ) * a / 8 = (j : ℝ) * a / 8 from rfl]
  have hdapos : 0 < d a := by
    have := abs_le.mp (hd a ha1 ha7)
    have : (1 : ℝ) ≤ a := by exact_mod_cast ha1
    nlinarith
  intro j hj1 hj7
  by_cases hja : j = a
  · subst hja
    refine clear_leave (j * j) (by rcases ha with rfl | rfl | rfl | rfl <;> norm_num) ?_
    push_cast; field_simp
  by_cases hjb : j = 8 - a
  · subst hjb
    refine clear_enter ((8 - a) * a) (by rcases ha with rfl | rfl | rfl | rfl <;> norm_num) (hdev _ hj1 hj7) ?_
    have h8 : (((8 - a : ℕ) : ℝ)) = 8 - (a : ℝ) := by
      rw [Nat.cast_sub (by omega)]; norm_num
    rw [h8] at hcond
    rw [show (((8 - a) * a : ℕ) : ℝ) = (8 - (a : ℝ)) * a by push_cast [Nat.cast_sub (by omega : a ≤ 8)]; ring]
    rw [show d (8 - a) * ((a : ℝ) ^ 2 / (8 * d a)) = a * (a * d (8 - a)) / (8 * d a) by ring]
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have : (0 : ℝ) ≤ a := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hcond this]
  · refine clear_mid (j * a) ?_ (hdev j hj1 hj7)
    rcases ha with rfl | rfl | rfl | rfl <;> interval_cases j <;> simp_all

/-- **The pair law.**  Every deformation of the progression with each reading within `c/20` keeps one instant of the
pair `(1, 7)` lonely, and one instant of the pair `(3, 5)`: the isolation is displaced within its pair. -/
theorem pair_law {c : ℝ} (hc : 0 < c) {d : ℕ → ℝ} (hd : ∀ j, 1 ≤ j → j ≤ 7 → |d j - j * c| ≤ c / 20)
    {a : ℕ} (ha : a = 1 ∨ a = 3) :
    ∃ b : ℕ, (b = a ∨ b = 8 - a) ∧ ∃ t : ℝ, 0 < t ∧ ∀ j, 1 ≤ j → j ≤ 7 → (8 : ℝ)⁻¹ ≤ circDist (d j * t) := by
  have hpos : ∀ b, 1 ≤ b → b ≤ 7 → 0 < d b := by
    intro b hb1 hb7
    have := abs_le.mp (hd b hb1 hb7)
    have : (1 : ℝ) ≤ b := by exact_mod_cast hb1
    nlinarith
  have hab : a ≤ 8 := by omega
  rcases le_total ((a : ℝ) * d (8 - a)) (((8 - a : ℕ) : ℝ) * d a) with h | h
  · refine ⟨a, Or.inl rfl, _, ?_, instant_lonely hc hd (by omega) h⟩
    have := hpos a (by omega) (by omega)
    have : (0 : ℝ) < a := by have : 1 ≤ a := by omega
                             exact_mod_cast this
    positivity
  · refine ⟨8 - a, Or.inr rfl, _, ?_, instant_lonely hc hd (a := 8 - a) (by omega) ?_⟩
    · have := hpos (8 - a) (by omega) (by omega)
      have : (0 : ℝ) < ((8 - a : ℕ) : ℝ) := by have : 1 ≤ 8 - a := by omega
                                               exact_mod_cast this
      positivity
    · rw [show 8 - (8 - a) = a by omega]; exact h

end LRC.ProgressionPair
