import LonelyRunner.LRC.Spec.TwoPinnerN

/-!
# The pair law for any grid

2026-09-27.  Running record: `RUNNING_LOG_order8_v1.md` E129.

The owner's reference, taken literally (E128): each reading `x i` (in units of a grid step) is a grid position `n i` plus
a deviation.  At the instant `u` (positions `x i · u` in eighths of a lap), a class `c` (an integer) places reading `i` at
`c · n i` up to its deviation.  Readings with `c · n i ≡ 2 … 6 (mod 8)` are interior: they may drift by `1`.  The reading
with `c · n i ≡ 1` sits on the leaving edge and must not fall below it; the one with `c · n i ≡ 7` on the entering edge
and must not rise above it.

* `clear_at_class`: those per-reading conditions give loneliness (at least `1/8` from the subject).
* **`grid_pair_law`**: a mirror class `c'` swaps the two edge readings `a` and `b`.  Rescale so that `a` sits exactly on
  its grid point (`ν = n a / x a`) or so that `b` does (`ν' = n b / x b`): one of `n a / x a ≤ n b / x b` or its reverse
  holds, and it is exactly the edge condition of one of the two classes.  If every reading deviates by at most `1/C`
  after either rescaling (`C` the larger class), the subject is lonely at that class's instant.  This is
  `ProgressionPairN.pair_law` for an arbitrary grid: the AP is `n i = i`.

What it does not cover, by its hypotheses: two readings on one edge (a doubled slot at an edge), a reading captured at
`0 (mod 8)`, and deviations beyond `1/C`.

Everything here is proved; no `sorry`, no `native_decide`.
-/

namespace LRC.GridPairLaw

/-- A position within `1` of an interior grid residue `2 … 6 (mod 8)` is clear. -/
theorem clear_interior {p : ℝ} {m : ℤ} (hr : 2 ≤ m % 8 ∧ m % 8 ≤ 6) (h : |p - m| ≤ 1) :
    (8 : ℝ)⁻¹ ≤ circDist (p / 8) := by
  obtain ⟨h1, h2⟩ := abs_le.mp h
  have hm : (m : ℝ) = 8 * (m / 8 : ℤ) + (m % 8 : ℤ) := by exact_mod_cast (Int.mul_ediv_add_emod m 8).symm
  have r1 : (2 : ℝ) ≤ (m % 8 : ℤ) := by exact_mod_cast hr.1
  have r2 : ((m % 8 : ℤ) : ℝ) ≤ 6 := by exact_mod_cast hr.2
  refine LRC.TwoPinner.clear_of_band (N := m / 8) ?_ ?_ <;> [skip; skip] <;>
    · rw [show p / 8 = p * 8⁻¹ by ring]; nlinarith

/-- A position at or just above the leaving edge `m ≡ 1 (mod 8)` is clear. -/
theorem clear_leaving {p : ℝ} {m : ℤ} (hr : m % 8 = 1) (h1 : (m : ℝ) ≤ p) (h2 : p ≤ m + 6) :
    (8 : ℝ)⁻¹ ≤ circDist (p / 8) := by
  have hm : (m : ℝ) = 8 * (m / 8 : ℤ) + 1 := by
    have := Int.mul_ediv_add_emod m 8; rw [hr] at this; exact_mod_cast this.symm
  refine LRC.TwoPinner.clear_of_band (N := m / 8) ?_ ?_ <;> linarith

/-- A position at or just below the entering edge `m ≡ 7 (mod 8)` is clear. -/
theorem clear_entering {p : ℝ} {m : ℤ} (hr : m % 8 = 7) (h1 : (m : ℝ) - 6 ≤ p) (h2 : p ≤ m) :
    (8 : ℝ)⁻¹ ≤ circDist (p / 8) := by
  have hm : (m : ℝ) = 8 * (m / 8 : ℤ) + 7 := by
    have := Int.mul_ediv_add_emod m 8; rw [hr] at this; exact_mod_cast this.symm
  refine LRC.TwoPinner.clear_of_band (N := m / 8) ?_ ?_ <;> linarith

/-- **The pair law for any grid.**  Readings `x i > 0` with grid positions `n i`; classes `c`, `c'` (`1 ≤ c ≤ C`,
`1 ≤ c' ≤ C`); reading `a` on the leaving edge of `c` and the entering edge of `c'`, reading `b` the reverse; every other
reading interior under both.  If every reading deviates by at most `1/C` from its grid point after rescaling by
`n a / x a` and after rescaling by `n b / x b`, the subject is lonely at `c·n a/x a` or at `c'·n b/x b` (positions in
eighths of a lap). -/
theorem grid_pair_law {ι : Type*} (S : Finset ι) (x : ι → ℝ) (n : ι → ℤ) {a b : ι} (ha : a ∈ S) (hb : b ∈ S)
    (hpos : ∀ i ∈ S, 0 < x i) (hna : 0 < n a) (hnb : 0 < n b) {c c' C : ℤ} (hc : 1 ≤ c) (hc' : 1 ≤ c') (hcC : c ≤ C)
    (hc'C : c' ≤ C)
    (ea : (c * n a) % 8 = 1) (eb : (c * n b) % 8 = 7) (ea' : (c' * n a) % 8 = 7) (eb' : (c' * n b) % 8 = 1)
    (hint : ∀ i ∈ S, i ≠ a → i ≠ b →
      (2 ≤ (c * n i) % 8 ∧ (c * n i) % 8 ≤ 6) ∧ (2 ≤ (c' * n i) % 8 ∧ (c' * n i) % 8 ≤ 6))
    (hdev : ∀ i ∈ S, |x i * (n a / x a) - n i| ≤ 1 / C ∧ |x i * (n b / x b) - n i| ≤ 1 / C) :
    ∃ u : ℝ, 0 < u ∧ ∀ i ∈ S, (8 : ℝ)⁻¹ ≤ circDist (x i * u / 8) := by
  have hxa := hpos a ha; have hxb := hpos b hb
  have hC : (1 : ℝ) ≤ C := by exact_mod_cast le_trans hc hcC
  have hcR : (1 : ℝ) ≤ c := by exact_mod_cast hc
  have hc'R : (1 : ℝ) ≤ c' := by exact_mod_cast hc'
  have hcC' : (c : ℝ) ≤ C := by exact_mod_cast hcC
  have hc'C' : (c' : ℝ) ≤ C := by exact_mod_cast hc'C
  have hnaR : (0 : ℝ) < n a := by exact_mod_cast hna
  have hnbR : (0 : ℝ) < n b := by exact_mod_cast hnb
  -- a deviation of at most 1/C, scaled by a class of size at most C, moves by at most 1
  have scale : ∀ (k : ℝ) (y m : ℝ), 1 ≤ k → k ≤ C → |y - m| ≤ 1 / C → |k * y - k * m| ≤ 1 := by
    intro k y m hk1 hkC hy
    rw [← mul_sub, abs_mul, abs_of_pos (by linarith)]
    calc k * |y - m| ≤ C * (1 / C) := by
          apply mul_le_mul hkC hy (abs_nonneg _) (by linarith)
      _ = 1 := by field_simp
  rcases le_total ((n a : ℝ) / x a) ((n b : ℝ) / x b) with hab | hab
  · -- class c at u = c · n a / x a: `a` exactly on its leaving edge
    refine ⟨c * (n a / x a), by positivity, fun i hi => ?_⟩
    have hx : x i * (c * (n a / x a)) / 8 = (c * (x i * (n a / x a))) / 8 := by ring
    rw [hx]
    by_cases hia : i = a
    · subst hia
      have e : (c : ℝ) * (x i * (n i / x i)) = ((c * n i : ℤ) : ℝ) := by push_cast; field_simp
      rw [e]; exact clear_leaving ea (le_refl _) (by linarith)
    by_cases hib : i = b
    · subst hib
      have hup : x i * (n a / x a) ≤ n i := by
        have := mul_le_mul_of_nonneg_left hab hxb.le
        rw [show x i * ((n i : ℝ) / x i) = n i by field_simp] at this; exact this
      have hlo := (abs_le.mp (hdev i hi).1).1
      refine clear_entering eb ?_ ?_ <;> push_cast
      · have := mul_le_mul_of_nonneg_left (by linarith : (n i : ℝ) - 1 / C ≤ x i * (n a / x a)) (by linarith : (0:ℝ) ≤ c)
        have hcC1 : (c : ℝ) * (1 / C) ≤ 1 := by rw [mul_one_div, div_le_one (by linarith)]; exact hcC'
        nlinarith
      · nlinarith
    · have hr := (hint i hi hia hib).1
      apply clear_interior hr
      have := scale c (x i * (n a / x a)) (n i) hcR hcC' (hdev i hi).1
      push_cast; simpa using this
  · -- class c' at u = c' · n b / x b: `b` exactly on its leaving edge
    refine ⟨c' * (n b / x b), by positivity, fun i hi => ?_⟩
    have hx : x i * (c' * (n b / x b)) / 8 = (c' * (x i * (n b / x b))) / 8 := by ring
    rw [hx]
    by_cases hib : i = b
    · subst hib
      have e : (c' : ℝ) * (x i * (n i / x i)) = ((c' * n i : ℤ) : ℝ) := by push_cast; field_simp
      rw [e]; exact clear_leaving eb' (le_refl _) (by linarith)
    by_cases hia : i = a
    · subst hia
      have hup : x i * (n b / x b) ≤ n i := by
        have := mul_le_mul_of_nonneg_left hab hxa.le
        rw [show x i * ((n i : ℝ) / x i) = n i by field_simp] at this; exact this
      have hlo := (abs_le.mp (hdev i hi).2).1
      refine clear_entering ea' ?_ ?_ <;> push_cast
      · have := mul_le_mul_of_nonneg_left (by linarith : (n i : ℝ) - 1 / C ≤ x i * (n b / x b)) (by linarith : (0:ℝ) ≤ c')
        have hcC1 : (c' : ℝ) * (1 / C) ≤ 1 := by rw [mul_one_div, div_le_one (by linarith)]; exact hc'C'
        nlinarith
      · nlinarith
    · have hr := (hint i hi hia hib).2
      apply clear_interior hr
      have := scale c' (x i * (n b / x b)) (n i) hc'R hc'C' (hdev i hi).2
      push_cast; simpa using this

end LRC.GridPairLaw
