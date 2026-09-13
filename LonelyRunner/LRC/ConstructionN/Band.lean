import LonelyRunner.LRC.ConstructionN.Integrality

/-!
# The band identity, and §7.3's settled cases at general `n`

**RING-FENCE.** General-`n` line (`LRC/ConstructionN/`). Not the artefact of the `n = 8`
paper, which cites the frozen `LRC/Construction8/`.

`docs/n8/MANUSCRIPT_v4.md` §7.3 names cases in which the procedure is **proved** to return,
from §§2-4 alone. One of them — *every runner none of whose readings lies within `1` of a
multiple of `8`* — rested on an identity stated only in prose. This module states the
identity at general `n` and derives that case from it.

## What this is and is not

These are **sufficient conditions** for the procedure to return, each with a hypothesis.
They are cases the manuscript already reports as proved, not the unconditional claim.
**Part 7 is the unconditional statement and is neither stated nor approached here**: nothing
below says the hypotheses ever hold, and a runner failing them is exactly the open case.
-/

namespace ConstructionN

/-- `circDist x` is at most the distance from `x` to any integer. -/
theorem circDist_le_abs_sub_int (x : ℝ) (k : ℤ) : circDist x ≤ |x - (k : ℝ)| := by
  unfold circDist
  have hfl := Int.floor_add_fract x
  have hf0 := Int.fract_nonneg x
  have hf1 := Int.fract_lt_one x
  set m : ℤ := k - ⌊x⌋ with hm
  have hx : x - (k : ℝ) = Int.fract x - (m : ℝ) := by
    rw [hm]; push_cast; linarith [hfl]
  rw [hx]
  rcases le_or_gt (m : ℤ) 0 with h | h
  · have hm0 : (m : ℝ) ≤ 0 := by exact_mod_cast h
    rw [abs_of_nonneg (by linarith)]
    exact le_trans (min_le_left _ _) (by linarith)
  · have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast h
    rw [abs_of_nonpos (by linarith)]
    exact le_trans (min_le_right _ _) (by linarith)

/-- And it is attained, so `circDist` IS the distance to the nearest integer. -/
theorem circDist_eq_abs_sub_some_int (x : ℝ) : ∃ k : ℤ, circDist x = |x - (k : ℝ)| := by
  unfold circDist
  have hfl := Int.floor_add_fract x
  have hf0 := Int.fract_nonneg x
  have hf1 := Int.fract_lt_one x
  rcases le_or_gt (Int.fract x) (1 - Int.fract x) with h | h
  · refine ⟨⌊x⌋, ?_⟩
    rw [min_eq_left h, abs_of_nonneg (by linarith)]
    linarith
  · refine ⟨⌊x⌋ + 1, ?_⟩
    rw [min_eq_right (le_of_lt h), abs_of_nonpos (by push_cast; linarith)]
    push_cast
    linarith

/-- **The band identity at general `n`.**  A reading `s` is clear at the first spine point
`u = 1/n` exactly when `s` is at distance at least `1` from every multiple of `n`.  At
`n = 8` this is §7.3's "no reading within 1 of a multiple of 8". -/
theorem band_identity (n : ℕ) (hn : 0 < n) (s : ℝ) :
    ((n : ℝ)⁻¹ ≤ circDist (s / n)) ↔ (∀ k : ℤ, 1 ≤ |s - (n : ℝ) * k|) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  constructor
  · intro h k
    have h1 := circDist_le_abs_sub_int (s / n) k
    have h2 : |s / (n : ℝ) - (k : ℝ)| = |s - (n : ℝ) * k| / n := by
      rw [show s / (n : ℝ) - (k : ℝ) = (s - (n : ℝ) * k) / n by field_simp, abs_div,
        abs_of_pos hn0]
    rw [h2, le_div_iff₀ hn0] at h1
    have hinv : (n : ℝ)⁻¹ * n = 1 := by field_simp
    nlinarith [h, h1]
  · intro h
    obtain ⟨k, hk⟩ := circDist_eq_abs_sub_some_int (s / n)
    rw [hk]
    have h2 : |s / (n : ℝ) - (k : ℝ)| = |s - (n : ℝ) * k| / n := by
      rw [show s / (n : ℝ) - (k : ℝ) = (s - (n : ℝ) * k) / n by field_simp, abs_div,
        abs_of_pos hn0]
    rw [h2, le_div_iff₀ hn0]
    have hk1 := h k
    have hinv : (n : ℝ)⁻¹ * n = 1 := by field_simp
    nlinarith [hk1, hinv]

/-- For an **integer** reading the band condition is exactly non-divisibility, which is how
§7.3's grid case reduces to the spine test already in `LemmaPass`. -/
theorem band_int (n : ℕ) (hn : 0 < n) (c : ℤ) :
    (∀ k : ℤ, 1 ≤ |(c : ℝ) - (n : ℝ) * k|) ↔ ¬ ((n : ℤ) ∣ c) := by
  constructor
  · rintro h ⟨m, rfl⟩
    have hm := h m
    rw [show ((((n : ℤ) * m : ℤ)) : ℝ) = (n : ℝ) * (m : ℝ) by push_cast; ring] at hm
    norm_num at hm
  · intro h k
    have hne : c - (n : ℤ) * k ≠ 0 := by
      intro hc
      exact h ⟨k, by omega⟩
    have hge : (1 : ℤ) ≤ |c - (n : ℤ) * k| := Int.one_le_abs hne
    have hcast : (((|c - (n : ℤ) * k| : ℤ)) : ℝ) = |(c : ℝ) - (n : ℝ) * k| := by
      rw [Int.cast_abs]; push_cast; ring_nf
    have : ((1 : ℤ) : ℝ) ≤ (((|c - (n : ℤ) * k| : ℤ)) : ℝ) := by exact_mod_cast hge
    rw [hcast] at this
    exact_mod_cast this

/-- **§7.3's first settled case at general `n`.**  If no reading lies within `1` of a
multiple of `n`, the first spine point `u = 1/n` clears every one of them, so the procedure
returns there.  At `n = 8` this is the manuscript's "no reading within 1 of a multiple of 8". -/
theorem returns_at_first_spine {ι : Type*} (n : ℕ) (hn : 0 < n) (s : ι → ℝ)
    (h : ∀ j, ∀ k : ℤ, 1 ≤ |s j - (n : ℝ) * k|) :
    ∀ j, (n : ℝ)⁻¹ ≤ circDist (s j * (n : ℝ)⁻¹) := by
  intro j
  have hrw : s j * (n : ℝ)⁻¹ = s j / n := by ring
  rw [hrw]
  exact (band_identity n hn (s j)).mpr (h j)

/-- And `u = 1/n` lies in the window, so it is a point the procedure may return. -/
theorem first_spine_in_window (n : ℕ) (hn : 1 < n) :
    (n : ℝ)⁻¹ ≤ (n : ℝ)⁻¹ ∧ (n : ℝ)⁻¹ ≤ 1 - (n : ℝ)⁻¹ := by
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hpos : (0 : ℝ) < n := by linarith
  have hmul : (n : ℝ)⁻¹ * n = 1 := by field_simp
  have hinv : (0 : ℝ) < (n : ℝ)⁻¹ := by positivity
  refine ⟨le_refl _, ?_⟩
  nlinarith [hmul, hinv, hn2]

/-! ## The tightest observed family -/
/-- The near-AP family `(1, …, n-1, n+1)`: its displaced top runner has differences
`2, 3, …, n`, so `d_min = 2` and its readings are `k/2` for `k = 3, …, n`.  Every such
reading is at distance at least `1` from every multiple of `n`. -/
theorem near_ap_reading_band (n : ℕ) (hn : 1 < n) (k : ℕ) (hk3 : 3 ≤ k) (hkn : k ≤ n)
    (m : ℤ) : 1 ≤ |(k : ℝ) / 2 - (n : ℝ) * m| := by
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hk3' : (3 : ℝ) ≤ k := by exact_mod_cast hk3
  have hkn' : (k : ℝ) ≤ n := by exact_mod_cast hkn
  rcases le_or_gt m 0 with hm | hm
  · have hm0 : (m : ℝ) ≤ 0 := by exact_mod_cast hm
    have : (0 : ℝ) ≤ (n : ℝ) * (-m) := by nlinarith
    rw [abs_of_nonneg (by nlinarith)]
    nlinarith
  · have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    rw [abs_of_nonpos (by nlinarith)]
    nlinarith

/-- **The tightest observed family still returns, at every `n`.**  The displaced top runner
of `(1, …, n-1, n+1)` is clear at the first spine point `u = 1/n`.

Empirically this runner's clear set is a **single instant** — see
`docs/nN/TIGHTEST_v1.md`.  That it is nonempty at every `n` is proved here; that it is a
single point is not, and is not claimed. -/
theorem near_ap_top_returns (n : ℕ) (hn : 1 < n) (k : ℕ) (hk3 : 3 ≤ k) (hkn : k ≤ n) :
    (n : ℝ)⁻¹ ≤ circDist (((k : ℝ) / 2) * (n : ℝ)⁻¹) := by
  have hn0 : 0 < n := by omega
  have hrw : ((k : ℝ) / 2) * (n : ℝ)⁻¹ = ((k : ℝ) / 2) / n := by ring
  rw [hrw]
  exact (band_identity n hn0 _).mpr (near_ap_reading_band n hn k hk3 hkn)

end ConstructionN
