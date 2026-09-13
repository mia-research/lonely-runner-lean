import LonelyRunner.LRC.ConstructionN.Coords

/-!
# §6.2, §6.3 and §9 at general `n`

**RING-FENCE.** General-`n` line (`LRC/ConstructionN/`). Not the artefact of the `n = 8`
paper, which cites the frozen `LRC/Construction8/`.

`docs/n8/MANUSCRIPT_v4.md` states three things in prose at `n = 8` that hold at every `n`.
This module states them once, at general `n`, with the `n = 8` numbers recovered as
instances.

* **§6.2(2)** — the overlap bound `9/7` is a **first-lap** bound. Lap `k` against lap `k'`
  gives `(n k' - 1) s < (n k + 1) s'`, and the bound loosens as the lap index grows. This
  is what defeats bounding the ratio a relay can span: there is no single ratio.
* **§6.2(4)** — the reading `s = n` blocks **both** ends of the window on its own, so the
  ends do not force two readings and there is no ratio to accumulate.
* **§6.3** — the reading `s = n` fragments the window into `n - 1` zones and `n - 2` clear
  gaps, each of width `(n-2)/n²`. At `n = 8`: seven zones, six gaps, `3/32`.
* **§9** — the local restrictions tighten as `n` grows: `(n+1)/(n-1)` strictly decreases,
  and the exclusion `2σ/(n-2)` with it. Neither reaches its limit.

**What is not claimed.** That the framework's obstructions can be defeated, or that any
route closes. §6's results are refutations of particular arguments; generalising them
generalises the refutations, not the conjecture. Part 7 is not stated or approached.
-/

namespace ConstructionN

/-- `circDist` vanishes on the integers. -/
theorem circDist_intCast (m : ℤ) : circDist (m : ℝ) = 0 := by
  unfold circDist
  simp [Int.fract_intCast]

/-! ## §6.2 — the relay bound is not a single ratio -/

/-- **§6.2(2) at general `n`.**  Lap `k` of reading `s` meets lap `k'` of `s'` exactly when
`(n k' - 1) s < (n k + 1) s'`.  At `k = k' = 1` this is `first_stretch_overlap`; at
`n = 8`, `(k,k') = (2,1)` and `(3,1)` it gives the `17/7` and `25/7` of §6.2. -/
theorem lap_overlap (n : ℕ) (hn : 0 < n) (k k' : ℕ) (s s' : ℝ) (hs : 0 < s) (hs' : 0 < s') :
    (((n : ℝ) * k' - 1) / (n * s') < ((n : ℝ) * k + 1) / (n * s))
      ↔ ((n : ℝ) * k' - 1) * s < ((n : ℝ) * k + 1) * s' := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  constructor <;> intro h <;> nlinarith

/-- The overlap bound loosens with the lap index, so no single ratio bounds a relay. -/
theorem lap_overlap_bound_grows (n : ℕ) (hn : 1 < n) (k : ℕ) :
    ((n : ℝ) * k + 1) / ((n : ℝ) - 1) < ((n : ℝ) * (k + 1) + 1) / ((n : ℝ) - 1) := by
  have hn1 : (1 : ℝ) < n := by exact_mod_cast hn
  have hd : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  rw [div_lt_div_iff_of_pos_right hd]
  nlinarith

/-- **§6.2(4) at general `n`.**  The single reading `s = n` blocks **both** ends of the
window: `n·(1/n) = 1` and `n·((n-1)/n) = n-1` are both whole laps. -/
theorem reading_n_blocks_both_ends (n : ℕ) (hn : 0 < n) :
    circDist ((n : ℝ) * (n : ℝ)⁻¹) = 0 ∧ circDist ((n : ℝ) * (1 - (n : ℝ)⁻¹)) = 0 := by
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  constructor
  · rw [mul_inv_cancel₀ hn0]
    exact_mod_cast circDist_intCast 1
  · have h1 : (n : ℝ) * (1 - (n : ℝ)⁻¹) = ((n : ℝ) - 1) := by field_simp
    have h2 : ((n : ℝ) - 1) = (((n : ℤ) - 1 : ℤ) : ℝ) := by push_cast; ring
    rw [h1, h2]
    exact circDist_intCast _

/-! ## §6.3 — the fragmentation, at general `n` -/

/-- **§6.3 at general `n`.**  The zone centres of `s = n` lying in the window are exactly
`k/n` for `k = 1, …, n-1`: `n - 1` zones, hence `n - 2` clear gaps.  At `n = 8`, seven and
six. -/
theorem reading_n_centres_in_window (n : ℕ) (hn : 0 < n) (k : ℕ) :
    ((n : ℝ)⁻¹ ≤ (k : ℝ) / n ∧ (k : ℝ) / n ≤ 1 - (n : ℝ)⁻¹) ↔ (1 ≤ k ∧ k ≤ n - 1) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [inv_eq_one_div, div_le_div_iff_of_pos_right hn0]
  constructor
  · rintro ⟨h1, h2⟩
    have hk1 : 1 ≤ k := by exact_mod_cast h1
    have hle : (k : ℝ) ≤ (n : ℝ) - 1 := by
      have h3 := h2
      rw [div_le_iff₀ hn0] at h3
      have hrw : (1 - 1 / (n : ℝ)) * (n : ℝ) = (n : ℝ) - 1 := by field_simp
      linarith [hrw ▸ h3]
    have hk2 : k ≤ n - 1 := by
      have hkn : (k : ℝ) + 1 ≤ (n : ℝ) := by linarith
      have : k + 1 ≤ n := by exact_mod_cast hkn
      omega
    exact ⟨hk1, hk2⟩
  · rintro ⟨h1, h2⟩
    have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast h1
    have hkn : k + 1 ≤ n := by omega
    have hkn' : (k : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hkn
    refine ⟨hk1, ?_⟩
    rw [div_le_iff₀ hn0]
    field_simp
    nlinarith

/-- The clear gaps `s = n` leaves have width `(n-2)/n²`. -/
theorem reading_n_gap_width (n : ℕ) (hn : 0 < n) (k : ℤ) :
    (((n : ℝ) - 1) / ((n : ℝ) * (n : ℝ)) + ((k : ℝ) + 1) / (n : ℝ))
      - (((n : ℝ) + 1) / ((n : ℝ) * (n : ℝ)) + (k : ℝ) / (n : ℝ))
      = ((n : ℝ) - 2) / ((n : ℝ) * (n : ℝ)) :=
  clear_width n hn (n : ℝ) (by exact_mod_cast hn) k

/-- At `n = 8` that is the `3/32` of §6.3. -/
theorem n8_gap_width : (((8 : ℕ) : ℝ) - 2) / (((8 : ℕ) : ℝ) * ((8 : ℕ) : ℝ)) = 3 / 32 := by
  norm_num

/-! ## §9 — the local restrictions tighten with `n` -/

/-- **§9 at general `n`.**  The first-zone overlap bound `(n+1)/(n-1)` strictly decreases in
`n`: two readings must be closer in ratio for their zones to meet at all. -/
theorem overlap_bound_decreasing (m n : ℕ) (hm : 1 < m) (hmn : m < n) :
    ((n : ℝ) + 1) / ((n : ℝ) - 1) < ((m : ℝ) + 1) / ((m : ℝ) - 1) := by
  have hm1 : (1 : ℝ) < m := by exact_mod_cast hm
  have hmn' : (m : ℝ) < n := by exact_mod_cast hmn
  rw [div_lt_div_iff₀ (by linarith) (by linarith)]
  nlinarith

/-- It never reaches `1`, at any `n`. -/
theorem overlap_bound_gt_one (n : ℕ) (hn : 1 < n) :
    1 < ((n : ℝ) + 1) / ((n : ℝ) - 1) := by
  have hn1 : (1 : ℝ) < n := by exact_mod_cast hn
  rw [lt_div_iff₀ (by linarith)]
  linarith

/-- **§9 at general `n`.**  The single-reading exclusion `2σ/(n-2)` tightens with `n`.  Its
`n > 2` hypothesis is the threshold recorded in `Coords.clear_width_pos`. -/
theorem exclusion_bound_decreasing (m n : ℕ) (hm : 2 < m) (hmn : m < n) (sig : ℝ)
    (hsig : 0 < sig) :
    2 * sig / ((n : ℝ) - 2) < 2 * sig / ((m : ℝ) - 2) := by
  have hm2 : (2 : ℝ) < m := by exact_mod_cast hm
  have hmn' : (m : ℝ) < n := by exact_mod_cast hmn
  rw [div_lt_div_iff₀ (by linarith) (by linarith)]
  nlinarith

/-- **§6.2(2)'s numbers recovered.**  At `n = 8`, laps `(2,1)` and `(3,1)` give the `17/7`
and `25/7` the manuscript quotes — from the general form, not restated. -/
theorem n8_lap_overlap_numbers (s s' : ℝ) (hs : 0 < s) (hs' : 0 < s') :
    ((7 : ℝ) / (8 * s') < (17 : ℝ) / (8 * s) ↔ 7 * s < 17 * s') ∧
    ((7 : ℝ) / (8 * s') < (25 : ℝ) / (8 * s) ↔ 7 * s < 25 * s') := by
  constructor
  · have h := lap_overlap 8 (by norm_num) 2 1 s s' hs hs'
    norm_num at h; exact h
  · have h := lap_overlap 8 (by norm_num) 3 1 s s' hs hs'
    norm_num at h; exact h

end ConstructionN
