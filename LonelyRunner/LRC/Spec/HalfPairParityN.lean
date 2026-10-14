import LonelyRunner.LRC.Defs

/-!
# The parity law of a half-integer walker at a flank's openings

2026-10-05 (running log E395).  At a flank `e` the openings are `u = 8k + 1`.  A walker `x` reads `u·x/e` laps of the
circle at the opening; with ratio `x/e = A + 1/2` this is `(8k+1)(2A+1)/16`.  The walker is in the way iff the
distance from that reading to the nearest integer is below `1/8`.

* `parity_law`: for whole `A` and `k`, the walker with ratio `A + 1/2` is in the way at the opening `8k+1` iff `k` is
  even and `A mod 8 ∈ {0, 7}`, or `k` is odd and `A mod 8 ∈ {3, 4}`.

So an exact half-pair covers both parities of the openings only with a walker at `A ≡ 0 or 7` and one at
`A ≡ 3 or 4 (mod 8)`.  This is the exact structure of the record's §6.11, stated for every `A` and `k`.

* `circDist_lt_iff_of_mem`: for `-7/8 ≤ y < 1/8`, `circDist y < 1/8 ↔ -1/8 < y`.
* `near_sharer_blocked_iff`: a walker with ratio `8a + 1 + ε`, `ε < 0`, at the opening `u` with `0 < u ≤ 8/|ε|` is in
  the way iff `u < 2/|ε|` (the near-sharer's persistence, exact).

Everything here is proved; no `sorry`, no `native_decide`.
-/

namespace LRC.HalfPairParity

/-- The distance to the nearest integer of `m / 16` for a natural `m` is below `1/8` iff `m mod 16` is `0`, `1` or `15`. -/
theorem circDist_div16_lt (m : ℕ) :
    circDist ((m : ℝ) / 16) < 1 / 8 ↔ (m % 16 = 0 ∨ m % 16 = 1 ∨ m % 16 = 15) := by
  have hq : (m : ℝ) / 16 = (((m / 16 : ℕ) : ℤ) : ℝ) + ((m % 16 : ℕ) : ℝ) / 16 := by
    have h : (m : ℝ) = 16 * ((m / 16 : ℕ) : ℝ) + ((m % 16 : ℕ) : ℝ) := by
      exact_mod_cast (Nat.div_add_mod m 16).symm
    rw [Int.cast_natCast, h]; ring
  have hr : (m % 16 : ℕ) < 16 := Nat.mod_lt _ (by norm_num)
  have hrR : ((m % 16 : ℕ) : ℝ) < 16 := by exact_mod_cast hr
  have hr0 : (0 : ℝ) ≤ ((m % 16 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hfract : Int.fract ((m : ℝ) / 16) = ((m % 16 : ℕ) : ℝ) / 16 := by
    rw [hq, Int.fract_intCast_add]
    exact Int.fract_eq_self.mpr ⟨by positivity, by linarith⟩
  unfold circDist
  rw [hfract]
  generalize hrr : m % 16 = r at hr hrR hr0 ⊢
  rw [min_lt_iff]
  constructor
  · rintro (h | h)
    · have h2 : (r : ℝ) < 2 := by linarith
      have h3 : r < 2 := by exact_mod_cast h2
      omega
    · have h2 : (14 : ℝ) < r := by linarith
      have h3 : 14 < r := by exact_mod_cast h2
      omega
  · rintro (h | h | h)
    · left; subst h; norm_num
    · left; subst h; norm_num
    · right; subst h; norm_num

/-- **The parity law.**  A walker with ratio `A + 1/2` at the flank's opening `u = 8k + 1` is in the way (its reading
is within `1/8` of an integer) iff `k` is even and `A mod 8 ∈ {0, 7}`, or `k` is odd and `A mod 8 ∈ {3, 4}`. -/
theorem parity_law (A k : ℕ) :
    circDist ((((8 * k + 1 : ℕ) : ℝ) * (((2 * A + 1 : ℕ) : ℝ) / 2)) / 8) < 1 / 8 ↔
      ((k % 2 = 0 ∧ (A % 8 = 0 ∨ A % 8 = 7)) ∨ (k % 2 = 1 ∧ (A % 8 = 3 ∨ A % 8 = 4))) := by
  have h : ((((8 * k + 1 : ℕ) : ℝ) * (((2 * A + 1 : ℕ) : ℝ) / 2)) / 8)
      = (((8 * k + 1) * (2 * A + 1) : ℕ) : ℝ) / 16 := by
    push_cast; ring
  rw [h, circDist_div16_lt]
  have e : (8 * k + 1) * (2 * A + 1) = 16 * (k * A) + 8 * k + 2 * A + 1 := by ring
  rw [e]
  omega

/-- On `[-7/8, 1/8)` the distance to the nearest integer is below `1/8` exactly above `-1/8`. -/
theorem circDist_lt_iff_of_mem {y : ℝ} (h1 : -7 / 8 ≤ y) (h2 : y < 1 / 8) :
    circDist y < 1 / 8 ↔ -1 / 8 < y := by
  unfold circDist
  rcases le_or_gt 0 y with h0 | h0
  · have hf : Int.fract y = y := Int.fract_eq_self.mpr ⟨h0, by linarith⟩
    rw [hf, min_lt_iff]
    constructor
    · intro _; linarith
    · intro _; left; exact h2
  · have hf : Int.fract y = y + 1 := by
      have := Int.fract_add_one y
      have h3 : Int.fract (y + 1) = y + 1 := Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
      linarith [Int.fract_add_one y]
    rw [hf, min_lt_iff]
    constructor
    · rintro (h | h)
      · linarith
      · linarith
    · intro h; right; linarith

/-- **Persistence of a near-sharer, exact.**  A walker with ratio `8a + 1 + ε`, `ε < 0`, at the flank's opening `u`
reads `a + (1 + ε u)/8` laps; for `0 < u ≤ 8/|ε|` it is in the way iff `u < 2/|ε|`. -/
theorem near_sharer_blocked_iff (a : ℤ) {ε u : ℝ} (hε : ε < 0) (hu : 0 < u) (hu8 : u ≤ 8 / (-ε)) :
    circDist (a + (1 + ε * u) / 8) < 1 / 8 ↔ u < 2 / (-ε) := by
  have hy : circDist (a + (1 + ε * u) / 8) = circDist ((1 + ε * u) / 8) := by
    unfold circDist
    rw [add_comm, Int.fract_add_intCast]
  rw [hy]
  have hne : 0 < -ε := by linarith
  have hu8' : -ε * u ≤ 8 := by
    have := (le_div_iff₀ hne).mp hu8
    linarith
  rw [circDist_lt_iff_of_mem (by nlinarith) (by nlinarith)]
  constructor
  · intro h
    rw [lt_div_iff₀ hne]
    nlinarith
  · intro h
    rw [lt_div_iff₀ hne] at h
    nlinarith

end LRC.HalfPairParity
