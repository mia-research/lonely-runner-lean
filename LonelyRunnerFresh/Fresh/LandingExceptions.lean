import Mathlib
import Fresh.Framework

/-!
# The landing opener: what decides it, and the exceptions (Task AN)

Written 2026-10-09.  Imports Mathlib and `Fresh.Framework` only.  Nothing is imported from the existing `LonelyRunner`
repo or from another `Fresh` module; every proof below was written here.  The data that suggested these statements is in
`experiments/n8/landing_exceptions_v1.py` and `.out` (exact integer and `Fraction` arithmetic, three full populations of
integer disparity sets, `N = 14, 18, 22`, plus counts to `N = 30`).

Provenance (existing declarations whose ideas were read, not copied; every argument was re-derived for `distInt` and
the threshold `1/8` of `Fresh.Framework`).
* `distInt_le`, `lt_distInt_iff`, `le_distInt_iff`, `distInt_add_int`, `distInt_neg`: elementary circle-distance facts
  (compare `MomentIterationN` and `GrandReturnN` in the existing repo).
* `nextOpening_of_near`, `inWay_until`, `step_blocks`, `chain_blocks`: `inWay_until_opening` and the "every step is at
  most every lonely instant" argument of `Cascade/Iteration.lean`.  The new content is the NAMED blocker: every instant
  in `[t_n, t_{n+1})` is blocked by the setter of move `n`, with its lap.
* `inWay_opening_iff`, `inWay_opening_iff_mod`: the certificate of v9 Theorem 10 (`Spec/Certificate`-style) stated for a
  single runner and a single opening.
* `landing_le_half`: the mirror symmetry of `GrandReturnN.lonely_mirror` plus the period 1 of integer disparities.

What is proved here (all for exact reals and integers, no float, no cap, no move count, no density).
1. `inWay_opening_iff` / `inWay_opening_iff_mod`: runner `z` is in the way at the opening time `n/(8x)` of runner `x`
   iff `|z n - 8 j x| < x` for an integer `j`, iff `z n mod 8x` lies in `[0,x)` or `(7x,8x)`.  This is the exact
   congruence that "z blocks the opening".
2. `chain_blocks_opening`: along ANY cascade sequence, every opening time in `[seq 0, seq N)` is blocked by the setter
   of the move whose interval contains it.  So each earlier opening has a named blocker and the exact inequality of 1.
3. `clear_ge_bound`, `clear_lap0_iff`, `landing_lap0_iff`, `landing_gt_of_forbidden`, `lap0_opener_is_min`: the landing
   is at lap 0 of runner `m` iff no disparity lies in a forbidden zone `|d - 8 j m| < m`; if one does, the landing is
   strictly later; a lap-0 opener of the landing is the smallest disparity.
4. `landing_le_half`, `opener_lap_bound`: integer disparities, a landing `t` satisfies `t <= 1/2`, hence its opener
   `(x,k)` has `8k + 1 <= 4x`.  This bounds the admissible laps for each `x` (the rare classes are finite lists).
5. `openers_at_instant`, `cofactor_class`: at `t = p/(8c)` (lowest terms, `p` odd) the runners standing exactly `1/8`
   past a lap are exactly `d = m c` with `m = p (mod 8)`; and `g * p = 8k + 1` forces `p = g (mod 8)`.
6. `neighbour_in_way`, `landing_no_predecessor`: the sweep-down rule, and its consequence for a landing with `R* < 2`.

Counting tool: none is used.  No statement has the shape of a coverage, cap, move budget or density claim.
-/

open Classical

namespace Fresh

namespace LandingExceptions

/-! ## Circle-distance toolkit -/

/-- `distInt x` is at most the distance from `x` to any integer. -/
theorem distInt_le (x : ℝ) (z : ℤ) : distInt x ≤ |x - z| := round_le x z

#print axioms distInt_le

theorem lt_distInt_iff (x c : ℝ) : distInt x < c ↔ ∃ z : ℤ, |x - z| < c :=
  ⟨fun h => ⟨round x, h⟩, fun ⟨z, hz⟩ => lt_of_le_of_lt (distInt_le x z) hz⟩

#print axioms lt_distInt_iff

theorem le_distInt_iff (x c : ℝ) : c ≤ distInt x ↔ ∀ z : ℤ, c ≤ |x - z| := by
  constructor
  · intro h z; exact le_trans h (distInt_le x z)
  · intro h; exact h (round x)

#print axioms le_distInt_iff

theorem distInt_add_int (x : ℝ) (z : ℤ) : distInt (x + z) = distInt x := by
  unfold distInt
  rw [round_add_intCast]
  push_cast
  ring_nf

#print axioms distInt_add_int

theorem distInt_neg (x : ℝ) : distInt (-x) = distInt x := by
  apply le_antisymm
  · have h := distInt_le (-x) (-(round x))
    have e : |-x - ((-(round x) : ℤ) : ℝ)| = |x - (round x : ℝ)| := by
      push_cast
      rw [show -x - -(round x : ℝ) = -(x - round x) by ring, abs_neg]
    rw [e] at h
    exact h
  · have h := distInt_le x (-(round (-x)))
    have e : |x - ((-(round (-x)) : ℤ) : ℝ)| = |-x - (round (-x) : ℝ)| := by
      push_cast
      rw [show x - -(round (-x) : ℝ) = -(-x - round (-x)) by ring, abs_neg]
    rw [e] at h
    exact h

#print axioms distInt_neg

/-- In the way means: within `1/8` of some whole lap. -/
theorem inWay_iff_near (d t : ℝ) : InWay d t ↔ ∃ z : ℤ, |d * t - z| < 1 / 8 :=
  lt_distInt_iff _ _

#print axioms inWay_iff_near

/-! ## 1. The exact blocking congruence -/

/-- **Blocking congruence.**  For integers `z`, `n` and `x > 0`: runner `z` is in the way at the opening time
`n/(8x)` iff `|z n - 8 j x| < x` for some integer `j` (the lap of `z`). -/
theorem inWay_opening_iff (z n x : ℤ) (hx : 0 < x) :
    InWay (z : ℝ) ((n : ℝ) / (8 * x)) ↔ ∃ j : ℤ, |z * n - 8 * j * x| < x := by
  have hx' : (0 : ℝ) < x := by exact_mod_cast hx
  have h8 : (0 : ℝ) < 8 * x := by positivity
  have key : ∀ j : ℤ, (z : ℝ) * ((n : ℝ) / (8 * x)) - j = ((z : ℝ) * n - 8 * j * x) / (8 * x) := by
    intro j; field_simp
  rw [inWay_iff_near]
  constructor
  · rintro ⟨j, hj⟩
    refine ⟨j, ?_⟩
    rw [key, abs_div, abs_of_pos h8, div_lt_iff₀ h8] at hj
    have : |(z : ℝ) * n - 8 * j * x| < x := by linarith
    exact_mod_cast this
  · rintro ⟨j, hj⟩
    refine ⟨j, ?_⟩
    rw [key, abs_div, abs_of_pos h8, div_lt_iff₀ h8]
    have : |(z : ℝ) * n - 8 * j * x| < x := by exact_mod_cast hj
    linarith

#print axioms inWay_opening_iff

/-- The same, as a congruence: `z n mod 8x` lies in `[0, x)` or in `(7x, 8x)`. -/
theorem inWay_opening_iff_mod (z n x : ℤ) (hx : 0 < x) :
    InWay (z : ℝ) ((n : ℝ) / (8 * x)) ↔ (z * n) % (8 * x) < x ∨ 7 * x < (z * n) % (8 * x) := by
  rw [inWay_opening_iff z n x hx]
  have h8 : 0 < 8 * x := by omega
  have hr0 : 0 ≤ (z * n) % (8 * x) := Int.emod_nonneg _ h8.ne'
  have hr1 : (z * n) % (8 * x) < 8 * x := Int.emod_lt_of_pos _ h8
  have hq : z * n = 8 * x * ((z * n) / (8 * x)) + (z * n) % (8 * x) := (Int.mul_ediv_add_emod _ _).symm
  set q := (z * n) / (8 * x) with hqdef
  set r := (z * n) % (8 * x) with hrdef
  constructor
  · rintro ⟨j, hj⟩
    have hj' : |r - 8 * (j - q) * x| < x := by
      have : z * n - 8 * j * x = r - 8 * (j - q) * x := by rw [hq]; ring
      rw [← this]; exact hj
    rw [abs_lt] at hj'
    obtain ⟨hl, hu⟩ := hj'
    by_contra hcon
    push Not at hcon
    obtain ⟨h1, h2⟩ := hcon
    -- s = j - q: show s = 0 gives r < x, s = 1 gives r > 7x, other s impossible
    rcases lt_trichotomy (j - q) 0 with hs | hs | hs
    · have : 8 * (j - q) * x ≤ -8 * x := by nlinarith
      linarith
    · rw [hs] at hu; linarith
    · rcases lt_or_ge (j - q) 2 with hs2 | hs2
      · have : j - q = 1 := by omega
        rw [this] at hl; linarith
      · have : 16 * x ≤ 8 * (j - q) * x := by nlinarith
        linarith
  · intro h
    rcases h with h | h
    · refine ⟨q, ?_⟩
      have : z * n - 8 * q * x = r := by rw [hq]; ring
      rw [this, abs_of_nonneg hr0]; exact h
    · refine ⟨q + 1, ?_⟩
      have : z * n - 8 * (q + 1) * x = r - 8 * x := by rw [hq]; ring
      rw [this, abs_of_neg (by linarith)]; linarith

#print axioms inWay_opening_iff_mod

/-! ## 2. The cascade: every instant before the landing is blocked, by a named runner -/

/-- If `d t` is within `1/8` of the lap `k`, the next opening is `(k + 1/8)/d`. -/
theorem nextOpening_of_near {d t : ℝ} {k : ℤ} (hk : |d * t - k| < 1 / 8) :
    nextOpening d t = ((k : ℝ) + 1 / 8) / d := by
  unfold nextOpening
  have : ⌈d * t - 1 / 8⌉ = k := by
    rw [Int.ceil_eq_iff]
    rw [abs_lt] at hk
    constructor <;> linarith [hk.1, hk.2]
  rw [this]

#print axioms nextOpening_of_near

/-- Between `t` and the next opening, the runner stays within `1/8` of the same lap `k`. -/
theorem inWay_until {d t s : ℝ} (hd : 0 < d) {k : ℤ} (hk : |d * t - k| < 1 / 8) (hts : t ≤ s)
    (hs : s < ((k : ℝ) + 1 / 8) / d) : |d * s - k| < 1 / 8 := by
  rw [abs_lt] at hk ⊢
  rw [lt_div_iff₀ hd] at hs
  constructor
  · nlinarith [hk.1]
  · nlinarith

#print axioms inWay_until

/-- One cascade move either fixes `t`, or has a named setter `z` at lap `k`: `z` is in the way at `t`, the new
instant is `z`'s opening `(k + 1/8)/z`, and `z` stays within `1/8` of lap `k` on all of `[t, t')`. -/
theorem step_blocks {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d) {t t' : ℝ} (hm : IsMove ds t t') :
    t' = t ∨ ∃ z ∈ ds, ∃ k : ℤ, |z * t - k| < 1 / 8 ∧ t' = ((k : ℝ) + 1 / 8) / z ∧
      ∀ s, t ≤ s → s < t' → |z * s - k| < 1 / 8 := by
  rcases hm with ⟨_, rfl⟩ | ⟨z, hz, hw, ht', _⟩
  · exact Or.inl rfl
  · right
    obtain ⟨k, hk⟩ := (inWay_iff_near z t).mp hw
    have hn := nextOpening_of_near hk
    refine ⟨z, hz, k, hk, ht'.trans hn, ?_⟩
    intro s hts hs
    rw [ht', hn] at hs
    exact inWay_until (hpos z hz) hk hts hs

#print axioms step_blocks

/-- **Chain blocking.**  Along a cascade sequence, every `s` in `[seq 0, seq N)` lies in some `[seq n, seq (n+1))`
and is blocked there by a runner `z` of the disparity set (the setter of move `n`) at a named integer lap `k`. -/
theorem chain_blocks {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d) {seq : ℕ → ℝ}
    (hmv : ∀ n, IsMove ds (seq n) (seq (n + 1))) {s : ℝ} :
    ∀ N : ℕ, seq 0 ≤ s → s < seq N →
      ∃ n < N, ∃ z ∈ ds, ∃ k : ℤ, seq n ≤ s ∧ s < seq (n + 1) ∧ |z * s - k| < 1 / 8 := by
  intro N
  induction N with
  | zero => intro h0 hN; exact absurd (lt_of_le_of_lt h0 hN) (lt_irrefl _)
  | succ N ih =>
    intro h0 hN
    by_cases h : s < seq N
    · obtain ⟨n, hn, z, hz, k, h1, h2, h3⟩ := ih h0 h
      exact ⟨n, Nat.lt_succ_of_lt hn, z, hz, k, h1, h2, h3⟩
    · push Not at h
      rcases step_blocks hpos (hmv N) with heq | ⟨z, hz, k, _, _, hblk⟩
      · rw [heq] at hN; exact absurd (lt_of_le_of_lt h hN) (lt_irrefl _)
      · exact ⟨N, Nat.lt_succ_self N, z, hz, k, h, hN, hblk s h hN⟩

#print axioms chain_blocks

/-- **Chain blocking, in the form the congruence uses.**  For integer disparities and an opening time `n/(8x)`
inside `[seq 0, seq N)`, some disparity `z` of the set satisfies `|z n - 8 j x| < x` for an integer `j`. -/
theorem chain_blocks_opening {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d) (hint : ∀ d ∈ ds, ∃ m : ℤ, d = m)
    {seq : ℕ → ℝ} (hmv : ∀ n, IsMove ds (seq n) (seq (n + 1))) (N : ℕ) (n x : ℤ) (hx : 0 < x)
    (h0 : seq 0 ≤ (n : ℝ) / (8 * x)) (hN : (n : ℝ) / (8 * x) < seq N) :
    ∃ i < N, ∃ z : ℤ, (z : ℝ) ∈ ds ∧ seq i ≤ (n : ℝ) / (8 * x) ∧ (n : ℝ) / (8 * x) < seq (i + 1) ∧
      ∃ j : ℤ, |z * n - 8 * j * x| < x := by
  obtain ⟨i, hi, z, hz, k, h1, h2, h3⟩ := chain_blocks hpos hmv N h0 hN
  obtain ⟨zi, hzi⟩ := hint z hz
  refine ⟨i, hi, zi, hzi ▸ hz, h1, h2, ?_⟩
  have hw : InWay (zi : ℝ) ((n : ℝ) / (8 * x)) := by
    rw [inWay_iff_near]; exact ⟨k, by rw [← hzi]; exact h3⟩
  exact (inWay_opening_iff zi n x hx).mp hw

#print axioms chain_blocks_opening

/-! ## 3. The landing, lap 0, and the forbidden zones of `d_min` -/

/-- Every disparity of `ds` is at circle distance at least `1/8` at `t`. -/
-- STANDING: DEFINITION
def ClearAt (ds : Finset ℝ) (t : ℝ) : Prop := ∀ d ∈ ds, (1 / 8 : ℝ) ≤ distInt (d * t)

/-- `t` is the landing: the least positive clear instant. -/
-- STANDING: DEFINITION
def IsLanding (ds : Finset ℝ) (t : ℝ) : Prop := 0 < t ∧ ClearAt ds t ∧ ∀ s, 0 < s → ClearAt ds s → t ≤ s

/-- v9 Theorem 7: a clear instant of a set containing `m > 0` satisfies `s >= 1/(8m)`. -/
theorem clear_ge_bound {ds : Finset ℝ} {m s : ℝ} (hm : m ∈ ds) (hmpos : 0 < m) (hs : 0 < s)
    (hc : ClearAt ds s) : 1 / (8 * m) ≤ s := by
  by_contra h
  push Not at h
  have hms : m * s < 1 / 8 := by
    have h' : s * (8 * m) < 1 := by rwa [lt_div_iff₀ (by positivity)] at h
    nlinarith
  have h1 := distInt_le (m * s) 0
  simp only [Int.cast_zero, sub_zero] at h1
  rw [abs_of_pos (by positivity)] at h1
  have := hc m hm
  linarith

#print axioms clear_ge_bound

/-- **Lap-0 criterion.**  The instant `1/(8m)` is clear iff no disparity lies in a forbidden zone of `m`:
`|d - 8 j m| >= m` for every `d` and every integer `j`. -/
theorem clear_lap0_iff {ds : Finset ℝ} {m : ℝ} (hm : 0 < m) :
    ClearAt ds (1 / (8 * m)) ↔ ∀ d ∈ ds, ∀ j : ℤ, m ≤ |d - 8 * j * m| := by
  have h8 : (0 : ℝ) < 8 * m := by positivity
  have key : ∀ (d : ℝ) (j : ℤ), d * (1 / (8 * m)) - j = (d - 8 * j * m) / (8 * m) := by
    intro d j; field_simp
  unfold ClearAt
  constructor
  · intro h d hd j
    have := (le_distInt_iff _ _).mp (h d hd) j
    rw [key, abs_div, abs_of_pos h8, le_div_iff₀ h8] at this
    linarith
  · intro h d hd
    rw [le_distInt_iff]
    intro j
    rw [key, abs_div, abs_of_pos h8, le_div_iff₀ h8]
    have := h d hd j
    linarith

#print axioms clear_lap0_iff

/-- A clear `1/(8m)` is the landing, for any `m` in the set (no minimality hypothesis is needed: a smaller
disparity would force a larger bound). -/
theorem landing_lap0_iff {ds : Finset ℝ} {m : ℝ} (hm : m ∈ ds) (hmpos : 0 < m) :
    IsLanding ds (1 / (8 * m)) ↔ ClearAt ds (1 / (8 * m)) := by
  constructor
  · exact fun h => h.2.1
  · intro h
    exact ⟨by positivity, h, fun s hs hc => clear_ge_bound hm hmpos hs hc⟩

#print axioms landing_lap0_iff

/-- **Not at lap 0.**  If some disparity lies in a forbidden zone of `m` (`|d - 8 j m| < m`), every clear instant is
strictly later than `1/(8m)`; in particular the landing is. -/
theorem landing_gt_of_forbidden {ds : Finset ℝ} {m t : ℝ} (hm : m ∈ ds) (hmpos : 0 < m)
    (hf : ∃ d ∈ ds, ∃ j : ℤ, |d - 8 * j * m| < m) (ht : 0 < t) (hc : ClearAt ds t) :
    1 / (8 * m) < t := by
  rcases (clear_ge_bound hm hmpos ht hc).lt_or_eq with h | h
  · exact h
  · exfalso
    rw [← h] at hc
    obtain ⟨d, hd, j, hj⟩ := hf
    have := (clear_lap0_iff hmpos).mp hc d hd j
    linarith

#print axioms landing_gt_of_forbidden

/-- A lap-0 opener of the landing is the smallest disparity. -/
theorem lap0_opener_is_min {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d) {t x : ℝ} (hl : IsLanding ds t)
    (hx : x ∈ ds) (hxt : x * t = 1 / 8) : ∀ d ∈ ds, x ≤ d := by
  intro d hd
  have h1 := clear_ge_bound hd (hpos d hd) hl.1 hl.2.1
  have hxpos := hpos x hx
  have ht : t = 1 / (8 * x) := by field_simp; linarith
  rw [ht] at h1
  have hdpos := hpos d hd
  rw [div_le_div_iff₀ (by positivity) (by positivity)] at h1
  nlinarith

#print axioms lap0_opener_is_min

/-! ## 4. The landing is at most `1/2` for integer disparities -/

theorem landing_nonempty {ds : Finset ℝ} {t : ℝ} (hl : IsLanding ds t) : ds.Nonempty := by
  by_contra h
  rw [Finset.not_nonempty_iff_eq_empty] at h
  have hc : ClearAt ds (t / 2) := by intro d hd; simp [h] at hd
  have := hl.2.2 (t / 2) (by linarith [hl.1]) hc
  linarith [hl.1]

#print axioms landing_nonempty

/-- **Landing at most one half.**  For integer disparities the clear set has period 1 and is symmetric under
`t ↦ 1 - t`, so the least clear instant is at most `1/2`. -/
theorem landing_le_half {ds : Finset ℝ} (hint : ∀ d ∈ ds, ∃ m : ℤ, d = m) {t : ℝ} (hl : IsLanding ds t) :
    t ≤ 1 / 2 := by
  obtain ⟨d0, hd0⟩ := landing_nonempty hl
  set u := Int.fract t with hu
  have hper : ∀ m : ℤ, distInt ((m : ℝ) * u) = distInt ((m : ℝ) * t) := by
    intro m
    have : (m : ℝ) * t = (m : ℝ) * u + ((m * ⌊t⌋ : ℤ) : ℝ) := by
      rw [hu, Int.fract]; push_cast; ring
    rw [this, distInt_add_int]
  have hclu : ClearAt ds u := by
    intro d hd
    obtain ⟨m, rfl⟩ := hint d hd
    rw [hper m]; exact hl.2.1 _ hd
  have hu0 : 0 < u := by
    rcases (Int.fract_nonneg t).lt_or_eq with h | h
    · exact h
    · exfalso
      obtain ⟨m, hm⟩ := hint d0 hd0
      have h1 := hclu d0 hd0
      have hu0' : u = 0 := by rw [hu]; exact h.symm
      rw [hm, hu0'] at h1
      simp only [mul_zero] at h1
      have : distInt 0 = 0 := by simp [distInt]
      rw [this] at h1; norm_num at h1
  have hu1 : u < 1 := Int.fract_lt_one t
  have hcl1 : ClearAt ds (1 - u) := by
    intro d hd
    obtain ⟨m, rfl⟩ := hint d hd
    have : (m : ℝ) * (1 - u) = -((m : ℝ) * u) + (m : ℤ) := by ring
    rw [this, distInt_add_int, distInt_neg]
    exact hclu _ hd
  have h1 := hl.2.2 u hu0 hclu
  have h2 := hl.2.2 (1 - u) (by linarith) hcl1
  linarith

#print axioms landing_le_half

/-- **Lap bound.**  An opener `(x, k)` of an integer landing satisfies `8k + 1 <= 4x`. -/
theorem opener_lap_bound {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d) (hint : ∀ d ∈ ds, ∃ m : ℤ, d = m) {t : ℝ}
    (hl : IsLanding ds t) {x : ℤ} (hx : (x : ℝ) ∈ ds) {k : ℤ} (hxt : (x : ℝ) * t = k + 1 / 8) :
    8 * k + 1 ≤ 4 * x := by
  have h := landing_le_half hint hl
  have hxpos : (0 : ℝ) < x := hpos _ hx
  have : (8 * k + 1 : ℝ) ≤ 4 * x := by nlinarith
  exact_mod_cast this

#print axioms opener_lap_bound

/-! ## 5. The openers at an instant `p/(8c)`; the unit class of `p` -/

/-- Units mod 8 are their own inverses, in the form used: for odd `p`, `8 | m p - 1` iff `8 | m - p`. -/
theorem unit_inv_class (m p : ℤ) (hp : Odd p) : (8 : ℤ) ∣ m * p - 1 ↔ (8 : ℤ) ∣ m - p := by
  have hp8 : p % 8 = 1 ∨ p % 8 = 3 ∨ p % 8 = 5 ∨ p % 8 = 7 := by
    obtain ⟨a, ha⟩ := hp; omega
  have hz : ∀ a b : ZMod 8, (a = 1 ∨ a = 3 ∨ a = 5 ∨ a = 7) → (b * a - 1 = 0 ↔ b - a = 0) := by decide
  have e : ∀ x : ℤ, (8 : ℤ) ∣ x ↔ ((x : ZMod 8) = 0) := fun x => (ZMod.intCast_zmod_eq_zero_iff_dvd x 8).symm
  rw [e, e]
  push_cast
  apply hz
  have : ((p : ℤ) : ZMod 8) = ((p % 8 : ℤ) : ZMod 8) := (ZMod.intCast_mod p 8).symm
  rw [this]
  rcases hp8 with h | h | h | h <;> rw [h] <;> decide

#print axioms unit_inv_class

/-- **Cofactor class.**  If `g p = 8 k + 1` then `p = g (mod 8)`: this is the statement that the reduced numerator `p`
of the landing `(8k+1)/(8x)` has the unit class of `g = gcd(8k+1, x)`. -/
theorem cofactor_class (g p k : ℤ) (h : g * p = 8 * k + 1) : (8 : ℤ) ∣ g - p := by
  have hp : Odd p := by
    have : Odd (g * p) := ⟨4 * k, by omega⟩
    exact (Int.odd_mul.mp this).2
  exact (unit_inv_class g p hp).mp ⟨k, by omega⟩

#print axioms cofactor_class

/-- The runner `m c` stands at `1/8` past a lap at `t = p/(8c)` iff `8 | m p - 1`. -/
theorem opens_iff (c p m : ℤ) (hc : 0 < c) :
    (∃ k : ℤ, ((m * c : ℤ) : ℝ) * ((p : ℝ) / (8 * c)) = k + 1 / 8) ↔ (8 : ℤ) ∣ m * p - 1 := by
  have hc' : (c : ℝ) ≠ 0 := by exact_mod_cast hc.ne'
  have key : ((m * c : ℤ) : ℝ) * ((p : ℝ) / (8 * c)) = (m : ℝ) * p / 8 := by push_cast; field_simp
  rw [key]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    have : (m : ℝ) * p = 8 * k + 1 := by linarith
    have : m * p = 8 * k + 1 := by exact_mod_cast this
    omega
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    have : m * p = 8 * k + 1 := by omega
    have h' : (m : ℝ) * p = 8 * k + 1 := by exact_mod_cast this
    linarith

#print axioms opens_iff

/-- A runner standing at `1/8` past a lap at `t = p/(8c)` (with `p`, `c` coprime) is a multiple of `c`. -/
theorem opener_dvd (c p d k : ℤ) (hc : 0 < c) (hcop : IsCoprime p c)
    (h : (d : ℝ) * ((p : ℝ) / (8 * c)) = k + 1 / 8) : c ∣ d := by
  have hc' : (c : ℝ) ≠ 0 := by exact_mod_cast hc.ne'
  have h1 : (d : ℝ) * p = c * (8 * k + 1) := by
    field_simp at h; linarith
  have h2 : d * p = c * (8 * k + 1) := by exact_mod_cast h1
  have : c ∣ d * p := ⟨8 * k + 1, h2⟩
  exact hcop.symm.dvd_of_dvd_mul_right this

#print axioms opener_dvd

/-- **Simultaneous openers (the ties).**  At `t = p/(8c)` with `p` odd and `gcd(p,c)=1`, an integer disparity `d`
stands exactly `1/8` past a lap iff `d = m c` with `m = p (mod 8)`. -/
theorem openers_at_instant (c p d : ℤ) (hc : 0 < c) (hcop : IsCoprime p c) (hp : Odd p) :
    (∃ k : ℤ, (d : ℝ) * ((p : ℝ) / (8 * c)) = k + 1 / 8) ↔ ∃ m : ℤ, d = m * c ∧ (8 : ℤ) ∣ m - p := by
  constructor
  · rintro ⟨k, hk⟩
    obtain ⟨m, hm⟩ := opener_dvd c p d k hc hcop hk
    have hd : d = m * c := by rw [hm]; ring
    refine ⟨m, hd, ?_⟩
    have : ∃ k' : ℤ, ((m * c : ℤ) : ℝ) * ((p : ℝ) / (8 * c)) = k' + 1 / 8 := ⟨k, by rw [← hd]; exact hk⟩
    exact (unit_inv_class m p hp).mp ((opens_iff c p m hc).mp this)
  · rintro ⟨m, hd, hdiv⟩
    rw [hd]
    exact (opens_iff c p m hc).mpr ((unit_inv_class m p hp).mpr hdiv)

#print axioms openers_at_instant

/-! ## 6. Sweep-down -/

/-- **Sweep-down.**  If `y` opens at lap `j` at time `t` (`y t = j + 1/8`) and a neighbour at distance `e` has
`0 < e t < 1/4`, then the runner `y - e` is in the way at `t`.  (With `e = d_min` and `R = 8 d_min t`, the
condition is `0 < R < 2`.) -/
theorem neighbour_in_way (y e t : ℝ) (j : ℤ) (h : y * t = j + 1 / 8) (h1 : 0 < e * t) (h2 : e * t < 1 / 4) :
    InWay (y - e) t := by
  rw [inWay_iff_near]
  refine ⟨j, ?_⟩
  rw [abs_lt]
  constructor <;> nlinarith

#print axioms neighbour_in_way

/-- **A landing never has its predecessor in the set.**  If `x` opens at the clear instant `t` (`x t = j + 1/8`),
`0 < e t < 1/4`, then `x - e` is not a disparity. -/
theorem landing_no_predecessor {ds : Finset ℝ} {t x e : ℝ} (hc : ClearAt ds t) (j : ℤ) (h : x * t = j + 1 / 8)
    (h1 : 0 < e * t) (h2 : e * t < 1 / 4) : x - e ∉ ds := by
  intro hmem
  have hw := neighbour_in_way x e t j h h1 h2
  have := hc _ hmem
  unfold InWay at hw
  linarith

#print axioms landing_no_predecessor

end LandingExceptions

end Fresh
