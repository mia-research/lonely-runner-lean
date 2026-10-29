import Mathlib
import Fresh.Localisation
import Fresh.ScaledCoreReal

/-!
# A checked chain of served intervals for a core and one real extra reading

Written 2026-10-29.  New file; imports `Fresh.Localisation` and `Fresh.ScaledCoreReal` only.
A `Piece` is a window `[lo, hi]` of a core (whole numbers `L`), a shift `d` with `s d` whole for every `s ∈ L`, a whole number `k`, and the interval `[a, b]` of real `y` it serves
(`k + 1/8 ≤ a (hi + d)`, `b (lo + d) ≤ k + 7/8`).  `chainOK` checks, over `ℚ`, that consecutive pieces overlap and reach from `cur` to `y0`.
`real_all`: if `chainOK`, `smallOK` and `largeOK` hold, then for every real `y > 0` the core together with `y` has a common `1/8`-clear instant.
**[PROVISIONAL: covering]** at the use: the claim named is that the listed intervals cover `[3/8, y0]`; the cover is the content of the Boolean `chainOK`, checked by the kernel, not assumed.  Grade [L].
-/

namespace Fresh.ScaledCoreChain

open Fresh

structure Piece where
  a : ℚ
  b : ℚ
  lo : ℚ
  hi : ℚ
  d : ℚ
  k : ℤ

noncomputable def coreSet (L : List ℕ) : Finset ℝ := (L.map (fun n : ℕ => (n : ℝ))).toFinset

def bandsOK (L : List ℕ) (lo hi : ℚ) : Bool :=
  L.all (fun s => decide ((s : ℚ) * hi ≤ ((⌊(s : ℚ) * lo - 1 / 8⌋ : ℤ) : ℚ) + 7 / 8))

def wholeOK (L : List ℕ) (d : ℚ) : Bool :=
  L.all (fun s => decide ((s : ℚ) * d = ((⌊(s : ℚ) * d⌋ : ℤ) : ℚ)))

def pieceOK (L : List ℕ) (p : Piece) : Bool :=
  decide (0 < p.lo) && decide (p.lo ≤ p.hi) && decide (0 ≤ p.d) && decide (p.a ≤ p.b) &&
    decide ((p.k : ℚ) + 1 / 8 ≤ p.a * (p.hi + p.d)) && decide (p.b * (p.lo + p.d) ≤ (p.k : ℚ) + 7 / 8) &&
    bandsOK L p.lo p.hi && wholeOK L p.d

theorem mem_coreSet {L : List ℕ} {s : ℝ} (h : s ∈ coreSet L) : ∃ n ∈ L, (n : ℝ) = s := by
  simpa [coreSet] using h

theorem bands_sound {L : List ℕ} {lo hi : ℚ} (h : bandsOK L lo hi = true) :
    ∀ s ∈ coreSet L, ∃ N : ℤ, (N : ℝ) + 1 / 8 ≤ s * (lo : ℝ) ∧ s * (hi : ℝ) ≤ (N : ℝ) + 7 / 8 := by
  intro s hs
  obtain ⟨n, hn, rfl⟩ := mem_coreSet hs
  simp only [bandsOK, List.all_eq_true, decide_eq_true_eq] at h
  refine ⟨⌊(n : ℚ) * lo - 1 / 8⌋, ?_, ?_⟩
  · have h1 : ((⌊(n : ℚ) * lo - 1 / 8⌋ : ℤ) : ℚ) ≤ (n : ℚ) * lo - 1 / 8 := Int.floor_le _
    have : ((⌊(n : ℚ) * lo - 1 / 8⌋ : ℤ) : ℚ) + 1 / 8 ≤ (n : ℚ) * lo := by linarith
    have h' := (Rat.cast_le (K := ℝ)).2 this
    push_cast at h'
    exact h'
  · have := h n hn
    have h' := (Rat.cast_le (K := ℝ)).2 this
    push_cast at h'
    exact h'

theorem whole_sound {L : List ℕ} {d : ℚ} (h : wholeOK L d = true) :
    ∀ s ∈ coreSet L, ∃ m : ℤ, s * (d : ℝ) = m := by
  intro s hs
  obtain ⟨n, hn, rfl⟩ := mem_coreSet hs
  simp only [wholeOK, List.all_eq_true, decide_eq_true_eq] at h
  refine ⟨⌊(n : ℚ) * d⌋, ?_⟩
  have := h n hn
  have h' := congrArg (fun q : ℚ => (q : ℝ)) this
  push_cast at h'
  exact h'

theorem piece_sound {L : List ℕ} (hL : ∀ n ∈ L, 0 < n) {p : Piece} (h : pieceOK L p = true) {y : ℝ} (hy : 0 < y)
    (h1 : (p.a : ℝ) ≤ y) (h2 : y ≤ (p.b : ℝ)) :
    ∃ t : ℝ, 0 < t ∧ (∀ s ∈ coreSet L, (1 / 8 : ℝ) ≤ distInt (s * t)) ∧ (1 / 8 : ℝ) ≤ distInt (y * t) := by
  simp only [pieceOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hlo, hle⟩, hd⟩, hab⟩, hk1⟩, hk2⟩, hb⟩, hw⟩ := h
  have hlo' : (0 : ℝ) < p.lo := by exact_mod_cast hlo
  have hle' : (p.lo : ℝ) ≤ p.hi := by exact_mod_cast hle
  have hd' : (0 : ℝ) ≤ p.d := by exact_mod_cast hd
  have hk1' : (p.k : ℝ) + 1 / 8 ≤ (p.a : ℝ) * ((p.hi : ℝ) + p.d) := by
    have h' := (Rat.cast_le (K := ℝ)).2 hk1
    push_cast at h'; exact h'
  have hk2' : (p.b : ℝ) * ((p.lo : ℝ) + p.d) ≤ (p.k : ℝ) + 7 / 8 := by
    have h' := (Rat.cast_le (K := ℝ)).2 hk2
    push_cast at h'; exact h'
  have hpos : ∀ s ∈ coreSet L, 0 < s := by
    intro s hs
    obtain ⟨n, hn, rfl⟩ := mem_coreSet hs
    exact_mod_cast hL n hn
  apply Fresh.ScaledCoreReal.served (p.d : ℝ) hlo' hle' hy hd' (whole_sound hw) (bands_sound hb) hpos p.k
  · have : (0 : ℝ) ≤ (p.hi : ℝ) + p.d := by linarith
    nlinarith [mul_le_mul_of_nonneg_right h1 this]
  · have : (0 : ℝ) ≤ (p.lo : ℝ) + p.d := by linarith
    nlinarith [mul_le_mul_of_nonneg_right h2 this]


def chainOK (L : List ℕ) : List Piece → ℚ → ℚ → Bool
  | [], _, _ => false
  | p :: ps, cur, y0 => decide (p.a ≤ cur) && pieceOK L p && (decide (y0 ≤ p.b) || chainOK L ps p.b y0)

theorem chain_sound {L : List ℕ} (hL : ∀ n ∈ L, 0 < n) :
    ∀ (ps : List Piece) (cur y0 : ℚ), chainOK L ps cur y0 = true → ∀ y : ℝ, (cur : ℝ) ≤ y → y ≤ (y0 : ℝ) → 0 < y →
      ∃ t : ℝ, 0 < t ∧ (∀ s ∈ coreSet L, (1 / 8 : ℝ) ≤ distInt (s * t)) ∧ (1 / 8 : ℝ) ≤ distInt (y * t) := by
  intro ps
  induction ps with
  | nil => intro cur y0 h; simp [chainOK] at h
  | cons p ps ih =>
    intro cur y0 h y hc hy0 hy
    simp only [chainOK, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hpa, hp⟩, hrest⟩ := h
    have hpa' : (p.a : ℝ) ≤ y := le_trans (by exact_mod_cast hpa) hc
    by_cases hyb : y ≤ (p.b : ℝ)
    · exact piece_sound hL hp hy hpa' hyb
    · push_neg at hyb
      rcases hrest with h0 | h1
      · have : (y0 : ℝ) ≤ p.b := by exact_mod_cast h0
        linarith
      · exact ih p.b y0 h1 y hyb.le hy0 hy

def smallOK (L : List ℕ) (lo hi τ : ℚ) : Bool :=
  decide (0 < lo) && decide (lo ≤ hi) && decide (0 < τ) && decide (lo ≤ τ) && decide (τ ≤ 1) && bandsOK L lo hi && wholeOK L τ

theorem small_sound {L : List ℕ} (hL : ∀ n ∈ L, 0 < n) {lo hi τ : ℚ} (h : smallOK L lo hi τ = true) {y : ℝ} (hy : 0 < y) (hy38 : y ≤ 3 / 8) :
    ∃ t : ℝ, 0 < t ∧ (∀ s ∈ coreSet L, (1 / 8 : ℝ) ≤ distInt (s * t)) ∧ (1 / 8 : ℝ) ≤ distInt (y * t) := by
  simp only [smallOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨hlo, hle⟩, hτ⟩, hlt⟩, hτ1⟩, hb⟩, hw⟩ := h
  have hlo' : (0 : ℝ) < lo := by exact_mod_cast hlo
  have hle' : (lo : ℝ) ≤ hi := by exact_mod_cast hle
  have hτ' : (0 : ℝ) < τ := by exact_mod_cast hτ
  have hlt' : (lo : ℝ) ≤ τ := by exact_mod_cast hlt
  have hτ1' : (τ : ℝ) ≤ 1 := by exact_mod_cast hτ1
  have h34 : y * ((lo : ℝ) + τ) ≤ 3 / 4 := by nlinarith
  obtain ⟨n, h1, h2⟩ := Fresh.ScaledCoreReal.small_y_shift hlo' hle' hτ' hy h34
  have hpos : ∀ s ∈ coreSet L, 0 < s := by
    intro s hs
    obtain ⟨m, hm, rfl⟩ := mem_coreSet hs
    exact_mod_cast hL m hm
  have hint : ∀ s ∈ coreSet L, ∃ m : ℤ, s * ((n : ℝ) * τ) = m := by
    intro s hs
    obtain ⟨m, hm⟩ := whole_sound hw s hs
    exact ⟨m * n, by push_cast; rw [← hm]; ring⟩
  exact Fresh.ScaledCoreReal.served ((n : ℝ) * τ) hlo' hle' hy (by positivity) hint (bands_sound hb) hpos 0 (by simpa using h1) (by simpa using h2)

def largeOK (L : List ℕ) (lo hi y0 : ℚ) : Bool :=
  decide (0 < lo) && decide (lo ≤ hi) && decide (1 / 4 ≤ y0 * (hi - lo)) && bandsOK L lo hi

theorem large_sound {L : List ℕ} (hL : ∀ n ∈ L, 0 < n) {lo hi y0 : ℚ} (h : largeOK L lo hi y0 = true) {y : ℝ} (hy0 : (y0 : ℝ) ≤ y) (hy : 0 < y) :
    ∃ t : ℝ, 0 < t ∧ (∀ s ∈ coreSet L, (1 / 8 : ℝ) ≤ distInt (s * t)) ∧ (1 / 8 : ℝ) ≤ distInt (y * t) := by
  simp only [largeOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hlo, hle⟩, hw⟩, hb⟩ := h
  have hlo' : (0 : ℝ) < lo := by exact_mod_cast hlo
  have hle' : (lo : ℝ) ≤ hi := by exact_mod_cast hle
  have hw' : (1 / 4 : ℝ) ≤ (y0 : ℝ) * ((hi : ℝ) - lo) := by
    have h' := (Rat.cast_le (K := ℝ)).2 hw
    push_cast at h'; exact h'
  have hpos : ∀ s ∈ coreSet L, 0 < s := by
    intro s hs
    obtain ⟨m, hm, rfl⟩ := mem_coreSet hs
    exact_mod_cast hL m hm
  set k : ℤ := ⌈y * lo - 7 / 8⌉ with hk
  have hk1 : y * lo - 7 / 8 ≤ k := Int.le_ceil _
  have hk2 : (k : ℝ) < y * lo - 7 / 8 + 1 := Int.ceil_lt_add_one _
  have hyw : (1 / 4 : ℝ) ≤ y * ((hi : ℝ) - lo) := by nlinarith [mul_le_mul_of_nonneg_right hy0 (sub_nonneg.2 hle')]
  exact Fresh.ScaledCoreReal.served 0 hlo' hle' hy le_rfl (fun s hs => ⟨0, by simp⟩) (bands_sound hb) hpos k
    (by nlinarith) (by nlinarith)

def coreOK (L : List ℕ) (ps : List Piece) (lo hi τ lo2 hi2 y0 : ℚ) : Bool :=
  chainOK L ps (3 / 8) y0 && smallOK L lo hi τ && largeOK L lo2 hi2 y0

/-- A core of whole numbers together with ANY one real positive reading has a common `1/8`-clear instant, once `coreOK` is checked. -/
theorem real_all {L : List ℕ} (hL : ∀ n ∈ L, 0 < n) {ps : List Piece} {lo hi τ lo2 hi2 y0 : ℚ}
    (h : coreOK L ps lo hi τ lo2 hi2 y0 = true) {y : ℝ} (hy : 0 < y) :
    ∃ t : ℝ, 0 < t ∧ (∀ s ∈ coreSet L, (1 / 8 : ℝ) ≤ distInt (s * t)) ∧ (1 / 8 : ℝ) ≤ distInt (y * t) := by
  simp only [coreOK, Bool.and_eq_true] at h
  obtain ⟨⟨hc, hs⟩, hl⟩ := h
  by_cases h38 : y ≤ 3 / 8
  · exact small_sound hL hs hy h38
  · push_neg at h38
    by_cases hy0 : y ≤ (y0 : ℝ)
    · exact chain_sound hL ps (3 / 8) y0 hc y (by push_cast; linarith) hy0 hy
    · push_neg at hy0
      exact large_sound hL hl hy0.le hy

#print axioms real_all

end Fresh.ScaledCoreChain
