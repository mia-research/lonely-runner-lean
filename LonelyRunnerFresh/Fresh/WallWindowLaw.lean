import Mathlib
import Fresh.Framework
import Fresh.Cascade
import Fresh.ChainCarried

/-!
# The wall-window laws (E929 to E931)

Written 2026-11-25.  New file; nothing existing is edited.  Readings are positive reals; no runner is stationary
(rule 5).  A reading `d` is in the way at `t` when `d * t` is within `1/8` of a whole lap (`InWay`), and its next
opening after `t` is `nextOpening d t` (both in `Fresh.Framework`).

* `inWay_iff_zone`: in the way at `t` iff `t` lies in a zone `((8k-1)/(8d), (8k+1)/(8d))` for some lap `k`.
* `one_move_pass_iff` (E930 item 1, one reading): `d` is in the way at `a` and its next opening is past `b` iff
  `(8k-1)/(8a) < d < (8k+1)/(8b)` for some lap `k`.
* `move_passes_iff` (E930 item 1): the cascade's move from `a`, among a finite set of readings, lands past `b` iff some
  reading of the set satisfies that condition.  This is the step-0 law of E331 taken at an instant `a`.
* `passCell_nonempty_iff` (E930 item 2): the condition can hold for some reading iff `(8k-1) b < (8k+1) a`.
* `inWay_at_opening_iff` (E931 item 1(b), the link law): reading `f'` is in the way at the opening
  `(8k+1)/(8f)` of reading `f` iff `(8k'-1)/(8k+1) < f'/f < (8k'+1)/(8k+1)` for some lap `k'`.

* `window_landing_eq` (E929 item 1): if `T` is the first lonely instant of `F ∪ S`, the frozen set `S` is lonely on
  `[a, T]`, every `S`-lonely instant before `a` has an `F` reading in the way, and the cascade of `F` alone from `a`
  fixes, then it fixes at `T`.  It is `Fresh.OneMover.chain_landing` (E757) read from the landing's side.  The
  cascade fixing is a hypothesis, not proved here.
No cap, covering, counting or termination step is used here.  Grades: [L].
-/

namespace Fresh.WallWindow

open Fresh Fresh.OneMover

/-- `distInt x < c` iff `x` is within `c` of some integer. -/
theorem distInt_lt_iff {x c : ℝ} : distInt x < c ↔ ∃ k : ℤ, |x - k| < c := by
  constructor
  · intro h; exact ⟨round x, h⟩
  · rintro ⟨k, hk⟩; exact lt_of_le_of_lt (Fresh.Cascade.distInt_le x k) hk

/-- **Zones.**  `d` is in the way at `t` iff `t` lies in one of its zones. -/
theorem inWay_iff_zone {d t : ℝ} (hd : 0 < d) :
    InWay d t ↔ ∃ k : ℤ, (8 * (k : ℝ) - 1) / (8 * d) < t ∧ t < (8 * (k : ℝ) + 1) / (8 * d) := by
  unfold InWay
  rw [distInt_lt_iff]
  have h8 : (0 : ℝ) < 8 * d := by positivity
  constructor
  · rintro ⟨k, hk⟩
    obtain ⟨h1, h2⟩ := abs_lt.mp hk
    refine ⟨k, ?_, ?_⟩
    · rw [div_lt_iff₀ h8]; nlinarith
    · rw [lt_div_iff₀ h8]; nlinarith
  · rintro ⟨k, h1, h2⟩
    rw [div_lt_iff₀ h8] at h1
    rw [lt_div_iff₀ h8] at h2
    exact ⟨k, abs_lt.mpr ⟨by nlinarith, by nlinarith⟩⟩

/-- **One reading passes `[a, b]` in one move** (E930 item 1).  For `0 < a ≤ b`: `d` is in the way at `a` and its
next opening is after `b` iff `(8k-1)/(8a) < d < (8k+1)/(8b)` for some lap `k`. -/
theorem one_move_pass_iff {d a b : ℝ} (hd : 0 < d) (ha : 0 < a) (hab : a ≤ b) :
    (InWay d a ∧ b < nextOpening d a) ↔
      ∃ k : ℤ, (8 * (k : ℝ) - 1) / (8 * a) < d ∧ d < (8 * (k : ℝ) + 1) / (8 * b) := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have h8a : (0 : ℝ) < 8 * a := by positivity
  have h8b : (0 : ℝ) < 8 * b := by positivity
  constructor
  · rintro ⟨hw, hn⟩
    obtain ⟨k, hk⟩ := Fresh.Cascade.exists_near_int hw
    rw [Fresh.Cascade.nextOpening_eq hk, lt_div_iff₀ hd] at hn
    obtain ⟨h1, _⟩ := abs_lt.mp hk
    refine ⟨k, ?_, ?_⟩
    · rw [div_lt_iff₀ h8a]; nlinarith
    · rw [lt_div_iff₀ h8b]; nlinarith
  · rintro ⟨k, h1, h2⟩
    rw [div_lt_iff₀ h8a] at h1
    rw [lt_div_iff₀ h8b] at h2
    have hda : d * a ≤ d * b := mul_le_mul_of_nonneg_left hab hd.le
    have hk : |d * a - k| < 1 / 8 := abs_lt.mpr ⟨by nlinarith, by nlinarith⟩
    refine ⟨lt_of_le_of_lt (Fresh.Cascade.distInt_le (d * a) k) hk, ?_⟩
    rw [Fresh.Cascade.nextOpening_eq hk, lt_div_iff₀ hd]
    nlinarith

/-- **The move from `a` passes `b`** (E930 item 1).  For a finite set of positive readings and `0 < a ≤ b`, the
cascade's move from `a` lands after `b` iff some reading of the set lies in `((8k-1)/(8a), (8k+1)/(8b))` for some
lap `k`. -/
theorem move_passes_iff {F : Finset ℝ} (hpos : ∀ d ∈ F, 0 < d) {a b t' : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hm : IsMove F a t') :
    b < t' ↔ ∃ d ∈ F, ∃ k : ℤ, (8 * (k : ℝ) - 1) / (8 * a) < d ∧ d < (8 * (k : ℝ) + 1) / (8 * b) := by
  constructor
  · intro hbt
    rcases hm with ⟨_, he⟩ | ⟨d, hd, hw, he, _⟩
    · rw [he] at hbt; exact absurd hab (not_le.mpr hbt)
    · rw [he] at hbt
      exact ⟨d, hd, (one_move_pass_iff (hpos d hd) ha hab).mp ⟨hw, hbt⟩⟩
  · rintro ⟨d, hd, hk⟩
    obtain ⟨hw, hn⟩ := (one_move_pass_iff (hpos d hd) ha hab).mpr hk
    rcases hm with ⟨hno, _⟩ | ⟨_, _, _, _, hmax⟩
    · exact absurd hw (hno d hd)
    · exact lt_of_lt_of_le hn (hmax d hd hw)

/-- **When the pass condition can hold at lap `k`** (E930 item 2): for `a, b > 0`, some real lies in
`((8k-1)/(8a), (8k+1)/(8b))` iff `(8k-1) b < (8k+1) a`. -/
theorem passCell_nonempty_iff {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (k : ℤ) :
    (∃ d : ℝ, (8 * (k : ℝ) - 1) / (8 * a) < d ∧ d < (8 * (k : ℝ) + 1) / (8 * b)) ↔
      (8 * (k : ℝ) - 1) * b < (8 * (k : ℝ) + 1) * a := by
  have h8a : (0 : ℝ) < 8 * a := by positivity
  have h8b : (0 : ℝ) < 8 * b := by positivity
  have key : (8 * (k : ℝ) - 1) / (8 * a) < (8 * (k : ℝ) + 1) / (8 * b) ↔
      (8 * (k : ℝ) - 1) * b < (8 * (k : ℝ) + 1) * a := by
    rw [div_lt_div_iff₀ h8a h8b]
    constructor <;> intro h <;> nlinarith
  constructor
  · rintro ⟨d, h1, h2⟩; exact key.mp (lt_trans h1 h2)
  · intro h
    have hlt := key.mpr h
    exact ⟨((8 * (k : ℝ) - 1) / (8 * a) + (8 * (k : ℝ) + 1) / (8 * b)) / 2, by linarith, by linarith⟩

/-- **The link law** (E931 item 1(b)).  For positive readings `f, f'` and a lap `k ≥ 0`, `f'` is in the way at `f`'s
opening `(8k+1)/(8f)` iff `(8k'-1)/(8k+1) < f'/f < (8k'+1)/(8k+1)` for some lap `k'`. -/
theorem inWay_at_opening_iff {f f' : ℝ} (hf : 0 < f) (hf' : 0 < f') {k : ℤ} (hk : 0 ≤ k) :
    InWay f' ((8 * (k : ℝ) + 1) / (8 * f)) ↔
      ∃ k' : ℤ, (8 * (k' : ℝ) - 1) / (8 * (k : ℝ) + 1) < f' / f ∧
        f' / f < (8 * (k' : ℝ) + 1) / (8 * (k : ℝ) + 1) := by
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hK : (0 : ℝ) < 8 * (k : ℝ) + 1 := by linarith
  have hx : f' * ((8 * (k : ℝ) + 1) / (8 * f)) = (f' / f) * (8 * (k : ℝ) + 1) / 8 := by
    field_simp
  unfold InWay
  rw [distInt_lt_iff, hx]
  constructor
  · rintro ⟨k', hk'⟩
    obtain ⟨h1, h2⟩ := abs_lt.mp hk'
    refine ⟨k', ?_, ?_⟩
    · rw [div_lt_iff₀ hK]; nlinarith
    · rw [lt_div_iff₀ hK]; nlinarith
  · rintro ⟨k', h1, h2⟩
    rw [div_lt_iff₀ hK] at h1
    rw [lt_div_iff₀ hK] at h2
    exact ⟨k', abs_lt.mpr ⟨by nlinarith, by nlinarith⟩⟩

/-- **The landing is the free readings' cascade from the window's opening** (E929 item 1). -/
theorem window_landing_eq {F S : Finset ℝ} (hpos : ∀ d ∈ F, 0 < d) {a T : ℝ} (ha : 0 < a)
    {seq : ℕ → ℝ} (h0 : seq 0 = a) (hmv : ∀ n, IsMove F (seq n) (seq (n + 1)))
    (hb : ∀ s : ℝ, 0 < s → s < a → Fresh.Cascade.LonelyAt S s → ∃ d ∈ F, InWay d s)
    (hT : IsFirst (F ∪ S) T) (hTpos : 0 < T)
    (hS : ∀ s : ℝ, a ≤ s → s ≤ T → Fresh.Cascade.LonelyAt S s)
    {K : ℕ} (hK : seq (K + 1) = seq K) : seq K = T := by
  have hle : seq K ≤ T := chain_lower hpos h0 hmv hb hTpos hT.1 K
  have hge : a ≤ seq K := by
    have := Fresh.Cascade.start_le_seq hpos hmv K; rwa [h0] at this
  have hfirst : IsFirst (F ∪ S) (seq K) := chain_landing hpos h0 hmv hb hK (hS _ hge hle)
  exact le_antisymm hle (hT.2 _ (lt_of_lt_of_le ha hge) hfirst.1)

#print axioms window_landing_eq
#print axioms distInt_lt_iff
#print axioms inWay_iff_zone
#print axioms one_move_pass_iff
#print axioms move_passes_iff
#print axioms passCell_nonempty_iff
#print axioms inWay_at_opening_iff

end Fresh.WallWindow
