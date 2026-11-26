import Mathlib
import Fresh.Framework
import Fresh.Grid
import Fresh.LonelyCells
import Fresh.PairLaw
import Fresh.PathClassify

/-!
# The displacement at zero margin: first order, exact (Task AH)

Written 2026-10-09.  Imports Mathlib and the Fresh modules `Framework`, `Grid`, `LonelyCells`, `PairLaw`,
`PathClassify`.  Nothing from the existing `LonelyRunner` repo.  Exact reals, positive speeds, no counting, covering,
density, cap or move budget as the SHAPE of any statement.

Objects.  A reading is `x = d * t` (a disparity times an instant).  A lonely instant `t0` of a disparity family
`d : ι → ℝ` has every reading at circle distance `≥ 1/8`.  A reading is
* an OPENER if `x = k + 1/8` (it stands at the end of its zone and leaves it as `t` grows),
* an ENTRY if `x = k + 7/8` (it is about to enter the next zone as `t` grows),
* SLACK if `1/8 < distInt x`.
(`crit_trichotomy`: a clear reading is exactly one of these.)  A lonely instant with at least one opener or entry is a
TOUCH (zero margin); `PathClassify.ap_not_strict` says that at the AP every lonely instant is one.

Results ([L] = Lean, `#print axioms` after each; [reasoned] = not formalised; [OWED] = not done).
* (1) EXACT survival.  Deform `d_i -> d_i + e δ_i`, move the instant `t0 -> t0 + e τ`.  The reading is
  `d_i t0 + e (A_i + e B_i)`, `A_i = δ_i t0 + d_i τ`, `B_i = δ_i τ` (`reading_expand`).  `exact_touch_survival`:
  for `e > 0` with `e|A_i + e B_i| < margin(d_i t0)` for every `i`, the family is lonely at the moved instant IFF every
  opener has `0 <= A_i + e B_i` and every entry has `A_i + e B_i <= 0`.  `exact_touch_explicit`: the range stated
  as `0 < e < 1`, `e (|A_i| + |B_i|) < margin_i`.  `exact_touch_eventually`: for small `e > 0` the equivalence holds.
  `touch_survives_of_strict` / `touch_fails_of_violation`: strict first-order inequalities decide small `e`.  The
  condition is linear in `e` after dividing by `e` (the product `(d + eδ)(t0 + eτ)` is quadratic in `e`; the `e²` term
  is `B_i = δ_i τ`).  At `A_i = 0` the sign of `B_i` decides: this is the second-order content (see `scaling_B_obstruction`).
* (2) Interval system.  `helly_one_dim`: a `τ` exists with all opener and entry inequalities iff for every opener `i`
  and entry `j`, `δ_j/d_j <= δ_i/d_i` (relative speed change of the opener at least that of the entry).  No opener
  or no entry: always solvable (`free_touch_survives`: then survival is STRICT for every direction).
* (3) The AP.  `ap_classes`: at the instant `a/8`, `a ∈ {1,3,5,7}`, the readings `j a/8` (`1 <= j <= 7`) have the opener
  exactly `j = a` and the entry exactly `j = 8 - a`, all others slack.  `ap_first_order_iff`: first-order survival iff
  `σ_a(δ) = δ_a/a - δ_b/b >= 0`, `b = 8 - a`.  `sigma_antisymm`: `σ_b = -σ_a`; `ap_mirror_survival`: for every
  direction, one of each mirror pair survives to first order.  `ap_displaced`: strict `σ_a > 0` gives a moved instant
  `a/8 + e τ` that is lonely for `pds (j + e δ_j)`, small `e > 0`.  `survival_form_is_linearisation`: `b d_a - a d_b` is
  affine in `e` with slope `a b σ_a`; `pair_law_is_survival_form`: `PairLaw.uA <= wA` iff `0 <= σ_a`, EXACTLY, for the affine
  deformation (the first-order form is the whole pair condition).  `ap_mirror_instant`: `(8-a)/8` swaps the roles of `a/8`.
* (4) Conjugates.  `mirror_seven`: `t -> 7 t` swaps openers and entries, for every critical reading at once.
  `conjugate_pair_exists`: a pair (i opener, j entry) at `t0` always has the swapped pair at `7 t0` (so the pairwise
  ratio condition is automatic).  `ratio_condition`: for naturals `p, q` with `p` odd, readings `p c t`, `q c t`
  have (opener, entry) at some `t > 0` iff `p + q ≡ 0 (mod 8)`; `ratio_condition_swapped` the same for the swapped
  roles; `ratio_condition_needs_coprime`: `p = 2, q = 6` satisfies the congruence and has no such instant.
  `commensurable_mirror`: if every disparity has `d T ∈ ℤ`, the reflection `t0 -> m T - t0` carries a lonely instant to a
  lonely instant and flips all roles (the AP's mirror is this reflection with `T = 1`).  `free_example`: a touch with
  an opener and no entry (no conjugate partner of any kind).
* (5) Positive dependence.  `gordan`: for finitely many linear forms on `ℝ^n`, either one direction makes all strictly
  negative, or a nonnegative nonzero combination vanishes (via Mathlib's Hahn-Banach separation).
  `every_direction_survivor_iff`: some form `>= 0` in every direction iff the forms are positively dependent.
  `ap_every_direction_survivor`: for the AP, every direction has `σ_{2k+1}(δ) >= 0` for some `k`.
  `ap_touch_positive_dependence`: for the AP, `σ_1 + σ_7 = 0` and `σ_3 + σ_5 = 0`.  The statement for general
  arrangements ('touch positive dependence') is OWED.

Provenance.  The existing repo has the pair law (`LRC/Spec/ProgressionPairN.lean`) re-derived in `Fresh/PairLaw.lean`; the
zero-margin first-order form, the exact expansion and the Helly equivalence are new here (no existing declaration
corresponds).  `crit_trichotomy`, `runner_exact` follow the idea of the window lemma `Localisation.clear_of_window`
(read and understood; nothing copied).  Gordan is proved here from `geometric_hahn_banach_compact_closed`.
-/

open Classical Filter Topology

namespace Fresh

namespace ZeroMargin

open Localisation

/-! ## (0) Openers, entries, slack -/

/-- A reading at the end of its zone: leaves it as the instant grows. -/
-- STANDING: DEFINITION
def IsOpener (x : ℝ) : Prop := ∃ k : ℤ, x = (k : ℝ) + 1 / 8

/-- A reading about to enter its zone as the instant grows. -/
-- STANDING: DEFINITION
def IsEntry (x : ℝ) : Prop := ∃ k : ℤ, x = (k : ℝ) + 7 / 8

theorem distInt_opening (k : ℤ) : distInt ((k : ℝ) + 1 / 8) = 1 / 8 := by
  apply le_antisymm
  · have := distInt_le ((k : ℝ) + 1 / 8) k
    rw [show (k : ℝ) + 1 / 8 - k = 1 / 8 by ring, abs_of_pos (by norm_num)] at this
    exact this
  · exact clear_of_window k le_rfl (by linarith)

#print axioms distInt_opening

theorem distInt_entry (k : ℤ) : distInt ((k : ℝ) + 7 / 8) = 1 / 8 := by
  apply le_antisymm
  · have := distInt_le ((k : ℝ) + 7 / 8) (k + 1)
    rw [show (k : ℝ) + 7 / 8 - ((k + 1 : ℤ) : ℝ) = -(1 / 8) by push_cast; ring, abs_neg,
      abs_of_pos (by norm_num)] at this
    exact this
  · exact clear_of_window k (by linarith) le_rfl

#print axioms distInt_entry

theorem not_opener_and_entry {x : ℝ} : ¬ (IsOpener x ∧ IsEntry x) := by
  rintro ⟨⟨k, hk⟩, ⟨k', hk'⟩⟩
  have h : ((k - k' : ℤ) : ℝ) * 4 = 3 := by push_cast; linarith
  have h' : (k - k') * 4 = (3 : ℤ) := by exact_mod_cast h
  omega

#print axioms not_opener_and_entry

theorem IsOpener.distInt_eq {x : ℝ} (h : IsOpener x) : distInt x = 1 / 8 := by
  obtain ⟨k, rfl⟩ := h; exact distInt_opening k

theorem IsEntry.distInt_eq {x : ℝ} (h : IsEntry x) : distInt x = 1 / 8 := by
  obtain ⟨k, rfl⟩ := h; exact distInt_entry k

/-- **A clear reading is exactly one of opener, entry, slack** [L]. -/
theorem crit_trichotomy {x : ℝ} (h : (1 / 8 : ℝ) ≤ distInt x) :
    IsOpener x ∨ IsEntry x ∨ 1 / 8 < distInt x := by
  rcases h.lt_or_eq with h | h
  · exact Or.inr (Or.inr h)
  · have h' : |x - (round x : ℝ)| = 1 / 8 := h.symm
    rcases abs_eq (by norm_num : (0 : ℝ) ≤ 1 / 8) |>.mp h' with h1 | h1
    · exact Or.inl ⟨round x, by linarith⟩
    · exact Or.inr (Or.inl ⟨round x - 1, by push_cast; linarith⟩)

#print axioms crit_trichotomy

/-- The room a reading has before its status can change. -/
noncomputable def margin (x : ℝ) : ℝ := if 1 / 8 < distInt x then distInt x - 1 / 8 else 1 / 4

theorem margin_pos {x : ℝ} (h : (1 / 8 : ℝ) ≤ distInt x) : 0 < margin x := by
  unfold margin
  split_ifs with h1
  · linarith
  · norm_num

#print axioms margin_pos

/-! ## (1) One runner, exactly -/

/-- Just past the opening, clearance is exactly "not before the opening" [L]. -/
theorem clear_iff_low {k : ℤ} {y : ℝ} (hy : |y - ((k : ℝ) + 1 / 8)| < 1 / 4) :
    (1 / 8 : ℝ) ≤ distInt y ↔ (k : ℝ) + 1 / 8 ≤ y := by
  rw [abs_lt] at hy
  constructor
  · intro h
    by_contra hc
    push Not at hc
    have h1 := distInt_le y k
    have h2 : |y - (k : ℝ)| < 1 / 8 := abs_lt.mpr ⟨by linarith, by linarith⟩
    linarith
  · intro h
    exact clear_of_window k h (by linarith)

theorem clear_iff_high {k : ℤ} {y : ℝ} (hy : |y - ((k : ℝ) + 7 / 8)| < 1 / 4) :
    (1 / 8 : ℝ) ≤ distInt y ↔ y ≤ (k : ℝ) + 7 / 8 := by
  rw [abs_lt] at hy
  constructor
  · intro h
    by_contra hc
    push Not at hc
    have h1 := distInt_le y (k + 1)
    push_cast at h1
    have h2 : |y - ((k : ℝ) + 1)| < 1 / 8 := abs_lt.mpr ⟨by linarith, by linarith⟩
    linarith
  · intro h
    exact clear_of_window k (by linarith) h

#print axioms clear_iff_low
#print axioms clear_iff_high

/-- **One runner, exactly** [L]: a clear reading `x0` moved to `y` within its margin stays clear iff an opener does not
retreat and an entry does not advance. -/
theorem runner_exact {x0 y : ℝ} (hl : (1 / 8 : ℝ) ≤ distInt x0) (hy : |y - x0| < margin x0) :
    (1 / 8 : ℝ) ≤ distInt y ↔ ((IsOpener x0 → x0 ≤ y) ∧ (IsEntry x0 → y ≤ x0)) := by
  rcases crit_trichotomy hl with ho | he | hs
  · have hm : margin x0 = 1 / 4 := by
      unfold margin; rw [ho.distInt_eq]; simp
    rw [hm] at hy
    obtain ⟨k, hk⟩ := ho
    have hne : ¬ IsEntry x0 := fun h => not_opener_and_entry ⟨⟨k, hk⟩, h⟩
    have hy' : |y - ((k : ℝ) + 1 / 8)| < 1 / 4 := hk ▸ hy
    constructor
    · intro h
      exact ⟨fun _ => by rw [hk]; exact (clear_iff_low hy').mp h, fun he => absurd he hne⟩
    · rintro ⟨h1, _⟩
      exact (clear_iff_low hy').mpr (hk ▸ h1 ⟨k, hk⟩)
  · have hm : margin x0 = 1 / 4 := by
      unfold margin; rw [he.distInt_eq]; simp
    rw [hm] at hy
    obtain ⟨k, hk⟩ := he
    have hne : ¬ IsOpener x0 := fun h => not_opener_and_entry ⟨h, ⟨k, hk⟩⟩
    have hy' : |y - ((k : ℝ) + 7 / 8)| < 1 / 4 := hk ▸ hy
    constructor
    · intro h
      exact ⟨fun ho => absurd ho hne, fun _ => by rw [hk]; exact (clear_iff_high hy').mp h⟩
    · rintro ⟨_, h2⟩
      exact (clear_iff_high hy').mpr (hk ▸ h2 ⟨k, hk⟩)
  · have hno : ¬ IsOpener x0 := fun h => by rw [h.distInt_eq] at hs; exact lt_irrefl _ hs
    have hne : ¬ IsEntry x0 := fun h => by rw [h.distInt_eq] at hs; exact lt_irrefl _ hs
    simp only [hno, hne, false_imp_iff, and_self, iff_true]
    unfold margin at hy
    rw [if_pos hs] at hy
    have h2 := PathLaws.distInt_lipschitz y x0
    linarith [neg_abs_le (distInt y - distInt x0)]

#print axioms runner_exact

/-! ## (1) The family, exactly -/

/-- The reading of runner `i` after the deformation `d + e δ` and the move `t0 + e τ` is the old reading plus
`e (A_i + e B_i)` [L]. -/
theorem reading_expand (d δ : ℝ) (t0 τ e : ℝ) :
    (d + e * δ) * (t0 + e * τ) = d * t0 + e * ((δ * t0 + d * τ) + e * (δ * τ)) := by ring

#print axioms reading_expand

/-- First-order coefficient. -/
noncomputable def coefA (d δ : ℝ) (t0 τ : ℝ) : ℝ := δ * t0 + d * τ

/-- Second-order coefficient. -/
noncomputable def coefB (δ : ℝ) (τ : ℝ) : ℝ := δ * τ

/-- **Exact survival of a touch** [L].  Let `t0` be lonely for `d`.  For `e > 0` such that every reading moves by less
than its margin (`e |A_i + e B_i| < margin (d_i t0)`), the deformed family `d + e δ` is lonely at `t0 + e τ` iff every
opener has `0 <= A_i + e B_i` and every entry has `A_i + e B_i <= 0`.  No first-order approximation is made. -/
theorem exact_touch_survival {ι : Type*} (d δ : ι → ℝ) (t0 τ e : ℝ) (he : 0 < e)
    (hl : ∀ i, (1 / 8 : ℝ) ≤ distInt (d i * t0))
    (hr : ∀ i, |e * (coefA (d i) (δ i) t0 τ + e * coefB (δ i) τ)| < margin (d i * t0)) :
    (∀ i, (1 / 8 : ℝ) ≤ distInt ((d i + e * δ i) * (t0 + e * τ))) ↔
      ((∀ i, IsOpener (d i * t0) → 0 ≤ coefA (d i) (δ i) t0 τ + e * coefB (δ i) τ) ∧
       (∀ i, IsEntry (d i * t0) → coefA (d i) (δ i) t0 τ + e * coefB (δ i) τ ≤ 0)) := by
  have key : ∀ i, (1 / 8 : ℝ) ≤ distInt ((d i + e * δ i) * (t0 + e * τ)) ↔
      ((IsOpener (d i * t0) → 0 ≤ coefA (d i) (δ i) t0 τ + e * coefB (δ i) τ) ∧
       (IsEntry (d i * t0) → coefA (d i) (δ i) t0 τ + e * coefB (δ i) τ ≤ 0)) := by
    intro i
    have hexp := reading_expand (d i) (δ i) t0 τ e
    unfold coefA coefB at hr ⊢
    have hy : |(d i + e * δ i) * (t0 + e * τ) - d i * t0| < margin (d i * t0) := by
      rw [hexp]; simpa using hr i
    rw [runner_exact (hl i) hy, hexp]
    have hiff : ∀ z : ℝ, (0 ≤ e * z ↔ 0 ≤ z) := fun z => mul_nonneg_iff_of_pos_left he
    have hiff' : ∀ z : ℝ, (e * z ≤ 0 ↔ z ≤ 0) := fun z => by
      rw [← neg_nonneg, ← neg_nonneg (a := z), ← mul_neg]; exact mul_nonneg_iff_of_pos_left he
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨fun ho => (hiff _).mp (by have := h1 ho; linarith),
             fun he' => (hiff' _).mp (by have := h2 he'; linarith)⟩
    · rintro ⟨h1, h2⟩
      exact ⟨fun ho => by have := (hiff _).mpr (h1 ho); linarith,
             fun he' => by have := (hiff' _).mpr (h2 he'); linarith⟩
  simp only [key, forall_and]

#print axioms exact_touch_survival

/-- The reach `e |A + e B|` is at most `e (|A| + |B|)` for `0 < e < 1`. -/
theorem reach_le {A B e : ℝ} (he : 0 < e) (he1 : e < 1) : |e * (A + e * B)| ≤ e * (|A| + |B|) := by
  rw [abs_mul, abs_of_pos he]
  apply mul_le_mul_of_nonneg_left _ he.le
  calc |A + e * B| ≤ |A| + |e * B| := abs_add_le _ _
    _ = |A| + e * |B| := by rw [abs_mul, abs_of_pos he]
    _ ≤ |A| + |B| := by
        have : e * |B| ≤ 1 * |B| := mul_le_mul_of_nonneg_right he1.le (abs_nonneg _)
        linarith

#print axioms reach_le

/-- **The stated range** [L]: the equivalence of `exact_touch_survival` holds for every `e` with `0 < e < 1` and
`e (|A_i| + |B_i|) < margin (d_i t0)` for all `i`. -/
theorem exact_touch_explicit {ι : Type*} (d δ : ι → ℝ) (t0 τ e : ℝ) (he : 0 < e) (he1 : e < 1)
    (hl : ∀ i, (1 / 8 : ℝ) ≤ distInt (d i * t0))
    (hr : ∀ i, e * (|coefA (d i) (δ i) t0 τ| + |coefB (δ i) τ|) < margin (d i * t0)) :
    (∀ i, (1 / 8 : ℝ) ≤ distInt ((d i + e * δ i) * (t0 + e * τ))) ↔
      ((∀ i, IsOpener (d i * t0) → 0 ≤ coefA (d i) (δ i) t0 τ + e * coefB (δ i) τ) ∧
       (∀ i, IsEntry (d i * t0) → coefA (d i) (δ i) t0 τ + e * coefB (δ i) τ ≤ 0)) :=
  exact_touch_survival d δ t0 τ e he hl fun i => lt_of_le_of_lt (reach_le he he1) (hr i)

#print axioms exact_touch_explicit

/-- For small `e > 0` the reach is below the margin, for every runner. -/
theorem reach_eventually {ι : Type*} [Finite ι] (d δ : ι → ℝ) (t0 τ : ℝ)
    (hl : ∀ i, (1 / 8 : ℝ) ≤ distInt (d i * t0)) :
    ∀ᶠ e in 𝓝[>] (0 : ℝ), 0 < e ∧ ∀ i, |e * (coefA (d i) (δ i) t0 τ + e * coefB (δ i) τ)| < margin (d i * t0) := by
  have h1 : ∀ᶠ e in 𝓝[>] (0 : ℝ), 0 < e := self_mem_nhdsWithin
  have h2 : ∀ᶠ e in 𝓝[>] (0 : ℝ), ∀ i, |e * (coefA (d i) (δ i) t0 τ + e * coefB (δ i) τ)| < margin (d i * t0) := by
    rw [Filter.eventually_all]
    intro i
    have hc : Continuous (fun e : ℝ => |e * (coefA (d i) (δ i) t0 τ + e * coefB (δ i) τ)|) := by fun_prop
    have h0 := hc.tendsto 0
    simp only [zero_mul, abs_zero] at h0
    exact nhdsWithin_le_nhds (h0.eventually (gt_mem_nhds (margin_pos (hl i))))
  exact h1.and h2

#print axioms reach_eventually

/-- **Exact survival for small `e`** [L]. -/
theorem exact_touch_eventually {ι : Type*} [Finite ι] (d δ : ι → ℝ) (t0 τ : ℝ)
    (hl : ∀ i, (1 / 8 : ℝ) ≤ distInt (d i * t0)) :
    ∀ᶠ e in 𝓝[>] (0 : ℝ),
      ((∀ i, (1 / 8 : ℝ) ≤ distInt ((d i + e * δ i) * (t0 + e * τ))) ↔
        ((∀ i, IsOpener (d i * t0) → 0 ≤ coefA (d i) (δ i) t0 τ + e * coefB (δ i) τ) ∧
         (∀ i, IsEntry (d i * t0) → coefA (d i) (δ i) t0 τ + e * coefB (δ i) τ ≤ 0))) := by
  filter_upwards [reach_eventually d δ t0 τ hl] with e ⟨he, hr⟩
  exact exact_touch_survival d δ t0 τ e he hl hr

#print axioms exact_touch_eventually

/-- **Strict first-order inequalities survive** [L]: openers with `A_i > 0` and entries with `A_i < 0` give a lonely
moved instant for every small `e > 0`. -/
theorem touch_survives_of_strict {ι : Type*} [Finite ι] (d δ : ι → ℝ) (t0 τ : ℝ)
    (hl : ∀ i, (1 / 8 : ℝ) ≤ distInt (d i * t0))
    (ho : ∀ i, IsOpener (d i * t0) → 0 < coefA (d i) (δ i) t0 τ)
    (hen : ∀ i, IsEntry (d i * t0) → coefA (d i) (δ i) t0 τ < 0) :
    ∀ᶠ e in 𝓝[>] (0 : ℝ), ∀ i, (1 / 8 : ℝ) ≤ distInt ((d i + e * δ i) * (t0 + e * τ)) := by
  have hc : ∀ i, Tendsto (fun e : ℝ => coefA (d i) (δ i) t0 τ + e * coefB (δ i) τ) (𝓝 0)
      (𝓝 (coefA (d i) (δ i) t0 τ)) := by
    intro i
    have : Continuous (fun e : ℝ => coefA (d i) (δ i) t0 τ + e * coefB (δ i) τ) := by fun_prop
    simpa using this.tendsto 0
  have hO : ∀ᶠ e in 𝓝[>] (0 : ℝ), ∀ i, IsOpener (d i * t0) → 0 ≤ coefA (d i) (δ i) t0 τ + e * coefB (δ i) τ := by
    rw [Filter.eventually_all]
    intro i
    by_cases h : IsOpener (d i * t0)
    · have := ((hc i).eventually (lt_mem_nhds (ho i h))).filter_mono (nhdsWithin_le_nhds (s := Set.Ioi (0:ℝ)))
      filter_upwards [this] with e he _ using he.le
    · exact Filter.Eventually.of_forall fun e hh => absurd hh h
  have hE : ∀ᶠ e in 𝓝[>] (0 : ℝ), ∀ i, IsEntry (d i * t0) → coefA (d i) (δ i) t0 τ + e * coefB (δ i) τ ≤ 0 := by
    rw [Filter.eventually_all]
    intro i
    by_cases h : IsEntry (d i * t0)
    · have := ((hc i).eventually (gt_mem_nhds (hen i h))).filter_mono (nhdsWithin_le_nhds (s := Set.Ioi (0:ℝ)))
      filter_upwards [this] with e he _ using he.le
    · exact Filter.Eventually.of_forall fun e hh => absurd hh h
  filter_upwards [exact_touch_eventually d δ t0 τ hl, hO, hE] with e h1 h2 h3
  exact h1.mpr ⟨h2, h3⟩

#print axioms touch_survives_of_strict

/-- **A strict first-order violation fails** [L]: an opener with `A_i < 0` or an entry with `A_i > 0` means the moved
instant is not lonely for every small `e > 0`. -/
theorem touch_fails_of_violation {ι : Type*} [Finite ι] (d δ : ι → ℝ) (t0 τ : ℝ)
    (hl : ∀ i, (1 / 8 : ℝ) ≤ distInt (d i * t0))
    (hv : (∃ i, IsOpener (d i * t0) ∧ coefA (d i) (δ i) t0 τ < 0) ∨
          (∃ i, IsEntry (d i * t0) ∧ 0 < coefA (d i) (δ i) t0 τ)) :
    ∀ᶠ e in 𝓝[>] (0 : ℝ), ¬ ∀ i, (1 / 8 : ℝ) ≤ distInt ((d i + e * δ i) * (t0 + e * τ)) := by
  rcases hv with ⟨i, hio, hA⟩ | ⟨i, hie, hA⟩
  · have hc : Continuous (fun e : ℝ => coefA (d i) (δ i) t0 τ + e * coefB (δ i) τ) := by fun_prop
    have h0 : Tendsto (fun e : ℝ => coefA (d i) (δ i) t0 τ + e * coefB (δ i) τ) (𝓝 0)
        (𝓝 (coefA (d i) (δ i) t0 τ)) := by simpa using hc.tendsto 0
    have hneg := (h0.eventually (gt_mem_nhds hA)).filter_mono (nhdsWithin_le_nhds (s := Set.Ioi (0:ℝ)))
    filter_upwards [exact_touch_eventually d δ t0 τ hl, hneg] with e h1 h2 hall
    have := ((h1.mp hall).1 i hio)
    linarith
  · have hc : Continuous (fun e : ℝ => coefA (d i) (δ i) t0 τ + e * coefB (δ i) τ) := by fun_prop
    have h0 : Tendsto (fun e : ℝ => coefA (d i) (δ i) t0 τ + e * coefB (δ i) τ) (𝓝 0)
        (𝓝 (coefA (d i) (δ i) t0 τ)) := by simpa using hc.tendsto 0
    have hpos := (h0.eventually (lt_mem_nhds hA)).filter_mono (nhdsWithin_le_nhds (s := Set.Ioi (0:ℝ)))
    filter_upwards [exact_touch_eventually d δ t0 τ hl, hpos] with e h1 h2 hall
    have := ((h1.mp hall).2 i hie)
    linarith

#print axioms touch_fails_of_violation

/-! ## (2) The interval system: one-dimensional Helly -/

/-- **The interval system in relative form** [L]: some `τ` is at least every `-(r_i t0)` (openers) and at most every
`-(r_j t0)` (entries) iff `r_j <= r_i` for every opener `i` and entry `j`.  Includes the cases with no opener or no entry. -/
theorem helly_aux {ι : Type*} [Fintype ι] (r : ι → ℝ) (t0 : ℝ) (ht : 0 < t0) (O E : ι → Prop) :
    (∃ τ : ℝ, (∀ i, O i → -(r i * t0) ≤ τ) ∧ (∀ j, E j → τ ≤ -(r j * t0))) ↔
      ∀ i j, O i → E j → r j ≤ r i := by
  constructor
  · rintro ⟨τ, h1, h2⟩ i j hi hj
    have := (h1 i hi).trans (h2 j hj)
    have h3 : r j * t0 ≤ r i * t0 := by linarith
    exact le_of_mul_le_mul_right h3 ht
  · intro h
    by_cases hO : ∃ i, O i
    · obtain ⟨i1, hi1⟩ := hO
      have hne : (Finset.univ.filter O).Nonempty := ⟨i1, by simpa using hi1⟩
      obtain ⟨i0, hi0, hmax⟩ := Finset.exists_max_image (Finset.univ.filter O) (fun i => -(r i * t0)) hne
      have hi0' : O i0 := by simpa using hi0
      refine ⟨-(r i0 * t0), fun i hi => hmax i (by simpa using hi), fun j hj => ?_⟩
      have := h i0 j hi0' hj
      nlinarith
    · by_cases hE : ∃ j, E j
      · obtain ⟨j1, hj1⟩ := hE
        have hne : (Finset.univ.filter E).Nonempty := ⟨j1, by simpa using hj1⟩
        obtain ⟨j0, hj0, hmin⟩ := Finset.exists_min_image (Finset.univ.filter E) (fun j => -(r j * t0)) hne
        refine ⟨-(r j0 * t0), fun i hi => absurd ⟨i, hi⟩ hO, fun j hj => hmin j (by simpa using hj)⟩
      · exact ⟨0, fun i hi => absurd ⟨i, hi⟩ hO, fun j hj => absurd ⟨j, hj⟩ hE⟩

#print axioms helly_aux

/-- **One-dimensional Helly for the touch** [L]: with positive disparities and `t0 > 0`, some `τ` satisfies all
first-order inequalities (`0 <= δ_i t0 + d_i τ` on openers, `δ_j t0 + d_j τ <= 0` on entries) iff for every opener `i`
and entry `j`, `δ_j / d_j <= δ_i / d_i`. -/
theorem helly_one_dim {ι : Type*} [Fintype ι] (d δ : ι → ℝ) (hd : ∀ i, 0 < d i) (t0 : ℝ) (ht : 0 < t0)
    (O E : ι → Prop) :
    (∃ τ : ℝ, (∀ i, O i → 0 ≤ δ i * t0 + d i * τ) ∧ (∀ j, E j → δ j * t0 + d j * τ ≤ 0)) ↔
      ∀ i j, O i → E j → δ j / d j ≤ δ i / d i := by
  rw [← helly_aux (fun i => δ i / d i) t0 ht O E]
  have key : ∀ i τ, δ i * t0 + d i * τ = d i * (δ i / d i * t0 + τ) := by
    intro i τ; have := (hd i).ne'; field_simp
  constructor <;> rintro ⟨τ, h1, h2⟩ <;> refine ⟨τ, fun i hi => ?_, fun j hj => ?_⟩
  · have := h1 i hi; rw [key] at this
    have := (mul_nonneg_iff_of_pos_left (hd i)).mp this; linarith
  · have := h2 j hj; rw [key] at this
    have hx : δ j / d j * t0 + τ ≤ 0 := by
      by_contra hc; push Not at hc; have := mul_pos (hd j) hc; linarith
    linarith
  · have := h1 i hi; rw [key]; exact mul_nonneg (hd i).le (by linarith)
  · have := h2 j hj; rw [key]; exact mul_nonpos_of_nonneg_of_nonpos (hd j).le (by linarith)

#print axioms helly_one_dim

/-- **Free touches** [L]: if no reading is an entry, or no reading is an opener, then for EVERY direction `δ` there is a
`τ` with all first-order inequalities strict, hence the moved instant is lonely for all small `e > 0`. -/
theorem free_touch_survives {ι : Type*} [Fintype ι] (d δ : ι → ℝ) (hd : ∀ i, 0 < d i) (t0 : ℝ)
    (hl : ∀ i, (1 / 8 : ℝ) ≤ distInt (d i * t0))
    (hfree : (∀ i, ¬ IsEntry (d i * t0)) ∨ (∀ i, ¬ IsOpener (d i * t0))) :
    ∃ τ : ℝ, ∀ᶠ e in 𝓝[>] (0 : ℝ), ∀ i, (1 / 8 : ℝ) ≤ distInt ((d i + e * δ i) * (t0 + e * τ)) := by
  set S : ℝ := ∑ i, |δ i / d i * t0| with hS
  have hb : ∀ i, |δ i / d i * t0| ≤ S := fun i =>
    Finset.single_le_sum (f := fun i => |δ i / d i * t0|) (fun i _ => abs_nonneg _) (Finset.mem_univ i)
  have key : ∀ i τ, coefA (d i) (δ i) t0 τ = d i * (δ i / d i * t0 + τ) := by
    intro i τ; unfold coefA; have := (hd i).ne'; field_simp
  rcases hfree with hf | hf
  · refine ⟨1 + S, touch_survives_of_strict d δ t0 _ hl ?_ (fun i hi => absurd hi (hf i))⟩
    intro i _
    rw [key]
    apply mul_pos (hd i)
    have := hb i
    have := neg_abs_le (δ i / d i * t0)
    linarith
  · refine ⟨-(1 + S), touch_survives_of_strict d δ t0 _ hl (fun i hi => absurd hi (hf i)) ?_⟩
    intro i _
    rw [key]
    apply mul_neg_of_pos_of_neg (hd i)
    have := hb i
    have := le_abs_self (δ i / d i * t0)
    linarith

#print axioms free_touch_survives

/-- **The scaling direction is a second-order obstruction for affine moves** [L].  If `δ = c d` with `c ≠ 0` and the
touch has both an opener and an entry, then for EVERY `τ` the affine move `t0 + e τ` fails for all small `e > 0`
(the first-order inequalities force `τ = -c t0`, and then `B_i = -c² d_i t0 < 0` makes the opener retreat).  The
instant itself survives along the non-affine path `t0/(1 + e c)` (`scaling_nonaffine_survives`). -/
theorem scaling_B_obstruction {ι : Type*} [Finite ι] (d : ι → ℝ) (hd : ∀ i, 0 < d i) (t0 : ℝ) (ht : 0 < t0) (c : ℝ) (hc : c ≠ 0)
    (hl : ∀ i, (1 / 8 : ℝ) ≤ distInt (d i * t0)) (i0 j0 : ι) (hi0 : IsOpener (d i0 * t0))
    (hj0 : IsEntry (d j0 * t0)) (τ : ℝ) :
    ∀ᶠ e in 𝓝[>] (0 : ℝ), ¬ ∀ i, (1 / 8 : ℝ) ≤ distInt ((d i + e * (c * d i)) * (t0 + e * τ)) := by
  have hA : ∀ i, coefA (d i) (c * d i) t0 τ = d i * (c * t0 + τ) := by intro i; unfold coefA; ring
  rcases lt_trichotomy (c * t0 + τ) 0 with h | h | h
  · exact touch_fails_of_violation d (fun i => c * d i) t0 τ hl
      (Or.inl ⟨i0, hi0, by rw [hA]; exact mul_neg_of_pos_of_neg (hd i0) h⟩)
  · filter_upwards [exact_touch_eventually d (fun i => c * d i) t0 τ hl, self_mem_nhdsWithin] with e h1 he hall
    have := (h1.mp hall).1 i0 hi0
    have hB : coefB (c * d i0) τ = -(c ^ 2 * d i0 * t0) := by
      unfold coefB; have : τ = -(c * t0) := by linarith
      rw [this]; ring
    rw [hA, h, hB] at this
    have he' : 0 < e := he
    have hpos : 0 < c ^ 2 := by positivity
    have : 0 < c ^ 2 * d i0 * t0 * e := by
      have := hd i0
      positivity
    linarith
  · exact touch_fails_of_violation d (fun i => c * d i) t0 τ hl
      (Or.inr ⟨j0, hj0, by rw [hA]; exact mul_pos (hd j0) h⟩)

#print axioms scaling_B_obstruction

/-- **The scaling direction survives along `t0/(1 + e c)`** [L]: every reading is unchanged. -/
theorem scaling_nonaffine_survives {ι : Type*} (d : ι → ℝ) (t0 c e : ℝ) (hec : 1 + e * c ≠ 0)
    (hl : ∀ i, (1 / 8 : ℝ) ≤ distInt (d i * t0)) (i : ι) :
    (1 / 8 : ℝ) ≤ distInt ((d i + e * (c * d i)) * (t0 / (1 + e * c))) := by
  have : (d i + e * (c * d i)) * (t0 / (1 + e * c)) = d i * t0 := by
    field_simp
  rw [this]; exact hl i

#print axioms scaling_nonaffine_survives

/-! ## (3) The AP -/

section Residues

theorem div8_opener_iff (m : ℕ) : IsOpener ((m : ℝ) / 8) ↔ m % 8 = 1 := by
  constructor
  · rintro ⟨k, hk⟩
    have h1 : (m : ℝ) = 8 * k + 1 := by linarith
    have h2 : (m : ℤ) = 8 * k + 1 := by exact_mod_cast h1
    omega
  · intro h
    have hm : m = 8 * (m / 8) + 1 := by omega
    have : (m : ℝ) = 8 * ((m / 8 : ℕ) : ℝ) + 1 := by exact_mod_cast hm
    generalize m / 8 = n at this
    refine ⟨(n : ℤ), ?_⟩
    rw [Int.cast_natCast]; linarith

theorem div8_entry_iff (m : ℕ) : IsEntry ((m : ℝ) / 8) ↔ m % 8 = 7 := by
  constructor
  · rintro ⟨k, hk⟩
    have h1 : (m : ℝ) = 8 * k + 7 := by linarith
    have h2 : (m : ℤ) = 8 * k + 7 := by exact_mod_cast h1
    omega
  · intro h
    have hm : m = 8 * (m / 8) + 7 := by omega
    have : (m : ℝ) = 8 * ((m / 8 : ℕ) : ℝ) + 7 := by exact_mod_cast hm
    generalize m / 8 = n at this
    refine ⟨(n : ℤ), ?_⟩
    rw [Int.cast_natCast]; linarith

theorem div8_clear (m : ℕ) (h : m % 8 ≠ 0) : (1 / 8 : ℝ) ≤ distInt ((m : ℝ) / 8) := by
  have := Fresh.distInt_int_div_eight (z := (m : ℤ)) (by omega)
  simpa using this

/-- A reading `m/8` with `2 <= m mod 8 <= 6` is strictly clear (indeed at distance `>= 2/8`). -/
theorem div8_slack (m : ℕ) (h2 : 2 ≤ m % 8) (h6 : m % 8 ≤ 6) : (1 / 8 : ℝ) < distInt ((m : ℝ) / 8) := by
  have hm : (m : ℝ) = 8 * ((m / 8 : ℕ) : ℝ) + ((m % 8 : ℕ) : ℝ) := by
    have := Nat.div_add_mod m 8
    have h' : ((8 * (m / 8) + m % 8 : ℕ) : ℝ) = (m : ℝ) := by rw [this]
    push_cast at h'; linarith
  have r2 : (2 : ℝ) ≤ ((m % 8 : ℕ) : ℝ) := by exact_mod_cast h2
  have r6 : ((m % 8 : ℕ) : ℝ) ≤ 6 := by exact_mod_cast h6
  generalize m / 8 = n at hm
  generalize m % 8 = r at hm r2 r6
  have : (2 / 8 : ℝ) ≤ distInt ((m : ℝ) / 8) := by
    rw [le_distInt_iff]
    intro z
    rcases le_or_gt z (n : ℤ) with hz | hz
    · have h1 : (z : ℝ) ≤ ((n : ℤ) : ℝ) := Int.cast_le.mpr hz
      rw [Int.cast_natCast] at h1
      rw [abs_of_nonneg (by linarith)]; linarith
    · have h1 : (((n : ℤ) + 1 : ℤ) : ℝ) ≤ (z : ℝ) := Int.cast_le.mpr (Int.add_one_le_iff.mpr hz)
      rw [Int.cast_add, Int.cast_natCast, Int.cast_one] at h1
      rw [abs_of_nonpos (by linarith)]; linarith
  linarith

#print axioms div8_opener_iff
#print axioms div8_entry_iff
#print axioms div8_clear
#print axioms div8_slack

end Residues

open Fresh.PairLaw in
/-- **The critical set of the AP touch `a/8`** [L]: for odd `a <= 7` and `1 <= j <= 7`, the reading `j a/8` is clear; it
is an opener iff `j = a` and an entry iff `j + a = 8`.  (Every other reading is slack by `div8_slack`.) -/
theorem ap_classes {a : ℕ} (ha : a % 2 = 1) (ha7 : a ≤ 7) {j : ℕ} (hj1 : 1 ≤ j) (hj7 : j ≤ 7) :
    (1 / 8 : ℝ) ≤ distInt ((j : ℝ) * ((a : ℝ) / 8)) ∧
    (IsOpener ((j : ℝ) * ((a : ℝ) / 8)) ↔ j = a) ∧ (IsEntry ((j : ℝ) * ((a : ℝ) / 8)) ↔ j + a = 8) := by
  -- [PROVISIONAL: counting tool] residues of `j a` mod 8 (PairLaw.res_one / res_seven), supporting `ap_classes` only.
  have e : (j : ℝ) * ((a : ℝ) / 8) = ((j * a : ℕ) : ℝ) / 8 := by push_cast; ring
  rw [e]
  refine ⟨div8_clear _ (res_ne_zero ha hj1 hj7), ?_, ?_⟩
  · rw [div8_opener_iff]
    exact ⟨res_one ha ha7 hj1 hj7, fun h => by subst h; exact odd_sq_mod8 ha⟩
  · rw [div8_entry_iff]
    exact ⟨res_seven ha ha7 hj1 hj7, fun h => mirror_res (b := j) ha (by omega)⟩

#print axioms ap_classes

/-- The AP disparities of the first runner: runner `i : Fin 7` has disparity `i + 1`. -/
noncomputable def apd (i : Fin 7) : ℝ := ((i : ℕ) : ℝ) + 1

/-- The survival form of the class `a` with mirror `b`: relative change of the opener minus that of the entry. -/
noncomputable def sigma (δ : ℕ → ℝ) (a b : ℕ) : ℝ := δ a / a - δ b / b

theorem apd_pos (i : Fin 7) : 0 < apd i := by unfold apd; positivity

theorem apd_val {j : ℕ} (hj1 : 1 ≤ j) (hj7 : j ≤ 7) : apd ⟨j - 1, by omega⟩ = (j : ℝ) := by
  unfold apd; simp only [Nat.cast_sub hj1]; push_cast; ring

theorem apd_eq (i : Fin 7) : apd i = (((i : ℕ) + 1 : ℕ) : ℝ) := by unfold apd; push_cast; ring

/-- The classes of `ap_classes`, for the indexed disparities [L]. -/
theorem ap_classes_fin {a : ℕ} (ha : a % 2 = 1) (ha7 : a ≤ 7) (i : Fin 7) :
    (1 / 8 : ℝ) ≤ distInt (apd i * ((a : ℝ) / 8)) ∧
    (IsOpener (apd i * ((a : ℝ) / 8)) ↔ (i : ℕ) + 1 = a) ∧
    (IsEntry (apd i * ((a : ℝ) / 8)) ↔ (i : ℕ) + 1 + a = 8) := by
  rw [apd_eq]
  exact ap_classes ha ha7 (by omega) (by omega)

#print axioms ap_classes_fin

/-- **First-order survival at the AP touch `a/8`** [L]: some `τ` satisfies the opener and entry inequalities iff
`σ_a(δ) >= 0`, i.e. `δ_b / b <= δ_a / a` (`b = 8 - a`). -/
theorem ap_first_order_iff {a b : ℕ} (ha : a % 2 = 1) (ha7 : a ≤ 7) (hab : a + b = 8) (δ : ℕ → ℝ) :
    (∃ τ : ℝ, (∀ i : Fin 7, IsOpener (apd i * ((a : ℝ) / 8)) → 0 ≤ coefA (apd i) (δ ((i : ℕ) + 1)) ((a : ℝ) / 8) τ) ∧
      (∀ i : Fin 7, IsEntry (apd i * ((a : ℝ) / 8)) → coefA (apd i) (δ ((i : ℕ) + 1)) ((a : ℝ) / 8) τ ≤ 0)) ↔
      0 ≤ sigma δ a b := by
  have ht : (0 : ℝ) < (a : ℝ) / 8 := by
    have : (1 : ℝ) ≤ a := by exact_mod_cast (show 1 ≤ a by omega)
    positivity
  unfold coefA
  rw [helly_one_dim apd (fun i => δ ((i : ℕ) + 1)) apd_pos _ ht]
  unfold sigma
  constructor
  · intro h
    have := h ⟨a - 1, by omega⟩ ⟨b - 1, by omega⟩
      ((ap_classes_fin ha ha7 _).2.1.mpr (by simp; omega)) ((ap_classes_fin ha ha7 _).2.2.mpr (by simp; omega))
    rw [apd_val (by omega) (by omega), apd_val (by omega) (by omega)] at this
    simp only [Nat.sub_add_cancel (show 1 ≤ a by omega), Nat.sub_add_cancel (show 1 ≤ b by omega)] at this
    linarith
  · intro h i j hi hj
    have hi' := (ap_classes_fin ha ha7 i).2.1.mp hi
    have hj' := (ap_classes_fin ha ha7 j).2.2.mp hj
    have e1 : apd i = (a : ℝ) := by rw [apd_eq, hi']
    have e2 : apd j = (b : ℝ) := by rw [apd_eq]; congr 1; omega
    have e3 : (i : ℕ) + 1 = a := hi'
    have e4 : (j : ℕ) + 1 = b := by omega
    simp only [e1, e2, e3, e4]
    linarith

#print axioms ap_first_order_iff

/-- **Antisymmetry** [L]: `σ_b = -σ_a`. -/
theorem sigma_antisymm (δ : ℕ → ℝ) (a b : ℕ) : sigma δ b a = -sigma δ a b := by
  unfold sigma; ring

/-- **For every direction one of each mirror pair survives to first order** [L]. -/
theorem ap_mirror_survival {a b : ℕ} (ha : a % 2 = 1) (ha7 : a ≤ 7) (hab : a + b = 8) (δ : ℕ → ℝ) :
    (∃ τ : ℝ, (∀ i : Fin 7, IsOpener (apd i * ((a : ℝ) / 8)) → 0 ≤ coefA (apd i) (δ ((i : ℕ) + 1)) ((a : ℝ) / 8) τ) ∧
      (∀ i : Fin 7, IsEntry (apd i * ((a : ℝ) / 8)) → coefA (apd i) (δ ((i : ℕ) + 1)) ((a : ℝ) / 8) τ ≤ 0)) ∨
    (∃ τ : ℝ, (∀ i : Fin 7, IsOpener (apd i * ((b : ℝ) / 8)) → 0 ≤ coefA (apd i) (δ ((i : ℕ) + 1)) ((b : ℝ) / 8) τ) ∧
      (∀ i : Fin 7, IsEntry (apd i * ((b : ℝ) / 8)) → coefA (apd i) (δ ((i : ℕ) + 1)) ((b : ℝ) / 8) τ ≤ 0)) := by
  have hb : b % 2 = 1 := by omega
  have hb7 : b ≤ 7 := by omega
  rw [ap_first_order_iff ha ha7 hab, ap_first_order_iff hb hb7 (b := a) (by omega)]
  rw [sigma_antisymm δ a b]
  rcases le_total 0 (sigma δ a b) with h | h
  · exact Or.inl h
  · exact Or.inr (by linarith)

#print axioms sigma_antisymm
#print axioms ap_mirror_survival

/-- **Strict survival displaces the touch** [L]: if `σ_a(δ) > 0` then there is `τ` such that for every small `e > 0`
the disparity set `{j + e δ_j}` (`j = 1..7`) is lonely at the moved instant `a/8 + e τ`. -/
theorem ap_displaced {a b : ℕ} (ha : a % 2 = 1) (ha7 : a ≤ 7) (hab : a + b = 8) (δ : ℕ → ℝ)
    (hσ : 0 < sigma δ a b) :
    ∃ τ : ℝ, ∀ᶠ e in 𝓝[>] (0 : ℝ),
      Cascade.LonelyAt (PairLaw.pds (fun j => (j : ℝ) + e * δ j)) ((a : ℝ) / 8 + e * τ) := by
  have ha1 : (1 : ℝ) ≤ a := by exact_mod_cast (show 1 ≤ a by omega)
  have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast (show 1 ≤ b by omega)
  have ht : (0 : ℝ) < (a : ℝ) / 8 := by positivity
  set t0 : ℝ := (a : ℝ) / 8 with ht0
  set ra : ℝ := δ a / a with hra
  set rb : ℝ := δ b / b with hrb
  have hda : δ a = ra * a := by rw [hra]; field_simp
  have hdb : δ b = rb * b := by rw [hrb]; field_simp
  have hσ' : 0 < ra - rb := by unfold sigma at hσ; linarith
  set τ : ℝ := -((ra + rb) / 2) * t0 with hτ
  refine ⟨τ, ?_⟩
  have hl : ∀ i : Fin 7, (1 / 8 : ℝ) ≤ distInt (apd i * t0) := fun i => (ap_classes_fin ha ha7 i).1
  have key := touch_survives_of_strict apd (fun i => δ ((i : ℕ) + 1)) t0 τ hl ?_ ?_
  · filter_upwards [key] with e he
    rw [PairLaw.lonelyAt_pds_iff]
    intro j hj1 hj7
    have := he ⟨j - 1, by omega⟩
    rw [apd_val hj1 hj7] at this
    simp only [Nat.sub_add_cancel hj1] at this
    exact this
  · intro i hi
    have hi' := (ap_classes_fin ha ha7 i).2.1.mp hi
    have e1 : apd i = (a : ℝ) := by rw [apd_eq, hi']
    have e3 : (i : ℕ) + 1 = a := hi'
    simp only [e1, e3]
    unfold coefA
    rw [hda, hτ]
    have : ra * a * t0 + a * (-((ra + rb) / 2) * t0) = a * t0 * ((ra - rb) / 2) := by ring
    rw [this]
    positivity
  · intro i hi
    have hi' := (ap_classes_fin ha ha7 i).2.2.mp hi
    have e2 : apd i = (b : ℝ) := by rw [apd_eq]; congr 1; omega
    have e4 : (i : ℕ) + 1 = b := by omega
    simp only [e2, e4]
    unfold coefA
    rw [hdb, hτ]
    have : rb * b * t0 + b * (-((ra + rb) / 2) * t0) = -(b * t0 * ((ra - rb) / 2)) := by ring
    rw [this]
    have : 0 < b * t0 * ((ra - rb) / 2) := by positivity
    linarith

#print axioms ap_displaced

/-- **The survival form is the linearisation of `a d_b <= b d_a`** [L].  For the affine deformation `d_j = j + e δ_j`,
`b d_a - a d_b = e (a b) σ_a(δ)` exactly (it is affine in `e`: no higher-order term). -/
theorem survival_form_is_linearisation (δ : ℕ → ℝ) {a b : ℕ} (ha1 : 1 ≤ a) (hb1 : 1 ≤ b) (e : ℝ) :
    (b : ℝ) * ((a : ℝ) + e * δ a) - (a : ℝ) * ((b : ℝ) + e * δ b) = e * ((a : ℝ) * b) * sigma δ a b := by
  have h1 : (a : ℝ) ≠ 0 := by have : (1 : ℝ) ≤ a := by exact_mod_cast ha1
                              linarith
  have h2 : (b : ℝ) ≠ 0 := by have : (1 : ℝ) ≤ b := by exact_mod_cast hb1
                              linarith
  unfold sigma
  field_simp
  ring

#print axioms survival_form_is_linearisation

/-- **Reconciliation with `PairLaw`** [L]: for `e > 0` and the deformation `d_j = j + e δ_j` (positive at `a, b`),
`PairLaw.uA d a <= PairLaw.wA d a b` (the interval of the class is nonempty) iff `0 <= σ_a(δ)`: the exact condition for
the pair, `a d_b <= b d_a`, equals the first-order survival condition. -/
theorem pair_law_is_survival_form (δ : ℕ → ℝ) {a b : ℕ} (ha1 : 1 ≤ a) (hb1 : 1 ≤ b) (e : ℝ) (he : 0 < e)
    (hda : 0 < (a : ℝ) + e * δ a) (hdb : 0 < (b : ℝ) + e * δ b) :
    PairLaw.uA (fun j => (j : ℝ) + e * δ j) a ≤ PairLaw.wA (fun j => (j : ℝ) + e * δ j) a b ↔ 0 ≤ sigma δ a b := by
  rw [PairLaw.u_le_w_iff (fun j => (j : ℝ) + e * δ j) hda hdb ha1]
  have hab : (0 : ℝ) < (a : ℝ) * b := by
    have : (1 : ℝ) ≤ a := by exact_mod_cast ha1
    have : (1 : ℝ) ≤ b := by exact_mod_cast hb1
    positivity
  have key := survival_form_is_linearisation δ ha1 hb1 e
  constructor
  · intro h
    have h0 : 0 ≤ e * ((a : ℝ) * b) * sigma δ a b := by rw [← key]; linarith
    have : 0 < e * ((a : ℝ) * b) := by positivity
    exact (mul_nonneg_iff_of_pos_left this).mp h0
  · intro h
    have : 0 ≤ e * ((a : ℝ) * b) * sigma δ a b := by
      have : 0 < e * ((a : ℝ) * b) := by positivity
      positivity
    linarith

#print axioms pair_law_is_survival_form

/-! ## (4) Conjugate touches -/

/-- Multiplying the instant by `N ≡ 7 (mod 8)` swaps openers and entries [L]. -/
theorem scale_flip {N : ℤ} (hN : N % 8 = 7) {x : ℝ} :
    (IsOpener x → IsEntry ((N : ℝ) * x)) ∧ (IsEntry x → IsOpener ((N : ℝ) * x)) := by
  obtain ⟨n, rfl⟩ : ∃ n, N = 8 * n + 7 := ⟨N / 8, by omega⟩
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨(8 * n + 7) * k + n, by push_cast; ring⟩
  · rintro ⟨k, rfl⟩
    exact ⟨(8 * n + 7) * k + 7 * n + 6, by push_cast; ring⟩

/-- Multiplying the instant by `N ≡ 1 (mod 8)` keeps openers and entries [L]. -/
theorem scale_keep {N : ℤ} (hN : N % 8 = 1) {x : ℝ} :
    (IsOpener x → IsOpener ((N : ℝ) * x)) ∧ (IsEntry x → IsEntry ((N : ℝ) * x)) := by
  obtain ⟨n, rfl⟩ : ∃ n, N = 8 * n + 1 := ⟨N / 8, by omega⟩
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨(8 * n + 1) * k + n, by push_cast; ring⟩
  · rintro ⟨k, rfl⟩
    exact ⟨(8 * n + 1) * k + 7 * n, by push_cast; ring⟩

#print axioms scale_flip
#print axioms scale_keep

theorem mirror_seven {x : ℝ} : (IsOpener x → IsEntry (7 * x)) ∧ (IsEntry x → IsOpener (7 * x)) := by
  have := scale_flip (N := 7) (by norm_num) (x := x)
  simpa using this

#print axioms mirror_seven

/-- **A pair always has its swapped pair** [L]: (opener `d_i t`, entry `d_j t`) at some `t > 0` iff (entry `d_i t'`,
opener `d_j t'`) at some `t' > 0`; the instants are related by `t' = 7 t`.  No ratio condition is needed beyond what the
first pair already satisfies. -/
theorem conjugate_pair_exists (di dj : ℝ) :
    (∃ t : ℝ, 0 < t ∧ IsOpener (di * t) ∧ IsEntry (dj * t)) ↔
      (∃ t : ℝ, 0 < t ∧ IsEntry (di * t) ∧ IsOpener (dj * t)) := by
  have ei : ∀ (d t : ℝ), d * (7 * t) = 7 * (d * t) := fun d t => by ring
  constructor
  · rintro ⟨t, ht, h1, h2⟩
    refine ⟨7 * t, by positivity, ?_, ?_⟩
    · rw [ei]; exact (mirror_seven (x := di * t)).1 h1
    · rw [ei]; exact (mirror_seven (x := dj * t)).2 h2
  · rintro ⟨t, ht, h1, h2⟩
    refine ⟨7 * t, by positivity, ?_, ?_⟩
    · rw [ei]; exact (mirror_seven (x := di * t)).2 h1
    · rw [ei]; exact (mirror_seven (x := dj * t)).1 h2

#print axioms conjugate_pair_exists

/-- The integer relation behind an (opener, entry) pair of commensurable disparities [L]. -/
theorem opener_entry_relation {p q : ℕ} {c t : ℝ} (hc : 0 < c) (ht : 0 < t)
    (h1 : IsOpener ((p : ℝ) * c * t)) (h2 : IsEntry ((q : ℝ) * c * t)) :
    ∃ k k' : ℤ, (q : ℤ) * (8 * k + 1) = (p : ℤ) * (8 * k' + 7) := by
  obtain ⟨k, hk⟩ := h1
  obtain ⟨k', hk'⟩ := h2
  refine ⟨k, k', ?_⟩
  have : (q : ℝ) * (8 * k + 1) = (p : ℝ) * (8 * k' + 7) := by
    have e1 : (q : ℝ) * (8 * (k : ℝ) + 1) = 8 * ((q : ℝ) * ((k : ℝ) + 1 / 8)) := by ring
    have e2 : (p : ℝ) * (8 * (k' : ℝ) + 7) = 8 * ((p : ℝ) * ((k' : ℝ) + 7 / 8)) := by ring
    rw [e1, e2, ← hk, ← hk']; ring
  exact_mod_cast this

#print axioms opener_entry_relation

/-- **The ratio condition, necessary** [L]: an (opener, entry) pair `p c t`, `q c t` forces `p + q ≡ 0 (mod 8)`. -/
theorem ratio_necessary {p q : ℕ} {c t : ℝ} (hc : 0 < c) (ht : 0 < t)
    (h1 : IsOpener ((p : ℝ) * c * t)) (h2 : IsEntry ((q : ℝ) * c * t)) : (p + q) % 8 = 0 := by
  obtain ⟨k, k', h⟩ := opener_entry_relation hc ht h1 h2
  have e : (q : ℤ) + 8 * ((q : ℤ) * k) = 7 * (p : ℤ) + 8 * ((p : ℤ) * k') := by linarith
  -- [PROVISIONAL: counting tool] residues mod 8 (omega), supporting `ratio_necessary` only.
  generalize (q : ℤ) * k = X at e
  generalize (p : ℤ) * k' = Y at e
  omega

#print axioms ratio_necessary

/-- **The ratio condition, sufficient for odd `p`** [L]: `p` odd and `p + q ≡ 0 (mod 8)` give the instant
`t = p/(8c)` with `p c t = p²/8` an opener and `q c t = p q/8` an entry. -/
theorem ratio_sufficient {p q : ℕ} (hp : p % 2 = 1) (hpq : (p + q) % 8 = 0) {c : ℝ} (hc : 0 < c) :
    ∃ t : ℝ, 0 < t ∧ IsOpener ((p : ℝ) * c * t) ∧ IsEntry ((q : ℝ) * c * t) := by
  have hp1 : 1 ≤ p := by omega
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp1
  refine ⟨(p : ℝ) / (8 * c), by positivity, ?_, ?_⟩
  · have e : (p : ℝ) * c * ((p : ℝ) / (8 * c)) = ((p * p : ℕ) : ℝ) / 8 := by
      push_cast; field_simp
    rw [e, div8_opener_iff]
    exact PairLaw.odd_sq_mod8 hp
  · have e : (q : ℝ) * c * ((p : ℝ) / (8 * c)) = ((q * p : ℕ) : ℝ) / 8 := by
      push_cast; field_simp
    rw [e, div8_entry_iff]
    have h1 := PairLaw.odd_sq_mod8 hp
    have h2 : 8 ∣ (p + q) * p := Dvd.dvd.mul_right (Nat.dvd_of_mod_eq_zero hpq) p
    have h3 : (p + q) * p = q * p + p * p := by ring
    rw [h3] at h2
    have := Nat.mod_eq_zero_of_dvd h2
    -- [PROVISIONAL: counting tool] residues mod 8, supporting `ratio_sufficient` only.
    generalize q * p = X at this ⊢
    generalize p * p = Y at this h1
    omega

#print axioms ratio_sufficient

/-- **The ratio condition** [L]: for `p` odd, readings `p c t` and `q c t` are (opener, entry) at some `t > 0` iff
`p + q ≡ 0 (mod 8)`. -/
theorem ratio_condition {p q : ℕ} (hp : p % 2 = 1) {c : ℝ} (hc : 0 < c) :
    (∃ t : ℝ, 0 < t ∧ IsOpener ((p : ℝ) * c * t) ∧ IsEntry ((q : ℝ) * c * t)) ↔ (p + q) % 8 = 0 :=
  ⟨fun ⟨_, ht, h1, h2⟩ => ratio_necessary hc ht h1 h2, fun h => ratio_sufficient hp h hc⟩

/-- **The swapped roles have the same condition** [L]: (entry `p c t`, opener `q c t`) iff `p + q ≡ 0 (mod 8)`
(`p` odd).  So the conjugate of a pair touch exists exactly when the pair touch does. -/
theorem ratio_condition_swapped {p q : ℕ} (hp : p % 2 = 1) {c : ℝ} (hc : 0 < c) :
    (∃ t : ℝ, 0 < t ∧ IsEntry ((p : ℝ) * c * t) ∧ IsOpener ((q : ℝ) * c * t)) ↔ (p + q) % 8 = 0 := by
  rw [← ratio_condition hp hc, ← conjugate_pair_exists]

#print axioms ratio_condition
#print axioms ratio_condition_swapped

/-- **`p + q ≡ 0 (mod 8)` alone is not sufficient** [L]: `p = 2`, `q = 6` has `8 ∣ p + q` and no (opener, entry)
instant (the reduced ratio is `1 : 3`, and `1 + 3 = 4`). -/
theorem ratio_condition_needs_coprime {c : ℝ} (hc : 0 < c) :
    (2 + 6) % 8 = 0 ∧ ¬ ∃ t : ℝ, 0 < t ∧ IsOpener (((2 : ℕ) : ℝ) * c * t) ∧ IsEntry (((6 : ℕ) : ℝ) * c * t) := by
  refine ⟨by norm_num, ?_⟩
  rintro ⟨t, ht, h1, h2⟩
  obtain ⟨k, k', h⟩ := opener_entry_relation hc ht h1 h2
  simp only [Nat.cast_ofNat] at h
  omega

#print axioms ratio_condition_needs_coprime

/-- Reflection: `N - x` swaps the roles [L]. -/
theorem reflect_roles (N : ℤ) (x : ℝ) :
    (IsOpener x ↔ IsEntry ((N : ℝ) - x)) ∧ (IsEntry x ↔ IsOpener ((N : ℝ) - x)) := by
  constructor
  · constructor
    · rintro ⟨k, hk⟩; exact ⟨N - k - 1, by push_cast; rw [hk]; ring⟩
    · rintro ⟨k, hk⟩; exact ⟨N - k - 1, by push_cast; linarith⟩
  · constructor
    · rintro ⟨k, hk⟩; exact ⟨N - k - 1, by push_cast; rw [hk]; ring⟩
    · rintro ⟨k, hk⟩; exact ⟨N - k - 1, by push_cast; linarith⟩

theorem distInt_reflect (N : ℤ) (x : ℝ) : distInt ((N : ℝ) - x) = distInt x := by
  have := distInt_add_int (-x) N
  rw [distInt_neg] at this
  rw [← this]; ring_nf

#print axioms reflect_roles
#print axioms distInt_reflect

/-- **The mirror of a commensurable family** [L].  If every disparity has `d_i T ∈ ℤ` (`T > 0`), then for every instant
`t0` there is `t' > 0` (namely `m T - t0`) at which every reading has the same circle distance (so a lonely instant goes to
a lonely instant) and openers become entries and entries become openers.  For the AP, `T = 1`. -/
theorem commensurable_mirror {ι : Type*} (d : ι → ℝ) (T : ℝ) (hT : 0 < T) (hint : ∀ i, ∃ n : ℤ, d i * T = n)
    (t0 : ℝ) :
    ∃ t' : ℝ, 0 < t' ∧ (∀ i, distInt (d i * t') = distInt (d i * t0)) ∧
      (∀ i, IsOpener (d i * t0) ↔ IsEntry (d i * t')) ∧ (∀ i, IsEntry (d i * t0) ↔ IsOpener (d i * t')) := by
  obtain ⟨m, hm⟩ := exists_nat_gt (t0 / T)
  have hmT : t0 < (m : ℝ) * T := by rwa [div_lt_iff₀ hT] at hm
  refine ⟨(m : ℝ) * T - t0, by linarith, ?_, ?_, ?_⟩
  all_goals
    intro i
    obtain ⟨n, hn⟩ := hint i
    have e : d i * ((m : ℝ) * T - t0) = (((m : ℤ) * n : ℤ) : ℝ) - d i * t0 := by
      push_cast; rw [mul_sub, ← hn]; ring
    rw [e]
  · exact distInt_reflect _ _
  · exact (reflect_roles _ _).1
  · exact (reflect_roles _ _).2

#print axioms commensurable_mirror

/-- **The AP mirror instant** [L]: the instant `(8 - a)/8` has the roles of `a/8` swapped, for every runner. -/
theorem ap_mirror_instant {a : ℕ} (ha7 : a ≤ 8) (i : Fin 7) :
    (IsOpener (apd i * ((a : ℝ) / 8)) ↔ IsEntry (apd i * (((8 - a : ℕ) : ℝ) / 8))) ∧
    (IsEntry (apd i * ((a : ℝ) / 8)) ↔ IsOpener (apd i * (((8 - a : ℕ) : ℝ) / 8))) := by
  have e : apd i * (((8 - a : ℕ) : ℝ) / 8) = (((i : ℕ) + 1 : ℤ) : ℝ) - apd i * ((a : ℝ) / 8) := by
    unfold apd; rw [Nat.cast_sub ha7]; push_cast; ring
  rw [e]
  exact reflect_roles _ _

#print axioms ap_mirror_instant

/-- **A touch with no conjugate partner of any kind** [L]: disparities `1, 2, 4` at the instant `1/8` are lonely, the
first reading is an opener and NO reading is an entry; so there is no (opener, entry) pair at all, and
`free_touch_survives` applies: every direction survives, strictly. -/
theorem free_example :
    let d : Fin 3 → ℝ := ![1, 2, 4]
    (∀ i, (1 / 8 : ℝ) ≤ distInt (d i * (1 / 8))) ∧ IsOpener (d 0 * (1 / 8)) ∧ (∀ i, ¬ IsEntry (d i * (1 / 8))) := by
  intro d
  have e0 : d 0 * (1 / 8) = ((1 : ℕ) : ℝ) / 8 := by simp [d]
  have e1 : d 1 * (1 / 8) = ((2 : ℕ) : ℝ) / 8 := by simp [d]; norm_num
  have e2 : d 2 * (1 / 8) = ((4 : ℕ) : ℝ) / 8 := by simp [d]; norm_num
  refine ⟨?_, ?_, ?_⟩
  · intro i; fin_cases i
    · show _ ≤ distInt (d 0 * (1 / 8)); rw [e0]; exact div8_clear 1 (by norm_num)
    · show _ ≤ distInt (d 1 * (1 / 8)); rw [e1]; exact div8_clear 2 (by norm_num)
    · show _ ≤ distInt (d 2 * (1 / 8)); rw [e2]; exact div8_clear 4 (by norm_num)
  · rw [e0, div8_opener_iff]
  · intro i; fin_cases i
    · show ¬ IsEntry (d 0 * (1 / 8)); rw [e0, div8_entry_iff]; norm_num
    · show ¬ IsEntry (d 1 * (1 / 8)); rw [e1, div8_entry_iff]; norm_num
    · show ¬ IsEntry (d 2 * (1 / 8)); rw [e2, div8_entry_iff]; norm_num

#print axioms free_example

/-! ## (5) Positive dependence of survival forms: the Gordan alternative -/

/-- A nonnegative nonzero combination of the forms vanishes. -/
-- STANDING: DEFINITION
def PositivelyDependent {m n : ℕ} (w : Fin m → Fin n → ℝ) : Prop :=
  ∃ l : Fin m → ℝ, (∀ a, 0 ≤ l a) ∧ l ≠ 0 ∧ ∑ a, l a • w a = 0

/-- **Gordan's alternative** [L] (from Mathlib's `geometric_hahn_banach_compact_closed`): for finitely many linear forms
`x ↦ w a ⬝ x` on `ℝ^n`, either some direction makes all of them strictly negative, or the forms are positively
dependent. -/
theorem gordan {m n : ℕ} (w : Fin m → Fin n → ℝ) :
    (∃ x : Fin n → ℝ, ∀ a, w a ⬝ᵥ x < 0) ∨ PositivelyDependent w := by
  let M : (Fin m → ℝ) →ₗ[ℝ] (Fin n → ℝ) := Matrix.vecMulLinear w
  have hM : ∀ l, M l = ∑ a, l a • w a := by
    intro l; ext j; simp [M, Matrix.vecMulLinear, Matrix.vecMul, dotProduct]
  let K : Set (Fin n → ℝ) := M '' stdSimplex ℝ (Fin m)
  have hKc : Convex ℝ K := (convex_stdSimplex ℝ (Fin m)).linear_image M
  have hKk : IsCompact K := (isCompact_stdSimplex ℝ (Fin m)).image M.continuous_of_finiteDimensional
  -- Compactness of the simplex is used only for the separation step of `gordan`; no covering of instants.
  by_cases h0 : (0 : Fin n → ℝ) ∈ K
  · right
    obtain ⟨l, hl, hl0⟩ := h0
    refine ⟨l, hl.1, ?_, by rw [← hM]; exact hl0⟩
    rintro rfl
    have := hl.2
    simp at this
  · left
    have hdisj : Disjoint K {(0 : Fin n → ℝ)} := by
      rw [Set.disjoint_singleton_right]; exact h0
    obtain ⟨f, u, v, hu, huv, hv⟩ := geometric_hahn_banach_compact_closed hKc hKk (convex_singleton _)
      isClosed_singleton hdisj
    have hv0 : v < 0 := by simpa using hv 0 rfl
    refine ⟨fun i => f (fun j => if i = j then (1 : ℝ) else 0), fun a => ?_⟩
    have hwa : w a ∈ K := by
      refine ⟨Pi.single a 1, single_mem_stdSimplex ℝ a, ?_⟩
      rw [hM]; ext j
      rw [Finset.sum_apply, Finset.sum_eq_single a]
      · simp
      · intro c _ hc; simp [Pi.single_apply, hc]
      · intro h; exact absurd (Finset.mem_univ a) h
    have h1 := hu _ hwa
    have h2 : f (w a) = w a ⬝ᵥ (fun i => f (fun j => if i = j then (1 : ℝ) else 0)) := by
      rw [dotProduct]
      have := LinearMap.pi_apply_eq_sum_univ f.toLinearMap (w a)
      simpa [smul_eq_mul] using this
    rw [← h2]; linarith

#print axioms gordan

/-- **Some form is nonnegative in every direction iff the forms are positively dependent** [L]. -/
theorem every_direction_survivor_iff {m n : ℕ} (w : Fin m → Fin n → ℝ) :
    (∀ x : Fin n → ℝ, ∃ a, 0 ≤ w a ⬝ᵥ x) ↔ PositivelyDependent w := by
  constructor
  · intro h
    rcases gordan w with ⟨x, hx⟩ | hd
    · obtain ⟨a, ha⟩ := h x
      exact absurd (hx a) (not_lt.mpr ha)
    · exact hd
  · rintro ⟨l, hl, hne, hsum⟩ x
    by_contra hcon
    push Not at hcon
    obtain ⟨a0, ha0⟩ : ∃ a0, l a0 ≠ 0 := by
      by_contra hh; push Not at hh; exact hne (funext hh)
    have hpos : 0 < l a0 := lt_of_le_of_ne (hl a0) (Ne.symm ha0)
    have hsum' : ∑ a, l a * (w a ⬝ᵥ x) = 0 := by
      have := congrArg (fun y => y ⬝ᵥ x) hsum
      simpa [sum_dotProduct, smul_dotProduct] using this
    have hlt : ∑ a, l a * (w a ⬝ᵥ x) < ∑ _a : Fin m, (0 : ℝ) := by
      apply Finset.sum_lt_sum
      · intro a _; exact mul_nonpos_of_nonneg_of_nonpos (hl a) (hcon a).le
      · exact ⟨a0, Finset.mem_univ _, mul_neg_of_pos_of_neg hpos (hcon a0)⟩
    simp at hlt; linarith

#print axioms every_direction_survivor_iff

/-- The survival forms of the AP touches, as vectors on the directions `(δ_1, …, δ_7)`: form `k` is `σ_a` with
`a = 2k + 1`, i.e. `δ_a / a - δ_{8-a} / (8-a)`. -/
noncomputable def apForm (k : Fin 4) : Fin 7 → ℝ := fun i =>
  (if (i : ℕ) + 1 = 2 * (k : ℕ) + 1 then 1 / ((2 * (k : ℕ) + 1 : ℕ) : ℝ) else 0) -
  (if (i : ℕ) + 1 = 7 - 2 * (k : ℕ) then 1 / ((7 - 2 * (k : ℕ) : ℕ) : ℝ) else 0)

/-- The vector form is the survival form [L]. -/
theorem apForm_dot (δ : ℕ → ℝ) (k : Fin 4) :
    apForm k ⬝ᵥ (fun i : Fin 7 => δ ((i : ℕ) + 1)) = sigma δ (2 * (k : ℕ) + 1) (7 - 2 * (k : ℕ)) := by
  fin_cases k <;> simp [apForm, dotProduct, Fin.sum_univ_succ, sigma] <;> ring

#print axioms apForm_dot

/-- **The AP survival forms are positively dependent** [L]: `σ_1 + σ_7 = 0` and `σ_3 + σ_5 = 0` as forms on `ℝ^7`
(`l = (1,0,0,1)` and `l = (0,1,1,0)`). -/
theorem ap_touch_positive_dependence : PositivelyDependent apForm := by
  refine ⟨![1, 0, 0, 1], ?_, ?_, ?_⟩
  · intro a; fin_cases a <;> simp
  · intro h; have := congrFun h 0; simp at this
  · ext i
    simp [Fin.sum_univ_succ, apForm]
    fin_cases i <;> simp <;> norm_num

#print axioms ap_touch_positive_dependence

/-- **The AP: every direction has a surviving touch** [L]: for every direction `δ` there is `k` with `σ_{2k+1}(δ) >= 0`;
with `ap_first_order_iff` this is first-order survival of one of the instants `1/8, 3/8, 5/8, 7/8`. -/
theorem ap_every_direction_survivor (δ : ℕ → ℝ) : ∃ k : Fin 4, 0 ≤ sigma δ (2 * (k : ℕ) + 1) (7 - 2 * (k : ℕ)) := by
  obtain ⟨k, hk⟩ := (every_direction_survivor_iff apForm).mpr ap_touch_positive_dependence
    (fun i : Fin 7 => δ ((i : ℕ) + 1))
  exact ⟨k, by rw [← apForm_dot]; exact hk⟩

#print axioms ap_every_direction_survivor

#print axioms IsOpener.distInt_eq
#print axioms IsEntry.distInt_eq
#print axioms apd_pos
#print axioms apd_val
#print axioms apd_eq

end ZeroMargin

end Fresh
