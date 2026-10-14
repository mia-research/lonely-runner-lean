import Mathlib
import Fresh.Framework
import Fresh.ZeroMargin
import Fresh.Cycle
import Fresh.PairLaw

/-!
# Touch theory: cones, the second-order pair, and the whole-set conjugate (Task AK)

Written 2026-10-09.  Imports Mathlib and the Fresh modules `Framework`, `ZeroMargin`, `Cycle`, `PairLaw`.  Nothing from
the existing `LonelyRunner` repo.  Exact reals, positive speeds, no density, coverage, cap or move budget as the SHAPE
of any statement.

Notation.  For a positive family `d : ι → ℝ`, a direction `δ`, and an instant `t > 0`, `x_i = δ_i / d_i` is the relative
change of runner `i`.  `FOSurvives d δ t` is the first-order survival of the touch at `t`: some `τ` gives
`δ_i t + d_i τ >= 0` on every opener and `<= 0` on every entry (`ZeroMargin.exact_touch_survival`).

Results ([L] = Lean, `#print axioms` after each; [reasoned] = not formalised; [OWED] = not done).
* (1) `fo_iff`: `FOSurvives` iff `x_e <= x_o` for every opener `o`, entry `e`.  `wholeset_conjugate`: for EVERY lonely
  instant `t0` of EVERY finite family there is a lonely `t' = N t0`, `N ≡ 7 (mod 8)`, at which every opener of `t0` is an
  entry and every entry is an opener (no commensurability hypothesis; uses `simult_approx`, simultaneous recurrence on the
  torus).  `not_cover_iff`: both the touch and its conjugate fail at first order iff some opener-entry pair has
  `x_o < x_e` and some has `x_e < x_o`.  `cones_cover_iff`: the two cones cover every direction iff there is no opener, or
  no entry, or exactly one opener and exactly one entry.  `touch_conjugate_cover`, `singleton_touch_survives`,
  `violating_direction_exists_iff`: the same for every positive family.  `violation_kills`: a strict violation kills the
  touch for every `τ` and all small `e`.  `E439_example`: (1,2,3,4,5,6,11), exact.
* (2) `sigma_zero_nonaffine` (the instant `a/8/(1 + e δ_a/a)` survives exactly when `σ_a = 0`), `sigma_zero_affine_iff`
  (an affine move survives iff `δ_a = 0`), `sigma_neg_no_affine`, `affine_survival_classification`,
  `window_trichotomy` (the `PairLaw` oracle: positive width / point / empty iff `σ_a` > / = / < 0), `scaling_case`,
  `ap_pair_survives_every_direction` (the second-order pair law, all `σ_a`).
* (3) `wholeset_conjugate` (a whole-set no-partner touch does not exist: the OWED item of `ZeroMargin` is false as a
  possibility), `blocked_pair_conjugate_example` (rational: the pair-level conjugate `7 t0` is blocked, `15 t0` is not).

Provenance.  Existing repo: `LRC/Spec/ProgressionPairN.lean` (pair law), re-derived in `Fresh/PairLaw.lean`; the touch
cones, conjugate existence by simultaneous recurrence and the second-order pair are new here (no existing declaration
corresponds).  I did not copy a proof I did not understand.
-/

open Classical Filter Topology

namespace Fresh

namespace TouchTheory

open ZeroMargin Localisation

/-! ## (0) First-order survival and its Helly form -/

/-- First-order survival of the touch at `t`: some `τ` makes every opener's `A_i` nonnegative and every entry's `A_i`
nonpositive. -/
-- STANDING: DEFINITION
def FOSurvives {ι : Type*} (d δ : ι → ℝ) (t : ℝ) : Prop :=
  ∃ τ : ℝ, (∀ i, IsOpener (d i * t) → 0 ≤ coefA (d i) (δ i) t τ) ∧
    (∀ i, IsEntry (d i * t) → coefA (d i) (δ i) t τ ≤ 0)

/-- **First-order survival is the opener-entry comparison** [L]. -/
theorem fo_iff {ι : Type*} [Fintype ι] (d δ : ι → ℝ) (hd : ∀ i, 0 < d i) (t : ℝ) (ht : 0 < t) :
    FOSurvives d δ t ↔
      ∀ o e, IsOpener (d o * t) → IsEntry (d e * t) → δ e / d e ≤ δ o / d o := by
  unfold FOSurvives coefA
  exact helly_one_dim d δ hd t ht _ _

#print axioms fo_iff

theorem opener_ne_entry {ι : Type*} (d : ι → ℝ) (t : ℝ) {o e : ι} (ho : IsOpener (d o * t))
    (he : IsEntry (d e * t)) : o ≠ e := by
  rintro rfl
  exact not_opener_and_entry ⟨ho, he⟩

#print axioms opener_ne_entry

/-! ## (1) The two cones -/

/-- **Both fail iff a strict order violates each** [L].  If `t'` has the roles of `t` swapped (openers of `t'` are the
entries of `t` and conversely), then neither the touch at `t` nor the touch at `t'` survives to first order iff some
opener-entry pair of `t` has `x_o < x_e` and some has `x_e < x_o`. -/
theorem not_cover_iff {ι : Type*} [Fintype ι] (d δ : ι → ℝ) (hd : ∀ i, 0 < d i) (t t' : ℝ) (ht : 0 < t)
    (ht' : 0 < t') (hO : ∀ i, IsOpener (d i * t') ↔ IsEntry (d i * t))
    (hE : ∀ i, IsEntry (d i * t') ↔ IsOpener (d i * t)) :
    ¬ (FOSurvives d δ t ∨ FOSurvives d δ t') ↔
      (∃ o e, IsOpener (d o * t) ∧ IsEntry (d e * t) ∧ δ o / d o < δ e / d e) ∧
      (∃ o e, IsOpener (d o * t) ∧ IsEntry (d e * t) ∧ δ e / d e < δ o / d o) := by
  rw [not_or, fo_iff d δ hd t ht, fo_iff d δ hd t' ht']
  simp only [hO, hE]
  constructor
  · rintro ⟨h1, h2⟩
    push Not at h1 h2
    obtain ⟨o, e, ho, he, h⟩ := h1
    obtain ⟨e', o', he', ho', h'⟩ := h2
    exact ⟨⟨o, e, ho, he, h⟩, ⟨o', e', ho', he', h'⟩⟩
  · rintro ⟨⟨o, e, ho, he, h⟩, ⟨o', e', ho', he', h'⟩⟩
    refine ⟨fun H => absurd (H o e ho he) (not_le.mpr h), fun H => absurd (H e' o' he' ho') (not_le.mpr h')⟩

#print axioms not_cover_iff

/-- **The exact cone-union description** [L].  With roles swapped between `t` and `t'`, the two first-order cones cover
every direction iff there is no opener, or no entry, or exactly one opener and exactly one entry. -/
theorem cones_cover_iff {ι : Type*} [Fintype ι] (d : ι → ℝ) (hd : ∀ i, 0 < d i) (t t' : ℝ) (ht : 0 < t)
    (ht' : 0 < t') (hO : ∀ i, IsOpener (d i * t') ↔ IsEntry (d i * t))
    (hE : ∀ i, IsEntry (d i * t') ↔ IsOpener (d i * t)) :
    (∀ δ : ι → ℝ, FOSurvives d δ t ∨ FOSurvives d δ t') ↔
      ((¬ ∃ i, IsOpener (d i * t)) ∨ (¬ ∃ j, IsEntry (d j * t)) ∨
        ((∀ i i', IsOpener (d i * t) → IsOpener (d i' * t) → i = i') ∧
         (∀ j j', IsEntry (d j * t) → IsEntry (d j' * t) → j = j'))) := by
  constructor
  · intro H
    by_contra hcon
    push Not at hcon
    obtain ⟨⟨i, hi⟩, ⟨j, hj⟩, hsing⟩ := hcon
    have hij : i ≠ j := opener_ne_entry d t hi hj
    -- a strict order of the three positions violating both touches
    have key : ∀ x : ι → ℝ, ¬ (FOSurvives d (fun k => d k * x k) t ∨ FOSurvives d (fun k => d k * x k) t') →
        False := fun x h => h (H _)
    by_cases hO2 : ∀ i', IsOpener (d i' * t) → i' = i
    · -- two distinct entries
      have hA : ∀ a a', IsOpener (d a * t) → IsOpener (d a' * t) → a = a' :=
        fun a a' ha ha' => (hO2 a ha).trans (hO2 a' ha').symm
      obtain ⟨j1, j', hj1, hj', hjj'⟩ := hsing hA
      have hij1 : i ≠ j1 := opener_ne_entry d t hi hj1
      have hij' : i ≠ j' := opener_ne_entry d t hi hj'
      refine key (fun k => if k = j1 then 0 else if k = i then 1 else if k = j' then 2 else 0) ?_
      rw [not_cover_iff _ _ hd t t' ht ht' hO hE]
      refine ⟨⟨i, j', hi, hj', ?_⟩, ⟨i, j1, hi, hj1, ?_⟩⟩
      · simp only [mul_div_cancel_left₀ _ (hd _).ne']
        simp [hij', hij'.symm, hij1, hij1.symm, hjj', hjj'.symm]
      · simp only [mul_div_cancel_left₀ _ (hd _).ne']
        simp [hij1, hij1.symm]
    · push Not at hO2
      obtain ⟨i', hi', hii'⟩ := hO2
      have hi'j : i' ≠ j := opener_ne_entry d t hi' hj
      refine key (fun k => if k = i then 0 else if k = j then 1 else if k = i' then 2 else 0) ?_
      rw [not_cover_iff _ _ hd t t' ht ht' hO hE]
      refine ⟨⟨i, j, hi, hj, ?_⟩, ⟨i', j, hi', hj, ?_⟩⟩
      · simp only [mul_div_cancel_left₀ _ (hd _).ne']
        simp [hij, hij.symm]
      · simp only [mul_div_cancel_left₀ _ (hd _).ne']
        simp [hi'j, hi'j.symm, hii', hii'.symm, hij, hij.symm]
  · intro H δ
    by_contra hcon
    rw [not_cover_iff _ _ hd t t' ht ht' hO hE] at hcon
    obtain ⟨⟨o, e, ho, he, h⟩, ⟨o', e', ho', he', h'⟩⟩ := hcon
    rcases H with H | H | ⟨H1, H2⟩
    · exact H ⟨o, ho⟩
    · exact H ⟨e, he⟩
    · have h1 := H1 o o' ho ho'
      have h2 := H2 e e' he he'
      subst h1; subst h2
      exact lt_asymm h h'

#print axioms cones_cover_iff

/-- **A strict violation kills the touch to every order that matters** [L].  If an opener `o` has `x_o < x_e` for an
entry `e`, then for EVERY `τ` the moved instant `t + e τ` is not lonely for all small `e > 0`. -/
theorem violation_kills {ι : Type*} [Finite ι] (d δ : ι → ℝ) (hd : ∀ i, 0 < d i) (t : ℝ) (ht : 0 < t)
    (hl : ∀ i, (1 / 8 : ℝ) ≤ distInt (d i * t)) {o e : ι} (ho : IsOpener (d o * t)) (he : IsEntry (d e * t))
    (hlt : δ o / d o < δ e / d e) (τ : ℝ) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ¬ ∀ i, (1 / 8 : ℝ) ≤ distInt ((d i + ε * δ i) * (t + ε * τ)) := by
  have key : ∀ i τ, coefA (d i) (δ i) t τ = d i * (δ i / d i * t + τ) := by
    intro i τ; unfold coefA; have := (hd i).ne'; field_simp
  apply touch_fails_of_violation d δ t τ hl
  by_cases h : 0 < δ e / d e * t + τ
  · exact Or.inr ⟨e, he, by rw [key]; exact mul_pos (hd e) h⟩
  · push Not at h
    refine Or.inl ⟨o, ho, ?_⟩
    rw [key]
    apply mul_neg_of_pos_of_neg (hd o)
    nlinarith

#print axioms violation_kills

/-! ## (1b) The whole-set conjugate always exists -/

/-- **Simultaneous recurrence** [L]: for finitely many reals, some positive multiple of all of them is within `ε` of an
integer at once.  (Compactness of the torus, via a convergent subsequence; no density or covering count.) -/
-- [PROVISIONAL: counting tool] (recurrence of a finite family of reals modulo 1 by compactness of the torus; supports
-- `wholeset_conjugate`, the claim that every lonely instant has a whole-set conjugate; tag added by the main session 2026-10-09)
theorem simult_approx {ι : Type*} [Fintype ι] (y : ι → ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ m : ℕ, 0 < m ∧ ∀ l, distInt ((m : ℝ) * y l) < ε := by
  haveI : Fact ((0 : ℝ) < 1) := ⟨one_pos⟩
  let z : ι → AddCircle (1 : ℝ) := fun l => ((y l : ℝ) : AddCircle (1 : ℝ))
  let s : ℕ → (ι → AddCircle (1 : ℝ)) := fun n => n • z
  obtain ⟨a, φ, hφ, hlim⟩ := CompactSpace.tendsto_subseq s
  rw [Metric.tendsto_atTop] at hlim
  obtain ⟨N, hN⟩ := hlim (ε / 2) (by positivity)
  have h1 := hN N le_rfl
  have h2 := hN (N + 1) (Nat.le_succ N)
  have hd : dist (s (φ (N + 1))) (s (φ N)) < ε := by
    calc dist (s (φ (N + 1))) (s (φ N)) ≤ dist (s (φ (N + 1))) a + dist a (s (φ N)) := dist_triangle _ _ _
      _ < ε / 2 + ε / 2 := by
          have := dist_comm a (s (φ N))
          simp only [Function.comp] at h1 h2
          linarith
      _ = ε := by ring
  have hlt : φ N < φ (N + 1) := hφ (Nat.lt_succ_self N)
  refine ⟨φ (N + 1) - φ N, by omega, fun l => ?_⟩
  have hs : s (φ (N + 1)) - s (φ N) = (φ (N + 1) - φ N) • z := by
    simp only [s]; exact (sub_nsmul z hlt.le).symm
  have hnorm : ‖(φ (N + 1) - φ N) • z‖ < ε := by
    rw [← hs, ← dist_eq_norm]; exact hd
  have hl : ‖((φ (N + 1) - φ N) • z) l‖ ≤ ‖(φ (N + 1) - φ N) • z‖ := norm_le_pi_norm _ l
  have hcoe : ((φ (N + 1) - φ N) • z) l = (((((φ (N + 1) - φ N : ℕ) : ℝ) * y l : ℝ)) : AddCircle (1 : ℝ)) := by
    simp only [Pi.smul_apply, z]
    rw [← AddCircle.coe_nsmul, nsmul_eq_mul]
  rw [hcoe, UnitAddCircle.norm_eq] at hl
  unfold distInt
  linarith

#print axioms simult_approx

/-- Subadditivity of the circle distance in the form needed: `distInt x <= distInt w + distInt (w - x)` [L]. -/
theorem distInt_sub_ge (x w : ℝ) : distInt x ≤ distInt w + distInt (w - x) := by
  have k := Localisation.distInt_le x ((round w : ℤ) - round (w - x))
  have e : x - (((round w : ℤ) - round (w - x) : ℤ) : ℝ) = (w - (round w : ℝ)) - ((w - x) - (round (w - x) : ℝ)) := by
    push_cast; ring
  rw [e] at k
  calc distInt x ≤ |(w - (round w : ℝ)) - ((w - x) - (round (w - x) : ℝ))| := k
    _ ≤ |w - (round w : ℝ)| + |(w - x) - (round (w - x) : ℝ)| := abs_sub _ _
    _ = distInt w + distInt (w - x) := rfl

#print axioms distInt_sub_ge

/-- Closeness of `8 m x` to an integer keeps a strictly clear reading `x` strictly clear after multiplying by `8m - 1`
(`(8m-1) x = 8 m x - x`) [L]. -/
theorem slack_persists {x w ε : ℝ} (hx : (1 / 8 : ℝ) < distInt x) (hε : ε ≤ distInt x - 1 / 8)
    (hw : distInt w < ε) : (1 / 8 : ℝ) < distInt (w - x) := by
  have := distInt_sub_ge x w
  linarith

#print axioms slack_persists

/-- One reading under the map `x -> N x`, `N = 8 m - 1`, when `8 m x` is within `ε` of an integer [L]: it stays clear, an
opener becomes an entry, an entry becomes an opener, and a strictly clear reading stays strictly clear (so is neither). -/
theorem conj_reading {x ε : ℝ} {N m : ℕ} (hx : (1 / 8 : ℝ) ≤ distInt x) (hN : (N : ℝ) = 8 * m - 1)
    (hN8 : N % 8 = 7) (hε : (1 / 8 : ℝ) < distInt x → ε ≤ distInt x - 1 / 8)
    (hm : distInt ((m : ℝ) * (8 * x)) < ε) :
    (1 / 8 : ℝ) ≤ distInt ((N : ℝ) * x) ∧ (IsOpener ((N : ℝ) * x) ↔ IsEntry x) ∧
      (IsEntry ((N : ℝ) * x) ↔ IsOpener x) := by
  have hN8' : ((N : ℤ)) % 8 = 7 := by omega
  have hflip := scale_flip (N := (N : ℤ)) hN8' (x := x)
  simp only [Int.cast_natCast] at hflip
  rcases crit_trichotomy hx with ho | he | hs
  · have h1 : IsEntry ((N : ℝ) * x) := hflip.1 ho
    exact ⟨h1.distInt_eq.ge, ⟨fun h => (not_opener_and_entry ⟨h, h1⟩).elim,
      fun h => (not_opener_and_entry ⟨ho, h⟩).elim⟩, ⟨fun _ => ho, fun _ => h1⟩⟩
  · have h1 : IsOpener ((N : ℝ) * x) := hflip.2 he
    exact ⟨h1.distInt_eq.ge, ⟨fun _ => he, fun _ => h1⟩,
      ⟨fun h => (not_opener_and_entry ⟨h1, h⟩).elim, fun h => (not_opener_and_entry ⟨h, he⟩).elim⟩⟩
  · have hslack : (1 / 8 : ℝ) < distInt ((N : ℝ) * x) := by
      have e : (N : ℝ) * x = (m : ℝ) * (8 * x) - x := by rw [hN]; ring
      rw [e]
      exact slack_persists hs (hε hs) hm
    have n1 : ¬ IsOpener x := fun h => by rw [h.distInt_eq] at hs; exact lt_irrefl _ hs
    have n2 : ¬ IsEntry x := fun h => by rw [h.distInt_eq] at hs; exact lt_irrefl _ hs
    have n3 : ¬ IsOpener ((N : ℝ) * x) := fun h => by rw [h.distInt_eq] at hslack; exact lt_irrefl _ hslack
    have n4 : ¬ IsEntry ((N : ℝ) * x) := fun h => by rw [h.distInt_eq] at hslack; exact lt_irrefl _ hslack
    exact ⟨hslack.le, ⟨fun h => absurd h n3, fun h => absurd h n2⟩, ⟨fun h => absurd h n4, fun h => absurd h n1⟩⟩

#print axioms conj_reading

/-- **The whole-set conjugate always exists** [L].  For EVERY finite family `d` of reals and EVERY lonely instant
`t0 > 0` there is `N ≡ 7 (mod 8)` such that `N t0` is lonely, every opener of `t0` is an entry of `N t0`, and every entry
of `t0` is an opener of `N t0`.  No commensurability and no positivity of `d` is assumed: the critical readings
`d_i t0 ∈ ⅛ + ℤ` or `7/8 + ℤ` flip under every `N ≡ 7 (mod 8)` (`scale_flip`), the strictly clear readings keep a margin,
and `N = 8m - 1` is chosen by simultaneous recurrence (`simult_approx`) so that every `8 m d_i t0` is within that margin
of an integer.  So a touch with both an opener and an entry always has a lonely role-swapped instant. -/
theorem wholeset_conjugate {ι : Type*} [Fintype ι] (d : ι → ℝ) (t0 : ℝ)
    (hl : ∀ i, (1 / 8 : ℝ) ≤ distInt (d i * t0)) :
    ∃ N : ℕ, N % 8 = 7 ∧ (∀ i, (1 / 8 : ℝ) ≤ distInt (d i * ((N : ℝ) * t0))) ∧
      (∀ i, IsOpener (d i * ((N : ℝ) * t0)) ↔ IsEntry (d i * t0)) ∧
      (∀ i, IsEntry (d i * ((N : ℝ) * t0)) ↔ IsOpener (d i * t0)) := by
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε ∧ ∀ i, (1 / 8 : ℝ) < distInt (d i * t0) →
      ε < distInt (d i * t0) - 1 / 8 := by
    have h0 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε := self_mem_nhdsWithin
    refine h0.and ?_
    rw [Filter.eventually_all]
    intro i
    by_cases h : (1 / 8 : ℝ) < distInt (d i * t0)
    · exact nhdsWithin_le_nhds ((gt_mem_nhds (by linarith : (0 : ℝ) < distInt (d i * t0) - 1 / 8)).mono
        fun ε he _ => he)
    · exact Filter.Eventually.of_forall fun ε hh => absurd hh h
  obtain ⟨ε, hε0, hε⟩ := hev.exists
  obtain ⟨m, hm0, hm⟩ := simult_approx (fun i => 8 * (d i * t0)) hε0
  have h1 : 1 ≤ 8 * m := by omega
  refine ⟨8 * m - 1, by omega, ?_⟩
  have hN : (((8 * m - 1 : ℕ)) : ℝ) = 8 * m - 1 := by
    rw [Nat.cast_sub h1]; push_cast; ring
  have key := fun i => conj_reading (x := d i * t0) (ε := ε) (N := 8 * m - 1) (m := m) (hl i) hN (by omega)
    (fun h => (hε i h).le) (hm i)
  have e : ∀ i, d i * (((8 * m - 1 : ℕ) : ℝ) * t0) = ((8 * m - 1 : ℕ) : ℝ) * (d i * t0) := fun i => by ring
  simp only [e]
  exact ⟨fun i => (key i).1, fun i => (key i).2.1, fun i => (key i).2.2⟩

#print axioms wholeset_conjugate

/-- **Touches and their conjugates, for every positive family** [L].  For a lonely `t0 > 0` there is a lonely `t' > 0`
with the roles swapped such that, for every direction `δ`, neither survives to first order iff some opener-entry pair
has `x_o < x_e` and some has `x_e < x_o`. -/
theorem touch_conjugate_cover {ι : Type*} [Fintype ι] (d : ι → ℝ) (hd : ∀ i, 0 < d i) (t0 : ℝ) (ht : 0 < t0)
    (hl : ∀ i, (1 / 8 : ℝ) ≤ distInt (d i * t0)) :
    ∃ t' : ℝ, 0 < t' ∧ (∀ i, (1 / 8 : ℝ) ≤ distInt (d i * t')) ∧
      (∀ i, IsOpener (d i * t') ↔ IsEntry (d i * t0)) ∧ (∀ i, IsEntry (d i * t') ↔ IsOpener (d i * t0)) ∧
      (∀ δ : ι → ℝ, ¬ (FOSurvives d δ t0 ∨ FOSurvives d δ t') ↔
        ((∃ o e, IsOpener (d o * t0) ∧ IsEntry (d e * t0) ∧ δ o / d o < δ e / d e) ∧
         (∃ o e, IsOpener (d o * t0) ∧ IsEntry (d e * t0) ∧ δ e / d e < δ o / d o))) := by
  obtain ⟨N, hN, hlt, hO, hE⟩ := wholeset_conjugate d t0 hl
  have hNpos : (0 : ℝ) < N := by
    have : 0 < N := by omega
    exact_mod_cast this
  exact ⟨(N : ℝ) * t0, by positivity, hlt, hO, hE,
    fun δ => not_cover_iff d δ hd t0 _ ht (by positivity) hO hE⟩

#print axioms touch_conjugate_cover

/-- **Singleton touches cover every direction** [L].  If a lonely instant has exactly one opener and exactly one entry
(or none of either), then for every direction the touch or its conjugate survives to first order.  (No commensurability.) -/
theorem singleton_touch_survives {ι : Type*} [Fintype ι] (d : ι → ℝ) (hd : ∀ i, 0 < d i) (t0 : ℝ) (ht : 0 < t0)
    (hl : ∀ i, (1 / 8 : ℝ) ≤ distInt (d i * t0))
    (hsing : (¬ ∃ i, IsOpener (d i * t0)) ∨ (¬ ∃ j, IsEntry (d j * t0)) ∨
      ((∀ i i', IsOpener (d i * t0) → IsOpener (d i' * t0) → i = i') ∧
       (∀ j j', IsEntry (d j * t0) → IsEntry (d j' * t0) → j = j'))) :
    ∃ t' : ℝ, 0 < t' ∧ (∀ i, (1 / 8 : ℝ) ≤ distInt (d i * t')) ∧
      ∀ δ : ι → ℝ, FOSurvives d δ t0 ∨ FOSurvives d δ t' := by
  obtain ⟨N, hN, hlt, hO, hE⟩ := wholeset_conjugate d t0 hl
  have hNpos : (0 : ℝ) < N := by
    have : 0 < N := by omega
    exact_mod_cast this
  exact ⟨(N : ℝ) * t0, by positivity, hlt,
    (cones_cover_iff d hd t0 _ ht (by positivity) hO hE).mpr hsing⟩

#print axioms singleton_touch_survives

/-- **Exactly when a touch has a violating order** [L]: some direction kills the touch and its conjugate at first order
iff the touch has an opener and an entry and not exactly one of each. -/
theorem violating_direction_exists_iff {ι : Type*} [Fintype ι] (d : ι → ℝ) (hd : ∀ i, 0 < d i) (t0 : ℝ) (ht : 0 < t0)
    (hl : ∀ i, (1 / 8 : ℝ) ≤ distInt (d i * t0)) :
    (∃ t' : ℝ, 0 < t' ∧ (∀ i, (1 / 8 : ℝ) ≤ distInt (d i * t')) ∧
      (∀ i, IsOpener (d i * t') ↔ IsEntry (d i * t0)) ∧ (∀ i, IsEntry (d i * t') ↔ IsOpener (d i * t0)) ∧
      ∃ δ : ι → ℝ, ¬ (FOSurvives d δ t0 ∨ FOSurvives d δ t')) ↔
    ((∃ i, IsOpener (d i * t0)) ∧ (∃ j, IsEntry (d j * t0)) ∧
      ¬ ((∀ i i', IsOpener (d i * t0) → IsOpener (d i' * t0) → i = i') ∧
         (∀ j j', IsEntry (d j * t0) → IsEntry (d j' * t0) → j = j'))) := by
  obtain ⟨N, hN, hlt, hO, hE⟩ := wholeset_conjugate d t0 hl
  have hNpos : (0 : ℝ) < N := by
    have : 0 < N := by omega
    exact_mod_cast this
  have hc := cones_cover_iff d hd t0 _ ht (by positivity : (0:ℝ) < (N : ℝ) * t0) hO hE
  constructor
  · rintro ⟨t', ht', hlt', hO', hE', δ, hδ⟩
    by_contra hcon
    have hall : ∀ δ : ι → ℝ, FOSurvives d δ t0 ∨ FOSurvives d δ t' := by
      have hc' := cones_cover_iff d hd t0 t' ht ht' hO' hE'
      rw [hc']
      by_contra h2
      rw [not_or, not_or] at h2
      exact hcon ⟨not_not.mp h2.1, not_not.mp h2.2.1, h2.2.2⟩
    exact hδ (hall δ)
  · intro h
    refine ⟨(N : ℝ) * t0, by positivity, hlt, hO, hE, ?_⟩
    by_contra hno
    push Not at hno
    have := hc.mp (fun δ => by have := hno δ; tauto)
    rcases this with h1 | h1 | h1
    · exact h1 h.1
    · exact h1 h.2.1
    · exact h.2.2 h1

#print axioms violating_direction_exists_iff

/-! ## (1c) The E439 exception (1,2,3,4,5,6,11), exactly -/

/-- The integer disparities `(1,2,3,4,5,6,11)`. -/
def e439v : Fin 7 → ℕ := ![1, 2, 3, 4, 5, 6, 11]

/-- The same, as reals. -/
noncomputable def e439d : Fin 7 → ℝ := fun i => ((e439v i : ℕ) : ℝ)

theorem nat_class (n a : ℕ) :
    (n * a % 8 ≠ 0 → (1 / 8 : ℝ) ≤ distInt ((n : ℝ) * ((a : ℝ) / 8))) ∧
    (IsOpener ((n : ℝ) * ((a : ℝ) / 8)) ↔ n * a % 8 = 1) ∧
    (IsEntry ((n : ℝ) * ((a : ℝ) / 8)) ↔ n * a % 8 = 7) := by
  have e : (n : ℝ) * ((a : ℝ) / 8) = ((n * a : ℕ) : ℝ) / 8 := by push_cast; ring
  rw [e]
  exact ⟨div8_clear _, div8_opener_iff _, div8_entry_iff _⟩

#print axioms nat_class

/-- **The E439 exception, exactly** [L].  Disparities `(1,2,3,4,5,6,11)`.  At `3/8` the family is lonely; the openers are
exactly the runners of disparity `3` and `11` (indices 2 and 6) and the only entry has disparity `5` (index 4).  At the
conjugate `5/8 = 1 - 3/8` it is lonely with the roles swapped.  For the direction `δ = d x` with `x = (1,2,3,4,5,6,7)`
(so `x_3 = 3 < x_5 = 5 < x_11 = 7`; `δ = (1,4,9,16,25,36,77)`), for EVERY `τ` the affine move fails for all small
`e > 0` at both instants (`violation_kills`): the strict order kills both touches. -/
theorem E439_example :
    (∀ i, (1 / 8 : ℝ) ≤ distInt (e439d i * ((3 : ℕ) / 8))) ∧
    (∀ i, IsOpener (e439d i * ((3 : ℕ) / 8)) ↔ (i = 2 ∨ i = 6)) ∧
    (∀ i, IsEntry (e439d i * ((3 : ℕ) / 8)) ↔ i = 4) ∧
    (∀ i, (1 / 8 : ℝ) ≤ distInt (e439d i * ((5 : ℕ) / 8))) ∧
    (∀ i, IsOpener (e439d i * ((5 : ℕ) / 8)) ↔ i = 4) ∧
    (∀ i, IsEntry (e439d i * ((5 : ℕ) / 8)) ↔ (i = 2 ∨ i = 6)) ∧
    (∀ τ : ℝ, ∀ᶠ ε in 𝓝[>] (0 : ℝ), ¬ ∀ i, (1 / 8 : ℝ) ≤
        distInt ((e439d i + ε * (e439d i * ((![1, 2, 3, 4, 5, 6, 7] : Fin 7 → ℝ) i))) * (((3 : ℕ) / 8 : ℝ) + ε * τ))) ∧
    (∀ τ : ℝ, ∀ᶠ ε in 𝓝[>] (0 : ℝ), ¬ ∀ i, (1 / 8 : ℝ) ≤
        distInt ((e439d i + ε * (e439d i * ((![1, 2, 3, 4, 5, 6, 7] : Fin 7 → ℝ) i))) * (((5 : ℕ) / 8 : ℝ) + ε * τ))) := by
  have h3 := fun i : Fin 7 => nat_class (e439v i) 3
  have h5 := fun i : Fin 7 => nat_class (e439v i) 5
  have hd : ∀ i, 0 < e439d i := by
    intro i; unfold e439d
    have : 0 < e439v i := by fin_cases i <;> simp [e439v]
    exact_mod_cast this
  have c3 : ∀ i, (1 / 8 : ℝ) ≤ distInt (e439d i * ((3 : ℕ) / 8)) := fun i =>
    (h3 i).1 (by fin_cases i <;> simp [e439v])
  have c5 : ∀ i, (1 / 8 : ℝ) ≤ distInt (e439d i * ((5 : ℕ) / 8)) := fun i =>
    (h5 i).1 (by fin_cases i <;> simp [e439v])
  have o3 : ∀ i, IsOpener (e439d i * ((3 : ℕ) / 8)) ↔ (i = 2 ∨ i = 6) := fun i =>
    (h3 i).2.1.trans (by fin_cases i <;> simp [e439v])
  have n3 : ∀ i, IsEntry (e439d i * ((3 : ℕ) / 8)) ↔ i = 4 := fun i =>
    (h3 i).2.2.trans (by fin_cases i <;> simp [e439v])
  have o5 : ∀ i, IsOpener (e439d i * ((5 : ℕ) / 8)) ↔ i = 4 := fun i =>
    (h5 i).2.1.trans (by fin_cases i <;> simp [e439v])
  have n5 : ∀ i, IsEntry (e439d i * ((5 : ℕ) / 8)) ↔ (i = 2 ∨ i = 6) := fun i =>
    (h5 i).2.2.trans (by fin_cases i <;> simp [e439v])
  refine ⟨c3, o3, n3, c5, o5, n5, ?_, ?_⟩
  · intro τ
    have hx : ∀ i : Fin 7, (e439d i * ((![1, 2, 3, 4, 5, 6, 7] : Fin 7 → ℝ) i)) / e439d i =
        (![1, 2, 3, 4, 5, 6, 7] : Fin 7 → ℝ) i := fun i => mul_div_cancel_left₀ _ (hd i).ne'
    refine violation_kills e439d (fun i => e439d i * ((![1, 2, 3, 4, 5, 6, 7] : Fin 7 → ℝ) i)) hd _
      (by positivity) c3 (o := 2) (e := 4) ((o3 2).mpr (Or.inl rfl)) ((n3 4).mpr rfl) ?_ τ
    rw [hx, hx]; simp; norm_num
  · intro τ
    have hx : ∀ i : Fin 7, (e439d i * ((![1, 2, 3, 4, 5, 6, 7] : Fin 7 → ℝ) i)) / e439d i =
        (![1, 2, 3, 4, 5, 6, 7] : Fin 7 → ℝ) i := fun i => mul_div_cancel_left₀ _ (hd i).ne'
    refine violation_kills e439d (fun i => e439d i * ((![1, 2, 3, 4, 5, 6, 7] : Fin 7 → ℝ) i)) hd _
      (by positivity) c5 (o := 4) (e := 6) ((o5 4).mpr rfl) ((n5 6).mpr (Or.inr rfl)) ?_ τ
    rw [hx, hx]; simp; norm_num

#print axioms E439_example

/-! ## (3) A rational touch whose pair-level conjugate `7 t0` is blocked -/

/-- Disparities `(1, 7, 16/7, 2, 3, 4, 5)`. -/
noncomputable def blkd : Fin 7 → ℝ := ![1, 7, 16 / 7, 2, 3, 4, 5]

/-- **A rational touch whose pair-level conjugate is blocked** [L].  At `t0 = 1/8` the family `(1,7,16/7,2,3,4,5)` is lonely;
runner `1` is an opener (`1/8`) and runner `7` is an entry (`7/8`).  The pair-level conjugate `7 t0 = 7/8` is NOT lonely:
the runner of disparity `16/7` stands at exactly `2` (a whole lap).  The whole-set conjugate is `15 t0 = 15/8` (`N = 15 ≡ 7`
mod 8): lonely, runner `1` is there an entry (`15/8 = 1 + 7/8`) and runner `7` an opener (`105/8 = 13 + 1/8`). -/
theorem blocked_pair_conjugate_example :
    (∀ i, (1 / 8 : ℝ) ≤ distInt (blkd i * (1 / 8))) ∧ IsOpener (blkd 0 * (1 / 8)) ∧ IsEntry (blkd 1 * (1 / 8)) ∧
    ¬ (∀ i, (1 / 8 : ℝ) ≤ distInt (blkd i * (7 * (1 / 8)))) ∧
    (∀ i, (1 / 8 : ℝ) ≤ distInt (blkd i * (15 * (1 / 8)))) ∧
    IsEntry (blkd 0 * (15 * (1 / 8))) ∧ IsOpener (blkd 1 * (15 * (1 / 8))) := by
  refine ⟨?_, ⟨0, by simp [blkd]⟩, ⟨0, by norm_num [blkd]⟩, ?_, ?_, ⟨1, by norm_num [blkd]⟩,
    ⟨13, by norm_num [blkd]⟩⟩
  · intro i
    fin_cases i
    · exact clear_of_window 0 (by norm_num [blkd]) (by norm_num [blkd])
    · exact clear_of_window 0 (by norm_num [blkd]) (by norm_num [blkd])
    · exact clear_of_window 0 (by norm_num [blkd]) (by norm_num [blkd])
    · exact clear_of_window 0 (by norm_num [blkd]) (by norm_num [blkd])
    · exact clear_of_window 0 (by norm_num [blkd]) (by norm_num [blkd])
    · exact clear_of_window 0 (by norm_num [blkd]) (by norm_num [blkd])
    · exact clear_of_window 0 (by norm_num [blkd]) (by norm_num [blkd])
  · intro h
    have := h 2
    have e : blkd 2 * (7 * (1 / 8)) = ((2 : ℤ) : ℝ) := by simp [blkd]; norm_num
    rw [e, distInt_intCast] at this
    norm_num at this
  · intro i
    fin_cases i
    · exact clear_of_window 1 (by norm_num [blkd]) (by norm_num [blkd])
    · exact clear_of_window 13 (by norm_num [blkd]) (by norm_num [blkd])
    · exact clear_of_window 4 (by norm_num [blkd]) (by norm_num [blkd])
    · exact clear_of_window 3 (by norm_num [blkd]) (by norm_num [blkd])
    · exact clear_of_window 5 (by norm_num [blkd]) (by norm_num [blkd])
    · exact clear_of_window 7 (by norm_num [blkd]) (by norm_num [blkd])
    · exact clear_of_window 9 (by norm_num [blkd]) (by norm_num [blkd])

#print axioms blocked_pair_conjugate_example

/-! ## (2) The second-order case `σ_a = 0` at the AP pair -/

/-- The AP family `{j + e δ_j}` is lonely at `t` iff each indexed runner is clear [L]. -/
theorem lonely_pds_fin (δ : ℕ → ℝ) (e t : ℝ) :
    Cascade.LonelyAt (PairLaw.pds (fun j => (j : ℝ) + e * δ j)) t ↔
      ∀ i : Fin 7, (1 / 8 : ℝ) ≤ distInt ((apd i + e * δ ((i : ℕ) + 1)) * t) := by
  rw [PairLaw.lonelyAt_pds_iff]
  constructor
  · intro h i
    have := h ((i : ℕ) + 1) (by omega) (by omega)
    rw [apd_eq]
    exact this
  · intro h j h1 h7
    have := h ⟨j - 1, by omega⟩
    rw [apd_val h1 h7] at this
    simp only [Nat.sub_add_cancel h1] at this
    exact this

#print axioms lonely_pds_fin

/-- The two critical readings and the slack ones at the AP touch, in one statement [L]. -/
theorem ap_slack_or_critical {a b : ℕ} (ha : a % 2 = 1) (ha7 : a ≤ 7) (hab : a + b = 8) (i : Fin 7) :
    ((i : ℕ) + 1 = a ∨ (i : ℕ) + 1 = b) ∨ (1 / 8 : ℝ) < distInt (apd i * ((a : ℝ) / 8)) := by
  obtain ⟨hc, ho, he⟩ := ap_classes_fin ha ha7 i
  rcases crit_trichotomy hc with h | h | h
  · exact Or.inl (Or.inl (ho.mp h))
  · exact Or.inl (Or.inr (by have := he.mp h; omega))
  · exact Or.inr h

#print axioms ap_slack_or_critical

/-- **The second-order case: the instant survives exactly along a NON-affine move** [L].  At the AP pair `(a, b = 8 - a)`
with `σ_a(δ) = 0` (so `δ_a / a = δ_b / b = r`), the instant `a/8 / (1 + e r)` is lonely for `{j + e δ_j}` for all small
`e > 0`.  The two critical readings are EXACTLY unchanged (`(a + e δ_a) t = a t0`), the others move by less than their
margin.  This is the exact content of `PairLaw`'s `u_a = w_a`: the class window is the single point `a / (8 (1 + e r))`. -/
theorem sigma_zero_nonaffine {a b : ℕ} (ha : a % 2 = 1) (ha7 : a ≤ 7) (hab : a + b = 8) (δ : ℕ → ℝ)
    (hσ : sigma δ a b = 0) :
    ∀ᶠ e in 𝓝[>] (0 : ℝ), Cascade.LonelyAt (PairLaw.pds (fun j => (j : ℝ) + e * δ j))
      (((a : ℝ) / 8) / (1 + e * (δ a / a))) := by
  have ha1 : (1 : ℝ) ≤ a := by exact_mod_cast (show 1 ≤ a by omega)
  have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast (show 1 ≤ b by omega)
  set t0 : ℝ := (a : ℝ) / 8 with ht0
  set r : ℝ := δ a / a with hr
  have hda : δ a = r * a := by rw [hr]; field_simp
  have hdb : δ b = r * b := by
    unfold sigma at hσ
    have : δ b / b = r := by linarith
    rw [← this]; field_simp
  have hne : ∀ᶠ e in 𝓝 (0 : ℝ), 1 + e * r ≠ 0 := by
    have hc : Continuous (fun e : ℝ => 1 + e * r) := by fun_prop
    have := hc.tendsto 0
    simp only [zero_mul, add_zero] at this
    exact this.eventually_ne one_ne_zero
  have hpt : ∀ i : Fin 7, ∀ᶠ e in 𝓝 (0 : ℝ), 1 + e * r ≠ 0 →
      (1 / 8 : ℝ) ≤ distInt ((apd i + e * δ ((i : ℕ) + 1)) * (t0 / (1 + e * r))) := by
    intro i
    have hl : (1 / 8 : ℝ) ≤ distInt (apd i * t0) := (ap_classes_fin ha ha7 i).1
    rcases ap_slack_or_critical ha ha7 hab i with hc | hs
    · refine Filter.Eventually.of_forall fun e hne' => ?_
      have hexact : (apd i + e * δ ((i : ℕ) + 1)) * (t0 / (1 + e * r)) = apd i * t0 := by
        rcases hc with h | h
        · have e1 : apd i = (a : ℝ) := by rw [apd_eq, h]
          rw [e1, h, hda]; field_simp
        · have e1 : apd i = (b : ℝ) := by rw [apd_eq, h]
          rw [e1, h, hdb]; field_simp
      rw [hexact]; exact hl
    · have hcont : ContinuousAt (fun e : ℝ => (apd i + e * δ ((i : ℕ) + 1)) * (t0 / (1 + e * r))) 0 := by
        apply ContinuousAt.mul (by fun_prop)
        apply ContinuousAt.div continuousAt_const (by fun_prop)
        simp
      have h0 : (fun e : ℝ => (apd i + e * δ ((i : ℕ) + 1)) * (t0 / (1 + e * r))) 0 = apd i * t0 := by simp
      have hcomp := PathLaws.continuous_distInt.continuousAt.comp hcont
      have hlim := hcomp.tendsto
      simp only [Function.comp, h0] at hlim
      exact (hlim.eventually (lt_mem_nhds hs)).mono fun e he _ => he.le
  have hall : ∀ᶠ e in 𝓝 (0 : ℝ), ∀ i : Fin 7, 1 + e * r ≠ 0 →
      (1 / 8 : ℝ) ≤ distInt ((apd i + e * δ ((i : ℕ) + 1)) * (t0 / (1 + e * r))) :=
    Filter.eventually_all.mpr hpt
  filter_upwards [nhdsWithin_le_nhds hne, nhdsWithin_le_nhds hall] with e h1 h2
  rw [lonely_pds_fin]
  exact fun i => h2 i h1

#print axioms sigma_zero_nonaffine

/-- **The affine move at `σ_a = 0`** [L].  For the AP pair with `σ_a(δ) = 0`: some `τ` makes `a/8 + e τ` lonely for
`{j + e δ_j}` at all small `e > 0` iff `δ_a = 0` (equivalently `δ_a = δ_b = 0`, since `δ_b = (b/a) δ_a`).  When `δ_a ≠ 0`
the second-order term of the opener is `A_a + e B_a = -e a r² t0 < 0` after the first order is cancelled (`r = δ_a/a`),
which is the obstruction `ZeroMargin.scaling_B_obstruction` shows for `δ = c d`. -/
theorem sigma_zero_affine_iff {a b : ℕ} (ha : a % 2 = 1) (ha7 : a ≤ 7) (hab : a + b = 8) (δ : ℕ → ℝ)
    (hσ : sigma δ a b = 0) :
    (∃ τ : ℝ, ∀ᶠ e in 𝓝[>] (0 : ℝ),
        Cascade.LonelyAt (PairLaw.pds (fun j => (j : ℝ) + e * δ j)) ((a : ℝ) / 8 + e * τ)) ↔ δ a = 0 := by
  have ha1 : (1 : ℝ) ≤ a := by exact_mod_cast (show 1 ≤ a by omega)
  have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast (show 1 ≤ b by omega)
  have ht : (0 : ℝ) < (a : ℝ) / 8 := by positivity
  set t0 : ℝ := (a : ℝ) / 8 with ht0
  set r : ℝ := δ a / a with hr
  have hda : δ a = r * a := by rw [hr]; field_simp
  have hdb : δ b = r * b := by
    unfold sigma at hσ
    have : δ b / b = r := by linarith
    rw [← this]; field_simp
  constructor
  · rintro ⟨τ, hτ⟩
    have hl : ∀ i : Fin 7, (1 / 8 : ℝ) ≤ distInt (apd i * t0) := fun i => (ap_classes_fin ha ha7 i).1
    have hex := exact_touch_eventually apd (fun i => δ ((i : ℕ) + 1)) t0 τ hl
    have key : ∀ᶠ e in 𝓝[>] (0 : ℝ), r * t0 + τ + e * (r * τ) = 0 := by
      filter_upwards [hex, hτ] with e h1 h2
      rw [lonely_pds_fin] at h2
      obtain ⟨hO, hE⟩ := h1.mp (by simpa using h2)
      have iA := hO ⟨a - 1, by omega⟩ ((ap_classes_fin ha ha7 _).2.1.mpr (by simp; omega))
      have iB := hE ⟨b - 1, by omega⟩ ((ap_classes_fin ha ha7 _).2.2.mpr (by simp; omega))
      rw [apd_val (by omega) (by omega)] at iA iB
      simp only [Nat.sub_add_cancel (show 1 ≤ a by omega), Nat.sub_add_cancel (show 1 ≤ b by omega)] at iA iB
      unfold coefA coefB at iA iB
      rw [hda] at iA
      rw [hdb] at iB
      have p1 : 0 ≤ (a : ℝ) * (r * t0 + τ + e * (r * τ)) := by nlinarith
      have p2 : (b : ℝ) * (r * t0 + τ + e * (r * τ)) ≤ 0 := by nlinarith
      have q1 : 0 ≤ r * t0 + τ + e * (r * τ) := (mul_nonneg_iff_of_pos_left (by linarith)).mp p1
      have q2 : r * t0 + τ + e * (r * τ) ≤ 0 := by
        by_contra hc; push Not at hc
        have := mul_pos (by linarith : (0 : ℝ) < b) hc; linarith
      linarith
    have hpos : ∀ᶠ e in 𝓝[>] (0 : ℝ), 0 < e := self_mem_nhdsWithin
    obtain ⟨e1, hk1, hp1⟩ := (key.and hpos).exists
    have hlt : ∀ᶠ e in 𝓝[>] (0 : ℝ), e < e1 := nhdsWithin_le_nhds (gt_mem_nhds hp1)
    obtain ⟨e2, hk2, hp2, hl2⟩ := (key.and (hpos.and hlt)).exists
    have hrt : r * τ = 0 := by
      have : (e1 - e2) * (r * τ) = 0 := by linarith
      rcases mul_eq_zero.mp this with h | h
      · linarith
      · exact h
    have hs : r * t0 + τ = 0 := by rw [hrt] at hk1; linarith
    have hr0 : r = 0 := by
      have : τ = -(r * t0) := by linarith
      rw [this] at hrt
      have : r * r * t0 = 0 := by linarith
      rcases mul_eq_zero.mp this with h | h
      · rcases mul_eq_zero.mp h with h | h <;> [exact h; exact h]
      · linarith
    rw [hda, hr0]; ring
  · intro h0
    have hr0 : r = 0 := by rw [hr, h0]; simp
    refine ⟨0, ?_⟩
    filter_upwards [sigma_zero_nonaffine ha ha7 hab δ hσ] with e he
    rw [← hr, hr0] at he
    simpa using he

#print axioms sigma_zero_affine_iff

/-- **A negative `σ_a` kills the affine move for every `τ`** [L]: if `σ_a(δ) < 0` there is no `τ` for which `a/8 + e τ` is
lonely at all small `e > 0`. -/
theorem sigma_neg_no_affine {a b : ℕ} (ha : a % 2 = 1) (ha7 : a ≤ 7) (hab : a + b = 8) (δ : ℕ → ℝ)
    (hσ : sigma δ a b < 0) (τ : ℝ) :
    ∀ᶠ e in 𝓝[>] (0 : ℝ),
      ¬ Cascade.LonelyAt (PairLaw.pds (fun j => (j : ℝ) + e * δ j)) ((a : ℝ) / 8 + e * τ) := by
  have ht : (0 : ℝ) < (a : ℝ) / 8 := by
    have : (1 : ℝ) ≤ a := by exact_mod_cast (show 1 ≤ a by omega)
    positivity
  have hl : ∀ i : Fin 7, (1 / 8 : ℝ) ≤ distInt (apd i * ((a : ℝ) / 8)) := fun i => (ap_classes_fin ha ha7 i).1
  -- the first-order system has no solution at all
  have hno : ¬ ((∀ i : Fin 7, IsOpener (apd i * ((a : ℝ) / 8)) → 0 ≤ coefA (apd i) (δ ((i : ℕ) + 1)) ((a : ℝ) / 8) τ) ∧
      (∀ i : Fin 7, IsEntry (apd i * ((a : ℝ) / 8)) → coefA (apd i) (δ ((i : ℕ) + 1)) ((a : ℝ) / 8) τ ≤ 0)) := by
    intro h
    have := (ap_first_order_iff ha ha7 hab δ).mp ⟨τ, h⟩
    linarith
  have hv : (∃ i : Fin 7, IsOpener (apd i * ((a : ℝ) / 8)) ∧ coefA (apd i) (δ ((i : ℕ) + 1)) ((a : ℝ) / 8) τ < 0) ∨
      (∃ i : Fin 7, IsEntry (apd i * ((a : ℝ) / 8)) ∧ 0 < coefA (apd i) (δ ((i : ℕ) + 1)) ((a : ℝ) / 8) τ) := by
    by_contra hc
    push Not at hc
    exact hno ⟨fun i hi => hc.1 i hi, fun i hi => hc.2 i hi⟩
  filter_upwards [touch_fails_of_violation apd (fun i : Fin 7 => δ ((i : ℕ) + 1)) _ τ hl hv] with e he h
  rw [lonely_pds_fin] at h
  exact he h

#print axioms sigma_neg_no_affine

/-- **Exact classification of the affine move at the AP pair** [L].  Some `τ` makes `a/8 + e τ` lonely for `{j + e δ_j}` at
all small `e > 0` iff `σ_a(δ) > 0`, or `σ_a(δ) = 0` and `δ_a = 0`. -/
theorem affine_survival_classification {a b : ℕ} (ha : a % 2 = 1) (ha7 : a ≤ 7) (hab : a + b = 8) (δ : ℕ → ℝ) :
    (∃ τ : ℝ, ∀ᶠ e in 𝓝[>] (0 : ℝ),
        Cascade.LonelyAt (PairLaw.pds (fun j => (j : ℝ) + e * δ j)) ((a : ℝ) / 8 + e * τ)) ↔
      (0 < sigma δ a b ∨ (sigma δ a b = 0 ∧ δ a = 0)) := by
  constructor
  · rintro ⟨τ, hτ⟩
    rcases lt_trichotomy (sigma δ a b) 0 with h | h | h
    · exfalso
      obtain ⟨e, h1, h2⟩ := (sigma_neg_no_affine ha ha7 hab δ h τ |>.and hτ).exists
      exact h1 h2
    · exact Or.inr ⟨h, (sigma_zero_affine_iff ha ha7 hab δ h).mp ⟨τ, hτ⟩⟩
    · exact Or.inl h
  · rintro (h | ⟨h, h0⟩)
    · exact ap_displaced ha ha7 hab δ h
    · exact (sigma_zero_affine_iff ha ha7 hab δ h).mpr h0

#print axioms affine_survival_classification

/-- **The oracle (`PairLaw`) for the affine deformation `d_j = j + e δ_j`, exactly** [L].  For `e > 0` with positive
`d_a, d_b`: the class window `[u_a, w_a]` has positive width iff `σ_a > 0`, is the single point `u_a = w_a` iff `σ_a = 0`,
and is empty iff `σ_a < 0`; at `σ_a = 0` the point is `a/8 / (1 + e δ_a / a)`, the instant of `sigma_zero_nonaffine`. -/
theorem window_trichotomy (δ : ℕ → ℝ) {a b : ℕ} (ha1 : 1 ≤ a) (hb1 : 1 ≤ b) (e : ℝ) (he : 0 < e)
    (hda : 0 < (a : ℝ) + e * δ a) (hdb : 0 < (b : ℝ) + e * δ b) :
    (PairLaw.uA (fun j => (j : ℝ) + e * δ j) a < PairLaw.wA (fun j => (j : ℝ) + e * δ j) a b ↔ 0 < sigma δ a b) ∧
    (PairLaw.uA (fun j => (j : ℝ) + e * δ j) a = PairLaw.wA (fun j => (j : ℝ) + e * δ j) a b ↔ sigma δ a b = 0) ∧
    (PairLaw.wA (fun j => (j : ℝ) + e * δ j) a b < PairLaw.uA (fun j => (j : ℝ) + e * δ j) a ↔ sigma δ a b < 0) := by
  have hA : (0 : ℝ) < a := by exact_mod_cast ha1
  have hB : (0 : ℝ) < b := by exact_mod_cast hb1
  have hab : (0 : ℝ) < (a : ℝ) * b := by positivity
  have key := survival_form_is_linearisation δ ha1 hb1 e
  have hpos : 0 < e * ((a : ℝ) * b) := by positivity
  unfold PairLaw.uA PairLaw.wA
  simp only []
  have e1 : ((a : ℝ)) ^ 2 * (8 * ((b : ℝ) + e * δ b)) = (8 * a) * (a * ((b : ℝ) + e * δ b)) := by ring
  have e2 : (a : ℝ) * b * (8 * ((a : ℝ) + e * δ a)) = (8 * a) * (b * ((a : ℝ) + e * δ a)) := by ring
  have hpos8 : (0 : ℝ) < 8 * a := by positivity
  refine ⟨?_, ?_, ?_⟩
  · rw [div_lt_div_iff₀ (by positivity) (by positivity), e1, e2]
    constructor
    · intro h
      have := lt_of_mul_lt_mul_left h hpos8.le
      have h0 : 0 < e * ((a : ℝ) * b) * sigma δ a b := by rw [← key]; linarith
      exact (mul_pos_iff_of_pos_left hpos).mp h0
    · intro h
      have h0 : 0 < e * ((a : ℝ) * b) * sigma δ a b := mul_pos hpos h
      exact mul_lt_mul_of_pos_left (by linarith) hpos8
  · rw [div_eq_div_iff (by positivity) (by positivity), e1, e2]
    constructor
    · intro h
      have := mul_left_cancel₀ hpos8.ne' h
      have h0 : e * ((a : ℝ) * b) * sigma δ a b = 0 := by rw [← key]; linarith
      rcases mul_eq_zero.mp h0 with h | h
      · exact absurd h hpos.ne'
      · exact h
    · intro h
      have h0 : (b : ℝ) * ((a : ℝ) + e * δ a) - a * ((b : ℝ) + e * δ b) = 0 := by rw [key, h]; ring
      rw [show (a : ℝ) * ((b : ℝ) + e * δ b) = b * ((a : ℝ) + e * δ a) by linarith]
  · rw [div_lt_div_iff₀ (by positivity) (by positivity), e1, e2]
    constructor
    · intro h
      have := lt_of_mul_lt_mul_left h hpos8.le
      have h0 : e * ((a : ℝ) * b) * sigma δ a b < 0 := by rw [← key]; linarith
      by_contra hc; push Not at hc
      nlinarith
    · intro h
      have h0 : e * ((a : ℝ) * b) * sigma δ a b < 0 := mul_neg_of_pos_of_neg hpos h
      exact mul_lt_mul_of_pos_left (by linarith) hpos8

#print axioms window_trichotomy

/-- The class window's left end is the nonaffine instant: `u_a = a/8 / (1 + e δ_a / a)` [L]. -/
theorem uA_eq_nonaffine (δ : ℕ → ℝ) {a : ℕ} (ha1 : 1 ≤ a) (e : ℝ) (hne : 1 + e * (δ a / a) ≠ 0) :
    PairLaw.uA (fun j => (j : ℝ) + e * δ j) a = ((a : ℝ) / 8) / (1 + e * (δ a / a)) := by
  have hA : (a : ℝ) ≠ 0 := by
    have : (1 : ℝ) ≤ a := by exact_mod_cast ha1
    linarith
  unfold PairLaw.uA
  have h2 : (a : ℝ) + e * δ a ≠ 0 := by
    intro h
    apply hne
    have : (a : ℝ) * (1 + e * (δ a / a)) = (a : ℝ) + e * δ a := by field_simp
    rw [← this] at h
    exact (mul_eq_zero.mp h).resolve_left hA
  field_simp

#print axioms uA_eq_nonaffine

/-- **The scaling direction as the test case** [L].  For `δ_j = c j` (every speed scaled, `c ≠ 0`): `σ_a = 0` at every
AP pair; no affine `τ` survives (`sigma_zero_affine_iff`, since `δ_a = c a ≠ 0`; the same conclusion as
`ZeroMargin.scaling_B_obstruction`), while the instant `a/8 / (1 + e c)` survives for all small `e > 0`. -/
theorem scaling_case {a b : ℕ} (ha : a % 2 = 1) (ha7 : a ≤ 7) (hab : a + b = 8) (c : ℝ) (hc : c ≠ 0) :
    sigma (fun j => c * (j : ℝ)) a b = 0 ∧
    (¬ ∃ τ : ℝ, ∀ᶠ e in 𝓝[>] (0 : ℝ),
        Cascade.LonelyAt (PairLaw.pds (fun j => (j : ℝ) + e * (c * (j : ℝ)))) ((a : ℝ) / 8 + e * τ)) ∧
    (∀ᶠ e in 𝓝[>] (0 : ℝ),
        Cascade.LonelyAt (PairLaw.pds (fun j => (j : ℝ) + e * (c * (j : ℝ)))) (((a : ℝ) / 8) / (1 + e * c))) := by
  have ha1 : (a : ℝ) ≠ 0 := by
    have : (1 : ℝ) ≤ a := by exact_mod_cast (show 1 ≤ a by omega)
    linarith
  have hb1 : (b : ℝ) ≠ 0 := by
    have : (1 : ℝ) ≤ b := by exact_mod_cast (show 1 ≤ b by omega)
    linarith
  have hσ : sigma (fun j => c * (j : ℝ)) a b = 0 := by
    unfold sigma; field_simp; ring
  have hr : c * (a : ℝ) / a = c := by field_simp
  refine ⟨hσ, ?_, ?_⟩
  · rintro h
    have := (sigma_zero_affine_iff ha ha7 hab _ hσ).mp h
    simp only [mul_eq_zero] at this
    rcases this with h1 | h1
    · exact hc h1
    · exact ha1 h1
  · have := sigma_zero_nonaffine ha ha7 hab _ hσ
    simpa only [hr] using this

#print axioms scaling_case

/-- **The second-order pair law, every direction** [L].  For every direction `δ` and every AP mirror pair `(a, 8 - a)`,
one of the instants `a/8`, `(8-a)/8` is displaced to a lonely instant of `{j + e δ_j}` for all small `e > 0`, along a
move `f(e) -> a/8` (resp. `(8-a)/8`): along an affine move if `σ_a != 0`, along `a/8 / (1 + e δ_a / a)` if `σ_a = 0`
(where both instants survive).  This extends `ZeroMargin.ap_mirror_survival` (first order) to all orders. -/
theorem ap_pair_survives_every_direction {a b : ℕ} (ha : a % 2 = 1) (ha7 : a ≤ 7) (hab : a + b = 8) (δ : ℕ → ℝ) :
    (∃ f : ℝ → ℝ, Tendsto f (𝓝[>] (0 : ℝ)) (𝓝 ((a : ℝ) / 8)) ∧ ∀ᶠ e in 𝓝[>] (0 : ℝ),
        Cascade.LonelyAt (PairLaw.pds (fun j => (j : ℝ) + e * δ j)) (f e)) ∨
    (∃ f : ℝ → ℝ, Tendsto f (𝓝[>] (0 : ℝ)) (𝓝 ((b : ℝ) / 8)) ∧ ∀ᶠ e in 𝓝[>] (0 : ℝ),
        Cascade.LonelyAt (PairLaw.pds (fun j => (j : ℝ) + e * δ j)) (f e)) := by
  have hb : b % 2 = 1 := by omega
  have hb7 : b ≤ 7 := by omega
  have ha1 : (1 : ℝ) ≤ a := by exact_mod_cast (show 1 ≤ a by omega)
  have aff : ∀ (c τ : ℝ), Tendsto (fun e : ℝ => c + e * τ) (𝓝[>] (0 : ℝ)) (𝓝 c) := by
    intro c τ
    have hc : Continuous (fun e : ℝ => c + e * τ) := by fun_prop
    have := hc.tendsto 0
    simp only [zero_mul, add_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  rcases lt_trichotomy (sigma δ a b) 0 with h | h | h
  · right
    have hneg : 0 < sigma δ b a := by rw [sigma_antisymm]; linarith
    obtain ⟨τ, hτ⟩ := ap_displaced hb hb7 (by omega : b + a = 8) δ hneg
    exact ⟨_, aff _ τ, hτ⟩
  · left
    refine ⟨fun e => ((a : ℝ) / 8) / (1 + e * (δ a / a)), ?_, sigma_zero_nonaffine ha ha7 hab δ h⟩
    have hc : ContinuousAt (fun e : ℝ => ((a : ℝ) / 8) / (1 + e * (δ a / a))) 0 := by
      apply ContinuousAt.div continuousAt_const (by fun_prop)
      simp
    have := hc.tendsto
    simp only [zero_mul, add_zero, div_one] at this
    exact this.mono_left nhdsWithin_le_nhds
  · left
    obtain ⟨τ, hτ⟩ := ap_displaced ha ha7 hab δ h
    exact ⟨_, aff _ τ, hτ⟩

#print axioms ap_pair_survives_every_direction

end TouchTheory

end Fresh
