import Mathlib
import Fresh.Framework

/-!
# The cascade, natively (Task C; v9 section 6, Theorems 11 to 13)

Built on `Fresh/Framework.lean` only (its `distInt`, `InWay`, `nextOpening`, `IsMove`, `CascadeFixes`,
`CascadeForm`, `LonelyRunnerEight`).  Nothing is imported from the existing `LonelyRunner` repo; every proof below
was written for this file.  Provenance (the existing declaration each theorem corresponds to, whose argument was
read and understood, not copied) is recorded on each theorem.  Exact reals only; no floats; no runner is stationary
(every disparity used is positive, and positivity of the disparities of an arrangement is proved, not assumed).

Contents.
* (1) Basic facts: a runner in the way at `t` has its next opening strictly after `t`, stands at exactly `1/8` there,
  and is in the way at every instant of `[t, nextOpening d t)`.
* (2) No overshoot: a move from `t ≤ s` with `s` lonely lands at or before `s`; so does every cascade sequence.
* (3) Fixed points: `IsMove ds t t ↔ LonelyAt ds t`.  The move is also deterministic and always exists.
* (4) Classification: `Isolation v k ↔ CascadeFixes (disparitySet v k) (1/(8m))` with `m = d_min`
  (`cascadeFixes_iff_isolation`), and `CascadeForm ↔ LonelyRunnerEight` (`cascadeForm_iff`).
-/

open Classical

namespace Fresh

namespace Cascade

/-! ## Basic facts about `distInt` -/

/-- `distInt x` is at most the distance from `x` to any integer. -/
theorem distInt_le (x : ℝ) (k : ℤ) : distInt x ≤ |x - k| := by
  unfold distInt
  exact round_le x k

#print axioms distInt_le

theorem distInt_nonneg (x : ℝ) : 0 ≤ distInt x := abs_nonneg _

#print axioms distInt_nonneg

/-- Shifting by a whole lap does not change `distInt`. -/
theorem distInt_add_int (x : ℝ) (k : ℤ) : distInt (x + k) = distInt x := by
  unfold distInt
  rw [round_add_intCast]
  push_cast
  ring_nf

#print axioms distInt_add_int

/-- Direction does not matter: `distInt (-x) = distInt x` (no tie-breaking issue: proved by `distInt_le` both ways). -/
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

theorem distInt_abs_mul (x t : ℝ) : distInt (|x| * t) = distInt (x * t) := by
  rcases abs_choice x with h | h
  · rw [h]
  · rw [h, neg_mul, distInt_neg]

#print axioms distInt_abs_mul

/-- `distInt (1/8 + k) = 1/8`: an opening stands at exactly one eighth. -/
theorem distInt_eighth_add_int (k : ℤ) : distInt (1 / 8 + k) = 1 / 8 := by
  rw [distInt_add_int]
  unfold distInt
  have : round (1 / 8 : ℝ) = 0 := by
    rw [round_eq, Int.floor_eq_iff]
    norm_num
  rw [this]
  norm_num

#print axioms distInt_eighth_add_int

/-! ## (1) In the way, and the next opening

Provenance: `MomentIterationN.exists_near_int`, `nextOpening_eq`, `lt_nextOpening`, `circDist_at_nextOpening`,
`inWay_until_opening` (existing `Cascade/Iteration.lean`, stated there with `circDist` and threshold `1/n`).  Re-proved
here for `distInt = |x - round x|` at threshold `1/8`; the arguments were read and understood, not copied. -/

/-- In the way means within `1/8` of a whole lap `k` (the nearest integer). -/
theorem exists_near_int {d t : ℝ} (h : InWay d t) : ∃ k : ℤ, |d * t - k| < 1 / 8 :=
  ⟨round (d * t), h⟩

#print axioms exists_near_int

/-- Within `1/8` of the lap `k`, the next opening is `(k + 1/8)/d`. -/
theorem nextOpening_eq {d t : ℝ} {k : ℤ} (hk : |d * t - k| < 1 / 8) :
    nextOpening d t = ((k : ℝ) + 1 / 8) / d := by
  unfold nextOpening
  have hc : ⌈d * t - 1 / 8⌉ = k := by
    rw [Int.ceil_eq_iff]
    have := abs_lt.mp hk
    constructor <;> linarith
  rw [hc]

#print axioms nextOpening_eq

/-- **The next opening is strictly after `t`.** -/
theorem lt_nextOpening {d t : ℝ} (hd : 0 < d) (h : InWay d t) : t < nextOpening d t := by
  obtain ⟨k, hk⟩ := exists_near_int h
  rw [nextOpening_eq hk, lt_div_iff₀ hd]
  have := abs_lt.mp hk
  linarith

#print axioms lt_nextOpening

/-- **At its next opening the runner stands at exactly `1/8`** (so it is clear there). -/
theorem distInt_at_nextOpening {d t : ℝ} (hd : 0 < d) :
    distInt (d * nextOpening d t) = 1 / 8 := by
  unfold nextOpening
  have e : d * ((((⌈d * t - 1 / 8⌉ : ℤ) : ℝ) + 1 / 8) / d) = 1 / 8 + ((⌈d * t - 1 / 8⌉ : ℤ) : ℝ) := by
    field_simp
    ring
  rw [e, distInt_eighth_add_int]

#print axioms distInt_at_nextOpening

theorem not_inWay_at_nextOpening {d t : ℝ} (hd : 0 < d) : ¬ InWay d (nextOpening d t) := by
  unfold InWay
  rw [distInt_at_nextOpening hd]
  exact lt_irrefl _

#print axioms not_inWay_at_nextOpening

/-- **A runner in the way stays in the way until its next opening**: every instant of `[t, nextOpening d t)` has it
within `1/8` of the same lap. -/
theorem inWay_until_opening {d t s : ℝ} (hd : 0 < d) (h : InWay d t) (hts : t ≤ s)
    (hs : s < nextOpening d t) : InWay d s := by
  obtain ⟨k, hk⟩ := exists_near_int h
  rw [nextOpening_eq hk, lt_div_iff₀ hd] at hs
  have h1 := abs_lt.mp hk
  have hds : d * t ≤ d * s := mul_le_mul_of_nonneg_left hts hd.le
  unfold InWay
  refine lt_of_le_of_lt (distInt_le (d * s) k) ?_
  rw [abs_lt]
  constructor <;> nlinarith

#print axioms inWay_until_opening

/-! ## (2) Lonely instants and no overshoot -/

/-- The subject is lonely at `s` for the disparities `ds`: every runner at distance at least `1/8` (closed). -/
-- STANDING: DEFINITION
def LonelyAt (ds : Finset ℝ) (s : ℝ) : Prop := ∀ d ∈ ds, (1 / 8 : ℝ) ≤ distInt (d * s)

theorem not_inWay_iff {d t : ℝ} : ¬ InWay d t ↔ (1 / 8 : ℝ) ≤ distInt (d * t) := not_lt

#print axioms not_inWay_iff

/-- **No instant strictly between `t` and the next opening of a runner in the way is lonely**: a lonely `s ≥ t` lies at
or after that opening.  (Provenance: `MomentIterationN.nextOpening_le_of_lonely`.) -/
theorem nextOpening_le_of_lonely {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d) {t s : ℝ}
    (hl : LonelyAt ds s) (hts : t ≤ s) {d : ℝ} (hd : d ∈ ds) (hw : InWay d t) :
    nextOpening d t ≤ s := by
  by_contra hc
  push Not at hc
  exact (not_inWay_iff.mpr (hl d hd)) (inWay_until_opening (hpos d hd) hw hts hc)

#print axioms nextOpening_le_of_lonely

/-- A move never goes backwards; it fixes `t` or goes strictly forward. -/
theorem le_of_isMove {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d) {t t' : ℝ} (hm : IsMove ds t t') : t ≤ t' := by
  rcases hm with ⟨_, rfl⟩ | ⟨d, hd, hw, rfl, _⟩
  · exact le_rfl
  · exact (lt_nextOpening (hpos d hd) hw).le

#print axioms le_of_isMove

theorem lt_of_isMove_of_ne {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d) {t t' : ℝ} (hm : IsMove ds t t')
    (hne : t' ≠ t) : t < t' :=
  lt_of_le_of_ne (le_of_isMove hpos hm) (Ne.symm hne)

#print axioms lt_of_isMove_of_ne

/-- **(2) No overshoot.**  A move from `t ≤ s`, with `s` lonely, lands at or before `s`.  No positivity of `s` is
needed.  (Provenance: `MomentIterationN.move_le_of_lonely`, there for the `fold max` function; here for the
relation `IsMove`.) -/
theorem isMove_le_of_lonely {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d) {t t' s : ℝ}
    (hl : LonelyAt ds s) (hts : t ≤ s) (hm : IsMove ds t t') : t' ≤ s := by
  rcases hm with ⟨_, rfl⟩ | ⟨d, hd, hw, rfl, _⟩
  · exact hts
  · exact nextOpening_le_of_lonely hpos hl hts hd hw

#print axioms isMove_le_of_lonely

/-- **Every cascade sequence from `t₀ ≤ s` stays at or below a lonely `s`.**
(Provenance: `MomentIterationN.iterate_le_of_lonely`.) -/
theorem seq_le_of_lonely {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d) {s : ℝ} (hl : LonelyAt ds s)
    {seq : ℕ → ℝ} (h0 : seq 0 ≤ s) (hmv : ∀ n, IsMove ds (seq n) (seq (n + 1))) : ∀ n, seq n ≤ s := by
  intro n
  induction n with
  | zero => exact h0
  | succ n ih => exact isMove_le_of_lonely hpos hl ih (hmv n)

#print axioms seq_le_of_lonely

/-- A cascade sequence never goes below its start. -/
theorem start_le_seq {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d) {seq : ℕ → ℝ}
    (hmv : ∀ n, IsMove ds (seq n) (seq (n + 1))) : ∀ n, seq 0 ≤ seq n := by
  intro n
  induction n with
  | zero => exact le_rfl
  | succ n ih => exact le_trans ih (le_of_isMove hpos (hmv n))

#print axioms start_le_seq

/-! ## (3) Fixed points; the move exists and is unique -/

/-- **(3) A fixed point of the move is exactly a lonely instant.**  (`→`: a runner in the way would send the move
strictly forward.  `←`: nobody is in the way, so the first clause of `IsMove` fixes `t`.)
(Provenance: `MomentIterationN.lonely_of_fixed`, one direction.) -/
theorem isMove_self_iff {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d) {t : ℝ} :
    IsMove ds t t ↔ LonelyAt ds t := by
  constructor
  · rintro (⟨h, _⟩ | ⟨d, hd, hw, he, _⟩)
    · exact fun d hd => not_inWay_iff.mp (h d hd)
    · exact absurd he (ne_of_lt (lt_nextOpening (hpos d hd) hw))
  · intro hl
    exact Or.inl ⟨fun d hd => not_inWay_iff.mpr (hl d hd), rfl⟩

#print axioms isMove_self_iff

/-- **The cascade is deterministic**: the move from `t` is unique (rule 14, the cascade is not random). -/
theorem isMove_unique {ds : Finset ℝ} {t t₁ t₂ : ℝ} (h₁ : IsMove ds t t₁) (h₂ : IsMove ds t t₂) : t₁ = t₂ := by
  rcases h₁ with ⟨hn₁, rfl⟩ | ⟨d₁, hd₁, hw₁, he₁, hmax₁⟩ <;>
    rcases h₂ with ⟨hn₂, rfl⟩ | ⟨d₂, hd₂, hw₂, he₂, hmax₂⟩
  · rfl
  · exact absurd hw₂ (hn₁ d₂ hd₂)
  · exact absurd hw₁ (hn₂ d₁ hd₁)
  · apply le_antisymm
    · rw [he₁]; exact hmax₂ d₁ hd₁ hw₁
    · rw [he₂]; exact hmax₁ d₂ hd₂ hw₂

#print axioms isMove_unique

/-- **The move always exists**: if nobody is in the way, fix; otherwise the largest next opening over the (finite,
nonempty) set of runners in the way. -/
theorem exists_isMove (ds : Finset ℝ) (t : ℝ) : ∃ t', IsMove ds t t' := by
  by_cases h : ∃ d ∈ ds, InWay d t
  · have hne : (ds.filter (fun d => InWay d t)).Nonempty := by
      obtain ⟨d, hd, hw⟩ := h
      exact ⟨d, Finset.mem_filter.mpr ⟨hd, hw⟩⟩
    obtain ⟨d, hdF, hmax⟩ := (ds.filter (fun d => InWay d t)).exists_max_image (fun d => nextOpening d t) hne
    rw [Finset.mem_filter] at hdF
    exact ⟨nextOpening d t, Or.inr ⟨d, hdF.1, hdF.2, rfl,
      fun d' hd' hw' => hmax d' (Finset.mem_filter.mpr ⟨hd', hw'⟩)⟩⟩
  · push Not at h
    exact ⟨t, Or.inl ⟨h, rfl⟩⟩

#print axioms exists_isMove

/-- The move as a function (its value is unique by `isMove_unique`). -/
noncomputable def step (ds : Finset ℝ) (t : ℝ) : ℝ := Classical.choose (exists_isMove ds t)

theorem isMove_step (ds : Finset ℝ) (t : ℝ) : IsMove ds t (step ds t) :=
  Classical.choose_spec (exists_isMove ds t)

#print axioms isMove_step

/-- The cascade sequence from `t₀`. -/
noncomputable def cascadeSeq (ds : Finset ℝ) (t₀ : ℝ) (n : ℕ) : ℝ := (step ds)^[n] t₀

theorem cascadeSeq_zero (ds : Finset ℝ) (t₀ : ℝ) : cascadeSeq ds t₀ 0 = t₀ := rfl

#print axioms cascadeSeq_zero

theorem cascadeSeq_isMove (ds : Finset ℝ) (t₀ : ℝ) (n : ℕ) :
    IsMove ds (cascadeSeq ds t₀ n) (cascadeSeq ds t₀ (n + 1)) := by
  unfold cascadeSeq
  rw [Function.iterate_succ_apply']
  exact isMove_step ds _

#print axioms cascadeSeq_isMove

/-- **Every cascade sequence is the cascade sequence**: by determinism, any sequence of moves from `t₀` agrees with
`cascadeSeq ds t₀` term by term. -/
theorem seq_eq_cascadeSeq {ds : Finset ℝ} {seq : ℕ → ℝ} (hmv : ∀ n, IsMove ds (seq n) (seq (n + 1))) :
    ∀ n, seq n = cascadeSeq ds (seq 0) n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    have h := cascadeSeq_isMove ds (seq 0) n
    rw [← ih] at h
    exact isMove_unique (hmv n) h

#print axioms seq_eq_cascadeSeq

/-! ## (4) The classification -/

/-- The openings of the runners of `ds` at laps `0 … ⌈d·s⌉`: a finite set. -/
noncomputable def openingsUpTo (ds : Finset ℝ) (s : ℝ) : Finset ℝ :=
  ds.biUnion (fun d => (Finset.Icc (0 : ℤ) ⌈d * s⌉).image (fun k : ℤ => ((k : ℝ) + 1 / 8) / d))

/-- A move from a positive `t ≤ s` (with `s` lonely) either fixes `t` or lands on one of the openings up to `s`.
(Provenance: the inductive step of `MomentIterationN.iterate_mem_openings`.) -/
theorem isMove_mem_openings {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d) {t t' s : ℝ} (ht : 0 < t)
    (hl : LonelyAt ds s) (hts : t ≤ s) (hm : IsMove ds t t') : t' = t ∨ t' ∈ openingsUpTo ds s := by
  have hle := isMove_le_of_lonely hpos hl hts hm
  rcases hm with ⟨_, rfl⟩ | ⟨d, hd, hw, rfl, _⟩
  · exact Or.inl rfl
  · right
    have hdpos := hpos d hd
    have hgt := lt_nextOpening hdpos hw
    obtain ⟨k, hk⟩ := exists_near_int hw
    rw [nextOpening_eq hk] at hle hgt ⊢
    have hk_up : (k : ℝ) ≤ d * s := by
      rw [div_le_iff₀ hdpos] at hle
      linarith
    have hk_lo : (0 : ℝ) < (k : ℝ) + 1 / 8 := by
      have : 0 < ((k : ℝ) + 1 / 8) / d := lt_trans ht hgt
      exact (div_pos_iff_of_pos_right hdpos).mp this
    have hk0 : (0 : ℤ) ≤ k := by
      by_contra hc
      push Not at hc
      have : (k : ℝ) ≤ -1 := by exact_mod_cast (show k ≤ -1 by omega)
      linarith
    have hkc : k ≤ ⌈d * s⌉ := by
      have := Int.le_ceil (d * s)
      exact_mod_cast le_trans hk_up this
    exact Finset.mem_biUnion.mpr ⟨d, hd, Finset.mem_image.mpr ⟨k, Finset.mem_Icc.mpr ⟨hk0, hkc⟩, rfl⟩⟩

#print axioms isMove_mem_openings

/-- **A lonely instant forces the cascade to fix.**  From a positive `t₀ ≤ s`, with `s` lonely, the cascade sequence
reaches a fixed point.

The argument: every term is `≤ s` (no overshoot), a term that is not fixed is strictly passed (`lt_of_isMove_of_ne`),
and every term lies in the finite set `insert t₀ (openingsUpTo ds s)`.
[PROVISIONAL: counting tool] the last step (an injective map from `ℕ` into a finite set is impossible) supports the
claim "the sequence cannot move forever below `s`".
(Provenance: `MomentIterationN.exists_fixed_of_lonely`.) -/
theorem exists_fixed_of_lonely {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d) {t₀ s : ℝ} (ht₀ : 0 < t₀)
    (hl : LonelyAt ds s) (h0 : t₀ ≤ s) :
    ∃ N, cascadeSeq ds t₀ (N + 1) = cascadeSeq ds t₀ N := by
  set seq := cascadeSeq ds t₀ with hseq
  have hmv : ∀ n, IsMove ds (seq n) (seq (n + 1)) := cascadeSeq_isMove ds t₀
  have hle : ∀ n, seq n ≤ s := seq_le_of_lonely hpos hl h0 hmv
  have hge : ∀ n, t₀ ≤ seq n := start_le_seq hpos hmv
  have hmem : ∀ n, seq n ∈ insert t₀ (openingsUpTo ds s) := by
    intro n
    induction n with
    | zero => exact Finset.mem_insert_self _ _
    | succ n ih =>
      rcases isMove_mem_openings hpos (lt_of_lt_of_le ht₀ (hge n)) hl (hle n) (hmv n) with h | h
      · rw [h]; exact ih
      · exact Finset.mem_insert_of_mem h
  by_contra hne
  push Not at hne
  have hsm : StrictMono seq :=
    strictMono_nat_of_lt_succ (fun n => lt_of_isMove_of_ne hpos (hmv n) (hne n))
  -- [PROVISIONAL: counting tool] supporting "the sequence cannot move forever below s".
  have hinf : (↑(insert t₀ (openingsUpTo ds s)) : Set ℝ).Infinite :=
    Set.infinite_of_injective_forall_mem hsm.injective (fun n => Finset.mem_coe.mpr (hmem n))
  exact hinf (Finset.finite_toSet _)

#print axioms exists_fixed_of_lonely

/-- The disparities of an arrangement are all positive (two runners never share a speed). -/
theorem disparitySet_pos {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8) :
    ∀ d ∈ disparitySet v k, 0 < d := by
  intro d hd
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hd
  have hik : i ≠ k := (Finset.mem_erase.mp hi).1
  exact abs_pos.mpr (sub_ne_zero.mpr (fun h => hik (hv.2 h)))

#print axioms disparitySet_pos

/-- Isolation of runner `k` at `t` is loneliness for its disparity set (direction of a reading is irrelevant). -/
theorem isolatedAt_iff_lonelyAt (v : Fin 8 → ℝ) (k : Fin 8) (t : ℝ) :
    IsolatedAt v k t ↔ LonelyAt (disparitySet v k) t := by
  constructor
  · intro h d hd
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hd
    rw [distInt_abs_mul]
    exact h i (Finset.mem_erase.mp hi).1
  · intro h i hi
    have := h (|v i - v k|) (Finset.mem_image_of_mem _ (Finset.mem_erase.mpr ⟨hi, Finset.mem_univ i⟩))
    rwa [distInt_abs_mul] at this

#print axioms isolatedAt_iff_lonelyAt

/-- **Nothing positive before the bound** `1/(8m)` (v9 Theorem 7): if `m ∈ ds` then a lonely `s > 0` has
`s ≥ 1/(8m)`.  (Provenance: `MomentIterationN.bound_le_of_lonely`; proved here directly, with the integer `0`.) -/
theorem bound_le_of_lonely {ds : Finset ℝ} {m s : ℝ} (hm : m ∈ ds) (hmpos : 0 < m)
    (hl : LonelyAt ds s) (hs : 0 < s) : 1 / (8 * m) ≤ s := by
  by_contra hc
  push Not at hc
  have hms : m * s < 1 / 8 := by
    rw [lt_div_iff₀ (by positivity)] at hc
    linarith
  have h1 := distInt_le (m * s) 0
  have hpos : 0 < m * s := mul_pos hmpos hs
  rw [Int.cast_zero, sub_zero, abs_of_pos hpos] at h1
  have := hl m hm
  linarith

#print axioms bound_le_of_lonely

/-- **The fixed point of the cascade from the bound is the first isolation** (v9 Theorem 11, first-ness): it is lonely
and lies at or before every positive lonely instant.  (Provenance: `MomentIterationN.first_isolation_of_fixed`.) -/
theorem fixed_is_first_isolation {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d) {m : ℝ} (hm : m ∈ ds)
    {seq : ℕ → ℝ} (h0 : seq 0 = 1 / (8 * m)) (hmv : ∀ n, IsMove ds (seq n) (seq (n + 1)))
    {N : ℕ} (hN : seq (N + 1) = seq N) :
    LonelyAt ds (seq N) ∧ ∀ s, 0 < s → LonelyAt ds s → seq N ≤ s := by
  refine ⟨?_, fun s hs hl => ?_⟩
  · have h := hmv N
    rw [hN] at h
    exact (isMove_self_iff hpos).mp h
  · exact seq_le_of_lonely hpos hl (h0 ▸ bound_le_of_lonely hm (hpos m hm) hl hs) hmv N

#print axioms fixed_is_first_isolation

/-- **(4) The classification of candidate (b).**  For an arrangement and a subject `k` with `d_min = m`: runner `k` is
isolated at some positive instant iff the cascade from `1/(8m)` reaches a fixed point.
(Provenance: `MomentIterationN.lonely_iff_run_ends` first part, and `LRC.Spec.doors_agree` / `doorArrives_iff`.) -/
theorem cascadeFixes_iff_isolation {v : Fin 8 → ℝ} (hv : IsArrangement v) {k : Fin 8} {m : ℝ}
    (hm : IsDmin v k m) : Isolation v k ↔ CascadeFixes (disparitySet v k) (1 / (8 * m)) := by
  have hpos := disparitySet_pos hv k
  have hmem : m ∈ disparitySet v k := hm.1
  have hmpos : 0 < m := hpos m hmem
  have hb : 0 < 1 / (8 * m) := by positivity
  constructor
  · rintro ⟨s, hs, hiso⟩
    have hl := (isolatedAt_iff_lonelyAt v k s).mp hiso
    obtain ⟨N, hN⟩ := exists_fixed_of_lonely hpos hb hl (bound_le_of_lonely hmem hmpos hl hs)
    exact ⟨cascadeSeq _ _, cascadeSeq_zero _ _, cascadeSeq_isMove _ _, N, hN⟩
  · rintro ⟨seq, h0, hmv, N, hN⟩
    have hfix := fixed_is_first_isolation hpos hmem h0 hmv hN
    have hge : seq 0 ≤ seq N := start_le_seq hpos hmv N
    refine ⟨seq N, lt_of_lt_of_le (h0 ▸ hb) hge, ?_⟩
    exact (isolatedAt_iff_lonelyAt v k _).mpr hfix.1

#print axioms cascadeFixes_iff_isolation

/-- Every subject of an arrangement has a smallest disparity. -/
theorem exists_dmin {v : Fin 8 → ℝ} (k : Fin 8) : ∃ m, IsDmin v k m := by
  have hne : (disparitySet v k).Nonempty := by
    refine Finset.Nonempty.image ?_ _
    by_cases hk : k = 0
    · exact ⟨1, Finset.mem_erase.mpr ⟨by rw [hk]; decide, Finset.mem_univ _⟩⟩
    · exact ⟨0, Finset.mem_erase.mpr ⟨fun h => hk h.symm, Finset.mem_univ _⟩⟩
  refine ⟨(disparitySet v k).min' hne, Finset.min'_mem _ _, ?_⟩
  intro x hx
  exact Finset.min'_le _ _ hx

#print axioms exists_dmin

/-- **Candidate (b) is the conjecture**: `CascadeForm ↔ LonelyRunnerEight`.  So (b) is a restatement, not a reduction:
it has exactly the content of the conjecture. -/
theorem cascadeForm_iff : CascadeForm ↔ LonelyRunnerEight := by
  constructor
  · intro h v hv k
    obtain ⟨m, hm⟩ := exists_dmin (v := v) k
    exact (cascadeFixes_iff_isolation hv hm).mpr (h v hv k m hm)
  · intro h v hv k m hm
    exact (cascadeFixes_iff_isolation hv hm).mp (h v hv k)

#print axioms cascadeForm_iff

end Cascade

end Fresh
