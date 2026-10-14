import Mathlib
import Fresh.Framework
import Fresh.PathLaws
import Fresh.PathForm

/-!
# Classification of the two owed path statements (Task AF)

Written 2026-10-09.  Imports `Mathlib`, `Fresh.Framework`, `Fresh.PathLaws`, `Fresh.PathForm` (and, through them, the
Fresh modules `Grid`, `Localisation`, `LonelyCells`, `Gate`).  Nothing from the existing `LonelyRunner` repo.  Exact
reals; every speed positive; no counting, covering or bound as the SHAPE of a result.

The two owed statements of `PathLaws` are `SuccessorIsolation` and `PathLonelyBound` (the latter is cap-shaped, rule 7).
This file classifies them, as stage 1 classified the candidate forms of "the displacement is forced".

Results ([L] = Lean; `#print axioms` after each theorem).
* (1) `lre_isoSet_eq`, `lre_imp_successorIsolation`, `lre_imp_right`, `lre_imp_closed`: the conjecture on a path of
  arrangements gives `isoSet = [0,1]`, hence `SuccessorIsolation` (every point of `[0,1]` has the neighbourhood
  `[0,1]` inside `isoSet`).  Converse fails alone: `successorIsolation_only_openness` (it gives openness at `0` and no more).
* (2) `PathLonelyBound` against the conjecture.  `pathLonelyBound_iff_localBound` (a uniform bound is the same as a
  bound near each point of `[0,1]`, by compactness); `localBound_of_strict` (a lonely instant with every runner strictly
  clear gives a local bound); `not_localBound_imp_touch` (a point without a local bound has ONLY zero-margin lonely
  instants); `not_localBound_imp_seq` (the escaping sequence: `s_n -> s0`, `s_n` in the isolation set, every lonely
  instant at `s_n` later than `n`).  The conjecture does not give a local bound at a touch-only point: that is the content
  owed.  Searched exactly for a path with this behaviour: none found ([OBS], see the report).
* (3) The weakest local hypotheses.  `isoSet_eq_iff`: `isoSet = [0,1]` iff `0 ∈ isoSet`, `isoSet` closed and
  `RightIsolation` (isolation at `s0 < 1` persists to the right).  `isoSet_eq_iff_leftClosed`: closedness may be
  weakened to `LeftClosed` (only limits from the left).  `isClosed_iff_no_escape`: closedness is the absence of an
  `EscapeAt` point, and at an escape point every witness sequence tends to infinity (`escape_witnesses_diverge`, from
  `isoSet_dichotomy`).  `lre_iff_leftClosed_right`: the conjecture is equivalent to `LeftClosed ∧ RightIsolation` along
  admissible paths.  `pathLonelyBound_imp_leftClosed`: the bound is sufficient for closedness; whether it is necessary
  is the open point.
* (4) The margin-positive form is the WRONG theory: `ap_not_strict` (Dirichlet: at the AP `(1,…,8)` no instant has every
  runner strictly clear), `strictForm_refuted` (`StrictLocalForm` is false).  So no argument of the shape "a strictly
  clear instant exists at every arrangement" is available, and at the AP every lonely instant is a touch.

Provenance.  The real-line induction is `isoSet_eq_of_owed` in `PathLaws` (re-used for the closed case) and a direct
`sSup` argument for the left-closed case (not found in the existing repo; no proof copied).  The compactness step uses
Mathlib's `IsCompact.induction_on`.  The Dirichlet step is Mathlib's `Real.exists_int_int_abs_mul_sub_le`.
-/

open Classical Filter Topology

namespace Fresh

namespace PathClassify

open PathLaws

/-- An admissible path: continuous on `[0,1]` with an arrangement at every parameter. -/
-- STANDING: DEFINITION
def AdmissiblePath (v : ℝ → Fin 8 → ℝ) : Prop :=
  ContinuousOn v (Set.Icc 0 1) ∧ ∀ s ∈ Set.Icc (0 : ℝ) 1, IsArrangement (v s)

/-! ## (1) The conjecture gives the isolation set `[0,1]`, hence `SuccessorIsolation` -/

/-- **The conjecture along a path of arrangements** [L]: `isoSet v k = [0,1]`. -/
theorem lre_isoSet_eq (h : LonelyRunnerEight) {v : ℝ → Fin 8 → ℝ}
    (hv : ∀ s ∈ Set.Icc (0 : ℝ) 1, IsArrangement (v s)) (k : Fin 8) : isoSet v k = Set.Icc 0 1 := by
  ext s
  exact ⟨fun hs => hs.1, fun hs => ⟨hs, h _ (hv s hs) k⟩⟩

#print axioms lre_isoSet_eq

/-- **`LonelyRunnerEight → SuccessorIsolation`** [L].  Precisely: for every path of arrangements on `[0,1]` and every
subject, every `s0 ∈ isoSet` (that is, every `s0 ∈ [0,1]`) has `isoSet` as a neighbourhood within `[0,1]`: the
neighbourhood is `[0,1]` itself. -/
theorem lre_imp_successorIsolation (h : LonelyRunnerEight) {v : ℝ → Fin 8 → ℝ}
    (hv : ∀ s ∈ Set.Icc (0 : ℝ) 1, IsArrangement (v s)) (k : Fin 8) : SuccessorIsolation v k := by
  intro s₀ _
  filter_upwards [self_mem_nhdsWithin] with s hs
  rw [lre_isoSet_eq h hv k]
  exact hs

#print axioms lre_imp_successorIsolation

/-- The one-sided persistence: isolation at `s0 < 1` persists on some interval to the right of `s0`.  This is the part of
`SuccessorIsolation` that the real-line induction uses. -/
-- STANDING: DEFINITION
def RightIsolation (v : ℝ → Fin 8 → ℝ) (k : Fin 8) : Prop :=
  ∀ s₀ ∈ isoSet v k, s₀ < 1 → ∀ᶠ s in 𝓝[>] s₀, s ∈ isoSet v k

/-- `SuccessorIsolation` is strictly more than `RightIsolation` in form (two-sided neighbourhood) [L]. -/
theorem successorIsolation_imp_right {v : ℝ → Fin 8 → ℝ} {k : Fin 8} (hS : SuccessorIsolation v k) :
    RightIsolation v k := by
  intro s₀ hs₀ h1
  have hmem : Set.Icc (0 : ℝ) 1 ∈ 𝓝[>] s₀ :=
    Filter.mem_of_superset (Ioo_mem_nhdsGT h1) (fun y hy => ⟨(hs₀.1.1).trans hy.1.le, hy.2.le⟩)
  have hle : 𝓝[>] s₀ ≤ 𝓝[Set.Icc 0 1] s₀ := nhdsWithin_le_of_mem hmem
  exact hle (hS s₀ hs₀)

#print axioms successorIsolation_imp_right

theorem lre_imp_right (h : LonelyRunnerEight) {v : ℝ → Fin 8 → ℝ}
    (hv : ∀ s ∈ Set.Icc (0 : ℝ) 1, IsArrangement (v s)) (k : Fin 8) : RightIsolation v k :=
  successorIsolation_imp_right (lre_imp_successorIsolation h hv k)

#print axioms lre_imp_right

theorem lre_imp_closed (h : LonelyRunnerEight) {v : ℝ → Fin 8 → ℝ}
    (hv : ∀ s ∈ Set.Icc (0 : ℝ) 1, IsArrangement (v s)) (k : Fin 8) : IsClosed (isoSet v k) := by
  rw [lre_isoSet_eq h hv k]; exact isClosed_Icc

#print axioms lre_imp_closed

/-- `SuccessorIsolation` with `0 ∈ isoSet` gives only a start interval [L]: openness at `0`.  Nothing beyond the
first interval follows without closedness (see `isoSet_eq_iff`). -/
theorem successorIsolation_only_openness {v : ℝ → Fin 8 → ℝ} {k : Fin 8} (hS : SuccessorIsolation v k)
    (h0 : (0 : ℝ) ∈ isoSet v k) : ∃ ε : ℝ, 0 < ε ∧ ∀ s ∈ Set.Ico (0 : ℝ) ε, s ∈ isoSet v k := by
  have h := successorIsolation_imp_right hS 0 h0 zero_lt_one
  obtain ⟨b, hb, hsub⟩ := (mem_nhdsGT_iff_exists_Ioo_subset' (by norm_num : (0 : ℝ) < 1)).mp h
  refine ⟨b, hb, fun s hs => ?_⟩
  rcases eq_or_lt_of_le hs.1 with h' | h'
  · rw [← h']; exact h0
  · exact hsub ⟨h', hs.2⟩

#print axioms successorIsolation_only_openness

/-! ## (2) The bound against the conjecture -/

/-- The bound is local at `s₀`: some `B` bounds a lonely witness for every isolation-set point near `s₀`. -/
-- STANDING: DEFINITION
def LocalBound (v : ℝ → Fin 8 → ℝ) (k : Fin 8) (s₀ : ℝ) : Prop :=
  ∃ B : ℝ, ∀ᶠ s in 𝓝[Set.Icc 0 1] s₀, s ∈ isoSet v k → ∃ t : ℝ, 0 < t ∧ t ≤ B ∧ IsolatedAt (v s) k t

/-- **A uniform bound is a bound near each point** [L] (compactness of `[0,1]` only; no continuity of the path used).
[PROVISIONAL: covering] `IsCompact.induction_on` is a finite-subcover step; it supports only this equivalence. -/
theorem pathLonelyBound_iff_localBound (v : ℝ → Fin 8 → ℝ) (k : Fin 8) :
    PathLonelyBound v k ↔ ∀ s₀ ∈ Set.Icc (0 : ℝ) 1, LocalBound v k s₀ := by
  constructor
  · rintro ⟨B, hB⟩ s₀ _
    exact ⟨B, Filter.Eventually.of_forall fun s hs => hB s hs⟩
  · intro h
    have key : ∃ B : ℝ, ∀ s ∈ Set.Icc (0 : ℝ) 1, s ∈ isoSet v k →
        ∃ t : ℝ, 0 < t ∧ t ≤ B ∧ IsolatedAt (v s) k t := by
      refine isCompact_Icc.induction_on
        (p := fun S => ∃ B : ℝ, ∀ s ∈ S, s ∈ isoSet v k → ∃ t : ℝ, 0 < t ∧ t ≤ B ∧ IsolatedAt (v s) k t)
        ?_ ?_ ?_ ?_
      · exact ⟨0, fun s hs => absurd hs (Set.notMem_empty s)⟩
      · rintro S T hST ⟨B, hB⟩
        exact ⟨B, fun s hs => hB s (hST hs)⟩
      · rintro S T ⟨B₁, h₁⟩ ⟨B₂, h₂⟩
        refine ⟨max B₁ B₂, fun s hs hz => ?_⟩
        rcases hs with hs | hs
        · obtain ⟨t, h0, hle, hl⟩ := h₁ s hs hz
          exact ⟨t, h0, hle.trans (le_max_left _ _), hl⟩
        · obtain ⟨t, h0, hle, hl⟩ := h₂ s hs hz
          exact ⟨t, h0, hle.trans (le_max_right _ _), hl⟩
      · intro x hx
        obtain ⟨B, hB⟩ := h x hx
        exact ⟨_, hB, ⟨B, fun s hs => hs⟩⟩
    obtain ⟨B, hB⟩ := key
    exact ⟨B, fun s hs => hB s hs.1 hs⟩

#print axioms pathLonelyBound_iff_localBound

/-- **A lonely instant with every runner strictly clear gives a local bound** [L]: the instant `t₀` itself persists
(`openness_s`), so the bound is `t₀`. -/
theorem localBound_of_strict {v : ℝ → Fin 8 → ℝ} (hv : ContinuousOn v (Set.Icc 0 1)) {s₀ : ℝ}
    (hs₀ : s₀ ∈ Set.Icc (0 : ℝ) 1) {k : Fin 8} {t₀ : ℝ} (ht₀ : 0 < t₀)
    (h : ∀ i, i ≠ k → 1 / 8 < distInt ((v s₀ i - v s₀ k) * t₀)) : LocalBound v k s₀ := by
  obtain ⟨e, he, hm⟩ := (strict_iff_margin (fun i => distInt ((v s₀ i - v s₀ k) * t₀)) k).mpr h
  refine ⟨t₀, ?_⟩
  filter_upwards [openness_s hv hs₀ ht₀.le he hm] with s hs _
  exact ⟨t₀, ht₀, le_rfl, hs⟩

#print axioms localBound_of_strict

/-- **Where an escape can sit** [L]: if `s₀` has no local bound, every lonely instant of `v s₀` (there may be none) has a
runner at exactly `1/8`: it is a touch, with zero margin. -/
theorem not_localBound_imp_touch {v : ℝ → Fin 8 → ℝ} (hv : ContinuousOn v (Set.Icc 0 1)) {s₀ : ℝ}
    (hs₀ : s₀ ∈ Set.Icc (0 : ℝ) 1) {k : Fin 8} (hn : ¬ LocalBound v k s₀) :
    ∀ t : ℝ, 0 < t → IsolatedAt (v s₀) k t → ∃ i, i ≠ k ∧ distInt ((v s₀ i - v s₀ k) * t) = 1 / 8 := by
  intro t ht hl
  by_contra hno
  push Not at hno
  exact hn (localBound_of_strict hv hs₀ ht fun i hi => lt_of_le_of_ne (hl i hi) (Ne.symm (hno i hi)))

#print axioms not_localBound_imp_touch

/-- **The escaping sequence** [L]: with no local bound at `s₀` there are `s_n` in the isolation set, `s_n → s₀`, such
that every lonely instant at `s_n` is later than `n`.  No continuity is needed for this extraction. -/
theorem not_localBound_imp_seq {v : ℝ → Fin 8 → ℝ} {k : Fin 8} {s₀ : ℝ} (hn : ¬ LocalBound v k s₀) :
    ∃ s : ℕ → ℝ, (∀ n, s n ∈ isoSet v k) ∧ Tendsto s atTop (𝓝 s₀) ∧
      ∀ n : ℕ, ∀ t : ℝ, 0 < t → IsolatedAt (v (s n)) k t → (n : ℝ) < t := by
  have hfreq : ∀ B : ℝ, ∃ᶠ s in 𝓝[Set.Icc 0 1] s₀,
      s ∈ isoSet v k ∧ ∀ t : ℝ, 0 < t → t ≤ B → ¬ IsolatedAt (v s) k t := by
    intro B
    by_contra hcon
    apply hn
    refine ⟨B, ?_⟩
    have := Filter.not_frequently.mp hcon
    filter_upwards [this] with s hs hz
    by_contra hno
    push Not at hno
    exact hs ⟨hz, hno⟩
  have hball : ∀ n : ℕ, ∀ᶠ s in 𝓝[Set.Icc 0 1] s₀, |s - s₀| < 1 / ((n : ℝ) + 1) := by
    intro n
    have h1 : ∀ᶠ s in 𝓝 s₀, |s - s₀| < 1 / ((n : ℝ) + 1) := by
      have := Metric.ball_mem_nhds s₀ (show (0 : ℝ) < 1 / ((n : ℝ) + 1) by positivity)
      filter_upwards [this] with s hs
      simpa [Real.dist_eq] using hs
    exact nhdsWithin_le_nhds h1
  choose s hs using fun n : ℕ => ((hfreq n).and_eventually (hball n)).exists
  refine ⟨s, fun n => (hs n).1.1, ?_, fun n t ht hl => ?_⟩
  · rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero (fun n => dist_nonneg) (fun n => ?_) tendsto_one_div_add_atTop_nhds_zero_nat
    rw [Real.dist_eq]
    exact (hs n).2.le
  · by_contra hle
    push Not at hle
    exact (hs n).1.2 t ht hle hl

#print axioms not_localBound_imp_seq

/-! ## (3) The weakest local hypotheses -/

/-- Left-closedness: a limit from the left of isolation-set points lies in the isolation set. -/
-- STANDING: DEFINITION
def LeftClosed (v : ℝ → Fin 8 → ℝ) (k : Fin 8) : Prop :=
  ∀ s₀ ∈ Set.Icc (0 : ℝ) 1, ∀ s : ℕ → ℝ, (∀ n, s n ∈ isoSet v k) → (∀ n, s n < s₀) →
    Tendsto s atTop (𝓝 s₀) → s₀ ∈ isoSet v k

theorem leftClosed_of_closed {v : ℝ → Fin 8 → ℝ} {k : Fin 8} (hc : IsClosed (isoSet v k)) : LeftClosed v k :=
  fun _ _ _ hs _ ht => hc.mem_of_tendsto ht (Filter.Eventually.of_forall hs)

#print axioms leftClosed_of_closed

/-- **`isoSet = [0,1]` iff `0 ∈ isoSet`, `LeftClosed` and `RightIsolation`** [L].  Pure topology: no continuity of the
path and no bound is used.  Each hypothesis is necessary (forward direction), so this is the weakest local form of the
two owed statements: only limits from the left and persistence to the right. -/
theorem isoSet_eq_iff_leftClosed (v : ℝ → Fin 8 → ℝ) (k : Fin 8) :
    isoSet v k = Set.Icc 0 1 ↔ (0 : ℝ) ∈ isoSet v k ∧ LeftClosed v k ∧ RightIsolation v k := by
  constructor
  · intro h
    refine ⟨by rw [h]; exact ⟨le_rfl, zero_le_one⟩, fun s₀ hs₀ _ _ _ _ => by rw [h]; exact hs₀, ?_⟩
    intro s₀ hs₀ h1
    filter_upwards [Ioo_mem_nhdsGT h1] with s hs
    rw [h]
    exact ⟨hs₀.1.1.trans hs.1.le, hs.2.le⟩
  · rintro ⟨h0, hL, hR⟩
    refine Set.Subset.antisymm (isoSet_subset v k) ?_
    let S : Set ℝ := {x | x ∈ Set.Icc (0 : ℝ) 1 ∧ Set.Icc 0 x ⊆ isoSet v k}
    have hS0 : (0 : ℝ) ∈ S := by
      refine ⟨⟨le_rfl, zero_le_one⟩, fun y hy => ?_⟩
      have : y = 0 := le_antisymm hy.2 hy.1
      rw [this]; exact h0
    have hbdd : BddAbove S := ⟨1, fun x hx => hx.1.2⟩
    have hc0 : 0 ≤ sSup S := le_csSup hbdd hS0
    have hc1 : sSup S ≤ 1 := csSup_le ⟨0, hS0⟩ (fun x hx => hx.1.2)
    have hbelow : ∀ y, 0 ≤ y → y < sSup S → y ∈ isoSet v k := by
      intro y hy0 hyc
      obtain ⟨x, hx, hyx⟩ := exists_lt_of_lt_csSup ⟨0, hS0⟩ hyc
      exact hx.2 ⟨hy0, hyx.le⟩
    have hcZ : sSup S ∈ isoSet v k := by
      rcases eq_or_lt_of_le hc0 with h | h
      · rw [← h]; exact h0
      · set c := sSup S with hc
        have hpos : ∀ n : ℕ, 0 < c / (2 * ((n : ℝ) + 1)) := fun n => by positivity
        have hle : ∀ n : ℕ, c / (2 * ((n : ℝ) + 1)) ≤ c := fun n => by
          rw [div_le_iff₀ (by positivity)]
          have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
          nlinarith
        refine hL c ⟨hc0, hc1⟩ (fun n => c - c / (2 * ((n : ℝ) + 1))) (fun n => hbelow _ ?_ ?_)
          (fun n => ?_) ?_
        · linarith [hle n]
        · linarith [hpos n]
        · linarith [hpos n]
        · have e : (fun n : ℕ => c - c / (2 * ((n : ℝ) + 1))) = fun n : ℕ => c - (c / 2) * (1 / ((n : ℝ) + 1)) := by
            funext n; field_simp
          rw [e]
          have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (c / 2)
          simpa using (tendsto_const_nhds (x := c)).sub this
    have hle : ∀ y, 0 ≤ y → y ≤ sSup S → y ∈ isoSet v k := by
      intro y hy0 hyc
      rcases eq_or_lt_of_le hyc with h | h
      · rw [h]; exact hcZ
      · exact hbelow y hy0 h
    have hc1' : sSup S = 1 := by
      by_contra hne
      have hlt : sSup S < 1 := lt_of_le_of_ne hc1 hne
      obtain ⟨b, hb, hsub⟩ := (mem_nhdsGT_iff_exists_Ioo_subset).mp (hR _ hcZ hlt)
      have hb' : sSup S < b := hb
      set x := min ((sSup S + b) / 2) 1 with hx
      have hxc : sSup S < x := lt_min (by linarith) hlt
      have hxS : x ∈ S := by
        refine ⟨⟨by linarith, min_le_right _ _⟩, fun y hy => ?_⟩
        rcases le_or_gt y (sSup S) with h | h
        · exact hle y hy.1 h
        · exact hsub ⟨h, lt_of_le_of_lt hy.2 (lt_of_le_of_lt (min_le_left _ _) (by linarith))⟩
      exact absurd (le_csSup hbdd hxS) (not_le.mpr hxc)
    intro y hy
    exact hle y hy.1 (hc1' ▸ hy.2)

#print axioms isoSet_eq_iff_leftClosed

/-- The closed form of the same equivalence [L]. -/
theorem isoSet_eq_iff (v : ℝ → Fin 8 → ℝ) (k : Fin 8) :
    isoSet v k = Set.Icc 0 1 ↔ (0 : ℝ) ∈ isoSet v k ∧ IsClosed (isoSet v k) ∧ RightIsolation v k := by
  constructor
  · intro h
    obtain ⟨h0, -, hR⟩ := (isoSet_eq_iff_leftClosed v k).mp h
    exact ⟨h0, by rw [h]; exact isClosed_Icc, hR⟩
  · rintro ⟨h0, hc, hR⟩
    exact (isoSet_eq_iff_leftClosed v k).mpr ⟨h0, leftClosed_of_closed hc, hR⟩

#print axioms isoSet_eq_iff

/-! ## Escape, and the bound as a sufficient condition -/

/-- An escape point: `s₀` is a limit of isolation-set points but is not itself in the isolation set. -/
-- STANDING: DEFINITION
def EscapeAt (v : ℝ → Fin 8 → ℝ) (k : Fin 8) (s₀ : ℝ) : Prop :=
  s₀ ∉ isoSet v k ∧ ∃ s : ℕ → ℝ, (∀ n, s n ∈ isoSet v k) ∧ Tendsto s atTop (𝓝 s₀)

/-- Closedness of the isolation set is the absence of an escape point [L]. -/
theorem isClosed_iff_no_escape (v : ℝ → Fin 8 → ℝ) (k : Fin 8) :
    IsClosed (isoSet v k) ↔ ∀ s₀, ¬ EscapeAt v k s₀ := by
  rw [← isSeqClosed_iff_isClosed]
  constructor
  · rintro hc s₀ ⟨hn, s, hs, ht⟩
    exact hn (hc hs ht)
  · intro h x p hx hxp
    by_contra hn
    exact h p ⟨hn, x, hx, hxp⟩

#print axioms isClosed_iff_no_escape

/-- **At an escape point every witness sequence tends to infinity** [L] (`isoSet_dichotomy`). -/
theorem escape_witnesses_diverge {v : ℝ → Fin 8 → ℝ} (hv : ContinuousOn v (Set.Icc 0 1)) {k : Fin 8}
    {s t : ℕ → ℝ} {s₀ : ℝ} (hs : ∀ n, s n ∈ Set.Icc (0 : ℝ) 1) (hst : Tendsto s atTop (𝓝 s₀))
    (hesc : s₀ ∉ isoSet v k) (hl : ∀ n, IsolatedAt (v (s n)) k (t n)) (hpos : ∀ n, 0 < t n) :
    Tendsto t atTop atTop :=
  (isoSet_dichotomy hv hs hst hl hpos).resolve_right hesc

#print axioms escape_witnesses_diverge

/-- The uniform bound is sufficient for left-closedness [L] (`isClosed_isoSet_of_bound`).  Whether it is NECESSARY
(closed does not obviously give a bound) is not settled here. -/
theorem pathLonelyBound_imp_leftClosed {v : ℝ → Fin 8 → ℝ} (hv : ContinuousOn v (Set.Icc 0 1)) {k : Fin 8}
    (hB : PathLonelyBound v k) : LeftClosed v k :=
  leftClosed_of_closed (isClosed_isoSet_of_bound hv hB)

#print axioms pathLonelyBound_imp_leftClosed

/-! ## The grid start and the exact classification -/

/-- A grid arrangement is isolated for every subject (`gridGlobalIsolation` at `a = 1`) [L]. -/
theorem isolation_of_isGrid {w : Fin 8 → ℝ} (hw : IsGrid w) (k : Fin 8) : Isolation w k := by
  obtain ⟨d, v₀, idx, hd, hidx, hv⟩ := hw
  have h := gridGlobalIsolation w d v₀ idx hd hidx hv 1 isCoprime_one_left
  exact ⟨((1 : ℤ) : ℝ) / (8 * d), by push_cast; positivity, h k⟩

#print axioms isolation_of_isGrid

/-- **The conjecture is equivalent to `LeftClosed ∧ RightIsolation` along admissible grid-start paths** [L].  This
classifies the pair (closedness, persistence to the right): together they are `LonelyRunnerEight`, as stage 1 showed for
the path form.  Neither is offered as the argument. -/
theorem lre_iff_leftClosed_right :
    LonelyRunnerEight ↔
      ∀ v : ℝ → Fin 8 → ℝ, AdmissiblePath v → IsGrid (v 0) → ∀ k, LeftClosed v k ∧ RightIsolation v k := by
  constructor
  · intro h v hv _ k
    have hiff := (isoSet_eq_iff_leftClosed v k).mp (lre_isoSet_eq h hv.2 k)
    exact ⟨hiff.2.1, hiff.2.2⟩
  · intro h
    refine displacementPath_imp_lonelyRunnerEight ?_
    intro γ hγ harr hgrid s hs k
    have hadm : AdmissiblePath γ := ⟨hγ, harr⟩
    have h0 : (0 : ℝ) ∈ isoSet γ k :=
      ⟨⟨le_rfl, zero_le_one⟩, isolation_of_isGrid hgrid k⟩
    obtain ⟨hL, hR⟩ := h γ hadm hgrid k
    have := (isoSet_eq_iff_leftClosed γ k).mpr ⟨h0, hL, hR⟩
    have hs' : s ∈ isoSet γ k := by rw [this]; exact hs
    exact hs'.2

#print axioms lre_iff_leftClosed_right

/-- The two owed statements together (the bound on every admissible grid-start path, and `SuccessorIsolation`) imply the
conjecture [L].  Recorded as the sufficiency of the pair; the bound is cap-shaped (rule 7) and is NOT offered as the
existence argument.  Whether the conjecture implies the bound is the open point. -/
theorem owed_pair_imp_lre
    (hB : ∀ v : ℝ → Fin 8 → ℝ, AdmissiblePath v → IsGrid (v 0) → ∀ k, PathLonelyBound v k)
    (hS : ∀ v : ℝ → Fin 8 → ℝ, AdmissiblePath v → IsGrid (v 0) → ∀ k, SuccessorIsolation v k) :
    LonelyRunnerEight :=
  lre_iff_leftClosed_right.mpr fun v hv hg k =>
    ⟨pathLonelyBound_imp_leftClosed hv.1 (hB v hv hg k), successorIsolation_imp_right (hS v hv hg k)⟩

#print axioms owed_pair_imp_lre

/-- OWED: the conjecture implies the uniform bound along every admissible grid-start path.  Equivalent (by
`pathLonelyBound_iff_localBound`) to a local bound at every point; by `not_localBound_imp_touch` a counterexample would
need a point all of whose lonely instants are zero-margin touches.  Asserted nowhere. -/
-- STANDING: OWED
def ConjectureGivesBound : Prop :=
  LonelyRunnerEight → ∀ v : ℝ → Fin 8 → ℝ, AdmissiblePath v → IsGrid (v 0) → ∀ k, PathLonelyBound v k

/-! ## (4) The margin-positive form is refuted at the AP (Dirichlet) -/

/-- The AP `(1, 2, …, 8)`. -/
def apv : Fin 8 → ℝ := fun j => ((j : ℕ) : ℝ) + 1

theorem apv_isArrangement : IsArrangement apv := by
  refine ⟨fun j => by simp only [apv]; positivity, ?_⟩
  intro i j hij
  apply Fin.ext
  have : ((i : ℕ) : ℝ) = ((j : ℕ) : ℝ) := by simpa [apv] using hij
  exact_mod_cast this

#print axioms apv_isArrangement

theorem apv_isGrid : IsGrid apv := by
  refine ⟨1, 1, fun j => ((j : ℕ) : ℤ), one_pos, ?_, ?_⟩
  · intro j j' h
    have hj := j.isLt
    have hj' := j'.isLt
    simp only at h
    apply Fin.ext
    omega
  · intro j
    simp [apv]
    ring

#print axioms apv_isGrid

/-- **Dirichlet at the AP** [L]: for EVERY real `t` some runner `i ≠ 0` has `distInt ((i+1 - 1) t) ≤ 1/8`.  So no
instant has all other runners strictly clear: every lonely instant of the AP is a zero-margin touch.  The reason is
Dirichlet's approximation theorem with `n = 7` (`Real.exists_int_int_abs_mul_sub_le`), the pigeonhole on eight points of
the circle.  [PROVISIONAL: counting tool] the pigeonhole is used here and supports only this statement. -/
theorem ap_not_strict (t : ℝ) : ∃ i : Fin 8, i ≠ 0 ∧ distInt ((apv i - apv 0) * t) ≤ 1 / 8 := by
  obtain ⟨j, k, hk0, hk7, hjk⟩ := Real.exists_int_int_abs_mul_sub_le t (n := 7) (by norm_num)
  have hkn : ((k.toNat : ℕ) : ℝ) = (k : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hk0.le
  refine ⟨⟨k.toNat, by omega⟩, ?_, ?_⟩
  · intro h
    have := congrArg Fin.val h
    simp only [Fin.val_zero] at this
    omega
  · have e : (apv ⟨k.toNat, by omega⟩ - apv 0) = (k : ℝ) := by
      simp only [apv, Fin.val_zero]
      rw [hkn]; push_cast; ring
    rw [e]
    have h1 := Localisation.distInt_le ((k : ℝ) * t) j
    have h2 : (1 : ℝ) / (((7 : ℕ) : ℝ) + 1) = 1 / 8 := by norm_num
    rw [h2] at hjk
    linarith

#print axioms ap_not_strict

/-- The margin-positive local statement: along every admissible grid-start path, at every parameter there is an instant
at which every other runner is STRICTLY clear.  Candidate shape of an argument; refuted below. -/
-- STANDING: DEFINITION
def StrictLocalForm : Prop :=
  ∀ v : ℝ → Fin 8 → ℝ, AdmissiblePath v → IsGrid (v 0) → ∀ k, ∀ s ∈ Set.Icc (0 : ℝ) 1,
    ∃ t : ℝ, 0 < t ∧ ∀ i, i ≠ k → 1 / 8 < distInt ((v s i - v s k) * t)

/-- **`StrictLocalForm` is false** [L]: the constant path at the AP is admissible, starts at a grid, and has no strictly
clear instant (`ap_not_strict`).  Why: the AP has gap exactly `1/8`, so the isolation there is a touch; a margin-positive
statement asks for slack the AP does not have (rule 7, "any bound with slack the AP does not have").  The cascade is
unaffected: the constant path has `isoSet = [0,1]` (`isolation_of_isGrid`). -/
theorem strictForm_refuted : ¬ StrictLocalForm := by
  intro h
  obtain ⟨t, -, ht⟩ := h (fun _ => apv) ⟨continuousOn_const, fun _ _ => apv_isArrangement⟩ apv_isGrid 0 0
    ⟨le_rfl, zero_le_one⟩
  obtain ⟨i, hi, hle⟩ := ap_not_strict t
  linarith [ht i hi]

#print axioms strictForm_refuted

/-- At the AP the isolation set of the constant path is all of `[0,1]`, with every lonely instant a touch [L]. -/
theorem ap_const_path_isoSet (k : Fin 8) : isoSet (fun _ => apv) k = Set.Icc 0 1 := by
  ext s
  exact ⟨fun h => h.1, fun hs => ⟨hs, isolation_of_isGrid apv_isGrid k⟩⟩

#print axioms ap_const_path_isoSet

end PathClassify

end Fresh
