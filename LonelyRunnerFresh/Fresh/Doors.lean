import Mathlib
import Fresh.Framework
import Fresh.Cascade
import Fresh.Localisation
import Fresh.WhereProofs
import Fresh.ChainLaws

/-!
# The doors (Task N; v9 section 6, Theorems 11, 12, 13)

Imports `Mathlib`, `Fresh.Framework`, `Fresh.Cascade`, `Fresh.Localisation`, `Fresh.WhereProofs`,
`Fresh.ChainLaws`; nothing from the existing `LonelyRunner` repo.  Every statement is about an arrangement `v`, a
subject `k`, `m = d_min` (`IsDmin`), `ds = disparitySet v k` (all positive, `Cascade.disparitySet_pos`) and the
unique cascade sequence `Cascade.cascadeSeq ds (1/(8m))` (any sequence of moves from the bound equals it,
`Cascade.seq_eq_cascadeSeq`).  Exact reals only; no runner is stationary; no cap, move bound or budget is stated.

Contents.
* (1) Theorem 11(d): `landing_is_opening`, `landing_runner` -- the landing is lonely, is the least positive lonely
  instant, and some runner stands there at exactly `j + 1/8`: the setter of the last forward move, or `d_min` itself
  when there was no forward move.
* (2) Theorem 11(b),(c): `instant_is_opening` (EVERY instant of the cascade, the start included, is an opening
  `(j + 1/8)/d` of some `d ∈ ds`, `j : ℕ`), `forward_or_fixed`, `fixed_stays`, `strictMonoOn_before_fix`
  (strictly increasing until fixed, constant after), and `zone_run` (each forward move starts inside the zone of its
  setter, ends at that zone's right end, and the next setter's zone contains that end; consecutive setters differ).
* (3) Theorem 13: `doors_agree` -- (A) isolation, (B) the cascade fixes, (C) its instants are bounded above,
  (D) some flank has an isolated opening, (E) every runner is in the way at only finitely many instants: all
  equivalent.
* (4) `global_door_iff`, `doorBounded_global_iff`, `doorFinite_global_iff`: each door, quantified over all
  arrangements, is exactly `LonelyRunnerEight`.

Provenance (existing declarations read for the argument, not imported; no proof copied, every proof written here):
* `landing_is_opening`, `landing_runner`: `LRC/Spec/Doors.lean` (the landing/first-isolation half of the doors) and
  `MomentIterationN.lonely_of_fixed`; the "runner at exactly 1/8" clause has its argument here in
  `instant_is_opening` (the setter reading `Dilation.setter_reading`).
* `instant_is_opening`: the inductive step of `MomentIterationN.iterate_mem_openings`, strengthened: no lonely
  instant above is assumed, the membership is in the openings of `ds` with no upper lap limit.
* `doors_agree`: `LRC.Spec.doors_agree` (`Spec/Doors.lean`, `Spec/DoorsN.lean`).  The bounded door and the finite door
  there are stated for the existing `MomentIterationN` iteration; here for `Cascade.cascadeSeq`.

Counting steps.  Two steps use a counting tool; each is tagged at the step: (C) → (B) (a strictly increasing
sequence cannot stay in a finite set of openings below a bound) and (E) → (B) (a finite union of finite sets of
indices cannot be all of `ℕ`).  (A) ↔ (B) uses `Cascade.exists_fixed_of_lonely`, tagged there.  Nothing else counts.

(4) [L] and [reasoned].  Every door is equivalent to `Isolation v k` (`doors_agree`), and each door quantified over
all arrangements is equivalent to `LonelyRunnerEight` (`global_door_iff` and its two instances, plus
`Cascade.cascadeForm_iff` for (B) and `Localisation.candidateScaleForm_iff` for (D)).  So every door is a
RESTATEMENT of the conjecture at that arrangement; none is a step toward it.  [reasoned] A door can still be useful as
a coordinate in which to read the displacement (the cascade shows WHERE the isolation is, `landing_runner`), but
proving any door for all arrangements is proving the conjecture.  No equivalence failed: a tie of setters (two runners
sharing the largest next opening) does not break any door, because every door speaks of the instants, which are
unique (`Cascade.isMove_unique`), never of which runner is named setter; at a tie BOTH runners stand at exactly `1/8`
at the landing (each satisfies `IsSetterAt`, and `ChainLaws.setters_same_step_distinct_lap` puts them on different
laps), so `landing_runner` holds for either choice.
-/

open Classical

namespace Fresh

namespace Doors

open Cascade ChainLaws Dilation

/-! ## Preliminaries -/

/-- The bound is itself an opening of `d_min`: `m · 1/(8m) = 0 + 1/8`. -/
theorem bound_reading {m : ℝ} (hm : 0 < m) : m * (1 / (8 * m)) = ((0 : ℕ) : ℝ) + 1 / 8 := by
  field_simp
  push_cast
  ring

#print axioms bound_reading

/-- `CascadeFixes` read on the unique cascade sequence. -/
theorem cascadeFixes_iff_seq {ds : Finset ℝ} {t₀ : ℝ} :
    CascadeFixes ds t₀ ↔ ∃ N, cascadeSeq ds t₀ (N + 1) = cascadeSeq ds t₀ N := by
  constructor
  · rintro ⟨seq, h0, hmv, N, hN⟩
    have h := seq_eq_cascadeSeq hmv
    refine ⟨N, ?_⟩
    rw [← h0, ← h (N + 1), ← h N]
    exact hN
  · rintro ⟨N, hN⟩
    exact ⟨cascadeSeq ds t₀, rfl, cascadeSeq_isMove ds t₀, N, hN⟩

#print axioms cascadeFixes_iff_seq

/-! ## (2) The run: every instant is an opening; strictly increasing until fixed -/

/-- **Every instant of the cascade from the bound is an opening**: `d · seq n = j + 1/8` for some `d ∈ ds`, `j : ℕ`.
At `n = 0` it is `d_min` at lap `0`; after a forward move it is the setter of that move (it lands at exactly `1/8`
past its lap, `Dilation.setter_reading`); after a fixing step it is whatever held before. -/
theorem instant_is_opening {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d) {m : ℝ} (hm : m ∈ ds) {seq : ℕ → ℝ}
    (h0 : seq 0 = 1 / (8 * m)) (hmv : ∀ n, IsMove ds (seq n) (seq (n + 1))) :
    ∀ n, ∃ d ∈ ds, ∃ j : ℕ, d * seq n = (j : ℝ) + 1 / 8 := by
  have hm0 := hpos m hm
  have hs0 : 0 < seq 0 := by rw [h0]; positivity
  intro n
  induction n with
  | zero => exact ⟨m, hm, 0, by rw [h0]; exact bound_reading hm0⟩
  | succ n ih =>
    rcases hmv n with ⟨_, he⟩ | ⟨x, hx, hw, he, _⟩
    · rw [he]; exact ih
    · have hl := setter_lap_nonneg hpos hs0 hmv (n := n) (x := x) ⟨hx, hw, he⟩
      refine ⟨x, hx, (lap x (seq n)).toNat, ?_⟩
      rw [he, setter_reading (hpos x hx) hw]
      have : (((lap x (seq n)).toNat : ℕ) : ℝ) = ((lap x (seq n) : ℤ) : ℝ) := by
        exact_mod_cast Int.toNat_of_nonneg hl
      rw [this]

#print axioms instant_is_opening

/-- The same, in the division form `seq n = (j + 1/8)/d`. -/
theorem instant_is_opening_div {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d) {m : ℝ} (hm : m ∈ ds) {seq : ℕ → ℝ}
    (h0 : seq 0 = 1 / (8 * m)) (hmv : ∀ n, IsMove ds (seq n) (seq (n + 1))) :
    ∀ n, ∃ d ∈ ds, ∃ j : ℕ, seq n = ((j : ℝ) + 1 / 8) / d := by
  intro n
  obtain ⟨d, hd, j, hj⟩ := instant_is_opening hpos hm h0 hmv n
  refine ⟨d, hd, j, ?_⟩
  rw [eq_div_iff (hpos d hd).ne', ← hj]
  ring

#print axioms instant_is_opening_div

/-- Each step either fixes or goes strictly forward. -/
theorem forward_or_fixed {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d) {seq : ℕ → ℝ}
    (hmv : ∀ n, IsMove ds (seq n) (seq (n + 1))) (n : ℕ) : seq (n + 1) = seq n ∨ seq n < seq (n + 1) := by
  by_cases h : seq (n + 1) = seq n
  · exact Or.inl h
  · exact Or.inr (lt_of_isMove_of_ne hpos (hmv n) h)

#print axioms forward_or_fixed

/-- **A fixed step is absorbing**: once `seq (N+1) = seq N`, the sequence is constant from `N` on. -/
theorem fixed_stays {ds : Finset ℝ} {seq : ℕ → ℝ} (hmv : ∀ n, IsMove ds (seq n) (seq (n + 1))) {N : ℕ}
    (hN : seq (N + 1) = seq N) : ∀ n, N ≤ n → seq n = seq N := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => rfl
  | succ n _ ih =>
    have h1 := hmv n
    have h2 := hmv N
    rw [hN] at h2
    rw [ih] at h1
    exact isMove_unique h1 h2

#print axioms fixed_stays

/-- **Strictly increasing until fixed**: if no step before `N` fixes, the instants `seq 0 < … < seq N`. -/
theorem strictMonoOn_before_fix {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d) {seq : ℕ → ℝ}
    (hmv : ∀ n, IsMove ds (seq n) (seq (n + 1))) {N : ℕ} (hne : ∀ n < N, seq (n + 1) ≠ seq n) :
    StrictMonoOn seq (Set.Iic N) := by
  intro a _ b hb hab
  have hb' : b ≤ N := hb
  clear hb
  induction b, hab using Nat.le_induction with
  | base => exact lt_of_isMove_of_ne hpos (hmv a) (hne a (by omega))
  | succ b hab ih =>
    exact lt_trans (ih (by omega)) (lt_of_isMove_of_ne hpos (hmv b) (hne b (by omega)))

#print axioms strictMonoOn_before_fix

/-- **The zone run (Theorem 11(b),(c))**.  A forward move at `n` with setter `x`: the start `seq n` lies in the zone
of `x` on its lap `j` (`|x · seq n − j| < 1/8`), the move ends at that zone's right end (`x · seq (n+1) = j + 1/8`,
strictly after `seq n`), and every setter `y` of the next move is a different runner whose zone (on its own lap)
contains that end.  The last clause is the record's "each zone contains the end of the one before"; given the
definition of a setter it is the in-the-way condition at `seq (n+1)`. -/
theorem zone_run {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d) {seq : ℕ → ℝ} {n : ℕ} {x : ℝ}
    (hx : IsSetterAt ds seq n x) :
    seq n < seq (n + 1) ∧ |x * seq n - (lap x (seq n) : ℝ)| < 1 / 8 ∧
      x * seq (n + 1) = (lap x (seq n) : ℝ) + 1 / 8 ∧
      ∀ y, IsSetterAt ds seq (n + 1) y → y ≠ x ∧ |y * seq (n + 1) - (lap y (seq (n + 1)) : ℝ)| < 1 / 8 := by
  obtain ⟨hxds, hxw, hxs⟩ := hx
  have hx0 := hpos x hxds
  refine ⟨?_, abs_sub_lap_lt hxw, ?_, fun y hy => ⟨?_, abs_sub_lap_lt hy.2.1⟩⟩
  · rw [hxs]; exact lt_nextOpening hx0 hxw
  · rw [hxs]; exact setter_reading hx0 hxw
  · rintro rfl
    exact setter_not_twice_in_row hpos ⟨hxds, hxw, hxs⟩ hy

#print axioms zone_run

/-- Every instant is the start, or the landing of the last forward move before it. -/
theorem last_forward {ds : Finset ℝ} {seq : ℕ → ℝ} (hmv : ∀ n, IsMove ds (seq n) (seq (n + 1))) :
    ∀ N, seq N = seq 0 ∨ ∃ n < N, ∃ x, IsSetterAt ds seq n x ∧ seq (n + 1) = seq N := by
  intro N
  induction N with
  | zero => exact Or.inl rfl
  | succ N ih =>
    rcases hmv N with ⟨_, he⟩ | ⟨x, hx, hw, he, _⟩
    · rw [he]
      rcases ih with h | ⟨n, hn, x, hx, hxe⟩
      · exact Or.inl h
      · exact Or.inr ⟨n, by omega, x, hx, hxe⟩
    · exact Or.inr ⟨N, by omega, x, ⟨hx, hw, he⟩, rfl⟩

#print axioms last_forward

/-! ## (1) Theorem 11(d): the landing is an opening -/

/-- At a fixed step `N` of the cascade from the bound, `seq N` is the least positive isolated instant
(via `WhereProofs.landingIsFirstIsolation`). -/
theorem landing_isLeast {v : Fin 8 → ℝ} (hv : IsArrangement v) {k : Fin 8} {m : ℝ} (hm : IsDmin v k m) {N : ℕ}
    (hN : cascadeSeq (disparitySet v k) (1 / (8 * m)) (N + 1) = cascadeSeq (disparitySet v k) (1 / (8 * m)) N) :
    IsLeast {t : ℝ | 0 < t ∧ IsolatedAt v k t} (cascadeSeq (disparitySet v k) (1 / (8 * m)) N) := by
  have hmv := cascadeSeq_isMove (disparitySet v k) (1 / (8 * m))
  have hfix := hmv N
  rw [hN] at hfix
  exact WhereProofs.landingIsFirstIsolation v hv k m hm _
    ⟨cascadeSeq (disparitySet v k) (1 / (8 * m)), N, rfl, fun n _ => hmv n, rfl, hfix⟩

#print axioms landing_isLeast

/-- **The landing runner (Theorem 11(d), precise form)**.  At any fixed step `N` of the cascade from the bound, the
landing `t* = seq N` is either the bound itself, where `d_min · t* = 1/8`, or the landing of the last forward move
`n < N`, whose setter `x` stands at `x · t* = j + 1/8` with `j = lap x (seq n) ≥ 0`. -/
theorem landing_runner {v : Fin 8 → ℝ} (hv : IsArrangement v) {k : Fin 8} {m : ℝ} (hm : IsDmin v k m) (N : ℕ) :
    (cascadeSeq (disparitySet v k) (1 / (8 * m)) N = 1 / (8 * m) ∧
        m * cascadeSeq (disparitySet v k) (1 / (8 * m)) N = 1 / 8) ∨
      ∃ n < N, ∃ x, IsSetterAt (disparitySet v k) (cascadeSeq (disparitySet v k) (1 / (8 * m))) n x ∧
        cascadeSeq (disparitySet v k) (1 / (8 * m)) (n + 1) = cascadeSeq (disparitySet v k) (1 / (8 * m)) N ∧
        0 ≤ lap x (cascadeSeq (disparitySet v k) (1 / (8 * m)) n) ∧
        x * cascadeSeq (disparitySet v k) (1 / (8 * m)) N =
          (lap x (cascadeSeq (disparitySet v k) (1 / (8 * m)) n) : ℝ) + 1 / 8 := by
  have hpos := disparitySet_pos hv k
  have hm0 : 0 < m := hpos m hm.1
  have hmv := cascadeSeq_isMove (disparitySet v k) (1 / (8 * m))
  have hs0 : 0 < cascadeSeq (disparitySet v k) (1 / (8 * m)) 0 := by
    rw [cascadeSeq_zero]; positivity
  rcases last_forward hmv N with h | ⟨n, hn, x, hx, hxe⟩
  · left
    rw [cascadeSeq_zero] at h
    refine ⟨h, ?_⟩
    rw [h, bound_reading hm0]; push_cast; ring
  · right
    refine ⟨n, hn, x, hx, hxe, setter_lap_nonneg hpos hs0 hmv hx, ?_⟩
    rw [← hxe, hx.2.2]
    exact setter_reading (hpos x hx.1) hx.2.1

#print axioms landing_runner

/-- **`landing_is_opening` (Theorem 11(d))**.  If the cascade from `1/(8 d_min)` fixes, then at its fixed step `N` the
landing `t* = seq N` is the least positive isolated instant, and some disparity stands there at exactly `j + 1/8`
(`landing_runner` says which: the last setter, or `d_min` when there was no forward move). -/
theorem landing_is_opening {v : Fin 8 → ℝ} (hv : IsArrangement v) {k : Fin 8} {m : ℝ} (hm : IsDmin v k m)
    (hfix : CascadeFixes (disparitySet v k) (1 / (8 * m))) :
    ∃ N, cascadeSeq (disparitySet v k) (1 / (8 * m)) (N + 1) = cascadeSeq (disparitySet v k) (1 / (8 * m)) N ∧
      IsLeast {t : ℝ | 0 < t ∧ IsolatedAt v k t} (cascadeSeq (disparitySet v k) (1 / (8 * m)) N) ∧
      ∃ d ∈ disparitySet v k, ∃ j : ℕ, d * cascadeSeq (disparitySet v k) (1 / (8 * m)) N = (j : ℝ) + 1 / 8 := by
  obtain ⟨N, hN⟩ := cascadeFixes_iff_seq.mp hfix
  exact ⟨N, hN, landing_isLeast hv hm hN,
    instant_is_opening (disparitySet_pos hv k) hm.1 rfl (cascadeSeq_isMove _ _) N⟩

#print axioms landing_is_opening

/-! ## (3) Theorem 13: the doors -/

/-- (B) → (C): a fixed sequence is bounded by its landing (monotone up to `N`, constant after). -/
theorem bddAbove_of_fixed {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d) {t₀ : ℝ} {N : ℕ}
    (hN : cascadeSeq ds t₀ (N + 1) = cascadeSeq ds t₀ N) : BddAbove (Set.range (cascadeSeq ds t₀)) := by
  have hmv := cascadeSeq_isMove ds t₀
  refine ⟨cascadeSeq ds t₀ N, ?_⟩
  rintro _ ⟨n, rfl⟩
  rcases le_total n N with h | h
  · exact seq_mono hpos hmv h
  · exact (fixed_stays hmv hN n h).le

#print axioms bddAbove_of_fixed

/-- (C) → (B): a bounded cascade from the bound fixes.  Every instant is an opening `(j + 1/8)/d` (`instant_is_opening`)
lying below the bound `M`, so in the finite set `openingsUpTo ds M`; a run that never fixes is strictly increasing. -/
theorem fixed_of_bddAbove {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d) {m : ℝ} (hm : m ∈ ds)
    (hb : BddAbove (Set.range (cascadeSeq ds (1 / (8 * m))))) :
    ∃ N, cascadeSeq ds (1 / (8 * m)) (N + 1) = cascadeSeq ds (1 / (8 * m)) N := by
  set seq := cascadeSeq ds (1 / (8 * m)) with hseq
  have hmv : ∀ n, IsMove ds (seq n) (seq (n + 1)) := cascadeSeq_isMove ds _
  obtain ⟨M, hM⟩ := hb
  have hle : ∀ n, seq n ≤ M := fun n => hM ⟨n, rfl⟩
  have hmem : ∀ n, seq n ∈ openingsUpTo ds M := by
    intro n
    obtain ⟨d, hd, j, hj⟩ := instant_is_opening hpos hm rfl hmv n
    have hd0 := hpos d hd
    have hjM : (j : ℝ) ≤ d * M := by
      have : d * seq n ≤ d * M := mul_le_mul_of_nonneg_left (hle n) hd0.le
      linarith
    have hjc : (j : ℤ) ≤ ⌈d * M⌉ := by
      have := Int.le_ceil (d * M)
      exact_mod_cast le_trans hjM this
    refine Finset.mem_biUnion.mpr ⟨d, hd, Finset.mem_image.mpr ⟨(j : ℤ), Finset.mem_Icc.mpr ⟨by positivity, hjc⟩, ?_⟩⟩
    rw [Int.cast_natCast, ← hj]
    field_simp
  by_contra hne
  push Not at hne
  have hsm : StrictMono seq :=
    strictMono_nat_of_lt_succ (fun n => lt_of_isMove_of_ne hpos (hmv n) (hne n))
  -- [PROVISIONAL: counting tool] supporting "a cascade whose instants are bounded fixes" (door C → door B):
  -- an injective map from `ℕ` into the finite set of openings below the bound is impossible.
  have hinf : (↑(openingsUpTo ds M) : Set ℝ).Infinite :=
    Set.infinite_of_injective_forall_mem hsm.injective (fun n => Finset.mem_coe.mpr (hmem n))
  exact hinf (Finset.finite_toSet _)

#print axioms fixed_of_bddAbove

/-- (B) → (E): after the fixed step nobody is in the way (the landing is lonely), so each runner is in the way only
at indices below `N`. -/
theorem finite_inWay_of_fixed {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d) {t₀ : ℝ} {N : ℕ}
    (hN : cascadeSeq ds t₀ (N + 1) = cascadeSeq ds t₀ N) :
    ∀ d ∈ ds, {n : ℕ | InWay d (cascadeSeq ds t₀ n)}.Finite := by
  have hmv := cascadeSeq_isMove ds t₀
  have hfix := hmv N
  rw [hN] at hfix
  have hl := (isMove_self_iff hpos).mp hfix
  intro d hd
  refine (Set.finite_Iio N).subset ?_
  intro n hn
  by_contra hc
  have hNn : N ≤ n := by simpa using hc
  have hw : InWay d (cascadeSeq ds t₀ n) := hn
  rw [fixed_stays hmv hN n hNn] at hw
  exact not_inWay_iff.mpr (hl d hd) hw

#print axioms finite_inWay_of_fixed

/-- (E) → (B): if every runner is in the way only finitely often, the cascade fixes.  A step that does not fix has a
runner in the way (its setter). -/
theorem fixed_of_finite_inWay {ds : Finset ℝ} {t₀ : ℝ}
    (hE : ∀ d ∈ ds, {n : ℕ | InWay d (cascadeSeq ds t₀ n)}.Finite) :
    ∃ N, cascadeSeq ds t₀ (N + 1) = cascadeSeq ds t₀ N := by
  have hmv := cascadeSeq_isMove ds t₀
  by_contra hne
  push Not at hne
  have hsub : (Set.univ : Set ℕ) ⊆ ⋃ d ∈ (↑ds : Set ℝ), {n : ℕ | InWay d (cascadeSeq ds t₀ n)} := by
    intro n _
    rcases hmv n with ⟨_, he⟩ | ⟨x, hx, hw, _, _⟩
    · exact absurd he (hne n)
    · exact Set.mem_biUnion (Finset.mem_coe.mpr hx) hw
  -- [PROVISIONAL: counting tool] supporting "if every runner is in the way finitely often the cascade fixes"
  -- (door E → door B): a finite union (over the finite set `ds`) of finite sets of indices is not all of `ℕ`.
  have hfin : (⋃ d ∈ (↑ds : Set ℝ), {n : ℕ | InWay d (cascadeSeq ds t₀ n)}).Finite :=
    ds.finite_toSet.biUnion (fun d hd => hE d (Finset.mem_coe.mp hd))
  exact Set.infinite_univ (hfin.subset hsub)

#print axioms fixed_of_finite_inWay

/-- **`doors_agree` (Theorem 13)**.  For an arrangement `v`, subject `k`, `m = d_min`, `ds = disparitySet v k` and the
cascade sequence `s = cascadeSeq ds (1/(8m))`, the five doors are equivalent:
(A) `Isolation v k`; (B) `CascadeFixes ds (1/(8m))`; (C) `s` is bounded above;
(D) some flank `e ∈ ds` has an isolated opening `(n + 1/8)/e`; (E) each `d ∈ ds` is in the way at finitely many `s n`.
Stated as (A) ↔ (B), (B) ↔ (C), (A) ↔ (D), (B) ↔ (E). -/
theorem doors_agree {v : Fin 8 → ℝ} (hv : IsArrangement v) {k : Fin 8} {m : ℝ} (hm : IsDmin v k m) :
    (Isolation v k ↔ CascadeFixes (disparitySet v k) (1 / (8 * m))) ∧
    (CascadeFixes (disparitySet v k) (1 / (8 * m)) ↔
      BddAbove (Set.range (cascadeSeq (disparitySet v k) (1 / (8 * m))))) ∧
    (Isolation v k ↔ ∃ e ∈ disparitySet v k, ∃ n : ℕ, IsolatedAt v k (((n : ℝ) + 1 / 8) / e)) ∧
    (CascadeFixes (disparitySet v k) (1 / (8 * m)) ↔
      ∀ d ∈ disparitySet v k, {n : ℕ | InWay d (cascadeSeq (disparitySet v k) (1 / (8 * m)) n)}.Finite) := by
  have hpos := disparitySet_pos hv k
  refine ⟨cascadeFixes_iff_isolation hv hm, ⟨fun h => ?_, fun h => ?_⟩, Localisation.localisation hv k,
    ⟨fun h => ?_, fun h => ?_⟩⟩
  · obtain ⟨N, hN⟩ := cascadeFixes_iff_seq.mp h
    exact bddAbove_of_fixed hpos hN
  · exact cascadeFixes_iff_seq.mpr (fixed_of_bddAbove hpos hm.1 h)
  · obtain ⟨N, hN⟩ := cascadeFixes_iff_seq.mp h
    exact finite_inWay_of_fixed hpos hN
  · exact cascadeFixes_iff_seq.mpr (fixed_of_finite_inWay h)

#print axioms doors_agree

/-! ## (4) Every door is a restatement of the conjecture -/

/-- Any per-arrangement door equivalent to `Isolation v k`, quantified over all arrangements, subjects and `d_min`, is
exactly `LonelyRunnerEight`. -/
theorem global_door_iff (P : (Fin 8 → ℝ) → Fin 8 → ℝ → Prop)
    (hP : ∀ v, IsArrangement v → ∀ k m, IsDmin v k m → (P v k m ↔ Isolation v k)) :
    (∀ v, IsArrangement v → ∀ k m, IsDmin v k m → P v k m) ↔ LonelyRunnerEight := by
  constructor
  · intro h v hv k
    obtain ⟨m, hm⟩ := exists_dmin (v := v) k
    exact (hP v hv k m hm).mp (h v hv k m hm)
  · intro h v hv k m hm
    exact (hP v hv k m hm).mpr (h v hv k)

#print axioms global_door_iff

/-- Door (C) for all arrangements is the conjecture. -/
theorem doorBounded_global_iff :
    (∀ v, IsArrangement v → ∀ k m, IsDmin v k m →
      BddAbove (Set.range (cascadeSeq (disparitySet v k) (1 / (8 * m))))) ↔ LonelyRunnerEight :=
  global_door_iff _ fun _ hv _ _ hm =>
    ((doors_agree hv hm).2.1.symm).trans (doors_agree hv hm).1.symm

#print axioms doorBounded_global_iff

/-- Door (E) for all arrangements is the conjecture. -/
theorem doorFinite_global_iff :
    (∀ v, IsArrangement v → ∀ k m, IsDmin v k m →
      ∀ d ∈ disparitySet v k, {n : ℕ | InWay d (cascadeSeq (disparitySet v k) (1 / (8 * m)) n)}.Finite) ↔
      LonelyRunnerEight :=
  global_door_iff _ fun _ hv _ _ hm =>
    ((doors_agree hv hm).2.2.2.symm).trans (doors_agree hv hm).1.symm

#print axioms doorFinite_global_iff

end Doors

end Fresh
