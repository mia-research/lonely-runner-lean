import Mathlib
import Fresh.Framework
import Fresh.Cascade
import Fresh.Dilation
import Fresh.ChainLaws
import Fresh.LonelyCells
import Fresh.Carving
import Fresh.Gate
import Fresh.Doors
import Fresh.OneMultiple
import Fresh.FiveReach

/-!
# The ladder: four, five and six disparities at gap `1/8` (Task AU)

Written 2026-10-09.  Imports `Mathlib` and the Fresh modules named in the task (plus `FiveReach`, whose `Reach`, `reach_three`
and `E_six` the task names).  Nothing is imported from the existing `LonelyRunner` repo.  Exact reals only; every
disparity is positive or at least nonzero (no runner is stationary); no floats.

## What the ladder is

A subject with `k+1` disparities has `d_min = m` among them.  In the cascade coordinate `R = 8 m t` the reading `m` is
clear on the whole first window `R ∈ [1, 7]` (`Gate.dmin_clear_first_window`).  So `k+1` disparities have a lonely instant
in `R ∈ [1, 7]` as soon as the OTHER `k` disparities (all `≥ m`) have one in `R ∈ [1, B]`, `B ≤ 7`.  That is
`ladder_step`: `Reach k B → (k+1 disparities)`.  The rungs:

| disparities | runners | needs | status |
|---|---|---|---|
| 4 | 5 | `Reach 3 B`, `B ≤ 7` | PROVED (`reach_three`, sup `729/343`): `four_disparities_lonely` |
| 5 | 6 | `Reach 4 B`, `B ≤ 7` | OWED (sup seen `289/105`): `five_disparities_of_reach_four` |
| 6 | 7 | `Reach 5 B`, `B ≤ 7` | OWED (sup seen `2125/483`; `FiveReach` is `B = 6`): `six_disparities_of_fiveReach` |
| 7 | 8 | `Reach 6 B`, `B ≤ 7` | FALSE for `B < 8.714` (`seven_cross_gate`, `no_ladder_at_seven`): the gate is crossed |

The step `k = 6` fails because six readings can carry the cascade past `R = 7`; this is the exact place the first window of
`d_min` stops protecting the subject, and it is the n = 8 situation (the gate lemmas of `Gate.lean`).

## Honest account of what is and is not a cascade proof

* `Reach 3` has TWO proofs in this folder.  `FiveReach.reach_three` (sup `729/343`) is a union bound in the measure `dR/R`
  (`cover_prod`): `[PROVISIONAL: covering]`, not a chain argument.  `reach_three_cascade` (section 2b, bound `(9/7)^7`) is a
  chain argument: the slowest reading returns only after four other moves (`slowest_return`, from `return_law` and `step_lt`),
  two other readings cannot fill four moves (`no_xyxy`, from `triple_law`), so at most seven moves occur.  The only counting step
  is the pigeonhole `eq_of_card_le_two` in `block_four_false`, `[PROVISIONAL: counting tool]`.  This is the cascade account of
  four disparities.
* `Reach 4`, `Reach 5` are OWED.  Section (2c) records the symbolic budget law that is the next tool (`lap_lower_of_ratio`,
  `step_lt_ratio`); the report records exactly where the chain argument stalls at four readings.

Provenance (existing declarations whose argument was read and understood, nothing copied): `Gate.dmin_clear_first_window` for
the idle first window; `FiveReach.reach_three`, `cover_six`, `not_reach_six`; `OneMultiple.seven_fails`.  The ladder
reductions are new here.
-/

open Classical

namespace Fresh

namespace Ladder

open Cascade Dilation ChainLaws FiveReachStudy

/-! ## (1) The ladder step -/

/-- A nonempty finite set of reals has a least element, in the form `IsLeast` that the gate lemmas use. -/
theorem exists_isLeast {ds : Finset ℝ} (h : ds.Nonempty) : ∃ m, IsLeast (ds : Set ℝ) m :=
  ⟨ds.min' h, ds.min'_mem h, fun d hd => ds.min'_le d hd⟩

#print axioms exists_isLeast

/-- **The ladder step** [L], any `k`.  Hypotheses: `Reach k B` with `B ≤ 7`; `ds` has least element `m > 0` and at most
`k + 1` members.  Conclusion: a lonely instant of `ds` in `R ∈ [1, B]`.
Why: `ds.erase m` has at most `k` members, all `≥ m`, so `Reach k B` gives a lonely instant `s` of them in
`[1/(8m), B/(8m)]`; and `m` itself reads in `[1/8, 7/8]` there (`Gate.dmin_clear_first_window`) because `B ≤ 7`.
`[PROVISIONAL: covering]` inherited from whichever `Reach k B` is supplied.  `B ≤ 7` is REQUIRED for this proof (at
`R ∈ (7, 9)` the reading `m` is in the way, `Gate.dmin_inWay_gate`); `0 < m` is REQUIRED (`audit_zero_disparity`). -/
theorem ladder_step {k : ℕ} {B : ℝ} (hB : B ≤ 7) (hR : Reach k B) {ds : Finset ℝ} {m : ℝ}
    (hm : IsLeast (ds : Set ℝ) m) (hm0 : 0 < m) (hcard : ds.card ≤ k + 1) :
    ∃ s, 1 / (8 * m) ≤ s ∧ s ≤ B / (8 * m) ∧ LonelyAt ds s := by
  have hE : (ds.erase m).card ≤ k := by
    have := Finset.card_erase_of_mem hm.1
    omega
  have hlow : ∀ d ∈ ds.erase m, m ≤ d := fun d hd => hm.2 (Finset.mem_of_mem_erase hd)
  obtain ⟨s, hs1, hs2, hsl⟩ := hR (ds.erase m) m hE hm0 hlow
  refine ⟨s, hs1, hs2, fun d hd => ?_⟩
  by_cases hdm : d = m
  · subst hdm
    refine Gate.dmin_clear_first_window hm0 hs1 (hs2.trans ?_)
    exact div_le_div_of_nonneg_right hB (by positivity)
  · exact hsl d (Finset.mem_erase.mpr ⟨hdm, hd⟩)

#print axioms ladder_step

/-- Positivity gives the least element and `m > 0`: the ladder step for a set of positive disparities. -/
theorem ladder_step_pos {k : ℕ} {B : ℝ} (hB : B ≤ 7) (hR : Reach k B) {ds : Finset ℝ}
    (hpos : ∀ d ∈ ds, 0 < d) (hcard : ds.card ≤ k + 1) :
    ∃ s, 0 < s ∧ LonelyAt ds s := by
  by_cases hne : ds.Nonempty
  · obtain ⟨m, hm⟩ := exists_isLeast hne
    have hm0 : 0 < m := hpos m hm.1
    obtain ⟨s, hs1, -, hsl⟩ := ladder_step hB hR hm hm0 hcard
    exact ⟨s, lt_of_lt_of_le (by positivity) hs1, hsl⟩
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    subst hne
    exact ⟨1, one_pos, fun d hd => absurd hd (Finset.notMem_empty d)⟩

#print axioms ladder_step_pos

/-! ## (2) Rung 4: four disparities, any positive reals -/

/-- **Four disparities (five runners)** [L].  Any set of at most four positive reals has a positive instant at which each
reads at least `1/8` from a lap line, and the instant lies in `R ∈ [1, 729/343]` of its least element.  No integrality,
commensurability, ordering or gap hypothesis; the count `≤ 4` is the only size hypothesis.
`[PROVISIONAL: covering]` (via `FiveReach.reach_three`, a union bound in `dR/R`; this is NOT a cascade-chain proof).
Compared with the counting proof `OneMultiple.exists_clear_card_le_four` (integers, pigeonhole on `j/(8P-1)`): the covering
proof needs no integrality and yields a window, the counting proof yields a rational instant but needs integers. -/
theorem four_disparities_lonely {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d) (hcard : ds.card ≤ 4) :
    ∃ s, 0 < s ∧ LonelyAt ds s :=
  ladder_step_pos (k := 3) (B := 729 / 343) (by norm_num) reach_three hpos hcard

#print axioms four_disparities_lonely

/-- The same with the window: the instant is in `[1/(8m), 729/(343·8m)]`. -/
theorem four_disparities_window {ds : Finset ℝ} {m : ℝ} (hm : IsLeast (ds : Set ℝ) m) (hm0 : 0 < m)
    (hcard : ds.card ≤ 4) :
    ∃ s, 1 / (8 * m) ≤ s ∧ s ≤ (729 / 343) / (8 * m) ∧ LonelyAt ds s :=
  ladder_step (k := 3) (B := 729 / 343) (by norm_num) reach_three hm hm0 hcard

#print axioms four_disparities_window

/-- **Positivity is not required, nonzero is** [L].  Disparities may carry either sign (`distInt` is even); a zero disparity
is never clear (`audit_zero_disparity`).  `[PROVISIONAL: covering]` as `four_disparities_lonely`. -/
theorem four_disparities_lonely_nonzero {ds : Finset ℝ} (hne : ∀ d ∈ ds, d ≠ 0) (hcard : ds.card ≤ 4) :
    ∃ s, 0 < s ∧ LonelyAt ds s := by
  have hc : (ds.image abs).card ≤ 4 := Finset.card_image_le.trans hcard
  have hp : ∀ d ∈ ds.image abs, 0 < d := by
    intro d hd
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hd
    exact abs_pos.mpr (hne e he)
  obtain ⟨s, hs, hl⟩ := four_disparities_lonely hp hc
  refine ⟨s, hs, fun d hd => ?_⟩
  have := hl |d| (Finset.mem_image_of_mem _ hd)
  rwa [distInt_abs_mul] at this

#print axioms four_disparities_lonely_nonzero

/-- **Five runners** [L]: five distinct speeds, every runner isolated at some positive instant at gap `1/8`.  (Also for
fewer runners.)  `[PROVISIONAL: covering]` as above. -/
theorem five_runners_isolated {n : ℕ} (hn : n ≤ 5) (v : Fin n → ℝ) (hv : Function.Injective v) (k : Fin n) :
    ∃ t : ℝ, 0 < t ∧ ∀ i, i ≠ k → (1 / 8 : ℝ) ≤ distInt ((v i - v k) * t) := by
  set ds : Finset ℝ := (Finset.univ.erase k).image (fun i => v i - v k) with hds
  have hc : ds.card ≤ 4 := by
    have h1 : ds.card ≤ (Finset.univ.erase k : Finset (Fin n)).card := Finset.card_image_le
    have h2 : (Finset.univ.erase k : Finset (Fin n)).card = n - 1 := by simp
    omega
  have hne : ∀ d ∈ ds, d ≠ 0 := by
    intro d hd
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hd
    have hik : i ≠ k := (Finset.mem_erase.mp hi).1
    intro h0
    exact hik (hv (by linarith))
  obtain ⟨s, hs, hl⟩ := four_disparities_lonely_nonzero hne hc
  exact ⟨s, hs, fun i hi => hl _ (Finset.mem_image_of_mem _ (Finset.mem_erase.mpr ⟨hi, Finset.mem_univ i⟩))⟩

#print axioms five_runners_isolated

/-! ## (2b) Rung 4 by the cascade's own laws: the slowest reading cannot return

The proof below does not cover and does not count instants.  It uses only: the setter of a move lands at
`x · seq (n+1) = j + 1/8` (`Dilation.setter_reading`); the faster clause persists (`ChainLaws.later_lap_of_ge`); one move on
lap `≥ N0` multiplies the instant by less than `(8 N0 + 1)/(8 N0 − 1)` (`FiveReach.step_lt`); the return inequality
(`FiveReach.return_law`); and the triple law (`FiveReach.triple_law`).  The number of moves is an OUTPUT (at most seven).
The only counting step is the pigeonhole `FiveReach.eq_of_card_le_two` (two letters cannot be three distinct letters),
`[PROVISIONAL: counting tool]`, supporting `block_four_false` and nothing else.

The recurrence of the argument: the SLOWEST reading `a` of the set that sets at `n` on lap `j` and is in the way again at
`k > n` forces `seq k > (8j+7)/(8j+1) · seq (n+1)`; every move in between is by a reading `≥ a`, hence on a lap `≥ j+1`
(faster clause), hence multiplies by less than `(8j+9)/(8j+7)`; and `((8j+9)/(8j+7))^3 < (8j+7)/(8j+1)` for all `j ≥ 0`.
So at least four moves intervene (`slowest_return`).  For a set of three readings the four intervening moves are set by the
two other readings, alternating, which the triple law forbids (`no_xyxy`). -/

/-- One move on laps `≥ N0 ≥ 1` (or no move) multiplies the instant by at most `(8N0+1)/(8N0−1)`. -/
theorem step_le_of_lap {E : Finset ℝ} {seq : ℕ → ℝ} (hpos : ∀ d ∈ E, 0 < d) (h0 : 0 < seq 0)
    (hmv : ∀ n, IsMove E (seq n) (seq (n + 1))) {s : ℕ} {N0 : ℝ} (hN0 : 1 ≤ N0)
    (hlaps : ∀ y, IsSetterAt E seq s y → N0 ≤ (lap y (seq s) : ℝ)) :
    seq (s + 1) ≤ (8 * N0 + 1) / (8 * N0 - 1) * seq s := by
  have hs0 : 0 < seq s := lt_of_lt_of_le h0 (start_le_seq hpos hmv s)
  rcases hmv s with ⟨_, hfix⟩ | ⟨x, hx, hwx, hset, _⟩
  · rw [hfix]
    have : 1 ≤ (8 * N0 + 1) / (8 * N0 - 1) := by
      rw [le_div_iff₀ (by linarith)]; linarith
    nlinarith
  · exact (step_lt hpos h0 hmv ⟨hx, hwx, hset⟩ hN0 (hlaps x ⟨hx, hwx, hset⟩)).le

#print axioms step_le_of_lap

/-- The numerical core: `((8j+9)/(8j+7))^3 < (8j+7)/(8j+1)` for `j ≥ 0`. -/
theorem cube_lt {j : ℝ} (hj : 0 ≤ j) : ((8 * j + 9) / (8 * j + 7)) ^ 3 < (8 * j + 7) / (8 * j + 1) := by
  rw [div_pow, div_lt_div_iff₀ (by positivity) (by positivity)]
  have e : (8 * j + 7) * (8 * j + 7) ^ 3 - (8 * j + 9) ^ 3 * (8 * j + 1)
      = 24 * (8 * j) ^ 2 + 400 * (8 * j) + 1672 := by ring
  nlinarith [sq_nonneg j]

#print axioms cube_lt

/-- **The slowest reading returns only after at least four other moves** [L].  Let `a ∈ E` be at most every member of `E`,
set the move at `n`, and be in the way at `seq k`, `n < k`.  Then `n + 5 ≤ k`. -/
theorem slowest_return {E : Finset ℝ} {m : ℝ} {seq : ℕ → ℝ} (hm : 0 < m) (hlow : ∀ d ∈ E, m ≤ d)
    (h0 : seq 0 = 1 / (8 * m)) (hmv : ∀ n, IsMove E (seq n) (seq (n + 1))) {a : ℝ} (ha : ∀ d ∈ E, a ≤ d)
    {n k : ℕ} (hn : IsSetterAt E seq n a) (hnk : n < k) (hw : InWay a (seq k)) : n + 5 ≤ k := by
  have hpos : ∀ d ∈ E, 0 < d := fun d hd => lt_of_lt_of_le hm (hlow d hd)
  have h0pos : 0 < seq 0 := by rw [h0]; positivity
  have hb : ∀ i, 1 / (8 * m) ≤ seq i := fun i => h0 ▸ start_le_seq hpos hmv i
  have hj1 : 1 ≤ lap a (seq n) := one_le_lap_of_bound hm (hlow a hn.1) (hb n) hn.2.1
  set j : ℝ := (lap a (seq n) : ℝ) with hjdef
  have hj1' : (1 : ℝ) ≤ j := by rw [hjdef]; exact_mod_cast hj1
  have hret := return_law hpos h0pos hmv hnk hn hw
  -- every later step is on a lap `≥ j + 1`
  have hstep : ∀ i : ℕ, seq (n + 1 + i + 1) ≤ (8 * (j + 1) + 1) / (8 * (j + 1) - 1) * seq (n + 1 + i) := by
    intro i
    refine step_le_of_lap hpos h0pos hmv (N0 := j + 1) (by linarith) (fun y hy => ?_)
    have hlap := later_lap_of_ge hpos h0pos hmv (show n < n + 1 + i by omega) hn (ha y hy.1) hy.2.1
    have : (lap a (seq n) : ℝ) + 1 ≤ (lap y (seq (n + 1 + i)) : ℝ) := by exact_mod_cast hlap
    linarith
  have hF : (8 * (j + 1) + 1) / (8 * (j + 1) - 1) = (8 * j + 9) / (8 * j + 7) := by
    congr 1 <;> ring
  rw [hF] at hstep
  have hF1 : 1 ≤ (8 * j + 9) / (8 * j + 7) := by
    rw [le_div_iff₀ (by linarith)]; linarith
  have hiter : ∀ i : ℕ, seq (n + 1 + i) ≤ ((8 * j + 9) / (8 * j + 7)) ^ i * seq (n + 1) := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      have hp : 0 < (8 * j + 9) / (8 * j + 7) := by positivity
      calc seq (n + 1 + (i + 1)) = seq (n + 1 + i + 1) := rfl
        _ ≤ (8 * j + 9) / (8 * j + 7) * seq (n + 1 + i) := hstep i
        _ ≤ (8 * j + 9) / (8 * j + 7) * (((8 * j + 9) / (8 * j + 7)) ^ i * seq (n + 1)) := by gcongr
        _ = ((8 * j + 9) / (8 * j + 7)) ^ (i + 1) * seq (n + 1) := by ring
  by_contra hcon
  have hk : k ≤ n + 4 := by omega
  obtain ⟨i, hi⟩ : ∃ i : ℕ, k = n + 1 + i := ⟨k - (n + 1), by omega⟩
  have hi3 : i ≤ 3 := by omega
  have hap : 0 < seq (n + 1) := lt_of_lt_of_le h0pos (start_le_seq hpos hmv (n + 1))
  have hpow : ((8 * j + 9) / (8 * j + 7)) ^ i ≤ ((8 * j + 9) / (8 * j + 7)) ^ 3 := pow_le_pow_right₀ hF1 hi3
  have hlt := cube_lt (j := j) (by linarith)
  have h1 : seq k ≤ ((8 * j + 9) / (8 * j + 7)) ^ 3 * seq (n + 1) := by
    rw [hi]
    exact (hiter i).trans (by gcongr)
  have h2 : ((8 * j + 9) / (8 * j + 7)) ^ 3 * seq (n + 1) < (8 * j + 7) / (8 * j + 1) * seq (n + 1) := by
    gcongr
  linarith

#print axioms slowest_return

/-- **Two readings do not alternate four times** [L]: `x y x y` as four consecutive setters is impossible
(`3 y < x` and `3 x < y`). -/
theorem no_xyxy {E : Finset ℝ} {seq : ℕ → ℝ} (hpos : ∀ d ∈ E, 0 < d) (h0 : 0 < seq 0)
    (hmv : ∀ n, IsMove E (seq n) (seq (n + 1))) {n : ℕ} {x y : ℝ} (hx : IsSetterAt E seq n x)
    (hy : IsSetterAt E seq (n + 1) y) (hx' : IsSetterAt E seq (n + 2) x) (hy' : IsSetterAt E seq (n + 3) y) :
    False := by
  have h1 := (triple_law hpos h0 hmv hx hy hx').1
  have h2 := (triple_law hpos h0 hmv hy hx' hy').1
  have hx0 := hpos x hx.1
  have hy0 := hpos y hy.1
  linarith

#print axioms no_xyxy

/-- **Four consecutive setters avoiding the slowest reading, from three readings, are impossible** [L].
`[PROVISIONAL: counting tool]` (`eq_of_card_le_two`: two letters cannot be three distinct letters), supporting only this
statement. -/
theorem block_four_false {E : Finset ℝ} {seq : ℕ → ℝ} (hpos : ∀ d ∈ E, 0 < d) (h0 : 0 < seq 0)
    (hmv : ∀ n, IsMove E (seq n) (seq (n + 1))) {a : ℝ} (haE : a ∈ E) (hcard : E.card ≤ 3) {n : ℕ}
    {w : ℕ → ℝ} (hw : ∀ i, n ≤ i → i ≤ n + 3 → IsSetterAt E seq i (w i)) (hna : ∀ i, n ≤ i → i ≤ n + 3 → w i ≠ a) :
    False := by
  have hE2 : (E.erase a).card ≤ 2 := by
    have := Finset.card_erase_of_mem haE
    omega
  have hmem : ∀ i, n ≤ i → i ≤ n + 3 → w i ∈ E.erase a :=
    fun i h1 h2 => Finset.mem_erase.mpr ⟨hna i h1 h2, (hw i h1 h2).1⟩
  have hne : ∀ i, n ≤ i → i + 1 ≤ n + 3 → w (i + 1) ≠ w i := by
    intro i h1 h2 heq
    exact setter_not_twice_in_row hpos (hw i h1 (by omega)) (heq ▸ hw (i + 1) (by omega) h2)
  have e02 : w n = w (n + 2) :=
    eq_of_card_le_two hE2 (hmem n le_rfl (by omega)) (hmem (n + 1) (by omega) (by omega)) (hmem (n + 2) (by omega) (by omega))
      (Ne.symm (hne n le_rfl (by omega))) (Ne.symm (hne (n + 1) (by omega) (by omega)))
  have e13 : w (n + 1) = w (n + 3) :=
    eq_of_card_le_two hE2 (hmem (n + 1) (by omega) (by omega)) (hmem (n + 2) (by omega) (by omega)) (hmem (n + 3) (by omega) (by omega))
      (Ne.symm (hne (n + 1) (by omega) (by omega))) (Ne.symm (hne (n + 2) (by omega) (by omega)))
  exact no_xyxy hpos h0 hmv (hw n le_rfl (by omega)) (hw (n + 1) (by omega) (by omega))
    (e02 ▸ hw (n + 2) (by omega) (by omega)) (e13 ▸ hw (n + 3) (by omega) (by omega))

#print axioms block_four_false

/-- **Three readings: the cascade makes at most seven forward moves, and it ends at `R ≤ (9/7)^7`** [L].  `Reach 3`
with the bound `(9/7)^7 = 4782969/823543 ≈ 5.81` (the exact supremum is `729/343 ≈ 2.13`; the cascade argument does not
reach it).  No covering, no density, no measure; the number of moves is an output.  Compare `FiveReach.reach_three`
(`[PROVISIONAL: covering]`).  `[PROVISIONAL: counting tool]` only in `block_four_false`. -/
theorem reach_three_cascade : Reach 3 ((9 / 7 : ℝ) ^ 7) := by
  intro E m hE hm hlow
  have hpos : ∀ d ∈ E, 0 < d := fun d hd => lt_of_lt_of_le hm (hlow d hd)
  have ht0 : 0 < 1 / (8 * m) := by positivity
  set seq : ℕ → ℝ := cascadeSeq E (1 / (8 * m)) with hseq
  have h0 : seq 0 = 1 / (8 * m) := cascadeSeq_zero E _
  have h0pos : 0 < seq 0 := by rw [h0]; exact ht0
  have hmv : ∀ n, IsMove E (seq n) (seq (n + 1)) := cascadeSeq_isMove E _
  have hb : ∀ n, 1 / (8 * m) ≤ seq n := fun n => h0 ▸ start_le_seq hpos hmv n
  -- some step `n ≤ 7` has nobody in the way
  have key : ∃ n, n ≤ 7 ∧ ∀ d ∈ E, ¬ InWay d (seq n) := by
    by_contra hcon
    push Not at hcon
    have hset : ∀ n, n ≤ 7 → ∃ x, IsSetterAt E seq n x := by
      intro n hn
      obtain ⟨d, hd, hdw⟩ := hcon n hn
      exact exists_setter hmv (fun hall => hall d hd hdw)
    have hne : E.Nonempty := by
      obtain ⟨x, hx⟩ := hset 0 (by norm_num)
      exact ⟨x, hx.1⟩
    choose! w hw using hset
    obtain ⟨a, haE⟩ := exists_isLeast hne
    -- pairwise: two settings of the slowest reading are at least five steps apart
    have hS : ∀ i j, i ≤ 7 → j ≤ 7 → w i = a → w j = a → i < j → i + 5 ≤ j := by
      intro i j hi hj hwi hwj hij
      refine slowest_return hm hlow h0 hmv (fun d hd => haE.2 hd) (n := i) (k := j) ?_ hij ?_
      · have := hw i hi
        rw [hwi] at this
        exact this
      · have := (hw j hj).2.1
        rw [hwj] at this
        exact this
    -- some window of four consecutive steps avoids `a`
    have hwin : ∃ s, s ≤ 4 ∧ ∀ i, s ≤ i → i ≤ s + 3 → w i ≠ a := by
      by_contra hno
      push Not at hno
      obtain ⟨i0, h0a, h0b, h0c⟩ := hno 0 (by norm_num)
      obtain ⟨i1, h1a, h1b, h1c⟩ := hno 1 (by norm_num)
      obtain ⟨i2, h2a, h2b, h2c⟩ := hno 2 (by norm_num)
      obtain ⟨i3, h3a, h3b, h3c⟩ := hno 3 (by norm_num)
      obtain ⟨i4, h4a, h4b, h4c⟩ := hno 4 (by norm_num)
      have p01 := hS i0 i1 (by omega) (by omega) h0c h1c
      have p10 := hS i1 i0 (by omega) (by omega) h1c h0c
      have p12 := hS i1 i2 (by omega) (by omega) h1c h2c
      have p21 := hS i2 i1 (by omega) (by omega) h2c h1c
      have p23 := hS i2 i3 (by omega) (by omega) h2c h3c
      have p32 := hS i3 i2 (by omega) (by omega) h3c h2c
      have p34 := hS i3 i4 (by omega) (by omega) h3c h4c
      have p43 := hS i4 i3 (by omega) (by omega) h4c h3c
      omega
    obtain ⟨s, hs4, hsa⟩ := hwin
    exact block_four_false hpos h0pos hmv haE.1 hE (n := s) (w := w)
      (fun i h1 h2 => hw i (by omega)) hsa
  obtain ⟨n, hn7, hn⟩ := key
  have hpow : seq n ≤ (9 / 7 : ℝ) ^ n * seq 0 := by
    have := seq_le_pow hm hlow h0 hmv 0 n
    simpa using this
  have hpow7 : (9 / 7 : ℝ) ^ n ≤ (9 / 7) ^ 7 := pow_le_pow_right₀ (by norm_num) hn7
  refine ⟨seq n, hb n, ?_, lonely_of_notInWay hn⟩
  rw [h0] at hpow
  calc seq n ≤ (9 / 7 : ℝ) ^ n * (1 / (8 * m)) := hpow
    _ ≤ (9 / 7 : ℝ) ^ 7 * (1 / (8 * m)) := by gcongr
    _ = (9 / 7 : ℝ) ^ 7 / (8 * m) := by ring

#print axioms reach_three_cascade

/-- **Four disparities by the cascade** [L]: any set of at most four positive reals has a lonely instant in `R ∈ [1, (9/7)^7]`
of its least element.  The proof of `reach_three_cascade` plus the idle first window of `d_min` (`ladder_step`, `(9/7)^7 ≤ 7`). -/
theorem four_disparities_lonely_cascade {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d) (hcard : ds.card ≤ 4) :
    ∃ s, 0 < s ∧ LonelyAt ds s :=
  ladder_step_pos (k := 3) (B := (9 / 7 : ℝ) ^ 7) (by norm_num) reach_three_cascade hpos hcard

#print axioms four_disparities_lonely_cascade

/-! ## (2c) The budget law: the lap of an intermediate reading is bounded below by its speed ratio

For ANY reading `x` that sets at `n` on lap `j` (not only the slowest), every later setter `y` has a lap bounded below by the
ratio `y/x`: `8·lap y + 1 > (y/x)(8j+1)`.  With `step_lt` this bounds the step factor of `y` by
`ρN/(ρN − 2)` (`ρ = y/x`, `N = 8j+1`) once `ρN ≥ 9`.  Multiplying over the moves between a setting and a return of `x`
gives the BUDGET LAW `∏_s ρ_s N/(ρ_s N − 2) > (N+6)/N` (`return_law`), i.e. asymptotically `Σ_s x/y_s ≥ 3`: the
intermediates must carry a total weight `x/y` of three.  `slowest_return` is the case where every `y ≥ x`, so every weight
is below one and at least four intermediates are needed.  The product form is a telescoping of the two lemmas below and
is tested exactly in the report (0 violations, `min (∏ / need) = 1.027`); it is not formalised here. -/

/-- **Lap lower bound from the speed ratio** [L]. -/
theorem lap_lower_of_ratio {E : Finset ℝ} {seq : ℕ → ℝ} (hpos : ∀ d ∈ E, 0 < d) (h0 : 0 < seq 0)
    (hmv : ∀ n, IsMove E (seq n) (seq (n + 1))) {n s : ℕ} {x y : ℝ} (hx : IsSetterAt E seq n x) (hns : n < s)
    (hy0 : 0 < y) (hy : InWay y (seq s)) :
    y / x * (8 * (lap x (seq n) : ℝ) + 1) < 8 * (lap y (seq s) : ℝ) + 1 := by
  have hx0 := hpos x hx.1
  have hland : x * seq (n + 1) = (lap x (seq n) : ℝ) + 1 / 8 := by
    rw [hx.2.2]; exact setter_reading hx0 hx.2.1
  have hle : seq (n + 1) ≤ seq s := seq_mono hpos hmv (Nat.succ_le_of_lt hns)
  have hb := (abs_lt.mp (abs_sub_lap_lt hy)).2
  have h1 : y * seq (n + 1) ≤ y * seq s := mul_le_mul_of_nonneg_left hle hy0.le
  -- y · seq(n+1) = (y/x)(j + 1/8)
  have e : y * seq (n + 1) = y / x * ((lap x (seq n) : ℝ) + 1 / 8) := by
    rw [← hland]; field_simp
  have : y / x * ((lap x (seq n) : ℝ) + 1 / 8) < (lap y (seq s) : ℝ) + 1 / 8 := by linarith
  linarith

#print axioms lap_lower_of_ratio

/-- **The step factor of an intermediate reading, from its speed ratio** [L].  If `x` sets at `n` on lap `j`, `y` sets at
`s > n`, and `ρ N ≥ 9` with `ρ = y/x`, `N = 8j+1`, then `seq (s+1) < ρN/(ρN − 2) · seq s`. -/
theorem step_lt_ratio {E : Finset ℝ} {seq : ℕ → ℝ} (hpos : ∀ d ∈ E, 0 < d) (h0 : 0 < seq 0)
    (hmv : ∀ n, IsMove E (seq n) (seq (n + 1))) {n s : ℕ} {x y : ℝ} (hx : IsSetterAt E seq n x) (hns : n < s)
    (hy : IsSetterAt E seq s y) (h9 : 9 ≤ y / x * (8 * (lap x (seq n) : ℝ) + 1)) :
    seq (s + 1) < (y / x * (8 * (lap x (seq n) : ℝ) + 1)) / (y / x * (8 * (lap x (seq n) : ℝ) + 1) - 2) * seq s := by
  have hy0 := hpos y hy.1
  have hlow := lap_lower_of_ratio hpos h0 hmv hx hns hy0 hy.2.1
  set P : ℝ := y / x * (8 * (lap x (seq n) : ℝ) + 1) with hP
  -- N0 = (P - 1)/8 ≥ 1 and N0 ≤ lap y
  have hN0 : (1 : ℝ) ≤ (P - 1) / 8 := by rw [le_div_iff₀ (by norm_num)]; linarith
  have hlap : (P - 1) / 8 ≤ (lap y (seq s) : ℝ) := by rw [div_le_iff₀ (by norm_num)]; linarith
  have := step_lt hpos h0 hmv hy hN0 hlap
  have e1 : 8 * ((P - 1) / 8) + 1 = P := by ring
  have e2 : 8 * ((P - 1) / 8) - 1 = P - 2 := by ring
  rwa [e1, e2] at this

#print axioms step_lt_ratio

/-! ## (3) Rungs 5 and 6: reductions, the statements owed -/

/-- Five disparities (six runners) have a lonely instant. -/
-- STANDING: OWED
def FiveDisparitiesLonely : Prop :=
  ∀ ds : Finset ℝ, (∀ d ∈ ds, 0 < d) → ds.card ≤ 5 → ∃ s, 0 < s ∧ LonelyAt ds s

/-- Six disparities (seven runners) have a lonely instant. -/
-- STANDING: OWED
def SixDisparitiesLonely : Prop :=
  ∀ ds : Finset ℝ, (∀ d ∈ ds, 0 < d) → ds.card ≤ 6 → ∃ s, 0 < s ∧ LonelyAt ds s

/-- **Rung 5 from `Reach 4`** [L]: any `B ≤ 7`.  The supremum seen is `289/105 ≈ 2.75`, so `7` carries a margin of `4.2`. -/
theorem five_disparities_of_reach_four {B : ℝ} (hB : B ≤ 7) (h : Reach 4 B) : FiveDisparitiesLonely :=
  fun _ hpos hcard => ladder_step_pos hB h hpos hcard

#print axioms five_disparities_of_reach_four

/-- **Rung 6 from `Reach 5`** [L]: any `B ≤ 7`. -/
theorem six_disparities_of_reach_five {B : ℝ} (hB : B ≤ 7) (h : Reach 5 B) : SixDisparitiesLonely :=
  fun _ hpos hcard => ladder_step_pos hB h hpos hcard

#print axioms six_disparities_of_reach_five

/-- **Rung 6 from `FiveReach`** (`Reach 5 6`). -/
theorem six_disparities_of_fiveReach (h : StrongGateStudy.FiveReach) : SixDisparitiesLonely :=
  six_disparities_of_reach_five (B := 6) (by norm_num) h

#print axioms six_disparities_of_fiveReach

/-- Rung 5 from the sharp statement owed in `FiveReach.lean`. -/
theorem five_disparities_of_sharp (h : ReachFourSharp) : FiveDisparitiesLonely :=
  five_disparities_of_reach_four (B := 289 / 105) (by norm_num) h

#print axioms five_disparities_of_sharp

/-- Rung 6 from the sharp statement owed in `FiveReach.lean`. -/
theorem six_disparities_of_sharp (h : ReachFiveSharp) : SixDisparitiesLonely :=
  six_disparities_of_reach_five (B := 2125 / 483) (by norm_num) h

#print axioms six_disparities_of_sharp

/-- The rungs are nested: six disparities give five (a set of at most five is a set of at most six). -/
theorem five_of_six (h : SixDisparitiesLonely) : FiveDisparitiesLonely :=
  fun ds hpos hcard => h ds hpos (hcard.trans (by norm_num))

#print axioms five_of_six

/-! ## (4) Where the ladder stops: seven disparities cross the gate -/

/-- **Seven disparities cross the gate** [L].  `ds = {1} ∪ E_six` (seven positive reals, `d_min = 1`): no instant of
`R ∈ [1, 8.7)` is lonely, in particular none in the first window `R ∈ [1, 7]` that protects `d_min`.  Proof: `cover_six`
(a chain of twenty zones of the six readings, certified by exact rational inequalities in `FiveReach.lean`). -/
theorem seven_cross_gate :
    ¬ ∃ s : ℝ, 1 / 8 ≤ s ∧ s ≤ 7 / 8 ∧ LonelyAt (insert (1 : ℝ) E_six) s := by
  rintro ⟨s, h1, h2, hl⟩
  obtain ⟨d, hd, hw⟩ := cover_six s h1 (by linarith)
  exact (not_inWay_iff.mpr (hl d (Finset.mem_insert_of_mem hd))) hw

#print axioms seven_cross_gate

/-- The ladder step cannot be run at `k = 6`: `Reach 6 7` is false (a sixth reading carries the cascade past `R = 7`). -/
theorem no_ladder_at_seven : ¬ Reach 6 7 := fun h => not_reach_six (reach_mono_bound (by norm_num) h)

#print axioms no_ladder_at_seven

/-! ## (5) Hypothesis audit -/

/-- A zero disparity is never clear. -/
theorem audit_zero_disparity : ¬ ∃ s : ℝ, LonelyAt ({0} : Finset ℝ) s := by
  rintro ⟨s, hl⟩
  have := hl 0 (Finset.mem_singleton_self 0)
  simp [distInt] at this
  linarith

#print axioms audit_zero_disparity

/-- (`m ≤ d` dropped from `Reach`) a reading below the base blocks the whole window: `E = {1/100}`, `m = 1`, window
`s ∈ [1/8, 7/8]`. -/
theorem audit_lower_bound : ¬ ∃ s : ℝ, 1 / 8 ≤ s ∧ s ≤ 7 / 8 ∧ LonelyAt ({(1 / 100 : ℝ)} : Finset ℝ) s := by
  rintro ⟨s, h1, h2, hl⟩
  have h := hl (1 / 100) (Finset.mem_singleton_self _)
  have h3 : distInt ((1 / 100 : ℝ) * s) ≤ |(1 / 100 : ℝ) * s - ((0 : ℤ) : ℝ)| := distInt_le _ 0
  have h4 : |(1 / 100 : ℝ) * s - ((0 : ℤ) : ℝ)| = (1 / 100) * s := by
    rw [Int.cast_zero, sub_zero]; exact abs_of_nonneg (by positivity)
  linarith

#print axioms audit_lower_bound

/-- (`B ≤ 7` dropped) with the window running into the gate `R ∈ (7, 9)`, a lonely instant of `ds.erase m` need not be
lonely for `ds`: `ds = {1}`, `ds.erase 1 = ∅` (lonely everywhere), `s = 1` (`R = 8`, in `[1, 9]`) is not clear for `m = 1`. -/
theorem audit_gate_needed : LonelyAt (∅ : Finset ℝ) 1 ∧ ¬ LonelyAt ({1} : Finset ℝ) 1 := by
  refine ⟨fun d hd => absurd hd (Finset.notMem_empty d), fun hl => ?_⟩
  have := hl 1 (Finset.mem_singleton_self 1)
  have h0 : distInt ((1 : ℝ) * 1) = 0 := by
    have := Localisation.distInt_intCast 1
    simpa using this
  rw [h0] at this
  norm_num at this

#print axioms audit_gate_needed

/-- (the count) eight disparities can fail: `{1,…,7,8}` has no lonely instant (`OneMultiple.seven_fails_c1`), so a size
hypothesis on `ds` is REQUIRED for the TRUTH of the lonely-instant statement, not only for the method. -/
theorem audit_card_eight : ¬ ∃ t : ℝ, LonelyAt (TwoScale.realSet {1, 2, 3, 4, 5, 6, 7} {1}) t :=
  OneMultiple.seven_fails_c1

#print axioms audit_card_eight

end Ladder

end Fresh
