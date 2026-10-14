import Mathlib
import Fresh.Framework
import Fresh.Cascade
import Fresh.Dilation
import Fresh.ChainLaws
import Fresh.Ladder
import Fresh.Ladder5
import Fresh.FourDistinct
import Fresh.LadderScale
import Fresh.TimeBudget
import Fresh.Gate

/-!
# Five disparities with the second smallest below five times `d_min` (Task CA)

Written 2026-10-10.  Nothing is imported from the existing `LonelyRunner` repo.  Exact reals only; every disparity is positive
(no runner is stationary); no floats.  Data (exact fractions, explicit grids; counts are observations of those grids):
`experiments/n8/five_low_v1.py/.out`.

Setting.  `E` is the set of the four readings other than `d_min = m`; `a = min E`; `S = E.erase a` has at most three members.
The cascade over `E` starts at `1/(8m)` (`R = 8 m t = 1`).

## Results (grades [L]; each theorem has its `#print axioms` line)

* `reach_four_cases`, `reach_four_low` [L]: if `729 a < 24353 m` (`ρ_a < 24353/729`, which contains `ρ_a ∈ [1,5)`), the four
  readings have a lonely instant in `R ∈ [1, (9/7)^7]`.  The argument is the cascade's own phase structure.
  (i) Until `a` is the SETTER of a move, the moves of the cascade over `E` are the moves of the cascade over `S`
  (`isMove_erase_of_not_setter`), so the cascade stays at or below any lonely instant of `S` (`seq_le_of_erase`); `Reach 3`
  gives one at `R ≤ 729/343`.  (ii) If `a` never sets, the fixed point is at `R ≤ 729/343`.  (iii) If `a` sets (first time at `k`),
  it sets on a lap `≤ 8`, so by `FourDistinct.slowest_of_four_never_returns_lap` it is never in the way again; the landing satisfies
  `seq (k+1) < 9/7 seq k`, the moves are again moves of `S`, now from `seq (k+1)`, and `Reach 3` for `S` rescaled to the base
  `1/(8 seq (k+1))` gives a lonely instant of `S` at `R ≤ 729/343 · seq (k+1)`.  So the fixed point is at
  `R ≤ (729/343)^2 · 9/7 = (9/7)^7`.
* `reach_four_small` [L]: if `729 a ≤ 2401 m` (`ρ_a ≤ 2401/729`) then `a` never matters: the lonely instant of `S` at `R ≤ 729/343`
  is lonely for `E`.  Above `2401/729` the reading `a` can be in the way at the end of an `S`-chain (data: `five_low_v1.out`,
  section 1, the smallest `a` that sets on the grids searched).
* `landing_lap_one`, `reach_four_where` [L]: for `ρ_a < 5` the setting of `a` is on lap `1` and lands at `R = 9 m/a`; the lonely
  instant is at `R ≤ 729/343` or at `R ≤ 729/343 · 9 m/a`.  This is the place the isolation of the `d_min` window `[1,7]` goes to
  when `a` displaces it.
* `five_disparities_low`, `fiveDisparitiesLowQuotient`, `five_disparities_quotient_below_57` [L]: five disparities, second
  smallest below `24353/729 · d_min` (so below `5 d_min`), have a lonely instant in `R ∈ [1,7]`; this is the statement
  `LadderScale.FiveDisparitiesLowQuotient` (tagged OWED there).  With `LadderScale.five_disparities_of_ratio` the quotient range
  `[1, 57)` is covered.

## Tags at the steps

`[PROVISIONAL: covering]` at every use of `FiveReachStudy.reach_three` (a union bound in the measure `dR/R`): it supplies a
lonely instant of three readings at `R ≤ 729/343`, and supports the position of the displaced isolation and nothing else (rule 1:
the isolation of the `d_min` window `[1,7]` is displaced by the one setting of `a`, and the cascade shows where it lands).  It is
not offered as an existence argument for the conjecture.  `[PROVISIONAL: counting tool]` in `four_cascade_fixes` (used to know the
cascade over `E` has a fixed point; the number fifteen does not enter any statement here).

## Hypotheses (REQUIRED / NOT REQUIRED / UNDECIDED)

| hypothesis | status |
|---|---|
| `E.card ≤ 4` | REQUIRED for this proof (`Reach 3` for `S`; `slowest_of_four_never_returns_lap`); at five readings the statement is UNDECIDED (data, section 2.2: no failure on the grid) |
| `a` least in `E` | REQUIRED for the proof; the sub-claim 'a does not return after it sets' is FALSE for a non-least reading (data, section 2.1: `E = {4,5,6,15/2}`, `x = 15/2`) |
| `m ≤ d` for `d ∈ E`, `0 < m` | REQUIRED (`step_nine`, `one_le_lap_of_bound`, the rescaled base `1/(8 seq (k+1)) ≤ m`) |
| `729 a < 24353 m` | REQUIRED for this proof (it gives `lap a (seq k) ≤ 8`, the lap condition of `FourDistinct`); NOT shown required for the statement (`LadderScale.five_disparities_of_ratio` covers `5 m ≤ a < 57 m` by the move count); the lap condition fails for `CE` (data 2.3) |
| `5 m ≤ a` of `five_disparities_of_ratio` | NOT REQUIRED here: this proof does not use the move count `N m ≤ 3 a` (data: `N m ≤ 3 a` fails on the grids, section 1) |
| `a < 5 m` in `landing_lap_one`, `reach_four_where` | REQUIRED for the lap-one landing (`a · seq n < 7/4` is derived from it); not used by `reach_four_low` |
| `Reach 3` with bound `729/343` | REQUIRED in this form: the final step needs `(bound)^2 · 9/7 ≤ 7`; the cascade chain bound `(9/7)^7` for three readings (`Ladder.reach_three_cascade`) is too large for it |

Provenance (existing declarations whose argument was read and understood, nothing copied): `LadderScale.four_cascade_fixes`
(the fixed point), `FourDistinct.slowest_of_four_never_returns_lap` (a setter `a` does not return),
`FiveReachStudy.reach_three` (covering), `FiveReachStudy.step_nine`, `Cascade.isMove_le_of_lonely` (no overshoot).  The comparison
of the cascade over `E` with the cascade over `E.erase a`, and the rescaled second use of `Reach 3`, are new here.
-/

open Classical

namespace Fresh

namespace FiveLow

open Cascade Dilation ChainLaws FiveReachStudy Ladder Ladder5 FourDistinct LadderScale

/-! ## (1) The cascade over `E` is the cascade over `E.erase a` until `a` sets -/

/-- **A move of `E` in which `a` is not the setter is a move of `E.erase a`** [L]. -/
theorem isMove_erase_of_not_setter {E : Finset ℝ} {t t' a : ℝ} (hm : IsMove E t t')
    (hns : ¬ (InWay a t ∧ t' = nextOpening a t)) : IsMove (E.erase a) t t' := by
  rcases hm with ⟨hall, hfix⟩ | ⟨d, hd, hwd, hdt, hmax⟩
  · left
    exact ⟨fun d hd => hall d (Finset.mem_of_mem_erase hd), hfix⟩
  · right
    have hda : d ≠ a := by
      intro h
      subst h
      exact hns ⟨hwd, hdt⟩
    exact ⟨d, Finset.mem_erase.mpr ⟨hda, hd⟩, hwd, hdt,
      fun d' hd' hw' => hmax d' (Finset.mem_of_mem_erase hd') hw'⟩

#print axioms isMove_erase_of_not_setter

/-- **No overshoot of a lonely instant of `E.erase a`, while `a` does not set** [L].  `seq` is a cascade sequence of `E`;
from `k1` to `K` no move is set by `a`; `s` is lonely for `E.erase a` and `seq k1 ≤ s`.  Then `seq n ≤ s` for `k1 ≤ n ≤ K`. -/
theorem seq_le_of_erase {E : Finset ℝ} {seq : ℕ → ℝ} {a s : ℝ} (haE : a ∈ E) (hpos : ∀ d ∈ E, 0 < d)
    (hmv : ∀ n, IsMove E (seq n) (seq (n + 1))) (hl : LonelyAt (E.erase a) s) {k1 K : ℕ} (hk1 : seq k1 ≤ s)
    (hns : ∀ n, k1 ≤ n → n < K → ¬ IsSetterAt E seq n a) : ∀ n, k1 ≤ n → n ≤ K → seq n ≤ s := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => intro _; exact hk1
  | succ n hn ih =>
    intro hnK
    have hmv' : IsMove (E.erase a) (seq n) (seq (n + 1)) :=
      isMove_erase_of_not_setter (hmv n) (fun h => hns n hn (by omega) ⟨haE, h.1, h.2⟩)
    exact isMove_le_of_lonely (fun d hd => hpos d (Finset.mem_of_mem_erase hd)) hl (ih (by omega)) hmv'

#print axioms seq_le_of_erase

/-! ## (2) `a` never matters when its quotient is at most `2401/729` -/

/-- **A reading `a` with `729 a ≤ 2401 m` is clear on the whole window of `Reach 3`** [L]: the lonely instant of `S` at
`R ≤ 729/343` is lonely for `E = insert a S`.  `[PROVISIONAL: covering]` (`reach_three`), supporting the position of the
displaced isolation only.  The threshold `2401/729 = 7/(729/343)` is where `ρ_a · 729/343` reaches `7`: a reading with `ρ_a R > 7`
at the end of an `S`-chain is in the way (`reach_four_cases` takes over). -/
theorem reach_four_small {E : Finset ℝ} {m a : ℝ} (hm : 0 < m) (hlow : ∀ d ∈ E, m ≤ d) (hcard : E.card ≤ 4)
    (haE : a ∈ E) (hr : 729 * a ≤ 2401 * m) :
    ∃ s, 1 / (8 * m) ≤ s ∧ s ≤ 729 / 343 / (8 * m) ∧ LonelyAt E s := by
  have hSc : (E.erase a).card ≤ 3 := by
    have := Finset.card_erase_of_mem haE
    omega
  have hSlow : ∀ d ∈ E.erase a, m ≤ d := fun d hd => hlow d (Finset.mem_of_mem_erase hd)
  obtain ⟨s1, hs1a, hs1b, hs1l⟩ := reach_three (E.erase a) m hSc hm hSlow
  have ham : m ≤ a := hlow a haE
  have ha0 : 0 < a := lt_of_lt_of_le hm ham
  refine ⟨s1, hs1a, hs1b, fun d hd => ?_⟩
  by_cases hda : d = a
  · subst hda
    refine Gate.dmin_clear_first_window ha0 ?_ ?_
    · refine le_trans ?_ hs1a
      exact one_div_le_one_div_of_le (by positivity) (by linarith)
    · refine hs1b.trans ?_
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
  · exact hs1l d (Finset.mem_erase.mpr ⟨hda, hd⟩)

#print axioms reach_four_small

/-! ## (3) The main statement: four readings, second smallest quotient below `24353/729` -/

/-- **Four readings, least quotient below `24353/729`: a lonely instant in `R ∈ [1, (9/7)^7]`** [L].  `E` has at most four
members, all `≥ m > 0`, `a = min E`, `729 a < 24353 m`.  `[PROVISIONAL: covering]` at both uses of `reach_three`
(`S = E.erase a` at base `m`, then at the base `1/(8 seq (k+1))`), supporting the position of the displaced isolation only
(rule 1: the isolation of the `d_min` window is displaced by the one setting of `a`; the cascade shows where it lands).
`[PROVISIONAL: counting tool]` in `four_cascade_fixes` (existence of the fixed point; the fifteen is not used).
Hypotheses: see the table in the header (`729 a < 24353 m` gives `lap a (seq k) ≤ 8`). -/
theorem reach_four_cases {E : Finset ℝ} {m a : ℝ} (hm : 0 < m) (hlow : ∀ d ∈ E, m ≤ d) (hcard : E.card ≤ 4)
    (haE : a ∈ E) (ham : ∀ d ∈ E, a ≤ d) (hr : 729 * a < 24353 * m) :
    ∃ s, 1 / (8 * m) ≤ s ∧ LonelyAt E s ∧
      (s ≤ 729 / 343 / (8 * m) ∨
        ∃ k, IsSetterAt E (cascadeSeq E (1 / (8 * m))) k a ∧ cascadeSeq E (1 / (8 * m)) k ≤ 729 / 343 / (8 * m) ∧
          s ≤ 729 / 343 * cascadeSeq E (1 / (8 * m)) (k + 1) ∧
          cascadeSeq E (1 / (8 * m)) (k + 1) ≤ 9 / 7 * (729 / 343 / (8 * m))) := by
  have hpos : ∀ d ∈ E, 0 < d := fun d hd => lt_of_lt_of_le hm (hlow d hd)
  have ha0 : 0 < a := hpos a haE
  set seq : ℕ → ℝ := cascadeSeq E (1 / (8 * m)) with hseq
  have h0 : seq 0 = 1 / (8 * m) := cascadeSeq_zero E _
  have h0pos : 0 < seq 0 := by rw [h0]; positivity
  have hmv : ∀ n, IsMove E (seq n) (seq (n + 1)) := cascadeSeq_isMove E _
  have hb : ∀ n, 1 / (8 * m) ≤ seq n := fun n => h0 ▸ start_le_seq hpos hmv n
  have hSc : (E.erase a).card ≤ 3 := by
    have := Finset.card_erase_of_mem haE
    omega
  have hSlow : ∀ d ∈ E.erase a, m ≤ d := fun d hd => hlow d (Finset.mem_of_mem_erase hd)
  -- [PROVISIONAL: covering]: a lonely instant of S at R ≤ 729/343
  obtain ⟨s1, hs1a, hs1b, hs1l⟩ := reach_three (E.erase a) m hSc hm hSlow
  have h57 : a < 57 * m := by linarith
  obtain ⟨N, -, hfix, -⟩ := four_cascade_fixes hpos h0pos hmv hcard haE ham (lapCond_of_ratio hm hpos ha0 ham h0 h57)
  by_cases hex : ∃ n, IsSetterAt E seq n a
  · -- `a` sets; `k` is its first setting
    set k := Nat.find hex with hkdef
    have hk : IsSetterAt E seq k a := Nat.find_spec hex
    have hkmin : ∀ n, n < k → ¬ IsSetterAt E seq n a := fun n hn => Nat.find_min hex hn
    have hseqk : seq k ≤ s1 :=
      seq_le_of_erase haE hpos hmv hs1l (k1 := 0) (K := k) (by rw [h0]; exact hs1a)
        (fun n _ hn => hkmin n hn) k (Nat.zero_le _) le_rfl
    -- the lap of `a` at its setting is at most eight
    have hlapk : lap a (seq k) ≤ 8 := by
      refine lap_le_eight_of_lt hk.2.1 ?_
      have h1 : a * seq k ≤ a * s1 := mul_le_mul_of_nonneg_left hseqk ha0.le
      have h2 : a * s1 ≤ a * (729 / 343 / (8 * m)) := mul_le_mul_of_nonneg_left hs1b ha0.le
      have h3 : a * (729 / 343 / (8 * m)) < 71 / 8 := by
        have e : a * (729 / 343 / (8 * m)) = (729 * a) / (2744 * m) := by field_simp; ring
        rw [e, div_lt_iff₀ (by positivity)]
        nlinarith
      linarith
    -- `a` does not return (FourDistinct, lap at most eight)
    have hnever : ∀ j, k < j → ¬ InWay a (seq j) := by
      intro j hj hw
      have hex2 : ∃ j, k < j ∧ InWay a (seq j) := ⟨j, hj, hw⟩
      have hj2 := Nat.find_spec hex2
      have hmin2 : ∀ s, k < s → s < Nat.find hex2 → ¬ InWay a (seq s) :=
        fun s h1 h2 h => Nat.find_min hex2 h2 ⟨h1, h⟩
      exact slowest_of_four_never_returns_lap hpos h0pos hmv hcard ham hk hj2.1 hmin2 (Or.inl hlapk) hj2.2
    have ht1 : seq (k + 1) < 9 / 7 * seq k := step_nine hm hlow h0 hmv hk
    have ht1b : seq (k + 1) ≤ 9 / 7 * s1 := by linarith
    have ht1pos : 0 < seq (k + 1) := lt_of_lt_of_le h0pos (start_le_seq hpos hmv (k + 1))
    have ht1ge : 1 / (8 * m) ≤ seq (k + 1) := hb _
    -- the second use of Reach 3: base `1/(8 seq (k+1))`
    have hm2 : 0 < 1 / (8 * seq (k + 1)) := by positivity
    have hm2low : ∀ d ∈ E.erase a, 1 / (8 * seq (k + 1)) ≤ d := by
      intro d hd
      have h1 : 1 / (8 * seq (k + 1)) ≤ m := by
        rw [div_le_iff₀ (by positivity)]
        have := (div_le_iff₀ (by positivity : (0 : ℝ) < 8 * m)).mp ht1ge
        linarith
      exact h1.trans (hSlow d hd)
    -- [PROVISIONAL: covering]: a lonely instant of S at R ≤ 729/343 · seq (k+1)
    obtain ⟨s2, hs2a, hs2b, hs2l⟩ := reach_three (E.erase a) (1 / (8 * seq (k + 1))) hSc hm2 hm2low
    have e8 : 1 / (8 * (1 / (8 * seq (k + 1)))) = seq (k + 1) := by field_simp
    rw [e8] at hs2a
    have hs2b' : s2 ≤ 729 / 343 * seq (k + 1) := by
      have e : (729 / 343 : ℝ) / (8 * (1 / (8 * seq (k + 1)))) = 729 / 343 * seq (k + 1) := by field_simp
      rw [e] at hs2b
      exact hs2b
    -- the fixed point is after `k`
    have hNk : k < N := by
      by_contra hle
      push Not at hle
      have hfx := fixed_forever hmv hfix (k - N)
      rw [show N + (k - N) = k by omega] at hfx
      have hw : InWay a (seq k) := hk.2.1
      rw [hfx] at hw
      exact hfix a haE hw
    have hNs2 : seq N ≤ s2 :=
      seq_le_of_erase haE hpos hmv hs2l (k1 := k + 1) (K := N) hs2a
        (fun n hn _ hset => hnever n (by omega) hset.2.1) N (by omega) le_rfl
    refine ⟨seq N, hb N, lonely_of_notInWay hfix, Or.inr ⟨k, hk, hseqk.trans hs1b, hNs2.trans hs2b', ?_⟩⟩
    calc seq (k + 1) ≤ 9 / 7 * s1 := ht1b
      _ ≤ 9 / 7 * (729 / 343 / (8 * m)) := by gcongr
  · -- `a` never sets: the cascade over `E` is the cascade over `S`
    push Not at hex
    have hNs1 : seq N ≤ s1 :=
      seq_le_of_erase haE hpos hmv hs1l (k1 := 0) (K := N) (by rw [h0]; exact hs1a)
        (fun n _ _ => hex n) N (Nat.zero_le _) le_rfl
    exact ⟨seq N, hb N, lonely_of_notInWay hfix, Or.inl (hNs1.trans hs1b)⟩

#print axioms reach_four_cases

/-- **Four readings, least quotient below `24353/729`: a lonely instant in `R ∈ [1, (9/7)^7]`** [L].  The two cases of
`reach_four_cases` give `729/343` and `729/343 · 9/7 · 729/343 = (9/7)^7`.  `[PROVISIONAL: covering]` as there. -/
theorem reach_four_low {E : Finset ℝ} {m a : ℝ} (hm : 0 < m) (hlow : ∀ d ∈ E, m ≤ d) (hcard : E.card ≤ 4)
    (haE : a ∈ E) (ham : ∀ d ∈ E, a ≤ d) (hr : 729 * a < 24353 * m) :
    ∃ s, 1 / (8 * m) ≤ s ∧ s ≤ (9 / 7 : ℝ) ^ 7 / (8 * m) ∧ LonelyAt E s := by
  obtain ⟨s, hs0, hl, hcase⟩ := reach_four_cases hm hlow hcard haE ham hr
  refine ⟨s, hs0, ?_, hl⟩
  rcases hcase with h | ⟨k, -, -, h2, h3⟩
  · exact h.trans (div_le_div_of_nonneg_right (by norm_num) (by positivity))
  · calc s ≤ 729 / 343 * cascadeSeq E (1 / (8 * m)) (k + 1) := h2
      _ ≤ 729 / 343 * (9 / 7 * (729 / 343 / (8 * m))) := by gcongr
      _ = (9 / 7 : ℝ) ^ 7 / (8 * m) := by ring

#print axioms reach_four_low

/-! ## (4) Where `a` lands, and the five-disparity statements -/

/-- **For `ρ_a < 5` the one setting of `a` is on lap one and lands at `R = 9 m/a`** [L].  `a` sets at `n` with
`seq n ≤ 729/343/(8m)` (as in `reach_four_low`) and `a < 5 m`: then `lap a (seq n) = 1` and `seq (n+1) = 9/(8 a)`.
This is the displacement of the isolation of the `d_min` window by the reading `a`: the landing depends on `a` alone. -/
theorem landing_lap_one {E : Finset ℝ} {seq : ℕ → ℝ} {m a : ℝ} (hm : 0 < m) (hr5 : a < 5 * m) (hma : m ≤ a)
    (h0 : 1 / (8 * m) ≤ seq n) (hn : IsSetterAt E seq n a) (hb : seq n ≤ 729 / 343 / (8 * m)) :
    lap a (seq n) = 1 ∧ seq (n + 1) = 9 / (8 * a) := by
  have ha0 : 0 < a := lt_of_lt_of_le hm hma
  have hl1 : 1 ≤ lap a (seq n) := one_le_lap_of_bound hm hma h0 hn.2.1
  have hbd := abs_lt.mp (abs_sub_lap_lt hn.2.1)
  have hup : a * seq n < 15 / 8 - 1 / 8 := by
    have h1 : a * seq n ≤ a * (729 / 343 / (8 * m)) := mul_le_mul_of_nonneg_left hb ha0.le
    have e : a * (729 / 343 / (8 * m)) = (729 * a) / (2744 * m) := by field_simp; ring
    rw [e] at h1
    have : (729 * a) / (2744 * m) < 15 / 8 - 1 / 8 := by
      rw [div_lt_iff₀ (by positivity)]
      nlinarith
    linarith
  have hlap1 : lap a (seq n) = 1 := by
    have h2 : (lap a (seq n) : ℝ) < 2 := by linarith
    have h3 : lap a (seq n) < 2 := by exact_mod_cast h2
    omega
  refine ⟨hlap1, ?_⟩
  have hop := hn.2.2
  rw [hop, nextOpening_eq_lap hn.2.1, hlap1]
  push_cast
  field_simp
  ring

#print axioms landing_lap_one

/-- **Where the isolation lands, for `ρ_a < 5`** [L].  Either the lonely instant of `E` is at `R ≤ 729/343` (the position of the
lonely instant of `S`; `a` did not set), or `a` set once, on lap one, and the lonely instant is at
`R ≤ 729/343 · 9 m/a`, that is at most `729/343` times the landing `9 m/a` of `a` (`landing_lap_one`).  So the displacement of the
isolation of the `d_min` window `[1,7]` is a function of `a` alone, times the position of the lonely instant of `S` from the
landing.  `[PROVISIONAL: covering]` as `reach_four_cases`. -/
theorem reach_four_where {E : Finset ℝ} {m a : ℝ} (hm : 0 < m) (hlow : ∀ d ∈ E, m ≤ d) (hcard : E.card ≤ 4)
    (haE : a ∈ E) (ham : ∀ d ∈ E, a ≤ d) (hr5 : a < 5 * m) :
    ∃ s, 1 / (8 * m) ≤ s ∧ LonelyAt E s ∧
      (s ≤ 729 / 343 / (8 * m) ∨ s ≤ 729 / 343 * (9 / (8 * a))) := by
  have hr : 729 * a < 24353 * m := by linarith
  obtain ⟨s, hs0, hl, hcase⟩ := reach_four_cases hm hlow hcard haE ham hr
  refine ⟨s, hs0, hl, ?_⟩
  rcases hcase with h | ⟨k, hk, hkb, h2, -⟩
  · exact Or.inl h
  · right
    have hpos : ∀ d ∈ E, 0 < d := fun d hd => lt_of_lt_of_le hm (hlow d hd)
    have hmv := cascadeSeq_isMove E (1 / (8 * m))
    have hb : 1 / (8 * m) ≤ cascadeSeq E (1 / (8 * m)) k := by
      have := start_le_seq hpos hmv k
      rwa [cascadeSeq_zero] at this
    obtain ⟨-, hland⟩ := landing_lap_one hm hr5 (hlow a haE) hb hk hkb
    rw [hland] at h2
    exact h2

#print axioms reach_four_where

/-- **Five disparities, second smallest below `24353/729 · d_min`: a lonely instant in `R ∈ [1, 7]`** [L].  `ds` has at most
five members, least element `m`; `a` is the least of the other four, `729 a < 24353 m` (in particular `a < 5 m`).
`[PROVISIONAL: covering]` as `reach_four_low`; the displacement-frame step it serves is rule 1: the isolation of the `d_min`
window `[1,7]` is displaced by the one setting of `a` and the cascade shows where it lands. -/
theorem five_disparities_low {ds : Finset ℝ} {m a : ℝ} (hm : IsLeast (ds : Set ℝ) m) (hm0 : 0 < m)
    (hcard : ds.card ≤ 5) (haE : a ∈ ds.erase m) (ham : ∀ d ∈ ds.erase m, a ≤ d) (hr : 729 * a < 24353 * m) :
    ∃ s, 1 / (8 * m) ≤ s ∧ s ≤ 7 / (8 * m) ∧ LonelyAt ds s := by
  have hc : (ds.erase m).card ≤ 4 := by
    have := Finset.card_erase_of_mem hm.1
    omega
  have hlow : ∀ d ∈ ds.erase m, m ≤ d := fun d hd => hm.2 (Finset.mem_of_mem_erase hd)
  obtain ⟨s, h1, h2, h3⟩ := reach_four_low hm0 hlow hc haE ham hr
  refine add_dmin hm hm0 ⟨s, h1, h2.trans ?_, h3⟩
  exact div_le_div_of_nonneg_right (by norm_num) (by positivity)

#print axioms five_disparities_low

/-- **`LadderScale.FiveDisparitiesLowQuotient` holds** [L]: five disparities with the second smallest below `5 d_min` have a
lonely instant.  (The statement is tagged OWED in `LadderScale`; this theorem proves it.) -/
theorem fiveDisparitiesLowQuotient : FiveDisparitiesLowQuotient := by
  intro ds m a hm hm0 hcard haE ham h5
  obtain ⟨s, h1, -, h3⟩ := five_disparities_low hm hm0 hcard haE ham (by linarith)
  exact ⟨s, lt_of_lt_of_le (by positivity) h1, h3⟩

#print axioms fiveDisparitiesLowQuotient

/-- **Five disparities, second smallest below `57 d_min`** [L]: `LadderScale.five_quotient_bounded_of_low` with the low part
proved here.  Together with `LadderScale.five_disparities_of_ratio` (`5 m ≤ a < 57 m`, lonely instant in `R ∈ [1,7]`) this is the
quotient-bounded five-disparity statement. -/
theorem five_disparities_quotient_below_57 :
    ∀ (ds : Finset ℝ) (m a : ℝ), IsLeast (ds : Set ℝ) m → 0 < m → ds.card ≤ 5 → a ∈ ds.erase m →
      (∀ d ∈ ds.erase m, a ≤ d) → a < 57 * m → ∃ s, 0 < s ∧ LonelyAt ds s :=
  five_quotient_bounded_of_low fiveDisparitiesLowQuotient

#print axioms five_disparities_quotient_below_57

end FiveLow

end Fresh
