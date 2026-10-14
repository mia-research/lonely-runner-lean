import Mathlib
import Fresh.Framework
import Fresh.TwoScale
import Fresh.Boundaries
import Fresh.BlockLanding
import Fresh.BlockLanding2
import Fresh.LonelyCells
import Fresh.Carving

/-!
# The one-multiple integer case (Task AS; log E441 to E444, Gap 1)

Written 2026-10-09.  Imports Mathlib and the Fresh modules named in the task.  Nothing is imported from the existing
`LonelyRunner` repo.  Exact reals; disparities are integers (a commensurable population: test cases, NOT a reduction).

Statement studied.  `D'` a finite set of integers, `c` an integer: is there `t > 0` with `1/8 ≤ distInt (d t)` for all
`d ∈ D'` and for `8c`?  (`Cascade.LonelyAt (TwoScale.realSet D' {c}) t`.)

Results (each hypothesis is graded REQUIRED / NOT REQUIRED / UNDECIDED in the task report):
* `exists_clear_card_le_four`, `exists_lonely_realSet_of_card_le_four`, `one_multiple_card_le_three`: `|D'| ≤ 3`, every
  `c ≠ 0`, `D'` any nonzero integers.  `[PROVISIONAL: counting tool]` (pigeonhole on `j/N`, `N = 8P - 1`).
* `lonely_shift_of_windows`, `displaced_minus`, `displaced_plus`, `lonely_displaced_by_multiple`, `lonely_below_multiple`:
  the grid instant `(m - η)/8` displaced by the multiple, any `|D'|`, hypothesis `d ≤ 8c (r_d - 1)`.
* `lonely_half_displaced`: odd `D'`, `|d| ≤ 24c`, any `|D'|`.
* `ap7_lonely_iff`, `seven_fails`, `seven_fails_c1`: `D' = {1,…,7}` has no lonely instant for any `c`; the count bound is
  required.
* `audit_*`: literal counterexamples for the hypotheses of `TwoScale.explicit_instant`.

Provenance.  `Boundaries.unit_lonely`/`half_nbhd_lonely` and `TwoScale.residue_window`/`explicit_instant*` are the
framework's own (re-used by import).  Existing-repo counterparts read for the idea only (`GrandReturnN` totient law,
`Spec/DoorFlank`): nothing was copied.  The counting lemma is the classical `p = 8q+7` residue-count argument for the
`1/(2n)` bound, written here from scratch in `ℤ`; Dirichlet is Mathlib's `Real.exists_int_int_abs_mul_sub_le`.
-/

open Classical

namespace Fresh.OneMultiple

open Fresh

/-! ## Counting lemma -/

/-- Residues `y` of `x` mod `N` with `N < 8y` and `N < 8(N-y)` read at least `1/8` from every integer. -/
theorem clear_of_residue (x N : ℤ) (hN : 0 < N) (h1 : N < 8 * (x % N)) (h2 : N < 8 * (N - x % N)) :
    (1 / 8 : ℝ) ≤ distInt ((x : ℝ) / N) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hx : x = x % N + N * (x / N) := (Int.emod_add_mul_ediv x N).symm
  have e : (x : ℝ) / N = ((x % N : ℤ) : ℝ) / N + ((x / N : ℤ) : ℝ) := by
    have : (x : ℝ) = ((x % N : ℤ) : ℝ) + N * ((x / N : ℤ) : ℝ) := by exact_mod_cast hx
    rw [this]; field_simp
  rw [e, Cascade.distInt_add_int]
  have h1' : (N : ℝ) < 8 * ((x % N : ℤ) : ℝ) := by exact_mod_cast h1
  have h2' : (N : ℝ) < 8 * ((N : ℝ) - ((x % N : ℤ) : ℝ)) := by exact_mod_cast h2
  have := Localisation.clear_of_window (y := ((x % N : ℤ) : ℝ) / N) 0 (by
    rw [le_div_iff₀ hNr]; push_cast; linarith) (by
    rw [div_le_iff₀ hNr]; push_cast; linarith)
  simpa using this

#print axioms clear_of_residue

/-- The residues mod `N = 8q+7` read strictly within `1/8` of a lap line, other than `0`. -/
noncomputable def badRes (N q : ℤ) : Finset ℤ := Finset.Icc 1 q ∪ Finset.Icc (N - q) (N - 1)

theorem badRes_card (N q : ℤ) (hq : 0 ≤ q) : (badRes N q).card ≤ 2 * q.toNat := by
  unfold badRes
  refine (Finset.card_union_le _ _).trans ?_
  simp only [Int.card_Icc]
  omega

theorem coprime_of_dvd (s P : ℤ) (h : s ∣ P) : IsCoprime s (8 * P - 1) := by
  obtain ⟨R, hR⟩ := h
  exact ⟨8 * R, -1, by rw [hR]; ring⟩

/-- **Counting lemma** [L].  `[PROVISIONAL: counting tool]` supports only this statement: for at most four nonzero
integers there is a rational instant `j/N` (`N = 8q+7` coprime to all of them) at which each reads at least `1/8` from a
lap line.  Pigeonhole: each `s` sends the `N-1` nonzero residues injectively, so at most `2q` of them are near a lap line
for `s`; `4 * 2q = 8q < N - 1 = 8q + 6`. -/
theorem exists_clear_card_le_four (S : Finset ℤ) (h0 : ∀ s ∈ S, s ≠ 0) (hc : S.card ≤ 4) :
    ∃ t : ℝ, 0 < t ∧ ∀ s ∈ S, (1 / 8 : ℝ) ≤ distInt ((s : ℝ) * t) := by
  set P : ℤ := ∏ s ∈ S, |s| with hP
  have hPpos : 0 < P := Finset.prod_pos (fun s hs => abs_pos.mpr (h0 s hs))
  set N : ℤ := 8 * P - 1 with hN
  set q : ℤ := P - 1 with hq
  have hNpos : 0 < N := by omega
  have hNq : N = 8 * q + 7 := by omega
  have hcop : ∀ s ∈ S, IsCoprime s N := by
    intro s hs
    exact coprime_of_dvd s P ((dvd_abs s s).mpr dvd_rfl |>.trans (Finset.dvd_prod_of_mem _ hs))
  set T : Finset ℤ := Finset.Icc 1 (N - 1) with hT
  have hTcard : T.card = 8 * q.toNat + 6 := by
    simp only [hT, Int.card_Icc]; omega
  set Bad : ℤ → Finset ℤ := fun s => T.filter (fun j => (s * j) % N ∈ badRes N q) with hBad
  have hBadcard : ∀ s ∈ S, (Bad s).card ≤ 2 * q.toNat := by
    intro s hs
    refine le_trans (Finset.card_le_card_of_injOn (fun j => (s * j) % N) ?_ ?_) (badRes_card N q (by omega))
    · intro j hj
      simp only [hBad, Finset.coe_filter, Set.mem_setOf_eq] at hj
      exact hj.2
    · intro j hj j' hj' hjj
      simp only [hBad, hT, Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_Icc] at hj hj'
      have hd : N ∣ s * j - s * j' := (Int.ModEq.dvd hjj.symm)
      have : N ∣ s * (j - j') := by rw [mul_sub]; exact hd
      have := (hcop s hs).symm.dvd_of_dvd_mul_left this
      obtain ⟨k, hk⟩ := this
      have : k = 0 := by
        rcases lt_trichotomy k 0 with hk0 | hk0 | hk0
        · nlinarith [hj.1.1, hj.1.2, hj'.1.1, hj'.1.2]
        · exact hk0
        · nlinarith [hj.1.1, hj.1.2, hj'.1.1, hj'.1.2]
      subst this
      linarith
  have hex : ∃ j ∈ T, ∀ s ∈ S, j ∉ Bad s := by
    by_contra hcon
    push Not at hcon
    have hsub : T ⊆ S.biUnion Bad := by
      intro j hj
      obtain ⟨s, hs, hjs⟩ := hcon j hj
      exact Finset.mem_biUnion.mpr ⟨s, hs, hjs⟩
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_biUnion_le (s := S) (t := Bad)
    have h3 : ∑ s ∈ S, (Bad s).card ≤ ∑ s ∈ S, 2 * q.toNat := Finset.sum_le_sum hBadcard
    rw [Finset.sum_const, smul_eq_mul] at h3
    have h4 : S.card * (2 * q.toNat) ≤ 4 * (2 * q.toNat) := Nat.mul_le_mul_right _ hc
    omega
  obtain ⟨j, hjT, hjB⟩ := hex
  have hjT' := Finset.mem_Icc.mp hjT
  refine ⟨(j : ℝ) / N, by
    have : (0 : ℝ) < j := by exact_mod_cast hjT'.1
    have : (0 : ℝ) < N := by exact_mod_cast hNpos
    positivity, fun s hs => ?_⟩
  have e : (s : ℝ) * ((j : ℝ) / N) = ((s * j : ℤ) : ℝ) / N := by push_cast; ring
  rw [e]
  have hnb := hjB s hs
  simp only [hBad, Finset.mem_filter, not_and, badRes, Finset.mem_union, Finset.mem_Icc, not_or] at hnb
  have hmem := hnb hjT
  set y := (s * j) % N with hy
  have hy0 : 0 ≤ y := Int.emod_nonneg _ (by omega)
  have hyN : y < N := Int.emod_lt_of_pos _ hNpos
  have hy_ne : y ≠ 0 := by
    intro hy0'
    have hdv : N ∣ s * j := Int.dvd_of_emod_eq_zero hy0'
    have := (hcop s hs).symm.dvd_of_dvd_mul_left hdv
    have hle := Int.le_of_dvd (by omega) this
    omega
  apply clear_of_residue _ _ hNpos
  · omega
  · omega

#print axioms exists_clear_card_le_four

/-! ## The one-multiple statement for |D'| <= 3 (all c) -/

/-- **Lonely instant for at most four disparities, multiples of 8 included** [L].  Hypotheses: every element of `D'` and
of `C` is nonzero, and `|D'| + |C| ≤ 4`.  Nothing else: no positivity, no `8 ∤ d`, no ordering, no size bound, no gcd.
`[PROVISIONAL: counting tool]` (via `exists_clear_card_le_four`). -/
theorem exists_lonely_realSet_of_card_le_four (D' C : Finset ℤ) (hD : ∀ d ∈ D', d ≠ 0) (hC : ∀ c ∈ C, c ≠ 0)
    (hcard : D'.card + C.card ≤ 4) :
    ∃ t : ℝ, 0 < t ∧ Cascade.LonelyAt (TwoScale.realSet D' C) t := by
  obtain ⟨t, ht, hall⟩ := exists_clear_card_le_four (D' ∪ C.image (fun c => 8 * c))
    (by
      intro s hs
      rcases Finset.mem_union.mp hs with h | h
      · exact hD s h
      · obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp h
        have := hC c hc
        omega)
    (le_trans (Finset.card_union_le _ _) (le_trans (Nat.add_le_add_left Finset.card_image_le _) hcard))
  exact ⟨t, ht, (TwoScale.lonelyAt_realSet_iff D' C t).mpr hall⟩

#print axioms exists_lonely_realSet_of_card_le_four

/-- **The one-multiple integer case, `|D'| ≤ 3`, every `c`** [L].  `D'` a finite set of integers with no element `0`
(in particular any set with no multiple of 8), `|D'| ≤ 3`, `c ≠ 0`: some `t > 0` has `1/8 ≤ distInt (d t)` for all
`d ∈ D'` and `1/8 ≤ distInt (8 c t)`.  `[PROVISIONAL: counting tool]`. -/
theorem one_multiple_card_le_three (D' : Finset ℤ) (c : ℤ) (hc : c ≠ 0) (hD : ∀ d ∈ D', d ≠ 0)
    (hcard : D'.card ≤ 3) :
    ∃ t : ℝ, 0 < t ∧ (∀ d ∈ D', (1 / 8 : ℝ) ≤ distInt ((d : ℝ) * t)) ∧ (1 / 8 : ℝ) ≤ distInt (((8 * c : ℤ) : ℝ) * t) := by
  obtain ⟨t, ht, hl⟩ := exists_lonely_realSet_of_card_le_four D' {c} hD (by simpa using hc) (by rw [Finset.card_singleton]; omega)
  rw [TwoScale.lonelyAt_realSet_iff] at hl
  refine ⟨t, ht, fun d hd => hl d (Finset.mem_union_left _ hd), hl (8 * c) ?_⟩
  exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨c, Finset.mem_singleton_self c, rfl⟩)

#print axioms one_multiple_card_le_three

/-- `|D'| = 0` explicitly: `t = 1/(16 c)` puts the multiple at half a lap [L]. -/
theorem one_multiple_card_zero (c : ℤ) (hc : 0 < c) :
    (1 / 8 : ℝ) ≤ distInt (((8 * c : ℤ) : ℝ) * (1 / (16 * (c : ℝ)))) := by
  have hc' : (0 : ℝ) < c := by exact_mod_cast hc
  have e : ((8 * c : ℤ) : ℝ) * (1 / (16 * (c : ℝ))) = 1 / 2 := by push_cast; field_simp; ring
  rw [e]
  apply Localisation.clear_of_window 0 <;> norm_num

#print axioms one_multiple_card_zero

/-! ## The displacement frame: the grid instant `a/8` displaced by `x`, with the hypotheses of `TwoScale.explicit_instant`
re-examined one by one -/

/-- **Window `j = 0`, no side conditions** [L].  If `x` is such that every `d ∈ D'` has `1 - r_d ≤ d x ≤ 7 - r_d`
(`r_d = d a mod 8`) and `C` is clear at `x`, then `(a + x)/8` is lonely for `D' ∪ 8C`.  Here `x` is an arbitrary real of
either sign; `a` is an arbitrary integer; `D'` and `C` are arbitrary finite sets of integers.  This is the displacement
statement in its weakest form (`TwoScale.residue_window` with `j = 0`); every hypothesis of `explicit_instant` is a way
of satisfying its first line. -/
theorem lonely_shift_of_windows (D' C : Finset ℤ) (a : ℤ) (x : ℝ)
    (hD : ∀ d ∈ D', 1 - (TwoScale.res d a : ℝ) ≤ (d : ℝ) * x ∧ (d : ℝ) * x ≤ 7 - (TwoScale.res d a : ℝ))
    (hC : ∀ c ∈ C, (1 / 8 : ℝ) ≤ distInt ((c : ℝ) * x)) :
    Cascade.LonelyAt (TwoScale.realSet D' C) (((a : ℝ) + x) / 8) := by
  rw [TwoScale.lonely_iff_shift]
  refine ⟨fun d hd => ?_, hC⟩
  rw [TwoScale.residue_window]
  exact ⟨0, by push_cast; linarith [(hD d hd).1], by push_cast; linarith [(hD d hd).2]⟩

#print axioms lonely_shift_of_windows

/-- **Minus side, sharpened** [L].  `a` any integer, `η ≥ 0`, every `d ∈ D'` with `d ≥ 0` and `d η ≤ r_d - 1`
(`r_d = d a mod 8`), `C` clear at `η`: then `(a - η)/8` is lonely.  Compared with `TwoScale.explicit_instant_minus`
(hypothesis `2 ≤ r_d` and `d η ≤ 1`): the bound `d η ≤ 1` is replaced by `d η ≤ r_d - 1` (weaker, since `r_d ≥ 2`
there), and `2 ≤ r_d` is not a hypothesis at all (it follows from `0 ≤ d η ≤ r_d - 1` once `η > 0` and `d > 0`, and
`r_d = 1` is allowed at `η = 0`). -/
theorem displaced_minus (D' C : Finset ℤ) (a : ℤ) (η : ℝ) (hη : 0 ≤ η) (hd0 : ∀ d ∈ D', 0 ≤ d)
    (hsmall : ∀ d ∈ D', (d : ℝ) * η ≤ (TwoScale.res d a : ℝ) - 1)
    (hC : ∀ c ∈ C, (1 / 8 : ℝ) ≤ distInt ((c : ℝ) * η)) :
    Cascade.LonelyAt (TwoScale.realSet D' C) (((a : ℝ) + (-η)) / 8) := by
  apply lonely_shift_of_windows
  · intro d hd
    have h0 : (0 : ℝ) ≤ (d : ℝ) * η := mul_nonneg (by exact_mod_cast hd0 d hd) hη
    have h8 : (TwoScale.res d a : ℝ) ≤ 7 := by
      have := TwoScale.res_lt d a
      have : TwoScale.res d a ≤ 7 := by omega
      exact_mod_cast this
    have := hsmall d hd
    constructor <;> nlinarith
  · intro c hc
    rw [show (c : ℝ) * (-η) = -((c : ℝ) * η) by ring, Cascade.distInt_neg]
    exact hC c hc

#print axioms displaced_minus

/-- **Plus side, sharpened** [L].  `a` any integer with `1 ≤ r_d` for every `d ∈ D'`, `d ≥ 0`, `η ≥ 0`,
`d η ≤ 7 - r_d`, `C` clear at `η`: then `(a + η)/8` is lonely.  Compared with `TwoScale.explicit_instant_plus`
(`r_d ≠ 7` and `d η ≤ 1`): `d η ≤ 1` is replaced by `d η ≤ 7 - r_d`, and `r_d ≠ 7` is not a hypothesis (it is forced
by `d η ≤ 7 - r_d` once `η > 0`, `d > 0`: residue 7 allows no positive displacement). -/
theorem displaced_plus (D' C : Finset ℤ) (a : ℤ) (η : ℝ) (hη : 0 ≤ η) (hd0 : ∀ d ∈ D', 0 ≤ d)
    (hr1 : ∀ d ∈ D', 1 ≤ TwoScale.res d a)
    (hsmall : ∀ d ∈ D', (d : ℝ) * η ≤ 7 - (TwoScale.res d a : ℝ))
    (hC : ∀ c ∈ C, (1 / 8 : ℝ) ≤ distInt ((c : ℝ) * η)) :
    Cascade.LonelyAt (TwoScale.realSet D' C) (((a : ℝ) + η) / 8) := by
  apply lonely_shift_of_windows
  · intro d hd
    have h0 : (0 : ℝ) ≤ (d : ℝ) * η := mul_nonneg (by exact_mod_cast hd0 d hd) hη
    have h1 : (1 : ℝ) ≤ (TwoScale.res d a : ℝ) := by exact_mod_cast hr1 d hd
    have := hsmall d hd
    constructor <;> linarith
  · exact hC

#print axioms displaced_plus

/-- Periodicity [L]: for integer disparities, a lonely instant plus any integer is lonely. -/
theorem lonelyAt_add_int (D' C : Finset ℤ) (t : ℝ) (n : ℤ) (h : Cascade.LonelyAt (TwoScale.realSet D' C) t) :
    Cascade.LonelyAt (TwoScale.realSet D' C) (t + n) := by
  rw [TwoScale.lonelyAt_realSet_iff] at h ⊢
  intro d hd
  have e : (d : ℝ) * (t + n) = (d : ℝ) * t + ((d * n : ℤ) : ℝ) := by push_cast; ring
  rw [e, Cascade.distInt_add_int]
  exact h d hd

#print axioms lonelyAt_add_int

/-- Positivity is free: an instant lonely for integer disparities can be moved by whole laps to a positive one [L]. -/
theorem exists_pos_of_lonelyAt (D' C : Finset ℤ) (t : ℝ) (h : Cascade.LonelyAt (TwoScale.realSet D' C) t) :
    ∃ t' : ℝ, 0 < t' ∧ Cascade.LonelyAt (TwoScale.realSet D' C) t' := by
  refine ⟨t + ((⌈-t⌉ + 1 : ℤ) : ℝ), ?_, lonelyAt_add_int D' C t _ h⟩
  have := Int.le_ceil (-t)
  push_cast
  linarith

#print axioms exists_pos_of_lonelyAt

/-- Pigeonhole [PROVISIONAL: counting tool] supporting only `exists_missing_odd_class`: a set of at most three integers
misses one of the four odd residue classes mod 8. -/
theorem exists_missing_odd_class (D' : Finset ℤ) (hcard : D'.card ≤ 3) :
    ∃ m : ℤ, m % 2 = 1 ∧ 0 < m ∧ m < 8 ∧ ∀ d ∈ D', d % 8 ≠ m := by
  by_contra hcon
  push Not at hcon
  have hsub : ({1, 3, 5, 7} : Finset ℤ) ⊆ D'.image (fun d => d % 8) := by
    intro m hm
    have hm' : m = 1 ∨ m = 3 ∨ m = 5 ∨ m = 7 := by simpa using hm
    have hodd : m % 2 = 1 := by rcases hm' with rfl | rfl | rfl | rfl <;> norm_num
    obtain ⟨d, hd, hdm⟩ := hcon m hodd (by rcases hm' with rfl | rfl | rfl | rfl <;> norm_num)
      (by rcases hm' with rfl | rfl | rfl | rfl <;> norm_num)
    exact Finset.mem_image.mpr ⟨d, hd, hdm⟩
  have h1 := Finset.card_le_card hsub
  have h2 : (D'.image (fun d => d % 8)).card ≤ D'.card := Finset.card_image_le
  have h3 : ({1, 3, 5, 7} : Finset ℤ).card = 4 := by decide
  omega

#print axioms exists_missing_odd_class

/-- **The displacement theorem, one hypothesis** [L].  `D'` positive integers, `c > 0`, `m` ANY integer, and for every
`d ∈ D'` the single inequality `d ≤ 8c (r_d - 1)`, `r_d = d m mod 8`.  Then `t = (m - 1/(8c))/8` is lonely for
`D' ∪ {8c}`.  The multiple sits at `c η = 1/8` (its opening) with `η = 1/(8c)`; `d` is displaced by `d/(8c) ≤ r_d - 1`.
The inequality forces `r_d ≥ 2`, so it contains "`m` odd", "`d` misses the class of `m`" and "`8 ∤ d`" (for odd `m`:
`r_d ∈ {0,1}` iff `d ≡ 0` or `d ≡ m`); none is a separate hypothesis.  No bound on `|D'|`. -/
theorem lonely_displaced_by_multiple (D' : Finset ℤ) (c m : ℤ) (hc : 0 < c) (hd0 : ∀ d ∈ D', 0 < d)
    (hdc : ∀ d ∈ D', d ≤ 8 * c * (TwoScale.res d m - 1)) :
    Cascade.LonelyAt (TwoScale.realSet D' {c}) (((m : ℝ) + (-(1 / (8 * (c : ℝ))))) / 8) := by
  have hcR : (0 : ℝ) < c := by exact_mod_cast hc
  refine displaced_minus D' {c} m (1 / (8 * (c : ℝ))) (by positivity) (fun d hd => (hd0 d hd).le)
    (fun d hd => ?_) (fun c' hc' => ?_)
  · have h := hdc d hd
    have hR : (d : ℝ) ≤ 8 * c * ((TwoScale.res d m : ℝ) - 1) := by exact_mod_cast h
    rw [mul_one_div, div_le_iff₀ (by positivity)]
    linarith
  · rw [Finset.mem_singleton] at hc'
    subst hc'
    rw [show (c' : ℝ) * (1 / (8 * (c' : ℝ))) = 1 / 8 by field_simp]
    have := Cascade.distInt_eighth_add_int 0
    simpa using this.ge

#print axioms lonely_displaced_by_multiple

/-- The residue is at least `2` when `m` is odd, `8 ∤ d` and `d` misses the class of `m` [L]. -/
theorem res_ge_two (d m : ℤ) (hm : m % 2 = 1) (hd8 : d % 8 ≠ 0) (hmiss : d % 8 ≠ m % 8) : 2 ≤ TwoScale.res d m := by
  have h1 : TwoScale.res d m ≠ 1 := TwoScale.residue_avoid_one d m hm hmiss
  have h0 : TwoScale.res d m ≠ 0 := TwoScale.residue_ne_zero d m hm hd8
  have := TwoScale.res_nonneg d m
  omega

#print axioms res_ge_two

/-- **Below the multiple, the form of `TwoScale.explicit_instant`** [L]: `D'` positive, none a multiple of 8, missing the odd
class `m`, none above `8c`.  Then `(m - 1/(8c))/8` is lonely and a positive lonely instant exists. -/
theorem lonely_below_multiple (D' : Finset ℤ) (c m : ℤ) (hc : 0 < c) (hm : m % 2 = 1)
    (hd0 : ∀ d ∈ D', 0 < d) (hd8 : ∀ d ∈ D', d % 8 ≠ 0) (hdc : ∀ d ∈ D', d ≤ 8 * c)
    (hmiss : ∀ d ∈ D', d % 8 ≠ m % 8) :
    Cascade.LonelyAt (TwoScale.realSet D' {c}) (((m : ℝ) + (-(1 / (8 * (c : ℝ))))) / 8) := by
  apply lonely_displaced_by_multiple D' c m hc hd0
  intro d hd
  have h2 := res_ge_two d m hm (hd8 d hd) (hmiss d hd)
  have := hdc d hd
  nlinarith

#print axioms lonely_below_multiple

/-- **Second proof of the `|D'| ≤ 3` case when the multiple is the largest disparity** [L].  `[PROVISIONAL: counting tool]`
(only through `exists_missing_odd_class`).  No counting is used on the instants. -/
theorem one_multiple_card_le_three_below (D' : Finset ℤ) (c : ℤ) (hc : 0 < c) (hcard : D'.card ≤ 3)
    (hd0 : ∀ d ∈ D', 0 < d) (hd8 : ∀ d ∈ D', d % 8 ≠ 0) (hdc : ∀ d ∈ D', d ≤ 8 * c) :
    ∃ t : ℝ, 0 < t ∧ Cascade.LonelyAt (TwoScale.realSet D' {c}) t := by
  obtain ⟨m, hm, hm0, hm8, hmiss⟩ := exists_missing_odd_class D' hcard
  have hl := lonely_below_multiple D' c m hc hm hd0 hd8 hdc
    (fun d hd => by have := hmiss d hd; omega)
  exact exists_pos_of_lonelyAt D' {c} _ hl

#print axioms one_multiple_card_le_three_below

/-! ## Hypothesis audit of `TwoScale.explicit_instant`: exact counterexamples when a hypothesis is dropped

Each certificate is a literal pair (set, instant) with a nearby integer; `norm_num` closes the arithmetic. -/

/-- A disparity `d ∈ D'` within `< 1/8` of an integer at `t` blocks `t`. -/
theorem not_lonely_of_near (D' C : Finset ℤ) (d : ℤ) (hd : d ∈ D') (t : ℝ) (n : ℤ)
    (h : |(d : ℝ) * t - n| < 1 / 8) : ¬ Cascade.LonelyAt (TwoScale.realSet D' C) t := by
  intro hl
  rw [TwoScale.lonelyAt_realSet_iff] at hl
  have h1 := hl d (Finset.mem_union_left _ hd)
  have h2 := Cascade.distInt_le ((d : ℝ) * t) n
  linarith

/-- (hmiss dropped) `D' = {1}`, `m = 1`, `η = 1/2`, `C = ∅`: both instants `(m-η)/8 = 1/16` and `(7+η)/8 = 15/16` are blocked. -/
theorem audit_hmiss :
    ¬ Cascade.LonelyAt (TwoScale.realSet {1} ∅) ((((1 : ℤ) : ℝ) - 1 / 2) / 8) ∧
    ¬ Cascade.LonelyAt (TwoScale.realSet {1} ∅) ((((8 - 1 : ℤ) : ℝ) + 1 / 2) / 8) := by
  constructor
  · refine not_lonely_of_near {1} ∅ 1 (by simp) _ 0 ?_
    norm_num [abs_of_pos]
  · refine not_lonely_of_near {1} ∅ 1 (by simp) _ 1 ?_
    norm_num [abs_of_neg]

/-- (hsmall dropped, `d η ≤ 1`) `D' = {2}`, `m = 1`, `η = 3/4` (`2 % 8 ≠ 1`, `C = ∅`): `(1 - 3/4)/8 = 1/32` and
`(7 + 3/4)/8 = 31/32` are blocked, because `d η = 3/2 > 1`. -/
theorem audit_hsmall :
    ¬ Cascade.LonelyAt (TwoScale.realSet {2} ∅) ((((1 : ℤ) : ℝ) - 3 / 4) / 8) ∧
    ¬ Cascade.LonelyAt (TwoScale.realSet {2} ∅) ((((8 - 1 : ℤ) : ℝ) + 3 / 4) / 8) := by
  constructor
  · refine not_lonely_of_near {2} ∅ 2 (by simp) _ 0 ?_
    norm_num [abs_of_pos]
  · refine not_lonely_of_near {2} ∅ 2 (by simp) _ 2 ?_
    norm_num [abs_of_neg]

/-- (`d ≤ 8c` dropped, i.e. `d η ≤ r_d - 1` with `η = 1/(8c)`) `D' = {17}`, `c = 1`, `m = 3` (`17 % 8 = 1 ≠ 3`):
the instant `(3 - 1/8)/8 = 23/64` is blocked: `17 · 23/64 = 391/64` is `7/64 < 1/8` from `6`. -/
theorem audit_below_multiple :
    ¬ Cascade.LonelyAt (TwoScale.realSet {17} {1}) ((((3 : ℤ) : ℝ) - 1 / (8 * ((1 : ℤ) : ℝ))) / 8) := by
  refine not_lonely_of_near {17} {1} 17 (by simp) _ 6 ?_
  norm_num [abs_of_pos]

/-- (`m` odd dropped) `D' = {4}`, `m = 2`, `η = 1/8` (`4 % 8 ≠ 2`, `4 η ≤ 1`, `C = ∅`): `(2 - 1/8)/8` is blocked. -/
theorem audit_m_odd :
    ¬ Cascade.LonelyAt (TwoScale.realSet {4} ∅) ((((2 : ℤ) : ℝ) - 1 / 8) / 8) := by
  refine not_lonely_of_near {4} ∅ 4 (by simp) _ 1 ?_
  norm_num [abs_of_neg]

/-- (`0 < d` dropped) `D' = {-1}`, `m = 1`, `η = 1/2` (`(-1) % 8 = 7 ≠ 1`, `d η ≤ 1`, `C = ∅`): `1/16` is blocked. -/
theorem audit_d_pos :
    ¬ Cascade.LonelyAt (TwoScale.realSet {-1} ∅) ((((1 : ℤ) : ℝ) - 1 / 2) / 8) := by
  refine not_lonely_of_near {-1} ∅ (-1) (by simp) _ 0 ?_
  norm_num [abs_of_neg]

/-- (`8 ∤ d` dropped) `D' = {8}`, `m = 1`, `η = 1/16` (`8 % 8 = 0 ≠ 1`, `8 η ≤ 1`, `C = ∅`): `(1 - 1/16)/8` is blocked. -/
theorem audit_d_not_mult8 :
    ¬ Cascade.LonelyAt (TwoScale.realSet {8} ∅) ((((1 : ℤ) : ℝ) - 1 / 16) / 8) := by
  refine not_lonely_of_near {8} ∅ 8 (by simp) _ 1 ?_
  norm_num [abs_of_neg]

/-! ## `|D'| = 7`: the statement fails (the `n = 9` situation) -/

theorem exists_k7 (j : ℤ) (hj : j % 2 = 1) : ∃ k : ℤ, 1 ≤ k ∧ k ≤ 7 ∧ (k * j) % 8 = 7 := by
  have : j % 8 = 1 ∨ j % 8 = 3 ∨ j % 8 = 5 ∨ j % 8 = 7 := by omega
  rcases this with h | h | h | h
  · exact ⟨7, by norm_num, by norm_num, by omega⟩
  · exact ⟨5, by norm_num, by norm_num, by omega⟩
  · exact ⟨3, by norm_num, by norm_num, by omega⟩
  · exact ⟨1, by norm_num, by norm_num, by omega⟩

theorem exists_k1 (j : ℤ) (hj : j % 2 = 1) : ∃ k : ℤ, 1 ≤ k ∧ k ≤ 7 ∧ (k * j) % 8 = 1 := by
  have : j % 8 = 1 ∨ j % 8 = 3 ∨ j % 8 = 5 ∨ j % 8 = 7 := by omega
  rcases this with h | h | h | h
  · exact ⟨1, by norm_num, by norm_num, by omega⟩
  · exact ⟨3, by norm_num, by norm_num, by omega⟩
  · exact ⟨5, by norm_num, by norm_num, by omega⟩
  · exact ⟨7, by norm_num, by norm_num, by omega⟩

/-- **The lonely set of `{1,…,7}` lies on the grid** [L].  If `1/8 ≤ distInt (k t)` for `k = 1,…,7` then `8 t` is an odd
integer.  Proof: Dirichlet (`Real.exists_int_int_abs_mul_sub_le`, `n = 8`) gives some `k ≤ 8` with `‖k t‖ ≤ 1/9 < 1/8`, so
`k = 8`: `8 t = j + δ`, `|δ| ≤ 1/9`.  `j` even is blocked by `k = 4` (`4t = j/2 + δ/2`); `j` odd and `δ > 0` is blocked by
the `k` with `k j ≡ 7 (8)` (it reads `(1 - kδ)/8 < 1/8`); `δ < 0` by the `k` with `k j ≡ 1 (8)` (it reads
`(1 + kδ)/8 < 1/8`).  [PROVISIONAL: counting tool] Dirichlet's pigeonhole supports only this statement. -/
theorem ap7_lonely_imp (t : ℝ) (h : ∀ k : ℤ, 1 ≤ k → k ≤ 7 → (1 / 8 : ℝ) ≤ distInt ((k : ℝ) * t)) :
    ∃ j : ℤ, 8 * t = j ∧ j % 2 = 1 := by
  obtain ⟨j, k, hk0, hk8, hjk⟩ := Real.exists_int_int_abs_mul_sub_le t (n := 8) (by norm_num)
  have hk8' : k ≤ 8 := by exact_mod_cast hk8
  have hjk' : |(k : ℝ) * t - j| ≤ 1 / 9 := by
    have : (1 : ℝ) / (((8 : ℕ) : ℝ) + 1) = 1 / 9 := by norm_num
    rw [this] at hjk; exact hjk
  have hk : k = 8 := by
    by_contra hne
    have h1 := h k hk0 (by omega)
    have h2 := Cascade.distInt_le ((k : ℝ) * t) j
    linarith
  subst hk
  have hδ : |8 * t - j| ≤ 1 / 9 := by push_cast at hjk'; exact hjk'
  obtain ⟨hδ1, hδ2⟩ := abs_le.mp hδ
  have hodd : j % 2 = 1 := by
    by_contra hev
    obtain ⟨i, hi⟩ : ∃ i, j = 2 * i := ⟨j / 2, by omega⟩
    have h4 := h 4 (by norm_num) (by norm_num)
    have h5 := Cascade.distInt_le (((4 : ℤ) : ℝ) * t) i
    have e : ((4 : ℤ) : ℝ) * t - i = (8 * t - j) / 2 := by
      rw [hi]; push_cast; ring
    rw [e, abs_div] at h5
    have : |(8 * t - (j : ℝ))| / |(2 : ℝ)| ≤ 1 / 18 := by
      rw [abs_of_pos (by norm_num : (0 : ℝ) < 2)]; linarith
    linarith
  refine ⟨j, ?_, hodd⟩
  by_contra hne
  have hδne : 8 * t - (j : ℝ) ≠ 0 := fun h0 => hne (by linarith)
  rcases lt_or_gt_of_ne hδne with hneg | hpos
  · -- δ < 0 : the k with k j ≡ 1 mod 8
    obtain ⟨k, hk1, hk7, hkj⟩ := exists_k1 j hodd
    have hw := Int.emod_add_mul_ediv (k * j) 8
    rw [hkj] at hw
    have hkR : (k : ℝ) ≤ 7 := by exact_mod_cast hk7
    have hk1R : (1 : ℝ) ≤ k := by exact_mod_cast hk1
    have hwR : ((k : ℝ) * j) = 1 + 8 * (((k * j) / 8 : ℤ) : ℝ) := by
      have : ((k * j : ℤ) : ℝ) = 1 + 8 * (((k * j) / 8 : ℤ) : ℝ) := by exact_mod_cast hw.symm
      push_cast at this ⊢; linarith
    have h5 := Cascade.distInt_le ((k : ℝ) * t) ((k * j) / 8)
    have e : (k : ℝ) * t - (((k * j) / 8 : ℤ) : ℝ) = (1 + k * (8 * t - j)) / 8 := by
      linarith
    rw [e] at h5
    have hpos' : 0 < 1 + (k : ℝ) * (8 * t - j) := by nlinarith
    have hlt : 1 + (k : ℝ) * (8 * t - j) < 1 := by nlinarith
    rw [abs_of_pos (by positivity)] at h5
    have := h k hk1 hk7
    linarith
  · -- δ > 0 : the k with k j ≡ 7 mod 8
    obtain ⟨k, hk1, hk7, hkj⟩ := exists_k7 j hodd
    have hw := Int.emod_add_mul_ediv (k * j) 8
    rw [hkj] at hw
    have hkR : (k : ℝ) ≤ 7 := by exact_mod_cast hk7
    have hk1R : (1 : ℝ) ≤ k := by exact_mod_cast hk1
    have hwR : ((k : ℝ) * j) = 7 + 8 * (((k * j) / 8 : ℤ) : ℝ) := by
      have : ((k * j : ℤ) : ℝ) = 7 + 8 * (((k * j) / 8 : ℤ) : ℝ) := by exact_mod_cast hw.symm
      push_cast at this ⊢; linarith
    have h5 := Cascade.distInt_le ((k : ℝ) * t) ((k * j) / 8 + 1)
    have e : (k : ℝ) * t - ((((k * j) / 8 + 1 : ℤ)) : ℝ) = (k * (8 * t - j) - 1) / 8 := by
      push_cast; linarith
    rw [e] at h5
    have hlt : (k : ℝ) * (8 * t - j) < 1 := by nlinarith
    have hpos' : 0 < (k : ℝ) * (8 * t - j) := by positivity
    rw [abs_of_neg (by linarith : ((k : ℝ) * (8 * t - j) - 1) / 8 < 0)] at h5
    have := h k hk1 hk7
    linarith

#print axioms ap7_lonely_imp

/-- **Lonely set of `{1,…,7}`, exactly** [L]: `‖k t‖ ≥ 1/8` for `k = 1..7` iff `8 t` is an odd integer (the converse is
`Boundaries.unit_lonely`).  Every lonely instant of the AP is a grid touch point. -/
theorem ap7_lonely_iff (t : ℝ) :
    (∀ k : ℤ, 1 ≤ k → k ≤ 7 → (1 / 8 : ℝ) ≤ distInt ((k : ℝ) * t)) ↔ ∃ j : ℤ, 8 * t = j ∧ j % 2 = 1 := by
  constructor
  · exact ap7_lonely_imp t
  · rintro ⟨j, hj, hodd⟩ k hk1 hk7
    have ht : t = (j : ℝ) / 8 := by linarith
    rw [ht]
    apply Boundaries.unit_lonely k j
    · intro h8
      have := Int.le_of_dvd (by omega) h8
      omega
    · exact Int.odd_iff.mpr hodd

#print axioms ap7_lonely_iff

/-- **`|D'| = 7` fails: the count bound `|D'| ≤ 6` is required** [L].  For `D' = {1,…,7}` (seven positive integers, none a
multiple of 8) and EVERY integer `c`, no real `t` (positive or not) is lonely for `D' ∪ {8c}`.  Why: the lonely set of
`D'` is the set of odd grid points `j/8` (`ap7_lonely_iff`), and at every one of them the multiple reads `8 c · j/8 = c j`,
a whole lap, so the multiple stands on a lap line: the grid isolation is not displaced anywhere by the multiple, because
`D'` contains all four odd residue classes mod 8, so no residue is free of the one-sided blocks (residue 1 on the minus
side, residue 7 on the plus side). -/
theorem seven_fails (c : ℤ) : ¬ ∃ t : ℝ, Cascade.LonelyAt (TwoScale.realSet (Finset.Icc (1 : ℤ) 7) {c}) t := by
  rintro ⟨t, hl⟩
  rw [TwoScale.lonelyAt_realSet_iff] at hl
  obtain ⟨j, hj, hodd⟩ := ap7_lonely_imp t (fun k hk1 hk7 =>
    hl k (Finset.mem_union_left _ (Finset.mem_Icc.mpr ⟨hk1, hk7⟩)))
  have h8 := hl (8 * c) (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨c, Finset.mem_singleton_self c, rfl⟩))
  have e : ((8 * c : ℤ) : ℝ) * t = ((c * j : ℤ) : ℝ) := by push_cast; rw [show (8 : ℝ) * c * t = c * (8 * t) by ring, hj]
  rw [e, Localisation.distInt_intCast] at h8
  norm_num at h8

#print axioms seven_fails

/-- The literal instance: `D' = {1,2,3,4,5,6,7}`, `c = 1` (the AP `1,…,8`). -/
theorem seven_fails_c1 : ¬ ∃ t : ℝ, Cascade.LonelyAt (TwoScale.realSet {1, 2, 3, 4, 5, 6, 7} {1}) t := by
  have : ({1, 2, 3, 4, 5, 6, 7} : Finset ℤ) = Finset.Icc (1 : ℤ) 7 := by decide
  rw [this]
  exact seven_fails 1

#print axioms seven_fails_c1

#print axioms not_lonely_of_near
#print axioms audit_hmiss
#print axioms audit_hsmall
#print axioms audit_below_multiple
#print axioms audit_m_odd
#print axioms audit_d_pos
#print axioms audit_d_not_mult8

/-- (`hsmall` is sufficient, not necessary, for the instant) `D' = {33}`, `c = 1`, `m = 3`: `33 > 8c (r_d - 1) = 16`
(`r_d = 99 % 8 = 3`), so the window `j = 0` does not contain `d η`, yet `(3 - 1/8)/8 = 23/64` is lonely: `d η = 33/8`
lies in the window `j = 1`.  So the bound `d η ≤ 1` of `explicit_instant` is not required for the conclusion about this
instant; it is a sufficient condition (the exact condition is `TwoScale.residue_window`, all `j`). -/
theorem audit_hsmall_not_necessary :
    Cascade.LonelyAt (TwoScale.realSet {33} {1}) (23 / 64) := by
  rw [TwoScale.lonelyAt_realSet_iff]
  intro d hd
  simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_image] at hd
  rcases hd with rfl | ⟨c, rfl, rfl⟩
  · apply Localisation.clear_of_window 11 <;> norm_num
  · apply Localisation.clear_of_window 2 <;> norm_num

#print axioms audit_hsmall_not_necessary

/-- (`c ≠ 0` required) with `0 ∈ C` the multiple `8·0 = 0` reads `0` at every instant. -/
theorem audit_c_zero (D' C : Finset ℤ) (h : (0 : ℤ) ∈ C) (t : ℝ) :
    ¬ Cascade.LonelyAt (TwoScale.realSet D' C) t := by
  intro hl
  rw [TwoScale.lonelyAt_realSet_iff] at hl
  have := hl (8 * 0) (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨0, h, rfl⟩))
  simp [distInt] at this
  norm_num at this

/-- (`d ≠ 0` required) with `0 ∈ D'` the disparity `0` reads `0` at every instant. -/
theorem audit_d_zero (D' C : Finset ℤ) (h : (0 : ℤ) ∈ D') (t : ℝ) :
    ¬ Cascade.LonelyAt (TwoScale.realSet D' C) t := by
  intro hl
  rw [TwoScale.lonelyAt_realSet_iff] at hl
  have := hl 0 (Finset.mem_union_left _ h)
  simp [distInt] at this
  norm_num at this

#print axioms audit_c_zero
#print axioms audit_d_zero

/-- **Second displacement family, odd `D'`, no bound on `|D'|`** [L].  If every `d ∈ D'` is odd with `|d| ≤ 24 c` (`c > 0`),
then `t = 1/2 + 1/(64 c)` is lonely for `D' ∪ {8c}`: odd disparities read `1/2` at `t = 1/2` and stay clear for
`|ε| |d| ≤ 3/8` (`Boundaries.half_nbhd_lonely`); the multiple reads `c·64⁻¹c⁻¹·8 = 1/8`, its opening. -/
theorem lonely_half_displaced (D' : Finset ℤ) (c : ℤ) (hc : 0 < c) (hodd : ∀ d ∈ D', Odd d)
    (hdc : ∀ d ∈ D', |d| ≤ 24 * c) :
    Cascade.LonelyAt (TwoScale.realSet D' {c}) (1 / 2 + 1 / (64 * (c : ℝ))) := by
  have hcR : (0 : ℝ) < c := by exact_mod_cast hc
  rw [TwoScale.lonelyAt_realSet_iff]
  intro d hd
  simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_image] at hd
  rcases hd with hd | ⟨c', hc', hd'⟩
  · apply Boundaries.half_nbhd_lonely d (hodd d hd)
    rw [abs_of_pos (by positivity : (0 : ℝ) < 1 / (64 * (c : ℝ)))]
    have h1 : |(d : ℝ)| ≤ 24 * c := by exact_mod_cast hdc d hd
    rw [one_div, inv_mul_le_iff₀ (by positivity)]
    linarith
  · rw [← hd', hc']
    have e : ((8 * c : ℤ) : ℝ) * (1 / 2 + 1 / (64 * (c : ℝ))) = ((4 * c : ℤ) : ℝ) + 1 / 8 := by
      push_cast; field_simp; ring
    rw [e, add_comm, Cascade.distInt_eighth_add_int]

#print axioms lonely_half_displaced

