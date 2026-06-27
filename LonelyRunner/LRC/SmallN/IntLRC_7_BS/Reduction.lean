import LonelyRunner.LRC.SmallN.IntLRC_7_BS.Section5b
import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# n = 7 (Barajas–Serra) — §4 reduction + the discrete core `bs_discrete_q`

Source: `sources_barajas_serra_2008.txt`, lines 237–264.

`m = max ν₇(D)`, `N = 7^(m+1)`. With `gcd(D) = 1` we have `D₇(0), D₇(m) ≠ ∅`.

This file proves `bs_discrete_q` (the residue-band core used by `Main`) by the §4
dispatch:
- **Easy branch** — if every valuation level `j < m` has `≤ 3` elements, the
  proven `corollary3` produces the multiplier directly.
- **Hard branch** — some level `j < m` has `≥ 4` elements. With `|D| = 6` at most
  one level can be that large; the §4 reduction (divide by `7^{i₀}`) moves it to
  the bottom, leaving `|D₇(0)| ∈ {4,5}` for the §5/§6 analysis. **This is the lone
  remaining `sorry`.**
-/

open Finset

namespace IntLRC7BS

/-- **Discrete Barajas–Serra core, residue-band form (n = 7).** See `Main` for the
statement context. Proved by the §4 dispatch into `corollary3` (easy branch) and
the §5/§6 case analysis (hard branch, still `sorry`). -/
theorem bs_discrete_q
    (D : Fin 6 → ℕ) (hpos : ∀ i, 0 < D i)
    (hinj : Function.Injective D) (hgcd : Finset.univ.gcd D = 1) :
    ∃ (m : ℕ) (lam : ℤ), ∀ i,
      (7 ^ m : ℤ) ≤ (lam * (D i : ℤ)) % (7 ^ (m + 1) : ℤ) ∧
      (lam * (D i : ℤ)) % (7 ^ (m + 1) : ℤ) ≤ 6 * 7 ^ m := by
  classical
  set m : ℕ := Finset.univ.sup (fun i => padicValNat 7 (D i)) with hm
  set DZ : Finset ℤ := Finset.image (fun i => (D i : ℤ)) Finset.univ with hDZ
  -- `m` bounds every valuation, so no element is divisible by `7^(m+1)`
  have hmax : ∀ d ∈ DZ, ¬ (7 : ℤ) ^ (m + 1) ∣ d := by
    intro d hd
    rw [hDZ, Finset.mem_image] at hd
    obtain ⟨i, -, rfl⟩ := hd
    rw [show (7 : ℤ) ^ (m + 1) = ((7 ^ (m + 1) : ℕ) : ℤ) by push_cast; ring,
      Int.natCast_dvd_natCast, padicValNat_dvd_iff_le (hpos i).ne']
    have hle : padicValNat 7 (D i) ≤ m := by
      rw [hm]; exact Finset.le_sup (f := fun i => padicValNat 7 (D i)) (Finset.mem_univ i)
    omega
  -- §4 dispatch on whether some level below the top is large
  by_cases hsmall : ∀ j, j < m →
      (DZ.filter (fun d => (7 : ℤ) ^ j ∣ d ∧ ¬ (7 : ℤ) ^ (j + 1) ∣ d)).card ≤ 3
  · -- easy branch: Corollary 3 applies with `i₀ = m`
    obtain ⟨lam, _hlam, hband⟩ := corollary3 m DZ hmax hsmall
    exact ⟨m, lam, fun i =>
      hband (D i : ℤ) (by rw [hDZ]; exact Finset.mem_image_of_mem _ (Finset.mem_univ i))⟩
  · -- hard branch: some level `j₀ < m` has `≥ 4` elements.
    push_neg at hsmall
    obtain ⟨j₀, hj₀m, hj₀big⟩ := hsmall
    have hj₀card : 4 ≤ (DZ.filter (fun d => (7 : ℤ) ^ j₀ ∣ d ∧
        ¬ (7 : ℤ) ^ (j₀ + 1) ∣ d)).card := by omega
    -- Case split: j₀ = 0 (big level at bottom → §5/§6 directly)
    --         vs  j₀ > 0 (interior big level → §4 reduction → §5)
    rcases eq_or_ne j₀ 0 with rfl | hj₀ne
    · -- j₀ = 0: |D₇(0)| ≥ 4.
      -- Convert the DZ filter to a Fin 6 filter.
      set S := Finset.univ.filter (fun i : Fin 6 => ¬ (7 : ℤ) ∣ (D i : ℤ)) with hS_def
      have hS_card : 4 ≤ S.card := by
        have hDZ_inj : Set.InjOn (fun i : Fin 6 => (D i : ℤ)) (↑(Finset.univ : Finset (Fin 6))) :=
          fun a _ b _ h => hinj (Nat.cast_injective h)
        rw [show (7 : ℤ) ^ 0 = 1 from by norm_num,
          show (7 : ℤ) ^ (0 + 1) = 7 from by norm_num] at hj₀card
        simp only [one_dvd, true_and] at hj₀card
        have : (DZ.filter (fun d => ¬ (7 : ℤ) ∣ d)).card
            = (Finset.univ.filter (fun i : Fin 6 => ¬ (7 : ℤ) ∣ (D i : ℤ))).card := by
          rw [hDZ]
          rw [Finset.filter_image]
          exact Finset.card_image_of_injOn
            (Set.InjOn.mono (fun x hx => Finset.mem_filter.mp hx |>.1) hDZ_inj)
        linarith
      -- Extract 4 level-0 indices
      obtain ⟨T, hTS, hT4⟩ := Finset.exists_subset_card_eq hS_card
      set f : Fin 4 → Fin 6 := fun k => (T.orderIsoOfFin hT4 k).val
      have hf_inj : Function.Injective f :=
        fun a b h => (T.orderIsoOfFin hT4).injective (Subtype.val_injective h)
      have hf_mem : ∀ k, f k ∈ S := fun k => hTS ((T.orderIsoOfFin hT4 k).prop)
      have hf_ndvd : ∀ k, ¬ (7 : ℤ) ∣ (D (f k) : ℤ) := fun k => by
        have := hf_mem k; simp only [hS_def, Finset.mem_filter, Finset.mem_univ, true_and] at this
        exact this
      -- Apply four_band to the 4 level-0 elements → get multiplier
      set d4 : Fin 4 → ℤ := fun k => (D (f k) : ℤ)
      obtain ⟨lam, hlam_unit, hband4⟩ := four_band m hj₀m d4 hf_ndvd
      -- Extend to all 6 elements
      refine ⟨m, lam, fun i => ?_⟩
      by_cases hi : i ∈ S
      · -- Level-0 element: if in T (chosen 4), band follows from hband4.
        by_cases hiT : i ∈ T
        · have ⟨k, hk⟩ : ∃ k : Fin 4, (T.orderIsoOfFin hT4 k).val = i := by
            have := (T.orderIsoOfFin hT4).surjective ⟨i, hiT⟩
            exact ⟨this.choose, congr_arg Subtype.val this.choose_spec⟩
          have := hband4 k; simp only [d4, f, hk] at this; exact this
        · -- 5th level-0 element (|D₇(0)| ≥ 5): §6 (|A|=5)
          sorry
      · -- Higher-level element (7 ∣ D i)
        simp only [hS_def, Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hi
        by_cases him : (7 : ℤ) ^ m ∣ (D i : ℤ)
        · exact band_top m lam (D i : ℤ) hlam_unit him
            (hmax _ (by rw [hDZ]; exact Finset.mem_image_of_mem _ (Finset.mem_univ i)))
        · -- Interior element: needs BS eq (8) pre-multiplier (u₀ construction).
          -- The multiplier from four_band doesn't handle interior elements
          -- because the Λ₀ shift has zero slope on elements divisible by 7.
          -- Fixing this requires restructuring to compute u₀ · (1+7^{m-i₀})
          -- BEFORE calling four_band. Deferred.
          sorry
    · -- j₀ > 0: interior big level. §4 reduction divides by 7^{j₀},
      -- reducing to |D'₇(0)| = |D₇(j₀)| ≥ 4 with fewer total elements.
      sorry

end IntLRC7BS
