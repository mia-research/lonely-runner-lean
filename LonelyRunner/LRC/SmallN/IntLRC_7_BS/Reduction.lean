import LonelyRunner.LRC.SmallN.IntLRC_7_BS.PrimeFiltering
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
    · -- j₀ = 0: |D₇(0)| ≥ 4, i.e. ≥ 4 elements not divisible by 7.
      -- With |D| = 6, |D₇(0)| ∈ {4, 5, 6}. §5 handles 4, §6 handles 5.
      sorry
    · -- j₀ > 0: interior big level. §4 reduction divides by 7^{j₀},
      -- reducing to |D'₇(0)| = |D₇(j₀)| ≥ 4 with fewer total elements.
      sorry

end IntLRC7BS
