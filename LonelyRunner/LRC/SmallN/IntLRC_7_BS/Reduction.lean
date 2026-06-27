import LonelyRunner.LRC.SmallN.IntLRC_7_BS.Section5b
import LonelyRunner.LRC.SmallN.IntLRC_7_BS.Section5c
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
      -- Case split: does an interior element (7∣d, ¬7^m∣d) exist?
      -- If no: four_band on d4 directly; non-level-0 = level-m → band_top.
      -- If yes: pre-multiplier from exists_pre_congr; four_band on pre·d4.
      by_cases hnointerior : ∀ i : Fin 6, i ∉ S → (7 : ℤ) ^ m ∣ (D i : ℤ)
      · -- No interior: all non-level-0 are level-m
        set d4 : Fin 4 → ℤ := fun k => (D (f k) : ℤ)
        obtain ⟨lam, hlam_unit, _, _, hband4⟩ := four_band m hj₀m d4 hf_ndvd
        refine ⟨m, lam, fun i => ?_⟩
        by_cases hi : i ∈ S
        · by_cases hiT : i ∈ T
          · have ⟨k, hk⟩ : ∃ k : Fin 4, (T.orderIsoOfFin hT4 k).val = i := by
              have := (T.orderIsoOfFin hT4).surjective ⟨i, hiT⟩
              exact ⟨this.choose, congr_arg Subtype.val this.choose_spec⟩
            have := hband4 k; simp only [d4, f, hk] at this; exact this
          · sorry -- 5th level-0 element: §6
        · exact band_top m lam (D i : ℤ) hlam_unit (hnointerior i hi)
            (hmax _ (by rw [hDZ]; exact Finset.mem_image_of_mem _ (Finset.mem_univ i)))
      · -- Interior element exists: pre-multiplier construction (BS eq 8)
        push_neg at hnointerior
        obtain ⟨e_int, he_notS, he_ndvd⟩ := hnointerior
        have h7_eint : (7 : ℤ) ∣ (D e_int : ℤ) := by
          simp only [hS_def, Finset.mem_filter, Finset.mem_univ, true_and] at he_notS
          exact not_not.mp he_notS
        have h7_nat : 7 ∣ D e_int := by exact_mod_cast h7_eint
        have hndvd_nat : ¬ 7 ^ m ∣ D e_int := by exact_mod_cast he_ndvd
        obtain ⟨pre, i₀, hpre_unit, hi₀_1, hi₀_m, hpre_congr⟩ :=
          exists_pre_congr m (D e_int) (hpos e_int) h7_nat hndvd_nat
        -- Call four_band on pre · d4
        set d4 : Fin 4 → ℤ := fun k => pre * (D (f k) : ℤ)
        have hd4_ndvd : ∀ k, ¬ (7 : ℤ) ∣ d4 k := fun k => by
          simp only [d4]; exact mt (Prime.dvd_mul (by norm_num : Prime (7 : ℤ)) |>.mp)
            (by simp [hpre_unit, hf_ndvd k])
        obtain ⟨lam', hlam'_unit, _, ⟨j_step, hj1, hj5, hcongr'⟩, hband4⟩ :=
          four_band m hj₀m d4 hd4_ndvd
        set lam := lam' * pre
        have hlam_unit : ¬ (7 : ℤ) ∣ lam := by
          exact mt (Prime.dvd_mul (by norm_num : Prime (7 : ℤ)) |>.mp)
            (by simp [hlam'_unit, hpre_unit])
        refine ⟨m, lam, fun i => ?_⟩
        by_cases hi : i ∈ S
        · by_cases hiT : i ∈ T
          · have ⟨k, hk⟩ : ∃ k : Fin 4, (T.orderIsoOfFin hT4 k).val = i := by
              have := (T.orderIsoOfFin hT4).surjective ⟨i, hiT⟩
              exact ⟨this.choose, congr_arg Subtype.val this.choose_spec⟩
            have := hband4 k; simp only [d4, f, hk, show lam = lam' * pre from rfl,
              show lam' * pre * (D ((T.orderIsoOfFin hT4 k).val) : ℤ) =
                lam' * (pre * (D ((T.orderIsoOfFin hT4 k).val) : ℤ)) from by ring] at this ⊢
            exact this
          · sorry -- 5th level-0 element: §6
        · -- Non-level-0 element
          simp only [hS_def, Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hi
          by_cases hi_eq : i = e_int
          · -- THE interior element: use pre-multiplier + interior_in_band
            subst hi_eq
            obtain ⟨c', hc'⟩ := hcongr'
            obtain ⟨w, hw⟩ := hpre_congr
            have hrw : lam * (D e_int : ℤ) =
                (j_step : ℤ) * pre * (D e_int : ℤ) +
                (7 : ℤ) ^ (m + 1) * (c' * pre * (D e_int : ℤ)) := by
              show lam' * pre * (D e_int : ℤ) = _
              rw [show lam' = (j_step : ℤ) + (7 : ℤ) ^ m * c' from by linarith]; ring
            have hmod_eq : (lam * (D e_int : ℤ)) % (7 : ℤ) ^ (m + 1) =
                ((j_step : ℤ) * ((7 : ℤ) ^ i₀ + (7 : ℤ) ^ m)) % (7 : ℤ) ^ (m + 1) := by
              rw [hrw, Int.add_mul_emod_self_left]
              congr 1
              have : (j_step : ℤ) * pre * (D e_int : ℤ) -
                  (j_step : ℤ) * ((7 : ℤ) ^ i₀ + (7 : ℤ) ^ m) =
                  (j_step : ℤ) * (pre * (D e_int : ℤ) -
                    ((7 : ℤ) ^ i₀ + (7 : ℤ) ^ m)) := by ring
              have hdvd : (7 : ℤ) ^ (m + 1) ∣ ((j_step : ℤ) * pre * (D e_int : ℤ) -
                  (j_step : ℤ) * ((7 : ℤ) ^ i₀ + (7 : ℤ) ^ m)) := by
                rw [this]; exact dvd_mul_of_dvd_right hpre_congr _
              exact (Int.emod_eq_emod_iff_emod_sub_eq_zero _ _ _).mpr
                (Int.dvd_emod_sub_self hdvd |>.symm ▸ Int.zero_emod _)
            obtain ⟨hlo, hhi, hlt, hnn⟩ := interior_in_band j_step i₀ m hj1 hj5 hi₀_1 hi₀_m
            rw [hmod_eq, Int.emod_eq_of_lt hnn hlt]
            exact ⟨hlo, hhi⟩
          · -- Not e_int: must be level-m → band_top
            have him : (7 : ℤ) ^ m ∣ (D i : ℤ) := by
              by_contra him'
              -- i and e_int both in Sᶜ with ¬7^m∣. The m-achieving
              -- element is a third element of Sᶜ. But |Sᶜ| ≤ 2.
              haveI : Fact (Nat.Prime 7) := ⟨by decide⟩
              have hSc_le : (Finset.univ.filter (fun j : Fin 6 =>
                  j ∉ S)).card ≤ 2 := by
                have := Finset.filter_card_add_filter_neg_card_eq_card
                  (s := Finset.univ) (p := fun j => j ∈ S)
                simp only [Finset.card_univ, Fintype.card_fin] at this
                omega
              have hmem_i : i ∈ Finset.univ.filter (fun j : Fin 6 => j ∉ S) := by
                simp [hi, Finset.mem_filter]
              have hmem_e : e_int ∈ Finset.univ.filter (fun j : Fin 6 =>
                  j ∉ S) := by simp [he_notS, Finset.mem_filter]
              -- m-achieving element
              have ⟨j_max, _, hj_eq⟩ := Finset.exists_max_image
                Finset.univ (fun i => padicValNat 7 (D i)) Finset.univ_nonempty
              have hj_dvd : (7 : ℤ) ^ m ∣ (D j_max : ℤ) := by
                rw [show (7 : ℤ) ^ m = ((7 ^ m : ℕ) : ℤ) from by push_cast; ring,
                  Int.natCast_dvd_natCast]
                exact (padicValNat_dvd_iff_le (hpos j_max).ne').mpr (by rw [← hj_eq]; rfl)
              have hj_notS : j_max ∉ S := by
                simp only [hS_def, Finset.mem_filter, Finset.mem_univ, true_and, not_not]
                exact dvd_trans (dvd_pow_self 7 (by omega : m ≠ 0)) (by exact_mod_cast hj_dvd)
              have hmem_j : j_max ∈ Finset.univ.filter (fun j : Fin 6 =>
                  j ∉ S) := by simp [hj_notS, Finset.mem_filter]
              have hne_ij : i ≠ j_max := by
                intro h; subst h; exact him' hj_dvd
              have hne_ej : e_int ≠ j_max := by
                intro h; subst h; exact he_ndvd hj_dvd
              -- 3 distinct elements in a set of size ≤ 2
              have h3 : ({i, e_int, j_max} : Finset (Fin 6)) ⊆
                  Finset.univ.filter (fun j : Fin 6 => j ∉ S) :=
                Finset.insert_subset_iff.mpr ⟨hmem_i,
                  Finset.insert_subset_iff.mpr ⟨hmem_e, Finset.singleton_subset_iff.mpr hmem_j⟩⟩
              have h3card : 3 ≤ ({i, e_int, j_max} : Finset (Fin 6)).card := by
                simp [Finset.card_insert_of_not_mem, hi_eq, hne_ij,
                  show e_int ≠ j_max from hne_ej,
                  show e_int ≠ i from Ne.symm hi_eq]
              exact absurd (le_trans h3card (Finset.card_le_card h3)) (by omega)
            exact band_top m lam (D i : ℤ) hlam_unit him
              (hmax _ (by rw [hDZ]; exact Finset.mem_image_of_mem _ (Finset.mem_univ i)))
    · -- j₀ > 0: interior big level. §4 reduction divides by 7^{j₀},
      -- reducing to |D'₇(0)| = |D₇(j₀)| ≥ 4 with fewer total elements.
      sorry

end IntLRC7BS
