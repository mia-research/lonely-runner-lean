import LonelyRunner.LRC.Spec.OrderSevenS5bN
import LonelyRunner.LRC.Spec.OrderSevenS5cN
import LonelyRunner.LRC.Spec.OrderSevenA5N
import LonelyRunner.LRC.Spec.OrderSevenS7WireN
import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# n = 7 (Barajas–Serra) — §4 reduction + the discrete core `bs_discrete_q`

Source: `sources_barajas_serra_2008.txt`, lines 237–264.

`m = max ν₇(D)`, `N = 7^(m+1)`. Some element is off the 7-lattice (`h7`), so `D₇(0), D₇(m) ≠ ∅`;
some element is odd (`h2`), which §7 uses at the modulus `98`. No `gcd` hypothesis.

This file proves `bs_discrete_q` (the residue-band core used by `Main`) by the §4
dispatch:
- **Easy branch** — if every valuation level `j < m` has `≤ 3` elements, the
  proven `corollary3` produces the multiplier directly.
- **Hard branch** — some level `j < m` has `≥ 4` elements. With `|D| = 6` at most
  one level can be that large; the §4 reduction (divide by `7^{i₀}`) moves it to
  the bottom, leaving `|D₇(0)| ∈ {4,5}` for the §5/§6 analysis. `|·| = 4` uses
  `four_band`; `|·| = 5` uses `five_band` (§6, `OrderSevenA5N`). All three
  sub-dispatches are wired; the only open leaf is `five_avoid` (`OrderSevenA5N`).
-/

open Finset

namespace LRC.OrderSevenN

/-- Repackage a power-of-7 band as a band at the general modulus `7·P`. -/
theorem band_at_pow (m : ℕ) (x : ℤ)
    (h : (7 ^ m : ℤ) ≤ x % (7 ^ (m + 1) : ℤ) ∧ x % (7 ^ (m + 1) : ℤ) ≤ 6 * 7 ^ m) :
    (((7 ^ m : ℕ) : ℤ)) ≤ x % (7 * ((7 ^ m : ℕ) : ℤ)) ∧
      x % (7 * ((7 ^ m : ℕ) : ℤ)) ≤ 6 * ((7 ^ m : ℕ) : ℤ) := by
  have hz : (7 : ℤ) * ((7 ^ m : ℕ) : ℤ) = (7 ^ (m + 1) : ℤ) := by push_cast; ring
  have hc : (((7 ^ m : ℕ) : ℤ)) = (7 ^ m : ℤ) := by push_cast; ring
  rw [hz, hc]; exact h

/-- **Discrete Barajas–Serra core, at a general modulus.**

The modulus is returned as `P` with the band taken mod `7·P`; the power-of-7 case
is `P = 7^m`. Stating it this way rather than as `∃ m` is what lets BS §7 be
transcribed: §7 resolves the `|A| = 5, m = 1` case at `N' = 2·49 = 98`, and
`98 = 7·14` is not a power of 7. See `docs/n7_bs/SECTION7_M1_ANALYSIS_v1.md`. -/
theorem bs_discrete_q
    (D : Fin 6 → ℕ) (hpos : ∀ i, 0 < D i)
    (hinj : Function.Injective D) (h7 : ∃ i, ¬ 7 ∣ D i) (h2 : ∃ i, ¬ 2 ∣ D i) :
    ∃ (P : ℕ) (lam : ℤ), 0 < P ∧ ∀ i,
      ((P : ℕ) : ℤ) ≤ (lam * (D i : ℤ)) % (7 * ((P : ℕ) : ℤ)) ∧
      (lam * (D i : ℤ)) % (7 * ((P : ℕ) : ℤ)) ≤ 6 * ((P : ℕ) : ℤ) := by
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
    exact ⟨7 ^ m, lam, by positivity, fun i => band_at_pow m _
      (hband (D i : ℤ) (by rw [hDZ]; exact Finset.mem_image_of_mem _ (Finset.mem_univ i)))⟩
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
      · -- No interior: all non-level-0 are level-m. |S| ∈ {4,5}.
        -- A level-m element exists (m ≥ 1 = max valuation), so it is ∉ S ⇒ |S| ≤ 5.
        obtain ⟨i_m, -, hi_m⟩ := Finset.exists_mem_eq_sup Finset.univ
          ⟨0, Finset.mem_univ 0⟩ (fun i => padicValNat 7 (D i))
        have hi_m_pos : 0 < padicValNat 7 (D i_m) := by rw [hm] at hj₀m; omega
        have hi_m_notS : i_m ∉ S := by
          simp only [hS_def, Finset.mem_filter, Finset.mem_univ, true_and, not_not]
          have : (7 : ℕ) ∣ D i_m := by
            have := (padicValNat_dvd_iff_le (hpos i_m).ne').mpr (by omega : 1 ≤ padicValNat 7 (D i_m))
            simpa using this
          exact_mod_cast this
        have hScard5 : S.card ≤ 5 := by
          have hsub : S ⊆ Finset.univ.erase i_m :=
            fun x hx => Finset.mem_erase.mpr ⟨fun h => hi_m_notS (h ▸ hx), Finset.mem_univ x⟩
          calc S.card ≤ (Finset.univ.erase i_m).card := Finset.card_le_card hsub
            _ = 5 := by rw [Finset.card_erase_of_mem (Finset.mem_univ _)]; simp
        by_cases hS5 : 5 ≤ S.card
        · -- |S| = 5: five_band on the five level-0 elements
          have hScard_eq : S.card = 5 := le_antisymm hScard5 hS5
          set g : Fin 5 → Fin 6 := fun k => (S.orderIsoOfFin hScard_eq k).val with hg_def
          have hg_mem : ∀ k, g k ∈ S := fun k => (S.orderIsoOfFin hScard_eq k).prop
          have hg_ndvd : ∀ k, ¬ (7 : ℤ) ∣ (D (g k) : ℤ) := fun k => by
            have := hg_mem k
            simp only [hS_def, Finset.mem_filter, Finset.mem_univ, true_and] at this; exact this
          set d5 : Fin 5 → ℤ := fun k => (D (g k) : ℤ)
          have hpos_d5 : ∀ k, 0 < d5 k := fun k => by
            show (0 : ℤ) < (D (g k) : ℤ); exact_mod_cast hpos (g k)
          have hinj_d5 : Function.Injective d5 := fun a b h => by
            have hDgab : D (g a) = D (g b) := by
              have : (D (g a) : ℤ) = D (g b) := h; exact_mod_cast this
            exact (S.orderIsoOfFin hScard_eq).injective (Subtype.val_injective (hinj hDgab))
          -- `S` misses exactly `i_m`, so any index outside `S` IS `i_m`.
          have hS_eq : S = Finset.univ.erase i_m :=
            Finset.eq_of_subset_of_card_le
              (fun x hx => Finset.mem_erase.mpr ⟨fun h => hi_m_notS (h ▸ hx), Finset.mem_univ x⟩)
              (by rw [Finset.card_erase_of_mem (Finset.mem_univ _), hScard_eq]; simp)
          have hnotS_eq : ∀ i : Fin 6, i ∉ S → i = i_m := by
            intro i hi
            by_contra hne
            exact hi (hS_eq ▸ Finset.mem_erase.mpr ⟨hne, Finset.mem_univ i⟩)
          have hkey : ∀ i : Fin 6, i ∈ S → ∃ k : Fin 5, (S.orderIsoOfFin hScard_eq k).val = i := by
            intro i hi
            have := (S.orderIsoOfFin hScard_eq).surjective ⟨i, hi⟩
            exact ⟨this.choose, congr_arg Subtype.val this.choose_spec⟩
          by_cases hm2 : 2 ≤ m
          · -- `m ≥ 2`: BS §6, via `five_band`.
            obtain ⟨lam, hlam_unit, hband5⟩ := five_band m hm2 d5 hg_ndvd hpos_d5 hinj_d5
            refine ⟨7 ^ m, lam, by positivity, fun i => band_at_pow m _ ?_⟩
            by_cases hi : i ∈ S
            · obtain ⟨k, hk⟩ := hkey i hi
              have := hband5 k; simp only [d5, g, hk] at this; exact this
            · exact band_top m lam (D i : ℤ) hlam_unit (hnointerior i hi)
                (hmax _ (by rw [hDZ]; exact Finset.mem_image_of_mem _ (Finset.mem_univ i)))
          · -- `m = 1`: BS §7. The five level-0 units have no good multiplier at
            -- `N = 49` when they form one of the three exceptional sets, and `d₆`
            -- cannot help there. `five_band_m1` handles all six jointly, and may
            -- return `P = 14` (that is, `N' = 98`), which is why the conclusion
            -- carries a general modulus.
            have h1m : 1 ≤ m := by omega
            have hm1 : m = 1 := by omega
            have hd6_dvd : (7 : ℤ) ∣ (D i_m : ℤ) := by
              have h := hnointerior i_m hi_m_notS
              rwa [hm1, pow_one] at h
            have hd6_ndvd : ¬ ((7 : ℤ) ^ 2 ∣ (D i_m : ℤ)) := by
              have h := hmax (D i_m : ℤ)
                (by rw [hDZ]; exact Finset.mem_image_of_mem _ (Finset.mem_univ i_m))
              rwa [hm1] at h
            have hodd6 : ¬ ((∀ k, (2 : ℤ) ∣ d5 k) ∧ (2 : ℤ) ∣ (D i_m : ℤ)) := by
              rintro ⟨hall, hdiv⟩
              obtain ⟨i2, hi2⟩ := h2
              apply hi2
              by_cases hi : i2 ∈ S
              · obtain ⟨k, hk⟩ := hkey i2 hi
                have hk' := hall k
                simp only [d5, g, hk] at hk'
                exact_mod_cast hk'
              · rw [hnotS_eq i2 hi]; exact_mod_cast hdiv
            obtain ⟨P, lam, hP, hb5, hb6⟩ :=
              five_band_m1 d5 (D i_m : ℤ) hpos_d5 hg_ndvd hinj_d5 hd6_dvd hd6_ndvd hodd6
            refine ⟨P, lam, hP, fun i => ?_⟩
            by_cases hi : i ∈ S
            · obtain ⟨k, hk⟩ := hkey i hi
              have := hb5 k; simp only [d5, g, hk] at this; exact this
            · rw [hnotS_eq i hi]; exact hb6
        · -- |S| = 4: four_band suffices (S = T, no 5th level-0 element)
          have hScard_eq : S.card = 4 := le_antisymm (by omega) hS_card
          have hST : T = S := Finset.eq_of_subset_of_card_le hTS (by rw [hScard_eq, hT4])
          set d4 : Fin 4 → ℤ := fun k => (D (f k) : ℤ)
          obtain ⟨lam, hlam_unit, _, _, hband4⟩ := four_band m hj₀m d4 hf_ndvd
          refine ⟨7 ^ m, lam, by positivity, fun i => band_at_pow m _ ?_⟩
          by_cases hi : i ∈ S
          · have hiT : i ∈ T := hST ▸ hi
            have ⟨k, hk⟩ : ∃ k : Fin 4, (T.orderIsoOfFin hT4 k).val = i := by
              have := (T.orderIsoOfFin hT4).surjective ⟨i, hiT⟩
              exact ⟨this.choose, congr_arg Subtype.val this.choose_spec⟩
            have := hband4 k; simp only [d4, f, hk] at this; exact this
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
          simp only [d4]; exact mt (Prime.dvd_mul seven_totient_full_int |>.mp)
            (by simp [hpre_unit, hf_ndvd k])
        obtain ⟨lam', hlam'_unit, _, ⟨j_step, hj1, hj5, hcongr'⟩, hband4⟩ :=
          four_band m hj₀m d4 hd4_ndvd
        set lam := lam' * pre
        have hlam_unit : ¬ (7 : ℤ) ∣ lam := by
          exact mt (Prime.dvd_mul seven_totient_full_int |>.mp)
            (by simp [hlam'_unit, hpre_unit])
        -- |S| = 4 here: the interior element `e_int` and a level-m element are two
        -- distinct elements of `Sᶜ`, so |S| ≤ 4; with `hS_card` (≥4), `S = T`.
        have hScard_eq : S.card = 4 := by
          obtain ⟨i_m, -, hi_m⟩ := Finset.exists_mem_eq_sup Finset.univ
            ⟨0, Finset.mem_univ 0⟩ (fun i => padicValNat 7 (D i))
          have hi_m_pos : 0 < padicValNat 7 (D i_m) := by rw [hm] at hj₀m; omega
          have hi_m_notS : i_m ∉ S := by
            simp only [hS_def, Finset.mem_filter, Finset.mem_univ, true_and, not_not]
            have h7 : (7 : ℕ) ∣ D i_m := by
              have := (padicValNat_dvd_iff_le (hpos i_m).ne').mpr
                (by omega : 1 ≤ padicValNat 7 (D i_m))
              simpa using this
            exact_mod_cast h7
          have he_int_val : padicValNat 7 (D e_int) < m :=
            Nat.lt_of_not_le fun h => hndvd_nat ((padicValNat_dvd_iff_le (hpos e_int).ne').mpr h)
          have hne : i_m ≠ e_int := by
            intro h; subst h
            exact hndvd_nat ((padicValNat_dvd_iff_le (hpos i_m).ne').mpr
              (by rw [hm]; exact le_of_eq hi_m))
          have hsub : S ⊆ (Finset.univ.erase i_m).erase e_int := fun x hx =>
            Finset.mem_erase.mpr ⟨fun h => he_notS (h ▸ hx),
              Finset.mem_erase.mpr ⟨fun h => hi_m_notS (h ▸ hx), Finset.mem_univ x⟩⟩
          have hle : S.card ≤ 4 := by
            calc S.card ≤ ((Finset.univ.erase i_m).erase e_int).card :=
                  Finset.card_le_card hsub
              _ = 4 := by
                  rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨Ne.symm hne, Finset.mem_univ _⟩),
                    Finset.card_erase_of_mem (Finset.mem_univ _)]; simp
          omega
        have hST : T = S := Finset.eq_of_subset_of_card_le hTS (by rw [hScard_eq, hT4])
        refine ⟨7 ^ m, lam, by positivity, fun i => band_at_pow m _ ?_⟩
        by_cases hi : i ∈ S
        · have hiT : i ∈ T := hST ▸ hi
          have ⟨k, hk⟩ : ∃ k : Fin 4, (T.orderIsoOfFin hT4 k).val = i := by
            have := (T.orderIsoOfFin hT4).surjective ⟨i, hiT⟩
            exact ⟨this.choose, congr_arg Subtype.val this.choose_spec⟩
          have := hband4 k; simp only [d4, f, hk] at this
          simp only [show lam = lam' * pre from rfl, mul_assoc]
          exact this
        · -- Non-level-0 element
          simp only [hS_def, Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hi
          by_cases hi_eq : i = e_int
          · -- THE interior element: use pre-multiplier + interior_in_band
            subst hi_eq
            -- After subst, e_int → i
            obtain ⟨c', hc'⟩ := hcongr'
            obtain ⟨w, hw⟩ := hpre_congr
            -- lam * Di = lam' * pre * Di ≡ j_step * (7^i₀ + 7^m) (mod 7^(m+1))
            have hmod_eq : (lam * (D i : ℤ)) % (7 : ℤ) ^ (m + 1) =
                ((j_step : ℤ) * ((7 : ℤ) ^ i₀ + (7 : ℤ) ^ m)) % (7 : ℤ) ^ (m + 1) := by
              apply Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr
              apply Int.emod_eq_zero_of_dvd
              have hlam' : lam' = (j_step : ℤ) + (7 : ℤ) ^ m * c' := by linarith
              have hpD : pre * (D i : ℤ) = (7 : ℤ) ^ i₀ + (7 : ℤ) ^ m + (7 : ℤ) ^ (m + 1) * w :=
                by linarith
              -- witness: j_step*w + c'*7^(i₀-1) + c'*7^(m-1) + 7^m*c'*w
              -- relies on: 7^m * 7^i₀ = 7^(m+1) * 7^(i₀-1) and 7^m * 7^m = 7^(m+1) * 7^(m-1)
              refine ⟨(j_step : ℤ) * w + c' * (7 : ℤ) ^ (i₀ - 1) +
                c' * (7 : ℤ) ^ (m - 1) + (7 : ℤ) ^ m * c' * w, ?_⟩
              have hfact : lam * (D i : ℤ) =
                  ((j_step : ℤ) + (7 : ℤ) ^ m * c') * ((7 : ℤ) ^ i₀ + (7 : ℤ) ^ m +
                    (7 : ℤ) ^ (m + 1) * w) := by
                calc lam * (D i : ℤ) = lam' * (pre * (D i : ℤ)) := by ring
                  _ = _ := by rw [hlam', hpD]
              have hi₀_eq : (7 : ℤ) ^ m * (7 : ℤ) ^ i₀ = (7 : ℤ) ^ (m + 1) * (7 : ℤ) ^ (i₀ - 1) := by
                rw [← pow_add, ← pow_add]; norm_cast; congr 1; omega
              have hm_eq : (7 : ℤ) ^ m * (7 : ℤ) ^ m = (7 : ℤ) ^ (m + 1) * (7 : ℤ) ^ (m - 1) := by
                rw [← pow_add, ← pow_add]; norm_cast; congr 1; omega
              linear_combination hfact - (j_step : ℤ) * (7 : ℤ) ^ i₀ -
                (j_step : ℤ) * (7 : ℤ) ^ m + c' * hi₀_eq + c' * hm_eq
            obtain ⟨hlo, hhi, hlt, hnn⟩ := interior_in_band j_step i₀ m hj1 hj5 hi₀_1 hi₀_m
            rw [hmod_eq, Int.emod_eq_of_lt hnn hlt]
            exact ⟨hlo, hhi⟩
          · -- Not e_int: must be level-m → band_top
            have him : (7 : ℤ) ^ m ∣ (D i : ℤ) := by
              by_contra him'
              -- i and e_int both in Sᶜ with ¬7^m∣. The m-achieving
              -- element is a third element of Sᶜ. But |Sᶜ| ≤ 2.
              haveI : Fact (Nat.Prime 7) := ⟨seven_totient_full⟩
              have hSc_le : (Finset.univ.filter (fun j : Fin 6 =>
                  j ∉ S)).card ≤ 2 := by
                have hpart := Finset.filter_card_add_filter_neg_card_eq_card
                  (s := Finset.univ) (p := fun j => j ∈ S)
                simp only [Finset.card_univ, Fintype.card_fin] at hpart
                have hfilt : (Finset.univ.filter (fun j : Fin 6 => j ∈ S)).card = 4 := by
                  convert hScard_eq using 1
                  congr 1; ext x; simp
                omega
              have hmem_i : i ∈ Finset.univ.filter (fun j : Fin 6 => j ∉ S) :=
                Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
                  simp only [hS_def, Finset.mem_filter, Finset.mem_univ, true_and, not_not]
                  exact hi⟩
              have hmem_e : e_int ∈ Finset.univ.filter (fun j : Fin 6 =>
                  j ∉ S) := by simp [he_notS, Finset.mem_filter]
              -- m-achieving element
              have ⟨j_max, _, hj_eq⟩ := Finset.exists_max_image
                Finset.univ (fun i => padicValNat 7 (D i)) Finset.univ_nonempty
              have hj_dvd : (7 : ℤ) ^ m ∣ (D j_max : ℤ) := by
                rw [show (7 : ℤ) ^ m = ((7 ^ m : ℕ) : ℤ) from by push_cast; ring,
                  Int.natCast_dvd_natCast]
                exact (padicValNat_dvd_iff_le (hpos j_max).ne').mpr
                  (by rw [hm]; exact Finset.sup_le (fun i _ => hj_eq i (Finset.mem_univ i)))
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
                simp [Finset.card_insert_of_notMem, hi_eq, hne_ij,
                  show e_int ≠ j_max from hne_ej,
                  show e_int ≠ i from Ne.symm hi_eq]
              exact absurd (le_trans h3card (Finset.card_le_card h3)) (by omega)
            exact band_top m lam (D i : ℤ) hlam_unit him
              (hmax _ (by rw [hDZ]; exact Finset.mem_image_of_mem _ (Finset.mem_univ i)))
    · -- j₀ > 0: interior big level (§4 reduction).
      -- Config is 1/4/1: extract 4 level-j₀ elements, divide by 7^{j₀}.
      -- Level-0 of D: single_level_avoid at level m.
      have hj₀pos : 0 < j₀ := Nat.pos_of_ne_zero hj₀ne
      have hmpos : 0 < m := by omega
      -- Extract level-j₀ elements (as Fin 6 indices)
      set Sj := Finset.univ.filter (fun i : Fin 6 =>
          (7 : ℤ) ^ j₀ ∣ (D i : ℤ) ∧ ¬ (7 : ℤ) ^ (j₀ + 1) ∣ (D i : ℤ)) with hSj_def
      have hSj_card : 4 ≤ Sj.card := by
        have hDZ_inj : Set.InjOn (fun i : Fin 6 => (D i : ℤ))
            (↑(Finset.univ : Finset (Fin 6))) :=
          fun a _ b _ h => hinj (Nat.cast_injective h)
        have : (DZ.filter (fun d => (7 : ℤ) ^ j₀ ∣ d ∧ ¬ (7 : ℤ) ^ (j₀ + 1) ∣ d)).card
            = Sj.card := by
          rw [hDZ, hSj_def, Finset.filter_image]
          exact Finset.card_image_of_injOn
            (Set.InjOn.mono (fun x hx => Finset.mem_filter.mp hx |>.1) hDZ_inj)
        linarith
      -- |Sj| = 4: a level-0 element (h7) and a level-m element are distinct and
      -- both ∉ Sj (valuations 0 and m ≠ j₀), so |Sj| ≤ 4; with hSj_card, = 4.
      have hSj_eq : Sj.card = 4 := by
        obtain ⟨i0, hi0⟩ : ∃ i, ¬ (7 : ℕ) ∣ D i := h7
        have hi0Z : ¬ (7 : ℤ) ∣ (D i0 : ℤ) := by exact_mod_cast hi0
        obtain ⟨i_m, -, hi_m⟩ := Finset.exists_mem_eq_sup Finset.univ
          ⟨0, Finset.mem_univ 0⟩ (fun i => padicValNat 7 (D i))
        have hi0_notSj : i0 ∉ Sj := by
          simp only [hSj_def, Finset.mem_filter, Finset.mem_univ, true_and]
          rintro ⟨hd, -⟩
          exact hi0Z (dvd_trans (dvd_pow_self 7 (by omega : j₀ ≠ 0)) hd)
        have him_dvd : (7 : ℤ) ^ (j₀ + 1) ∣ (D i_m : ℤ) := by
          rw [show (7 : ℤ) ^ (j₀ + 1) = ((7 ^ (j₀ + 1) : ℕ) : ℤ) from by push_cast; ring,
            Int.natCast_dvd_natCast]
          exact (padicValNat_dvd_iff_le (hpos i_m).ne').mpr (by rw [hm] at hj₀m; omega)
        have him_notSj : i_m ∉ Sj := by
          simp only [hSj_def, Finset.mem_filter, Finset.mem_univ, true_and]
          rintro ⟨-, hnd⟩; exact hnd him_dvd
        have hne : i0 ≠ i_m := by
          rintro rfl
          have h0 : padicValNat 7 (D i0) = 0 := padicValNat.eq_zero_of_not_dvd hi0
          rw [← hi_m, ← hm] at h0; omega
        have hsub : Sj ⊆ (Finset.univ.erase i0).erase i_m := fun x hx =>
          Finset.mem_erase.mpr ⟨fun h => him_notSj (h ▸ hx),
            Finset.mem_erase.mpr ⟨fun h => hi0_notSj (h ▸ hx), Finset.mem_univ x⟩⟩
        have hle : Sj.card ≤ 4 := by
          calc Sj.card ≤ ((Finset.univ.erase i0).erase i_m).card := Finset.card_le_card hsub
            _ = 4 := by
                rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨Ne.symm hne, Finset.mem_univ _⟩),
                  Finset.card_erase_of_mem (Finset.mem_univ _)]; simp
        omega
      obtain ⟨Tj, hTjS, hTj4⟩ := Finset.exists_subset_card_eq hSj_card
      have hSjTj : Tj = Sj := Finset.eq_of_subset_of_card_le hTjS (by rw [hSj_eq, hTj4])
      set fj : Fin 4 → Fin 6 := fun k => (Tj.orderIsoOfFin hTj4 k).val
      have hfj_mem : ∀ k, fj k ∈ Sj := fun k => hTjS ((Tj.orderIsoOfFin hTj4 k).prop)
      have hfj_dvd : ∀ k, (7 : ℤ) ^ j₀ ∣ (D (fj k) : ℤ) := fun k => by
        have := hfj_mem k; simp only [hSj_def, Finset.mem_filter] at this; exact this.2.1
      have hfj_ndvd : ∀ k, ¬ (7 : ℤ) ^ (j₀ + 1) ∣ (D (fj k) : ℤ) := fun k => by
        have := hfj_mem k; simp only [hSj_def, Finset.mem_filter] at this; exact this.2.2
      -- Divide by 7^{j₀}: get coprime-to-7 values
      set d4 : Fin 4 → ℤ := fun k => (D (fj k) : ℤ) / (7 : ℤ) ^ j₀
      have hd4_ndvd : ∀ k, ¬ (7 : ℤ) ∣ d4 k := fun k => by
        intro h7
        exact hfj_ndvd k (by
          rw [show (7 : ℤ) ^ (j₀ + 1) = 7 ^ j₀ * 7 from by ring]
          have hkey : (7 : ℤ) ^ j₀ * d4 k = (D (fj k) : ℤ) :=
            Int.mul_ediv_cancel' (hfj_dvd k)
          exact hkey ▸ mul_dvd_mul dvd_rfl h7)
      -- Apply four_band at level m' = m - j₀
      set m' := m - j₀
      have hm'pos : 0 < m' := by omega
      have hm'eq : j₀ + m' = m := by omega
      obtain ⟨lam', hlam'_unit, _, _, hband'⟩ := four_band m' hm'pos d4 hd4_ndvd
      -- Apply single_level_avoid at level m for the level-0 element.
      -- The (1+k·7^m) factor shifts qz at level m; inert for 7-divisible elements.
      -- Only the coprime-to-7 elements constrain k. With |D₇(0)| ≤ 2 and
      -- |F_i| = 2 per element, ∑|F| ≤ 4 ≤ 6, so single_level_avoid works.
      set S0 := Finset.univ.filter (fun i : Fin 6 => ¬ (7 : ℤ) ∣ (D i : ℤ)) with hS0_def
      have hS0_sum : ∑ i ∈ S0, ({(0 : ZMod 7), 6} : Finset (ZMod 7)).card ≤ 6 := by
        simp only [Finset.card_pair (by decide : (0 : ZMod 7) ≠ 6)]
        have hS0_Sj_disj : Disjoint S0 Sj := by
          simp only [Finset.disjoint_left, hS0_def, hSj_def, Finset.mem_filter,
            Finset.mem_univ, true_and]
          intro i hi ⟨hdvd, _⟩
          exact hi (dvd_trans (dvd_pow_self 7 hj₀ne) hdvd)
        have hS0_card : S0.card ≤ 2 := by
          have hunion := Finset.card_union_of_disjoint hS0_Sj_disj
          have hle : (S0 ∪ Sj).card ≤ 6 := (Finset.card_le_card
            (Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _))).trans
            (by simp [Finset.card_univ, Fintype.card_fin])
          omega
        have hsum_eq : ∑ i ∈ S0, (2 : ℕ) = S0.card * 2 :=
          Finset.sum_const_nat (fun _ _ => rfl)
        omega
      have hS0_r : ∀ i ∈ S0, ((lam' * (D i : ℤ) : ℤ) : ZMod 7) ≠ 0 := fun i hi => by
        simp only [hS0_def, Finset.mem_filter] at hi
        push_cast
        apply mul_ne_zero
        · exact_mod_cast mt (ZMod.intCast_zmod_eq_zero_iff_dvd lam' 7).mp hlam'_unit
        · exact_mod_cast mt (ZMod.intCast_zmod_eq_zero_iff_dvd (D i : ℤ) 7).mp hi.2
      obtain ⟨kz, hkz⟩ := single_level_avoid S0
        (fun i => qz m (lam' * (D i : ℤ)))
        (fun i => ((lam' * (D i : ℤ) : ℤ) : ZMod 7))
        (fun _ => {0, 6}) hS0_r hS0_sum
      set lam := (1 + (kz.val : ℤ) * (7 : ℤ) ^ m) * lam'
      have hlam_unit : ¬ (7 : ℤ) ∣ lam := by
        exact mt (Prime.dvd_mul seven_totient_full_int |>.mp)
          (by simp [lambda0_coprime m hmpos, hlam'_unit])
      refine ⟨7 ^ m, lam, by positivity, fun i => band_at_pow m _ ?_⟩
      by_cases h7i : (7 : ℤ) ∣ (D i : ℤ)
      · -- 7 ∣ D i: the (1+k·7^m) factor is inert
        have hinert : (lam * (D i : ℤ)) % (7 : ℤ) ^ (m + 1) =
            (lam' * (D i : ℤ)) % (7 : ℤ) ^ (m + 1) := by
          show ((1 + (kz.val : ℤ) * (7 : ℤ) ^ m) * lam' * (D i : ℤ)) % _ = _
          exact lambda0_inert m _ lam' _ h7i
        rw [hinert]
        by_cases him : (7 : ℤ) ^ m ∣ (D i : ℤ)
        · exact band_top m lam' (D i : ℤ) hlam'_unit him
            (hmax _ (by rw [hDZ]; exact Finset.mem_image_of_mem _ (Finset.mem_univ i)))
        · -- Level j₀: lift band from m' to m. First show i ∈ Sj.
          -- Case split immediately on i ∈ Sj; the ∉ case gives cardinality contradiction.
          by_cases hiSj : i ∈ Sj
          · -- i is one of the level-j₀ elements (Sj = Tj since |Sj| = 4)
            have hiTj : i ∈ Tj := hSjTj ▸ hiSj
            have hdvd_j : (7 : ℤ) ^ j₀ ∣ (D i : ℤ) := by
              have := (Finset.mem_filter.mp hiSj).2; simp [hSj_def] at this; exact this.1
            have hdi' : (D i : ℤ) = (7 : ℤ) ^ j₀ * ((D i : ℤ) / (7 : ℤ) ^ j₀) :=
              (Int.mul_ediv_cancel' hdvd_j).symm
            have ⟨ki, hki⟩ : ∃ ki : Fin 4, (Tj.orderIsoOfFin hTj4 ki).val = i := by
              have := (Tj.orderIsoOfFin hTj4).surjective ⟨i, hiTj⟩
              exact ⟨this.choose, congr_arg Subtype.val this.choose_spec⟩
            have hdi_eq : (D i : ℤ) / (7 : ℤ) ^ j₀ = d4 ki := by
              simp only [d4, fj, hki]
            have hband_ki := hband' ki
            rw [show d4 ki = (D i : ℤ) / (7 : ℤ) ^ j₀ from hdi_eq.symm] at hband_ki
            rw [hdi']
            exact hm'eq ▸ band_lift j₀ m' lam' _ hband_ki
          · -- i ∉ Sj but 7∣D i and ¬7^m∣D i: impossible by 1/4/1 cardinality.
            -- With |Sj|=4, a level-0 element (from h7), a level-m achiever, and i itself,
            -- we have 7 distinct elements in Fin 6 — contradiction.
            exfalso
            obtain ⟨i0, hi0⟩ : ∃ i0 : Fin 6, ¬ (7 : ℕ) ∣ D i0 := h7
            have hi0_notSj : i0 ∉ Sj := by
              simp only [hSj_def, Finset.mem_filter, Finset.mem_univ, true_and]
              rintro ⟨hd, -⟩
              exact hi0 (by exact_mod_cast dvd_trans (dvd_pow_self 7 hj₀ne) hd)
            obtain ⟨i_m, -, hi_m⟩ := Finset.exists_mem_eq_sup Finset.univ
              ⟨0, Finset.mem_univ 0⟩ (fun i => padicValNat 7 (D i))
            have him_dvd : (7 : ℤ) ^ m ∣ (D i_m : ℤ) := by
              rw [show (7 : ℤ) ^ m = ((7 ^ m : ℕ) : ℤ) from by push_cast; ring,
                Int.natCast_dvd_natCast]
              exact (padicValNat_dvd_iff_le (hpos i_m).ne').mpr
                (by rw [hm]; exact le_of_eq hi_m)
            have him_notSj : i_m ∉ Sj := by
              simp only [hSj_def, Finset.mem_filter, Finset.mem_univ, true_and]
              rintro ⟨-, hnd⟩
              exact hnd (dvd_trans (pow_dvd_pow 7 (by omega : j₀ + 1 ≤ m)) him_dvd)
            have hineqm : i ≠ i_m := fun h => him (h ▸ him_dvd)
            have hi0nei : i0 ≠ i := fun h => by
              simp only [h] at hi0
              exact hi0 (by exact_mod_cast (show (7 : ℤ) ∣ (D i : ℤ) from h7i))
            have hi0nem : i0 ≠ i_m := fun h => by
              simp only [h] at hi0
              exact hi0 (by
                have : (7 : ℤ) ^ m ∣ (D i_m : ℤ) := him_dvd
                have h7 : (7 : ℕ) ^ m ∣ D i_m := by exact_mod_cast this
                exact dvd_trans (dvd_pow_self 7 (by omega : m ≠ 0)) h7)
            -- {i0, i, i_m} are 3 distinct elements outside Sj (card 4) ⊆ Fin 6 (card 6)
            have hdisj : Disjoint ({i0, i, i_m} : Finset (Fin 6)) Sj :=
              Finset.disjoint_left.mpr (fun x hx =>
                Finset.mem_insert.mp hx |>.elim (fun h => h ▸ hi0_notSj)
                  (Finset.mem_insert.mp · |>.elim (fun h => h ▸ hiSj)
                    (Finset.mem_singleton.mp · ▸ him_notSj)))
            have h3card : ({i0, i, i_m} : Finset (Fin 6)).card = 3 := by
              have hnem : i ∉ ({i_m} : Finset (Fin 6)) := by simp [hineqm]
              have hne0 : i0 ∉ ({i, i_m} : Finset (Fin 6)) := by simp [hi0nei, hi0nem]
              rw [Finset.card_insert_of_notMem hne0, Finset.card_insert_of_notMem hnem,
                Finset.card_singleton]
            have hcard7 : (({i0, i, i_m} : Finset (Fin 6)) ∪ Sj).card = 7 := by
              rw [Finset.card_union_of_disjoint hdisj, h3card, hSj_eq]
            have hle : (({i0, i, i_m} : Finset (Fin 6)) ∪ Sj).card ≤ 6 :=
              (Finset.card_le_card (Finset.subset_univ _)).trans (by simp)
            omega
      · -- ¬7 ∣ D i: level-0 element. Use qz avoidance.
        have hiS0 : i ∈ S0 := by simp [hS0_def, h7i]
        have havoid := hkz i hiS0
        -- havoid : qz m (lam' * Di) + kz * (lam' * Di : ZMod 7) ∉ {0, 6}
        have hqz_shift : qz m (lam * (D i : ℤ)) =
            qz m (lam' * (D i : ℤ)) + (kz : ZMod 7) * ((lam' * (D i : ℤ) : ℤ) : ZMod 7) := by
          have heq : lam * (D i : ℤ) = (1 + (kz.val : ℤ) * (7 : ℤ) ^ m) * (lam' * (D i : ℤ)) :=
            by ring
          rw [heq, qz_shift0]; congr 1; congr 1
          have : ((kz.val : ℤ) : ZMod 7) = kz := by
            have h1 := ZMod.natCast_val (R := ZMod 7) kz
            rw [ZMod.cast_id] at h1; exact_mod_cast h1
          push_cast; exact this
        -- havoid : qz m (lam' * Di) + kz * (lam' * Di : ZMod 7) ∉ {0, 6}
        -- hqz_shift : qz m (lam * Di) = qz m (lam' * Di) + kz * (lam' * Di : ZMod 7)
        have havoid' : qz m (lam * (D i : ℤ)) ∉ ({0, 6} : Finset (ZMod 7)) := by
          rwa [hqz_shift]
        have h0 : qz m (lam * (D i : ℤ)) ≠ 0 := by
          intro h; apply havoid'; simp [h]
        have h6 : qz m (lam * (D i : ℤ)) ≠ 6 := by
          intro h; apply havoid'; simp [h]
        exact band_of_qz_ne m _ h0 h6

end LRC.OrderSevenN
