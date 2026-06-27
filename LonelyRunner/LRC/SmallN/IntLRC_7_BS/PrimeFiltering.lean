import LonelyRunner.LRC.SmallN.IntLRC_7_BS.Defs
import Mathlib.Algebra.Field.ZMod

/-!
# n = 7 (Barajas–Serra) — Prime Filtering Lemma + Corollary 3

Source: `sources_barajas_serra_2008.txt`, lines 129–177.

The reduction engine. Built on the equation-(3) identity `qz_lambda` from `Defs`.

- `single_level_avoid` — the combinatorial core: over `ZMod 7`, with each index
  carrying an affine map `k ↦ c i + k·r i` (`r i` a unit) and a forbidden set
  `F i`, if the forbidden sets have total size `≤ 6` then some `k ∈ ZMod 7`
  avoids all of them. This is the single-level pigeonhole behind Lemma 2.
- `prime_filtering` — **Lemma 2** (Prime Filtering), proven by the level induction
  wrapping `single_level_avoid` / `single_level_avoid_excl` via `qz_step`.
- `corollary3` — **Corollary 3** (`i₀ = m` form): if every level `j < m` has
  `≤ 3` elements, a multiplier sends all of `D` into the central residue band.
-/

open Finset

namespace IntLRC7BS

instance : Fact (Nat.Prime 7) := ⟨by decide⟩

/-- **Single-level avoidance (pigeonhole core of Lemma 2).** For a finite index
set `s`, current values `c i`, unit slopes `r i ≠ 0`, and forbidden sets `F i` in
`ZMod 7` with total size `≤ 6`, there is a multiplier coefficient `k ∈ ZMod 7`
such that the shifted value `c i + k·r i` avoids `F i` for every `i ∈ s`.

This is BHK-free combinatorics: as `k` ranges over `ZMod 7` (7 values), the
affine map `k ↦ c i + k·r i` is a bijection, so it lands in `F i` for exactly
`|F i|` values of `k`; the union of bad `k`'s has size `≤ 6 < 7`. -/
theorem single_level_avoid {ι : Type*} (s : Finset ι)
    (c r : ι → ZMod 7) (F : ι → Finset (ZMod 7))
    (hr : ∀ i ∈ s, r i ≠ 0)
    (hsum : ∑ i ∈ s, (F i).card ≤ 6) :
    ∃ k : ZMod 7, ∀ i ∈ s, c i + k * r i ∉ F i := by
  classical
  -- bad coefficients for index `i`: preimage of `F i` under the affine map
  set B : ι → Finset (ZMod 7) := fun i => (F i).image (fun y => (y - c i) * (r i)⁻¹) with hB
  have hBcard : ∀ i ∈ s, (B i).card ≤ (F i).card := fun i _ => card_image_le
  have hunion : (s.biUnion B).card ≤ 6 :=
    le_trans card_biUnion_le (le_trans (sum_le_sum hBcard) hsum)
  -- the union of bad sets does not cover all of `ZMod 7`
  have hcard7 : (univ : Finset (ZMod 7)).card = 7 := by
    rw [card_univ, ZMod.card]
  have hne : ∃ k : ZMod 7, k ∉ s.biUnion B := by
    by_contra h
    push_neg at h
    have hsub : (univ : Finset (ZMod 7)) ⊆ s.biUnion B := fun k _ => h k
    have hle := card_le_card hsub
    rw [hcard7] at hle
    omega
  obtain ⟨k, hknot⟩ := hne
  refine ⟨k, fun i hi hmem => ?_⟩
  have hkB : k ∉ B i := fun h => hknot (mem_biUnion.mpr ⟨i, hi, h⟩)
  apply hkB
  rw [hB, mem_image]
  refine ⟨c i + k * r i, hmem, ?_⟩
  have hrne : r i ≠ 0 := hr i hi
  show (c i + k * r i - c i) * (r i)⁻¹ = k
  rw [add_sub_cancel_left, mul_assoc, mul_inv_cancel₀ hrne, mul_one]

/-- **Avoidance with one excluded coefficient.** As `single_level_avoid`, but the
chosen `k` may also be required to avoid a single value `e`. Used at the top
level, where `k = e` (`= 6`) would make the multiplier `1 + e·7^0 = 7` a
non-unit. Needs the tighter bound `∑ |F i| ≤ 5` (so the bad set together with
`{e}` stays `≤ 6 < 7`). -/
theorem single_level_avoid_excl {ι : Type*} (s : Finset ι)
    (c r : ι → ZMod 7) (F : ι → Finset (ZMod 7)) (e : ZMod 7)
    (hr : ∀ i ∈ s, r i ≠ 0)
    (hsum : ∑ i ∈ s, (F i).card ≤ 5) :
    ∃ k : ZMod 7, k ≠ e ∧ ∀ i ∈ s, c i + k * r i ∉ F i := by
  classical
  set B : ι → Finset (ZMod 7) := fun i => (F i).image (fun y => (y - c i) * (r i)⁻¹) with hB
  have hBcard : ∀ i ∈ s, (B i).card ≤ (F i).card := fun i _ => card_image_le
  have hunion : (s.biUnion B).card ≤ 5 :=
    le_trans card_biUnion_le (le_trans (sum_le_sum hBcard) hsum)
  have hbad : (insert e (s.biUnion B)).card ≤ 6 :=
    le_trans (card_insert_le _ _) (by omega)
  have hcard7 : (univ : Finset (ZMod 7)).card = 7 := by rw [card_univ, ZMod.card]
  have hne : ∃ k : ZMod 7, k ∉ insert e (s.biUnion B) := by
    by_contra h
    push_neg at h
    have hsub : (univ : Finset (ZMod 7)) ⊆ insert e (s.biUnion B) := fun k _ => h k
    have hle := card_le_card hsub
    rw [hcard7] at hle
    omega
  obtain ⟨k, hknot⟩ := hne
  have hke : k ≠ e := fun h => hknot (mem_insert.mpr (Or.inl h))
  refine ⟨k, hke, fun i hi hmem => ?_⟩
  have hkB : k ∉ B i := fun h => hknot (mem_insert.mpr (Or.inr (mem_biUnion.mpr ⟨i, hi, h⟩)))
  apply hkB
  rw [hB, mem_image]
  refine ⟨c i + k * r i, hmem, ?_⟩
  have hrne : r i ≠ 0 := hr i hi
  show (c i + k * r i - c i) * (r i)⁻¹ = k
  rw [add_sub_cancel_left, mul_assoc, mul_inv_cancel₀ hrne, mul_one]

/-- Lift a `ZMod 7` element to an integer with the same residue. -/
private lemma intCast_val (k : ZMod 7) : ((k.val : ℤ) : ZMod 7) = k := by
  push_cast
  exact ZMod.natCast_rightInverse k

private lemma natCast_val (k : ZMod 7) : ((k.val : ℕ) : ZMod 7) = k :=
  ZMod.natCast_rightInverse k

/-- **Lemma 2 (Prime Filtering).** Let `m` bound the 7-adic valuations of the
(positive) integers in `D` (`¬ 7^{m+1} ∣ d`). If the forbidden sets `F d ⊂ ZMod 7`
satisfy `∑ |F d| ≤ 6` summed over each valuation level `j < m`, and `∑ |F d| ≤ 5`
over the top level `m`, then there is a multiplier `lam` (coprime to 7) with
`q(lam·d) ∉ F d` for every `d ∈ D`.

Proof: descending induction on the level `i`, accumulating a unit multiplier that
handles all `d` with `7^i ∣ d`. Each step picks the next coefficient with
`single_level_avoid` (`j < m`) or `single_level_avoid_excl` (`j = m`, keeping the
multiplier a unit), via the step identity `qz_step`. -/
theorem prime_filtering (m : ℕ) (D : Finset ℤ) (F : ℤ → Finset (ZMod 7))
    (hmax : ∀ d ∈ D, ¬ (7 : ℤ) ^ (m + 1) ∣ d)
    (hlo : ∀ j, j < m →
      (∑ d ∈ D.filter (fun d => (7 : ℤ) ^ j ∣ d ∧ ¬ (7 : ℤ) ^ (j + 1) ∣ d), (F d).card) ≤ 6)
    (hhi : (∑ d ∈ D.filter (fun d => (7 : ℤ) ^ m ∣ d ∧ ¬ (7 : ℤ) ^ (m + 1) ∣ d), (F d).card) ≤ 5) :
    ∃ lam : ℤ, ¬ (7 : ℤ) ∣ lam ∧ ∀ d ∈ D, qz m (lam * d) ∉ F d := by
  classical
  suffices H : ∀ t : ℕ, ∃ lam : ℤ, ¬ (7 : ℤ) ∣ lam ∧
      ∀ d ∈ D, (7 : ℤ) ^ (m + 1 - t) ∣ d → qz m (lam * d) ∉ F d by
    obtain ⟨lam, hu, hd⟩ := H (m + 1)
    exact ⟨lam, hu, fun d hdD => hd d hdD (by simpa using one_dvd d)⟩
  intro t
  induction t with
  | zero =>
    exact ⟨1, by norm_num, fun d hdD hdvd => absurd (by simpa using hdvd) (hmax d hdD)⟩
  | succ t ih =>
    obtain ⟨lam, hu, hd⟩ := ih
    rcases Nat.lt_or_ge t (m + 1) with ht | ht
    · -- new level `j = m - t`
      set j := m - t with hj
      have hjm : j ≤ m := by omega
      have hj1 : m + 1 - t = j + 1 := by omega
      have hj0 : m + 1 - (t + 1) = j := by omega
      -- slopes
      set s := D.filter (fun d => (7 : ℤ) ^ j ∣ d ∧ ¬ (7 : ℤ) ^ (j + 1) ∣ d) with hs
      set cf : ℤ → ZMod 7 := fun d => qz m (lam * d) with hcf
      set rf : ℤ → ZMod 7 := fun d => (lam : ZMod 7) * ((d / 7 ^ j : ℤ) : ZMod 7) with hrf
      have hlamz : (lam : ZMod 7) ≠ 0 := by
        rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact_mod_cast hu
      -- the slope is a unit on level-`j` elements
      have hru : ∀ d ∈ s, rf d ≠ 0 := by
        intro d hd_s
        rw [hs, mem_filter] at hd_s
        obtain ⟨hdD, hjd, hnj1⟩ := hd_s
        refine mul_ne_zero hlamz ?_
        rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
        intro hdiv
        apply hnj1
        obtain ⟨e, he⟩ := hdiv
        refine ⟨e, ?_⟩
        have hdd : d = 7 ^ j * (d / 7 ^ j) := (Int.mul_ediv_cancel' hjd).symm
        rw [hdd, he]; ring
      -- key: from `7^(j+1) ∣ d` (and `7^j ∣ d`) the slope vanishes
      have hslope0 : ∀ d, (7 : ℤ) ^ j ∣ d → (7 : ℤ) ^ (j + 1) ∣ d → rf d = 0 := by
        intro d hjd hj1d
        have h7 : (7 : ℤ) ∣ d / 7 ^ j := by
          obtain ⟨e, he⟩ := hj1d
          refine ⟨e, ?_⟩
          rw [he, pow_succ, mul_assoc, Int.mul_ediv_cancel_left _ (pow_ne_zero j (by norm_num))]
        rw [hrf]
        simp only [mul_eq_zero]
        right
        rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; exact_mod_cast h7
      -- choose the coefficient and assemble the new multiplier
      by_cases hjeq : j = m
      · -- top level: exclude `k = 6` so the multiplier stays a unit
        have hsum_s : (∑ d ∈ s, (F d).card) ≤ 5 := by rw [hs, hjeq]; exact hhi
        obtain ⟨k, hk6, havoid⟩ := single_level_avoid_excl s cf rf F 6 hru hsum_s
        refine ⟨(1 + (k.val : ℤ) * 7 ^ (m - j)) * lam, ?_, ?_⟩
        · -- unit (`1 + k·7^0 = 1 + k ≠ 0` since `k ≠ 6`)
          have hlam'0 : (((1 + (k.val : ℤ) * 7 ^ (m - j)) * lam : ℤ) : ZMod 7) ≠ 0 := by
            push_cast [natCast_val]
            refine mul_ne_zero ?_ hlamz
            rw [show m - j = 0 by omega, pow_zero, mul_one]
            intro h
            apply hk6
            have hk : k = -1 := by linear_combination h
            rw [hk]; decide
          exact fun hdvd => hlam'0 ((ZMod.intCast_zmod_eq_zero_iff_dvd _ 7).mpr (by exact_mod_cast hdvd))
        · intro d hdD hjd
          rw [hj0] at hjd
          have hstep := qz_step m j hjm (k.val : ℤ) lam d hjd
          rw [show (1 + (k.val : ℤ) * 7 ^ (m - j)) * lam * d
                = (1 + (k.val : ℤ) * 7 ^ (m - j)) * (lam * d) by ring, hstep]
          rw [intCast_val]
          by_cases hj1d : (7 : ℤ) ^ (j + 1) ∣ d
          · have := hslope0 d hjd hj1d
            rw [show (lam : ZMod 7) * ((d / 7 ^ j : ℤ) : ZMod 7) = rf d from rfl, this,
              mul_zero, add_zero]
            exact hd d hdD (by rw [hj1]; exact hj1d)
          · have hd_s : d ∈ s := by rw [hs, mem_filter]; exact ⟨hdD, hjd, hj1d⟩
            have := havoid d hd_s
            rwa [show (lam : ZMod 7) * ((d / 7 ^ j : ℤ) : ZMod 7) = rf d from rfl,
              show qz m (lam * d) = cf d from rfl]
      · -- inner level `j < m`: any coefficient keeps the multiplier a unit
        have hjlt : j < m := lt_of_le_of_ne hjm hjeq
        have hsum_s : (∑ d ∈ s, (F d).card) ≤ 6 := by rw [hs]; exact hlo j hjlt
        obtain ⟨k, havoid⟩ := single_level_avoid s cf rf F hru hsum_s
        have hmj : 1 ≤ m - j := by omega
        refine ⟨(1 + (k.val : ℤ) * 7 ^ (m - j)) * lam, ?_, ?_⟩
        · -- unit (multiplier ≡ 1 mod 7 since `m - j ≥ 1`)
          have hlam'0 : (((1 + (k.val : ℤ) * 7 ^ (m - j)) * lam : ℤ) : ZMod 7) ≠ 0 := by
            push_cast [natCast_val]
            refine mul_ne_zero ?_ hlamz
            rw [show (7 : ZMod 7) = 0 from by decide, zero_pow (show m - j ≠ 0 by omega),
              mul_zero, add_zero]
            exact one_ne_zero
          exact fun hdvd => hlam'0 ((ZMod.intCast_zmod_eq_zero_iff_dvd _ 7).mpr (by exact_mod_cast hdvd))
        · intro d hdD hjd
          rw [hj0] at hjd
          have hstep := qz_step m j hjm (k.val : ℤ) lam d hjd
          rw [show (1 + (k.val : ℤ) * 7 ^ (m - j)) * lam * d
                = (1 + (k.val : ℤ) * 7 ^ (m - j)) * (lam * d) by ring, hstep]
          rw [intCast_val]
          by_cases hj1d : (7 : ℤ) ^ (j + 1) ∣ d
          · have := hslope0 d hjd hj1d
            rw [show (lam : ZMod 7) * ((d / 7 ^ j : ℤ) : ZMod 7) = rf d from rfl, this,
              mul_zero, add_zero]
            exact hd d hdD (by rw [hj1]; exact hj1d)
          · have hd_s : d ∈ s := by rw [hs, mem_filter]; exact ⟨hdD, hjd, hj1d⟩
            have := havoid d hd_s
            rwa [show (lam : ZMod 7) * ((d / 7 ^ j : ℤ) : ZMod 7) = rf d from rfl,
              show qz m (lam * d) = cf d from rfl]
    · -- `t > m`: nothing new to handle
      refine ⟨lam, hu, fun d hdD hdvd => hd d hdD ?_⟩
      have h1 : m + 1 - t = 0 := by omega
      have h2 : m + 1 - (t + 1) = 0 := by omega
      rw [h1]; rw [h2] at hdvd; exact hdvd

/-- A top-level element (`7^m ∥ d`) multiplied by a unit lands in the central
band: `(lam·d)_N = 7^m·((lam·u) mod 7)` with `(lam·u) mod 7 ∈ {1,…,6}`. -/
theorem band_top (m : ℕ) (lam d : ℤ) (hlam : ¬ (7 : ℤ) ∣ lam)
    (hd : (7 : ℤ) ^ m ∣ d) (hnd : ¬ (7 : ℤ) ^ (m + 1) ∣ d) :
    (7 : ℤ) ^ m ≤ (lam * d) % 7 ^ (m + 1) ∧ (lam * d) % 7 ^ (m + 1) ≤ 6 * 7 ^ m := by
  obtain ⟨u, hu⟩ := hd
  have h7m : (0 : ℤ) < 7 ^ m := by positivity
  have hnu : ¬ (7 : ℤ) ∣ u := fun hh => by
    obtain ⟨e, he⟩ := hh; exact hnd ⟨e, by rw [hu, he, pow_succ]; ring⟩
  have hp7 : Prime (7 : ℤ) := Nat.prime_iff_prime_int.mp (by decide)
  have hnlu : ¬ (7 : ℤ) ∣ lam * u := fun hh => by
    rcases hp7.dvd_or_dvd hh with h | h
    · exact hlam h
    · exact hnu h
  have hmod : (lam * d) % 7 ^ (m + 1) = 7 ^ m * ((lam * u) % 7) := by
    rw [hu, show lam * (7 ^ m * u) = 7 ^ m * (lam * u) by ring,
      show (7 : ℤ) ^ (m + 1) = 7 ^ m * 7 by ring]
    exact Int.mul_emod_mul_of_pos (lam * u) 7 h7m
  have hr0 : 0 ≤ (lam * u) % 7 := Int.emod_nonneg _ (by norm_num)
  have hr7 : (lam * u) % 7 < 7 := Int.emod_lt_of_pos _ (by norm_num)
  have hrne : (lam * u) % 7 ≠ 0 := fun h => hnlu (Int.dvd_of_emod_eq_zero h)
  have hr1 : 1 ≤ (lam * u) % 7 := by omega
  have hr6 : (lam * u) % 7 ≤ 6 := by omega
  rw [hmod]
  exact ⟨by nlinarith [mul_le_mul_of_nonneg_left hr1 (le_of_lt h7m)],
    by nlinarith [mul_le_mul_of_nonneg_left hr6 (le_of_lt h7m)]⟩

/-- **Corollary 3** (`i₀ = m`). If every valuation level below the top has at most
`3` elements, there is a multiplier `lam` (coprime to 7) sending every residue
`(lam·d)_N` into the central band `[7^m, 6·7^m]`. The top-level elements are kept
good by `band_top`; the lower levels by `prime_filtering` with `F_d = {0,6}`. -/
theorem corollary3 (m : ℕ) (D : Finset ℤ)
    (hmax : ∀ d ∈ D, ¬ (7 : ℤ) ^ (m + 1) ∣ d)
    (hsmall : ∀ j, j < m →
      (D.filter (fun d => (7 : ℤ) ^ j ∣ d ∧ ¬ (7 : ℤ) ^ (j + 1) ∣ d)).card ≤ 3) :
    ∃ lam : ℤ, ¬ (7 : ℤ) ∣ lam ∧
      ∀ d ∈ D, (7 : ℤ) ^ m ≤ (lam * d) % 7 ^ (m + 1) ∧ (lam * d) % 7 ^ (m + 1) ≤ 6 * 7 ^ m := by
  classical
  set top : ℤ → Prop := fun d => (7 : ℤ) ^ m ∣ d ∧ ¬ (7 : ℤ) ^ (m + 1) ∣ d with htop_def
  set F : ℤ → Finset (ZMod 7) := fun d => if top d then ∅ else {0, 6} with hF
  -- lower levels: `F_d = {0,6}`, sum `= 2·|level| ≤ 6`
  have Hlo : ∀ j, j < m →
      (∑ d ∈ D.filter (fun d => (7 : ℤ) ^ j ∣ d ∧ ¬ (7 : ℤ) ^ (j + 1) ∣ d), (F d).card) ≤ 6 := by
    intro j hjm
    have hcard : ∀ d ∈ D.filter (fun d => (7 : ℤ) ^ j ∣ d ∧ ¬ (7 : ℤ) ^ (j + 1) ∣ d),
        (F d).card = 2 := by
      intro d hd
      rw [mem_filter] at hd
      have hntop : ¬ top d := by
        rintro ⟨hm, -⟩
        exact hd.2.2 (dvd_trans (pow_dvd_pow 7 (by omega)) hm)
      simp only [hF]; rw [if_neg hntop]; decide
    calc (∑ d ∈ D.filter (fun d => (7 : ℤ) ^ j ∣ d ∧ ¬ (7 : ℤ) ^ (j + 1) ∣ d), (F d).card)
        = ∑ _d ∈ D.filter (fun d => (7 : ℤ) ^ j ∣ d ∧ ¬ (7 : ℤ) ^ (j + 1) ∣ d), 2 :=
          Finset.sum_congr rfl hcard
      _ = 2 * (D.filter (fun d => (7 : ℤ) ^ j ∣ d ∧ ¬ (7 : ℤ) ^ (j + 1) ∣ d)).card := by
          rw [Finset.sum_const, smul_eq_mul]; ring
      _ ≤ 6 := by have := hsmall j hjm; omega
  -- top level: `F_d = ∅`, sum `= 0 ≤ 5`
  have Hhi : (∑ d ∈ D.filter (fun d => (7 : ℤ) ^ m ∣ d ∧ ¬ (7 : ℤ) ^ (m + 1) ∣ d), (F d).card) ≤ 5 := by
    have hcard : ∀ d ∈ D.filter (fun d => (7 : ℤ) ^ m ∣ d ∧ ¬ (7 : ℤ) ^ (m + 1) ∣ d),
        (F d).card = 0 := by
      intro d hd
      rw [mem_filter] at hd
      simp only [hF]; rw [if_pos hd.2]; rfl
    calc (∑ d ∈ D.filter (fun d => (7 : ℤ) ^ m ∣ d ∧ ¬ (7 : ℤ) ^ (m + 1) ∣ d), (F d).card)
        = ∑ _d ∈ D.filter (fun d => (7 : ℤ) ^ m ∣ d ∧ ¬ (7 : ℤ) ^ (m + 1) ∣ d), 0 :=
          Finset.sum_congr rfl hcard
      _ ≤ 5 := by rw [Finset.sum_const_zero]; omega
  obtain ⟨lam, hlam, hq⟩ := prime_filtering m D F hmax Hlo Hhi
  refine ⟨lam, hlam, fun d hdD => ?_⟩
  by_cases hdtop : top d
  · exact band_top m lam d hlam hdtop.1 hdtop.2
  · have hFd : F d = {0, 6} := by simp only [hF]; exact if_neg hdtop
    have hmem := hq d hdD
    rw [hFd] at hmem
    have h0 : qz m (lam * d) ≠ 0 := fun h => hmem (by rw [h]; decide)
    have h6 : qz m (lam * d) ≠ 6 := fun h => hmem (by rw [h]; decide)
    exact band_of_qz_ne m (lam * d) h0 h6

end IntLRC7BS
