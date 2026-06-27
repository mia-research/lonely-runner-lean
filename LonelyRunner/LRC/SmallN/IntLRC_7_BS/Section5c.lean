import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic

/-!
# n = 7 (Barajas–Serra) — §5 interior element handling (eq 8)

Source: `sources_barajas_serra_2008.txt`, lines 269–273.

For an interior element d₅ ∈ D₇(i₀) with 0 < i₀ < m, BS constructs a
pre-multiplier `pre = u₀·(1+7^{m-i₀})` where u₀ is the modular inverse of the
unit part of d₅. The key identity: `pre·d₅ ≡ 7^{i₀}+7^m (mod 7^{m+1})`,
whence `j·pre·d₅` lands in band `[7^m, 6·7^m]` for 1 ≤ j ≤ 5.
-/

namespace IntLRC7BS

/-- Band condition for j·(7^{i₀}+7^m) with 1 ≤ j ≤ 5, 1 ≤ i₀ < m. -/
theorem interior_in_band (j i₀ m : ℕ) (hj1 : 1 ≤ j) (hj5 : j ≤ 5)
    (hi1 : 1 ≤ i₀) (him : i₀ < m) :
    (7 : ℤ) ^ m ≤ (j : ℤ) * ((7 : ℤ) ^ i₀ + (7 : ℤ) ^ m) ∧
    (j : ℤ) * ((7 : ℤ) ^ i₀ + (7 : ℤ) ^ m) ≤ 6 * (7 : ℤ) ^ m ∧
    (j : ℤ) * ((7 : ℤ) ^ i₀ + (7 : ℤ) ^ m) < (7 : ℤ) ^ (m + 1) ∧
    0 ≤ (j : ℤ) * ((7 : ℤ) ^ i₀ + (7 : ℤ) ^ m) := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 2 := ⟨m - 2, by omega⟩
  have hi_le : i₀ ≤ m' + 1 := by omega
  have h7i : (7 : ℤ) ^ i₀ ≤ 7 ^ (m' + 1) := by
    exact_mod_cast Nat.pow_le_pow_right (by norm_num : 1 ≤ 7) hi_le
  have h7pos : (0 : ℤ) < 7 ^ (m' + 1) := by positivity
  have h7m : (7 : ℤ) ^ (m' + 2) = 7 * 7 ^ (m' + 1) := by ring
  have h7m1 : (7 : ℤ) ^ (m' + 2 + 1) = 49 * 7 ^ (m' + 1) := by ring
  refine ⟨?_, ?_, ?_, by positivity⟩
  · have : (7 : ℤ) ^ i₀ ≥ 7 := by
      calc (7 : ℤ) ^ i₀ ≥ 7 ^ 1 := by
            exact_mod_cast Nat.pow_le_pow_right (by norm_num : 1 ≤ 7) hi1
           _ = 7 := by norm_num
    nlinarith
  · nlinarith
  · nlinarith

set_option maxHeartbeats 400000 in
/-- Pre-multiplier existence for interior elements (BS eq 8).
Given d with 7∣d and ¬7^m∣d, produces `pre` coprime to 7 with
pre * d ≡ 7^i₀ + 7^m (mod 7^(m+1)) where i₀ = ν₇(d). -/
theorem exists_pre_congr (m : ℕ) (d : ℕ) (hd : 0 < d)
    (h7 : 7 ∣ d) (hm' : ¬ (7 : ℕ) ^ m ∣ d) :
    ∃ (pre : ℤ) (i₀ : ℕ), ¬ (7 : ℤ) ∣ pre ∧ 1 ≤ i₀ ∧ i₀ < m ∧
      (7 : ℤ) ^ (m + 1) ∣ (pre * (d : ℤ) - ((7 : ℤ) ^ i₀ + (7 : ℤ) ^ m)) := by
  haveI : Fact (Nat.Prime 7) := ⟨by decide⟩
  set v := padicValNat 7 d
  set u := d / 7 ^ v
  have hv1 : 1 ≤ v := (padicValNat_dvd_iff_le hd.ne').mp h7
  have hvm : v < m := by
    by_contra h; push_neg at h; exact hm' ((padicValNat_dvd_iff_le hd.ne').mpr h)
  have hdu : d = 7 ^ v * u := (Nat.mul_div_cancel' pow_padicValNat_dvd).symm
  have hu7 : ¬ 7 ∣ u := by
    intro h; exact absurd ((padicValNat_dvd_iff_le hd.ne').mp
      (show 7 ^ (v + 1) ∣ d from pow_succ 7 v ▸ Nat.mul_dvd_of_dvd_div pow_padicValNat_dvd h))
      (by omega)
  have hcop : Nat.Coprime u (7 ^ (m + 1 - v)) :=
    ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hu7).symm.pow_right _
  obtain ⟨u₀, hu₀⟩ := Int.mod_coprime hcop
  have hinv : (7 : ℤ) ^ (m + 1 - v) ∣ ((u : ℤ) * u₀ - 1) := by
    rw [show (7 : ℤ) ^ (m + 1 - v) = ((7 ^ (m + 1 - v) : ℕ) : ℤ) from by push_cast; ring]
    exact Int.ModEq.dvd hu₀.symm
  set pre := u₀ * (1 + (7 : ℤ) ^ (m - v))
  refine ⟨pre, v, ?_, hv1, hvm, ?_⟩
  · intro h7pre
    have hu₀_ndvd : ¬ (7 : ℤ) ∣ u₀ := by
      intro h; exact (show ¬ (7 : ℤ) ∣ (u : ℤ) from by exact_mod_cast hu7) <| by
        have := Int.dvd_sub (dvd_mul_of_dvd_right h (u : ℤ))
          (dvd_trans (dvd_pow_self 7 (by omega)) hinv); simp at this
    have h1_ndvd : ¬ (7 : ℤ) ∣ (1 + (7 : ℤ) ^ (m - v)) := by
      intro ⟨c, hc⟩
      exact absurd ((dvd_add_right (dvd_pow_self 7 (by omega : m - v ≠ 0))).mp
        ⟨c, by linarith⟩) (by norm_num : ¬ (7 : ℤ) ∣ 1)
    exact absurd ((Prime.dvd_mul (by norm_num : Prime (7 : ℤ))).mp h7pre) (by tauto)
  · obtain ⟨w, hw⟩ := hinv
    have hdu' : (d : ℤ) = (7 : ℤ) ^ v * (u : ℤ) := by exact_mod_cast hdu
    have huu₀ : (u : ℤ) * u₀ = 1 + (7 : ℤ) ^ (m + 1 - v) * w := by linarith
    refine ⟨w * (1 + (7 : ℤ) ^ (m - v)), ?_⟩
    rw [hdu', show (7 : ℤ) ^ (m + 1) = (7 : ℤ) ^ (m + 1 - v) * (7 : ℤ) ^ v from by
      rw [← pow_add]; congr 1; omega]
    rw [show (7 : ℤ) ^ m = (7 : ℤ) ^ (m - v) * (7 : ℤ) ^ v from by
      rw [← pow_add]; congr 1; omega]
    linear_combination (7 : ℤ) ^ v * (1 + (7 : ℤ) ^ (m - v)) * huu₀

/-- Band-lifting: if `lam·d'` is in band at level `m'`, then `lam·(7^j₀·d')` is
in band at level `j₀ + m'`. -/
theorem band_lift (j₀ m' : ℕ) (lam d' : ℤ)
    (hband : (7 : ℤ) ^ m' ≤ (lam * d') % (7 : ℤ) ^ (m' + 1) ∧
      (lam * d') % (7 : ℤ) ^ (m' + 1) ≤ 6 * (7 : ℤ) ^ m') :
    (7 : ℤ) ^ (j₀ + m') ≤ (lam * ((7 : ℤ) ^ j₀ * d')) % (7 : ℤ) ^ (j₀ + m' + 1) ∧
    (lam * ((7 : ℤ) ^ j₀ * d')) % (7 : ℤ) ^ (j₀ + m' + 1) ≤
      6 * (7 : ℤ) ^ (j₀ + m') := by
  set r := (lam * d') % (7 : ℤ) ^ (m' + 1)
  have hr0 : 0 ≤ r := Int.emod_nonneg _ (by positivity)
  have hrN : r < (7 : ℤ) ^ (m' + 1) := Int.emod_lt_of_pos _ (by positivity)
  have hkey : (lam * ((7 : ℤ) ^ j₀ * d')) % (7 : ℤ) ^ (j₀ + m' + 1) =
      (7 : ℤ) ^ j₀ * r := by
    have hfact : lam * ((7 : ℤ) ^ j₀ * d') = (7 : ℤ) ^ j₀ * (lam * d') := by ring
    rw [hfact]
    have hNfact : (7 : ℤ) ^ (j₀ + m' + 1) = (7 : ℤ) ^ j₀ * (7 : ℤ) ^ (m' + 1) := by
      rw [← pow_add]; congr 1
    rw [hNfact, Int.mul_emod_mul_of_pos _ _ (by positivity : (0 : ℤ) < 7 ^ j₀)]
  rw [hkey, show (7 : ℤ) ^ (j₀ + m') = (7 : ℤ) ^ j₀ * (7 : ℤ) ^ m' from by
    rw [← pow_add]]
  have h7pos : (0 : ℤ) ≤ 7 ^ j₀ := by positivity
  constructor
  · exact mul_le_mul_of_nonneg_left hband.1 h7pos
  · calc (7 : ℤ) ^ j₀ * r ≤ (7 : ℤ) ^ j₀ * (6 * (7 : ℤ) ^ m') :=
          mul_le_mul_of_nonneg_left hband.2 h7pos
      _ = 6 * ((7 : ℤ) ^ j₀ * (7 : ℤ) ^ m') := by ring

/-- Multiplying by `1+k·7^m` doesn't change the mod-`7^(m+1)` residue when `7∣d`. -/
theorem lambda0_inert (m : ℕ) (k lam d : ℤ) (h7 : (7 : ℤ) ∣ d) :
    ((1 + k * (7 : ℤ) ^ m) * lam * d) % (7 : ℤ) ^ (m + 1) =
    (lam * d) % (7 : ℤ) ^ (m + 1) := by
  obtain ⟨c, hc⟩ := h7
  have hrw : (1 + k * (7 : ℤ) ^ m) * lam * d =
      lam * d + k * lam * c * (7 : ℤ) ^ (m + 1) := by rw [hc, pow_succ]; ring
  rw [hrw, show lam * d + k * lam * c * (7 : ℤ) ^ (m + 1) =
      lam * d + (k * lam * c) * (7 : ℤ) ^ (m + 1) from by ring,
    Int.add_mul_emod_self_right]

/-- Coprimality of `1+k·7^m` to 7 for any `k`. -/
theorem lambda0_coprime (m : ℕ) (hm : 0 < m) (k : ℤ) :
    ¬ (7 : ℤ) ∣ (1 + k * (7 : ℤ) ^ m) := by
  intro ⟨c, hc⟩
  have h7m : (7 : ℤ) ∣ (7 : ℤ) ^ m := dvd_pow_self 7 (by omega : m ≠ 0)
  have : (7 : ℤ) ∣ 1 := (dvd_add_right (dvd_mul_of_dvd_left h7m k)).mp ⟨c, by linarith⟩
  exact absurd this (by norm_num)

end IntLRC7BS
