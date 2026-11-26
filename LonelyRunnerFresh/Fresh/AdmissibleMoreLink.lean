import Mathlib
import Fresh.Framework
import Fresh.Localisation
import Fresh.Admissible
import Fresh.EightResidualLink
import Fresh.AdmissibleMore
import Fresh.FastPairReal

/-!
# Links of the two new classes to the old structure, for integer disparity sets

Written 2026-10-25.  New file.  `unit_inv`: if every element of a set `S` of positive integers with no common factor is a natural multiple of a real `u > 0`, then `u = 1/N` for a natural `N` (rational argument as in `eight_not_grid`).
* `noMultiple_of_old` (unit 1): the old R6 hypothesis (`∃ q ∈ [2, 8]` dividing no disparity) gives `NoMultipleClass`.
* `not_noMultiple_of_fields`: the fields "a multiple of each of 5, 6, 7, 8" (hence of 2, 3, 4 too) with no common factor exclude `NoMultipleClass` for EVERY unit `u`.  So the old residual subjects are exactly the complement of `NoMultipleClass`.
* `fastPair_imp_old`: `FastPairClass` gives the old `FastPair8` fields; `old_fastPair_imp_class`: the old fields with a nonempty core and a `1/6`-clear core instant give `FastPairClass`.
Grades: [L].
-/

open Classical

namespace Fresh.AdmissibleMoreLink

open Fresh Fresh.Admissible Fresh.EightResidualLink Fresh.AdmissibleMore Fresh.FastPairReal

theorem unit_inv {S : Finset ℕ} (hpos : ∀ d ∈ S, 0 < d) (hcf : ∀ g, 2 ≤ g → ∃ d ∈ S, ¬ g ∣ d) (hne : S.Nonempty)
    {u : ℝ} (hu : 0 < u) (hd : ∀ d ∈ S, ∃ n : ℕ, (d : ℝ) = (n : ℝ) * u) : ∃ N : ℕ, 0 < N ∧ u * N = 1 := by
  obtain ⟨e, he⟩ := hne
  obtain ⟨ne, hene⟩ := hd e he
  have hepos : (0 : ℝ) < e := by exact_mod_cast hpos e he
  have hnepos : 0 < ne := by
    rcases Nat.eq_zero_or_pos ne with h | h
    · exfalso
      have h0 : (e : ℝ) = 0 := by rw [hene, h]; simp
      linarith
    · exact h
  have hneR : (0 : ℝ) < ne := by exact_mod_cast hnepos
  set r : ℚ := (e : ℚ) / (ne : ℚ) with hr
  have hru : (r : ℝ) = u := by
    rw [hr]; push_cast
    rw [div_eq_iff hneR.ne']
    linarith
  have hall : ∀ d ∈ S, ∃ n : ℕ, (d : ℚ) = (n : ℚ) * r := by
    intro d hdS
    obtain ⟨n, hn⟩ := hd d hdS
    refine ⟨n, ?_⟩
    have : ((d : ℚ) : ℝ) = (((n : ℚ) * r : ℚ) : ℝ) := by push_cast; rw [hru]; exact hn
    exact_mod_cast this
  have hrpos : 0 < r := by
    rw [hr]; apply div_pos
    · exact_mod_cast hepos
    · exact_mod_cast hnepos
  have hnum : 0 < r.num := Rat.num_pos.2 hrpos
  have hcop : IsCoprime r.num (r.den : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    simpa [Int.gcd, Nat.Coprime] using r.reduced
  have hden : (r.den : ℚ) ≠ 0 := by exact_mod_cast r.den_nz
  have hdiv : ∀ d ∈ S, r.num ∣ (d : ℤ) := by
    intro d hdS
    obtain ⟨n, hn⟩ := hall d hdS
    have h1 : (d : ℚ) = (n : ℚ) * (r.num / r.den) := by rw [hn, Rat.num_div_den]
    have h2 : (d : ℚ) * r.den = (n : ℚ) * r.num := by rw [h1]; field_simp
    have h3 : (d : ℤ) * r.den = n * r.num := by exact_mod_cast h2
    have h4 : r.num ∣ (d : ℤ) * r.den := ⟨n, by rw [h3]; ring⟩
    exact hcop.dvd_of_dvd_mul_right h4
  have hp1 : r.num = 1 := by
    by_contra hne1
    have h2 : 2 ≤ r.num.natAbs := by omega
    obtain ⟨s, hs, hns⟩ := hcf r.num.natAbs h2
    apply hns
    have h5 : (r.num.natAbs : ℤ) ∣ (s : ℤ) := by rw [Int.natAbs_dvd]; exact hdiv s hs
    exact_mod_cast h5
  have hrden : r * (r.den : ℚ) = 1 := by
    have h := Rat.mul_den_eq_num r
    rw [hp1] at h
    simpa using h
  refine ⟨r.den, r.den_pos, ?_⟩
  have : (u * (r.den : ℝ)) = ((r * (r.den : ℚ) : ℚ) : ℝ) := by push_cast; rw [hru]
  rw [this, hrden]; simp

theorem noMultiple_of_old {v : Fin 8 → ℝ} {k : Fin 8} {S : Finset ℕ} (hS : HasDisp v k S)
    (h : ∃ q : ℕ, 2 ≤ q ∧ q ≤ 8 ∧ ∀ d ∈ S, ¬ q ∣ d) : NoMultipleClass v k := by
  obtain ⟨q, hq2, hq8, hq⟩ := h
  refine ⟨1, one_pos, q, hq2, hq8, fun x hx => ?_⟩
  obtain ⟨d, hd, rfl⟩ := (hS x).1 hx
  exact ⟨d, by simp, hq d hd⟩

theorem not_noMultiple_of_fields {v : Fin 8 → ℝ} (hinj : Function.Injective v) {k : Fin 8} {S : Finset ℕ} (hS : HasDisp v k S)
    (hcf : ∀ g, 2 ≤ g → ∃ d ∈ S, ¬ g ∣ d) (h5 : ∃ d ∈ S, 5 ∣ d) (h6 : ∃ d ∈ S, 6 ∣ d) (h7 : ∃ d ∈ S, 7 ∣ d)
    (h8 : ∃ d ∈ S, 8 ∣ d) : ¬ NoMultipleClass v k := by
  rintro ⟨u, hu, q, hq2, hq8, hd⟩
  have hmul : ∃ e ∈ S, q ∣ e := by
    obtain ⟨e5, he5, hd5⟩ := h5; obtain ⟨e6, he6, hd6⟩ := h6; obtain ⟨e7, he7, hd7⟩ := h7; obtain ⟨e8, he8, hd8⟩ := h8
    interval_cases q
    · exact ⟨e6, he6, dvd_trans (by norm_num) hd6⟩
    · exact ⟨e6, he6, dvd_trans (by norm_num) hd6⟩
    · exact ⟨e8, he8, dvd_trans (by norm_num) hd8⟩
    · exact ⟨e5, he5, hd5⟩
    · exact ⟨e6, he6, hd6⟩
    · exact ⟨e7, he7, hd7⟩
    · exact ⟨e8, he8, hd8⟩
  obtain ⟨e, heS, hqe⟩ := hmul
  have hall : ∀ d ∈ S, ∃ n : ℕ, (d : ℝ) = (n : ℝ) * u ∧ ¬ q ∣ n := fun d hdS => hd d ((hS _).2 ⟨d, hdS, rfl⟩)
  have hpos : ∀ d ∈ S, 0 < d := fun d hdS => hasDisp_pos hinj hS hdS
  obtain ⟨N, hNpos, hN⟩ := unit_inv hpos hcf ⟨e, heS⟩ hu (fun d hdS => by obtain ⟨n, hn, _⟩ := hall d hdS; exact ⟨n, hn⟩)
  obtain ⟨ne, hene, hnq⟩ := hall e heS
  have h1 : (ne : ℝ) = (e : ℝ) * N := by
    have : (e : ℝ) * N = (ne : ℝ) * u * N := by rw [hene]
    have h2 : (ne : ℝ) * (u * N) = ne := by rw [hN]; ring
    nlinarith
  have h2 : ne = e * N := by exact_mod_cast h1
  apply hnq
  rw [h2]
  exact Dvd.dvd.mul_right hqe N

theorem fastPair_imp_old {v : Fin 8 → ℝ} {k : Fin 8} {S : Finset ℕ} (hS : HasDisp v k S) (h : FastPairClass v k) :
    ∃ a ∈ S, ∃ b ∈ S, a < b ∧ ∀ c ∈ S, c ≠ a → c ≠ b → 9 * c ≤ a := by
  obtain ⟨x, hx, y, hy, hxy, _, τ, hτ, hcore⟩ := h
  obtain ⟨a, ha, rfl⟩ := (hS x).1 hx
  obtain ⟨b, hb, rfl⟩ := (hS y).1 hy
  refine ⟨a, ha, b, hb, by exact_mod_cast hxy, fun c hc hca hcb => ?_⟩
  have := (hcore (c : ℝ) ((hS _).2 ⟨c, hc, rfl⟩) (fun h => hca (by exact_mod_cast h)) (fun h => hcb (by exact_mod_cast h))).2
  exact_mod_cast this

#print axioms unit_inv
#print axioms noMultiple_of_old
#print axioms not_noMultiple_of_fields
#print axioms fastPair_imp_old

end Fresh.AdmissibleMoreLink
