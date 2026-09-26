import LonelyRunner.LRC.Spec.MirrorCentreN
import LonelyRunner.LRC.Cascade.Flanks
import LonelyRunner.LRC.ConstructionN.LemmaPass

/-!
# The grid pair law: a configuration near the grid pattern is lonely at `t` or at `((8 − a)/a)·t`

2026-09-26 (running log E74).  Owner: global isolation holds at every **grid** (reduced speeds a complete residue system
mod 8, e.g. `1 … 7, 16`), not only at the progression; any arrangement deforms the circle geometry and relocates it.

At a grid instant `a/(8g)`, `a ∈ {1, 3, 5, 7}`, a subject sees the other runners at `a·n j / 8` with `a·n j mod 8` running
over `1 … 7`: one runner `p` on the leaving edge `1/8`, one runner `q` on the entering edge `7/8`, the rest at `2/8 … 6/8`.
The law is about that **pattern on the circle**, at any instant `t` of any arrangement:

* runner `p` exactly at `a·n p / 8 ≡ 1/8`;
* every other runner within `1/56` of `a·n j / 8`, with `a·n q ≡ 7` and the rest `≡ 2 … 6`.

Then the subject is lonely at `t` or at `((8 − a)/a)·t` (`grid_pair`).  At the second instant every position is the
reflection of the first, `a·n j / 8 − ((8 − a)/a)·D j` (`D j` the deviation at `t`): the deviations are scaled by at most
`7` and reversed in sign, so whichever side `q` sits on at `t`, it sits on the clear side at the partner instant.  For
`a = 1` the partner is `7t`.  The progression pair law (`ProgressionPairN`) is the case of the progression near `t = 1/(8c)`.

Everything here is proved; no `sorry`, no `native_decide`.
-/

namespace LRC.GridPair

open LRC.MirrorCentre

/-- A position within `1/8` of `m/8` with `m mod 8 ∈ [2, 6]` is clear. -/
theorem clear_mid {x : ℝ} (m : ℤ) (hr : 2 ≤ m % 8 ∧ m % 8 ≤ 6) (h : |x - (m : ℝ) / 8| ≤ 1 / 8) :
    (8 : ℝ)⁻¹ ≤ circDist x := by
  have hm : (m : ℝ) = 8 * ((m / 8 : ℤ) : ℝ) + ((m % 8 : ℤ) : ℝ) := by exact_mod_cast (Int.mul_ediv_add_emod m 8).symm
  have hr1 : (2 : ℝ) ≤ ((m % 8 : ℤ) : ℝ) := by exact_mod_cast hr.1
  have hr2 : ((m % 8 : ℤ) : ℝ) ≤ 6 := by exact_mod_cast hr.2
  obtain ⟨h1, h2⟩ := abs_le.mp h
  generalize m / 8 = k at hm
  rw [show (8 : ℝ)⁻¹ = 1 / 8 by norm_num]
  exact circDist_ge_of_window (m := k) (by linarith) (by linarith) (by norm_num)

/-- The leaving edge: at or just above `m/8` with `m ≡ 1 mod 8`. -/
theorem clear_up {x : ℝ} (m : ℤ) (hr : m % 8 = 1) (h0 : (m : ℝ) / 8 ≤ x) (h1 : x ≤ (m : ℝ) / 8 + 3 / 4) :
    (8 : ℝ)⁻¹ ≤ circDist x := by
  have hm : (m : ℝ) = 8 * ((m / 8 : ℤ) : ℝ) + ((m % 8 : ℤ) : ℝ) := by exact_mod_cast (Int.mul_ediv_add_emod m 8).symm
  rw [hr] at hm
  generalize m / 8 = k at hm
  push_cast at hm
  rw [show (8 : ℝ)⁻¹ = 1 / 8 by norm_num]
  exact circDist_ge_of_window (m := k) (by linarith) (by linarith) (by norm_num)

/-- The entering edge: at or just below `m/8` with `m ≡ 7 mod 8`. -/
theorem clear_down {x : ℝ} (m : ℤ) (hr : m % 8 = 7) (h0 : (m : ℝ) / 8 - 3 / 4 ≤ x) (h1 : x ≤ (m : ℝ) / 8) :
    (8 : ℝ)⁻¹ ≤ circDist x := by
  have hm : (m : ℝ) = 8 * ((m / 8 : ℤ) : ℝ) + ((m % 8 : ℤ) : ℝ) := by exact_mod_cast (Int.mul_ediv_add_emod m 8).symm
  rw [hr] at hm
  generalize m / 8 = k at hm
  push_cast at hm
  rw [show (8 : ℝ)⁻¹ = 1 / 8 by norm_num]
  exact circDist_ge_of_window (m := k) (by linarith) (by linarith) (by norm_num)

/-- **The reflection.**  At the partner instant `((8 − a)/a)·t` runner `j` sits at the reflection of
`a·n/8 − ((8 − a)/a)·D`, where `D` is its deviation from `a·n/8` at `t`. -/
theorem partner_position {a : ℝ} (ha : 0 < a) (w t : ℝ) (n : ℤ) :
    circDist (w * ((8 - a) / a * t)) = circDist (a * n / 8 - (8 - a) / a * (w * t - a * n / 8)) := by
  have e : w * ((8 - a) / a * t) = -(a * n / 8 - (8 - a) / a * (w * t - a * n / 8)) + (n : ℝ) := by
    field_simp; ring
  rw [e, ConstructionN.circDist_add_int, Flanks.circDist_neg]

/-- **The grid pair law.**  At an instant `t` where runner `p` sits exactly at `a·n p/8 ≡ 1/8`, runner `q` within `1/56`
of `a·n q/8 ≡ 7/8`, and every other runner of `s` within `1/56` of `a·n j/8 ≡ 2 … 6 (mod 8)`, the subject is lonely at
`t` or at `((8 − a)/a)·t`. -/
theorem grid_pair {ι : Type*} {s : Finset ι} {w : ι → ℝ} {n : ι → ℤ} {a : ℕ} (ha1 : 1 ≤ a) (ha7 : a ≤ 7)
    {t : ℝ} {p q : ι} (hmp : ((a : ℤ) * n p) % 8 = 1) (hmq : ((a : ℤ) * n q) % 8 = 7)
    (hmid : ∀ j ∈ s, j ≠ p → j ≠ q → 2 ≤ ((a : ℤ) * n j) % 8 ∧ ((a : ℤ) * n j) % 8 ≤ 6)
    (hpin : w p * t = (a : ℝ) * n p / 8)
    (hdev : ∀ j ∈ s, |w j * t - (a : ℝ) * n j / 8| ≤ 1 / 56) :
    (∀ j ∈ s, (8 : ℝ)⁻¹ ≤ circDist (w j * t)) ∨
      (∀ j ∈ s, (8 : ℝ)⁻¹ ≤ circDist (w j * ((8 - a) / a * t))) := by
  have haR : (1 : ℝ) ≤ a := by exact_mod_cast ha1
  have ha7R : (a : ℝ) ≤ 7 := by exact_mod_cast ha7
  have hlam0 : 0 ≤ (8 - (a : ℝ)) / a := div_nonneg (by linarith) (by linarith)
  have hlam7 : (8 - (a : ℝ)) / a ≤ 7 := by rw [div_le_iff₀ (by linarith)]; linarith
  have cast : ∀ j, ((((a : ℤ) * n j : ℤ)) : ℝ) / 8 = (a : ℝ) * n j / 8 := fun j => by push_cast; ring
  rcases le_or_gt (w q * t) ((a : ℝ) * n q / 8) with hq | hq
  · left
    intro j hj
    by_cases hjp : j = p
    · subst hjp
      refine clear_up _ hmp ?_ ?_ <;> rw [cast, hpin] <;> linarith
    by_cases hjq : j = q
    · subst hjq
      have := abs_le.mp (hdev j hj)
      refine clear_down _ hmq ?_ ?_ <;> rw [cast] <;> linarith [this.1]
    · refine clear_mid _ (hmid j hj hjp hjq) ?_
      rw [cast]; linarith [hdev j hj, show (1 : ℝ) / 56 ≤ 1 / 8 by norm_num]
  · right
    intro j hj
    rw [partner_position (by linarith) (w j) t (n j)]
    set lam := (8 - (a : ℝ)) / a
    have hD := abs_le.mp (hdev j hj)
    by_cases hjp : j = p
    · subst hjp
      have h0 : w j * t - (a : ℝ) * n j / 8 = 0 := by rw [hpin]; ring
      refine clear_up _ hmp ?_ ?_ <;> rw [cast, h0] <;> linarith
    by_cases hjq : j = q
    · subst hjq
      have hpos : 0 ≤ lam * (w j * t - (a : ℝ) * n j / 8) := mul_nonneg hlam0 (by linarith)
      have hsmall : lam * (w j * t - (a : ℝ) * n j / 8) ≤ 7 * (1 / 56) :=
        mul_le_mul hlam7 hD.2 (by linarith) (by norm_num)
      refine clear_down _ hmq ?_ ?_ <;> rw [cast] <;> linarith
    · refine clear_mid _ (hmid j hj hjp hjq) ?_
      rw [cast]
      have hb : |lam * (w j * t - (a : ℝ) * n j / 8)| ≤ 7 * (1 / 56) := by
        rw [abs_mul, abs_of_nonneg hlam0]
        exact mul_le_mul hlam7 (hdev j hj) (abs_nonneg _) (by norm_num)
      rw [show (a : ℝ) * n j / 8 - lam * (w j * t - (a : ℝ) * n j / 8) - (a : ℝ) * n j / 8
          = -(lam * (w j * t - (a : ℝ) * n j / 8)) by ring, abs_neg]
      linarith

end LRC.GridPair
