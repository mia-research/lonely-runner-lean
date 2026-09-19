import Mathlib

/-!
# A flank has exactly `e` openings

For flank `e` and difference `d`, the reduced denominator is `q = e / gcd(d,e)`, and the
blocking pattern in the opening index has period `q`. The flank's own period is
`L = lcm_j q_j`, which divides `e`.

When the difference multiset has `gcd = 1` — the normalisation that costs nothing, since
scaling all differences scales every flank with them — **`L = e` exactly**. So flank `e`
carries exactly `e` openings, and `d_max` is the flank with the most.

The argument is elementary and avoids prime factorisation. Put `g_j = gcd(d_j, e)`, so
`g_j ∣ e` and `gcd_j g_j = gcd(gcd_j d_j, e) = gcd(1, e) = 1`. Each `e/g_j` divides `e`, so
`L ∣ e`; writing `m = e / L`, every `e/g_j` divides `e/m`, which forces `m ∣ g_j` for every
`j`, hence `m ∣ 1` and `L = e`.

*(Verified on 1,331,924 flanks before proving.)*
-/

namespace Openings

/-- The cancellation step, with no division lemmas: from `e = g*u`, `e = m*L` and `u ∣ L`
it follows that `m ∣ g`. -/
theorem dvd_of_div_dvd {e g u m L : ℕ} (he : 0 < e) (hgu : e = g * u) (hmL : e = m * L)
    (h : u ∣ L) : m ∣ g := by
  obtain ⟨t, rfl⟩ := h
  have hu : 0 < u := Nat.pos_of_ne_zero (by rintro rfl; omega)
  have h2 : g * u = (m * t) * u := by rw [← hgu, hmL]; ring
  exact ⟨t, Nat.eq_of_mul_eq_mul_right hu h2⟩

/-- The common period divides `e`. -/
theorem foldr_lcm_dvd {e : ℕ} : ∀ (gs : List ℕ), (∀ g ∈ gs, g ∣ e) →
    (gs.map (fun g => e / g)).foldr Nat.lcm 1 ∣ e
  | [], _ => by simp
  | g :: t, h => by
      simp only [List.map_cons, List.foldr_cons]
      exact Nat.lcm_dvd (Nat.div_dvd_of_dvd (h g (by simp)))
        (foldr_lcm_dvd t (fun x hx => h x (by simp [hx])))

/-- Each individual period divides the common period. -/
theorem dvd_foldr_lcm {e : ℕ} : ∀ (gs : List ℕ) (g : ℕ), g ∈ gs →
    e / g ∣ (gs.map (fun x => e / x)).foldr Nat.lcm 1
  | [], g, hg => by simp at hg
  | a :: t, g, hg => by
      simp only [List.map_cons, List.foldr_cons]
      rcases List.mem_cons.mp hg with rfl | h
      · exact Nat.dvd_lcm_left _ _
      · exact dvd_trans (dvd_foldr_lcm t g h) (Nat.dvd_lcm_right _ _)

/-- **A flank has exactly `e` openings.**  If every `g_j` divides `e` and the `g_j` have gcd
`1`, the common period `L = lcm_j (e/g_j)` is `e` itself.  Stated for a list. -/
theorem lcm_div_eq {e : ℕ} (he : 0 < e) (gs : List ℕ)
    (hdvd : ∀ g ∈ gs, g ∣ e) (hgcd : ∀ m : ℕ, (∀ g ∈ gs, m ∣ g) → m ∣ 1) :
    (gs.map (fun g => e / g)).foldr Nat.lcm 1 = e := by
  obtain ⟨m, hm⟩ := foldr_lcm_dvd gs hdvd
  have hmul : e = m * ((gs.map (fun g => e / g)).foldr Nat.lcm 1) :=
    hm.trans (Nat.mul_comm _ _)
  have hone : m ∣ 1 := by
    refine hgcd m (fun g hg => ?_)
    have hgu : e = g * (e / g) := (Nat.mul_div_cancel' (hdvd g hg)).symm
    exact dvd_of_div_dvd he hgu hmul (dvd_foldr_lcm gs g hg)
  have hm1 : m = 1 := Nat.dvd_one.mp hone
  subst hm1
  rw [Nat.mul_one] at hm
  omega

end Openings

#print axioms Openings.dvd_of_div_dvd
#print axioms Openings.foldr_lcm_dvd
#print axioms Openings.dvd_foldr_lcm
#print axioms Openings.lcm_div_eq
