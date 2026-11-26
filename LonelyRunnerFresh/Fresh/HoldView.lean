import Mathlib
import Fresh.Framework
import Fresh.CascadeLanding

/-!
# The hold step in view terms (E744)

Written 2026-11-01.  New file; nothing existing is edited.  `Holds ρ l r` (`CascadeLanding.lean`) is the hold step of
every `holdG<set>_exists`.  Here it is stated three ways, each exact:

* `holds_iff_exists_clear`: the piece `[l, r]` holds iff the mover is clear (`1/8 ≤ distInt (ρ s)`) at some instant `s`
  of the piece; in the view of E741, iff the mover's status is ok at some scale `1/(8s)`, `s ∈ [l, r]`;
* `not_holds_iff_zone`: the piece fails iff the mover sweeps it inside one blocked zone `(N - 1/8, N + 1/8)`;
* `not_holds_iff_rho`: for `0 < l`, the piece fails iff `ρ ∈ ((N - 1/8)/l, (N + 1/8)/r)` for some integer `N`.

So (H) for a set of pieces is: no mover reading beyond the least frozen one lies in every piece's failing set.
`holds_of_ratio`: a piece with `ρ l > 1/8` and `r/l ≥ 9/7` holds; `lonely_of_frozen_window`: for any finite frozen set
with least reading `a`, clear on `[1/(8a), 9/(56a)]`, every mover reading `ρ > a` leaves an instant with every reading
clear.  Nothing here uses the base being the AP.  Grades: [L]; the last two [PROVISIONAL: covering and counting tool].
-/

namespace Fresh.OneMover

open Fresh

/-- A point inside a blocked zone is not clear. -/
theorem not_clear_of_zone {x : ℝ} {N : ℤ} (h1 : (N : ℝ) - 1 / 8 < x) (h2 : x < (N : ℝ) + 1 / 8) :
    distInt x < 1 / 8 := by
  unfold distInt
  have := round_le x N
  have hN : |x - (N : ℝ)| < 1 / 8 := by rw [abs_lt]; constructor <;> linarith
  linarith

/-- **The piece fails iff the mover sweeps it inside one blocked zone.** -/
theorem not_holds_iff_zone {ρ l r : ℝ} (hρ : 0 < ρ) (hlr : l ≤ r) :
    ¬ Holds ρ l r ↔ ∃ N : ℤ, (N : ℝ) - 1 / 8 < ρ * l ∧ ρ * r < (N : ℝ) + 1 / 8 := by
  refine ⟨not_holds_win hρ, ?_⟩
  rintro ⟨N, h1, h2⟩ hH
  have hlr' : ρ * l ≤ ρ * r := mul_le_mul_of_nonneg_left hlr hρ.le
  rcases hH with hc | hr
  · exact absurd hc (not_le.2 (not_clear_of_zone h1 (by linarith)))
  · have hround : round (ρ * l) = N := by
      rw [round_eq, Int.floor_eq_iff]; constructor <;> linarith
    rw [hround, div_le_iff₀ hρ] at hr
    linarith

/-- **The piece holds iff the mover is clear at some instant of it.** -/
theorem holds_iff_exists_clear {ρ l r : ℝ} (hρ : 0 < ρ) (hlr : l ≤ r) :
    Holds ρ l r ↔ ∃ s : ℝ, l ≤ s ∧ s ≤ r ∧ (1 / 8 : ℝ) ≤ distInt (ρ * s) := by
  constructor
  · intro h
    obtain ⟨hc, hl, hr, -⟩ := holds_clear hρ hlr h
    exact ⟨firstPt ρ l, hl, hr, hc⟩
  · rintro ⟨s, hs1, hs2, hc⟩
    by_contra hH
    obtain ⟨N, h1, h2⟩ := (not_holds_iff_zone hρ hlr).mp hH
    have a1 : ρ * l ≤ ρ * s := mul_le_mul_of_nonneg_left hs1 hρ.le
    have a2 : ρ * s ≤ ρ * r := mul_le_mul_of_nonneg_left hs2 hρ.le
    exact absurd hc (not_le.2 (not_clear_of_zone (N := N) (by linarith) (by linarith)))

/-- **The failing mover readings of a piece.**  For `0 < l ≤ r`, the piece fails for `ρ` iff `ρ` lies in
`((N - 1/8)/l, (N + 1/8)/r)` for some integer `N`. -/
theorem not_holds_iff_rho {ρ l r : ℝ} (hρ : 0 < ρ) (hl : 0 < l) (hlr : l ≤ r) :
    ¬ Holds ρ l r ↔ ∃ N : ℤ, ((N : ℝ) - 1 / 8) / l < ρ ∧ ρ < ((N : ℝ) + 1 / 8) / r := by
  have hr : 0 < r := lt_of_lt_of_le hl hlr
  rw [not_holds_iff_zone hρ hlr]
  refine exists_congr fun N => ?_
  rw [div_lt_iff₀ hl, lt_div_iff₀ hr]

/-- **A piece of ratio at least `9/7` past the mover's bound holds.**  If the mover is past `1/8` at the piece's left
end and `r/l ≥ 9/7`, the mover cannot sweep `[l, r]` inside one blocked zone.  [PROVISIONAL: covering and counting tool] (zone width
`1/4` against the piece); it supports `lonely_of_frozen_window`. -/
theorem holds_of_ratio {ρ l r : ℝ} (hρ : 0 < ρ) (hl : 1 / 8 < ρ * l) (hr : 9 * l ≤ 7 * r) : Holds ρ l r := by
  by_contra h
  obtain ⟨N, h1, h2⟩ := not_holds_win hρ h
  have hl0 : 0 < l := by
    by_contra h0; push Not at h0; nlinarith
  have hlr : ρ * (9 * l) ≤ ρ * (7 * r) := mul_le_mul_of_nonneg_left hr hρ.le
  have hN1 : (1 : ℤ) ≤ N := by
    have : (0 : ℝ) < N := by nlinarith
    exact_mod_cast (show (0 : ℤ) < N by exact_mod_cast this)
  have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  nlinarith

/-- **A frozen window of ratio `9/7` at the bound makes the subject lonely, for any base.**  `F` is any finite set
of readings with least reading `a` (only `a > 0` is used); if every reading of `F` is clear on `[1/(8a), 9/(56a)]`,
then for every mover reading `ρ > a` some instant has every reading of `insert ρ F` clear.  Nothing about the AP is
assumed.  [PROVISIONAL: covering and counting tool] via `holds_of_ratio`. -/
theorem lonely_of_frozen_window (F : Finset ℝ) {a ρ : ℝ} (ha : 0 < a) (hρ : a < ρ)
    (hF : ∀ s : ℝ, 1 / (8 * a) ≤ s → s ≤ 9 / (56 * a) → ∀ f ∈ F, (1 / 8 : ℝ) ≤ distInt (f * s)) :
    ∃ s : ℝ, ∀ d ∈ insert ρ F, (1 / 8 : ℝ) ≤ distInt (d * s) := by
  have hρ0 : 0 < ρ := lt_trans ha hρ
  have hl : 1 / 8 < ρ * (1 / (8 * a)) := by
    rw [mul_one_div, lt_div_iff₀ (by positivity)]; nlinarith
  have hr : 9 * (1 / (8 * a)) ≤ 7 * (9 / (56 * a)) := by
    rw [le_iff_eq_or_lt]; left; field_simp; ring
  have hlr : 1 / (8 * a) ≤ 9 / (56 * a) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
  obtain ⟨s, hs1, hs2, hc⟩ :=
    (holds_iff_exists_clear hρ0 hlr).mp (holds_of_ratio hρ0 hl hr)
  refine ⟨s, fun d hd => ?_⟩
  rcases Finset.mem_insert.mp hd with rfl | hd
  · exact hc
  · exact hF s hs1 hs2 d hd

#print axioms holds_of_ratio
#print axioms lonely_of_frozen_window
#print axioms not_holds_iff_zone
#print axioms holds_iff_exists_clear
#print axioms not_holds_iff_rho

end Fresh.OneMover
