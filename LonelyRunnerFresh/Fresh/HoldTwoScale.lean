import Mathlib
import Fresh.Framework
import Fresh.CascadeLanding
import Fresh.HoldView

/-!
# The hold step at two scales, for any frozen set (E746)

Written 2026-11-01.  New file; nothing existing is edited.  E745 read the AP's one-mover hold step at two scales:
the mover at the bound `1/(8a)`, and the mover at a frozen reading `d`'s class-1 instant `(8M+1)/(8d)` (E742: the
landing scale `d/(8M+1)`).  This file states it for any frozen set and any `a`, `d`, `M`:

* `first_fail_iff_captured`: the first piece `[1/(8a), r₁]` fails iff `ρ ∈ ((8N-1)a, (N+1/8)/r₁)` for some
  integer `N`: the mover's grid index at scale `a` is `8N` (residue 0, captured) and it is still captured at `r₁`;
* `position_at_class_instant`: at `(8M+1)/(8d)` the mover sits at `(8N + η)·a(8M+1)/d` eighths, `η = ρ/a - 8N`;
* `lonely_two_scale`: if the frozen set is clear on the first piece and at `(8M+1)/(8d)`, and for every captured
  zone `N` the whole captured interval lands, at `(8M+1)/(8d)`, between `8k+1` and `8k+7` eighths, then some
  instant has every reading clear.  `lonely_of_frozen_window` (`HoldView`) is the case with no captured zone.

Nothing here uses the base being the AP.  Grades: [L]; `lonely_two_scale` [PROVISIONAL: covering and counting tool]
(through `not_holds_iff_zone`'s zone against the piece; supports "the subject is lonely").
-/

namespace Fresh.OneMover

open Fresh

/-- A point between `k + 1/8` and `k + 7/8` is clear. -/
theorem clear_of_between {x : ℝ} {k : ℤ} (h1 : (k : ℝ) + 1 / 8 ≤ x) (h2 : x ≤ (k : ℝ) + 7 / 8) :
    (1 / 8 : ℝ) ≤ distInt x := by
  unfold distInt
  rcases le_or_gt (round x) k with h | h
  · have : ((round x : ℤ) : ℝ) ≤ k := by exact_mod_cast h
    rw [abs_of_nonneg (by linarith)]; linarith
  · have : (k : ℝ) + 1 ≤ ((round x : ℤ) : ℝ) := by exact_mod_cast h
    rw [abs_of_neg (by linarith)]; linarith

/-- **The first piece fails iff the mover is captured at the bound and still captured at its end.** -/
theorem first_fail_iff_captured {a ρ r₁ : ℝ} (ha : 0 < a) (hρ : 0 < ρ) (hr : 1 / (8 * a) ≤ r₁) :
    ¬ Holds ρ (1 / (8 * a)) r₁ ↔ ∃ N : ℤ, (8 * (N : ℝ) - 1) * a < ρ ∧ ρ < ((N : ℝ) + 1 / 8) / r₁ := by
  rw [not_holds_iff_rho hρ (by positivity) hr]
  refine exists_congr fun N => ?_
  have e : ((N : ℝ) - 1 / 8) / (1 / (8 * a)) = (8 * (N : ℝ) - 1) * a := by field_simp
  rw [e]

/-- **The mover at a frozen reading's class-1 instant**, in eighths: `(8N + η)·a(8M+1)/d`. -/
theorem position_at_class_instant (a d ρ : ℝ) (ha : a ≠ 0) (hd : d ≠ 0) (M N : ℤ) :
    8 * (ρ * ((8 * (M : ℝ) + 1) / (8 * d))) =
      (8 * (N : ℝ) + (ρ / a - 8 * N)) * (a * (8 * (M : ℝ) + 1) / d) := by
  field_simp; ring

/-- **The two-scale hold, for any frozen set.**  `F` is clear on the first piece `[1/(8a), r₁]` and at the class-1
instant `l₂ = (8M+1)/(8d)`.  For each captured zone `N` (the first piece's failing interval
`((8N-1)a, (N+1/8)/r₁)`), the interval's image at `l₂`, from `(8N-1)·a(8M+1)/d` to `(8N+1)(8M+1)/(8 d r₁)` eighths,
lies in `[8k+1, 8k+7]` for some `k`.  Then some instant has every reading of `insert ρ F` clear.
[PROVISIONAL: covering and counting tool] -/
theorem lonely_two_scale (F : Finset ℝ) {a d ρ r₁ : ℝ} {M : ℤ} (ha : 0 < a) (hd : 0 < d) (hρ : a < ρ)
    (hM : 0 < 8 * (M : ℝ) + 1) (hr : 1 / (8 * a) ≤ r₁)
    (hF1 : ∀ s : ℝ, 1 / (8 * a) ≤ s → s ≤ r₁ → ∀ f ∈ F, (1 / 8 : ℝ) ≤ distInt (f * s))
    (hF2 : ∀ f ∈ F, (1 / 8 : ℝ) ≤ distInt (f * ((8 * (M : ℝ) + 1) / (8 * d))))
    (hC : ∀ N : ℤ, (8 * (N : ℝ) - 1) * a < ρ → ρ < ((N : ℝ) + 1 / 8) / r₁ →
      ∃ k : ℤ, 8 * (k : ℝ) + 1 ≤ (8 * (N : ℝ) - 1) * (a * (8 * (M : ℝ) + 1) / d) ∧
        (8 * (N : ℝ) + 1) * (8 * (M : ℝ) + 1) / (8 * d * r₁) ≤ 8 * (k : ℝ) + 7) :
    ∃ s : ℝ, ∀ x ∈ insert ρ F, (1 / 8 : ℝ) ≤ distInt (x * s) := by
  have hρ0 : 0 < ρ := lt_trans ha hρ
  have hr0 : 0 < r₁ := lt_of_lt_of_le (by positivity) hr
  by_cases hH : Holds ρ (1 / (8 * a)) r₁
  · obtain ⟨s, hs1, hs2, hc⟩ := (holds_iff_exists_clear hρ0 hr).mp hH
    refine ⟨s, fun x hx => ?_⟩
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hc
    · exact hF1 s hs1 hs2 x hx
  · obtain ⟨N, h1, h2⟩ := (first_fail_iff_captured ha hρ0 hr).mp hH
    obtain ⟨k, hk1, hk2⟩ := hC N h1 h2
    set l₂ := (8 * (M : ℝ) + 1) / (8 * d) with hl₂
    have hl₂0 : 0 < l₂ := by positivity
    -- the mover's position at l₂ lies between the images of the interval's ends
    have lo : (8 * (N : ℝ) - 1) * (a * (8 * (M : ℝ) + 1) / d) ≤ 8 * (ρ * l₂) := by
      have : (8 * (N : ℝ) - 1) * (a * (8 * (M : ℝ) + 1) / d) = 8 * (((8 * (N : ℝ) - 1) * a) * l₂) := by
        rw [hl₂]; field_simp
      rw [this]; nlinarith
    have hi : 8 * (ρ * l₂) ≤ (8 * (N : ℝ) + 1) * (8 * (M : ℝ) + 1) / (8 * d * r₁) := by
      have e : (8 * (N : ℝ) + 1) * (8 * (M : ℝ) + 1) / (8 * d * r₁) = 8 * ((((N : ℝ) + 1 / 8) / r₁) * l₂) := by
        rw [hl₂]; field_simp
      rw [e]; nlinarith
    have hc : (1 / 8 : ℝ) ≤ distInt (ρ * l₂) :=
      clear_of_between (k := k) (by linarith) (by linarith)
    refine ⟨l₂, fun x hx => ?_⟩
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hc
    · exact hF2 x hx

/-- **Any piece that holds gives a lonely instant**, for any frozen set clear on it.  This is the pointwise form
used when a captured interval splits across later pieces (E746). -/
theorem lonely_of_holds (F : Finset ℝ) {ρ l r : ℝ} (hρ : 0 < ρ) (hlr : l ≤ r)
    (hF : ∀ s : ℝ, l ≤ s → s ≤ r → ∀ f ∈ F, (1 / 8 : ℝ) ≤ distInt (f * s)) (hH : Holds ρ l r) :
    ∃ s : ℝ, ∀ x ∈ insert ρ F, (1 / 8 : ℝ) ≤ distInt (x * s) := by
  obtain ⟨s, hs1, hs2, hc⟩ := (holds_iff_exists_clear hρ hlr).mp hH
  refine ⟨s, fun x hx => ?_⟩
  rcases Finset.mem_insert.mp hx with rfl | hx
  · exact hc
  · exact hF s hs1 hs2 x hx

/-- **The exit inside a later piece.**  If the mover is in zone `K` at `l` and leaves it, at `(K + 1/8)/ρ`, no
later than `r`, the piece holds. -/
theorem holds_of_exit {ρ l r : ℝ} (hρ : 0 < ρ) {K : ℤ} (hK1 : (K : ℝ) - 1 / 8 < ρ * l)
    (hK2 : ρ * l < (K : ℝ) + 1 / 8) (hexit : ((K : ℝ) + 1 / 8) / ρ ≤ r) : Holds ρ l r := by
  right
  have hround : round (ρ * l) = K := by
    rw [round_eq, Int.floor_eq_iff]; constructor <;> linarith
  rw [hround]; exact hexit

#print axioms clear_of_between
#print axioms first_fail_iff_captured
#print axioms position_at_class_instant
#print axioms lonely_two_scale
#print axioms lonely_of_holds
#print axioms holds_of_exit

end Fresh.OneMover
