import LonelyRunner.LRC.Construction8.Parts
import Mathlib.Algebra.Order.Round
import Mathlib.Tactic

/-!
# Coordinates, stretch overlap, and the wide-gap lemma

Three independent pieces, none of which depends on the others.

* `coord_iff` — the `(a, m)` resolution condition. Evaluating at the rational time
  `t = a/m` turns "runner at relative speed `d` is clear of the subject" into a
  condition on the integer residue `(d*a) % m`, with no real division and no
  `Int.fract` in the statement. This is the substrate the handover of 2026-09-13
  §7 item 2 asks for: it removes the boundary hazard (trap 1) from the statement
  rather than leaving it to an interior argument, since `≥` on integers is exact.

* `stretch_overlap`, `first_stretch_overlap`, `consecutive_break` — the algebra of
  when one reading's in-the-way stretch reaches past the start of another's.
  `first_stretch_overlap` is the `9/7` bound for first stretches; `stretch_overlap`
  is the general form, and the two differ, which matters: `9/7` is the lap-1
  against lap-1 case only.

* `wide_gap_core`, `wide_gap_end` — `docs/n8/WIDE_GAP_LEMMA_v1.md` §1 and §2.

Nothing here uses measure, density, covering, a witness, a carrier, primes, or LRC at
any other order. Nothing here states or attempts part 7 of `PROOF_CANDIDATE_v3`.
-/

namespace Construction8

/-! ## The `(a, m)` resolution condition -/

/-- At the rational time `t = a/m`, a runner at relative speed `d` is at circle
distance `≥ 1/n` from the subject **iff** the integer residue `R = (d*a) % m`
satisfies `m ≤ n*R` and `n*R + m ≤ n*m` — that is, `R ∈ [m/n, (n-1)m/n]`, written
without division.  Exact on `ℕ`; the boundary is included on both sides. -/
theorem coord_iff (n d a m : ℕ) (hn : 0 < n) (hm : 0 < m) :
    ((n : ℝ)⁻¹ ≤ circDist ((d * a : ℕ) / (m : ℝ))) ↔
      (m ≤ n * ((d * a) % m) ∧ n * ((d * a) % m) + m ≤ n * m) := by
  have hm0 : (0:ℝ) < m := by exact_mod_cast hm
  have hn0 : (0:ℝ) < n := by exact_mod_cast hn
  set R := (d * a) % m with hRdef
  set Q := (d * a) / m with hQdef
  have hdm : (m : ℝ) * (Q : ℝ) + (R : ℝ) = ((d * a : ℕ) : ℝ) := by
    exact_mod_cast congrArg (fun k : ℕ => (k : ℝ)) (Nat.div_add_mod (d * a) m)
  have hRlt : (R : ℝ) < (m : ℝ) := by exact_mod_cast Nat.mod_lt _ hm
  have h1 : ((d * a : ℕ) : ℝ) / (m : ℝ) = ((Q : ℤ) : ℝ) + (R : ℝ) / m := by
    rw [← hdm]; push_cast; field_simp
  have hfrac : Int.fract (((d * a : ℕ) : ℝ) / (m : ℝ)) = (R : ℝ) / m := by
    rw [h1, Int.fract_intCast_add]
    exact Int.fract_eq_self.mpr ⟨by positivity, (div_lt_one hm0).mpr hRlt⟩
  rw [circDist, hfrac, le_min_iff]
  have e1 : ((n : ℝ)⁻¹ ≤ (R : ℝ) / m) ↔ ((m : ℝ) ≤ (n : ℝ) * R) := by
    rw [inv_eq_one_div, div_le_div_iff₀ hn0 hm0]
    constructor <;> intro h <;> nlinarith
  have e2 : ((n : ℝ)⁻¹ ≤ 1 - (R : ℝ) / m) ↔ ((n : ℝ) * R + m ≤ (n : ℝ) * m) := by
    rw [le_sub_iff_add_le, inv_eq_one_div,
        div_add_div _ _ (ne_of_gt hn0) (ne_of_gt hm0), div_le_one (by positivity)]
    constructor <;> intro h <;> nlinarith
  rw [e1, e2]
  constructor
  · rintro ⟨ha, hb⟩; exact ⟨by exact_mod_cast ha, by exact_mod_cast hb⟩
  · rintro ⟨ha, hb⟩; exact ⟨by exact_mod_cast ha, by exact_mod_cast hb⟩

/-! ## Stretch overlap

Reading `s` is in the way on its lap-`k` stretch, the interval
`((n k - 1)/(n s), (n k + 1)/(n s))`.  Whether one stretch reaches past the start of
another is a cross-multiplication. -/

/-- The upper end `A/s` of one stretch lies past the lower end `B/s'` of another
exactly when `B * s < A * s'`. -/
theorem stretch_overlap (A B s s' : ℝ) (hs : 0 < s) (hs' : 0 < s') :
    (B / s' < A / s) ↔ (B * s < A * s') := div_lt_div_iff₀ hs' hs

/-- At `n = 8`, for the **first** stretches of both readings, the ends are
`9/(8 s)` and `7/(8 s')`, so overlap is `7 s < 9 s'` — the `9/7` bound.
Later laps give a different bound; see `stretch_overlap`. -/
theorem first_stretch_overlap (s s' : ℝ) (hs : 0 < s) (hs' : 0 < s') :
    ((7 : ℝ) / (8 * s') < (9 : ℝ) / (8 * s)) ↔ (7 * s < 9 * s') := by
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  constructor <;> intro h <;> nlinarith

/-- Reading the first-stretch bound down a step of one: `s' = s - 1` gives `9 < 2 s`,
so a descent through consecutive integers cannot pass `s = 4`. -/
theorem consecutive_break (s : ℝ) : (7 * s < 9 * (s - 1)) ↔ (9 < 2 * s) := by
  constructor <;> intro h <;> linarith

/-! ## The wide-gap lemma

`docs/n8/WIDE_GAP_LEMMA_v1.md`.  With `c = n - 1`, `S` the spread, `a` and `b` a
runner's two adjacent speed gaps and `D` its farthest difference, Branch A is
`D ≤ c * min a b`. -/

/-- If both of a runner's adjacent speed gaps reach the average `S/c`, and its
farthest difference is at most the spread `S`, then Branch A holds for it. -/
theorem wide_gap_core (c S a b D : ℝ) (hc : 0 < c)
    (ha : S / c ≤ a) (hb : S / c ≤ b) (hD : D ≤ S) : D ≤ c * min a b := by
  have hmin : S / c ≤ min a b := le_min ha hb
  rw [div_le_iff₀ hc] at hmin; linarith

/-- The end runners need only one wide gap: their farthest difference is the whole
spread, so `S/c ≤ a` already gives `S ≤ c * a`. -/
theorem wide_gap_end (c S a : ℝ) (hc : 0 < c) (ha : S / c ≤ a) : S ≤ c * a := by
  rw [div_le_iff₀ hc] at ha; linarith

end Construction8
