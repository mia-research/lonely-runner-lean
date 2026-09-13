import LonelyRunner.LRC.ConstructionN.Parts
import Mathlib.Algebra.Order.Round
import Mathlib.Tactic

/-!

**RING-FENCE.**  This tree is the general-`n` line and is **not** the artefact of
`docs/n8/MANUSCRIPT_v1.md`.  That paper cites `LonelyRunner/LRC/Construction8/`, which is
**frozen**: nothing here may change it, and `scripts/n8/gate.sh` gates it independently.
This file began as a copy of its `Construction8` counterpart with the namespace renamed;
divergence from that starting point is the point of the tree, and is recorded per file as
it happens.
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

namespace ConstructionN

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

/-! ## The single-reading clear-interval bound

A reading's in-the-way zones are the **open** intervals `((8k-1)/(8s), (8k+1)/(8s))`,
one per lap.  Open, not closed: in-the-way means `circDist (s*u) < 1/n` strictly, so the
endpoints are clear.  That is what leaves the AP's own reading as isolated points rather
than nothing (handover 2026-09-13 §5 trap 1), and closing the brackets would destroy it.

Each zone has width `1/(4s)` and consecutive zones are separated by a clear interval of
width `3/(4s)`.  So a single reading reaches contiguously at most `1/(4s)` — it cannot
bridge its own clear interval, and it cannot bridge a wider one belonging to a slower
reading.
-/

/-! ### General-`n` forms

These six statements carried `n = 8` in the `Construction8` originals.  Here they are at
general `n`, using the forms recorded and checked at `MANUSCRIPT_v1.md` §9.  With threshold
`1/n` a reading `s` is in the way when `|u - k/s| < 1/(ns)`, so the lap-`k` zone runs from
`((n-1)/(ns) + k/s)` to `((n+1)/(ns) + k/s)`, and everything else follows.

At `n = 8` these read `2/(8s) = 1/(4s)`, `6/(8s) = 3/(4s)`, `7s < 9s'`, `9 < 2s` and
`1/(4s') < 3/(4σ)` — the `Construction8` statements exactly.

**One hypothesis is new and is not an artefact of the generalisation.**  The single-reading
exclusion needs `4 < n`: it asserts `2/(ns') < (n-2)/(nσ)`, and at `n = 4` the two sides
coincide.  The exclusion is therefore a fact about `n ≥ 5` and was invisible at `n = 8`.
-/

/-- An in-the-way zone has width `2/(ns)`. -/
theorem blocked_width (n : ℕ) (hn : 0 < n) (s : ℝ) (hs : 0 < s) (k : ℤ) :
    (((n : ℝ) + 1) / (n * s) + (k : ℝ) / s) - (((n : ℝ) - 1) / (n * s) + (k : ℝ) / s)
      = 2 / (n * s) := by
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  field_simp
  ring

/-- Consecutive zones are separated by a clear interval of width `(n-2)/(ns)`. -/
theorem clear_width (n : ℕ) (hn : 0 < n) (s : ℝ) (hs : 0 < s) (k : ℤ) :
    (((n : ℝ) - 1) / (n * s) + ((k : ℝ) + 1) / s) - (((n : ℝ) + 1) / (n * s) + (k : ℝ) / s)
      = ((n : ℝ) - 2) / (n * s) := by
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  field_simp
  ring

/-- First zones overlap iff `s/s' < (n+1)/(n-1)`. -/
theorem first_stretch_overlap (n : ℕ) (hn : 0 < n) (s s' : ℝ) (hs : 0 < s) (hs' : 0 < s') :
    (((n : ℝ) - 1) / (n * s') < ((n : ℝ) + 1) / (n * s))
      ↔ ((n : ℝ) - 1) * s < ((n : ℝ) + 1) * s' := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  constructor <;> intro h <;> nlinarith

/-- A descent through consecutive integers needs `2s > n + 1`, so it breaks at
`s = ⌊(n+1)/2⌋`.  At `n = 8` that is `s = 4`. -/
theorem consecutive_break (n : ℕ) (s : ℝ) :
    (((n : ℝ) - 1) * s < ((n : ℝ) + 1) * (s - 1)) ↔ ((n : ℝ) + 1 < 2 * s) := by
  constructor <;> intro h <;> nlinarith

/-- **Single-reading exclusion, general `n`.**  Needs `4 < n`; at `n = 4` the two sides
coincide and the exclusion is vacuous. -/
theorem no_solo_closure (n : ℕ) (hn : 4 < n) (sig s' : ℝ) (hsig : 0 < sig) (hle : sig ≤ s') :
    2 / ((n : ℝ) * s') < ((n : ℝ) - 2) / (n * sig) := by
  have hn0 : (0 : ℝ) < n := by positivity
  have hn4 : (4 : ℝ) < n := by exact_mod_cast hn
  have h1 : 2 / ((n : ℝ) * s') ≤ 2 / ((n : ℝ) * sig) := by gcongr
  have h2 : 2 / ((n : ℝ) * sig) < ((n : ℝ) - 2) / (n * sig) := by
    rw [div_lt_div_iff_of_pos_right (by positivity)]
    linarith
  linarith

/-- Contrapositive of the exclusion. -/
theorem solo_closure_forces_smaller (n : ℕ) (hn : 4 < n) (sig s' : ℝ)
    (hsig : 0 < sig) (hs' : 0 < s')
    (h : ((n : ℝ) - 2) / (n * sig) ≤ 2 / ((n : ℝ) * s')) : s' < sig := by
  by_contra hcon
  push Not at hcon
  exact absurd h (not_le.mpr (no_solo_closure n hn sig s' hsig hcon))

/-! ### Faithfulness at `n = 8`

Each general form above, instantiated at `n = 8`, gives back the statement proved in
`Construction8/Coords.lean` — same hypotheses, same constants.  These six are the check
that the generalisation did not quietly change what was proved.  The constants `1/(4s)`,
`3/(4s)`, `7 s < 9 s'`, `9 < 2 s`, `1/(4s') < 3/(4σ)` are the `Construction8` literals.
-/

/-- `blocked_width` at `n = 8` is the `Construction8` statement. -/
theorem n8_blocked_width (s : ℝ) (hs : 0 < s) (k : ℤ) :
    (9 / (8 * s) + (k : ℝ) / s) - (7 / (8 * s) + (k : ℝ) / s) = 1 / (4 * s) := by
  have h := blocked_width 8 (by norm_num) s hs k
  norm_num at h
  rw [show (9 : ℝ) / (8 * s) + (k : ℝ) / s - (7 / (8 * s) + (k : ℝ) / s)
        = 9 / (8 * s) - 7 / (8 * s) by ring, h]
  rw [div_eq_div_iff (by positivity) (by positivity)]
  ring

/-- `clear_width` at `n = 8` is the `Construction8` statement. -/
theorem n8_clear_width (s : ℝ) (hs : 0 < s) (k : ℤ) :
    (7 / (8 * s) + ((k : ℝ) + 1) / s) - (9 / (8 * s) + (k : ℝ) / s) = 3 / (4 * s) := by
  have h := clear_width 8 (by norm_num) s hs k
  norm_num at h
  rw [h, div_eq_div_iff (by positivity) (by positivity)]
  ring

/-- `first_stretch_overlap` at `n = 8` is the `9/7` bound. -/
theorem n8_first_stretch_overlap (s s' : ℝ) (hs : 0 < s) (hs' : 0 < s') :
    ((7 : ℝ) / (8 * s') < (9 : ℝ) / (8 * s)) ↔ (7 * s < 9 * s') := by
  have h := first_stretch_overlap 8 (by norm_num) s s' hs hs'
  norm_num at h
  exact h

/-- `consecutive_break` at `n = 8` breaks at `s = 4`. -/
theorem n8_consecutive_break (s : ℝ) : (7 * s < 9 * (s - 1)) ↔ (9 < 2 * s) := by
  have h := consecutive_break 8 s
  norm_num at h
  exact h

/-- `no_solo_closure` at `n = 8`.  The `4 < n` hypothesis is discharged by `norm_num`,
which is why it was invisible in `Construction8`. -/
theorem n8_no_solo_closure (sig s' : ℝ) (hsig : 0 < sig) (hle : sig ≤ s') :
    1 / (4 * s') < 3 / (4 * sig) := by
  have hs' : (0 : ℝ) < s' := lt_of_lt_of_le hsig hle
  have h := no_solo_closure 8 (by norm_num) sig s' hsig hle
  norm_num at h
  calc (1 : ℝ) / (4 * s') = 2 / (8 * s') := by
        rw [div_eq_div_iff (by positivity) (by positivity)]; ring
    _ < 6 / (8 * sig) := h
    _ = 3 / (4 * sig) := by
        rw [div_eq_div_iff (by positivity) (by positivity)]; ring

/-- `solo_closure_forces_smaller` at `n = 8`. -/
theorem n8_solo_closure_forces_smaller (sig s' : ℝ) (hsig : 0 < sig) (hs' : 0 < s')
    (h : 3 / (4 * sig) ≤ 1 / (4 * s')) : s' < sig := by
  by_contra hcon
  push Not at hcon
  exact absurd h (not_le.mpr (n8_no_solo_closure sig s' hsig hcon))

/-! ### Thresholds in `n`

`no_solo_closure` needing `4 < n` prompted a check of the other general forms for
thresholds that `n = 8` could not show.  There is exactly one more, and it is here.
-/

/-- The clear interval between consecutive zones is **positive only for `n > 2`**. -/
theorem clear_width_pos (n : ℕ) (hn : 2 < n) (s : ℝ) (hs : 0 < s) :
    0 < ((n : ℝ) - 2) / (n * s) := by
  have hn2 : (2 : ℝ) < n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  exact div_pos (by linarith) (by positivity)

/-- At `n = 2` the zones tile with nothing between them: the clear interval has width zero,
and the framework's evaluation has no room to work in. -/
theorem clear_width_eq_zero_at_two (s : ℝ) (hs : 0 < s) :
    (((2 : ℕ) : ℝ) - 2) / (2 * s) = 0 := by norm_num

end ConstructionN
