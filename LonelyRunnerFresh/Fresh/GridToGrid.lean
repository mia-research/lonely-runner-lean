import Mathlib
import Fresh.Framework
import Fresh.Grid
import Fresh.DMax
import Fresh.Cycle

/-!
# D_min between two grids of different step

Written 2026-10-08 (task Z2).  Owner: "From any AP speed and from any Grid speed to the next AP/Grid speed any
individual isolation is deformed with that isolation being displaced.  This is called D-min. ... Dmin also works from
one Grid speed to the next."

`Fresh.Cycle` gives the exact displacement when the step `d` is the same.  Here the step changes:
`v j = v₀ + idx j · d` is moved to `v' j = v₀' + idx' j · d'` (same labels, `d' ≠ d` allowed).  Three parts.

1. Exact displacement of every reading, at the old instant `a/(8d)` and at the new instant `a'/(8d')`, and the
   isolation criterion at the new instants.
2. The two sets of grid instants, and exactly when and why an old instant is (or is not) a new one.
3. The straight path of speeds `v_s = (1-s) v + s v'`: the reading is affine in `s`; the exact `s` at which it reaches
   circle distance `1/8`.

Nothing here says a displaced isolation exists or where it lands: displacement statements only.  All speeds are
positive wherever positivity is used; every quantity is a difference of speeds; no floats.

Provenance (existing repo, read for the argument, nothing copied): `Fresh.Cycle.grid_reading_shift`,
`Fresh.Cycle.isolatedAt_grid_iff` are the same-step versions in this tree; nothing in `LonelyRunner/` states the
different-step case, so these theorems were derived here.
-/

open Classical

namespace Fresh

namespace GridToGrid

/-! ## Part 1: exact displacement of the readings -/

/-- **Closed form of the reading change** (no instant yet): with `Δ = idx i - idx k`, `Δ' = idx' i - idx' k`, the
difference-of-speeds of the pair `(i,k)` changes by `Δ' d' - Δ d`. -/
theorem pair_change (v v' : Fin 8 → ℝ) (d d' v₀ v₀' : ℝ) (idx idx' : Fin 8 → ℤ)
    (hv : ∀ j, v j = v₀ + (idx j : ℝ) * d) (hv' : ∀ j, v' j = v₀' + (idx' j : ℝ) * d') (i k : Fin 8) :
    (v' i - v' k) - (v i - v k)
      = (((idx' i - idx' k : ℤ)) : ℝ) * d' - (((idx i - idx k : ℤ)) : ℝ) * d := by
  rw [hv i, hv k, hv' i, hv' k]; push_cast; ring

#print axioms pair_change

/-- **The reading of the new arrangement at the OLD instant `a/(8d)`**, in the old reading plus a displacement.
`ρ = d'/d`.  The displacement is `(Δ' ρ - Δ) a / 8` laps: the new index difference scaled by the ratio of steps, minus
the old index difference. -/
theorem reading_at_old_instant (v v' : Fin 8 → ℝ) (d d' v₀ v₀' : ℝ) (hd : 0 < d) (idx idx' : Fin 8 → ℤ)
    (hv : ∀ j, v j = v₀ + (idx j : ℝ) * d) (hv' : ∀ j, v' j = v₀' + (idx' j : ℝ) * d') (a : ℤ) (i k : Fin 8) :
    (v' i - v' k) * ((a : ℝ) / (8 * d))
      = (v i - v k) * ((a : ℝ) / (8 * d))
        + ((((idx' i - idx' k : ℤ) : ℝ) * (d' / d) - ((idx i - idx k : ℤ) : ℝ)) * (a : ℝ)) / 8 := by
  have hd0 : d ≠ 0 := hd.ne'
  have h := pair_change v v' d d' v₀ v₀' idx idx' hv hv' i k
  have : (v' i - v' k) = (v i - v k) + ((((idx' i - idx' k : ℤ)) : ℝ) * d' - (((idx i - idx k : ℤ)) : ℝ) * d) := by
    linarith
  rw [this]; field_simp

#print axioms reading_at_old_instant

/-- **The reading of the old arrangement at the NEW instant `a'/(8d')`** (the same identity read the other way:
`ρ' = d/d'`, `Δ - ...`). -/
theorem reading_old_at_new_instant (v : Fin 8 → ℝ) (d d' v₀ : ℝ) (hd' : 0 < d') (idx : Fin 8 → ℤ)
    (hv : ∀ j, v j = v₀ + (idx j : ℝ) * d) (a' : ℤ) (i k : Fin 8) :
    (v i - v k) * ((a' : ℝ) / (8 * d')) = ((((idx i - idx k : ℤ) : ℝ) * (d / d')) * (a' : ℝ)) / 8 := by
  have hd0 : d' ≠ 0 := hd'.ne'
  rw [hv i, hv k]; push_cast; field_simp; ring

#print axioms reading_old_at_new_instant

/-- **Reading at the new instant**: `Δ' a' / 8` laps exactly (the new grid's own value). -/
theorem reading_at_new_instant (v' : Fin 8 → ℝ) (d' v₀' : ℝ) (hd' : 0 < d') (idx' : Fin 8 → ℤ)
    (hv' : ∀ j, v' j = v₀' + (idx' j : ℝ) * d') (a' : ℤ) (i k : Fin 8) :
    (v' i - v' k) * ((a' : ℝ) / (8 * d')) = (((idx' i - idx' k) * a' : ℤ) : ℝ) / 8 :=
  Cycle.grid_reading_value v' d' v₀' hd' idx' hv' a' k i

#print axioms reading_at_new_instant

/-- **The exact identity relating the two readings** (old reading at the old instant, new reading at the new
instant): the reading moves by `(Δ' a' - Δ a)/8` laps, a whole number of eighths, for every pair, whatever the steps
`d`, `d'` and the bases `v₀`, `v₀'`.  This is the different-step form of `Cycle.grid_reading_shift`. -/
theorem matched_reading_shift (v v' : Fin 8 → ℝ) (d d' v₀ v₀' : ℝ) (hd : 0 < d) (hd' : 0 < d')
    (idx idx' : Fin 8 → ℤ)
    (hv : ∀ j, v j = v₀ + (idx j : ℝ) * d) (hv' : ∀ j, v' j = v₀' + (idx' j : ℝ) * d') (a a' : ℤ) (i k : Fin 8) :
    (v' i - v' k) * ((a' : ℝ) / (8 * d'))
      = (v i - v k) * ((a : ℝ) / (8 * d))
        + (((idx' i - idx' k) * a' - (idx i - idx k) * a : ℤ) : ℝ) / 8 := by
  rw [reading_at_new_instant v' d' v₀' hd' idx' hv' a' i k, Cycle.grid_reading_value v d v₀ hd idx hv a k i]
  push_cast; ring

#print axioms matched_reading_shift

/-- Consequently the circle distance of a reading is unchanged whenever `8 ∣ Δ' a' - Δ a`. -/
theorem matched_reading_distInt (v v' : Fin 8 → ℝ) (d d' v₀ v₀' : ℝ) (hd : 0 < d) (hd' : 0 < d')
    (idx idx' : Fin 8 → ℤ)
    (hv : ∀ j, v j = v₀ + (idx j : ℝ) * d) (hv' : ∀ j, v' j = v₀' + (idx' j : ℝ) * d') (a a' : ℤ) (i k : Fin 8)
    (h8 : (8 : ℤ) ∣ (idx' i - idx' k) * a' - (idx i - idx k) * a) :
    distInt ((v' i - v' k) * ((a' : ℝ) / (8 * d'))) = distInt ((v i - v k) * ((a : ℝ) / (8 * d))) := by
  obtain ⟨m, hm⟩ := h8
  have : (v' i - v' k) * ((a' : ℝ) / (8 * d'))
      = (v i - v k) * ((a : ℝ) / (8 * d)) + (m : ℝ) := by
    rw [matched_reading_shift v v' d d' v₀ v₀' hd hd' idx idx' hv hv' a a' i k, hm]
    push_cast; ring
  rw [this, distInt_add_int]

#print axioms matched_reading_distInt

/-- **Isolation at the new instants (exactly `isolatedAt_grid_iff` for the new grid).**  Subject `k` of
`v' j = v₀' + idx' j · d'` is isolated at `a'/(8d')`, `a'` a unit, iff no other index is congruent to `idx' k` mod 8.
The condition mentions neither `d'`, `v₀'`, `a'`, nor the old arrangement. -/
theorem new_isolatedAt_iff (v' : Fin 8 → ℝ) (d' v₀' : ℝ) (hd' : 0 < d') (idx' : Fin 8 → ℤ)
    (hv' : ∀ j, v' j = v₀' + (idx' j : ℝ) * d') (a' : ℤ) (ha' : IsCoprime a' 8) (k : Fin 8) :
    IsolatedAt v' k ((a' : ℝ) / (8 * d')) ↔ ∀ i, i ≠ k → ¬ (8 : ℤ) ∣ idx' i - idx' k :=
  Cycle.isolatedAt_grid_iff v' d' v₀' hd' idx' hv' a' ha' k

#print axioms new_isolatedAt_iff

/-- **Isolation transfers between grid instants of different steps** whenever the congruence pattern of the subject is
the same: if `idx' i - idx' k` is divisible by 8 exactly when `idx i - idx k` is, then `k` is isolated in `v` at
`a/(8d)` iff isolated in `v'` at `a'/(8d')`. -/
theorem isolatedAt_transfer (v v' : Fin 8 → ℝ) (d d' v₀ v₀' : ℝ) (hd : 0 < d) (hd' : 0 < d')
    (idx idx' : Fin 8 → ℤ)
    (hv : ∀ j, v j = v₀ + (idx j : ℝ) * d) (hv' : ∀ j, v' j = v₀' + (idx' j : ℝ) * d') (a a' : ℤ)
    (ha : IsCoprime a 8) (ha' : IsCoprime a' 8) (k : Fin 8)
    (hpat : ∀ i, i ≠ k → ((8 : ℤ) ∣ idx' i - idx' k ↔ (8 : ℤ) ∣ idx i - idx k)) :
    IsolatedAt v' k ((a' : ℝ) / (8 * d')) ↔ IsolatedAt v k ((a : ℝ) / (8 * d)) := by
  rw [new_isolatedAt_iff v' d' v₀' hd' idx' hv' a' ha' k, Cycle.isolatedAt_grid_iff v d v₀ hd idx hv a ha k]
  refine forall_congr' fun i => forall_congr' fun hi => ?_
  rw [hpat i hi]

#print axioms isolatedAt_transfer

/-- **Complete new indices: every subject of the new grid is isolated at every new instant** (the new grid is
globally isolated at `a'/(8d')`).  Together with `reading_at_old_instant`, this is the whole D_min statement between
grids: the new isolation sits at `a'/(8d')`, and the old reading is displaced to the new one by
`matched_reading_shift`. -/
theorem new_global (v' : Fin 8 → ℝ) (d' v₀' : ℝ) (hd' : 0 < d') (idx' : Fin 8 → ℤ) (hc : CompleteResidues idx')
    (hv' : ∀ j, v' j = v₀' + (idx' j : ℝ) * d') (a' : ℤ) (ha' : IsCoprime a' 8) :
    GloballyIsolatedAt v' ((a' : ℝ) / (8 * d')) :=
  gridGlobalIsolation v' d' v₀' idx' hd' hc hv' a' ha'

#print axioms new_global

/-! ## Part 2: the map of instants -/

/-- The global-isolation instants of a grid of step `d`: the positive reals `a/(8d)`, `a` a unit mod 8. -/
def instantSet (d : ℝ) : Set ℝ := {t | 0 < t ∧ ∃ a : ℤ, IsCoprime a 8 ∧ t = (a : ℝ) / (8 * d)}

/-- A unit mod 8 is odd. -/
theorem odd_of_isCoprime_eight {a : ℤ} (h : IsCoprime a 8) : Odd a := by
  by_contra hodd
  have heven : Even a := by simpa using hodd
  obtain ⟨c, hc⟩ := heven
  obtain ⟨u, w, huw⟩ := h
  have h2 : 2 * (u * c + 4 * w) = 1 := by subst hc; linarith [huw]
  omega

#print axioms odd_of_isCoprime_eight

/-- **When an old instant is a new instant.**  The two instant sets meet iff there are units `a`, `a'` mod 8 with
`a' d = a d'` (and `a > 0`).  Reason: `a/(8d) = a'/(8d')` is cross-multiplication. -/
theorem instants_meet_iff (d d' : ℝ) (hd : 0 < d) (hd' : 0 < d') :
    (instantSet d ∩ instantSet d').Nonempty ↔
      ∃ a a' : ℤ, 0 < a ∧ IsCoprime a 8 ∧ IsCoprime a' 8 ∧ (a' : ℝ) * d = (a : ℝ) * d' := by
  have hd0 : d ≠ 0 := hd.ne'
  have hd0' : d' ≠ 0 := hd'.ne'
  constructor
  · rintro ⟨t, ⟨ht, a, ha, hta⟩, ⟨_, a', ha', hta'⟩⟩
    refine ⟨a, a', ?_, ha, ha', ?_⟩
    · have : (0 : ℝ) < a := by
        have h8 : (0 : ℝ) < 8 * d := by positivity
        rw [hta] at ht
        exact (div_pos_iff_of_pos_right h8).mp ht
      exact_mod_cast this
    · have h := hta.symm.trans hta'
      field_simp at h
      linarith
  · rintro ⟨a, a', hpos, ha, ha', h⟩
    refine ⟨(a : ℝ) / (8 * d), ⟨?_, a, ha, rfl⟩, ⟨?_, a', ha', ?_⟩⟩
    · have : (0 : ℝ) < a := by exact_mod_cast hpos
      positivity
    · have : (0 : ℝ) < a := by exact_mod_cast hpos
      positivity
    · field_simp
      linarith

#print axioms instants_meet_iff

/-- **Rational ratio with odd numerator and denominator: the instants coincide.**  If `p d = q d'` with `p`, `q` odd
and `q > 0` (that is, `d'/d = p/q` with both odd), then `q/(8d) = p/(8d')` lies in both sets.  More generally the
instants `c q/(8d) = c p/(8d')`, `c` odd and positive, coincide. -/
theorem instants_coincide (d d' : ℝ) (hd : 0 < d) (hd' : 0 < d') (p q : ℤ) (hp : Odd p) (hq : Odd q) (hqpos : 0 < q)
    (h : (p : ℝ) * d = (q : ℝ) * d') :
    (q : ℝ) / (8 * d) ∈ instantSet d ∩ instantSet d' := by
  have hqr : (0 : ℝ) < q := by exact_mod_cast hqpos
  have hd0 : d ≠ 0 := hd.ne'
  have hd0' : d' ≠ 0 := hd'.ne'
  refine ⟨⟨by positivity, q, isCoprime_eight_of_odd hq, rfl⟩, ⟨by positivity, p, isCoprime_eight_of_odd hp, ?_⟩⟩
  field_simp
  linarith

#print axioms instants_coincide

/-- **The converse: a shared instant forces the ratio `d'/d` to be a quotient of two odd integers.** -/
theorem ratio_odd_of_meet (d d' : ℝ) (hd : 0 < d) (hd' : 0 < d')
    (hm : (instantSet d ∩ instantSet d').Nonempty) :
    ∃ p q : ℤ, Odd p ∧ Odd q ∧ 0 < q ∧ (p : ℝ) * d = (q : ℝ) * d' := by
  obtain ⟨a, a', hpos, ha, ha', h⟩ := (instants_meet_iff d d' hd hd').mp hm
  exact ⟨a', a, odd_of_isCoprime_eight ha', odd_of_isCoprime_eight ha, hpos, h⟩

#print axioms ratio_odd_of_meet

/-- **Incommensurable steps: no old instant is a new instant.**  If `d'` is not a rational multiple of `d`, the two
instant sets are disjoint.  Reason: a shared instant gives `d' = (a'/a) d`. -/
theorem instants_disjoint_of_incommensurable (d d' : ℝ) (hd : 0 < d) (hd' : 0 < d')
    (hinc : ∀ q : ℚ, d' ≠ (q : ℝ) * d) : instantSet d ∩ instantSet d' = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro t ht
  obtain ⟨a, a', hpos, _, _, h⟩ := (instants_meet_iff d d' hd hd').mp ⟨t, ht⟩
  have hne : (a : ℝ) ≠ 0 := by
    have : (0 : ℝ) < a := by exact_mod_cast hpos
    exact this.ne'
  apply hinc ((a' : ℚ) / (a : ℚ))
  push_cast
  field_simp
  linarith

#print axioms instants_disjoint_of_incommensurable

/-- **Doubling the step: no old instant is a new instant.**  `d' = 2 d` gives `a' = 2 a`, which is even, so never a
unit.  The reason is 2-adic: `a/(8d) = 2a/(8·2d)` but `2a` is not a unit mod 8. -/
theorem instants_disjoint_double (d d' : ℝ) (hd : 0 < d) (hd' : 0 < d') (h2 : d' = 2 * d) :
    instantSet d ∩ instantSet d' = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro t ht
  obtain ⟨a, a', _, _, ha', h⟩ := (instants_meet_iff d d' hd hd').mp ⟨t, ht⟩
  have h' : (a' : ℝ) = 2 * a := by
    rw [h2] at h
    have hd0 : d ≠ 0 := hd.ne'
    have : ((a' : ℝ) - 2 * a) * d = 0 := by linarith
    rcases mul_eq_zero.mp this with h0 | h0
    · linarith
    · exact absurd h0 hd0
  have hz : a' = 2 * a := by exact_mod_cast h'
  have := odd_of_isCoprime_eight ha'
  rw [hz] at this
  obtain ⟨c, hc⟩ := this
  omega

#print axioms instants_disjoint_double

/-- **At an old instant, doubled step, every subject of the new grid is NOT isolated** (not only "the instant is not
in the new set"): for any complete `idx'` and any integer `a`, the new arrangement `v₀' + idx' j (2d)` has, for each
subject `k`, a partner `i` with `idx' i ≡ idx' k + 4 (mod 8)`; their reading at `a/(8d)` is `(Δ'/4) a`, a whole number
of laps.  Reason: `d'/d = 2` means the old instant is `2a/(8d')`, an even multiple of `1/(8d')`, and an even `a'` makes
the pair at index distance 4 coincide.  **[PROVISIONAL: counting tool]** at `Cycle.exists_index_congruent` (an
injective map `Fin 8 → ZMod 8` is onto), supporting the claim that a partner at residue `+4` exists. -/
theorem double_step_no_isolation (v' : Fin 8 → ℝ) (d v₀' : ℝ) (hd : 0 < d) (idx' : Fin 8 → ℤ)
    (hc : CompleteResidues idx') (hv' : ∀ j, v' j = v₀' + (idx' j : ℝ) * (2 * d)) (a : ℤ) (k : Fin 8) :
    ¬ IsolatedAt v' k ((a : ℝ) / (8 * d)) := by
  intro hiso
  obtain ⟨i, hi⟩ := Cycle.exists_index_congruent hc (idx' k + 4)
  obtain ⟨m, hm⟩ := hi
  have hik : i ≠ k := by
    intro hik
    subst hik
    omega
  have h1 := hiso i hik
  have hd0 : d ≠ 0 := hd.ne'
  have hval : (v' i - v' k) * ((a : ℝ) / (8 * d)) = (((1 - 2 * m) * a : ℤ) : ℝ) := by
    rw [hv' i, hv' k]
    have hm' : (idx' i : ℝ) = idx' k + 4 - 8 * m := by
      have : idx' i = idx' k + 4 - 8 * m := by omega
      exact_mod_cast this
    rw [hm']; push_cast; field_simp; ring
  rw [hval, distInt_intCast] at h1
  norm_num at h1

#print axioms double_step_no_isolation

/-- **Exact counterexample.**  `v j = 1 + j` (AP, `d = 1`) is globally isolated at `1/8`; the next grid
`v' j = 1 + 2 j` (step `d' = 2`, indices `0..7` complete) has NO subject isolated at that old instant `1/8`, though it
is globally isolated at its own instants `a'/16`.  The old instant is not a new isolation instant because
`1/8 = 2/16` and `a' = 2` is not a unit mod 8. -/
theorem counterexample_double :
    (let v : Fin 8 → ℝ := fun j => 1 + ((j : ℕ) : ℝ) * 1
     let v' : Fin 8 → ℝ := fun j => 1 + ((j : ℕ) : ℝ) * 2
     GloballyIsolatedAt v ((1 : ℝ) / 8) ∧ (∀ k, ¬ IsolatedAt v' k ((1 : ℝ) / 8)) ∧
       GloballyIsolatedAt v' ((1 : ℝ) / 16)) := by
  intro v v'
  refine ⟨?_, ?_, ?_⟩
  · have := gridGlobalIsolation v 1 1 (fun j : Fin 8 => ((j : ℕ) : ℤ)) one_pos completeResidues_id
      (fun j => by simp [v]) 1 isCoprime_one_left
    simpa using this
  · intro k
    have := double_step_no_isolation v' 1 1 one_pos (fun j : Fin 8 => ((j : ℕ) : ℤ)) completeResidues_id
      (fun j => by simp [v']) 1 k
    simpa using this
  · have := gridGlobalIsolation v' 2 1 (fun j : Fin 8 => ((j : ℕ) : ℤ)) (by norm_num) completeResidues_id
      (fun j => by simp [v']) 1 isCoprime_one_left
    convert this using 2 <;> norm_num

#print axioms counterexample_double

/-- **When the old instant IS a new instant, the subjects' isolation there is `new_isolatedAt_iff`.**  If
`a' d = a d'` with `a'` a unit, the old instant `a/(8d)` equals `a'/(8d')`, and subject `k` of the new grid is isolated
there iff no other `idx'` is congruent to `idx' k` mod 8. -/
theorem old_instant_is_new_instant_iff (v' : Fin 8 → ℝ) (d d' v₀' : ℝ) (hd : 0 < d) (hd' : 0 < d')
    (idx' : Fin 8 → ℤ) (hv' : ∀ j, v' j = v₀' + (idx' j : ℝ) * d') (a a' : ℤ) (ha' : IsCoprime a' 8)
    (h : (a' : ℝ) * d = (a : ℝ) * d') (k : Fin 8) :
    IsolatedAt v' k ((a : ℝ) / (8 * d)) ↔ ∀ i, i ≠ k → ¬ (8 : ℤ) ∣ idx' i - idx' k := by
  have hd0 : d ≠ 0 := hd.ne'
  have hd0' : d' ≠ 0 := hd'.ne'
  have e : (a : ℝ) / (8 * d) = (a' : ℝ) / (8 * d') := by
    field_simp; linarith
  rw [e]
  exact new_isolatedAt_iff v' d' v₀' hd' idx' hv' a' ha' k

#print axioms old_instant_is_new_instant_iff

/-! ## Part 3: the deformation along the straight path of speeds -/

/-- The straight path of speeds from `v` to `v'`. -/
def pathSpeed (v v' : Fin 8 → ℝ) (s : ℝ) : Fin 8 → ℝ := fun j => (1 - s) * v j + s * v' j

/-- **The reading is affine in `s`.**  At a fixed pair `(i,k)` and instant `t`, along `v_s = (1-s) v + s v'`,
`(v_s i - v_s k) t = R₀ + s (R₁ - R₀)` with `R₀`, `R₁` the readings of `v`, `v'` at `t`.  The slope is the
reading change `R₁ - R₀ = ((v' i - v' k) - (v i - v k)) t` of `reading_displacement`. -/
theorem path_reading_affine (v v' : Fin 8 → ℝ) (s t : ℝ) (i k : Fin 8) :
    (pathSpeed v v' s i - pathSpeed v v' s k) * t
      = (v i - v k) * t + s * ((v' i - v' k) * t - (v i - v k) * t) := by
  unfold pathSpeed; ring

#print axioms path_reading_affine

/-- Along the path every speed is positive for `0 ≤ s ≤ 1` (no runner is ever stationary). -/
theorem path_pos (v v' : Fin 8 → ℝ) (hv : ∀ j, 0 < v j) (hv' : ∀ j, 0 < v' j) (s : ℝ) (h0 : 0 ≤ s) (h1 : s ≤ 1)
    (j : Fin 8) : 0 < pathSpeed v v' s j := by
  unfold pathSpeed
  have h1' : 0 ≤ 1 - s := by linarith
  rcases eq_or_lt_of_le h0 with h | h
  · rw [← h]; simpa using hv j
  · have := hv j
    have := hv' j
    nlinarith [mul_nonneg h1' (hv j).le, mul_pos h (hv' j)]

#print axioms path_pos

/-- Two runners whose order is the same at both ends are apart all along the path: the pair never meets, so the
obstruction named in rule 4 (two speeds meeting) is not reached for that pair. -/
theorem path_pair_apart (v v' : Fin 8 → ℝ) (i k : Fin 8) (h0 : v k < v i) (h1 : v' k < v' i) (s : ℝ) (hs0 : 0 ≤ s)
    (hs1 : s ≤ 1) : pathSpeed v v' s k < pathSpeed v v' s i := by
  unfold pathSpeed
  have h1' : 0 ≤ 1 - s := by linarith
  rcases eq_or_lt_of_le hs0 with h | h
  · rw [← h]; simpa using h0
  · nlinarith [mul_nonneg h1' (sub_pos.mpr h0).le, mul_pos h (sub_pos.mpr h1)]

#print axioms path_pair_apart

/-- If `v` and `v'` are both strictly increasing, so is every `v_s`, `0 ≤ s ≤ 1`: the path is a path of ordered
arrangements. -/
theorem path_strictMono (v v' : Fin 8 → ℝ) (hv : StrictMono v) (hv' : StrictMono v') (s : ℝ) (hs0 : 0 ≤ s)
    (hs1 : s ≤ 1) : StrictMono (pathSpeed v v' s) :=
  fun _ _ hij => path_pair_apart v v' _ _ (hv hij) (hv' hij) s hs0 hs1

#print axioms path_strictMono

/-- **The parameter at which the pair's speeds meet** (if the order is swapped between the ends): with
`g₀ = v i - v k`, `g₁ = v' i - v' k`, `g_s = g₀ + s (g₁ - g₀)` vanishes iff `s = g₀/(g₀ - g₁)` (when `g₀ ≠ g₁`). -/
theorem path_meet_iff (v v' : Fin 8 → ℝ) (i k : Fin 8) (hne : (v i - v k) ≠ (v' i - v' k)) (s : ℝ) :
    pathSpeed v v' s i = pathSpeed v v' s k ↔ s = (v i - v k) / ((v i - v k) - (v' i - v' k)) := by
  have hne' : (v i - v k) - (v' i - v' k) ≠ 0 := sub_ne_zero.mpr hne
  unfold pathSpeed
  rw [eq_div_iff hne']
  constructor <;> intro h <;> nlinarith [h]

#print axioms path_meet_iff

/-- Circle distance at least `1/8` from all integers, unfolded. -/
theorem one_eighth_le_distInt_iff (x : ℝ) : (1 / 8 : ℝ) ≤ distInt x ↔ ∀ z : ℤ, 1 / 8 ≤ |x - (z : ℝ)| := by
  constructor
  · intro h z
    exact h.trans (by unfold distInt; exact round_le x z)
  · intro h
    exact h (round x)

#print axioms one_eighth_le_distInt_iff

/-- A number is at exactly circle distance `1/8` iff it is a whole number plus or minus `1/8`. -/
theorem distInt_eq_eighth_iff (x : ℝ) : distInt x = 1 / 8 ↔ ∃ z : ℤ, x = (z : ℝ) + 1 / 8 ∨ x = (z : ℝ) - 1 / 8 := by
  constructor
  · intro h
    unfold distInt at h
    rcases abs_cases (x - (round x : ℝ)) with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact ⟨round x, Or.inl (by linarith)⟩
    · exact ⟨round x, Or.inr (by linarith)⟩
  · rintro ⟨z, hz | hz⟩
    · have hle : distInt x ≤ 1 / 8 := by
        have := round_le x z
        unfold distInt
        refine this.trans ?_
        rw [hz]; simp
      have hge : (1 / 8 : ℝ) ≤ distInt x := by
        rw [one_eighth_le_distInt_iff]
        intro w
        rw [hz]
        have : (z : ℝ) + 1 / 8 - w = ((z - w : ℤ) : ℝ) + 1 / 8 := by push_cast; ring
        rw [this]
        rcases le_or_gt 0 (z - w) with hn | hn
        · have : (0 : ℝ) ≤ ((z - w : ℤ) : ℝ) := by exact_mod_cast hn
          rw [abs_of_nonneg (by linarith)]; linarith
        · have : ((z - w : ℤ) : ℝ) ≤ -1 := by exact_mod_cast (by omega : z - w ≤ -1)
          rw [abs_of_nonpos (by linarith)]; linarith
      exact le_antisymm hle hge
    · have hle : distInt x ≤ 1 / 8 := by
        have := round_le x z
        unfold distInt
        refine this.trans ?_
        rw [hz]; simp
      have hge : (1 / 8 : ℝ) ≤ distInt x := by
        rw [one_eighth_le_distInt_iff]
        intro w
        rw [hz]
        have : (z : ℝ) - 1 / 8 - w = ((z - w : ℤ) : ℝ) - 1 / 8 := by push_cast; ring
        rw [this]
        rcases le_or_gt 1 (z - w) with hn | hn
        · have : (1 : ℝ) ≤ ((z - w : ℤ) : ℝ) := by exact_mod_cast hn
          rw [abs_of_nonneg (by linarith)]; linarith
        · have : ((z - w : ℤ) : ℝ) ≤ 0 := by exact_mod_cast (by omega : z - w ≤ 0)
          rw [abs_of_nonpos (by linarith)]; linarith
      exact le_antisymm hle hge

#print axioms distInt_eq_eighth_iff

/-- **The exact `s` at which a deforming reading reaches circle distance `1/8`.**  Along the path the reading is
`R(s) = R₀ + s D` (`D = R₁ - R₀`, `D ≠ 0`).  Its circle distance equals `1/8` iff
`s = (z + 1/8 - R₀)/D` or `s = (z - 1/8 - R₀)/D` for some whole number `z`.  (This says where a reading reaches the
edge of the exclusion arc; it says nothing about whether any subject is isolated there.) -/
theorem reading_reaches_eighth (R₀ D s : ℝ) (hD : D ≠ 0) :
    distInt (R₀ + s * D) = 1 / 8 ↔
      ∃ z : ℤ, s = ((z : ℝ) + 1 / 8 - R₀) / D ∨ s = ((z : ℝ) - 1 / 8 - R₀) / D := by
  rw [distInt_eq_eighth_iff]
  refine exists_congr fun z => ?_
  rw [eq_div_iff hD, eq_div_iff hD]
  constructor <;> rintro (h | h)
  · left; linarith
  · right; linarith
  · left; linarith
  · right; linarith

#print axioms reading_reaches_eighth

/-- **If the reading does not deform (`D = 0`) it is constant along the path.** -/
theorem reading_constant (R₀ s : ℝ) : R₀ + s * 0 = R₀ := by ring

/-- **The same for the path of two grids, at the old instant `a/(8d)`.**  For the pair `(i,k)`, the reading along
`v_s` at `t = a/(8d)` is `Δ a/8 + s (Δ' ρ - Δ) a/8` with `ρ = d'/d`: affine in `s`, slope `(Δ'ρ - Δ) a/8`. -/
theorem grid_path_reading_old (v v' : Fin 8 → ℝ) (d d' v₀ v₀' : ℝ) (hd : 0 < d) (idx idx' : Fin 8 → ℤ)
    (hv : ∀ j, v j = v₀ + (idx j : ℝ) * d) (hv' : ∀ j, v' j = v₀' + (idx' j : ℝ) * d') (a : ℤ) (s : ℝ)
    (i k : Fin 8) :
    (pathSpeed v v' s i - pathSpeed v v' s k) * ((a : ℝ) / (8 * d))
      = (((idx i - idx k) * a : ℤ) : ℝ) / 8
        + s * ((((idx' i - idx' k : ℤ) : ℝ) * (d' / d) - ((idx i - idx k : ℤ) : ℝ)) * (a : ℝ) / 8) := by
  rw [path_reading_affine, reading_at_old_instant v v' d d' v₀ v₀' hd idx idx' hv hv' a i k,
    Cycle.grid_reading_value v d v₀ hd idx hv a k i]
  ring

#print axioms grid_path_reading_old

end GridToGrid

end Fresh
