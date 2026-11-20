import Fresh.SelectRung1

/-!
# SelectRung1Data: the data side of the box-1 select rung (OWED-A and OWED-B)

New file (2026-11-20); nothing existing is edited.  It banks, with exact arithmetic, what
the enumeration actually supports about the two STANDING: OWED hypothesis shapes of
`Fresh.SelectRung1.selectRung1_1_3_4_5_5_5_7`.

## OWED-A (`hdom`): the per-walk domination datum is REFUTED as a uniform datum

The rung's `hdom` demands: for EVERY realizable first-window walk from the start table,
the walk's `chainRun` trace is `TabLe`-below the banked census trace `T8_1_3_4_5_5_5_7_12`.
Data side (`experiments/n8/onefast_audit/selectoweda_v1.py` .. `selectoweda_v3.py`,
exact `Fraction` only, feasibility decided by the ratio-closure itself with the 2-cycle
back-check): the realizable walk class from the closure start `mkTab_1_3_4_5_5_5_7` over
the closed face box (with `g 0 = 1`) has EXACTLY 804 complete walks (lengths 18..28,
no tooth repeats -- strict position increase forbids them).  Cross-checks: the dump's
TABLE-level enumeration (`perrec8_gen_v1.py w0chains2`, 804 words) coincides with this
class AS A SET (0 symmetric difference); every class walk's `mkTab`-fineness demands are
implied by box+seams; no class walk uses a tooth beyond the search's per-row zone cap;
the census word itself is in the class (and passes).  But 564 of the 804 FAIL `TabLe`
against the census trace: the componentwise-loosest complete-walk trace is looser than
the census trace on 12 pairs ((0,1): loosest 850/2511 vs census 110/351; also (0,5),
(0,6), (2,1), (3,0), (3,1), (3,5), (3,6), (4,1), (5,1), (5,6), (6,1)).  So `hdom` cannot
be discharged from the closure start as a box-uniform datum, and the rung cannot supply
the `select` hypothesis of `Fresh.OpeningChainConflict.twoWindows_of_select_opening_record`
for box b1 from census data alone.  Banked below as an exact counterexample: `walk19`
(19 tooth steps, sharing the census word's first 11, whose banked `stepEq_1..11` are
reused) at the exact in-box arrangement `g19`, fully realizable (`UFine` + `ChainRealized`
+ `EnvChain`), whose run's trace violates `TabLe` at pair (0,1): 34/105 vs 110/351.

## OWED-B (`hopen`): the per-arrangement opening record is NONEMPTY, with exact witness

The forced corridor (`hopen_forces_ratio`): every admissible `(j, k, R)` satisfies
`31 * g 6 < 65 * g 1`, i.e. `g 1 / g 6 > 31/65`, and the ratio window
`g 6 * (8k-1) < (8j+1) * g 1 < g 6 * (8k+1)`.  Discrete scan (`selectowedb_v1.py`):
over the face envelope the joint-feasible `(j, k)` are exactly
{(8,4), (9,5), (10,5), (11,6), (12,6)} ((8,5),(8,6),(9,6) pass the demand but are
ratio-infeasible in the box; `j = 13` is R-window-empty).  The supplyable set is
`{in-box g : g 6/g 1 in [13/7, 89/47) or (65/33, 65/31)}` -- a proper subset of the
envelope (the corner `g 1 = 5/2, g 6 = 15/2` has ratio 3 and admits NO record), so no
single `(j, k)` covers the whole face.  Exact witness banked: the rational in-box
arrangement `g2open = ![1, 7/2, 18/5, 23/5, 24/5, 5, 131/20]` (which also satisfies the
closure start's strict orderings, so the SAME point can consume both OWEDs' shapes)
admits `(j, k, R) = (11, 6, 1780/131)`: `g2open 6 * R = 89 = 8*11+1` exactly,
`inZone g2open 1 6 R` (47 < 6230/131 < 49), demand 89/47 <= 65/31.

All arithmetic exact (`norm_num` on literals; data-side scripts run `python3 -I` with
`Fraction` only).  Every theorem carries `#print axioms`; accepted profile is the standard
three -- `sorryAx` is failure.
-/
namespace Fresh.SelectRung1Data

open Fresh.ChainDomBase Fresh.CapChainsOfCarve Fresh.JoinFamComposed Fresh.OneSidedComposed
  Fresh.OneSidedGlue Fresh.UClosure Fresh.SpineSound Fresh.FilterAssembly Fresh.DumpDomData
  Fresh.ChainDomPerRec8 Fresh.WordCoverSide Fresh.SelectRung1

set_option maxHeartbeats 10000000

/-- `mkOf` at the literal box dispatches to the transcribed closure start. -/
theorem mkOf_b1 : mkOf (![1, 3, 4, 5, 5, 5, 7] : Fin 7 → ℤ) = mkTab_1_3_4_5_5_5_7 := by simp [mkOf]
#print axioms mkOf_b1

/-- **Task 1.1 (the `ufine` datum).**  The closure start `mkTab_1_3_4_5_5_5_7` is
realized by every in-box arrangement satisfying the strict orderings the closure itself
encodes (`mk(n)` seeds `g y < g (y+1)` for y = 1..5; the propagated strict entries are
consequences of those + the closed box).  No `ufine_mkOf`-style lemma existed anywhere
in the tree; this is proved on the established literal-table pattern.  The plain
"fine for every face point" statement is FALSE -- see `faceLo_b1_not_fine`. -/
-- STANDING: LEMMA (Task 1.1)
theorem ufine_mkTab_b1 {g : Fin 7 → ℝ}
    (hface : ∀ i, FaceLo (![1, 3, 4, 5, 5, 5, 7] : Fin 7 → ℤ) i ≤ g i ∧ g i ≤ FaceHi (![1, 3, 4, 5, 5, 5, 7] : Fin 7 → ℤ) i)
    (hpin : g 0 = 1)
    (h12 : g 1 < g 2) (h23 : g 2 < g 3) (h34 : g 3 < g 4) (h45 : g 4 < g 5) (h56 : g 5 < g 6) :
    UFine g mkTab_1_3_4_5_5_5_7 := by
  have f0 := hface 0; have f1 := hface 1; have f2 := hface 2; have f3 := hface 3
  have f4 := hface 4; have f5 := hface 5; have f6 := hface 6
  simp [FaceLo, FaceHi] at f0 f1 f2 f3 f4 f5 f6
  have p0 : (0 : ℝ) < g 0 := by linarith
  have p1 : (0 : ℝ) < g 1 := by linarith
  have p2 : (0 : ℝ) < g 2 := by linarith
  have p3 : (0 : ℝ) < g 3 := by linarith
  have p4 : (0 : ℝ) < g 4 := by linarith
  have p5 : (0 : ℝ) < g 5 := by linarith
  have p6 : (0 : ℝ) < g 6 := by linarith
  -- `fin_cases` leaves the Fin literals as `Fin.mk d _`; `norm_num` normalizes only
  -- `d ∈ {0,1}`.  These rfl-lemmas (instance unfolding + proof irrelevance) normalize
  -- the rest to the OfNat form of the p_i/f_i facts, so `rw`/`linarith` match.
  have v2 : (Fin.mk 2 (by omega : (2:ℕ) < 7) : Fin 7) = (2 : Fin 7) := rfl
  have v3 : (Fin.mk 3 (by omega : (3:ℕ) < 7) : Fin 7) = (3 : Fin 7) := rfl
  have v4 : (Fin.mk 4 (by omega : (4:ℕ) < 7) : Fin 7) = (4 : Fin 7) := rfl
  have v5 : (Fin.mk 5 (by omega : (5:ℕ) < 7) : Fin 7) = (5 : Fin 7) := rfl
  have v6 : (Fin.mk 6 (by omega : (6:ℕ) < 7) : Fin 7) = (6 : Fin 7) := rfl
  intro i j c₀ s₀ hc
  fin_cases i <;> fin_cases j <;>
    simp only [mkTab_1_3_4_5_5_5_7, Option.some.injEq, Prod.mk.injEq] at hc <;>
    obtain ⟨rfl, rfl⟩ := hc <;>
    simp only [BHolds] <;> norm_num <;> (try simp only [v2, v3, v4, v5, v6]) <;>
    first
      | rw [div_lt_iff₀ p0] <;> linarith
      | rw [div_lt_iff₀ p1] <;> linarith
      | rw [div_lt_iff₀ p2] <;> linarith
      | rw [div_lt_iff₀ p3] <;> linarith
      | rw [div_lt_iff₀ p4] <;> linarith
      | rw [div_lt_iff₀ p5] <;> linarith
      | rw [div_lt_iff₀ p6] <;> linarith
      | rw [div_le_iff₀ p0] <;> linarith
      | rw [div_le_iff₀ p1] <;> linarith
      | rw [div_le_iff₀ p2] <;> linarith
      | rw [div_le_iff₀ p3] <;> linarith
      | rw [div_le_iff₀ p4] <;> linarith
      | rw [div_le_iff₀ p5] <;> linarith
      | rw [div_le_iff₀ p6] <;> linarith

#print axioms ufine_mkTab_b1

/-- The every-face-point version is FALSE: the pointwise-FaceLo corner of the box (with
`g 0 = 1`, hence an admissible face point) violates the strict closure entries
`(0,4) = (2/9, strict)` and `(3,4) = (1, strict)`. -/
-- STANDING: LEMMA (the boundary refutation of the general `ufine_mkOf` shape)
theorem faceLo_b1_not_fine :
    ¬ UFine (FaceLo (![1, 3, 4, 5, 5, 5, 7] : Fin 7 → ℤ)) mkTab_1_3_4_5_5_5_7 := by
  intro h
  have h34 := h (3 : Fin 7) (4 : Fin 7) (1 : ℚ) true (by simp [mkTab_1_3_4_5_5_5_7])
  simp [BHolds, FaceLo] at h34

#print axioms faceLo_b1_not_fine

/- **Task 1.3 (the `hdom` refutation).**  `walk19` is a realizable first-window walk
from the closure start whose run’s trace is NOT `TabLe`-below the census trace. -/

/-- transcribed trace table of the W19 run (mirror of `Fresh.UClosure`'s `add` semantics; snapshot after the corresponding `add` of the walk). -/
-- STANDING: DEFINITION (transcribed trace table, value-verbatim mirror run)
def W19_1 : UTable := fun p q =>
  if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((34 / 105 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((34 / 135 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((2 / 9 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((33 / 161 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((9 / 49 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 / 7 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((33 / 10 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((187 / 225 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((11 / 15 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((1089 / 1610 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((3 / 5 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((33 / 70 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((187 / 46 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((9 / 7 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((187 / 207 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((6171 / 7406 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((17 / 23 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((187 / 322 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((3179 / 690 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((51 / 35 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((17 / 15 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((34969 / 37030 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((289 / 345 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((3179 / 4830 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((54043 / 10350 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((289 / 175 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((289 / 225 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((17 / 15 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((4913 / 5175 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((54043 / 72450 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((11 / 2 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((187 / 105 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((187 / 135 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((11 / 9 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((363 / 322 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((11 / 14 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((99 / 14 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((561 / 245 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((187 / 105 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((11 / 7 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((33 / 23 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((9 / 7 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

/-- transcribed trace table of the W19 run (mirror of `Fresh.UClosure`'s `add` semantics; snapshot after the corresponding `add` of the walk). -/
-- STANDING: DEFINITION (transcribed trace table, value-verbatim mirror run)
def W19_7 : UTable := fun p q =>
  if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((34 / 105 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((34 / 135 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((2 / 9 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((550 / 2691 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((50 / 273 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((50 / 351 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((33 / 10 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((187 / 225 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((11 / 15 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((605 / 897 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((3 / 5 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((55 / 117 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((187 / 46 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((9 / 7 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((187 / 207 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((51425 / 61893 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((17 / 23 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((4675 / 8073 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((825 / 182 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((51 / 35 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((17 / 15 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((275 / 299 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((75 / 91 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((25 / 39 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((935 / 182 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((289 / 175 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((289 / 225 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((17 / 15 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((85 / 91 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((85 / 117 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((11 / 2 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((187 / 105 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((187 / 135 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((11 / 9 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((3025 / 2691 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((275 / 351 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((99 / 14 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((561 / 245 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((187 / 105 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((11 / 7 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((33 / 23 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((9 / 7 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

/-- transcribed trace table of the W19 run (mirror of `Fresh.UClosure`'s `add` semantics; snapshot after the corresponding `add` of the walk). -/
-- STANDING: DEFINITION (transcribed trace table, value-verbatim mirror run)
def W19_11 : UTable := fun p q =>
  if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((34 / 105 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((34 / 135 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((2 / 9 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((170 / 837 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((50 / 273 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((50 / 351 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((33 / 10 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((187 / 225 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((11 / 15 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((187 / 279 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((3 / 5 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((55 / 117 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((187 / 46 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((9 / 7 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((187 / 207 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((25 / 31 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((17 / 23 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((4675 / 8073 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((825 / 182 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((51 / 35 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((17 / 15 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((85 / 93 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((75 / 91 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((25 / 39 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((935 / 182 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((289 / 175 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((289 / 225 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((17 / 15 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((85 / 91 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((85 / 117 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((11 / 2 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((187 / 105 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((187 / 135 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((11 / 9 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((935 / 837 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((275 / 351 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((99 / 14 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((561 / 245 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((187 / 105 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((11 / 7 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((33 / 23 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((9 / 7 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

/-- transcribed trace table of the W19 run (mirror of `Fresh.UClosure`'s `add` semantics; snapshot after the corresponding `add` of the walk). -/
-- STANDING: DEFINITION (transcribed trace table, value-verbatim mirror run)
def W19_13 : UTable := fun p q =>
  if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((34 / 105 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((34 / 135 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((2 / 9 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((170 / 837 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((50 / 273 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((50 / 351 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((33 / 10 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((187 / 225 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((11 / 15 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((187 / 279 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((3 / 5 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((55 / 117 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((81675 / 20398 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((9 / 7 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((9075 / 10199 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((25 / 31 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((7425 / 10199 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((825 / 1457 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((825 / 182 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((51 / 35 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((17 / 15 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((85 / 93 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((75 / 91 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((25 / 39 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((3267 / 658 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((18513 / 11515 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((2057 / 1645 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((363 / 329 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((297 / 329 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((33 / 47 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((11 / 2 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((187 / 105 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((187 / 135 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((11 / 9 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((935 / 837 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((275 / 351 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((99 / 14 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((561 / 245 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((187 / 105 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((11 / 7 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((33 / 23 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((9 / 7 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

theorem addEqW_23 : uAdd T8_1_3_4_5_5_5_7_10 (6 : Fin 7) (4 : Fin 7) ((33 : ℚ) / (23 : ℚ)) true = some W19_1 :=
  uAdd_eq_some' (by simp [uKeepCur, T8_1_3_4_5_5_5_7_10]; norm_num) (by simp [uBackCond, uBack, T8_1_3_4_5_5_5_7_10]; norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, T8_1_3_4_5_5_5_7_10, W19_1] <;> norm_num)
#print axioms addEqW_23

theorem addEqW_24 : uAdd W19_1 (4 : Fin 7) (6 : Fin 7) ((25 : ℚ) / (33 : ℚ)) true = some W19_1 := by
  simp [uAdd, uKeepCur, uBackCond, uBack, W19_1] <;> norm_num
#print axioms addEqW_24

theorem addEqW_25 : uAdd W19_1 (4 : Fin 7) (1 : Fin 7) ((25 : ℚ) / (15 : ℚ)) true = some W19_1 := by
  simp [uAdd, uKeepCur, uBackCond, uBack, W19_1] <;> norm_num
#print axioms addEqW_25

theorem addEqW_26 : uAdd W19_1 (1 : Fin 7) (4 : Fin 7) ((17 : ℚ) / (25 : ℚ)) true = some W19_1 := by
  simp [uAdd, uKeepCur, uBackCond, uBack, W19_1] <;> norm_num
#print axioms addEqW_26

theorem addEqW_27 : uAdd W19_1 (1 : Fin 7) (3 : Fin 7) ((17 : ℚ) / (23 : ℚ)) true = some W19_1 := by
  simp [uAdd, uKeepCur, uBackCond, uBack, W19_1] <;> norm_num
#print axioms addEqW_27

theorem addEqW_28 : uAdd W19_1 (3 : Fin 7) (1 : Fin 7) ((25 : ℚ) / (17 : ℚ)) true = some W19_1 := by
  simp [uAdd, uKeepCur, uBackCond, uBack, W19_1] <;> norm_num
#print axioms addEqW_28

theorem addEqW_29 : uAdd W19_1 (3 : Fin 7) (6 : Fin 7) ((25 : ℚ) / (39 : ℚ)) true = some W19_7 :=
  uAdd_eq_some' (by simp [uKeepCur, W19_1]; norm_num) (by simp [uBackCond, uBack, W19_1]; norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, W19_1, W19_7] <;> norm_num)
#print axioms addEqW_29

theorem addEqW_30 : uAdd W19_7 (6 : Fin 7) (3 : Fin 7) ((41 : ℚ) / (25 : ℚ)) true = some W19_7 := by
  simp [uAdd, uKeepCur, uBackCond, uBack, W19_7] <;> norm_num
#print axioms addEqW_30

theorem addEqW_31 : uAdd W19_7 (6 : Fin 7) (2 : Fin 7) ((41 : ℚ) / (23 : ℚ)) true = some W19_7 := by
  simp [uAdd, uKeepCur, uBackCond, uBack, W19_7] <;> norm_num
#print axioms addEqW_31

theorem addEqW_32 : uAdd W19_7 (2 : Fin 7) (6 : Fin 7) ((25 : ℚ) / (41 : ℚ)) true = some W19_7 := by
  simp [uAdd, uKeepCur, uBackCond, uBack, W19_7] <;> norm_num
#print axioms addEqW_32

theorem addEqW_33 : uAdd W19_7 (2 : Fin 7) (4 : Fin 7) ((25 : ℚ) / (31 : ℚ)) true = some W19_11 :=
  uAdd_eq_some' (by simp [uKeepCur, W19_7]; norm_num) (by simp [uBackCond, uBack, W19_7]; norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, W19_7, W19_11] <;> norm_num)
#print axioms addEqW_33

theorem addEqW_34 : uAdd W19_11 (4 : Fin 7) (2 : Fin 7) ((33 : ℚ) / (25 : ℚ)) true = some W19_11 := by
  simp [uAdd, uKeepCur, uBackCond, uBack, W19_11] <;> norm_num
#print axioms addEqW_34

theorem addEqW_35 : uAdd W19_11 (4 : Fin 7) (6 : Fin 7) ((33 : ℚ) / (47 : ℚ)) true = some W19_13 :=
  uAdd_eq_some' (by simp [uKeepCur, W19_11]; norm_num) (by simp [uBackCond, uBack, W19_11]; norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, W19_11, W19_13] <;> norm_num)
#print axioms addEqW_35

theorem addEqW_36 : uAdd W19_13 (6 : Fin 7) (4 : Fin 7) ((49 : ℚ) / (33 : ℚ)) true = some W19_13 := by
  simp [uAdd, uKeepCur, uBackCond, uBack, W19_13] <;> norm_num
#print axioms addEqW_36

theorem addEqW_37 : uAdd W19_13 (6 : Fin 7) (3 : Fin 7) ((49 : ℚ) / (31 : ℚ)) true = some W19_13 := by
  simp [uAdd, uKeepCur, uBackCond, uBack, W19_13] <;> norm_num
#print axioms addEqW_37

theorem addEqW_38 : uAdd W19_13 (3 : Fin 7) (6 : Fin 7) ((33 : ℚ) / (49 : ℚ)) true = some W19_13 := by
  simp [uAdd, uKeepCur, uBackCond, uBack, W19_13] <;> norm_num
#print axioms addEqW_38

theorem stepEqW_12 : uStep T8_1_3_4_5_5_5_7_10 (6 : Fin 7) (4 : Fin 7) (33 : ℚ) (23 : ℚ) (25 : ℚ) = some W19_1 := by
  unfold uStep
  rw [uGt_pos T8_1_3_4_5_5_5_7_10 (6 : Fin 7) (4 : Fin 7) (by norm_num) (by norm_num), addEqW_23]
  simp only [Option.bind_some]
  rw [uGt_pos W19_1 (4 : Fin 7) (6 : Fin 7) (by norm_num) (by norm_num)]
  exact addEqW_24
#print axioms stepEqW_12

theorem stepEqW_13 : uStep W19_1 (4 : Fin 7) (1 : Fin 7) (25 : ℚ) (15 : ℚ) (17 : ℚ) = some W19_1 := by
  unfold uStep
  rw [uGt_pos W19_1 (4 : Fin 7) (1 : Fin 7) (by norm_num) (by norm_num), addEqW_25]
  simp only [Option.bind_some]
  rw [uGt_pos W19_1 (1 : Fin 7) (4 : Fin 7) (by norm_num) (by norm_num)]
  exact addEqW_26
#print axioms stepEqW_13

theorem stepEqW_14 : uStep W19_1 (1 : Fin 7) (3 : Fin 7) (17 : ℚ) (23 : ℚ) (25 : ℚ) = some W19_1 := by
  unfold uStep
  rw [uGt_pos W19_1 (1 : Fin 7) (3 : Fin 7) (by norm_num) (by norm_num), addEqW_27]
  simp only [Option.bind_some]
  rw [uGt_pos W19_1 (3 : Fin 7) (1 : Fin 7) (by norm_num) (by norm_num)]
  exact addEqW_28
#print axioms stepEqW_14

theorem stepEqW_15 : uStep W19_1 (3 : Fin 7) (6 : Fin 7) (25 : ℚ) (39 : ℚ) (41 : ℚ) = some W19_7 := by
  unfold uStep
  rw [uGt_pos W19_1 (3 : Fin 7) (6 : Fin 7) (by norm_num) (by norm_num), addEqW_29]
  simp only [Option.bind_some]
  rw [uGt_pos W19_7 (6 : Fin 7) (3 : Fin 7) (by norm_num) (by norm_num)]
  exact addEqW_30
#print axioms stepEqW_15

theorem stepEqW_16 : uStep W19_7 (6 : Fin 7) (2 : Fin 7) (41 : ℚ) (23 : ℚ) (25 : ℚ) = some W19_7 := by
  unfold uStep
  rw [uGt_pos W19_7 (6 : Fin 7) (2 : Fin 7) (by norm_num) (by norm_num), addEqW_31]
  simp only [Option.bind_some]
  rw [uGt_pos W19_7 (2 : Fin 7) (6 : Fin 7) (by norm_num) (by norm_num)]
  exact addEqW_32
#print axioms stepEqW_16

theorem stepEqW_17 : uStep W19_7 (2 : Fin 7) (4 : Fin 7) (25 : ℚ) (31 : ℚ) (33 : ℚ) = some W19_11 := by
  unfold uStep
  rw [uGt_pos W19_7 (2 : Fin 7) (4 : Fin 7) (by norm_num) (by norm_num), addEqW_33]
  simp only [Option.bind_some]
  rw [uGt_pos W19_11 (4 : Fin 7) (2 : Fin 7) (by norm_num) (by norm_num)]
  exact addEqW_34
#print axioms stepEqW_17

theorem stepEqW_18 : uStep W19_11 (4 : Fin 7) (6 : Fin 7) (33 : ℚ) (47 : ℚ) (49 : ℚ) = some W19_13 := by
  unfold uStep
  rw [uGt_pos W19_11 (4 : Fin 7) (6 : Fin 7) (by norm_num) (by norm_num), addEqW_35]
  simp only [Option.bind_some]
  rw [uGt_pos W19_13 (6 : Fin 7) (4 : Fin 7) (by norm_num) (by norm_num)]
  exact addEqW_36
#print axioms stepEqW_18

theorem stepEqW_19 : uStep W19_13 (6 : Fin 7) (3 : Fin 7) (49 : ℚ) (31 : ℚ) (33 : ℚ) = some W19_13 := by
  unfold uStep
  rw [uGt_pos W19_13 (6 : Fin 7) (3 : Fin 7) (by norm_num) (by norm_num), addEqW_37]
  simp only [Option.bind_some]
  rw [uGt_pos W19_13 (3 : Fin 7) (6 : Fin 7) (by norm_num) (by norm_num)]
  exact addEqW_38
#print axioms stepEqW_19

/-- The counterexample walk: 19 tooth steps; the head is the pinned opening’s
z-form, the rest are envelope teeth (rows 1..6, numerators 8j±1). -/
-- STANDING: DEFINITION
def walk19 : List Step :=
  ⟨(6 : Fin 7), zEntry 1, zExit 1⟩ ::
  [⟨(5 : Fin 7), (7 : ℚ), (9 : ℚ)⟩, ⟨(3 : Fin 7), (7 : ℚ), (9 : ℚ)⟩, ⟨(2 : Fin 7), (7 : ℚ), (9 : ℚ)⟩, ⟨(1 : Fin 7), (7 : ℚ), (9 : ℚ)⟩, ⟨(5 : Fin 7), (15 : ℚ), (17 : ℚ)⟩, ⟨(4 : Fin 7), (15 : ℚ), (17 : ℚ)⟩, ⟨(3 : Fin 7), (15 : ℚ), (17 : ℚ)⟩, ⟨(2 : Fin 7), (15 : ℚ), (17 : ℚ)⟩, ⟨(5 : Fin 7), (23 : ℚ), (25 : ℚ)⟩, ⟨(6 : Fin 7), (31 : ℚ), (33 : ℚ)⟩, ⟨(4 : Fin 7), (23 : ℚ), (25 : ℚ)⟩, ⟨(1 : Fin 7), (15 : ℚ), (17 : ℚ)⟩, ⟨(3 : Fin 7), (23 : ℚ), (25 : ℚ)⟩, ⟨(6 : Fin 7), (39 : ℚ), (41 : ℚ)⟩, ⟨(2 : Fin 7), (23 : ℚ), (25 : ℚ)⟩, ⟨(4 : Fin 7), (31 : ℚ), (33 : ℚ)⟩, ⟨(6 : Fin 7), (47 : ℚ), (49 : ℚ)⟩, ⟨(3 : Fin 7), (31 : ℚ), (33 : ℚ)⟩]

/-- The walk, value-literal (the run/realized proofs consume it step by step). -/
theorem walk19_lit : walk19 = { b := 6, A := 7, B := 9 } :: { b := 5, A := 7, B := 9 } ::
    { b := 3, A := 7, B := 9 } :: { b := 2, A := 7, B := 9 } :: { b := 1, A := 7, B := 9 } ::
    { b := 5, A := 15, B := 17 } :: { b := 4, A := 15, B := 17 } :: { b := 3, A := 15, B := 17 } ::
    { b := 2, A := 15, B := 17 } :: { b := 5, A := 23, B := 25 } :: { b := 6, A := 31, B := 33 } ::
    { b := 4, A := 23, B := 25 } :: { b := 1, A := 15, B := 17 } :: { b := 3, A := 23, B := 25 } ::
    { b := 6, A := 39, B := 41 } :: { b := 2, A := 23, B := 25 } :: { b := 4, A := 31, B := 33 } ::
    { b := 6, A := 47, B := 49 } :: { b := 3, A := 31, B := 33 } :: [] := by
  simp [walk19, zEntry, zExit] <;> norm_num

#print axioms walk19_lit

/-- The W19 run from the closure start: peels the banked census step equations for
steps 1-11 and the fresh ones for steps 12-19. -/
theorem run19 :
    chainRun mkTab_1_3_4_5_5_5_7 0 1 walk19 = some (W19_13, (3 : Fin 7), (33 : ℚ)) := by
  rw [← mkOf_b1, walk19_lit]
  simp only [chainRun_step_some stepEq_1_1_3_4_5_5_5_7,
    chainRun_step_some stepEq_2_1_3_4_5_5_5_7,
    chainRun_step_some stepEq_3_1_3_4_5_5_5_7,
    chainRun_step_some stepEq_4_1_3_4_5_5_5_7,
    chainRun_step_some stepEq_5_1_3_4_5_5_5_7,
    chainRun_step_some stepEq_6_1_3_4_5_5_5_7,
    chainRun_step_some stepEq_7_1_3_4_5_5_5_7,
    chainRun_step_some stepEq_8_1_3_4_5_5_5_7,
    chainRun_step_some stepEq_9_1_3_4_5_5_5_7,
    chainRun_step_some stepEq_10_1_3_4_5_5_5_7,
    chainRun_step_some stepEq_11_1_3_4_5_5_5_7,
    chainRun_step_some stepEqW_12,
    chainRun_step_some stepEqW_13,
    chainRun_step_some stepEqW_14,
    chainRun_step_some stepEqW_15,
    chainRun_step_some stepEqW_16,
    chainRun_step_some stepEqW_17,
    chainRun_step_some stepEqW_18,
    chainRun_step_some stepEqW_19,
    chainRun_nil, Option.some.injEq, Prod.mk.injEq]

#print axioms run19

-- STANDING: DEFINITION
noncomputable def g19 : Fin 7 → ℝ := ![1, (13/4 : ℝ), 4, (9/2 : ℝ), (129/26 : ℝ), (11/2 : ℝ), (106/15 : ℝ)]

theorem g19_face : ∀ i, FaceLo (![1, 3, 4, 5, 5, 5, 7] : Fin 7 → ℤ) i ≤ g19 i ∧ g19 i ≤ FaceHi (![1, 3, 4, 5, 5, 5, 7] : Fin 7 → ℤ) i := by
  intro i; fin_cases i <;> simp [FaceLo, FaceHi, g19] <;> norm_num

#print axioms g19_face

theorem g19_ord : g19 1 < g19 2 ∧ g19 2 < g19 3 ∧ g19 3 < g19 4 ∧ g19 4 < g19 5 ∧ g19 5 < g19 6 := by
  simp [g19] <;> norm_num

#print axioms g19_ord

theorem g19_fine : UFine g19 mkTab_1_3_4_5_5_5_7 :=
  ufine_mkTab_b1 g19_face (by simp [g19]) g19_ord.1 g19_ord.2.1 g19_ord.2.2.1
    g19_ord.2.2.2.1 g19_ord.2.2.2.2

#print axioms g19_fine

/-- `ChainRealized g19 mkTab_1_3_4_5_5_5_7 0 1 walk19`: each step survives on its own
trace (the step equations), both strict seam bounds hold at the exact arrangement `g19`,
and the walk ends past `7/g 0` (`7 * g19 3 = 31/2 < 33`). -/
theorem walk19_realized : ChainRealized g19 mkTab_1_3_4_5_5_5_7 0 1 walk19 := by
  rw [← mkOf_b1, walk19_lit]
  exact ⟨T8_1_3_4_5_5_5_7_1, stepEq_1_1_3_4_5_5_5_7, by simp [BHolds, g19, zEntry, zExit] <;> norm_num, by simp [BHolds, g19, zEntry, zExit] <;> norm_num, by simp [BHolds, g19, zEntry, zExit] <;> norm_num, by simp [BHolds, g19, zEntry, zExit] <;> norm_num, ⟨T8_1_3_4_5_5_5_7_2, stepEq_2_1_3_4_5_5_5_7, by simp [BHolds, g19, zEntry, zExit] <;> norm_num, by simp [BHolds, g19, zEntry, zExit] <;> norm_num, by simp [BHolds, g19, zEntry, zExit] <;> norm_num, by simp [BHolds, g19, zEntry, zExit] <;> norm_num, ⟨T8_1_3_4_5_5_5_7_2, stepEq_3_1_3_4_5_5_5_7, by simp [BHolds, g19, zEntry, zExit] <;> norm_num, by simp [BHolds, g19, zEntry, zExit] <;> norm_num, by simp [BHolds, g19, zEntry, zExit] <;> norm_num, by simp [BHolds, g19, zEntry, zExit] <;> norm_num, ⟨T8_1_3_4_5_5_5_7_3, stepEq_4_1_3_4_5_5_5_7, by simp [BHolds, g19, zEntry, zExit] <;> norm_num, by simp [BHolds, g19, zEntry, zExit] <;> norm_num, by simp [BHolds, g19, zEntry, zExit] <;> norm_num, by simp [BHolds, g19, zEntry, zExit] <;> norm_num, ⟨T8_1_3_4_5_5_5_7_4, stepEq_5_1_3_4_5_5_5_7, by simp [BHolds, g19, zEntry, zExit] <;> norm_num, by simp [BHolds, g19, zEntry, zExit] <;> norm_num, by simp [BHolds, g19, zEntry, zExit] <;> norm_num, by simp [BHolds, g19, zEntry, zExit] <;> norm_num, ⟨T8_1_3_4_5_5_5_7_6, stepEq_6_1_3_4_5_5_5_7, by simp [BHolds, g19, zEntry, zExit] <;> norm_num, by simp [BHolds, g19, zEntry, zExit] <;> norm_num, by simp [BHolds, g19, zEntry, zExit] <;> norm_num, by simp [BHolds, g19, zEntry, zExit] <;> norm_num, ⟨T8_1_3_4_5_5_5_7_7, stepEq_7_1_3_4_5_5_5_7, by simp [BHolds, g19, zEntry, zExit] <;> norm_num, by simp [BHolds, g19, zEntry, zExit] <;> norm_num, by simp [BHolds, g19, zEntry, zExit] <;> norm_num, by simp [BHolds, g19, zEntry, zExit] <;> norm_num, ⟨T8_1_3_4_5_5_5_7_8, stepEq_8_1_3_4_5_5_5_7, by simp [BHolds, g19, zEntry, zExit] <;> norm_num, by simp [BHolds, g19, zEntry, zExit] <;> norm_num, by simp [BHolds, g19, zEntry, zExit] <;> norm_num, by simp [BHolds, g19, zEntry, zExit] <;> norm_num, ⟨T8_1_3_4_5_5_5_7_9, stepEq_9_1_3_4_5_5_5_7, by simp [BHolds, g19, zEntry, zExit] <;> norm_num, by simp [BHolds, g19, zEntry, zExit] <;> norm_num, by simp [BHolds, g19, zEntry, zExit] <;> norm_num, by simp [BHolds, g19, zEntry, zExit] <;> norm_num, ⟨T8_1_3_4_5_5_5_7_10, stepEq_10_1_3_4_5_5_5_7, by simp [BHolds, g19, zEntry, zExit] <;> norm_num, by simp [BHolds, g19, zEntry, zExit] <;> norm_num, by simp [BHolds, g19, zEntry, zExit] <;> norm_num, by simp [BHolds, g19, zEntry, zExit] <;> norm_num, ⟨T8_1_3_4_5_5_5_7_10, stepEq_11_1_3_4_5_5_5_7, by simp [BHolds, g19, zEntry, zExit] <;> norm_num, by simp [BHolds, g19, zEntry, zExit] <;> norm_num, by simp [BHolds, g19, zEntry, zExit] <;> norm_num, by simp [BHolds, g19, zEntry, zExit] <;> norm_num, ⟨W19_1, stepEqW_12, by simp [BHolds, g19, zEntry, zExit] <;> norm_num, by simp [BHolds, g19, zEntry, zExit] <;> norm_num, by simp [BHolds, g19, zEntry, zExit] <;> norm_num, by simp [BHolds, g19, zEntry, zExit] <;> norm_num, ⟨W19_1, stepEqW_13, by simp [BHolds, g19, zEntry, zExit] <;> norm_num, by simp [BHolds, g19, zEntry, zExit] <;> norm_num, by simp [BHolds, g19, zEntry, zExit] <;> norm_num, by simp [BHolds, g19, zEntry, zExit] <;> norm_num, ⟨W19_1, stepEqW_14, by simp [BHolds, g19, zEntry, zExit] <;> norm_num, by simp [BHolds, g19, zEntry, zExit] <;> norm_num, by simp [BHolds, g19, zEntry, zExit] <;> norm_num, by simp [BHolds, g19, zEntry, zExit] <;> norm_num, ⟨W19_7, stepEqW_15, by simp [BHolds, g19, zEntry, zExit] <;> norm_num, by simp [BHolds, g19, zEntry, zExit] <;> norm_num, by simp [BHolds, g19, zEntry, zExit] <;> norm_num, by simp [BHolds, g19, zEntry, zExit] <;> norm_num, ⟨W19_7, stepEqW_16, by simp [BHolds, g19, zEntry, zExit] <;> norm_num, by simp [BHolds, g19, zEntry, zExit] <;> norm_num, by simp [BHolds, g19, zEntry, zExit] <;> norm_num, by simp [BHolds, g19, zEntry, zExit] <;> norm_num, ⟨W19_11, stepEqW_17, by simp [BHolds, g19, zEntry, zExit] <;> norm_num, by simp [BHolds, g19, zEntry, zExit] <;> norm_num, by simp [BHolds, g19, zEntry, zExit] <;> norm_num, by simp [BHolds, g19, zEntry, zExit] <;> norm_num, ⟨W19_13, stepEqW_18, by simp [BHolds, g19, zEntry, zExit] <;> norm_num, by simp [BHolds, g19, zEntry, zExit] <;> norm_num, by simp [BHolds, g19, zEntry, zExit] <;> norm_num, by simp [BHolds, g19, zEntry, zExit] <;> norm_num, ⟨W19_13, stepEqW_19, by simp [BHolds, g19, zEntry, zExit] <;> norm_num, by simp [BHolds, g19, zEntry, zExit] <;> norm_num, by simp [BHolds, g19, zEntry, zExit] <;> norm_num, by simp [BHolds, g19, zEntry, zExit] <;> norm_num, by simp [ChainRealized, BHolds, g19] <;> norm_num⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

#print axioms walk19_realized

theorem walk19_env : EnvChain 6 (zExit 1) walk19.tail := by
  refine ⟨by norm_num, ⟨0, rfl⟩, ?_⟩
  intro st hst
  -- one full peel: membership over the 18-step tail becomes a literal disjunction;
  -- then one `rcases` per element (no per-element simp: `List.mem_cons` has nothing
  -- left to rewrite and would error with `made no progress`).
  simp only [walk19, List.tail_cons, List.mem_cons] at hst
  rcases hst with rfl | hst
  · exact ⟨by norm_num, ⟨0, by simp [envA, exitNum] <;> norm_num, by simp [envB, exitNum] <;> norm_num⟩⟩
  rcases hst with rfl | hst
  · exact ⟨by norm_num, ⟨0, by simp [envA, exitNum] <;> norm_num, by simp [envB, exitNum] <;> norm_num⟩⟩
  rcases hst with rfl | hst
  · exact ⟨by norm_num, ⟨0, by simp [envA, exitNum] <;> norm_num, by simp [envB, exitNum] <;> norm_num⟩⟩
  rcases hst with rfl | hst
  · exact ⟨by norm_num, ⟨0, by simp [envA, exitNum] <;> norm_num, by simp [envB, exitNum] <;> norm_num⟩⟩
  rcases hst with rfl | hst
  · exact ⟨by norm_num, ⟨1, by simp [envA, exitNum] <;> norm_num, by simp [envB, exitNum] <;> norm_num⟩⟩
  rcases hst with rfl | hst
  · exact ⟨by norm_num, ⟨1, by simp [envA, exitNum] <;> norm_num, by simp [envB, exitNum] <;> norm_num⟩⟩
  rcases hst with rfl | hst
  · exact ⟨by norm_num, ⟨1, by simp [envA, exitNum] <;> norm_num, by simp [envB, exitNum] <;> norm_num⟩⟩
  rcases hst with rfl | hst
  · exact ⟨by norm_num, ⟨1, by simp [envA, exitNum] <;> norm_num, by simp [envB, exitNum] <;> norm_num⟩⟩
  rcases hst with rfl | hst
  · exact ⟨by norm_num, ⟨2, by simp [envA, exitNum] <;> norm_num, by simp [envB, exitNum] <;> norm_num⟩⟩
  rcases hst with rfl | hst
  · exact ⟨by norm_num, ⟨3, by simp [envA, exitNum] <;> norm_num, by simp [envB, exitNum] <;> norm_num⟩⟩
  rcases hst with rfl | hst
  · exact ⟨by norm_num, ⟨2, by simp [envA, exitNum] <;> norm_num, by simp [envB, exitNum] <;> norm_num⟩⟩
  rcases hst with rfl | hst
  · exact ⟨by norm_num, ⟨1, by simp [envA, exitNum] <;> norm_num, by simp [envB, exitNum] <;> norm_num⟩⟩
  rcases hst with rfl | hst
  · exact ⟨by norm_num, ⟨2, by simp [envA, exitNum] <;> norm_num, by simp [envB, exitNum] <;> norm_num⟩⟩
  rcases hst with rfl | hst
  · exact ⟨by norm_num, ⟨4, by simp [envA, exitNum] <;> norm_num, by simp [envB, exitNum] <;> norm_num⟩⟩
  rcases hst with rfl | hst
  · exact ⟨by norm_num, ⟨2, by simp [envA, exitNum] <;> norm_num, by simp [envB, exitNum] <;> norm_num⟩⟩
  rcases hst with rfl | hst
  · exact ⟨by norm_num, ⟨3, by simp [envA, exitNum] <;> norm_num, by simp [envB, exitNum] <;> norm_num⟩⟩
  rcases hst with rfl | hst
  · exact ⟨by norm_num, ⟨5, by simp [envA, exitNum] <;> norm_num, by simp [envB, exitNum] <;> norm_num⟩⟩
  rcases hst with rfl | hst
  · exact ⟨by norm_num, ⟨3, by simp [envA, exitNum] <;> norm_num, by simp [envB, exitNum] <;> norm_num⟩⟩
  exact absurd hst (by simp)

#print axioms walk19_env

/-- The refutation: the W19 run’s trace violates `TabLe` against the census trace at
pair (0,1): its stored 34/105 exceeds the census 110/351. -/
theorem walk19_not_hdom :
    ¬ (∀ V : UTable, ∀ af : Fin 7, ∀ Af : ℚ,
        chainRun mkTab_1_3_4_5_5_5_7 0 1 walk19 = some (V, af, Af) →
        TabLe V T8_1_3_4_5_5_5_7_12) := by
  intro h
  obtain ⟨c₀, s₀, hW, hle⟩ :=
    h W19_13 (3 : Fin 7) (33 : ℚ) run19 0 1 (110 / 351 : ℚ) true (by simp [T8_1_3_4_5_5_5_7_12])
  have h01 : W19_13 0 1 = some ((34 / 105 : ℚ), true) := by simp [W19_13]
  rw [h01] at hW
  simp only [Option.some.injEq, Prod.mk.injEq] at hW
  obtain ⟨rfl, rfl⟩ := hW
  norm_num at hle

#print axioms walk19_not_hdom

/-- **THE OWED-A VERDICT.**  The rung’s `hdom` OWED is not supplyable as a box-uniform
datum: there is a fully admissible instance (closed face box, `g 0 = 1`, the closure
start realized, the walk realizable AND in the consumer’s `EnvChain` class) whose run
violates the domination. -/
-- STANDING: DATA-REFUTATION (Task 1.3)
theorem selectRung1_hdom_owed_unsupplyable_b1 :
    ∃ (g : Fin 7 → ℝ) (walk : List Step),
      (∀ i, FaceLo (![1, 3, 4, 5, 5, 5, 7] : Fin 7 → ℤ) i ≤ g i ∧ g i ≤ FaceHi (![1, 3, 4, 5, 5, 5, 7] : Fin 7 → ℤ) i) ∧
      g 0 = 1 ∧ UFine g mkTab_1_3_4_5_5_5_7 ∧
      ChainRealized g mkTab_1_3_4_5_5_5_7 0 1 walk ∧
      EnvChain 6 (zExit 1) walk.tail ∧
      ¬ (∀ V : UTable, ∀ af : Fin 7, ∀ Af : ℚ,
          chainRun mkTab_1_3_4_5_5_5_7 0 1 walk = some (V, af, Af) →
          TabLe V T8_1_3_4_5_5_5_7_12) :=
  ⟨g19, walk19, g19_face, by simp [g19], g19_fine, walk19_realized, walk19_env,
    walk19_not_hdom⟩

#print axioms selectRung1_hdom_owed_unsupplyable_b1

/-- **Task 2 (the forced corridor).**  Every admissible opening record forces
`(31 : ℝ) * g 6 < (65 : ℝ) * g 1`, i.e. `g 1 / g 6 > 31/65`, together with the exact
ratio window `g 6 * (8k-1) < (8j+1) * g 1 < g 6 * (8k+1)`. -/
-- STANDING: LEMMA (Task 2: forced corridor)
theorem hopen_forces_ratio {g : Fin 7 → ℝ} {j k : ℕ} {R : ℝ}
    (hR9 : 9 ≤ R) (hk1 : 1 ≤ k)
    (heq : g 6 * R = (j : ℝ) * 8 + 1)
    (hin : inZone g (1 : Fin 7) k R)
    (hdem : ((j : ℝ) * 8 + 1) / ((k : ℝ) * 8 - 1) ≤ (65 : ℝ) / 31) :
    (31 : ℝ) * g 6 < (65 : ℝ) * g 1 ∧
      g 6 * ((k : ℝ) * 8 - 1) < ((j : ℝ) * 8 + 1) * g 1 ∧
      ((j : ℝ) * 8 + 1) * g 1 < g 6 * ((k : ℝ) * 8 + 1) := by
  have hR : (0 : ℝ) < R := by linarith
  have hden : (0 : ℝ) < (k : ℝ) * 8 - 1 := by
    have hk' : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
    linarith
  have hnum : (0 : ℝ) < (j : ℝ) * 8 + 1 := by positivity
  have h1 : ((j : ℝ) * 8 + 1) ≤ (65 : ℝ) / 31 * ((k : ℝ) * 8 - 1) := (div_le_iff₀ hden).mp hdem
  have h2 : ((k : ℝ) * 8 - 1) < g 1 * R := hin.1
  have h2' : g 1 * R < ((k : ℝ) * 8 + 1) := hin.2
  have h3 : g 6 * R ≤ (65 : ℝ) / 31 * ((k : ℝ) * 8 - 1) := by rw [heq]; exact h1
  have h4 : (65 : ℝ) / 31 * ((k : ℝ) * 8 - 1) < (65 : ℝ) / 31 * (g 1 * R) :=
    mul_lt_mul_of_pos_left h2 (by norm_num)
  have h5 : g 6 * R < ((65 : ℝ) / 31 * g 1) * R := by
    have h45 : ((65 : ℝ) / 31 * g 1) * R = (65 : ℝ) / 31 * (g 1 * R) := by ring
    rw [h45]
    exact lt_of_le_of_lt h3 h4
  have h6 : g 6 < (65 : ℝ) / 31 * g 1 := by
    by_contra hcon
    push_neg at hcon
    -- both sides right-multiplied by R (same syntactic atoms, so linarith closes)
    have hP : (65 : ℝ) / 31 * g 1 * R ≤ g 6 * R := mul_le_mul_of_nonneg_right hcon hR.le
    linarith
  refine ⟨by linarith, ?_, ?_⟩
  · have e1 : g 6 * ((k : ℝ) * 8 - 1) * R = ((j : ℝ) * 8 + 1) * ((k : ℝ) * 8 - 1) := by
      rw [← heq]; ring
    have e2 : ((j : ℝ) * 8 + 1) * ((k : ℝ) * 8 - 1) < ((j : ℝ) * 8 + 1) * (g 1 * R) :=
      mul_lt_mul_of_pos_left h2 hnum
    have e3 : g 6 * ((k : ℝ) * 8 - 1) * R < ((j : ℝ) * 8 + 1) * g 1 * R := by
      rw [e1]
      exact e2.trans_le (le_of_eq (by ring))
    nlinarith [hR, e3]
  · have f1 : ((j : ℝ) * 8 + 1) * g 1 * R < ((j : ℝ) * 8 + 1) * ((k : ℝ) * 8 + 1) := by
      have h := mul_lt_mul_of_pos_left h2' hnum
      have e : ((j : ℝ) * 8 + 1) * g 1 * R = ((j : ℝ) * 8 + 1) * (g 1 * R) := by ring
      rw [e]; exact h
    have f3 : g 6 * ((k : ℝ) * 8 + 1) * R = (g 6 * R) * ((k : ℝ) * 8 + 1) := by ring
    have f4 : g 6 * ((k : ℝ) * 8 + 1) * R = ((j : ℝ) * 8 + 1) * ((k : ℝ) * 8 + 1) := by rw [f3, heq]
    nlinarith [hR, f1, f4]

#print axioms hopen_forces_ratio

/-- **Task 2 (exact witness).**  The rational in-box arrangement `g2open` (which also
satisfies the closure start’s strict orderings, so the SAME point can consume both
OWEDs’ hypothesis shapes) admits the opening record `(j, k, R) = (11, 6, 1780/131)`. -/
-- STANDING: DEFINITION
noncomputable def g2open : Fin 7 → ℝ := ![1, (7/2 : ℝ), (18/5 : ℝ), (23/5 : ℝ), (24/5 : ℝ), 5, (131/20 : ℝ)]

theorem g2open_face : ∀ i, FaceLo (![1, 3, 4, 5, 5, 5, 7] : Fin 7 → ℤ) i ≤ g2open i ∧ g2open i ≤ FaceHi (![1, 3, 4, 5, 5, 5, 7] : Fin 7 → ℤ) i := by
  intro i; fin_cases i <;> simp [FaceLo, FaceHi, g2open] <;> norm_num

#print axioms g2open_face

theorem g2open_ord : g2open 1 < g2open 2 ∧ g2open 2 < g2open 3 ∧ g2open 3 < g2open 4 ∧
    g2open 4 < g2open 5 ∧ g2open 5 < g2open 6 := by simp [g2open] <;> norm_num

#print axioms g2open_ord

theorem g2open_fine : UFine g2open mkTab_1_3_4_5_5_5_7 :=
  ufine_mkTab_b1 g2open_face (by simp [g2open]) g2open_ord.1 g2open_ord.2.1
    g2open_ord.2.2.1 g2open_ord.2.2.2.1 g2open_ord.2.2.2.2

#print axioms g2open_fine

-- STANDING: DATA (Task 2 witness)
theorem hopen_witness_b1 :
    9 ≤ ((1780 / 131 : ℚ) : ℝ) ∧ ((1780 / 131 : ℚ) : ℝ) ≤ 15 ∧ 1 ≤ 6 ∧
    g2open 6 * ((1780 / 131 : ℚ) : ℝ) = (11 : ℝ) * 8 + 1 ∧
    inZone g2open (1 : Fin 7) 6 ((1780 / 131 : ℚ) : ℝ) ∧
    ((11 : ℝ) * 8 + 1) / ((6 : ℝ) * 8 - 1) ≤ (65 : ℝ) / 31 := by
  simp only [inZone, g2open]
  push_cast
  norm_num

#print axioms hopen_witness_b1

end Fresh.SelectRung1Data
