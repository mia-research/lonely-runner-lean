import Fresh.UClosureKill

/-!
# M4FixBankC3: the C3 fixpoint bank — inventory, one worked instance, and the composition blocker

New file (2026-11-21, review-order item 4); nothing existing is edited.  Input data:
`experiments/n8/m4comp_uclosure_ckpt_v2.jsonl` (25,226 lines; field census in
`experiments/n8/m4fix_inventory.out`, parser `m4fix_inventory.py`), recompute-with-recording
`experiments/n8/m4fix_recompute.py` + `m4fix_recompute_1_1_1_5_7_12.json`.

## 1. The inventory (the honest data-side finding)

The checkpoint is a VERDICT-SUMMARY format: every line carries exactly `{t, key, killed,
nstates, ceil}` (avg 87.6 bytes; 12,613 boxes x 2 merge keys; exactly 10,211 lines with
`key='aA'` and `killed=true` — the C3 bank target count, matching
`m4comp_uclosure_v2.out`'s "aA-key: M4 killed 10211/12540").  Against `Fresh.UClosure.Fixpoint`'s
four fields the census is:

| Fixpoint field              | checkpoint carries? | note |
|-----------------------------|---------------------|------|
| `states : Finset (Fin 6 x Fin 15)` | count only (`nstates`) | the `(a, Aex)` key set is not recorded |
| `table : key -> UTable`     | NO                  | the per-key merged 7x7 tables are not recorded |
| `rank : key -> Fin 7`       | derivable           | `rank k = rowOf k.1` (canonical), needs the key set |
| `aex : key -> Q`            | derivable           | `aex k = envB k.2 = B0` exactly (aA keys), needs the key set |
| seed (opening record)       | NO                  | the pre-fold `st` dict (keys + opening tables + P) unrecorded |
| iteration count T           | NO                  | the convergence round is unrecorded (`boxAdmit_of_kill` needs `T >= 112`) |

So the bank is NOT mechanical from the checkpoint: the generator
(`m4comp_uclosure_sweep_v2.py` -> `merged_kill`) needs a re-run with recording.  Minimum
fields to record per box: (1) the final `st` — list of `{a, Aex, U (7x7 of null|[num,str,bool]), P}`;
(2) the opening record (pre-fold seed, same shape); (3) the convergence round count.
The recompute script demonstrates the recorded form on the smallest killed box and
reproduces the checkpoint line field-for-field (`killed=True, nstates=1, ceil=17/7`).

## 2. The worked instance (smallest checkpoint box `(1,1,1,5,7,12)`, nstates = 1)

The recomputed final record: one state, key `(a=4, Aex=9)` — the Lean key
`((4 : Fin 6), (0 : Fin 15))` (`rowOf 4 = 5`, `envB 0 = 9`) — with the merged 7x7 table of
`m4fix_recompute_1_1_1_5_7_12.json`.  Emitted verbatim:
`m4fixTab_1_1_1_5_7_12` (the 49-cell table literal), `m4fix_1_1_1_5_7_12 : Fixpoint`
(states = that singleton; table = the literal at the state key and the trivial `none` table
off it; rank/aex canonical), `m4fixData_1_1_1_5_7_12 : FixKilled m4fix_1_1_1_5_7_12` — the
checkpoint's `killed=true` verdict at the converged record (T = 0 in `fixIter` terms),
kernel-checked, no axioms.  Proof discipline: the machinery's `decide`-on-`Q` conditions do
not kernel-reduce, so every one is discharged by the `decide_eq_true_iff` /
`decide_eq_false_iff_not` bridge with `norm_num`-proved comparisons; the Nat-matched table
literal DOES kernel-reduce (`rfl`).

## 3. Blocker A (the fold, mechanical): FixKilled at T >= 1 is FALSE for this seed

`fixRound` gives every first-birth key the trivial all-`none` table (its accumulator base is
`fun _ _ => none`, and `uLooserB none _ = none`, so every merged contribution is killed).
The recomputed record's single state has TWO surviving fixpoint children (checked
computationally: keys `(3,0)` and `(5,1)`; the survivor `(5,1)` is proved in Lean below),
and a first-birth key's all-`none` table never rejects the direct exit check.  Hence
`FixKilled (fixIter m4fix_1_1_1_5_7_12 T)` is FALSE for every `T >= 1`
(`m4fixNotKilled_ge1_1_1_1_5_7_12`), while `boxAdmit_of_kill` needs it at `T >= 112`.
The Python engine's kill verdict is about the PRUNED fixpoint (reach_utc + P-frontier
pruning, and first births store the child table itself); the Lean fold is an
over-approximation whose T >= 1 records are generically not killable from a converged
Python record.  The two engines do not meet at any `T >= 1`; the checkpoint's verdict
corresponds to `fixIter`-time `T = 0` only.

## 4. Blocker B (the composition, mechanical): the would-be hypothesis set is EMPTY

`boxAdmit_of_kill` consumes `hseedfine : ∀ (ρ : Fin 7 → ℝ), (∀ k, 0 < ρ k) → ∀ k ∈
seed.states, UFine ρ (seed.table k)` — fineness of the SEED tables by EVERY positive
vector.  No finite off-diagonal bound holds for every positive vector, so a
universally-fine table has `none` at every off-diagonal cell (`univFine_none` below).
The fold only loosens tables (every round merges `uLooser acc V`, cellwise looser than
`acc`), so every round-T table of a universally-fine seed is again universally fine, and an
all-`none` exit back-cell `(0, rowOf k.1)` never rejects — `uExitOK` passes on every state.
Since `hopen` forces `seed.states` to contain all 90 keys, `FixKilled` must fail on a
nonempty state set: the hypothesis tuple `(hcanon, hopen, hseedfine, hclose)` of
`boxAdmit_of_kill` is JOINTLY UNSATISFIABLE for every seed and every T
(`c3fix_unsat` below, kernel-checked, no axioms).  The composed route from
`Fresh.UClosureKill.boxAdmit_of_kill` to the per-box admission theorem is therefore
VACUOUS as stated: the instance compiles (`m4fixAdmit_of_E810_vacuous`, by explosion) but
no data can discharge its hypotheses.  Repairing the route requires editing
`Fresh.UClosureKill.lean` (weaken `hseedfine` to in-box `ρ` with the seed tables carrying
the box's face bounds; give first-birth keys their child table as the Python engine does;
record the per-box seed + T) — out of scope for a new-files-only rung; named honestly here.

## Verdict

The C3 bank is NOT mechanical from `m4comp_uclosure_ckpt_v2.jsonl`: (a) the checkpoint
lacks every Fixpoint field beyond the verdict; (b) even a full recording re-dump gives the
Python fixpoint, not the Lean fold's (Blocker A); (c) the composition
`boxAdmit_of_kill` cannot be instantiated by ANY data (Blocker B).  The bank needs the
generator re-run with recording AND the three named repairs in `UClosureKill.lean` before
per-box emission can reach `M4BoxNoCarvePinned`.  This rung banks the inventory, the
worked instance, and both blockers as kernel-checked facts.
-/

namespace Fresh.M4FixBankC3

open Fresh.UClosure Fresh.FilterAssembly

/-! ## 0. The Prop-to-Bool bridges for the machinery's `decide`-on-`Q` conditions

The `m4comp_lib_v1`-verbatim definitions test `Q` comparisons through `decide`, and those
`Decidable` instances do not kernel-reduce (the Rat literal arithmetic inside them is not
`decide`-evaluable by `rfl`).  Every evaluation below therefore rewrites each condition by
the iff-bridges with a `norm_num`-proved comparison, then closes the residual Bool
arithmetic by `rfl`. -/

theorem decEQ_true {a b : ℚ} (h : a = b) : decide (a = b) = true := by
  rw [decide_eq_true_iff]; exact h

theorem decEQ_false {a b : ℚ} (h : ¬ a = b) : decide (a = b) = false := by
  rw [decide_eq_false_iff_not]; exact h

theorem decLT_true {a b : ℚ} (h : a < b) : decide (a < b) = true := by
  rw [decide_eq_true_iff]; exact h

theorem decLT_false {a b : ℚ} (h : ¬ a < b) : decide (a < b) = false := by
  rw [decide_eq_false_iff_not]; exact h

/-! ## 1. The worked record (smallest checkpoint-killed box `(1,1,1,5,7,12)`, nstates = 1)

Verbatim the merged table of the single final state (a=4, Aex=9) from
`m4fix_recompute_1_1_1_5_7_12.json` (the recording re-run of `merged_kill`, which
reproduces the checkpoint line exactly).  Rows/columns are the 7 rows of the ratio system;
cells are `(value, strict)` bounds, `none` = unbounded. -/

def m4fixTab_1_1_1_5_7_12 : UTable := fun i j =>
  match i.val, j.val with
  | 0, 0 => some (1, false)     | 0, 1 => some (1, true)
  | 0, 2 => some (1, true)      | 0, 3 => some (1, true)
  | 0, 4 => some (2 / 9, false) | 0, 5 => some (1 / 7, true)
  | 0, 6 => some (2 / 23, false)
  | 1, 0 => some (3 / 2, true)  | 1, 1 => some (1, false)
  | 1, 2 => some (1, true)      | 1, 3 => some (1, true)
  | 1, 4 => some (1 / 3, true)  | 1, 5 => some (3 / 14, true)
  | 1, 6 => some (3 / 23, true)
  | 2, 0 => some (3 / 2, true)  | 2, 1 => some (3 / 2, true)
  | 2, 2 => some (1, false)     | 2, 3 => some (1, true)
  | 2, 4 => some (1 / 3, true)  | 2, 5 => some (3 / 14, true)
  | 2, 6 => some (3 / 23, true)
  | 3, 0 => some (3 / 2, false) | 3, 1 => some (3 / 2, true)
  | 3, 2 => some (3 / 2, true)  | 3, 3 => some (1, false)
  | 3, 4 => some (1 / 3, false) | 3, 5 => some (3 / 14, true)
  | 3, 6 => some (3 / 23, false)
  | 4, 0 => some (11 / 2, false) | 4, 1 => some (11 / 2, true)
  | 4, 2 => some (11 / 2, true)  | 4, 3 => some (11 / 2, true)
  | 4, 4 => some (1, false)      | 4, 5 => some (11 / 14, true)
  | 4, 6 => some (11 / 23, false)
  | 5, 0 => some (15 / 2, false) | 5, 1 => some (15 / 2, true)
  | 5, 2 => some (15 / 2, true)  | 5, 3 => some (15 / 2, true)
  | 5, 4 => some (5 / 3, false)  | 5, 5 => some (1, false)
  | 5, 6 => some (15 / 23, false)
  | 6, 0 => some (25 / 2, false) | 6, 1 => some (25 / 2, true)
  | 6, 2 => some (25 / 2, true)  | 6, 3 => some (25 / 2, true)
  | 6, 4 => some (25 / 9, false) | 6, 5 => some (25 / 14, true)
  | 6, 6 => some (1, false)
  | _, _ => none

/-- The recomputed final fixpoint record for box `(1,1,1,5,7,12)`: one state (the aA key
`(a=4, Aex=9)` in Lean encoding `((4 : Fin 6), (0 : Fin 15))`), the merged table above at
the state key (the trivial table off it), rank/exit-numerator canonical (`rowOf`/`envB`). -/
def m4fix_1_1_1_5_7_12 : Fixpoint :=
  { states := {((4 : Fin 6), (0 : Fin 15))}
    table := fun k =>
      if k = ((4 : Fin 6), (0 : Fin 15)) then m4fixTab_1_1_1_5_7_12 else fun _ _ => none
    rank := fun k => rowOf k.1
    aex := fun k => envB k.2 }

/-- The canonical rank/exit-numerator hypothesis of the worked record (`hcanon` shape of
`boxAdmit_of_kill`). -/
theorem m4fixCanon_1_1_1_5_7_12 :
    (∀ k, m4fix_1_1_1_5_7_12.rank k = rowOf k.1) ∧
      (∀ k, m4fix_1_1_1_5_7_12.aex k = envB k.2) := ⟨fun _ => rfl, fun _ => rfl⟩

/-- The exit-numerator / entry-edge literals of the worked state's key. -/
theorem m4fixenvB0 : envB (0 : Fin 15) = (9 : ℚ) := by
  simp only [envB, exitNum]; norm_num

theorem m4fixenvA1 : envA (1 : Fin 15) = (15 : ℚ) := by
  simp only [envA, exitNum]; norm_num

theorem m4fixenvB1 : envB (1 : Fin 15) = (17 : ℚ) := by
  simp only [envB, exitNum]; norm_num

/-- The table cells read by the worked instance's evaluations (the Nat-matched table
literal kernel-reduces). -/
theorem m4fixh50 : m4fixTab_1_1_1_5_7_12 (rowOf (4 : Fin 6)) 0 = some ((15 / 2 : ℚ), false) :=
  rfl
theorem m4fixh05 : m4fixTab_1_1_1_5_7_12 0 (rowOf (4 : Fin 6)) = some ((1 / 7 : ℚ), true) :=
  rfl
theorem m4fixh56 : m4fixTab_1_1_1_5_7_12 (rowOf (4 : Fin 6)) (rowOf (5 : Fin 6)) =
    some ((15 / 23 : ℚ), false) := rfl
theorem m4fixh65 : m4fixTab_1_1_1_5_7_12 (rowOf (5 : Fin 6)) (rowOf (4 : Fin 6)) =
    some ((25 / 14 : ℚ), true) := rfl

/-- The worked record's field values at the two keys touched by the child-step evaluation
(the record projections kernel-reduce). -/
theorem m4fixhtab0 : m4fix_1_1_1_5_7_12.table ((4 : Fin 6), (0 : Fin 15)) =
    m4fixTab_1_1_1_5_7_12 := rfl
theorem m4fixhrank0 : m4fix_1_1_1_5_7_12.rank ((4 : Fin 6), (0 : Fin 15)) =
    rowOf (4 : Fin 6) := rfl
theorem m4fixhaex0 : m4fix_1_1_1_5_7_12.aex ((4 : Fin 6), (0 : Fin 15)) =
    envB (0 : Fin 15) := rfl
theorem m4fixhrank1 : m4fix_1_1_1_5_7_12.rank ((5 : Fin 6), (1 : Fin 15)) =
    rowOf (5 : Fin 6) := rfl
theorem m4fixhaex1 : m4fix_1_1_1_5_7_12.aex ((5 : Fin 6), (1 : Fin 15)) =
    envB (1 : Fin 15) := rfl

/-- **The worked instance's data theorem**: the checkpoint's `killed=true` verdict for box
`(1,1,1,5,7,12)` (nstates = 1, ceil 17/7, converged after 1 round — recompute matches the
checkpoint line field-for-field), as the `FixKilled` predicate at the converged record.
The single state's direct exit check: keep-cur is false (`15/2 ≮ 9/7`), the back-bound
`ρ₀/ρ₅ < 1/7` gives `1/7 · 9/7 = 9/49 < 1`, so the exit `add` rejects. -/
theorem m4fixData_1_1_1_5_7_12 : FixKilled m4fix_1_1_1_5_7_12 := by
  unfold FixKilled
  intro k hk
  simp only [m4fix_1_1_1_5_7_12, Finset.mem_singleton] at hk
  subst hk
  show (uAdd m4fixTab_1_1_1_5_7_12 (rowOf (4 : Fin 6)) 0
      ((envB (0 : Fin 15)) / 7) true).isSome = false
  rw [show (envB (0 : Fin 15)) / 7 = (9 : ℚ) / 7 from by simp only [m4fixenvB0]]
  have hadd : uAdd m4fixTab_1_1_1_5_7_12 (rowOf (4 : Fin 6)) 0 ((9 : ℚ) / 7) true = none := by
    simp only [uAdd, uKeepCur, uBack, uBackCond, m4fixh50, m4fixh05,
      decLT_false (by norm_num : ¬ ((15 / 2 : ℚ) < (9 / 7 : ℚ))),
      decEQ_false (by norm_num : ¬ ((15 / 2 : ℚ) = (9 / 7 : ℚ))),
      decLT_true (by norm_num : (1 / 7 : ℚ) * (9 / 7 : ℚ) < (1 : ℚ))]
    simp
  rw [hadd]
  rfl

#print axioms m4fixData_1_1_1_5_7_12

/-! ## 2. Blocker A, mechanically: the fold's verdict at `T ≥ 1` is FALSE for the worked seed

The state `(5,1)` is born at round 1 (its `uStepF` from `(4,0)` survives — the two `gt`
steps land on strict `add`s by `uGt_pos`: `ρ₅/ρ₆ < 9/15` against back `25/14` gives
`15/14 > 1`, no rejection; then `ρ₆/ρ₅ < 17/9` is keep-cur on `25/14`), receives the
trivial table, and the trivial table never rejects any exit check.  First-birth tables
stay trivial forever (`childTab` merging into `fun _ _ => none` returns
`fun _ _ => none`), so the state's exit check passes at every round `T ≥ 1`. -/

/-- Merging into the trivial table is trivial: `uLooserB none _ = none`. -/
theorem childTab_none (F : Fixpoint) (ck k : Fin 6 × Fin 15) :
    childTab F ck k (fun _ _ => none) = fun _ _ => none := by
  unfold childTab
  cases h : uStepF F k ck with
  | none => rfl
  | some V =>
    funext i j
    simp [uLooser, uLooserB]

/-- The fixpoint round's table fold from the trivial base stays trivial. -/
theorem foldl_childTab_none (F : Fixpoint) (ck : Fin 6 × Fin 15)
    (l : List (Fin 6 × Fin 15)) :
    l.foldl (fun acc k => childTab F ck k acc) (fun _ _ => none) = fun _ _ => none := by
  induction l with
  | nil => rfl
  | cons k l ih =>
    rw [List.foldl_cons, childTab_none]
    exact ih

/-- The round's table at a key stays trivial whenever the base (the membership-conditional
seed table) is trivial. -/
theorem fixRound_table_none_of (F : Fixpoint) (ck : Fin 6 × Fin 15)
    (hbase : (if ck ∈ F.states then F.table ck else fun _ _ => none) = fun _ _ => none) :
    (fixRound F).table ck = fun _ _ => none := by
  simp only [fixRound]
  rw [hbase]
  exact foldl_childTab_none F ck F.states.toList

/-- The surviving child contribution of the worked state toward `(5,1)`: the first `add`'s
propagated table, whose `(ρ₆, ρ₅)` cell keeps the stored `25/14` bound (the propagated
`375/196` is not tighter). -/
def m4fixV1 : UTable :=
  uProp m4fixTab_1_1_1_5_7_12 (rowOf (4 : Fin 6)) (rowOf (5 : Fin 6)) ((9 : ℚ) / 15) true

/-- The worked seed's child step to `(5,1)` survives: the two-`gt` chain step returns
`some m4fixV1` and a further surviving `add` (keep-cur on `25/14 < 17/9`), so `isSome`. -/
theorem m4fixChildB_1_1_1_5_7_12 :
    (uStepF m4fix_1_1_1_5_7_12 ((4 : Fin 6), (0 : Fin 15)) ((5 : Fin 6), (1 : Fin 15))).isSome
      = true := by
  have hadd1 : uGt m4fixTab_1_1_1_5_7_12 (9 : ℚ) (rowOf (4 : Fin 6)) (15 : ℚ)
      (rowOf (5 : Fin 6)) = some m4fixV1 := by
    rw [uGt_pos m4fixTab_1_1_1_5_7_12 (rowOf (4 : Fin 6)) (rowOf (5 : Fin 6))
      (by norm_num : (0 : ℚ) < 9) (by norm_num : (0 : ℚ) < 15)]
    simp only [uAdd, uKeepCur, uBack, uBackCond, m4fixV1, m4fixh56, m4fixh65,
      decLT_false (by norm_num : ¬ ((15 / 23 : ℚ) < (9 / 15 : ℚ))),
      decEQ_false (by norm_num : ¬ ((15 / 23 : ℚ) = (9 / 15 : ℚ))),
      decLT_false (by norm_num : ¬ ((25 / 14 : ℚ) * (9 / 15 : ℚ) < (1 : ℚ))),
      decEQ_false (by norm_num : ¬ ((25 / 14 : ℚ) * (9 / 15 : ℚ) = (1 : ℚ)))]
    simp
  have hV1cell : m4fixV1 (rowOf (5 : Fin 6)) (rowOf (4 : Fin 6)) = some ((25 / 14 : ℚ), true) := by
    simp only [m4fixV1, uProp, uTighter, m4fixh65,
      decLT_false (by norm_num : ¬ ((25 / 14 : ℚ) * (9 / 15 : ℚ) * (25 / 14 : ℚ) < (25 / 14 : ℚ))),
      decEQ_false (by norm_num : ¬ ((25 / 14 : ℚ) * (9 / 15 : ℚ) * (25 / 14 : ℚ) = (25 / 14 : ℚ)))]
    rfl
  have hadd2 : uGt m4fixV1 (17 : ℚ) (rowOf (5 : Fin 6)) (9 : ℚ) (rowOf (4 : Fin 6))
      = some m4fixV1 := by
    rw [uGt_pos m4fixV1 (rowOf (5 : Fin 6)) (rowOf (4 : Fin 6))
      (by norm_num : (0 : ℚ) < 17) (by norm_num : (0 : ℚ) < 9)]
    simp only [uAdd, uKeepCur, hV1cell,
      decLT_true (by norm_num : (25 / 14 : ℚ) < (17 / 9 : ℚ))]
    simp
  have hmem' : uStepF m4fix_1_1_1_5_7_12 ((4 : Fin 6), (0 : Fin 15)) ((5 : Fin 6), (1 : Fin 15))
      = some m4fixV1 := by
    simp only [uStepF, uStep, m4fixhtab0, m4fixhrank0, m4fixhaex0,
      m4fixenvB0, m4fixenvA1, m4fixenvB1]
    rw [hadd1]
    show uGt m4fixV1 (17 : ℚ) (rowOf (5 : Fin 6)) (9 : ℚ) (rowOf (4 : Fin 6)) = some m4fixV1
    rw [hadd2]
  rw [hmem']
  rfl

theorem m4fixChild_1_1_1_5_7_12 :
    uStepF m4fix_1_1_1_5_7_12 ((4 : Fin 6), (0 : Fin 15)) ((5 : Fin 6), (1 : Fin 15)) ≠ none := by
  intro h
  have h2 : (uStepF m4fix_1_1_1_5_7_12 ((4 : Fin 6), (0 : Fin 15))
      ((5 : Fin 6), (1 : Fin 15))).isSome = false := by
    rw [h]; rfl
  rw [m4fixChildB_1_1_1_5_7_12] at h2
  exact Bool.noConfusion h2

/-- The child key `(5,1)` enters the state set at round 1. -/
theorem m4fixChildMem_1_1_1_5_7_12 :
    ((5 : Fin 6), (1 : Fin 15)) ∈ (fixIter m4fix_1_1_1_5_7_12 1).states := by
  rw [fixIter]
  simp only [fixRound]
  rw [Finset.mem_union, Finset.mem_biUnion]
  refine Or.inr ⟨((4 : Fin 6), (0 : Fin 15)), ?_, ?_⟩
  · simp [m4fix_1_1_1_5_7_12, fixIter]
  · rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, by
      simp only [fixIter]; exact m4fixChildB_1_1_1_5_7_12⟩

/-- The child key's table is trivial at every round `T ≥ 1`. -/
theorem m4fixChildTab_1_1_1_5_7_12 : ∀ T, 1 ≤ T →
    (fixIter m4fix_1_1_1_5_7_12 T).table ((5 : Fin 6), (1 : Fin 15)) = fun _ _ => none := by
  intro T
  induction T with
  | zero => intro hT; exact absurd hT (by omega)
  | succ T ih =>
    intro hT
    rw [fixIter]
    rcases Nat.eq_zero_or_pos T with h0 | h0
    · subst h0
      exact fixRound_table_none_of _ _
        (by simp [m4fix_1_1_1_5_7_12, fixIter])
    · refine fixRound_table_none_of _ _ ?_
      rw [if_pos (fixIter_states_mono m4fix_1_1_1_5_7_12 1 T (by omega)
        m4fixChildMem_1_1_1_5_7_12)]
      exact ih h0

/-- **Blocker A (mechanical).**  The recomputed seed's fold verdict is FALSE at every
`T ≥ 1` — in particular at the `T = 112` that `boxAdmit_of_kill` requires.  The checkpoint
verdict lives at `T = 0` only; the Lean fold and the Python pruned fixpoint do not meet. -/
theorem m4fixNotKilled_ge1_1_1_1_5_7_12 : ∀ T, 1 ≤ T →
    ¬ FixKilled (fixIter m4fix_1_1_1_5_7_12 T) := by
  intro T hT hkill
  have hmem : ((5 : Fin 6), (1 : Fin 15)) ∈ (fixIter m4fix_1_1_1_5_7_12 T).states :=
    fixIter_states_mono m4fix_1_1_1_5_7_12 1 T hT m4fixChildMem_1_1_1_5_7_12
  have hc := fixIter_canon m4fix_1_1_1_5_7_12 m4fixCanon_1_1_1_5_7_12 T
    ((5 : Fin 6), (1 : Fin 15))
  have hexit := hkill ((5 : Fin 6), (1 : Fin 15)) hmem
  rw [hc.1, hc.2, m4fixChildTab_1_1_1_5_7_12 T hT] at hexit
  -- the trivial table passes every exit check (definitional: keep-cur false, back none)
  have hpass : uExitOK (fun _ _ => none)
      (rowOf ((5 : Fin 6), (1 : Fin 15)).1) (envB ((5 : Fin 6), (1 : Fin 15)).2) = true :=
    rfl
  rw [hpass] at hexit
  exact Bool.noConfusion hexit

#print axioms m4fixNotKilled_ge1_1_1_1_5_7_12

/-! ## 3. Blocker B, mechanically: `boxAdmit_of_kill`'s hypothesis set is empty

A table realized by EVERY positive vector has no finite off-diagonal bound. -/

/-- **Universal fineness forces trivial off-diagonal cells.**  If `UFine ρ U` holds for
every positive `ρ`, then `U i j = none` for every `i ≠ j`: a stored bound `(c, s)` would
have to bound `ρ i / ρ j` for all positive vectors, and the vector `(ρ i, ρ j) =
(max c 0 + 1, 1)` exceeds any `c`. -/
theorem univFine_none {U : UTable}
    (h : ∀ ρ : Fin 7 → ℝ, (∀ k, 0 < ρ k) → UFine ρ U) :
    ∀ i j : Fin 7, i ≠ j → U i j = none := by
  intro i j hij
  rcases hc : U i j with hn | ⟨c, s⟩
  · rfl
  · exfalso
    set C : ℚ := max c 0 + 1 with hC
    have hCpos : (0 : ℚ) < C := by
      have h1 := le_max_right c (0 : ℚ)
      linarith
    have hpos : ∀ k, 0 < (fun k : Fin 7 => if k = j then (1 : ℝ) else ((C : ℚ) : ℝ)) k := by
      intro k
      by_cases hk : k = j
      · simp [hk]
      · simp only [if_neg hk]
        exact_mod_cast hCpos
    have hfi := h _ hpos i j
    rw [hc] at hfi
    rw [if_neg hij, if_pos rfl, div_one] at hfi
    have hkey := bhof_eq_some hfi rfl
    have hCgtQ : C > c := by
      rcases le_total c 0 with hle | hle
      · rw [hC, max_eq_right hle]
        linarith
      · rw [hC, max_eq_left hle]
        linarith
    have hCgt : ((C : ℚ) : ℝ) > ((c : ℚ) : ℝ) := by exact_mod_cast hCgtQ
    cases s <;> simp only [BHolds] at hkey <;> linarith

/-- **Blocker B (mechanical).**  The hypothesis tuple of `Fresh.UClosureKill.boxAdmit_of_kill`
is jointly unsatisfiable: `hopen` forces all 90 keys into the seed's state set (nonempty),
`hseedfine` forces the seed tables — hence, merges only loosening, every round-T table —
to be universally fine, hence trivial at the off-diagonal exit back-cell `(0, rowOf k.1)`,
hence the direct exit check passes on every state — contradicting `hclose`.  Holds for
every seed and every `T`, `hcanon` included (so even `T = 0` is blocked; and `hT : 112 ≤ T`
is beside the point).  Named repair (data-side + `UClosureKill.lean` edit): weaken
`hseedfine` to in-box `ρ` (the seed tables then carry the box's face bounds, realized by
the `E810ChainCover` chain's readings), give first-birth keys their child table (the
Python engine's birth rule), and record the per-box seed + convergence round. -/
theorem c3fix_unsat (seed : Fixpoint) (T : ℕ)
    (hcanon : (∀ k, seed.rank k = rowOf k.1) ∧ (∀ k, seed.aex k = envB k.2))
    (hopen : ∀ (a : Fin 7) (c : Fin 15), keyOf a c ∈ seed.states)
    (hseedfine : ∀ (ρ : Fin 7 → ℝ), (∀ k, 0 < ρ k) → ∀ k ∈ seed.states,
      UFine ρ (seed.table k))
    (hclose : FixKilled (fixIter seed T)) : False := by
  have hmem0 : keyOf 1 0 ∈ seed.states := hopen 1 0
  have hmem : keyOf 1 0 ∈ (fixIter seed T).states :=
    fixIter_states_mono seed 0 T (Nat.zero_le T) hmem0
  have hc := fixIter_canon seed hcanon T (keyOf 1 0)
  have hfine : ∀ ρ : Fin 7 → ℝ, (∀ k, 0 < ρ k) →
      UFine ρ ((fixIter seed T).table (keyOf 1 0)) :=
    fun ρ hpos => fixIter_fine seed ρ (hseedfine ρ hpos) T (keyOf 1 0) hmem
  have hane : rowOf (keyOf 1 0).1 ≠ 0 := by
    intro h
    have h1 : (rowOf (keyOf 1 0).1 : ℕ) = 1 := by simp [rowOf, keyOf]
    rw [h] at h1
    norm_num at h1
  have hcell1 : ((fixIter seed T).table (keyOf 1 0)) (rowOf (keyOf 1 0).1) 0 = none :=
    univFine_none hfine _ _ hane
  have hcell2 : ((fixIter seed T).table (keyOf 1 0)) 0 (rowOf (keyOf 1 0).1) = none :=
    univFine_none hfine _ _ (Ne.symm hane)
  have hexit := hclose (keyOf 1 0) hmem
  rw [hc.1, hc.2] at hexit
  unfold uExitOK at hexit
  have hsurv : uAdd ((fixIter seed T).table (keyOf 1 0)) (rowOf (keyOf 1 0).1) 0
      ((envB (keyOf 1 0).2) / 7) true ≠ none := by
    intro hnone
    simp [uAdd, uKeepCur, uBack, hcell1, hcell2] at hnone
  cases hb : uAdd ((fixIter seed T).table (keyOf 1 0)) (rowOf (keyOf 1 0).1) 0
      ((envB (keyOf 1 0).2) / 7) true with
  | none => exact hsurv hb
  | some _ =>
    rw [hb] at hexit
    simp at hexit

#print axioms c3fix_unsat

/-! ## 4. The composed instance, honest form

`m4fixAdmit_of_E810_vacuous` mirrors `boxAdmit_of_kill`'s exact signature (E810
consumption stub included as the hypothesis `hE810`).  It compiles axiom-clean — but ONLY
by explosion through `c3fix_unsat`: the hypothesis tuple is provably empty (Blocker B), so
the instance delivers no per-box content and cannot carry the C3 route to
`M4BoxNoCarvePinned`.  This is the honest terminal shape of this rung. -/

theorem m4fixAdmit_of_E810_vacuous (n : Fin 7 → ℤ) (hn17 : ∀ i, n i ≤ 17)
    (hE810 : E810ChainCover n hn17)
    (seed : Fixpoint) (T : ℕ)
    (hcanon : (∀ k, seed.rank k = rowOf k.1) ∧ (∀ k, seed.aex k = envB k.2))
    (hseedfine : ∀ (ρ : Fin 7 → ℝ), (∀ k, 0 < ρ k) → ∀ k ∈ seed.states,
      UFine ρ (seed.table k))
    (hopen : ∀ (a : Fin 7) (c : Fin 15), keyOf a c ∈ seed.states)
    (hT : 112 ≤ T) (hclose : FixKilled (fixIter seed T))
    (g : Fin 7 → ℝ) (hface : ∀ i, FaceLo n i ≤ g i ∧ g i ≤ FaceHi n i) :
    ∃ s : ℝ, 1 ≤ s ∧ s ≤ 7 ∧ ∀ i, (1 / 8 : ℝ) ≤ Fresh.distInt (g i * (s / 8)) :=
  (c3fix_unsat seed T hcanon hopen hseedfine hclose).elim

#print axioms m4fixAdmit_of_E810_vacuous

-- Full-file axiom census (every named declaration's footprint, all inside the accepted set)
#print axioms decEQ_true
#print axioms decEQ_false
#print axioms decLT_true
#print axioms decLT_false
#print axioms m4fixCanon_1_1_1_5_7_12
#print axioms m4fixenvB0
#print axioms m4fixenvA1
#print axioms m4fixenvB1
#print axioms m4fixh50
#print axioms m4fixh05
#print axioms m4fixh56
#print axioms m4fixh65
#print axioms m4fixhtab0
#print axioms m4fixhrank0
#print axioms m4fixhaex0
#print axioms m4fixhrank1
#print axioms m4fixhaex1
#print axioms childTab_none
#print axioms foldl_childTab_none
#print axioms fixRound_table_none_of
#print axioms m4fixChildB_1_1_1_5_7_12
#print axioms m4fixChild_1_1_1_5_7_12
#print axioms m4fixChildMem_1_1_1_5_7_12
#print axioms m4fixChildTab_1_1_1_5_7_12
#print axioms univFine_none

end Fresh.M4FixBankC3
