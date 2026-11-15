import Fresh.ChainDomPerRecStart
import Fresh.ChainDomTrace19

namespace Fresh.ChainDomPerRec8

open Fresh.ChainDomBase Fresh.CapChainsOfCarve Fresh.JoinFamComposed Fresh.OneSidedComposed Fresh.OneSidedGlue
  Fresh.UClosure Fresh.SpineSound Fresh.FilterAssembly Fresh.DumpDomData

-- the 49-point `fin_cases` checks and the big literal tables need headroom
set_option maxHeartbeats 10000000

/- `mk`'s (the `uMk` fold's) output for box (1, 3, 4, 5, 7, 7, 9) is transcribed verbatim
(`perrec8_gen_v1.py`, value-verbatim mirror of `Fresh.UClosureKill`'s `uKeepCur`/
`uBack`/`uProp`/`uAdd`; 49 entries -- the FULL closure is dense) as `mkTab_1_3_4_5_7_7_9`
(section 2).  Census cross-check: at every census pair the transcription agrees with
the banked `Fresh.DumpDomData` `u0e_1_3_4_5_7_7_9_*` facts (`mkU0_1_3_4_5_7_7_9_*` below). -/

/-- `mk`'s entry at (0, 5) for box (1, 3, 4, 5, 7, 7, 9): exact census datum (cross-checked
against the banked `Fresh.DumpDomData.u0e_1_3_4_5_7_7_9_0_5`). -/
theorem mke_1_3_4_5_7_7_9_0_5 : mkOf (![1, 3, 4, 5, 7, 7, 9] : Fin 7 → ℤ) (0 : Fin 7) (5 : Fin 7) = some ((2 / 13 : ℚ), true) :=
  by simp [mkOf, mkTab_1_3_4_5_7_7_9]

#print axioms mke_1_3_4_5_7_7_9_0_5

/-- The closure transcription agrees with the sparse census transcription at (0, 5). -/
theorem mkU0_1_3_4_5_7_7_9_0_5 : mkOf (![1, 3, 4, 5, 7, 7, 9] : Fin 7 → ℤ) (0 : Fin 7) (5 : Fin 7) = u0Of (![1, 3, 4, 5, 7, 7, 9] : Fin 7 → ℤ) (0 : Fin 7) (5 : Fin 7) :=
  by rw [mke_1_3_4_5_7_7_9_0_5, u0e_1_3_4_5_7_7_9_0_5]

#print axioms mkU0_1_3_4_5_7_7_9_0_5

/-- `mk`'s entry at (1, 5) for box (1, 3, 4, 5, 7, 7, 9): exact census datum (cross-checked
against the banked `Fresh.DumpDomData.u0e_1_3_4_5_7_7_9_1_5`). -/
theorem mke_1_3_4_5_7_7_9_1_5 : mkOf (![1, 3, 4, 5, 7, 7, 9] : Fin 7 → ℤ) (1 : Fin 7) (5 : Fin 7) = some ((7 / 13 : ℚ), true) :=
  by simp [mkOf, mkTab_1_3_4_5_7_7_9]

#print axioms mke_1_3_4_5_7_7_9_1_5

/-- The closure transcription agrees with the sparse census transcription at (1, 5). -/
theorem mkU0_1_3_4_5_7_7_9_1_5 : mkOf (![1, 3, 4, 5, 7, 7, 9] : Fin 7 → ℤ) (1 : Fin 7) (5 : Fin 7) = u0Of (![1, 3, 4, 5, 7, 7, 9] : Fin 7 → ℤ) (1 : Fin 7) (5 : Fin 7) :=
  by rw [mke_1_3_4_5_7_7_9_1_5, u0e_1_3_4_5_7_7_9_1_5]

#print axioms mkU0_1_3_4_5_7_7_9_1_5

/-- The EMPTY-chain non-vacuity for box (1, 3, 4, 5, 7, 7, 9): every strict witness's cap is
strictly TIGHTER than the closure entry at its pair, so `CapsDom (mkOf (![1, 3, 4, 5, 7, 7, 9] : Fin 7 → ℤ)) ...`
is refuted on every record -- a witness of the existential must be a genuine
dominating run (mirror of `Fresh.DumpDomData.not_capsDomU0all_*`). -/
theorem not_capsDomMk8all_1_3_4_5_7_7_9 :
    ∀ e ∈ dumpFam_1_3_4_5_7_7_9.edges,
      ¬ CapsDom (mkOf (![1, 3, 4, 5, 7, 7, 9] : Fin 7 → ℤ)) e.y e.caps e.x := by
  intro e he
  simp only [dumpFam_1_3_4_5_7_7_9, List.mem_cons] at he
  rcases he with rfl | rfl | rfl | rfl | h0
  · exact not_capsDomU0_of_entry_lt (mke_1_3_4_5_7_7_9_0_5) (by norm_num)
  · exact not_capsDomU0_of_entry_lt (mke_1_3_4_5_7_7_9_1_5) (by norm_num)
  · exact not_capsDomU0_of_entry_lt (mke_1_3_4_5_7_7_9_1_5) (by norm_num)
  · exact not_capsDomU0_of_entry_lt (mke_1_3_4_5_7_7_9_1_5) (by norm_num)
  · exact absurd h0 (by simp)

#print axioms not_capsDomMk8all_1_3_4_5_7_7_9

/-- The attesting-chain PREFIX for box (1, 3, 4, 5, 7, 7, 9): the first 18 steps of enumerated chain
index 8 of the box's dump enumeration (full word length 19; chain index and count
re-verified against the dump's `chains_enumerated` = 176 by `perrec8_gen_v1.py`).  Entries
only tighten along a run, so the prefix run's closed trace already carries the
dominating entries at every record pair ((0,5) first dominated at step 18, (1,5) first dominated at step 18). -/
def steps8_1_3_4_5_7_7_9 : List Step := [
  ⟨(5 : Fin 7), (7 : ℚ), (9 : ℚ)⟩, ⟨(4 : Fin 7), (7 : ℚ), (9 : ℚ)⟩, ⟨(3 : Fin 7), (7 : ℚ), (9 : ℚ)⟩, ⟨(2 : Fin 7), (7 : ℚ), (9 : ℚ)⟩, ⟨(5 : Fin 7), (15 : ℚ), (17 : ℚ)⟩, ⟨(1 : Fin 7), (7 : ℚ), (9 : ℚ)⟩, ⟨(3 : Fin 7), (15 : ℚ), (17 : ℚ)⟩, ⟨(6 : Fin 7), (31 : ℚ), (33 : ℚ)⟩, ⟨(4 : Fin 7), (23 : ℚ), (25 : ℚ)⟩, ⟨(2 : Fin 7), (15 : ℚ), (17 : ℚ)⟩, ⟨(6 : Fin 7), (39 : ℚ), (41 : ℚ)⟩, ⟨(5 : Fin 7), (31 : ℚ), (33 : ℚ)⟩, ⟨(3 : Fin 7), (23 : ℚ), (25 : ℚ)⟩, ⟨(4 : Fin 7), (31 : ℚ), (33 : ℚ)⟩, ⟨(1 : Fin 7), (15 : ℚ), (17 : ℚ)⟩, ⟨(2 : Fin 7), (23 : ℚ), (25 : ℚ)⟩, ⟨(3 : Fin 7), (31 : ℚ), (33 : ℚ)⟩, ⟨(5 : Fin 7), (47 : ℚ), (49 : ℚ)⟩
]

/-- transcribed trace table: T8_1_3_4_5_7_7_9_1 (the mirror run's add-end snapshot). -/
def T8_1_3_4_5_7_7_9_1 : UTable := fun p q =>
  if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((2 / 5 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((2 / 7 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((2 / 9 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((2 / 13 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 / 7 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((2 / 17 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((7 / 2 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((7 / 9 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((7 / 13 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 / 2 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((7 / 17 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 / 2 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((9 / 5 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((9 / 13 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((9 / 14 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((9 / 17 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((11 / 2 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((11 / 5 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((11 / 7 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((11 / 13 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((11 / 14 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((11 / 17 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((15 / 2 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((3 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((15 / 7 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((5 / 3 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((15 / 17 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((15 / 2 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((3 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((15 / 7 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((5 / 3 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((15 / 13 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((15 / 17 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((19 / 2 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((19 / 5 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((19 / 7 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((19 / 9 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((19 / 13 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((19 / 14 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

/-- transcribed trace table: T8_1_3_4_5_7_7_9_2 (the mirror run's add-end snapshot). -/
def T8_1_3_4_5_7_7_9_2 : UTable := fun p q =>
  if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((2 / 5 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((2 / 7 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((18 / 91 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((2 / 13 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 / 7 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((2 / 17 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((7 / 2 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((9 / 13 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((7 / 13 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 / 2 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((7 / 17 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 / 2 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((9 / 5 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((81 / 91 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((9 / 13 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((9 / 14 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((9 / 17 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((11 / 2 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((11 / 5 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((11 / 7 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((11 / 13 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((11 / 14 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((11 / 17 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((99 / 14 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((99 / 35 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((99 / 49 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((9 / 7 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((99 / 119 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((15 / 2 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((3 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((15 / 7 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((135 / 91 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((15 / 13 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((15 / 17 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((19 / 2 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((19 / 5 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((19 / 7 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((171 / 91 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((19 / 13 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((19 / 14 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

/-- transcribed trace table: T8_1_3_4_5_7_7_9_3 (the mirror run's add-end snapshot). -/
def T8_1_3_4_5_7_7_9_3 : UTable := fun p q =>
  if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((2 / 5 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((162 / 637 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((18 / 91 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((2 / 13 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 / 7 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((2 / 17 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((7 / 2 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((81 / 91 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((9 / 13 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((7 / 13 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 / 2 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((7 / 17 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 / 2 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((9 / 5 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((81 / 91 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((9 / 13 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((9 / 14 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((9 / 17 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((11 / 2 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((11 / 5 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((9 / 7 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((11 / 13 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((11 / 14 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((11 / 17 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((99 / 14 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((99 / 35 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((81 / 49 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((9 / 7 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((99 / 119 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((15 / 2 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((3 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((1215 / 637 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((135 / 91 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((15 / 13 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((15 / 17 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((19 / 2 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((19 / 5 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((1539 / 637 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((171 / 91 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((19 / 13 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((19 / 14 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

/-- transcribed trace table: T8_1_3_4_5_7_7_9_4 (the mirror run's add-end snapshot). -/
def T8_1_3_4_5_7_7_9_4 : UTable := fun p q =>
  if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((2 / 5 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((162 / 637 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((18 / 91 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((2 / 13 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 / 7 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((2 / 17 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((7 / 2 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((81 / 91 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((9 / 13 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((7 / 13 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 / 2 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((7 / 17 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 / 2 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((9 / 5 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((81 / 91 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((9 / 13 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((3 / 5 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((9 / 17 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((11 / 2 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((11 / 5 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((9 / 7 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((11 / 13 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((27 / 35 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((11 / 17 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((99 / 14 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((99 / 35 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((81 / 49 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((9 / 7 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((243 / 245 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((99 / 119 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((15 / 2 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((3 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((1215 / 637 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((135 / 91 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((15 / 13 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((15 / 17 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((19 / 2 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((19 / 5 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((1539 / 637 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((171 / 91 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((19 / 13 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((19 / 14 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

/-- transcribed trace table: T8_1_3_4_5_7_7_9_5 (the mirror run's add-end snapshot). -/
def T8_1_3_4_5_7_7_9_5 : UTable := fun p q =>
  if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((2 / 5 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((162 / 637 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((18 / 91 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((2 / 13 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 / 7 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((2 / 17 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((7 / 2 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((81 / 91 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((9 / 13 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((7 / 13 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 / 2 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((7 / 17 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 / 2 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((9 / 5 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((81 / 91 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((9 / 13 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((3 / 5 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((9 / 17 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((11 / 2 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((11 / 5 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((9 / 7 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((11 / 13 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((27 / 35 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((11 / 17 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((99 / 14 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((99 / 35 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((81 / 49 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((9 / 7 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((243 / 245 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((99 / 119 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((15 / 2 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((3 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((17 / 9 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((135 / 91 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((15 / 13 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((15 / 17 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((19 / 2 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((19 / 5 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((1539 / 637 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((171 / 91 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((19 / 13 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((19 / 14 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

/-- transcribed trace table: T8_1_3_4_5_7_7_9_6 (the mirror run's add-end snapshot). -/
def T8_1_3_4_5_7_7_9_6 : UTable := fun p q =>
  if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((17 / 49 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((162 / 637 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((18 / 91 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((2 / 13 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 / 7 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((2 / 17 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((7 / 2 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((81 / 91 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((9 / 13 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((7 / 13 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 / 2 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((7 / 17 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 / 2 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((51 / 35 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((81 / 91 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((9 / 13 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((3 / 5 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((9 / 17 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((11 / 2 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((459 / 245 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((9 / 7 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((11 / 13 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((27 / 35 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((11 / 17 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((99 / 14 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((4131 / 1715 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((81 / 49 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((9 / 7 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((243 / 245 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((99 / 119 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((15 / 2 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((17 / 7 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((17 / 9 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((135 / 91 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((15 / 13 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((15 / 17 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((19 / 2 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((323 / 98 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((1539 / 637 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((171 / 91 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((19 / 13 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((19 / 14 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

/-- transcribed trace table: T8_1_3_4_5_7_7_9_7 (the mirror run's add-end snapshot). -/
def T8_1_3_4_5_7_7_9_7 : UTable := fun p q =>
  if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((17 / 49 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((162 / 637 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((18 / 91 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((2 / 13 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 / 7 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((2 / 17 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((33 / 10 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((27 / 35 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((3 / 5 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((33 / 65 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((81 / 175 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((33 / 85 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 / 2 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((51 / 35 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((153 / 175 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((9 / 13 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((3 / 5 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((9 / 17 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((11 / 2 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((459 / 245 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((9 / 7 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((11 / 13 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((27 / 35 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((11 / 17 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((99 / 14 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((4131 / 1715 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((81 / 49 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((9 / 7 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((243 / 245 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((99 / 119 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((15 / 2 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((17 / 7 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((459 / 245 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((51 / 35 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((15 / 13 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((15 / 17 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((19 / 2 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((323 / 98 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((1539 / 637 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((171 / 91 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((19 / 13 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((19 / 14 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

/-- transcribed trace table: T8_1_3_4_5_7_7_9_8 (the mirror run's add-end snapshot). -/
def T8_1_3_4_5_7_7_9_8 : UTable := fun p q =>
  if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((17 / 49 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((162 / 637 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((18 / 91 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((2 / 13 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 / 7 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((306 / 2821 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((969 / 310 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((27 / 35 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((3 / 5 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((969 / 2015 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((969 / 2170 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((51 / 155 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 / 2 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((51 / 35 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((153 / 175 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((9 / 13 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((3 / 5 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((2601 / 5425 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((323 / 62 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((5491 / 3038 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((9 / 7 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((323 / 403 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((323 / 434 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((17 / 31 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((2907 / 434 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((49419 / 21266 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((81 / 49 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((9 / 7 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((2907 / 3038 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((153 / 217 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((15 / 2 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((17 / 7 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((459 / 245 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((51 / 35 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((15 / 13 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((867 / 1085 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((19 / 2 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((323 / 98 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((1539 / 637 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((171 / 91 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((19 / 13 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((19 / 14 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

/-- transcribed trace table: T8_1_3_4_5_7_7_9_9 (the mirror run's add-end snapshot). -/
def T8_1_3_4_5_7_7_9_9 : UTable := fun p q =>
  if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((17 / 49 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((162 / 637 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((18 / 91 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((2 / 13 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 / 7 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((306 / 2821 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((969 / 310 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((27 / 35 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((3 / 5 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((1683 / 3565 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((969 / 2170 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((51 / 155 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 / 2 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((51 / 35 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((153 / 175 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((85833 / 124775 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((3 / 5 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((2601 / 5425 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((323 / 62 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((5491 / 3038 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((9 / 7 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((561 / 713 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((323 / 434 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((17 / 31 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((2907 / 434 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((49419 / 21266 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((81 / 49 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((9 / 7 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((2907 / 3038 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((153 / 217 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((15 / 2 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((17 / 7 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((459 / 245 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((51 / 35 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((28611 / 24955 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((867 / 1085 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((19 / 2 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((323 / 98 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((2673 / 1127 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((297 / 161 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((33 / 23 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((19 / 14 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

/-- transcribed trace table: T8_1_3_4_5_7_7_9_10 (the mirror run's add-end snapshot). -/
def T8_1_3_4_5_7_7_9_10 : UTable := fun p q =>
  if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((17 / 49 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((162 / 637 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((18 / 91 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((2 / 13 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 / 7 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((306 / 2821 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((969 / 310 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((27 / 35 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((3 / 5 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((1683 / 3565 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((969 / 2170 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((51 / 155 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 / 2 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((51 / 35 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((153 / 175 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 25 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((3 / 5 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((2601 / 5425 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((323 / 62 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((5491 / 3038 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((9 / 7 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((561 / 713 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((323 / 434 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((17 / 31 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((2907 / 434 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((49419 / 21266 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((81 / 49 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((9 / 7 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((2907 / 3038 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((153 / 217 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((15 / 2 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((17 / 7 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((459 / 245 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((51 / 35 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((28611 / 24955 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((867 / 1085 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((19 / 2 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((323 / 98 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((2673 / 1127 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((297 / 161 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((33 / 23 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((19 / 14 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

/-- transcribed trace table: T8_1_3_4_5_7_7_9_11 (the mirror run's add-end snapshot). -/
def T8_1_3_4_5_7_7_9_11 : UTable := fun p q =>
  if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((17 / 49 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((162 / 637 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((18 / 91 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((2 / 13 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 / 7 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((306 / 2821 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((969 / 310 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((27 / 35 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((3 / 5 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((1683 / 3565 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((969 / 2170 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((51 / 155 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((323 / 78 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((5491 / 3822 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((1683 / 2093 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((187 / 299 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((323 / 546 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((17 / 39 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((323 / 62 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((5491 / 3038 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((9 / 7 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((561 / 713 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((323 / 434 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((17 / 31 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((2907 / 434 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((49419 / 21266 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((81 / 49 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((9 / 7 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((2907 / 3038 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((153 / 217 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((15 / 2 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((17 / 7 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((459 / 245 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((51 / 35 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((28611 / 24955 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((867 / 1085 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((19 / 2 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((323 / 98 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((2673 / 1127 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((297 / 161 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((33 / 23 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((19 / 14 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

/-- transcribed trace table: T8_1_3_4_5_7_7_9_12 (the mirror run's add-end snapshot). -/
def T8_1_3_4_5_7_7_9_12 : UTable := fun p q =>
  if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((17 / 49 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((162 / 637 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((18 / 91 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((2 / 13 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 / 7 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((306 / 2821 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((969 / 310 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((27 / 35 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((3 / 5 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((1683 / 3565 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((2091 / 4805 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((51 / 155 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((323 / 78 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((11849 / 8463 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((1683 / 2093 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((187 / 299 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((697 / 1209 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((17 / 39 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((323 / 62 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((11849 / 6727 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((9 / 7 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((561 / 713 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((697 / 961 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((17 / 31 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((2907 / 434 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((106641 / 47089 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((81 / 49 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((9 / 7 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((6273 / 6727 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((153 / 217 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((15 / 2 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((17 / 7 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((459 / 245 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((51 / 35 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((28611 / 24955 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((867 / 1085 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((19 / 2 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((697 / 217 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((2673 / 1127 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((297 / 161 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((33 / 23 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((41 / 31 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

/-- transcribed trace table: T8_1_3_4_5_7_7_9_13 (the mirror run's add-end snapshot). -/
def T8_1_3_4_5_7_7_9_13 : UTable := fun p q =>
  if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((17 / 49 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((162 / 637 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((18 / 91 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((2 / 13 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 / 7 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((306 / 2821 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((969 / 310 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((27 / 35 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((3 / 5 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((1683 / 3565 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((2091 / 4805 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((51 / 155 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((323 / 78 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((11849 / 8463 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((1683 / 2093 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((187 / 299 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((697 / 1209 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((17 / 39 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((323 / 62 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((11849 / 6727 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((9 / 7 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((561 / 713 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((697 / 961 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((17 / 31 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((2907 / 434 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((106641 / 47089 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((81 / 49 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((9 / 7 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((6273 / 6727 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((153 / 217 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((10659 / 1426 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((17 / 7 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((297 / 161 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((33 / 23 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((18513 / 16399 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((561 / 713 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((19 / 2 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((697 / 217 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((2673 / 1127 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((297 / 161 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((33 / 23 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((41 / 31 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

/-- transcribed trace table: T8_1_3_4_5_7_7_9_14 (the mirror run's add-end snapshot). -/
def T8_1_3_4_5_7_7_9_14 : UTable := fun p q =>
  if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((22 / 65 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((162 / 637 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((18 / 91 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((2 / 13 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 / 7 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((306 / 2821 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((969 / 310 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((27 / 35 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((3 / 5 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((1683 / 3565 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((2091 / 4805 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((51 / 155 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((323 / 78 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((2057 / 1495 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((1683 / 2093 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((187 / 299 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((697 / 1209 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((17 / 39 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((323 / 62 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((6171 / 3565 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((9 / 7 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((561 / 713 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((697 / 961 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((17 / 31 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((2907 / 434 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((11 / 5 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((81 / 49 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((9 / 7 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((6273 / 6727 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((153 / 217 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((10659 / 1426 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((17 / 7 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((297 / 161 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((33 / 23 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((18513 / 16399 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((561 / 713 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((19 / 2 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((363 / 115 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((2673 / 1127 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((297 / 161 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((33 / 23 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((41 / 31 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

/-- transcribed trace table: T8_1_3_4_5_7_7_9_15 (the mirror run's add-end snapshot). -/
def T8_1_3_4_5_7_7_9_15 : UTable := fun p q =>
  if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((22 / 65 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((374 / 1495 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((18 / 91 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((2 / 13 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 / 7 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((306 / 2821 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((5491 / 1794 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((17 / 23 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((28611 / 48139 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((3179 / 6877 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((11849 / 27807 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((289 / 897 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((323 / 78 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((2057 / 1495 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((1683 / 2093 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((187 / 299 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((697 / 1209 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((17 / 39 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((323 / 62 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((6171 / 3565 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((104907 / 81995 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((561 / 713 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((697 / 961 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((17 / 31 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((2907 / 434 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((11 / 5 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((187 / 115 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((9 / 7 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((6273 / 6727 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((153 / 217 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((93347 / 12558 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((17 / 7 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((289 / 161 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((33 / 23 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((54043 / 48139 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((4913 / 6279 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((19 / 2 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((363 / 115 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((6171 / 2645 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((297 / 161 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((33 / 23 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((41 / 31 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

/-- transcribed trace table: T8_1_3_4_5_7_7_9_16 (the mirror run's add-end snapshot). -/
def T8_1_3_4_5_7_7_9_16 : UTable := fun p q =>
  if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((10098 / 29939 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((171666 / 688597 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((18 / 91 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((2 / 13 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((594 / 4277 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((306 / 2821 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((5491 / 1794 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((17 / 23 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((28611 / 48139 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((3179 / 6877 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((944163 / 2262533 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((289 / 897 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((323 / 78 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((944163 / 688597 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((1683 / 2093 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((187 / 299 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((55539 / 98371 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((17 / 39 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((323 / 62 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((561 / 329 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((9537 / 7567 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((561 / 713 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((33 / 47 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((17 / 31 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((2907 / 434 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((5049 / 2303 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((85833 / 52969 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((9 / 7 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((297 / 329 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((153 / 217 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((93347 / 12558 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((17 / 7 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((289 / 161 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((33 / 23 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((54043 / 48139 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((4913 / 6279 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((19 / 2 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((166617 / 52969 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((2832489 / 1218287 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((297 / 161 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((33 / 23 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((9801 / 7567 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

/-- Add 1 of the attesting chain: keep-cur and back are ground-false and the propagated result IS the next transcribed table (49 concrete pointwise checks). -/
theorem addEq_1_1_3_4_5_7_7_9 : uAdd (mkOf (![1, 3, 4, 5, 7, 7, 9] : Fin 7 → ℤ)) (0 : Fin 7) (5 : Fin 7) ((1 : ℚ) / (7 : ℚ)) true = some T8_1_3_4_5_7_7_9_1 :=
  uAdd_eq_some' (by simp [uKeepCur, uBackCond, mkOf, mkTab_1_3_4_5_7_7_9] <;> norm_num) (by simp [uBack, uBackCond, mkOf, mkTab_1_3_4_5_7_7_9] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, mkOf, mkTab_1_3_4_5_7_7_9, T8_1_3_4_5_7_7_9_1] <;> norm_num)

#print axioms addEq_1_1_3_4_5_7_7_9

/-- Add 2 of the attesting chain: the entry at its pair is already tight (`uKeepCur` fires ground-true), so the table is unchanged. -/
theorem addEq_2_1_3_4_5_7_7_9 : uAdd T8_1_3_4_5_7_7_9_1 (5 : Fin 7) (0 : Fin 7) ((9 : ℚ) / (1 : ℚ)) true = some T8_1_3_4_5_7_7_9_1 :=
  by simp [uAdd, uKeepCur, uBackCond, uBack, uTighter, uProp, T8_1_3_4_5_7_7_9_1] <;> norm_num

#print axioms addEq_2_1_3_4_5_7_7_9

/-- Add 3 of the attesting chain: the entry at its pair is already tight (`uKeepCur` fires ground-true), so the table is unchanged. -/
theorem addEq_3_1_3_4_5_7_7_9 : uAdd T8_1_3_4_5_7_7_9_1 (5 : Fin 7) (4 : Fin 7) ((9 : ℚ) / (7 : ℚ)) true = some T8_1_3_4_5_7_7_9_1 :=
  by simp [uAdd, uKeepCur, uBackCond, uBack, uTighter, uProp, T8_1_3_4_5_7_7_9_1] <;> norm_num

#print axioms addEq_3_1_3_4_5_7_7_9

/-- Add 4 of the attesting chain: the entry at its pair is already tight (`uKeepCur` fires ground-true), so the table is unchanged. -/
theorem addEq_4_1_3_4_5_7_7_9 : uAdd T8_1_3_4_5_7_7_9_1 (4 : Fin 7) (5 : Fin 7) ((9 : ℚ) / (9 : ℚ)) true = some T8_1_3_4_5_7_7_9_1 :=
  by simp [uAdd, uKeepCur, uBackCond, uBack, uTighter, uProp, T8_1_3_4_5_7_7_9_1] <;> norm_num

#print axioms addEq_4_1_3_4_5_7_7_9

/-- Add 5 of the attesting chain: keep-cur and back are ground-false and the propagated result IS the next transcribed table (49 concrete pointwise checks). -/
theorem addEq_5_1_3_4_5_7_7_9 : uAdd T8_1_3_4_5_7_7_9_1 (4 : Fin 7) (3 : Fin 7) ((9 : ℚ) / (7 : ℚ)) true = some T8_1_3_4_5_7_7_9_2 :=
  uAdd_eq_some' (by simp [uKeepCur, uBackCond, T8_1_3_4_5_7_7_9_1] <;> norm_num) (by simp [uBack, uBackCond, T8_1_3_4_5_7_7_9_1] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, T8_1_3_4_5_7_7_9_1, T8_1_3_4_5_7_7_9_2] <;> norm_num)

#print axioms addEq_5_1_3_4_5_7_7_9

/-- Add 6 of the attesting chain: the entry at its pair is already tight (`uKeepCur` fires ground-true), so the table is unchanged. -/
theorem addEq_6_1_3_4_5_7_7_9 : uAdd T8_1_3_4_5_7_7_9_2 (3 : Fin 7) (4 : Fin 7) ((9 : ℚ) / (9 : ℚ)) true = some T8_1_3_4_5_7_7_9_2 :=
  by simp [uAdd, uKeepCur, uBackCond, uBack, uTighter, uProp, T8_1_3_4_5_7_7_9_2] <;> norm_num

#print axioms addEq_6_1_3_4_5_7_7_9

/-- Add 7 of the attesting chain: keep-cur and back are ground-false and the propagated result IS the next transcribed table (49 concrete pointwise checks). -/
theorem addEq_7_1_3_4_5_7_7_9 : uAdd T8_1_3_4_5_7_7_9_2 (3 : Fin 7) (2 : Fin 7) ((9 : ℚ) / (7 : ℚ)) true = some T8_1_3_4_5_7_7_9_3 :=
  uAdd_eq_some' (by simp [uKeepCur, uBackCond, T8_1_3_4_5_7_7_9_2] <;> norm_num) (by simp [uBack, uBackCond, T8_1_3_4_5_7_7_9_2] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, T8_1_3_4_5_7_7_9_2, T8_1_3_4_5_7_7_9_3] <;> norm_num)

#print axioms addEq_7_1_3_4_5_7_7_9

/-- Add 8 of the attesting chain: the entry at its pair is already tight (`uKeepCur` fires ground-true), so the table is unchanged. -/
theorem addEq_8_1_3_4_5_7_7_9 : uAdd T8_1_3_4_5_7_7_9_3 (2 : Fin 7) (3 : Fin 7) ((9 : ℚ) / (9 : ℚ)) true = some T8_1_3_4_5_7_7_9_3 :=
  by simp [uAdd, uKeepCur, uBackCond, uBack, uTighter, uProp, T8_1_3_4_5_7_7_9_3] <;> norm_num

#print axioms addEq_8_1_3_4_5_7_7_9

/-- Add 9 of the attesting chain: keep-cur and back are ground-false and the propagated result IS the next transcribed table (49 concrete pointwise checks). -/
theorem addEq_9_1_3_4_5_7_7_9 : uAdd T8_1_3_4_5_7_7_9_3 (2 : Fin 7) (5 : Fin 7) ((9 : ℚ) / (15 : ℚ)) true = some T8_1_3_4_5_7_7_9_4 :=
  uAdd_eq_some' (by simp [uKeepCur, uBackCond, T8_1_3_4_5_7_7_9_3] <;> norm_num) (by simp [uBack, uBackCond, T8_1_3_4_5_7_7_9_3] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, T8_1_3_4_5_7_7_9_3, T8_1_3_4_5_7_7_9_4] <;> norm_num)

#print axioms addEq_9_1_3_4_5_7_7_9

/-- Add 10 of the attesting chain: keep-cur and back are ground-false and the propagated result IS the next transcribed table (49 concrete pointwise checks). -/
theorem addEq_10_1_3_4_5_7_7_9 : uAdd T8_1_3_4_5_7_7_9_4 (5 : Fin 7) (2 : Fin 7) ((17 : ℚ) / (9 : ℚ)) true = some T8_1_3_4_5_7_7_9_5 :=
  uAdd_eq_some' (by simp [uKeepCur, uBackCond, T8_1_3_4_5_7_7_9_4] <;> norm_num) (by simp [uBack, uBackCond, T8_1_3_4_5_7_7_9_4] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, T8_1_3_4_5_7_7_9_4, T8_1_3_4_5_7_7_9_5] <;> norm_num)

#print axioms addEq_10_1_3_4_5_7_7_9

/-- Add 11 of the attesting chain: keep-cur and back are ground-false and the propagated result IS the next transcribed table (49 concrete pointwise checks). -/
theorem addEq_11_1_3_4_5_7_7_9 : uAdd T8_1_3_4_5_7_7_9_5 (5 : Fin 7) (1 : Fin 7) ((17 : ℚ) / (7 : ℚ)) true = some T8_1_3_4_5_7_7_9_6 :=
  uAdd_eq_some' (by simp [uKeepCur, uBackCond, T8_1_3_4_5_7_7_9_5] <;> norm_num) (by simp [uBack, uBackCond, T8_1_3_4_5_7_7_9_5] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, T8_1_3_4_5_7_7_9_5, T8_1_3_4_5_7_7_9_6] <;> norm_num)

#print axioms addEq_11_1_3_4_5_7_7_9

/-- Add 12 of the attesting chain: the entry at its pair is already tight (`uKeepCur` fires ground-true), so the table is unchanged. -/
theorem addEq_12_1_3_4_5_7_7_9 : uAdd T8_1_3_4_5_7_7_9_6 (1 : Fin 7) (5 : Fin 7) ((9 : ℚ) / (17 : ℚ)) true = some T8_1_3_4_5_7_7_9_6 :=
  by simp [uAdd, uKeepCur, uBackCond, uBack, uTighter, uProp, T8_1_3_4_5_7_7_9_6] <;> norm_num

#print axioms addEq_12_1_3_4_5_7_7_9

/-- Add 13 of the attesting chain: keep-cur and back are ground-false and the propagated result IS the next transcribed table (49 concrete pointwise checks). -/
theorem addEq_13_1_3_4_5_7_7_9 : uAdd T8_1_3_4_5_7_7_9_6 (1 : Fin 7) (3 : Fin 7) ((9 : ℚ) / (15 : ℚ)) true = some T8_1_3_4_5_7_7_9_7 :=
  uAdd_eq_some' (by simp [uKeepCur, uBackCond, T8_1_3_4_5_7_7_9_6] <;> norm_num) (by simp [uBack, uBackCond, T8_1_3_4_5_7_7_9_6] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, T8_1_3_4_5_7_7_9_6, T8_1_3_4_5_7_7_9_7] <;> norm_num)

#print axioms addEq_13_1_3_4_5_7_7_9

/-- Add 14 of the attesting chain: the entry at its pair is already tight (`uKeepCur` fires ground-true), so the table is unchanged. -/
theorem addEq_14_1_3_4_5_7_7_9 : uAdd T8_1_3_4_5_7_7_9_7 (3 : Fin 7) (1 : Fin 7) ((17 : ℚ) / (9 : ℚ)) true = some T8_1_3_4_5_7_7_9_7 :=
  by simp [uAdd, uKeepCur, uBackCond, uBack, uTighter, uProp, T8_1_3_4_5_7_7_9_7] <;> norm_num

#print axioms addEq_14_1_3_4_5_7_7_9

/-- Add 15 of the attesting chain: keep-cur and back are ground-false and the propagated result IS the next transcribed table (49 concrete pointwise checks). -/
theorem addEq_15_1_3_4_5_7_7_9 : uAdd T8_1_3_4_5_7_7_9_7 (3 : Fin 7) (6 : Fin 7) ((17 : ℚ) / (31 : ℚ)) true = some T8_1_3_4_5_7_7_9_8 :=
  uAdd_eq_some' (by simp [uKeepCur, uBackCond, T8_1_3_4_5_7_7_9_7] <;> norm_num) (by simp [uBack, uBackCond, T8_1_3_4_5_7_7_9_7] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, T8_1_3_4_5_7_7_9_7, T8_1_3_4_5_7_7_9_8] <;> norm_num)

#print axioms addEq_15_1_3_4_5_7_7_9

/-- Add 16 of the attesting chain: the entry at its pair is already tight (`uKeepCur` fires ground-true), so the table is unchanged. -/
theorem addEq_16_1_3_4_5_7_7_9 : uAdd T8_1_3_4_5_7_7_9_8 (6 : Fin 7) (3 : Fin 7) ((33 : ℚ) / (17 : ℚ)) true = some T8_1_3_4_5_7_7_9_8 :=
  by simp [uAdd, uKeepCur, uBackCond, uBack, uTighter, uProp, T8_1_3_4_5_7_7_9_8] <;> norm_num

#print axioms addEq_16_1_3_4_5_7_7_9

/-- Add 17 of the attesting chain: keep-cur and back are ground-false and the propagated result IS the next transcribed table (49 concrete pointwise checks). -/
theorem addEq_17_1_3_4_5_7_7_9 : uAdd T8_1_3_4_5_7_7_9_8 (6 : Fin 7) (4 : Fin 7) ((33 : ℚ) / (23 : ℚ)) true = some T8_1_3_4_5_7_7_9_9 :=
  uAdd_eq_some' (by simp [uKeepCur, uBackCond, T8_1_3_4_5_7_7_9_8] <;> norm_num) (by simp [uBack, uBackCond, T8_1_3_4_5_7_7_9_8] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, T8_1_3_4_5_7_7_9_8, T8_1_3_4_5_7_7_9_9] <;> norm_num)

#print axioms addEq_17_1_3_4_5_7_7_9

/-- Add 18 of the attesting chain: the entry at its pair is already tight (`uKeepCur` fires ground-true), so the table is unchanged. -/
theorem addEq_18_1_3_4_5_7_7_9 : uAdd T8_1_3_4_5_7_7_9_9 (4 : Fin 7) (6 : Fin 7) ((25 : ℚ) / (33 : ℚ)) true = some T8_1_3_4_5_7_7_9_9 :=
  by simp [uAdd, uKeepCur, uBackCond, uBack, uTighter, uProp, T8_1_3_4_5_7_7_9_9] <;> norm_num

#print axioms addEq_18_1_3_4_5_7_7_9

/-- Add 19 of the attesting chain: the entry at its pair is already tight (`uKeepCur` fires ground-true), so the table is unchanged. -/
theorem addEq_19_1_3_4_5_7_7_9 : uAdd T8_1_3_4_5_7_7_9_9 (4 : Fin 7) (2 : Fin 7) ((25 : ℚ) / (15 : ℚ)) true = some T8_1_3_4_5_7_7_9_9 :=
  by simp [uAdd, uKeepCur, uBackCond, uBack, uTighter, uProp, T8_1_3_4_5_7_7_9_9] <;> norm_num

#print axioms addEq_19_1_3_4_5_7_7_9

/-- Add 20 of the attesting chain: keep-cur and back are ground-false and the propagated result IS the next transcribed table (49 concrete pointwise checks). -/
theorem addEq_20_1_3_4_5_7_7_9 : uAdd T8_1_3_4_5_7_7_9_9 (2 : Fin 7) (4 : Fin 7) ((17 : ℚ) / (25 : ℚ)) true = some T8_1_3_4_5_7_7_9_10 :=
  uAdd_eq_some' (by simp [uKeepCur, uBackCond, T8_1_3_4_5_7_7_9_9] <;> norm_num) (by simp [uBack, uBackCond, T8_1_3_4_5_7_7_9_9] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, T8_1_3_4_5_7_7_9_9, T8_1_3_4_5_7_7_9_10] <;> norm_num)

#print axioms addEq_20_1_3_4_5_7_7_9

/-- Add 21 of the attesting chain: keep-cur and back are ground-false and the propagated result IS the next transcribed table (49 concrete pointwise checks). -/
theorem addEq_21_1_3_4_5_7_7_9 : uAdd T8_1_3_4_5_7_7_9_10 (2 : Fin 7) (6 : Fin 7) ((17 : ℚ) / (39 : ℚ)) true = some T8_1_3_4_5_7_7_9_11 :=
  uAdd_eq_some' (by simp [uKeepCur, uBackCond, T8_1_3_4_5_7_7_9_10] <;> norm_num) (by simp [uBack, uBackCond, T8_1_3_4_5_7_7_9_10] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, T8_1_3_4_5_7_7_9_10, T8_1_3_4_5_7_7_9_11] <;> norm_num)

#print axioms addEq_21_1_3_4_5_7_7_9

/-- Add 22 of the attesting chain: the entry at its pair is already tight (`uKeepCur` fires ground-true), so the table is unchanged. -/
theorem addEq_22_1_3_4_5_7_7_9 : uAdd T8_1_3_4_5_7_7_9_11 (6 : Fin 7) (2 : Fin 7) ((41 : ℚ) / (17 : ℚ)) true = some T8_1_3_4_5_7_7_9_11 :=
  by simp [uAdd, uKeepCur, uBackCond, uBack, uTighter, uProp, T8_1_3_4_5_7_7_9_11] <;> norm_num

#print axioms addEq_22_1_3_4_5_7_7_9

/-- Add 23 of the attesting chain: keep-cur and back are ground-false and the propagated result IS the next transcribed table (49 concrete pointwise checks). -/
theorem addEq_23_1_3_4_5_7_7_9 : uAdd T8_1_3_4_5_7_7_9_11 (6 : Fin 7) (5 : Fin 7) ((41 : ℚ) / (31 : ℚ)) true = some T8_1_3_4_5_7_7_9_12 :=
  uAdd_eq_some' (by simp [uKeepCur, uBackCond, T8_1_3_4_5_7_7_9_11] <;> norm_num) (by simp [uBack, uBackCond, T8_1_3_4_5_7_7_9_11] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, T8_1_3_4_5_7_7_9_11, T8_1_3_4_5_7_7_9_12] <;> norm_num)

#print axioms addEq_23_1_3_4_5_7_7_9

/-- Add 24 of the attesting chain: the entry at its pair is already tight (`uKeepCur` fires ground-true), so the table is unchanged. -/
theorem addEq_24_1_3_4_5_7_7_9 : uAdd T8_1_3_4_5_7_7_9_12 (5 : Fin 7) (6 : Fin 7) ((33 : ℚ) / (41 : ℚ)) true = some T8_1_3_4_5_7_7_9_12 :=
  by simp [uAdd, uKeepCur, uBackCond, uBack, uTighter, uProp, T8_1_3_4_5_7_7_9_12] <;> norm_num

#print axioms addEq_24_1_3_4_5_7_7_9

/-- Add 25 of the attesting chain: keep-cur and back are ground-false and the propagated result IS the next transcribed table (49 concrete pointwise checks). -/
theorem addEq_25_1_3_4_5_7_7_9 : uAdd T8_1_3_4_5_7_7_9_12 (5 : Fin 7) (3 : Fin 7) ((33 : ℚ) / (23 : ℚ)) true = some T8_1_3_4_5_7_7_9_13 :=
  uAdd_eq_some' (by simp [uKeepCur, uBackCond, T8_1_3_4_5_7_7_9_12] <;> norm_num) (by simp [uBack, uBackCond, T8_1_3_4_5_7_7_9_12] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, T8_1_3_4_5_7_7_9_12, T8_1_3_4_5_7_7_9_13] <;> norm_num)

#print axioms addEq_25_1_3_4_5_7_7_9

/-- Add 26 of the attesting chain: the entry at its pair is already tight (`uKeepCur` fires ground-true), so the table is unchanged. -/
theorem addEq_26_1_3_4_5_7_7_9 : uAdd T8_1_3_4_5_7_7_9_13 (3 : Fin 7) (5 : Fin 7) ((25 : ℚ) / (33 : ℚ)) true = some T8_1_3_4_5_7_7_9_13 :=
  by simp [uAdd, uKeepCur, uBackCond, uBack, uTighter, uProp, T8_1_3_4_5_7_7_9_13] <;> norm_num

#print axioms addEq_26_1_3_4_5_7_7_9

/-- Add 27 of the attesting chain: the entry at its pair is already tight (`uKeepCur` fires ground-true), so the table is unchanged. -/
theorem addEq_27_1_3_4_5_7_7_9 : uAdd T8_1_3_4_5_7_7_9_13 (3 : Fin 7) (4 : Fin 7) ((25 : ℚ) / (31 : ℚ)) true = some T8_1_3_4_5_7_7_9_13 :=
  by simp [uAdd, uKeepCur, uBackCond, uBack, uTighter, uProp, T8_1_3_4_5_7_7_9_13] <;> norm_num

#print axioms addEq_27_1_3_4_5_7_7_9

/-- Add 28 of the attesting chain: the entry at its pair is already tight (`uKeepCur` fires ground-true), so the table is unchanged. -/
theorem addEq_28_1_3_4_5_7_7_9 : uAdd T8_1_3_4_5_7_7_9_13 (4 : Fin 7) (3 : Fin 7) ((33 : ℚ) / (25 : ℚ)) true = some T8_1_3_4_5_7_7_9_13 :=
  by simp [uAdd, uKeepCur, uBackCond, uBack, uTighter, uProp, T8_1_3_4_5_7_7_9_13] <;> norm_num

#print axioms addEq_28_1_3_4_5_7_7_9

/-- Add 29 of the attesting chain: keep-cur and back are ground-false and the propagated result IS the next transcribed table (49 concrete pointwise checks). -/
theorem addEq_29_1_3_4_5_7_7_9 : uAdd T8_1_3_4_5_7_7_9_13 (4 : Fin 7) (1 : Fin 7) ((33 : ℚ) / (15 : ℚ)) true = some T8_1_3_4_5_7_7_9_14 :=
  uAdd_eq_some' (by simp [uKeepCur, uBackCond, T8_1_3_4_5_7_7_9_13] <;> norm_num) (by simp [uBack, uBackCond, T8_1_3_4_5_7_7_9_13] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, T8_1_3_4_5_7_7_9_13, T8_1_3_4_5_7_7_9_14] <;> norm_num)

#print axioms addEq_29_1_3_4_5_7_7_9

/-- Add 30 of the attesting chain: the entry at its pair is already tight (`uKeepCur` fires ground-true), so the table is unchanged. -/
theorem addEq_30_1_3_4_5_7_7_9 : uAdd T8_1_3_4_5_7_7_9_14 (1 : Fin 7) (4 : Fin 7) ((17 : ℚ) / (33 : ℚ)) true = some T8_1_3_4_5_7_7_9_14 :=
  by simp [uAdd, uKeepCur, uBackCond, uBack, uTighter, uProp, T8_1_3_4_5_7_7_9_14] <;> norm_num

#print axioms addEq_30_1_3_4_5_7_7_9

/-- Add 31 of the attesting chain: keep-cur and back are ground-false and the propagated result IS the next transcribed table (49 concrete pointwise checks). -/
theorem addEq_31_1_3_4_5_7_7_9 : uAdd T8_1_3_4_5_7_7_9_14 (1 : Fin 7) (2 : Fin 7) ((17 : ℚ) / (23 : ℚ)) true = some T8_1_3_4_5_7_7_9_15 :=
  uAdd_eq_some' (by simp [uKeepCur, uBackCond, T8_1_3_4_5_7_7_9_14] <;> norm_num) (by simp [uBack, uBackCond, T8_1_3_4_5_7_7_9_14] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, T8_1_3_4_5_7_7_9_14, T8_1_3_4_5_7_7_9_15] <;> norm_num)

#print axioms addEq_31_1_3_4_5_7_7_9

/-- Add 32 of the attesting chain: the entry at its pair is already tight (`uKeepCur` fires ground-true), so the table is unchanged. -/
theorem addEq_32_1_3_4_5_7_7_9 : uAdd T8_1_3_4_5_7_7_9_15 (2 : Fin 7) (1 : Fin 7) ((25 : ℚ) / (17 : ℚ)) true = some T8_1_3_4_5_7_7_9_15 :=
  by simp [uAdd, uKeepCur, uBackCond, uBack, uTighter, uProp, T8_1_3_4_5_7_7_9_15] <;> norm_num

#print axioms addEq_32_1_3_4_5_7_7_9

/-- Add 33 of the attesting chain: the entry at its pair is already tight (`uKeepCur` fires ground-true), so the table is unchanged. -/
theorem addEq_33_1_3_4_5_7_7_9 : uAdd T8_1_3_4_5_7_7_9_15 (2 : Fin 7) (3 : Fin 7) ((25 : ℚ) / (31 : ℚ)) true = some T8_1_3_4_5_7_7_9_15 :=
  by simp [uAdd, uKeepCur, uBackCond, uBack, uTighter, uProp, T8_1_3_4_5_7_7_9_15] <;> norm_num

#print axioms addEq_33_1_3_4_5_7_7_9

/-- Add 34 of the attesting chain: the entry at its pair is already tight (`uKeepCur` fires ground-true), so the table is unchanged. -/
theorem addEq_34_1_3_4_5_7_7_9 : uAdd T8_1_3_4_5_7_7_9_15 (3 : Fin 7) (2 : Fin 7) ((33 : ℚ) / (25 : ℚ)) true = some T8_1_3_4_5_7_7_9_15 :=
  by simp [uAdd, uKeepCur, uBackCond, uBack, uTighter, uProp, T8_1_3_4_5_7_7_9_15] <;> norm_num

#print axioms addEq_34_1_3_4_5_7_7_9

/-- Add 35 of the attesting chain: keep-cur and back are ground-false and the propagated result IS the next transcribed table (49 concrete pointwise checks). -/
theorem addEq_35_1_3_4_5_7_7_9 : uAdd T8_1_3_4_5_7_7_9_15 (3 : Fin 7) (5 : Fin 7) ((33 : ℚ) / (47 : ℚ)) true = some T8_1_3_4_5_7_7_9_16 :=
  uAdd_eq_some' (by simp [uKeepCur, uBackCond, T8_1_3_4_5_7_7_9_15] <;> norm_num) (by simp [uBack, uBackCond, T8_1_3_4_5_7_7_9_15] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, T8_1_3_4_5_7_7_9_15, T8_1_3_4_5_7_7_9_16] <;> norm_num)

#print axioms addEq_35_1_3_4_5_7_7_9

/-- Add 36 of the attesting chain: the entry at its pair is already tight (`uKeepCur` fires ground-true), so the table is unchanged. -/
theorem addEq_36_1_3_4_5_7_7_9 : uAdd T8_1_3_4_5_7_7_9_16 (5 : Fin 7) (3 : Fin 7) ((49 : ℚ) / (33 : ℚ)) true = some T8_1_3_4_5_7_7_9_16 :=
  by simp [uAdd, uKeepCur, uBackCond, uBack, uTighter, uProp, T8_1_3_4_5_7_7_9_16] <;> norm_num

#print axioms addEq_36_1_3_4_5_7_7_9

/-- Step 1 of the attesting chain: its two `uAdd`s on positive numerators compose to the step equation. -/
theorem stepEq_1_1_3_4_5_7_7_9 : uStep (mkOf (![1, 3, 4, 5, 7, 7, 9] : Fin 7 → ℤ)) (0 : Fin 7) (5 : Fin 7) (1 : ℚ) (7 : ℚ) (9 : ℚ) = some T8_1_3_4_5_7_7_9_1 :=
  uStep_eq_some' (by norm_num) (by norm_num) (by norm_num) addEq_1_1_3_4_5_7_7_9 addEq_2_1_3_4_5_7_7_9

#print axioms stepEq_1_1_3_4_5_7_7_9

/-- Step 2 of the attesting chain: its two `uAdd`s on positive numerators compose to the step equation. -/
theorem stepEq_2_1_3_4_5_7_7_9 : uStep T8_1_3_4_5_7_7_9_1 (5 : Fin 7) (4 : Fin 7) (9 : ℚ) (7 : ℚ) (9 : ℚ) = some T8_1_3_4_5_7_7_9_1 :=
  uStep_eq_some' (by norm_num) (by norm_num) (by norm_num) addEq_3_1_3_4_5_7_7_9 addEq_4_1_3_4_5_7_7_9

#print axioms stepEq_2_1_3_4_5_7_7_9

/-- Step 3 of the attesting chain: its two `uAdd`s on positive numerators compose to the step equation. -/
theorem stepEq_3_1_3_4_5_7_7_9 : uStep T8_1_3_4_5_7_7_9_1 (4 : Fin 7) (3 : Fin 7) (9 : ℚ) (7 : ℚ) (9 : ℚ) = some T8_1_3_4_5_7_7_9_2 :=
  uStep_eq_some' (by norm_num) (by norm_num) (by norm_num) addEq_5_1_3_4_5_7_7_9 addEq_6_1_3_4_5_7_7_9

#print axioms stepEq_3_1_3_4_5_7_7_9

/-- Step 4 of the attesting chain: its two `uAdd`s on positive numerators compose to the step equation. -/
theorem stepEq_4_1_3_4_5_7_7_9 : uStep T8_1_3_4_5_7_7_9_2 (3 : Fin 7) (2 : Fin 7) (9 : ℚ) (7 : ℚ) (9 : ℚ) = some T8_1_3_4_5_7_7_9_3 :=
  uStep_eq_some' (by norm_num) (by norm_num) (by norm_num) addEq_7_1_3_4_5_7_7_9 addEq_8_1_3_4_5_7_7_9

#print axioms stepEq_4_1_3_4_5_7_7_9

/-- Step 5 of the attesting chain: its two `uAdd`s on positive numerators compose to the step equation. -/
theorem stepEq_5_1_3_4_5_7_7_9 : uStep T8_1_3_4_5_7_7_9_3 (2 : Fin 7) (5 : Fin 7) (9 : ℚ) (15 : ℚ) (17 : ℚ) = some T8_1_3_4_5_7_7_9_5 :=
  uStep_eq_some' (by norm_num) (by norm_num) (by norm_num) addEq_9_1_3_4_5_7_7_9 addEq_10_1_3_4_5_7_7_9

#print axioms stepEq_5_1_3_4_5_7_7_9

/-- Step 6 of the attesting chain: its two `uAdd`s on positive numerators compose to the step equation. -/
theorem stepEq_6_1_3_4_5_7_7_9 : uStep T8_1_3_4_5_7_7_9_5 (5 : Fin 7) (1 : Fin 7) (17 : ℚ) (7 : ℚ) (9 : ℚ) = some T8_1_3_4_5_7_7_9_6 :=
  uStep_eq_some' (by norm_num) (by norm_num) (by norm_num) addEq_11_1_3_4_5_7_7_9 addEq_12_1_3_4_5_7_7_9

#print axioms stepEq_6_1_3_4_5_7_7_9

/-- Step 7 of the attesting chain: its two `uAdd`s on positive numerators compose to the step equation. -/
theorem stepEq_7_1_3_4_5_7_7_9 : uStep T8_1_3_4_5_7_7_9_6 (1 : Fin 7) (3 : Fin 7) (9 : ℚ) (15 : ℚ) (17 : ℚ) = some T8_1_3_4_5_7_7_9_7 :=
  uStep_eq_some' (by norm_num) (by norm_num) (by norm_num) addEq_13_1_3_4_5_7_7_9 addEq_14_1_3_4_5_7_7_9

#print axioms stepEq_7_1_3_4_5_7_7_9

/-- Step 8 of the attesting chain: its two `uAdd`s on positive numerators compose to the step equation. -/
theorem stepEq_8_1_3_4_5_7_7_9 : uStep T8_1_3_4_5_7_7_9_7 (3 : Fin 7) (6 : Fin 7) (17 : ℚ) (31 : ℚ) (33 : ℚ) = some T8_1_3_4_5_7_7_9_8 :=
  uStep_eq_some' (by norm_num) (by norm_num) (by norm_num) addEq_15_1_3_4_5_7_7_9 addEq_16_1_3_4_5_7_7_9

#print axioms stepEq_8_1_3_4_5_7_7_9

/-- Step 9 of the attesting chain: its two `uAdd`s on positive numerators compose to the step equation. -/
theorem stepEq_9_1_3_4_5_7_7_9 : uStep T8_1_3_4_5_7_7_9_8 (6 : Fin 7) (4 : Fin 7) (33 : ℚ) (23 : ℚ) (25 : ℚ) = some T8_1_3_4_5_7_7_9_9 :=
  uStep_eq_some' (by norm_num) (by norm_num) (by norm_num) addEq_17_1_3_4_5_7_7_9 addEq_18_1_3_4_5_7_7_9

#print axioms stepEq_9_1_3_4_5_7_7_9

/-- Step 10 of the attesting chain: its two `uAdd`s on positive numerators compose to the step equation. -/
theorem stepEq_10_1_3_4_5_7_7_9 : uStep T8_1_3_4_5_7_7_9_9 (4 : Fin 7) (2 : Fin 7) (25 : ℚ) (15 : ℚ) (17 : ℚ) = some T8_1_3_4_5_7_7_9_10 :=
  uStep_eq_some' (by norm_num) (by norm_num) (by norm_num) addEq_19_1_3_4_5_7_7_9 addEq_20_1_3_4_5_7_7_9

#print axioms stepEq_10_1_3_4_5_7_7_9

/-- Step 11 of the attesting chain: its two `uAdd`s on positive numerators compose to the step equation. -/
theorem stepEq_11_1_3_4_5_7_7_9 : uStep T8_1_3_4_5_7_7_9_10 (2 : Fin 7) (6 : Fin 7) (17 : ℚ) (39 : ℚ) (41 : ℚ) = some T8_1_3_4_5_7_7_9_11 :=
  uStep_eq_some' (by norm_num) (by norm_num) (by norm_num) addEq_21_1_3_4_5_7_7_9 addEq_22_1_3_4_5_7_7_9

#print axioms stepEq_11_1_3_4_5_7_7_9

/-- Step 12 of the attesting chain: its two `uAdd`s on positive numerators compose to the step equation. -/
theorem stepEq_12_1_3_4_5_7_7_9 : uStep T8_1_3_4_5_7_7_9_11 (6 : Fin 7) (5 : Fin 7) (41 : ℚ) (31 : ℚ) (33 : ℚ) = some T8_1_3_4_5_7_7_9_12 :=
  uStep_eq_some' (by norm_num) (by norm_num) (by norm_num) addEq_23_1_3_4_5_7_7_9 addEq_24_1_3_4_5_7_7_9

#print axioms stepEq_12_1_3_4_5_7_7_9

/-- Step 13 of the attesting chain: its two `uAdd`s on positive numerators compose to the step equation. -/
theorem stepEq_13_1_3_4_5_7_7_9 : uStep T8_1_3_4_5_7_7_9_12 (5 : Fin 7) (3 : Fin 7) (33 : ℚ) (23 : ℚ) (25 : ℚ) = some T8_1_3_4_5_7_7_9_13 :=
  uStep_eq_some' (by norm_num) (by norm_num) (by norm_num) addEq_25_1_3_4_5_7_7_9 addEq_26_1_3_4_5_7_7_9

#print axioms stepEq_13_1_3_4_5_7_7_9

/-- Step 14 of the attesting chain: its two `uAdd`s on positive numerators compose to the step equation. -/
theorem stepEq_14_1_3_4_5_7_7_9 : uStep T8_1_3_4_5_7_7_9_13 (3 : Fin 7) (4 : Fin 7) (25 : ℚ) (31 : ℚ) (33 : ℚ) = some T8_1_3_4_5_7_7_9_13 :=
  uStep_eq_some' (by norm_num) (by norm_num) (by norm_num) addEq_27_1_3_4_5_7_7_9 addEq_28_1_3_4_5_7_7_9

#print axioms stepEq_14_1_3_4_5_7_7_9

/-- Step 15 of the attesting chain: its two `uAdd`s on positive numerators compose to the step equation. -/
theorem stepEq_15_1_3_4_5_7_7_9 : uStep T8_1_3_4_5_7_7_9_13 (4 : Fin 7) (1 : Fin 7) (33 : ℚ) (15 : ℚ) (17 : ℚ) = some T8_1_3_4_5_7_7_9_14 :=
  uStep_eq_some' (by norm_num) (by norm_num) (by norm_num) addEq_29_1_3_4_5_7_7_9 addEq_30_1_3_4_5_7_7_9

#print axioms stepEq_15_1_3_4_5_7_7_9

/-- Step 16 of the attesting chain: its two `uAdd`s on positive numerators compose to the step equation. -/
theorem stepEq_16_1_3_4_5_7_7_9 : uStep T8_1_3_4_5_7_7_9_14 (1 : Fin 7) (2 : Fin 7) (17 : ℚ) (23 : ℚ) (25 : ℚ) = some T8_1_3_4_5_7_7_9_15 :=
  uStep_eq_some' (by norm_num) (by norm_num) (by norm_num) addEq_31_1_3_4_5_7_7_9 addEq_32_1_3_4_5_7_7_9

#print axioms stepEq_16_1_3_4_5_7_7_9

/-- Step 17 of the attesting chain: its two `uAdd`s on positive numerators compose to the step equation. -/
theorem stepEq_17_1_3_4_5_7_7_9 : uStep T8_1_3_4_5_7_7_9_15 (2 : Fin 7) (3 : Fin 7) (25 : ℚ) (31 : ℚ) (33 : ℚ) = some T8_1_3_4_5_7_7_9_15 :=
  uStep_eq_some' (by norm_num) (by norm_num) (by norm_num) addEq_33_1_3_4_5_7_7_9 addEq_34_1_3_4_5_7_7_9

#print axioms stepEq_17_1_3_4_5_7_7_9

/-- Step 18 of the attesting chain: its two `uAdd`s on positive numerators compose to the step equation. -/
theorem stepEq_18_1_3_4_5_7_7_9 : uStep T8_1_3_4_5_7_7_9_15 (3 : Fin 7) (5 : Fin 7) (33 : ℚ) (47 : ℚ) (49 : ℚ) = some T8_1_3_4_5_7_7_9_16 :=
  uStep_eq_some' (by norm_num) (by norm_num) (by norm_num) addEq_35_1_3_4_5_7_7_9 addEq_36_1_3_4_5_7_7_9

#print axioms stepEq_18_1_3_4_5_7_7_9

/-- The 18-step prefix run's trace table IS `T8_1_3_4_5_7_7_9_16` (peel the first 18 step equations; entries only tighten along a run). -/
theorem traceP_1_3_4_5_7_7_9_p18 {V : UTable} {af : Fin 7} {Af : ℚ}
    (hrun : chainRun (mkOf (![1, 3, 4, 5, 7, 7, 9] : Fin 7 → ℤ)) 0 1 steps8_1_3_4_5_7_7_9 = some (V, af, Af)) :
    V = T8_1_3_4_5_7_7_9_16 := by
  simp only [steps8_1_3_4_5_7_7_9,
    chainRun_step_some stepEq_1_1_3_4_5_7_7_9,
    chainRun_step_some stepEq_2_1_3_4_5_7_7_9,
    chainRun_step_some stepEq_3_1_3_4_5_7_7_9,
    chainRun_step_some stepEq_4_1_3_4_5_7_7_9,
    chainRun_step_some stepEq_5_1_3_4_5_7_7_9,
    chainRun_step_some stepEq_6_1_3_4_5_7_7_9,
    chainRun_step_some stepEq_7_1_3_4_5_7_7_9,
    chainRun_step_some stepEq_8_1_3_4_5_7_7_9,
    chainRun_step_some stepEq_9_1_3_4_5_7_7_9,
    chainRun_step_some stepEq_10_1_3_4_5_7_7_9,
    chainRun_step_some stepEq_11_1_3_4_5_7_7_9,
    chainRun_step_some stepEq_12_1_3_4_5_7_7_9,
    chainRun_step_some stepEq_13_1_3_4_5_7_7_9,
    chainRun_step_some stepEq_14_1_3_4_5_7_7_9,
    chainRun_step_some stepEq_15_1_3_4_5_7_7_9,
    chainRun_step_some stepEq_16_1_3_4_5_7_7_9,
    chainRun_step_some stepEq_17_1_3_4_5_7_7_9,
    chainRun_step_some stepEq_18_1_3_4_5_7_7_9,
    chainRun_nil, Option.some.injEq, Prod.mk.injEq] at hrun
  exact hrun.1.symm

#print axioms traceP_1_3_4_5_7_7_9_p18

/-- The per-record attestation: the 18-step prefix chain's closed-trace entry at
(0, 5) is 594/4277, dominating the record's cap 594/4277. -/
theorem attests_1_3_4_5_7_7_9_r0 : Attests8 (![1, 3, 4, 5, 7, 7, 9] : Fin 7 → ℤ) ⟨5, 0, 13, 3, [(5, (594 / 4277 : ℝ))]⟩ steps8_1_3_4_5_7_7_9 :=
  by
  intro V af Af hrun
  have hV := traceP_1_3_4_5_7_7_9_p18 hrun
  rw [hV]
  exact capsDom_single ⟨(594 / 4277 : ℚ), true, by simp [T8_1_3_4_5_7_7_9_16], by norm_num⟩

#print axioms attests_1_3_4_5_7_7_9_r0

/-- The per-record attestation: the 18-step prefix chain's closed-trace entry at
(1, 5) is 944163/2262533, dominating the record's cap 99/235. -/
theorem attests_1_3_4_5_7_7_9_r1 : Attests8 (![1, 3, 4, 5, 7, 7, 9] : Fin 7 → ℤ) ⟨5, 1, 65, 31, [(5, (99 / 235 : ℝ))]⟩ steps8_1_3_4_5_7_7_9 :=
  by
  intro V af Af hrun
  have hV := traceP_1_3_4_5_7_7_9_p18 hrun
  rw [hV]
  exact capsDom_single ⟨(944163 / 2262533 : ℚ), true, by simp [T8_1_3_4_5_7_7_9_16], by norm_num⟩

#print axioms attests_1_3_4_5_7_7_9_r1

/-- The per-record attestation: the 18-step prefix chain's closed-trace entry at
(1, 5) is 944163/2262533, dominating the record's cap 99/235. -/
theorem attests_1_3_4_5_7_7_9_r2 : Attests8 (![1, 3, 4, 5, 7, 7, 9] : Fin 7 → ℤ) ⟨5, 1, 5, 3, [(5, (99 / 235 : ℝ))]⟩ steps8_1_3_4_5_7_7_9 :=
  by
  intro V af Af hrun
  have hV := traceP_1_3_4_5_7_7_9_p18 hrun
  rw [hV]
  exact capsDom_single ⟨(944163 / 2262533 : ℚ), true, by simp [T8_1_3_4_5_7_7_9_16], by norm_num⟩

#print axioms attests_1_3_4_5_7_7_9_r2

/-- The per-record attestation: the 18-step prefix chain's closed-trace entry at
(1, 5) is 944163/2262533, dominating the record's cap 99/235. -/
theorem attests_1_3_4_5_7_7_9_r3 : Attests8 (![1, 3, 4, 5, 7, 7, 9] : Fin 7 → ℤ) ⟨5, 1, 65, 47, [(5, (99 / 235 : ℝ))]⟩ steps8_1_3_4_5_7_7_9 :=
  by
  intro V af Af hrun
  have hV := traceP_1_3_4_5_7_7_9_p18 hrun
  rw [hV]
  exact capsDom_single ⟨(944163 / 2262533 : ℚ), true, by simp [T8_1_3_4_5_7_7_9_16], by norm_num⟩

#print axioms attests_1_3_4_5_7_7_9_r3

/-- Per-record attestation for this box:
box (1, 3, 4, 5, 7, 7, 9)'s strict-class family carries the faithful per-record datum from the
transcribed full closure -- every record is attested by a nested prefix of the one
attesting chain (records sharing a pair share the witness). -/
theorem chainDomPerRecord8_1_3_4_5_7_7_9 :
    ChainDomPerRecord8 (![1, 3, 4, 5, 7, 7, 9] : Fin 7 → ℤ) dumpFam_1_3_4_5_7_7_9 := by
  intro e he
  simp only [dumpFam_1_3_4_5_7_7_9, List.mem_cons] at he
  rcases he with rfl | rfl | rfl | rfl | h0
  · exact ⟨steps8_1_3_4_5_7_7_9, attests_1_3_4_5_7_7_9_r0⟩
  · exact ⟨steps8_1_3_4_5_7_7_9, attests_1_3_4_5_7_7_9_r1⟩
  · exact ⟨steps8_1_3_4_5_7_7_9, attests_1_3_4_5_7_7_9_r2⟩
  · exact ⟨steps8_1_3_4_5_7_7_9, attests_1_3_4_5_7_7_9_r3⟩
  · exact absurd h0 (by simp)

#print axioms chainDomPerRecord8_1_3_4_5_7_7_9


end Fresh.ChainDomPerRec8
