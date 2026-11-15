import Fresh.ChainDomPerRecStart
import Fresh.ChainDomTrace19

namespace Fresh.ChainDomPerRec8

open Fresh.ChainDomBase Fresh.CapChainsOfCarve Fresh.JoinFamComposed Fresh.OneSidedComposed Fresh.OneSidedGlue
  Fresh.UClosure Fresh.SpineSound Fresh.FilterAssembly Fresh.DumpDomData

-- the 49-point `fin_cases` checks and the big literal tables need headroom
set_option maxHeartbeats 10000000

/- `mk`'s (the `uMk` fold's) output for box (1, 3, 4, 5, 5, 5, 7) is transcribed verbatim
(`perrec8_gen_v1.py`, value-verbatim mirror of `Fresh.UClosureKill`'s `uKeepCur`/
`uBack`/`uProp`/`uAdd`; 49 entries -- the FULL closure is dense) as `mkTab_1_3_4_5_5_5_7`
(section 2).  Census cross-check: at every census pair the transcription agrees with
the banked `Fresh.DumpDomData` `u0e_1_3_4_5_5_5_7_*` facts (`mkU0_1_3_4_5_5_5_7_*` below). -/

/-- `mk`'s entry at (0, 6) for box (1, 3, 4, 5, 5, 5, 7): exact census datum (cross-checked
against the banked `Fresh.DumpDomData.u0e_1_3_4_5_5_5_7_0_6`). -/
theorem mke_1_3_4_5_5_5_7_0_6 : mkOf (![1, 3, 4, 5, 5, 5, 7] : Fin 7 → ℤ) (0 : Fin 7) (6 : Fin 7) = some ((2 / 13 : ℚ), false) :=
  by simp [mkOf, mkTab_1_3_4_5_5_5_7]

#print axioms mke_1_3_4_5_5_5_7_0_6

/-- The closure transcription agrees with the sparse census transcription at (0, 6). -/
theorem mkU0_1_3_4_5_5_5_7_0_6 : mkOf (![1, 3, 4, 5, 5, 5, 7] : Fin 7 → ℤ) (0 : Fin 7) (6 : Fin 7) = u0Of (![1, 3, 4, 5, 5, 5, 7] : Fin 7 → ℤ) (0 : Fin 7) (6 : Fin 7) :=
  by rw [mke_1_3_4_5_5_5_7_0_6, u0e_1_3_4_5_5_5_7_0_6]

#print axioms mkU0_1_3_4_5_5_5_7_0_6

/-- `mk`'s entry at (1, 6) for box (1, 3, 4, 5, 5, 5, 7): exact census datum (cross-checked
against the banked `Fresh.DumpDomData.u0e_1_3_4_5_5_5_7_1_6`). -/
theorem mke_1_3_4_5_5_5_7_1_6 : mkOf (![1, 3, 4, 5, 5, 5, 7] : Fin 7 → ℤ) (1 : Fin 7) (6 : Fin 7) = some ((7 / 13 : ℚ), false) :=
  by simp [mkOf, mkTab_1_3_4_5_5_5_7]

#print axioms mke_1_3_4_5_5_5_7_1_6

/-- The closure transcription agrees with the sparse census transcription at (1, 6). -/
theorem mkU0_1_3_4_5_5_5_7_1_6 : mkOf (![1, 3, 4, 5, 5, 5, 7] : Fin 7 → ℤ) (1 : Fin 7) (6 : Fin 7) = u0Of (![1, 3, 4, 5, 5, 5, 7] : Fin 7 → ℤ) (1 : Fin 7) (6 : Fin 7) :=
  by rw [mke_1_3_4_5_5_5_7_1_6, u0e_1_3_4_5_5_5_7_1_6]

#print axioms mkU0_1_3_4_5_5_5_7_1_6

/-- The EMPTY-chain non-vacuity for box (1, 3, 4, 5, 5, 5, 7): every strict witness's cap is
strictly TIGHTER than the closure entry at its pair, so `CapsDom (mkOf (![1, 3, 4, 5, 5, 5, 7] : Fin 7 → ℤ)) ...`
is refuted on every record -- a witness of the existential must be a genuine
dominating run (mirror of `Fresh.DumpDomData.not_capsDomU0all_*`). -/
theorem not_capsDomMk8all_1_3_4_5_5_5_7 :
    ∀ e ∈ dumpFam_1_3_4_5_5_5_7.edges,
      ¬ CapsDom (mkOf (![1, 3, 4, 5, 5, 5, 7] : Fin 7 → ℤ)) e.y e.caps e.x := by
  intro e he
  simp only [dumpFam_1_3_4_5_5_5_7, List.mem_cons] at he
  rcases he with rfl | rfl | rfl | rfl | h0
  · exact not_capsDomU0_of_entry_lt (mke_1_3_4_5_5_5_7_0_6) (by norm_num)
  · exact not_capsDomU0_of_entry_lt (mke_1_3_4_5_5_5_7_1_6) (by norm_num)
  · exact not_capsDomU0_of_entry_lt (mke_1_3_4_5_5_5_7_1_6) (by norm_num)
  · exact not_capsDomU0_of_entry_lt (mke_1_3_4_5_5_5_7_1_6) (by norm_num)
  · exact absurd h0 (by simp)

#print axioms not_capsDomMk8all_1_3_4_5_5_5_7

/-- The attesting-chain PREFIX for box (1, 3, 4, 5, 5, 5, 7): the first 14 steps of enumerated chain
index 0 of the box's dump enumeration (full word length 18; chain index and count
re-verified against the dump's `chains_enumerated` = 804 by `perrec8_gen_v1.py`).  Entries
only tighten along a run, so the prefix run's closed trace already carries the
dominating entries at every record pair ((0,6) first dominated at step 14, (1,6) first dominated at step 14). -/
def steps8_1_3_4_5_5_5_7 : List Step := [
  ⟨(6 : Fin 7), (7 : ℚ), (9 : ℚ)⟩, ⟨(5 : Fin 7), (7 : ℚ), (9 : ℚ)⟩, ⟨(3 : Fin 7), (7 : ℚ), (9 : ℚ)⟩, ⟨(2 : Fin 7), (7 : ℚ), (9 : ℚ)⟩, ⟨(1 : Fin 7), (7 : ℚ), (9 : ℚ)⟩, ⟨(5 : Fin 7), (15 : ℚ), (17 : ℚ)⟩, ⟨(4 : Fin 7), (15 : ℚ), (17 : ℚ)⟩, ⟨(3 : Fin 7), (15 : ℚ), (17 : ℚ)⟩, ⟨(2 : Fin 7), (15 : ℚ), (17 : ℚ)⟩, ⟨(5 : Fin 7), (23 : ℚ), (25 : ℚ)⟩, ⟨(6 : Fin 7), (31 : ℚ), (33 : ℚ)⟩, ⟨(1 : Fin 7), (15 : ℚ), (17 : ℚ)⟩, ⟨(3 : Fin 7), (23 : ℚ), (25 : ℚ)⟩, ⟨(6 : Fin 7), (39 : ℚ), (41 : ℚ)⟩
]

/-- transcribed trace table: T8_1_3_4_5_5_5_7_1 (the mirror run's add-end snapshot). -/
def T8_1_3_4_5_5_5_7_1 : UTable := fun p q =>
  if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((2 / 5 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((2 / 7 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((2 / 9 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((2 / 9 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((2 / 9 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 / 7 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((7 / 2 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((7 / 9 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((7 / 9 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((7 / 9 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 / 2 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 / 2 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((9 / 5 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((9 / 14 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((11 / 2 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((11 / 5 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((11 / 7 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((11 / 14 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((11 / 2 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((11 / 5 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((11 / 7 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((11 / 9 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((11 / 14 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((11 / 2 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((11 / 5 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((11 / 7 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((11 / 9 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((11 / 9 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((11 / 14 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((15 / 2 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((3 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((15 / 7 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((5 / 3 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((5 / 3 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((5 / 3 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

/-- transcribed trace table: T8_1_3_4_5_5_5_7_2 (the mirror run's add-end snapshot). -/
def T8_1_3_4_5_5_5_7_2 : UTable := fun p q =>
  if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((2 / 5 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((2 / 7 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((2 / 9 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((2 / 9 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((9 / 49 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 / 7 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((7 / 2 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((7 / 9 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((7 / 9 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((9 / 14 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 / 2 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 / 2 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((9 / 5 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((81 / 98 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((9 / 14 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((11 / 2 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((11 / 5 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((11 / 7 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((11 / 14 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((11 / 2 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((11 / 5 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((11 / 7 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((11 / 9 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((11 / 14 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((11 / 2 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((11 / 5 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((11 / 7 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((11 / 9 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((11 / 9 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((11 / 14 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((99 / 14 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((99 / 35 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((99 / 49 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((11 / 7 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((11 / 7 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((9 / 7 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

/-- transcribed trace table: T8_1_3_4_5_5_5_7_3 (the mirror run's add-end snapshot). -/
def T8_1_3_4_5_5_5_7_3 : UTable := fun p q =>
  if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((2 / 5 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((2 / 7 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((2 / 9 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((2 / 9 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((9 / 49 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 / 7 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((7 / 2 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((7 / 9 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((7 / 9 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((9 / 14 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 / 2 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 / 2 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((9 / 5 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((81 / 98 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((9 / 14 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((11 / 2 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((11 / 5 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((9 / 7 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((11 / 14 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((11 / 2 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((11 / 5 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((11 / 7 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((11 / 9 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((11 / 14 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((11 / 2 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((11 / 5 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((11 / 7 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((11 / 9 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((11 / 9 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((11 / 14 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((99 / 14 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((99 / 35 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((99 / 49 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((11 / 7 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((11 / 7 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((9 / 7 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

/-- transcribed trace table: T8_1_3_4_5_5_5_7_4 (the mirror run's add-end snapshot). -/
def T8_1_3_4_5_5_5_7_4 : UTable := fun p q =>
  if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((18 / 49 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((2 / 7 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((2 / 9 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((2 / 9 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((9 / 49 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 / 7 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((7 / 2 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((7 / 9 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((7 / 9 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((9 / 14 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 / 2 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 / 2 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((9 / 7 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((81 / 98 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((9 / 14 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((11 / 2 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((81 / 49 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((9 / 7 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((11 / 14 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((11 / 2 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((99 / 49 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((11 / 7 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((11 / 9 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((11 / 14 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((11 / 2 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((99 / 49 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((11 / 7 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((11 / 9 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((11 / 9 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((11 / 14 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((99 / 14 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((891 / 343 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((99 / 49 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((11 / 7 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((11 / 7 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((9 / 7 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

/-- transcribed trace table: T8_1_3_4_5_5_5_7_5 (the mirror run's add-end snapshot). -/
def T8_1_3_4_5_5_5_7_5 : UTable := fun p q =>
  if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((18 / 49 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((2 / 7 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((2 / 9 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((2 / 9 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((9 / 49 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 / 7 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((33 / 10 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((33 / 35 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((11 / 15 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((11 / 15 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((3 / 5 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((33 / 70 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((297 / 70 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((9 / 7 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((33 / 35 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((33 / 35 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((27 / 35 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((297 / 490 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((2673 / 490 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((81 / 49 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((9 / 7 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((243 / 245 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((2673 / 3430 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((11 / 2 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((99 / 49 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((11 / 7 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((11 / 9 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((11 / 14 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((11 / 2 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((99 / 49 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((11 / 7 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((11 / 9 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((11 / 9 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((11 / 14 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((99 / 14 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((891 / 343 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((99 / 49 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((11 / 7 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((11 / 7 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((9 / 7 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

/-- transcribed trace table: T8_1_3_4_5_5_5_7_6 (the mirror run's add-end snapshot). -/
def T8_1_3_4_5_5_5_7_6 : UTable := fun p q =>
  if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((17 / 49 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((2 / 7 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((2 / 9 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((2 / 9 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((9 / 49 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 / 7 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((33 / 10 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((33 / 35 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((11 / 15 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((11 / 15 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((3 / 5 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((33 / 70 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((297 / 70 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((9 / 7 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((33 / 35 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((33 / 35 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((27 / 35 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((297 / 490 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((2673 / 490 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((81 / 49 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((9 / 7 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((243 / 245 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((2673 / 3430 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((11 / 2 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((17 / 9 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((11 / 7 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((11 / 9 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((11 / 14 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((11 / 2 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((17 / 9 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((11 / 7 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((11 / 9 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((11 / 9 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((11 / 14 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((99 / 14 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((17 / 7 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((99 / 49 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((11 / 7 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((11 / 7 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((9 / 7 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

/-- transcribed trace table: T8_1_3_4_5_5_5_7_7 (the mirror run's add-end snapshot). -/
def T8_1_3_4_5_5_5_7_7 : UTable := fun p q =>
  if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((17 / 49 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((2 / 7 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((2 / 9 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((51 / 245 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((9 / 49 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 / 7 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((33 / 10 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((33 / 35 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((11 / 15 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 25 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((3 / 5 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((33 / 70 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((297 / 70 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((9 / 7 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((33 / 35 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((153 / 175 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((27 / 35 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((297 / 490 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((2673 / 490 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((81 / 49 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((9 / 7 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((243 / 245 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((2673 / 3430 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((11 / 2 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((17 / 9 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((11 / 7 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((11 / 9 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((11 / 14 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((11 / 2 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((17 / 9 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((11 / 7 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((11 / 9 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 15 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((11 / 14 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((99 / 14 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((17 / 7 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((99 / 49 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((11 / 7 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((51 / 35 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((9 / 7 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

/-- transcribed trace table: T8_1_3_4_5_5_5_7_8 (the mirror run's add-end snapshot). -/
def T8_1_3_4_5_5_5_7_8 : UTable := fun p q =>
  if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((17 / 49 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((2 / 7 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((2 / 9 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((51 / 245 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((9 / 49 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 / 7 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((33 / 10 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((33 / 35 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((11 / 15 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 25 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((3 / 5 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((33 / 70 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((297 / 70 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((9 / 7 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((33 / 35 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((153 / 175 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((27 / 35 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((297 / 490 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((2673 / 490 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((81 / 49 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((9 / 7 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((243 / 245 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((2673 / 3430 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((11 / 2 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((459 / 245 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((51 / 35 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((17 / 15 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((11 / 14 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((11 / 2 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((17 / 9 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((11 / 7 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((11 / 9 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 15 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((11 / 14 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((99 / 14 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((17 / 7 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((99 / 49 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((11 / 7 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((51 / 35 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((9 / 7 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

/-- transcribed trace table: T8_1_3_4_5_5_5_7_9 (the mirror run's add-end snapshot). -/
def T8_1_3_4_5_5_5_7_9 : UTable := fun p q =>
  if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((34 / 105 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((34 / 135 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((2 / 9 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((51 / 245 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((9 / 49 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 / 7 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((33 / 10 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((187 / 225 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((11 / 15 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 25 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((3 / 5 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((33 / 70 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((297 / 70 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((9 / 7 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((33 / 35 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((153 / 175 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((27 / 35 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((297 / 490 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((1683 / 350 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((51 / 35 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((17 / 15 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((867 / 875 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((153 / 175 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((1683 / 2450 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((9537 / 1750 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((289 / 175 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((289 / 225 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((17 / 15 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((867 / 875 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((9537 / 12250 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((11 / 2 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((187 / 105 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((187 / 135 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((11 / 9 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 15 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((11 / 14 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((99 / 14 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((561 / 245 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((187 / 105 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((11 / 7 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((51 / 35 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((9 / 7 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

/-- transcribed trace table: T8_1_3_4_5_5_5_7_10 (the mirror run's add-end snapshot). -/
def T8_1_3_4_5_5_5_7_10 : UTable := fun p q =>
  if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((34 / 105 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((34 / 135 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((2 / 9 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((51 / 245 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((9 / 49 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 / 7 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((33 / 10 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((187 / 225 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((11 / 15 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 25 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((3 / 5 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((33 / 70 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((187 / 46 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((9 / 7 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((187 / 207 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((289 / 345 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((17 / 23 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((187 / 322 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((3179 / 690 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((51 / 35 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((17 / 15 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((4913 / 5175 : ℚ), true)
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
  else if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 15 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((11 / 14 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((99 / 14 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((561 / 245 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((187 / 105 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((11 / 7 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((51 / 35 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((9 / 7 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

/-- transcribed trace table: T8_1_3_4_5_5_5_7_11 (the mirror run's add-end snapshot). -/
def T8_1_3_4_5_5_5_7_11 : UTable := fun p q =>
  if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((11 / 35 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((34 / 135 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((2 / 9 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((51 / 245 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((9 / 49 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 / 7 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((33 / 10 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((187 / 225 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((11 / 15 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 25 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((3 / 5 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((33 / 70 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((187 / 46 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((2057 / 1610 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((187 / 207 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((289 / 345 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((17 / 23 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((187 / 322 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((3179 / 690 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((34969 / 24150 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((17 / 15 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((4913 / 5175 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((289 / 345 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((3179 / 4830 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((54043 / 10350 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((594473 / 362250 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((289 / 225 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((17 / 15 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((4913 / 5175 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((54043 / 72450 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((11 / 2 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((121 / 70 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((187 / 135 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((11 / 9 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 15 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((11 / 14 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((99 / 14 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((11 / 5 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((187 / 105 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((11 / 7 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((51 / 35 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((9 / 7 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

/-- transcribed trace table: T8_1_3_4_5_5_5_7_12 (the mirror run's add-end snapshot). -/
def T8_1_3_4_5_5_5_7_12 : UTable := fun p q =>
  if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((110 / 351 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((34 / 135 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((2 / 9 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((170 / 819 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((50 / 273 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((50 / 351 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((33 / 10 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((187 / 225 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((11 / 15 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 25 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((3 / 5 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((55 / 117 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((187 / 46 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((10285 / 8073 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((187 / 207 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((289 / 345 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((17 / 23 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((4675 / 8073 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((825 / 182 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((55 / 39 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((17 / 15 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((85 / 91 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((75 / 91 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((25 / 39 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((935 / 182 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((187 / 117 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((289 / 225 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((17 / 15 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((85 / 91 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((85 / 117 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((11 / 2 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((605 / 351 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((187 / 135 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((11 / 9 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 15 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((275 / 351 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((99 / 14 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((11 / 5 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((187 / 105 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((11 / 7 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((51 / 35 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((9 / 7 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

/-- Add 1 of the attesting chain: keep-cur and back are ground-false and the propagated result IS the next transcribed table (49 concrete pointwise checks). -/
theorem addEq_1_1_3_4_5_5_5_7 : uAdd (mkOf (![1, 3, 4, 5, 5, 5, 7] : Fin 7 → ℤ)) (0 : Fin 7) (6 : Fin 7) ((1 : ℚ) / (7 : ℚ)) true = some T8_1_3_4_5_5_5_7_1 :=
  uAdd_eq_some' (by simp [uKeepCur, uBackCond, mkOf, mkTab_1_3_4_5_5_5_7] <;> norm_num) (by simp [uBack, uBackCond, mkOf, mkTab_1_3_4_5_5_5_7] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, mkOf, mkTab_1_3_4_5_5_5_7, T8_1_3_4_5_5_5_7_1] <;> norm_num)

#print axioms addEq_1_1_3_4_5_5_5_7

/-- Add 2 of the attesting chain: the entry at its pair is already tight (`uKeepCur` fires ground-true), so the table is unchanged. -/
theorem addEq_2_1_3_4_5_5_5_7 : uAdd T8_1_3_4_5_5_5_7_1 (6 : Fin 7) (0 : Fin 7) ((9 : ℚ) / (1 : ℚ)) true = some T8_1_3_4_5_5_5_7_1 :=
  by simp [uAdd, uKeepCur, uBackCond, uBack, uTighter, uProp, T8_1_3_4_5_5_5_7_1] <;> norm_num

#print axioms addEq_2_1_3_4_5_5_5_7

/-- Add 3 of the attesting chain: keep-cur and back are ground-false and the propagated result IS the next transcribed table (49 concrete pointwise checks). -/
theorem addEq_3_1_3_4_5_5_5_7 : uAdd T8_1_3_4_5_5_5_7_1 (6 : Fin 7) (5 : Fin 7) ((9 : ℚ) / (7 : ℚ)) true = some T8_1_3_4_5_5_5_7_2 :=
  uAdd_eq_some' (by simp [uKeepCur, uBackCond, T8_1_3_4_5_5_5_7_1] <;> norm_num) (by simp [uBack, uBackCond, T8_1_3_4_5_5_5_7_1] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, T8_1_3_4_5_5_5_7_1, T8_1_3_4_5_5_5_7_2] <;> norm_num)

#print axioms addEq_3_1_3_4_5_5_5_7

/-- Add 4 of the attesting chain: the entry at its pair is already tight (`uKeepCur` fires ground-true), so the table is unchanged. -/
theorem addEq_4_1_3_4_5_5_5_7 : uAdd T8_1_3_4_5_5_5_7_2 (5 : Fin 7) (6 : Fin 7) ((9 : ℚ) / (9 : ℚ)) true = some T8_1_3_4_5_5_5_7_2 :=
  by simp [uAdd, uKeepCur, uBackCond, uBack, uTighter, uProp, T8_1_3_4_5_5_5_7_2] <;> norm_num

#print axioms addEq_4_1_3_4_5_5_5_7

/-- Add 5 of the attesting chain: the entry at its pair is already tight (`uKeepCur` fires ground-true), so the table is unchanged. -/
theorem addEq_5_1_3_4_5_5_5_7 : uAdd T8_1_3_4_5_5_5_7_2 (5 : Fin 7) (3 : Fin 7) ((9 : ℚ) / (7 : ℚ)) true = some T8_1_3_4_5_5_5_7_2 :=
  by simp [uAdd, uKeepCur, uBackCond, uBack, uTighter, uProp, T8_1_3_4_5_5_5_7_2] <;> norm_num

#print axioms addEq_5_1_3_4_5_5_5_7

/-- Add 6 of the attesting chain: the entry at its pair is already tight (`uKeepCur` fires ground-true), so the table is unchanged. -/
theorem addEq_6_1_3_4_5_5_5_7 : uAdd T8_1_3_4_5_5_5_7_2 (3 : Fin 7) (5 : Fin 7) ((9 : ℚ) / (9 : ℚ)) true = some T8_1_3_4_5_5_5_7_2 :=
  by simp [uAdd, uKeepCur, uBackCond, uBack, uTighter, uProp, T8_1_3_4_5_5_5_7_2] <;> norm_num

#print axioms addEq_6_1_3_4_5_5_5_7

/-- Add 7 of the attesting chain: keep-cur and back are ground-false and the propagated result IS the next transcribed table (49 concrete pointwise checks). -/
theorem addEq_7_1_3_4_5_5_5_7 : uAdd T8_1_3_4_5_5_5_7_2 (3 : Fin 7) (2 : Fin 7) ((9 : ℚ) / (7 : ℚ)) true = some T8_1_3_4_5_5_5_7_3 :=
  uAdd_eq_some' (by simp [uKeepCur, uBackCond, T8_1_3_4_5_5_5_7_2] <;> norm_num) (by simp [uBack, uBackCond, T8_1_3_4_5_5_5_7_2] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, T8_1_3_4_5_5_5_7_2, T8_1_3_4_5_5_5_7_3] <;> norm_num)

#print axioms addEq_7_1_3_4_5_5_5_7

/-- Add 8 of the attesting chain: the entry at its pair is already tight (`uKeepCur` fires ground-true), so the table is unchanged. -/
theorem addEq_8_1_3_4_5_5_5_7 : uAdd T8_1_3_4_5_5_5_7_3 (2 : Fin 7) (3 : Fin 7) ((9 : ℚ) / (9 : ℚ)) true = some T8_1_3_4_5_5_5_7_3 :=
  by simp [uAdd, uKeepCur, uBackCond, uBack, uTighter, uProp, T8_1_3_4_5_5_5_7_3] <;> norm_num

#print axioms addEq_8_1_3_4_5_5_5_7

/-- Add 9 of the attesting chain: keep-cur and back are ground-false and the propagated result IS the next transcribed table (49 concrete pointwise checks). -/
theorem addEq_9_1_3_4_5_5_5_7 : uAdd T8_1_3_4_5_5_5_7_3 (2 : Fin 7) (1 : Fin 7) ((9 : ℚ) / (7 : ℚ)) true = some T8_1_3_4_5_5_5_7_4 :=
  uAdd_eq_some' (by simp [uKeepCur, uBackCond, T8_1_3_4_5_5_5_7_3] <;> norm_num) (by simp [uBack, uBackCond, T8_1_3_4_5_5_5_7_3] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, T8_1_3_4_5_5_5_7_3, T8_1_3_4_5_5_5_7_4] <;> norm_num)

#print axioms addEq_9_1_3_4_5_5_5_7

/-- Add 10 of the attesting chain: the entry at its pair is already tight (`uKeepCur` fires ground-true), so the table is unchanged. -/
theorem addEq_10_1_3_4_5_5_5_7 : uAdd T8_1_3_4_5_5_5_7_4 (1 : Fin 7) (2 : Fin 7) ((9 : ℚ) / (9 : ℚ)) true = some T8_1_3_4_5_5_5_7_4 :=
  by simp [uAdd, uKeepCur, uBackCond, uBack, uTighter, uProp, T8_1_3_4_5_5_5_7_4] <;> norm_num

#print axioms addEq_10_1_3_4_5_5_5_7

/-- Add 11 of the attesting chain: keep-cur and back are ground-false and the propagated result IS the next transcribed table (49 concrete pointwise checks). -/
theorem addEq_11_1_3_4_5_5_5_7 : uAdd T8_1_3_4_5_5_5_7_4 (1 : Fin 7) (5 : Fin 7) ((9 : ℚ) / (15 : ℚ)) true = some T8_1_3_4_5_5_5_7_5 :=
  uAdd_eq_some' (by simp [uKeepCur, uBackCond, T8_1_3_4_5_5_5_7_4] <;> norm_num) (by simp [uBack, uBackCond, T8_1_3_4_5_5_5_7_4] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, T8_1_3_4_5_5_5_7_4, T8_1_3_4_5_5_5_7_5] <;> norm_num)

#print axioms addEq_11_1_3_4_5_5_5_7

/-- Add 12 of the attesting chain: keep-cur and back are ground-false and the propagated result IS the next transcribed table (49 concrete pointwise checks). -/
theorem addEq_12_1_3_4_5_5_5_7 : uAdd T8_1_3_4_5_5_5_7_5 (5 : Fin 7) (1 : Fin 7) ((17 : ℚ) / (9 : ℚ)) true = some T8_1_3_4_5_5_5_7_6 :=
  uAdd_eq_some' (by simp [uKeepCur, uBackCond, T8_1_3_4_5_5_5_7_5] <;> norm_num) (by simp [uBack, uBackCond, T8_1_3_4_5_5_5_7_5] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, T8_1_3_4_5_5_5_7_5, T8_1_3_4_5_5_5_7_6] <;> norm_num)

#print axioms addEq_12_1_3_4_5_5_5_7

/-- Add 13 of the attesting chain: keep-cur and back are ground-false and the propagated result IS the next transcribed table (49 concrete pointwise checks). -/
theorem addEq_13_1_3_4_5_5_5_7 : uAdd T8_1_3_4_5_5_5_7_6 (5 : Fin 7) (4 : Fin 7) ((17 : ℚ) / (15 : ℚ)) true = some T8_1_3_4_5_5_5_7_7 :=
  uAdd_eq_some' (by simp [uKeepCur, uBackCond, T8_1_3_4_5_5_5_7_6] <;> norm_num) (by simp [uBack, uBackCond, T8_1_3_4_5_5_5_7_6] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, T8_1_3_4_5_5_5_7_6, T8_1_3_4_5_5_5_7_7] <;> norm_num)

#print axioms addEq_13_1_3_4_5_5_5_7

/-- Add 14 of the attesting chain: the entry at its pair is already tight (`uKeepCur` fires ground-true), so the table is unchanged. -/
theorem addEq_14_1_3_4_5_5_5_7 : uAdd T8_1_3_4_5_5_5_7_7 (4 : Fin 7) (5 : Fin 7) ((17 : ℚ) / (17 : ℚ)) true = some T8_1_3_4_5_5_5_7_7 :=
  by simp [uAdd, uKeepCur, uBackCond, uBack, uTighter, uProp, T8_1_3_4_5_5_5_7_7] <;> norm_num

#print axioms addEq_14_1_3_4_5_5_5_7

/-- Add 15 of the attesting chain: keep-cur and back are ground-false and the propagated result IS the next transcribed table (49 concrete pointwise checks). -/
theorem addEq_15_1_3_4_5_5_5_7 : uAdd T8_1_3_4_5_5_5_7_7 (4 : Fin 7) (3 : Fin 7) ((17 : ℚ) / (15 : ℚ)) true = some T8_1_3_4_5_5_5_7_8 :=
  uAdd_eq_some' (by simp [uKeepCur, uBackCond, T8_1_3_4_5_5_5_7_7] <;> norm_num) (by simp [uBack, uBackCond, T8_1_3_4_5_5_5_7_7] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, T8_1_3_4_5_5_5_7_7, T8_1_3_4_5_5_5_7_8] <;> norm_num)

#print axioms addEq_15_1_3_4_5_5_5_7

/-- Add 16 of the attesting chain: the entry at its pair is already tight (`uKeepCur` fires ground-true), so the table is unchanged. -/
theorem addEq_16_1_3_4_5_5_5_7 : uAdd T8_1_3_4_5_5_5_7_8 (3 : Fin 7) (4 : Fin 7) ((17 : ℚ) / (17 : ℚ)) true = some T8_1_3_4_5_5_5_7_8 :=
  by simp [uAdd, uKeepCur, uBackCond, uBack, uTighter, uProp, T8_1_3_4_5_5_5_7_8] <;> norm_num

#print axioms addEq_16_1_3_4_5_5_5_7

/-- Add 17 of the attesting chain: keep-cur and back are ground-false and the propagated result IS the next transcribed table (49 concrete pointwise checks). -/
theorem addEq_17_1_3_4_5_5_5_7 : uAdd T8_1_3_4_5_5_5_7_8 (3 : Fin 7) (2 : Fin 7) ((17 : ℚ) / (15 : ℚ)) true = some T8_1_3_4_5_5_5_7_9 :=
  uAdd_eq_some' (by simp [uKeepCur, uBackCond, T8_1_3_4_5_5_5_7_8] <;> norm_num) (by simp [uBack, uBackCond, T8_1_3_4_5_5_5_7_8] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, T8_1_3_4_5_5_5_7_8, T8_1_3_4_5_5_5_7_9] <;> norm_num)

#print axioms addEq_17_1_3_4_5_5_5_7

/-- Add 18 of the attesting chain: the entry at its pair is already tight (`uKeepCur` fires ground-true), so the table is unchanged. -/
theorem addEq_18_1_3_4_5_5_5_7 : uAdd T8_1_3_4_5_5_5_7_9 (2 : Fin 7) (3 : Fin 7) ((17 : ℚ) / (17 : ℚ)) true = some T8_1_3_4_5_5_5_7_9 :=
  by simp [uAdd, uKeepCur, uBackCond, uBack, uTighter, uProp, T8_1_3_4_5_5_5_7_9] <;> norm_num

#print axioms addEq_18_1_3_4_5_5_5_7

/-- Add 19 of the attesting chain: keep-cur and back are ground-false and the propagated result IS the next transcribed table (49 concrete pointwise checks). -/
theorem addEq_19_1_3_4_5_5_5_7 : uAdd T8_1_3_4_5_5_5_7_9 (2 : Fin 7) (5 : Fin 7) ((17 : ℚ) / (23 : ℚ)) true = some T8_1_3_4_5_5_5_7_10 :=
  uAdd_eq_some' (by simp [uKeepCur, uBackCond, T8_1_3_4_5_5_5_7_9] <;> norm_num) (by simp [uBack, uBackCond, T8_1_3_4_5_5_5_7_9] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, T8_1_3_4_5_5_5_7_9, T8_1_3_4_5_5_5_7_10] <;> norm_num)

#print axioms addEq_19_1_3_4_5_5_5_7

/-- Add 20 of the attesting chain: the entry at its pair is already tight (`uKeepCur` fires ground-true), so the table is unchanged. -/
theorem addEq_20_1_3_4_5_5_5_7 : uAdd T8_1_3_4_5_5_5_7_10 (5 : Fin 7) (2 : Fin 7) ((25 : ℚ) / (17 : ℚ)) true = some T8_1_3_4_5_5_5_7_10 :=
  by simp [uAdd, uKeepCur, uBackCond, uBack, uTighter, uProp, T8_1_3_4_5_5_5_7_10] <;> norm_num

#print axioms addEq_20_1_3_4_5_5_5_7

/-- Add 21 of the attesting chain: the entry at its pair is already tight (`uKeepCur` fires ground-true), so the table is unchanged. -/
theorem addEq_21_1_3_4_5_5_5_7 : uAdd T8_1_3_4_5_5_5_7_10 (5 : Fin 7) (6 : Fin 7) ((25 : ℚ) / (31 : ℚ)) true = some T8_1_3_4_5_5_5_7_10 :=
  by simp [uAdd, uKeepCur, uBackCond, uBack, uTighter, uProp, T8_1_3_4_5_5_5_7_10] <;> norm_num

#print axioms addEq_21_1_3_4_5_5_5_7

/-- Add 22 of the attesting chain: the entry at its pair is already tight (`uKeepCur` fires ground-true), so the table is unchanged. -/
theorem addEq_22_1_3_4_5_5_5_7 : uAdd T8_1_3_4_5_5_5_7_10 (6 : Fin 7) (5 : Fin 7) ((33 : ℚ) / (25 : ℚ)) true = some T8_1_3_4_5_5_5_7_10 :=
  by simp [uAdd, uKeepCur, uBackCond, uBack, uTighter, uProp, T8_1_3_4_5_5_5_7_10] <;> norm_num

#print axioms addEq_22_1_3_4_5_5_5_7

/-- Add 23 of the attesting chain: keep-cur and back are ground-false and the propagated result IS the next transcribed table (49 concrete pointwise checks). -/
theorem addEq_23_1_3_4_5_5_5_7 : uAdd T8_1_3_4_5_5_5_7_10 (6 : Fin 7) (1 : Fin 7) ((33 : ℚ) / (15 : ℚ)) true = some T8_1_3_4_5_5_5_7_11 :=
  uAdd_eq_some' (by simp [uKeepCur, uBackCond, T8_1_3_4_5_5_5_7_10] <;> norm_num) (by simp [uBack, uBackCond, T8_1_3_4_5_5_5_7_10] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, T8_1_3_4_5_5_5_7_10, T8_1_3_4_5_5_5_7_11] <;> norm_num)

#print axioms addEq_23_1_3_4_5_5_5_7

/-- Add 24 of the attesting chain: the entry at its pair is already tight (`uKeepCur` fires ground-true), so the table is unchanged. -/
theorem addEq_24_1_3_4_5_5_5_7 : uAdd T8_1_3_4_5_5_5_7_11 (1 : Fin 7) (6 : Fin 7) ((17 : ℚ) / (33 : ℚ)) true = some T8_1_3_4_5_5_5_7_11 :=
  by simp [uAdd, uKeepCur, uBackCond, uBack, uTighter, uProp, T8_1_3_4_5_5_5_7_11] <;> norm_num

#print axioms addEq_24_1_3_4_5_5_5_7

/-- Add 25 of the attesting chain: the entry at its pair is already tight (`uKeepCur` fires ground-true), so the table is unchanged. -/
theorem addEq_25_1_3_4_5_5_5_7 : uAdd T8_1_3_4_5_5_5_7_11 (1 : Fin 7) (3 : Fin 7) ((17 : ℚ) / (23 : ℚ)) true = some T8_1_3_4_5_5_5_7_11 :=
  by simp [uAdd, uKeepCur, uBackCond, uBack, uTighter, uProp, T8_1_3_4_5_5_5_7_11] <;> norm_num

#print axioms addEq_25_1_3_4_5_5_5_7

/-- Add 26 of the attesting chain: the entry at its pair is already tight (`uKeepCur` fires ground-true), so the table is unchanged. -/
theorem addEq_26_1_3_4_5_5_5_7 : uAdd T8_1_3_4_5_5_5_7_11 (3 : Fin 7) (1 : Fin 7) ((25 : ℚ) / (17 : ℚ)) true = some T8_1_3_4_5_5_5_7_11 :=
  by simp [uAdd, uKeepCur, uBackCond, uBack, uTighter, uProp, T8_1_3_4_5_5_5_7_11] <;> norm_num

#print axioms addEq_26_1_3_4_5_5_5_7

/-- Add 27 of the attesting chain: keep-cur and back are ground-false and the propagated result IS the next transcribed table (49 concrete pointwise checks). -/
theorem addEq_27_1_3_4_5_5_5_7 : uAdd T8_1_3_4_5_5_5_7_11 (3 : Fin 7) (6 : Fin 7) ((25 : ℚ) / (39 : ℚ)) true = some T8_1_3_4_5_5_5_7_12 :=
  uAdd_eq_some' (by simp [uKeepCur, uBackCond, T8_1_3_4_5_5_5_7_11] <;> norm_num) (by simp [uBack, uBackCond, T8_1_3_4_5_5_5_7_11] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, T8_1_3_4_5_5_5_7_11, T8_1_3_4_5_5_5_7_12] <;> norm_num)

#print axioms addEq_27_1_3_4_5_5_5_7

/-- Add 28 of the attesting chain: the entry at its pair is already tight (`uKeepCur` fires ground-true), so the table is unchanged. -/
theorem addEq_28_1_3_4_5_5_5_7 : uAdd T8_1_3_4_5_5_5_7_12 (6 : Fin 7) (3 : Fin 7) ((41 : ℚ) / (25 : ℚ)) true = some T8_1_3_4_5_5_5_7_12 :=
  by simp [uAdd, uKeepCur, uBackCond, uBack, uTighter, uProp, T8_1_3_4_5_5_5_7_12] <;> norm_num

#print axioms addEq_28_1_3_4_5_5_5_7

/-- Step 1 of the attesting chain: its two `uAdd`s on positive numerators compose to the step equation. -/
theorem stepEq_1_1_3_4_5_5_5_7 : uStep (mkOf (![1, 3, 4, 5, 5, 5, 7] : Fin 7 → ℤ)) (0 : Fin 7) (6 : Fin 7) (1 : ℚ) (7 : ℚ) (9 : ℚ) = some T8_1_3_4_5_5_5_7_1 :=
  uStep_eq_some' (by norm_num) (by norm_num) (by norm_num) addEq_1_1_3_4_5_5_5_7 addEq_2_1_3_4_5_5_5_7

#print axioms stepEq_1_1_3_4_5_5_5_7

/-- Step 2 of the attesting chain: its two `uAdd`s on positive numerators compose to the step equation. -/
theorem stepEq_2_1_3_4_5_5_5_7 : uStep T8_1_3_4_5_5_5_7_1 (6 : Fin 7) (5 : Fin 7) (9 : ℚ) (7 : ℚ) (9 : ℚ) = some T8_1_3_4_5_5_5_7_2 :=
  uStep_eq_some' (by norm_num) (by norm_num) (by norm_num) addEq_3_1_3_4_5_5_5_7 addEq_4_1_3_4_5_5_5_7

#print axioms stepEq_2_1_3_4_5_5_5_7

/-- Step 3 of the attesting chain: its two `uAdd`s on positive numerators compose to the step equation. -/
theorem stepEq_3_1_3_4_5_5_5_7 : uStep T8_1_3_4_5_5_5_7_2 (5 : Fin 7) (3 : Fin 7) (9 : ℚ) (7 : ℚ) (9 : ℚ) = some T8_1_3_4_5_5_5_7_2 :=
  uStep_eq_some' (by norm_num) (by norm_num) (by norm_num) addEq_5_1_3_4_5_5_5_7 addEq_6_1_3_4_5_5_5_7

#print axioms stepEq_3_1_3_4_5_5_5_7

/-- Step 4 of the attesting chain: its two `uAdd`s on positive numerators compose to the step equation. -/
theorem stepEq_4_1_3_4_5_5_5_7 : uStep T8_1_3_4_5_5_5_7_2 (3 : Fin 7) (2 : Fin 7) (9 : ℚ) (7 : ℚ) (9 : ℚ) = some T8_1_3_4_5_5_5_7_3 :=
  uStep_eq_some' (by norm_num) (by norm_num) (by norm_num) addEq_7_1_3_4_5_5_5_7 addEq_8_1_3_4_5_5_5_7

#print axioms stepEq_4_1_3_4_5_5_5_7

/-- Step 5 of the attesting chain: its two `uAdd`s on positive numerators compose to the step equation. -/
theorem stepEq_5_1_3_4_5_5_5_7 : uStep T8_1_3_4_5_5_5_7_3 (2 : Fin 7) (1 : Fin 7) (9 : ℚ) (7 : ℚ) (9 : ℚ) = some T8_1_3_4_5_5_5_7_4 :=
  uStep_eq_some' (by norm_num) (by norm_num) (by norm_num) addEq_9_1_3_4_5_5_5_7 addEq_10_1_3_4_5_5_5_7

#print axioms stepEq_5_1_3_4_5_5_5_7

/-- Step 6 of the attesting chain: its two `uAdd`s on positive numerators compose to the step equation. -/
theorem stepEq_6_1_3_4_5_5_5_7 : uStep T8_1_3_4_5_5_5_7_4 (1 : Fin 7) (5 : Fin 7) (9 : ℚ) (15 : ℚ) (17 : ℚ) = some T8_1_3_4_5_5_5_7_6 :=
  uStep_eq_some' (by norm_num) (by norm_num) (by norm_num) addEq_11_1_3_4_5_5_5_7 addEq_12_1_3_4_5_5_5_7

#print axioms stepEq_6_1_3_4_5_5_5_7

/-- Step 7 of the attesting chain: its two `uAdd`s on positive numerators compose to the step equation. -/
theorem stepEq_7_1_3_4_5_5_5_7 : uStep T8_1_3_4_5_5_5_7_6 (5 : Fin 7) (4 : Fin 7) (17 : ℚ) (15 : ℚ) (17 : ℚ) = some T8_1_3_4_5_5_5_7_7 :=
  uStep_eq_some' (by norm_num) (by norm_num) (by norm_num) addEq_13_1_3_4_5_5_5_7 addEq_14_1_3_4_5_5_5_7

#print axioms stepEq_7_1_3_4_5_5_5_7

/-- Step 8 of the attesting chain: its two `uAdd`s on positive numerators compose to the step equation. -/
theorem stepEq_8_1_3_4_5_5_5_7 : uStep T8_1_3_4_5_5_5_7_7 (4 : Fin 7) (3 : Fin 7) (17 : ℚ) (15 : ℚ) (17 : ℚ) = some T8_1_3_4_5_5_5_7_8 :=
  uStep_eq_some' (by norm_num) (by norm_num) (by norm_num) addEq_15_1_3_4_5_5_5_7 addEq_16_1_3_4_5_5_5_7

#print axioms stepEq_8_1_3_4_5_5_5_7

/-- Step 9 of the attesting chain: its two `uAdd`s on positive numerators compose to the step equation. -/
theorem stepEq_9_1_3_4_5_5_5_7 : uStep T8_1_3_4_5_5_5_7_8 (3 : Fin 7) (2 : Fin 7) (17 : ℚ) (15 : ℚ) (17 : ℚ) = some T8_1_3_4_5_5_5_7_9 :=
  uStep_eq_some' (by norm_num) (by norm_num) (by norm_num) addEq_17_1_3_4_5_5_5_7 addEq_18_1_3_4_5_5_5_7

#print axioms stepEq_9_1_3_4_5_5_5_7

/-- Step 10 of the attesting chain: its two `uAdd`s on positive numerators compose to the step equation. -/
theorem stepEq_10_1_3_4_5_5_5_7 : uStep T8_1_3_4_5_5_5_7_9 (2 : Fin 7) (5 : Fin 7) (17 : ℚ) (23 : ℚ) (25 : ℚ) = some T8_1_3_4_5_5_5_7_10 :=
  uStep_eq_some' (by norm_num) (by norm_num) (by norm_num) addEq_19_1_3_4_5_5_5_7 addEq_20_1_3_4_5_5_5_7

#print axioms stepEq_10_1_3_4_5_5_5_7

/-- Step 11 of the attesting chain: its two `uAdd`s on positive numerators compose to the step equation. -/
theorem stepEq_11_1_3_4_5_5_5_7 : uStep T8_1_3_4_5_5_5_7_10 (5 : Fin 7) (6 : Fin 7) (25 : ℚ) (31 : ℚ) (33 : ℚ) = some T8_1_3_4_5_5_5_7_10 :=
  uStep_eq_some' (by norm_num) (by norm_num) (by norm_num) addEq_21_1_3_4_5_5_5_7 addEq_22_1_3_4_5_5_5_7

#print axioms stepEq_11_1_3_4_5_5_5_7

/-- Step 12 of the attesting chain: its two `uAdd`s on positive numerators compose to the step equation. -/
theorem stepEq_12_1_3_4_5_5_5_7 : uStep T8_1_3_4_5_5_5_7_10 (6 : Fin 7) (1 : Fin 7) (33 : ℚ) (15 : ℚ) (17 : ℚ) = some T8_1_3_4_5_5_5_7_11 :=
  uStep_eq_some' (by norm_num) (by norm_num) (by norm_num) addEq_23_1_3_4_5_5_5_7 addEq_24_1_3_4_5_5_5_7

#print axioms stepEq_12_1_3_4_5_5_5_7

/-- Step 13 of the attesting chain: its two `uAdd`s on positive numerators compose to the step equation. -/
theorem stepEq_13_1_3_4_5_5_5_7 : uStep T8_1_3_4_5_5_5_7_11 (1 : Fin 7) (3 : Fin 7) (17 : ℚ) (23 : ℚ) (25 : ℚ) = some T8_1_3_4_5_5_5_7_11 :=
  uStep_eq_some' (by norm_num) (by norm_num) (by norm_num) addEq_25_1_3_4_5_5_5_7 addEq_26_1_3_4_5_5_5_7

#print axioms stepEq_13_1_3_4_5_5_5_7

/-- Step 14 of the attesting chain: its two `uAdd`s on positive numerators compose to the step equation. -/
theorem stepEq_14_1_3_4_5_5_5_7 : uStep T8_1_3_4_5_5_5_7_11 (3 : Fin 7) (6 : Fin 7) (25 : ℚ) (39 : ℚ) (41 : ℚ) = some T8_1_3_4_5_5_5_7_12 :=
  uStep_eq_some' (by norm_num) (by norm_num) (by norm_num) addEq_27_1_3_4_5_5_5_7 addEq_28_1_3_4_5_5_5_7

#print axioms stepEq_14_1_3_4_5_5_5_7

/-- The 14-step prefix run's trace table IS `T8_1_3_4_5_5_5_7_12` (peel the first 14 step equations; entries only tighten along a run). -/
theorem traceP_1_3_4_5_5_5_7_p14 {V : UTable} {af : Fin 7} {Af : ℚ}
    (hrun : chainRun (mkOf (![1, 3, 4, 5, 5, 5, 7] : Fin 7 → ℤ)) 0 1 steps8_1_3_4_5_5_5_7 = some (V, af, Af)) :
    V = T8_1_3_4_5_5_5_7_12 := by
  simp only [steps8_1_3_4_5_5_5_7,
    chainRun_step_some stepEq_1_1_3_4_5_5_5_7,
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
    chainRun_step_some stepEq_12_1_3_4_5_5_5_7,
    chainRun_step_some stepEq_13_1_3_4_5_5_5_7,
    chainRun_step_some stepEq_14_1_3_4_5_5_5_7,
    chainRun_nil, Option.some.injEq, Prod.mk.injEq] at hrun
  exact hrun.1.symm

#print axioms traceP_1_3_4_5_5_5_7_p14

/-- The per-record attestation: the 14-step prefix chain's closed-trace entry at
(0, 6) is 50/351, dominating the record's cap 1870/13113. -/
theorem attests_1_3_4_5_5_5_7_r0 : Attests8 (![1, 3, 4, 5, 5, 5, 7] : Fin 7 → ℤ) ⟨6, 0, 13, 3, [(6, (1870 / 13113 : ℝ))]⟩ steps8_1_3_4_5_5_5_7 :=
  by
  intro V af Af hrun
  have hV := traceP_1_3_4_5_5_5_7_p14 hrun
  rw [hV]
  exact capsDom_single ⟨(50 / 351 : ℚ), true, by simp [T8_1_3_4_5_5_5_7_12], by norm_num⟩

#print axioms attests_1_3_4_5_5_5_7_r0

/-- The per-record attestation: the 14-step prefix chain's closed-trace entry at
(1, 6) is 55/117, dominating the record's cap 55/117. -/
theorem attests_1_3_4_5_5_5_7_r1 : Attests8 (![1, 3, 4, 5, 5, 5, 7] : Fin 7 → ℤ) ⟨6, 1, 65, 31, [(6, (55 / 117 : ℝ))]⟩ steps8_1_3_4_5_5_5_7 :=
  by
  intro V af Af hrun
  have hV := traceP_1_3_4_5_5_5_7_p14 hrun
  rw [hV]
  exact capsDom_single ⟨(55 / 117 : ℚ), true, by simp [T8_1_3_4_5_5_5_7_12], by norm_num⟩

#print axioms attests_1_3_4_5_5_5_7_r1

/-- The per-record attestation: the 14-step prefix chain's closed-trace entry at
(1, 6) is 55/117, dominating the record's cap 55/117. -/
theorem attests_1_3_4_5_5_5_7_r2 : Attests8 (![1, 3, 4, 5, 5, 5, 7] : Fin 7 → ℤ) ⟨6, 1, 5, 3, [(6, (55 / 117 : ℝ))]⟩ steps8_1_3_4_5_5_5_7 :=
  by
  intro V af Af hrun
  have hV := traceP_1_3_4_5_5_5_7_p14 hrun
  rw [hV]
  exact capsDom_single ⟨(55 / 117 : ℚ), true, by simp [T8_1_3_4_5_5_5_7_12], by norm_num⟩

#print axioms attests_1_3_4_5_5_5_7_r2

/-- The per-record attestation: the 14-step prefix chain's closed-trace entry at
(1, 6) is 55/117, dominating the record's cap 55/117. -/
theorem attests_1_3_4_5_5_5_7_r3 : Attests8 (![1, 3, 4, 5, 5, 5, 7] : Fin 7 → ℤ) ⟨6, 1, 65, 47, [(6, (55 / 117 : ℝ))]⟩ steps8_1_3_4_5_5_5_7 :=
  by
  intro V af Af hrun
  have hV := traceP_1_3_4_5_5_5_7_p14 hrun
  rw [hV]
  exact capsDom_single ⟨(55 / 117 : ℚ), true, by simp [T8_1_3_4_5_5_5_7_12], by norm_num⟩

#print axioms attests_1_3_4_5_5_5_7_r3

/-- Per-record attestation for this box:
box (1, 3, 4, 5, 5, 5, 7)'s strict-class family carries the faithful per-record datum from the
transcribed full closure -- every record is attested by a nested prefix of the one
attesting chain (records sharing a pair share the witness). -/
theorem chainDomPerRecord8_1_3_4_5_5_5_7 :
    ChainDomPerRecord8 (![1, 3, 4, 5, 5, 5, 7] : Fin 7 → ℤ) dumpFam_1_3_4_5_5_5_7 := by
  intro e he
  simp only [dumpFam_1_3_4_5_5_5_7, List.mem_cons] at he
  rcases he with rfl | rfl | rfl | rfl | h0
  · exact ⟨steps8_1_3_4_5_5_5_7, attests_1_3_4_5_5_5_7_r0⟩
  · exact ⟨steps8_1_3_4_5_5_5_7, attests_1_3_4_5_5_5_7_r1⟩
  · exact ⟨steps8_1_3_4_5_5_5_7, attests_1_3_4_5_5_5_7_r2⟩
  · exact ⟨steps8_1_3_4_5_5_5_7, attests_1_3_4_5_5_5_7_r3⟩
  · exact absurd h0 (by simp)

#print axioms chainDomPerRecord8_1_3_4_5_5_5_7


end Fresh.ChainDomPerRec8
