import Fresh.ChainDomPerRecStart
import Fresh.ChainDomTrace19

namespace Fresh.ChainDomPerRec8

open Fresh.ChainDomBase Fresh.CapChainsOfCarve Fresh.JoinFamComposed Fresh.OneSidedComposed Fresh.OneSidedGlue
  Fresh.UClosure Fresh.SpineSound Fresh.FilterAssembly Fresh.DumpDomData

-- the 49-point `fin_cases` checks and the big literal tables need headroom
set_option maxHeartbeats 10000000

/- `mk`'s (the `uMk` fold's) output for box (1, 5, 5, 5, 6, 7, 8) is transcribed verbatim
(`perrec8_gen_v1.py`, value-verbatim mirror of `Fresh.UClosureKill`'s `uKeepCur`/
`uBack`/`uProp`/`uAdd`; 49 entries -- the FULL closure is dense) as `mkTab_1_5_5_5_6_7_8`
(section 2).  Census cross-check: at every census pair the transcription agrees with
the banked `Fresh.DumpDomData` `u0e_1_5_5_5_6_7_8_*` facts (`mkU0_1_5_5_5_6_7_8_*` below). -/

/-- `mk`'s entry at (0, 6) for box (1, 5, 5, 5, 6, 7, 8): exact census datum (cross-checked
against the banked `Fresh.DumpDomData.u0e_1_5_5_5_6_7_8_0_6`). -/
theorem mke_1_5_5_5_6_7_8_0_6 : mkOf (![1, 5, 5, 5, 6, 7, 8] : Fin 7 → ℤ) (0 : Fin 7) (6 : Fin 7) = some ((2 / 15 : ℚ), false) :=
  by simp [mkOf, mkTab_1_5_5_5_6_7_8]

#print axioms mke_1_5_5_5_6_7_8_0_6

/-- The closure transcription agrees with the sparse census transcription at (0, 6). -/
theorem mkU0_1_5_5_5_6_7_8_0_6 : mkOf (![1, 5, 5, 5, 6, 7, 8] : Fin 7 → ℤ) (0 : Fin 7) (6 : Fin 7) = u0Of (![1, 5, 5, 5, 6, 7, 8] : Fin 7 → ℤ) (0 : Fin 7) (6 : Fin 7) :=
  by rw [mke_1_5_5_5_6_7_8_0_6, u0e_1_5_5_5_6_7_8_0_6]

#print axioms mkU0_1_5_5_5_6_7_8_0_6

/-- `mk`'s entry at (1, 6) for box (1, 5, 5, 5, 6, 7, 8): exact census datum (cross-checked
against the banked `Fresh.DumpDomData.u0e_1_5_5_5_6_7_8_1_6`). -/
theorem mke_1_5_5_5_6_7_8_1_6 : mkOf (![1, 5, 5, 5, 6, 7, 8] : Fin 7 → ℤ) (1 : Fin 7) (6 : Fin 7) = some ((11 / 15 : ℚ), true) :=
  by simp [mkOf, mkTab_1_5_5_5_6_7_8]

#print axioms mke_1_5_5_5_6_7_8_1_6

/-- The closure transcription agrees with the sparse census transcription at (1, 6). -/
theorem mkU0_1_5_5_5_6_7_8_1_6 : mkOf (![1, 5, 5, 5, 6, 7, 8] : Fin 7 → ℤ) (1 : Fin 7) (6 : Fin 7) = u0Of (![1, 5, 5, 5, 6, 7, 8] : Fin 7 → ℤ) (1 : Fin 7) (6 : Fin 7) :=
  by rw [mke_1_5_5_5_6_7_8_1_6, u0e_1_5_5_5_6_7_8_1_6]

#print axioms mkU0_1_5_5_5_6_7_8_1_6

/-- The EMPTY-chain non-vacuity for box (1, 5, 5, 5, 6, 7, 8): every strict witness's cap is
strictly TIGHTER than the closure entry at its pair, so `CapsDom (mkOf (![1, 5, 5, 5, 6, 7, 8] : Fin 7 → ℤ)) ...`
is refuted on every record -- a witness of the existential must be a genuine
dominating run (mirror of `Fresh.DumpDomData.not_capsDomU0all_*`). -/
theorem not_capsDomMk8all_1_5_5_5_6_7_8 :
    ∀ e ∈ dumpFam_1_5_5_5_6_7_8.edges,
      ¬ CapsDom (mkOf (![1, 5, 5, 5, 6, 7, 8] : Fin 7 → ℤ)) e.y e.caps e.x := by
  intro e he
  simp only [dumpFam_1_5_5_5_6_7_8, List.mem_cons] at he
  rcases he with rfl | rfl | rfl | rfl | h0
  · exact not_capsDomU0_of_entry_lt (mke_1_5_5_5_6_7_8_0_6) (by norm_num)
  · exact not_capsDomU0_of_entry_lt (mke_1_5_5_5_6_7_8_1_6) (by norm_num)
  · exact not_capsDomU0_of_entry_lt (mke_1_5_5_5_6_7_8_1_6) (by norm_num)
  · exact not_capsDomU0_of_entry_lt (mke_1_5_5_5_6_7_8_1_6) (by norm_num)
  · exact absurd h0 (by simp)

#print axioms not_capsDomMk8all_1_5_5_5_6_7_8

/-- The attesting-chain PREFIX for box (1, 5, 5, 5, 6, 7, 8): the first 19 steps of enumerated chain
index 0 of the box's dump enumeration (full word length 22; chain index and count
re-verified against the dump's `chains_enumerated` = 312 by `perrec8_gen_v1.py`).  Entries
only tighten along a run, so the prefix run's closed trace already carries the
dominating entries at every record pair ((0,6) first dominated at step 19, (1,6) first dominated at step 19). -/
def steps8_1_5_5_5_6_7_8 : List Step := [
  ⟨(5 : Fin 7), (7 : ℚ), (9 : ℚ)⟩, ⟨(3 : Fin 7), (7 : ℚ), (9 : ℚ)⟩, ⟨(1 : Fin 7), (7 : ℚ), (9 : ℚ)⟩, ⟨(6 : Fin 7), (15 : ℚ), (17 : ℚ)⟩, ⟨(5 : Fin 7), (15 : ℚ), (17 : ℚ)⟩, ⟨(4 : Fin 7), (15 : ℚ), (17 : ℚ)⟩, ⟨(3 : Fin 7), (15 : ℚ), (17 : ℚ)⟩, ⟨(2 : Fin 7), (15 : ℚ), (17 : ℚ)⟩, ⟨(1 : Fin 7), (15 : ℚ), (17 : ℚ)⟩, ⟨(4 : Fin 7), (23 : ℚ), (25 : ℚ)⟩, ⟨(6 : Fin 7), (31 : ℚ), (33 : ℚ)⟩, ⟨(3 : Fin 7), (23 : ℚ), (25 : ℚ)⟩, ⟨(5 : Fin 7), (31 : ℚ), (33 : ℚ)⟩, ⟨(2 : Fin 7), (23 : ℚ), (25 : ℚ)⟩, ⟨(4 : Fin 7), (31 : ℚ), (33 : ℚ)⟩, ⟨(1 : Fin 7), (23 : ℚ), (25 : ℚ)⟩, ⟨(5 : Fin 7), (39 : ℚ), (41 : ℚ)⟩, ⟨(3 : Fin 7), (31 : ℚ), (33 : ℚ)⟩, ⟨(6 : Fin 7), (47 : ℚ), (49 : ℚ)⟩
]

/-- transcribed trace table: T8_1_5_5_5_6_7_8_1 (the mirror run's add-end snapshot). -/
def T8_1_5_5_5_6_7_8_1 : UTable := fun p q =>
  if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((2 / 9 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((2 / 9 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((2 / 9 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((2 / 11 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 / 7 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((2 / 15 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((11 / 2 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((11 / 14 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((11 / 15 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((11 / 2 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((11 / 9 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((11 / 14 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((11 / 15 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((11 / 2 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((11 / 9 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((11 / 9 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((11 / 14 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((11 / 15 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((13 / 2 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((13 / 9 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((13 / 9 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((13 / 9 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((13 / 14 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((13 / 15 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((15 / 2 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((5 / 3 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((5 / 3 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((5 / 3 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((15 / 11 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((17 / 2 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((17 / 9 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((17 / 9 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((17 / 9 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 11 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((17 / 14 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

/-- transcribed trace table: T8_1_5_5_5_6_7_8_2 (the mirror run's add-end snapshot). -/
def T8_1_5_5_5_6_7_8_2 : UTable := fun p q =>
  if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((2 / 9 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((2 / 9 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((9 / 49 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((2 / 11 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 / 7 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((2 / 15 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((11 / 2 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((11 / 14 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((11 / 15 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((11 / 2 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((11 / 9 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((11 / 14 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((11 / 15 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((11 / 2 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((11 / 9 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((11 / 9 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((11 / 14 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((11 / 15 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((13 / 2 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((13 / 9 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((13 / 9 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((117 / 98 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((13 / 14 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((13 / 15 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((99 / 14 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((11 / 7 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((11 / 7 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((9 / 7 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((9 / 7 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((33 / 35 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((17 / 2 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((17 / 9 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((17 / 9 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((153 / 98 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 11 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((17 / 14 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

/-- transcribed trace table: T8_1_5_5_5_6_7_8_3 (the mirror run's add-end snapshot). -/
def T8_1_5_5_5_6_7_8_3 : UTable := fun p q =>
  if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((2 / 9 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((2 / 9 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((9 / 49 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((2 / 11 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 / 7 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((2 / 15 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((51 / 10 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((459 / 490 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((51 / 55 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((51 / 70 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((3 / 5 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((11 / 2 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((11 / 9 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((11 / 14 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((11 / 15 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((11 / 2 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((11 / 9 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((11 / 9 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((11 / 14 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((11 / 15 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((13 / 2 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((13 / 9 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((13 / 9 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((117 / 98 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((13 / 14 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((13 / 15 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((99 / 14 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((11 / 7 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((11 / 7 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((9 / 7 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((9 / 7 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((33 / 35 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((17 / 2 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((17 / 9 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((17 / 9 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((153 / 98 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 11 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((17 / 14 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

/-- transcribed trace table: T8_1_5_5_5_6_7_8_4 (the mirror run's add-end snapshot). -/
def T8_1_5_5_5_6_7_8_4 : UTable := fun p q =>
  if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((2 / 9 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((2 / 9 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((9 / 49 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((2 / 11 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 / 7 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((2 / 15 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((51 / 10 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((459 / 490 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((51 / 55 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((51 / 70 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((3 / 5 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((11 / 2 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((11 / 9 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((11 / 14 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((11 / 15 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((11 / 2 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((11 / 9 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((11 / 9 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((11 / 14 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((11 / 15 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((13 / 2 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((13 / 9 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((13 / 9 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((117 / 98 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((13 / 14 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((13 / 15 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((99 / 14 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((11 / 7 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((11 / 7 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((9 / 7 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((9 / 7 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((33 / 35 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((17 / 2 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((17 / 9 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((17 / 9 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((153 / 98 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 11 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((17 / 14 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

/-- transcribed trace table: T8_1_5_5_5_6_7_8_5 (the mirror run's add-end snapshot). -/
def T8_1_5_5_5_6_7_8_5 : UTable := fun p q =>
  if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((2 / 9 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((2 / 9 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((9 / 49 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((2 / 11 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 / 7 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((2 / 15 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((1683 / 350 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((153 / 175 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((153 / 175 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((17 / 25 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((3 / 5 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((11 / 2 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((11 / 9 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((11 / 14 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((11 / 15 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((11 / 2 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((11 / 9 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((11 / 9 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((11 / 14 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((11 / 15 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((13 / 2 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((13 / 9 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((13 / 9 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((117 / 98 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((13 / 14 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((13 / 15 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((99 / 14 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((11 / 7 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((11 / 7 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((9 / 7 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((9 / 7 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((33 / 35 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((561 / 70 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((187 / 105 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((187 / 105 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((51 / 35 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((51 / 35 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((17 / 15 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

/-- transcribed trace table: T8_1_5_5_5_6_7_8_6 (the mirror run's add-end snapshot). -/
def T8_1_5_5_5_6_7_8_6 : UTable := fun p q =>
  if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((2 / 9 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((2 / 9 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((9 / 49 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 105 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 / 7 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((2 / 15 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((1683 / 350 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((153 / 175 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((289 / 375 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((17 / 25 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((3 / 5 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((11 / 2 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((11 / 9 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((187 / 210 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((11 / 14 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((11 / 15 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((11 / 2 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((11 / 9 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((11 / 9 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((187 / 210 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((11 / 14 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((11 / 15 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((13 / 2 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((13 / 9 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((13 / 9 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((117 / 98 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((13 / 14 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((13 / 15 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((99 / 14 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((11 / 7 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((11 / 7 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((9 / 7 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 15 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((33 / 35 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((561 / 70 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((187 / 105 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((187 / 105 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((51 / 35 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((289 / 225 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((17 / 15 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

/-- transcribed trace table: T8_1_5_5_5_6_7_8_7 (the mirror run's add-end snapshot). -/
def T8_1_5_5_5_6_7_8_7 : UTable := fun p q =>
  if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((2 / 9 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((2 / 9 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((289 / 1575 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 105 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 / 7 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((2 / 15 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((54043 / 11250 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((4913 / 5625 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((289 / 375 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((17 / 25 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((3 / 5 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((11 / 2 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((11 / 9 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((187 / 210 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((11 / 14 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((11 / 15 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((11 / 2 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((11 / 9 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((11 / 9 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((187 / 210 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((11 / 14 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((11 / 15 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((187 / 30 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((187 / 135 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((187 / 135 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((17 / 15 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((187 / 210 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((187 / 225 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((3179 / 450 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((3179 / 2025 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((3179 / 2025 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((289 / 225 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 15 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((3179 / 3375 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((54043 / 6750 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((54043 / 30375 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((54043 / 30375 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((4913 / 3375 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((289 / 225 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((17 / 15 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

/-- transcribed trace table: T8_1_5_5_5_6_7_8_8 (the mirror run's add-end snapshot). -/
def T8_1_5_5_5_6_7_8_8 : UTable := fun p q =>
  if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((2 / 9 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((4913 / 23625 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((289 / 1575 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 105 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 / 7 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((2 / 15 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((54043 / 11250 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((83521 / 84375 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((4913 / 5625 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((289 / 375 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((17 / 25 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((3 / 5 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((11 / 2 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((11 / 9 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((187 / 210 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((11 / 14 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((11 / 15 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((11 / 2 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((11 / 9 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((17 / 15 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((187 / 210 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((11 / 14 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((11 / 15 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((187 / 30 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((187 / 135 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((289 / 225 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((17 / 15 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((187 / 210 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((187 / 225 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((3179 / 450 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((3179 / 2025 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((4913 / 3375 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((289 / 225 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 15 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((3179 / 3375 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((54043 / 6750 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((54043 / 30375 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((83521 / 50625 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((4913 / 3375 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((289 / 225 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((17 / 15 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

/-- transcribed trace table: T8_1_5_5_5_6_7_8_9 (the mirror run's add-end snapshot). -/
def T8_1_5_5_5_6_7_8_9 : UTable := fun p q =>
  if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((2 / 9 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((4913 / 23625 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((289 / 1575 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 105 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 / 7 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((2 / 15 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((54043 / 11250 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((83521 / 84375 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((4913 / 5625 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((289 / 375 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((17 / 25 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((3 / 5 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((918731 / 168750 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((17 / 15 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((83521 / 84375 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((4913 / 5625 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((289 / 375 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((17 / 25 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((11 / 2 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((11 / 9 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((17 / 15 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((187 / 210 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((11 / 14 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((11 / 15 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((187 / 30 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((187 / 135 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((289 / 225 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((17 / 15 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((187 / 210 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((187 / 225 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((3179 / 450 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((3179 / 2025 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((4913 / 3375 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((289 / 225 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 15 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((3179 / 3375 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((54043 / 6750 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((54043 / 30375 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((83521 / 50625 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((4913 / 3375 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((289 / 225 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((17 / 15 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

/-- transcribed trace table: T8_1_5_5_5_6_7_8_10 (the mirror run's add-end snapshot). -/
def T8_1_5_5_5_6_7_8_10 : UTable := fun p q =>
  if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((2 / 9 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((4913 / 23625 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((289 / 1575 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 105 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 / 7 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((2 / 15 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((3179 / 690 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((4913 / 5175 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((289 / 345 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 23 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((3179 / 4830 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((3 / 5 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((54043 / 10350 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((17 / 15 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((4913 / 5175 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((289 / 345 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((54043 / 72450 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((17 / 25 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((11 / 2 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((11 / 9 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((17 / 15 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((187 / 210 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((11 / 14 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((11 / 15 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((187 / 30 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((187 / 135 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((289 / 225 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((17 / 15 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((187 / 210 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((187 / 225 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((3179 / 450 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((3179 / 2025 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((4913 / 3375 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((289 / 225 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 15 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((3179 / 3375 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((54043 / 6750 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((54043 / 30375 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((83521 / 50625 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((4913 / 3375 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((289 / 225 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((17 / 15 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

/-- transcribed trace table: T8_1_5_5_5_6_7_8_11 (the mirror run's add-end snapshot). -/
def T8_1_5_5_5_6_7_8_11 : UTable := fun p q =>
  if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((2 / 9 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((4913 / 23625 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((289 / 1575 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 105 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 / 7 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((85 / 651 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((3179 / 690 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((4913 / 5175 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((289 / 345 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 23 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((3179 / 4830 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((425 / 713 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((54043 / 10350 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((17 / 15 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((4913 / 5175 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((289 / 345 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((54043 / 72450 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((1445 / 2139 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((11 / 2 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((11 / 9 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((17 / 15 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((187 / 210 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((11 / 14 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((935 / 1302 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((187 / 30 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((187 / 135 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((289 / 225 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((17 / 15 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((187 / 210 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((25 / 31 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((3179 / 450 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((3179 / 2025 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((4913 / 3375 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((289 / 225 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 15 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((85 / 93 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((54043 / 6750 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((54043 / 30375 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((83521 / 50625 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((4913 / 3375 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((289 / 225 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((17 / 15 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

/-- transcribed trace table: T8_1_5_5_5_6_7_8_12 (the mirror run's add-end snapshot). -/
def T8_1_5_5_5_6_7_8_12 : UTable := fun p q =>
  if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((2 / 9 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((4913 / 23625 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((289 / 1575 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 105 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 / 7 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((85 / 651 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((3179 / 690 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((4913 / 5175 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((289 / 345 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 23 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((3179 / 4830 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((425 / 713 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((54043 / 10350 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((17 / 15 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((4913 / 5175 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((289 / 345 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((54043 / 72450 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((1445 / 2139 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((11 / 2 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((11 / 9 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((17 / 15 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((187 / 210 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((11 / 14 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((935 / 1302 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((187 / 30 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((187 / 135 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((289 / 225 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((17 / 15 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((187 / 210 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((25 / 31 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((3179 / 450 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((3179 / 2025 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((4913 / 3375 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((289 / 225 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 15 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((85 / 93 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((363 / 46 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((121 / 69 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((187 / 115 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((33 / 23 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((2057 / 1610 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((363 / 322 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

/-- transcribed trace table: T8_1_5_5_5_6_7_8_13 (the mirror run's add-end snapshot). -/
def T8_1_5_5_5_6_7_8_13 : UTable := fun p q =>
  if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((2 / 9 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((33 / 161 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((289 / 1575 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 105 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 / 7 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((85 / 651 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((3179 / 690 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((34969 / 37030 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((289 / 345 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 23 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((3179 / 4830 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((425 / 713 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((54043 / 10350 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((17 / 15 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((4913 / 5175 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((289 / 345 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((54043 / 72450 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((1445 / 2139 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((11 / 2 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((11 / 9 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((363 / 322 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((187 / 210 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((11 / 14 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((935 / 1302 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((187 / 30 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((187 / 135 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((2057 / 1610 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((17 / 15 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((187 / 210 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((25 / 31 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((3179 / 450 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((3179 / 2025 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((33 / 23 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((289 / 225 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 15 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((85 / 93 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((363 / 46 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((121 / 69 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((11979 / 7406 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((33 / 23 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((2057 / 1610 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((363 / 322 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

/-- transcribed trace table: T8_1_5_5_5_6_7_8_14 (the mirror run's add-end snapshot). -/
def T8_1_5_5_5_6_7_8_14 : UTable := fun p q =>
  if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((2 / 9 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((33 / 161 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((289 / 1575 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 105 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 / 7 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((85 / 651 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((3179 / 690 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((34969 / 37030 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((289 / 345 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 23 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((3179 / 4830 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((425 / 713 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((935 / 186 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((935 / 837 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((85 / 93 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((25 / 31 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((935 / 1302 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((625 / 961 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((11 / 2 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((11 / 9 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((363 / 322 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((187 / 210 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((11 / 14 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((935 / 1302 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((187 / 30 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((187 / 135 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((2057 / 1610 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((17 / 15 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((187 / 210 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((25 / 31 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((3179 / 450 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((3179 / 2025 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((33 / 23 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((289 / 225 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 15 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((85 / 93 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((363 / 46 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((121 / 69 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((11979 / 7406 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((33 / 23 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((2057 / 1610 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((363 / 322 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

/-- transcribed trace table: T8_1_5_5_5_6_7_8_15 (the mirror run's add-end snapshot). -/
def T8_1_5_5_5_6_7_8_15 : UTable := fun p q =>
  if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((2 / 9 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((550 / 2691 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((578 / 3159 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((170 / 1053 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((50 / 351 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((4250 / 32643 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((3179 / 702 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((275 / 299 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((289 / 351 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((85 / 117 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((25 / 39 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((2125 / 3627 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((935 / 186 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((935 / 837 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((85 / 93 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((25 / 31 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((23375 / 32643 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((625 / 961 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((11 / 2 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((11 / 9 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((3025 / 2691 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((935 / 1053 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((275 / 351 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((23375 / 32643 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((187 / 30 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((187 / 135 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((10285 / 8073 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((17 / 15 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((935 / 1053 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((25 / 31 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((3179 / 450 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((3179 / 2025 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((33 / 23 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((289 / 225 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 15 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((85 / 93 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((363 / 46 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((121 / 69 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((33275 / 20631 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((33 / 23 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((10285 / 8073 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((3025 / 2691 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

/-- transcribed trace table: T8_1_5_5_5_6_7_8_16 (the mirror run's add-end snapshot). -/
def T8_1_5_5_5_6_7_8_16 : UTable := fun p q =>
  if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((2 / 9 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((550 / 2691 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((578 / 3159 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((170 / 1053 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((50 / 351 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((6358 / 49491 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((3179 / 702 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((275 / 299 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((289 / 351 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((85 / 117 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((25 / 39 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((3179 / 5499 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((935 / 186 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((935 / 837 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((85 / 93 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((25 / 31 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((23375 / 32643 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((935 / 1457 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((11 / 2 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((11 / 9 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((3025 / 2691 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((935 / 1053 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((275 / 351 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((33 / 47 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((187 / 30 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((187 / 135 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((10285 / 8073 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((17 / 15 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((935 / 1053 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((187 / 235 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((3179 / 450 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((3179 / 2025 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((33 / 23 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((289 / 225 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 15 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((3179 / 3525 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((363 / 46 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((121 / 69 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((33275 / 20631 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((33 / 23 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((10285 / 8073 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((3025 / 2691 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

/-- Add 1 of the attesting chain: keep-cur and back are ground-false and the propagated result IS the next transcribed table (49 concrete pointwise checks). -/
theorem addEq_1_1_5_5_5_6_7_8 : uAdd (mkOf (![1, 5, 5, 5, 6, 7, 8] : Fin 7 → ℤ)) (0 : Fin 7) (5 : Fin 7) ((1 : ℚ) / (7 : ℚ)) true = some T8_1_5_5_5_6_7_8_1 :=
  uAdd_eq_some' (by simp [uKeepCur, uBackCond, mkOf, mkTab_1_5_5_5_6_7_8] <;> norm_num) (by simp [uBack, uBackCond, mkOf, mkTab_1_5_5_5_6_7_8] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, mkOf, mkTab_1_5_5_5_6_7_8, T8_1_5_5_5_6_7_8_1] <;> norm_num)

#print axioms addEq_1_1_5_5_5_6_7_8

/-- Add 2 of the attesting chain: the entry at its pair is already tight (`uKeepCur` fires ground-true), so the table is unchanged. -/
theorem addEq_2_1_5_5_5_6_7_8 : uAdd T8_1_5_5_5_6_7_8_1 (5 : Fin 7) (0 : Fin 7) ((9 : ℚ) / (1 : ℚ)) true = some T8_1_5_5_5_6_7_8_1 :=
  by simp [uAdd, uKeepCur, uBackCond, uBack, uTighter, uProp, T8_1_5_5_5_6_7_8_1] <;> norm_num

#print axioms addEq_2_1_5_5_5_6_7_8

/-- Add 3 of the attesting chain: keep-cur and back are ground-false and the propagated result IS the next transcribed table (49 concrete pointwise checks). -/
theorem addEq_3_1_5_5_5_6_7_8 : uAdd T8_1_5_5_5_6_7_8_1 (5 : Fin 7) (3 : Fin 7) ((9 : ℚ) / (7 : ℚ)) true = some T8_1_5_5_5_6_7_8_2 :=
  uAdd_eq_some' (by simp [uKeepCur, uBackCond, T8_1_5_5_5_6_7_8_1] <;> norm_num) (by simp [uBack, uBackCond, T8_1_5_5_5_6_7_8_1] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, T8_1_5_5_5_6_7_8_1, T8_1_5_5_5_6_7_8_2] <;> norm_num)

#print axioms addEq_3_1_5_5_5_6_7_8

/-- Add 4 of the attesting chain: the entry at its pair is already tight (`uKeepCur` fires ground-true), so the table is unchanged. -/
theorem addEq_4_1_5_5_5_6_7_8 : uAdd T8_1_5_5_5_6_7_8_2 (3 : Fin 7) (5 : Fin 7) ((9 : ℚ) / (9 : ℚ)) true = some T8_1_5_5_5_6_7_8_2 :=
  by simp [uAdd, uKeepCur, uBackCond, uBack, uTighter, uProp, T8_1_5_5_5_6_7_8_2] <;> norm_num

#print axioms addEq_4_1_5_5_5_6_7_8

/-- Add 5 of the attesting chain: the entry at its pair is already tight (`uKeepCur` fires ground-true), so the table is unchanged. -/
theorem addEq_5_1_5_5_5_6_7_8 : uAdd T8_1_5_5_5_6_7_8_2 (3 : Fin 7) (1 : Fin 7) ((9 : ℚ) / (7 : ℚ)) true = some T8_1_5_5_5_6_7_8_2 :=
  by simp [uAdd, uKeepCur, uBackCond, uBack, uTighter, uProp, T8_1_5_5_5_6_7_8_2] <;> norm_num

#print axioms addEq_5_1_5_5_5_6_7_8

/-- Add 6 of the attesting chain: the entry at its pair is already tight (`uKeepCur` fires ground-true), so the table is unchanged. -/
theorem addEq_6_1_5_5_5_6_7_8 : uAdd T8_1_5_5_5_6_7_8_2 (1 : Fin 7) (3 : Fin 7) ((9 : ℚ) / (9 : ℚ)) true = some T8_1_5_5_5_6_7_8_2 :=
  by simp [uAdd, uKeepCur, uBackCond, uBack, uTighter, uProp, T8_1_5_5_5_6_7_8_2] <;> norm_num

#print axioms addEq_6_1_5_5_5_6_7_8

/-- Add 7 of the attesting chain: keep-cur and back are ground-false and the propagated result IS the next transcribed table (49 concrete pointwise checks). -/
theorem addEq_7_1_5_5_5_6_7_8 : uAdd T8_1_5_5_5_6_7_8_2 (1 : Fin 7) (6 : Fin 7) ((9 : ℚ) / (15 : ℚ)) true = some T8_1_5_5_5_6_7_8_3 :=
  uAdd_eq_some' (by simp [uKeepCur, uBackCond, T8_1_5_5_5_6_7_8_2] <;> norm_num) (by simp [uBack, uBackCond, T8_1_5_5_5_6_7_8_2] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, T8_1_5_5_5_6_7_8_2, T8_1_5_5_5_6_7_8_3] <;> norm_num)

#print axioms addEq_7_1_5_5_5_6_7_8

/-- Add 8 of the attesting chain: keep-cur and back are ground-false and the propagated result IS the next transcribed table (49 concrete pointwise checks). -/
theorem addEq_8_1_5_5_5_6_7_8 : uAdd T8_1_5_5_5_6_7_8_3 (6 : Fin 7) (1 : Fin 7) ((17 : ℚ) / (9 : ℚ)) true = some T8_1_5_5_5_6_7_8_4 :=
  uAdd_eq_some' (by simp [uKeepCur, uBackCond, T8_1_5_5_5_6_7_8_3] <;> norm_num) (by simp [uBack, uBackCond, T8_1_5_5_5_6_7_8_3] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, T8_1_5_5_5_6_7_8_3, T8_1_5_5_5_6_7_8_4] <;> norm_num)

#print axioms addEq_8_1_5_5_5_6_7_8

/-- Add 9 of the attesting chain: keep-cur and back are ground-false and the propagated result IS the next transcribed table (49 concrete pointwise checks). -/
theorem addEq_9_1_5_5_5_6_7_8 : uAdd T8_1_5_5_5_6_7_8_4 (6 : Fin 7) (5 : Fin 7) ((17 : ℚ) / (15 : ℚ)) true = some T8_1_5_5_5_6_7_8_5 :=
  uAdd_eq_some' (by simp [uKeepCur, uBackCond, T8_1_5_5_5_6_7_8_4] <;> norm_num) (by simp [uBack, uBackCond, T8_1_5_5_5_6_7_8_4] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, T8_1_5_5_5_6_7_8_4, T8_1_5_5_5_6_7_8_5] <;> norm_num)

#print axioms addEq_9_1_5_5_5_6_7_8

/-- Add 10 of the attesting chain: the entry at its pair is already tight (`uKeepCur` fires ground-true), so the table is unchanged. -/
theorem addEq_10_1_5_5_5_6_7_8 : uAdd T8_1_5_5_5_6_7_8_5 (5 : Fin 7) (6 : Fin 7) ((17 : ℚ) / (17 : ℚ)) true = some T8_1_5_5_5_6_7_8_5 :=
  by simp [uAdd, uKeepCur, uBackCond, uBack, uTighter, uProp, T8_1_5_5_5_6_7_8_5] <;> norm_num

#print axioms addEq_10_1_5_5_5_6_7_8

/-- Add 11 of the attesting chain: keep-cur and back are ground-false and the propagated result IS the next transcribed table (49 concrete pointwise checks). -/
theorem addEq_11_1_5_5_5_6_7_8 : uAdd T8_1_5_5_5_6_7_8_5 (5 : Fin 7) (4 : Fin 7) ((17 : ℚ) / (15 : ℚ)) true = some T8_1_5_5_5_6_7_8_6 :=
  uAdd_eq_some' (by simp [uKeepCur, uBackCond, T8_1_5_5_5_6_7_8_5] <;> norm_num) (by simp [uBack, uBackCond, T8_1_5_5_5_6_7_8_5] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, T8_1_5_5_5_6_7_8_5, T8_1_5_5_5_6_7_8_6] <;> norm_num)

#print axioms addEq_11_1_5_5_5_6_7_8

/-- Add 12 of the attesting chain: the entry at its pair is already tight (`uKeepCur` fires ground-true), so the table is unchanged. -/
theorem addEq_12_1_5_5_5_6_7_8 : uAdd T8_1_5_5_5_6_7_8_6 (4 : Fin 7) (5 : Fin 7) ((17 : ℚ) / (17 : ℚ)) true = some T8_1_5_5_5_6_7_8_6 :=
  by simp [uAdd, uKeepCur, uBackCond, uBack, uTighter, uProp, T8_1_5_5_5_6_7_8_6] <;> norm_num

#print axioms addEq_12_1_5_5_5_6_7_8

/-- Add 13 of the attesting chain: keep-cur and back are ground-false and the propagated result IS the next transcribed table (49 concrete pointwise checks). -/
theorem addEq_13_1_5_5_5_6_7_8 : uAdd T8_1_5_5_5_6_7_8_6 (4 : Fin 7) (3 : Fin 7) ((17 : ℚ) / (15 : ℚ)) true = some T8_1_5_5_5_6_7_8_7 :=
  uAdd_eq_some' (by simp [uKeepCur, uBackCond, T8_1_5_5_5_6_7_8_6] <;> norm_num) (by simp [uBack, uBackCond, T8_1_5_5_5_6_7_8_6] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, T8_1_5_5_5_6_7_8_6, T8_1_5_5_5_6_7_8_7] <;> norm_num)

#print axioms addEq_13_1_5_5_5_6_7_8

/-- Add 14 of the attesting chain: the entry at its pair is already tight (`uKeepCur` fires ground-true), so the table is unchanged. -/
theorem addEq_14_1_5_5_5_6_7_8 : uAdd T8_1_5_5_5_6_7_8_7 (3 : Fin 7) (4 : Fin 7) ((17 : ℚ) / (17 : ℚ)) true = some T8_1_5_5_5_6_7_8_7 :=
  by simp [uAdd, uKeepCur, uBackCond, uBack, uTighter, uProp, T8_1_5_5_5_6_7_8_7] <;> norm_num

#print axioms addEq_14_1_5_5_5_6_7_8

/-- Add 15 of the attesting chain: keep-cur and back are ground-false and the propagated result IS the next transcribed table (49 concrete pointwise checks). -/
theorem addEq_15_1_5_5_5_6_7_8 : uAdd T8_1_5_5_5_6_7_8_7 (3 : Fin 7) (2 : Fin 7) ((17 : ℚ) / (15 : ℚ)) true = some T8_1_5_5_5_6_7_8_8 :=
  uAdd_eq_some' (by simp [uKeepCur, uBackCond, T8_1_5_5_5_6_7_8_7] <;> norm_num) (by simp [uBack, uBackCond, T8_1_5_5_5_6_7_8_7] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, T8_1_5_5_5_6_7_8_7, T8_1_5_5_5_6_7_8_8] <;> norm_num)

#print axioms addEq_15_1_5_5_5_6_7_8

/-- Add 16 of the attesting chain: the entry at its pair is already tight (`uKeepCur` fires ground-true), so the table is unchanged. -/
theorem addEq_16_1_5_5_5_6_7_8 : uAdd T8_1_5_5_5_6_7_8_8 (2 : Fin 7) (3 : Fin 7) ((17 : ℚ) / (17 : ℚ)) true = some T8_1_5_5_5_6_7_8_8 :=
  by simp [uAdd, uKeepCur, uBackCond, uBack, uTighter, uProp, T8_1_5_5_5_6_7_8_8] <;> norm_num

#print axioms addEq_16_1_5_5_5_6_7_8

/-- Add 17 of the attesting chain: keep-cur and back are ground-false and the propagated result IS the next transcribed table (49 concrete pointwise checks). -/
theorem addEq_17_1_5_5_5_6_7_8 : uAdd T8_1_5_5_5_6_7_8_8 (2 : Fin 7) (1 : Fin 7) ((17 : ℚ) / (15 : ℚ)) true = some T8_1_5_5_5_6_7_8_9 :=
  uAdd_eq_some' (by simp [uKeepCur, uBackCond, T8_1_5_5_5_6_7_8_8] <;> norm_num) (by simp [uBack, uBackCond, T8_1_5_5_5_6_7_8_8] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, T8_1_5_5_5_6_7_8_8, T8_1_5_5_5_6_7_8_9] <;> norm_num)

#print axioms addEq_17_1_5_5_5_6_7_8

/-- Add 18 of the attesting chain: the entry at its pair is already tight (`uKeepCur` fires ground-true), so the table is unchanged. -/
theorem addEq_18_1_5_5_5_6_7_8 : uAdd T8_1_5_5_5_6_7_8_9 (1 : Fin 7) (2 : Fin 7) ((17 : ℚ) / (17 : ℚ)) true = some T8_1_5_5_5_6_7_8_9 :=
  by simp [uAdd, uKeepCur, uBackCond, uBack, uTighter, uProp, T8_1_5_5_5_6_7_8_9] <;> norm_num

#print axioms addEq_18_1_5_5_5_6_7_8

/-- Add 19 of the attesting chain: keep-cur and back are ground-false and the propagated result IS the next transcribed table (49 concrete pointwise checks). -/
theorem addEq_19_1_5_5_5_6_7_8 : uAdd T8_1_5_5_5_6_7_8_9 (1 : Fin 7) (4 : Fin 7) ((17 : ℚ) / (23 : ℚ)) true = some T8_1_5_5_5_6_7_8_10 :=
  uAdd_eq_some' (by simp [uKeepCur, uBackCond, T8_1_5_5_5_6_7_8_9] <;> norm_num) (by simp [uBack, uBackCond, T8_1_5_5_5_6_7_8_9] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, T8_1_5_5_5_6_7_8_9, T8_1_5_5_5_6_7_8_10] <;> norm_num)

#print axioms addEq_19_1_5_5_5_6_7_8

/-- Add 20 of the attesting chain: the entry at its pair is already tight (`uKeepCur` fires ground-true), so the table is unchanged. -/
theorem addEq_20_1_5_5_5_6_7_8 : uAdd T8_1_5_5_5_6_7_8_10 (4 : Fin 7) (1 : Fin 7) ((25 : ℚ) / (17 : ℚ)) true = some T8_1_5_5_5_6_7_8_10 :=
  by simp [uAdd, uKeepCur, uBackCond, uBack, uTighter, uProp, T8_1_5_5_5_6_7_8_10] <;> norm_num

#print axioms addEq_20_1_5_5_5_6_7_8

/-- Add 21 of the attesting chain: keep-cur and back are ground-false and the propagated result IS the next transcribed table (49 concrete pointwise checks). -/
theorem addEq_21_1_5_5_5_6_7_8 : uAdd T8_1_5_5_5_6_7_8_10 (4 : Fin 7) (6 : Fin 7) ((25 : ℚ) / (31 : ℚ)) true = some T8_1_5_5_5_6_7_8_11 :=
  uAdd_eq_some' (by simp [uKeepCur, uBackCond, T8_1_5_5_5_6_7_8_10] <;> norm_num) (by simp [uBack, uBackCond, T8_1_5_5_5_6_7_8_10] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, T8_1_5_5_5_6_7_8_10, T8_1_5_5_5_6_7_8_11] <;> norm_num)

#print axioms addEq_21_1_5_5_5_6_7_8

/-- Add 22 of the attesting chain: the entry at its pair is already tight (`uKeepCur` fires ground-true), so the table is unchanged. -/
theorem addEq_22_1_5_5_5_6_7_8 : uAdd T8_1_5_5_5_6_7_8_11 (6 : Fin 7) (4 : Fin 7) ((33 : ℚ) / (25 : ℚ)) true = some T8_1_5_5_5_6_7_8_11 :=
  by simp [uAdd, uKeepCur, uBackCond, uBack, uTighter, uProp, T8_1_5_5_5_6_7_8_11] <;> norm_num

#print axioms addEq_22_1_5_5_5_6_7_8

/-- Add 23 of the attesting chain: keep-cur and back are ground-false and the propagated result IS the next transcribed table (49 concrete pointwise checks). -/
theorem addEq_23_1_5_5_5_6_7_8 : uAdd T8_1_5_5_5_6_7_8_11 (6 : Fin 7) (3 : Fin 7) ((33 : ℚ) / (23 : ℚ)) true = some T8_1_5_5_5_6_7_8_12 :=
  uAdd_eq_some' (by simp [uKeepCur, uBackCond, T8_1_5_5_5_6_7_8_11] <;> norm_num) (by simp [uBack, uBackCond, T8_1_5_5_5_6_7_8_11] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, T8_1_5_5_5_6_7_8_11, T8_1_5_5_5_6_7_8_12] <;> norm_num)

#print axioms addEq_23_1_5_5_5_6_7_8

/-- Add 24 of the attesting chain: the entry at its pair is already tight (`uKeepCur` fires ground-true), so the table is unchanged. -/
theorem addEq_24_1_5_5_5_6_7_8 : uAdd T8_1_5_5_5_6_7_8_12 (3 : Fin 7) (6 : Fin 7) ((25 : ℚ) / (33 : ℚ)) true = some T8_1_5_5_5_6_7_8_12 :=
  by simp [uAdd, uKeepCur, uBackCond, uBack, uTighter, uProp, T8_1_5_5_5_6_7_8_12] <;> norm_num

#print axioms addEq_24_1_5_5_5_6_7_8

/-- Add 25 of the attesting chain: the entry at its pair is already tight (`uKeepCur` fires ground-true), so the table is unchanged. -/
theorem addEq_25_1_5_5_5_6_7_8 : uAdd T8_1_5_5_5_6_7_8_12 (3 : Fin 7) (5 : Fin 7) ((25 : ℚ) / (31 : ℚ)) true = some T8_1_5_5_5_6_7_8_12 :=
  by simp [uAdd, uKeepCur, uBackCond, uBack, uTighter, uProp, T8_1_5_5_5_6_7_8_12] <;> norm_num

#print axioms addEq_25_1_5_5_5_6_7_8

/-- Add 26 of the attesting chain: the entry at its pair is already tight (`uKeepCur` fires ground-true), so the table is unchanged. -/
theorem addEq_26_1_5_5_5_6_7_8 : uAdd T8_1_5_5_5_6_7_8_12 (5 : Fin 7) (3 : Fin 7) ((33 : ℚ) / (25 : ℚ)) true = some T8_1_5_5_5_6_7_8_12 :=
  by simp [uAdd, uKeepCur, uBackCond, uBack, uTighter, uProp, T8_1_5_5_5_6_7_8_12] <;> norm_num

#print axioms addEq_26_1_5_5_5_6_7_8

/-- Add 27 of the attesting chain: keep-cur and back are ground-false and the propagated result IS the next transcribed table (49 concrete pointwise checks). -/
theorem addEq_27_1_5_5_5_6_7_8 : uAdd T8_1_5_5_5_6_7_8_12 (5 : Fin 7) (2 : Fin 7) ((33 : ℚ) / (23 : ℚ)) true = some T8_1_5_5_5_6_7_8_13 :=
  uAdd_eq_some' (by simp [uKeepCur, uBackCond, T8_1_5_5_5_6_7_8_12] <;> norm_num) (by simp [uBack, uBackCond, T8_1_5_5_5_6_7_8_12] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, T8_1_5_5_5_6_7_8_12, T8_1_5_5_5_6_7_8_13] <;> norm_num)

#print axioms addEq_27_1_5_5_5_6_7_8

/-- Add 28 of the attesting chain: the entry at its pair is already tight (`uKeepCur` fires ground-true), so the table is unchanged. -/
theorem addEq_28_1_5_5_5_6_7_8 : uAdd T8_1_5_5_5_6_7_8_13 (2 : Fin 7) (5 : Fin 7) ((25 : ℚ) / (33 : ℚ)) true = some T8_1_5_5_5_6_7_8_13 :=
  by simp [uAdd, uKeepCur, uBackCond, uBack, uTighter, uProp, T8_1_5_5_5_6_7_8_13] <;> norm_num

#print axioms addEq_28_1_5_5_5_6_7_8

/-- Add 29 of the attesting chain: keep-cur and back are ground-false and the propagated result IS the next transcribed table (49 concrete pointwise checks). -/
theorem addEq_29_1_5_5_5_6_7_8 : uAdd T8_1_5_5_5_6_7_8_13 (2 : Fin 7) (4 : Fin 7) ((25 : ℚ) / (31 : ℚ)) true = some T8_1_5_5_5_6_7_8_14 :=
  uAdd_eq_some' (by simp [uKeepCur, uBackCond, T8_1_5_5_5_6_7_8_13] <;> norm_num) (by simp [uBack, uBackCond, T8_1_5_5_5_6_7_8_13] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, T8_1_5_5_5_6_7_8_13, T8_1_5_5_5_6_7_8_14] <;> norm_num)

#print axioms addEq_29_1_5_5_5_6_7_8

/-- Add 30 of the attesting chain: the entry at its pair is already tight (`uKeepCur` fires ground-true), so the table is unchanged. -/
theorem addEq_30_1_5_5_5_6_7_8 : uAdd T8_1_5_5_5_6_7_8_14 (4 : Fin 7) (2 : Fin 7) ((33 : ℚ) / (25 : ℚ)) true = some T8_1_5_5_5_6_7_8_14 :=
  by simp [uAdd, uKeepCur, uBackCond, uBack, uTighter, uProp, T8_1_5_5_5_6_7_8_14] <;> norm_num

#print axioms addEq_30_1_5_5_5_6_7_8

/-- Add 31 of the attesting chain: the entry at its pair is already tight (`uKeepCur` fires ground-true), so the table is unchanged. -/
theorem addEq_31_1_5_5_5_6_7_8 : uAdd T8_1_5_5_5_6_7_8_14 (4 : Fin 7) (1 : Fin 7) ((33 : ℚ) / (23 : ℚ)) true = some T8_1_5_5_5_6_7_8_14 :=
  by simp [uAdd, uKeepCur, uBackCond, uBack, uTighter, uProp, T8_1_5_5_5_6_7_8_14] <;> norm_num

#print axioms addEq_31_1_5_5_5_6_7_8

/-- Add 32 of the attesting chain: the entry at its pair is already tight (`uKeepCur` fires ground-true), so the table is unchanged. -/
theorem addEq_32_1_5_5_5_6_7_8 : uAdd T8_1_5_5_5_6_7_8_14 (1 : Fin 7) (4 : Fin 7) ((25 : ℚ) / (33 : ℚ)) true = some T8_1_5_5_5_6_7_8_14 :=
  by simp [uAdd, uKeepCur, uBackCond, uBack, uTighter, uProp, T8_1_5_5_5_6_7_8_14] <;> norm_num

#print axioms addEq_32_1_5_5_5_6_7_8

/-- Add 33 of the attesting chain: keep-cur and back are ground-false and the propagated result IS the next transcribed table (49 concrete pointwise checks). -/
theorem addEq_33_1_5_5_5_6_7_8 : uAdd T8_1_5_5_5_6_7_8_14 (1 : Fin 7) (5 : Fin 7) ((25 : ℚ) / (39 : ℚ)) true = some T8_1_5_5_5_6_7_8_15 :=
  uAdd_eq_some' (by simp [uKeepCur, uBackCond, T8_1_5_5_5_6_7_8_14] <;> norm_num) (by simp [uBack, uBackCond, T8_1_5_5_5_6_7_8_14] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, T8_1_5_5_5_6_7_8_14, T8_1_5_5_5_6_7_8_15] <;> norm_num)

#print axioms addEq_33_1_5_5_5_6_7_8

/-- Add 34 of the attesting chain: the entry at its pair is already tight (`uKeepCur` fires ground-true), so the table is unchanged. -/
theorem addEq_34_1_5_5_5_6_7_8 : uAdd T8_1_5_5_5_6_7_8_15 (5 : Fin 7) (1 : Fin 7) ((41 : ℚ) / (25 : ℚ)) true = some T8_1_5_5_5_6_7_8_15 :=
  by simp [uAdd, uKeepCur, uBackCond, uBack, uTighter, uProp, T8_1_5_5_5_6_7_8_15] <;> norm_num

#print axioms addEq_34_1_5_5_5_6_7_8

/-- Add 35 of the attesting chain: the entry at its pair is already tight (`uKeepCur` fires ground-true), so the table is unchanged. -/
theorem addEq_35_1_5_5_5_6_7_8 : uAdd T8_1_5_5_5_6_7_8_15 (5 : Fin 7) (3 : Fin 7) ((41 : ℚ) / (31 : ℚ)) true = some T8_1_5_5_5_6_7_8_15 :=
  by simp [uAdd, uKeepCur, uBackCond, uBack, uTighter, uProp, T8_1_5_5_5_6_7_8_15] <;> norm_num

#print axioms addEq_35_1_5_5_5_6_7_8

/-- Add 36 of the attesting chain: the entry at its pair is already tight (`uKeepCur` fires ground-true), so the table is unchanged. -/
theorem addEq_36_1_5_5_5_6_7_8 : uAdd T8_1_5_5_5_6_7_8_15 (3 : Fin 7) (5 : Fin 7) ((33 : ℚ) / (41 : ℚ)) true = some T8_1_5_5_5_6_7_8_15 :=
  by simp [uAdd, uKeepCur, uBackCond, uBack, uTighter, uProp, T8_1_5_5_5_6_7_8_15] <;> norm_num

#print axioms addEq_36_1_5_5_5_6_7_8

/-- Add 37 of the attesting chain: keep-cur and back are ground-false and the propagated result IS the next transcribed table (49 concrete pointwise checks). -/
theorem addEq_37_1_5_5_5_6_7_8 : uAdd T8_1_5_5_5_6_7_8_15 (3 : Fin 7) (6 : Fin 7) ((33 : ℚ) / (47 : ℚ)) true = some T8_1_5_5_5_6_7_8_16 :=
  uAdd_eq_some' (by simp [uKeepCur, uBackCond, T8_1_5_5_5_6_7_8_15] <;> norm_num) (by simp [uBack, uBackCond, T8_1_5_5_5_6_7_8_15] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, T8_1_5_5_5_6_7_8_15, T8_1_5_5_5_6_7_8_16] <;> norm_num)

#print axioms addEq_37_1_5_5_5_6_7_8

/-- Add 38 of the attesting chain: the entry at its pair is already tight (`uKeepCur` fires ground-true), so the table is unchanged. -/
theorem addEq_38_1_5_5_5_6_7_8 : uAdd T8_1_5_5_5_6_7_8_16 (6 : Fin 7) (3 : Fin 7) ((49 : ℚ) / (33 : ℚ)) true = some T8_1_5_5_5_6_7_8_16 :=
  by simp [uAdd, uKeepCur, uBackCond, uBack, uTighter, uProp, T8_1_5_5_5_6_7_8_16] <;> norm_num

#print axioms addEq_38_1_5_5_5_6_7_8

/-- Step 1 of the attesting chain: its two `uAdd`s on positive numerators compose to the step equation. -/
theorem stepEq_1_1_5_5_5_6_7_8 : uStep (mkOf (![1, 5, 5, 5, 6, 7, 8] : Fin 7 → ℤ)) (0 : Fin 7) (5 : Fin 7) (1 : ℚ) (7 : ℚ) (9 : ℚ) = some T8_1_5_5_5_6_7_8_1 :=
  uStep_eq_some' (by norm_num) (by norm_num) (by norm_num) addEq_1_1_5_5_5_6_7_8 addEq_2_1_5_5_5_6_7_8

#print axioms stepEq_1_1_5_5_5_6_7_8

/-- Step 2 of the attesting chain: its two `uAdd`s on positive numerators compose to the step equation. -/
theorem stepEq_2_1_5_5_5_6_7_8 : uStep T8_1_5_5_5_6_7_8_1 (5 : Fin 7) (3 : Fin 7) (9 : ℚ) (7 : ℚ) (9 : ℚ) = some T8_1_5_5_5_6_7_8_2 :=
  uStep_eq_some' (by norm_num) (by norm_num) (by norm_num) addEq_3_1_5_5_5_6_7_8 addEq_4_1_5_5_5_6_7_8

#print axioms stepEq_2_1_5_5_5_6_7_8

/-- Step 3 of the attesting chain: its two `uAdd`s on positive numerators compose to the step equation. -/
theorem stepEq_3_1_5_5_5_6_7_8 : uStep T8_1_5_5_5_6_7_8_2 (3 : Fin 7) (1 : Fin 7) (9 : ℚ) (7 : ℚ) (9 : ℚ) = some T8_1_5_5_5_6_7_8_2 :=
  uStep_eq_some' (by norm_num) (by norm_num) (by norm_num) addEq_5_1_5_5_5_6_7_8 addEq_6_1_5_5_5_6_7_8

#print axioms stepEq_3_1_5_5_5_6_7_8

/-- Step 4 of the attesting chain: its two `uAdd`s on positive numerators compose to the step equation. -/
theorem stepEq_4_1_5_5_5_6_7_8 : uStep T8_1_5_5_5_6_7_8_2 (1 : Fin 7) (6 : Fin 7) (9 : ℚ) (15 : ℚ) (17 : ℚ) = some T8_1_5_5_5_6_7_8_4 :=
  uStep_eq_some' (by norm_num) (by norm_num) (by norm_num) addEq_7_1_5_5_5_6_7_8 addEq_8_1_5_5_5_6_7_8

#print axioms stepEq_4_1_5_5_5_6_7_8

/-- Step 5 of the attesting chain: its two `uAdd`s on positive numerators compose to the step equation. -/
theorem stepEq_5_1_5_5_5_6_7_8 : uStep T8_1_5_5_5_6_7_8_4 (6 : Fin 7) (5 : Fin 7) (17 : ℚ) (15 : ℚ) (17 : ℚ) = some T8_1_5_5_5_6_7_8_5 :=
  uStep_eq_some' (by norm_num) (by norm_num) (by norm_num) addEq_9_1_5_5_5_6_7_8 addEq_10_1_5_5_5_6_7_8

#print axioms stepEq_5_1_5_5_5_6_7_8

/-- Step 6 of the attesting chain: its two `uAdd`s on positive numerators compose to the step equation. -/
theorem stepEq_6_1_5_5_5_6_7_8 : uStep T8_1_5_5_5_6_7_8_5 (5 : Fin 7) (4 : Fin 7) (17 : ℚ) (15 : ℚ) (17 : ℚ) = some T8_1_5_5_5_6_7_8_6 :=
  uStep_eq_some' (by norm_num) (by norm_num) (by norm_num) addEq_11_1_5_5_5_6_7_8 addEq_12_1_5_5_5_6_7_8

#print axioms stepEq_6_1_5_5_5_6_7_8

/-- Step 7 of the attesting chain: its two `uAdd`s on positive numerators compose to the step equation. -/
theorem stepEq_7_1_5_5_5_6_7_8 : uStep T8_1_5_5_5_6_7_8_6 (4 : Fin 7) (3 : Fin 7) (17 : ℚ) (15 : ℚ) (17 : ℚ) = some T8_1_5_5_5_6_7_8_7 :=
  uStep_eq_some' (by norm_num) (by norm_num) (by norm_num) addEq_13_1_5_5_5_6_7_8 addEq_14_1_5_5_5_6_7_8

#print axioms stepEq_7_1_5_5_5_6_7_8

/-- Step 8 of the attesting chain: its two `uAdd`s on positive numerators compose to the step equation. -/
theorem stepEq_8_1_5_5_5_6_7_8 : uStep T8_1_5_5_5_6_7_8_7 (3 : Fin 7) (2 : Fin 7) (17 : ℚ) (15 : ℚ) (17 : ℚ) = some T8_1_5_5_5_6_7_8_8 :=
  uStep_eq_some' (by norm_num) (by norm_num) (by norm_num) addEq_15_1_5_5_5_6_7_8 addEq_16_1_5_5_5_6_7_8

#print axioms stepEq_8_1_5_5_5_6_7_8

/-- Step 9 of the attesting chain: its two `uAdd`s on positive numerators compose to the step equation. -/
theorem stepEq_9_1_5_5_5_6_7_8 : uStep T8_1_5_5_5_6_7_8_8 (2 : Fin 7) (1 : Fin 7) (17 : ℚ) (15 : ℚ) (17 : ℚ) = some T8_1_5_5_5_6_7_8_9 :=
  uStep_eq_some' (by norm_num) (by norm_num) (by norm_num) addEq_17_1_5_5_5_6_7_8 addEq_18_1_5_5_5_6_7_8

#print axioms stepEq_9_1_5_5_5_6_7_8

/-- Step 10 of the attesting chain: its two `uAdd`s on positive numerators compose to the step equation. -/
theorem stepEq_10_1_5_5_5_6_7_8 : uStep T8_1_5_5_5_6_7_8_9 (1 : Fin 7) (4 : Fin 7) (17 : ℚ) (23 : ℚ) (25 : ℚ) = some T8_1_5_5_5_6_7_8_10 :=
  uStep_eq_some' (by norm_num) (by norm_num) (by norm_num) addEq_19_1_5_5_5_6_7_8 addEq_20_1_5_5_5_6_7_8

#print axioms stepEq_10_1_5_5_5_6_7_8

/-- Step 11 of the attesting chain: its two `uAdd`s on positive numerators compose to the step equation. -/
theorem stepEq_11_1_5_5_5_6_7_8 : uStep T8_1_5_5_5_6_7_8_10 (4 : Fin 7) (6 : Fin 7) (25 : ℚ) (31 : ℚ) (33 : ℚ) = some T8_1_5_5_5_6_7_8_11 :=
  uStep_eq_some' (by norm_num) (by norm_num) (by norm_num) addEq_21_1_5_5_5_6_7_8 addEq_22_1_5_5_5_6_7_8

#print axioms stepEq_11_1_5_5_5_6_7_8

/-- Step 12 of the attesting chain: its two `uAdd`s on positive numerators compose to the step equation. -/
theorem stepEq_12_1_5_5_5_6_7_8 : uStep T8_1_5_5_5_6_7_8_11 (6 : Fin 7) (3 : Fin 7) (33 : ℚ) (23 : ℚ) (25 : ℚ) = some T8_1_5_5_5_6_7_8_12 :=
  uStep_eq_some' (by norm_num) (by norm_num) (by norm_num) addEq_23_1_5_5_5_6_7_8 addEq_24_1_5_5_5_6_7_8

#print axioms stepEq_12_1_5_5_5_6_7_8

/-- Step 13 of the attesting chain: its two `uAdd`s on positive numerators compose to the step equation. -/
theorem stepEq_13_1_5_5_5_6_7_8 : uStep T8_1_5_5_5_6_7_8_12 (3 : Fin 7) (5 : Fin 7) (25 : ℚ) (31 : ℚ) (33 : ℚ) = some T8_1_5_5_5_6_7_8_12 :=
  uStep_eq_some' (by norm_num) (by norm_num) (by norm_num) addEq_25_1_5_5_5_6_7_8 addEq_26_1_5_5_5_6_7_8

#print axioms stepEq_13_1_5_5_5_6_7_8

/-- Step 14 of the attesting chain: its two `uAdd`s on positive numerators compose to the step equation. -/
theorem stepEq_14_1_5_5_5_6_7_8 : uStep T8_1_5_5_5_6_7_8_12 (5 : Fin 7) (2 : Fin 7) (33 : ℚ) (23 : ℚ) (25 : ℚ) = some T8_1_5_5_5_6_7_8_13 :=
  uStep_eq_some' (by norm_num) (by norm_num) (by norm_num) addEq_27_1_5_5_5_6_7_8 addEq_28_1_5_5_5_6_7_8

#print axioms stepEq_14_1_5_5_5_6_7_8

/-- Step 15 of the attesting chain: its two `uAdd`s on positive numerators compose to the step equation. -/
theorem stepEq_15_1_5_5_5_6_7_8 : uStep T8_1_5_5_5_6_7_8_13 (2 : Fin 7) (4 : Fin 7) (25 : ℚ) (31 : ℚ) (33 : ℚ) = some T8_1_5_5_5_6_7_8_14 :=
  uStep_eq_some' (by norm_num) (by norm_num) (by norm_num) addEq_29_1_5_5_5_6_7_8 addEq_30_1_5_5_5_6_7_8

#print axioms stepEq_15_1_5_5_5_6_7_8

/-- Step 16 of the attesting chain: its two `uAdd`s on positive numerators compose to the step equation. -/
theorem stepEq_16_1_5_5_5_6_7_8 : uStep T8_1_5_5_5_6_7_8_14 (4 : Fin 7) (1 : Fin 7) (33 : ℚ) (23 : ℚ) (25 : ℚ) = some T8_1_5_5_5_6_7_8_14 :=
  uStep_eq_some' (by norm_num) (by norm_num) (by norm_num) addEq_31_1_5_5_5_6_7_8 addEq_32_1_5_5_5_6_7_8

#print axioms stepEq_16_1_5_5_5_6_7_8

/-- Step 17 of the attesting chain: its two `uAdd`s on positive numerators compose to the step equation. -/
theorem stepEq_17_1_5_5_5_6_7_8 : uStep T8_1_5_5_5_6_7_8_14 (1 : Fin 7) (5 : Fin 7) (25 : ℚ) (39 : ℚ) (41 : ℚ) = some T8_1_5_5_5_6_7_8_15 :=
  uStep_eq_some' (by norm_num) (by norm_num) (by norm_num) addEq_33_1_5_5_5_6_7_8 addEq_34_1_5_5_5_6_7_8

#print axioms stepEq_17_1_5_5_5_6_7_8

/-- Step 18 of the attesting chain: its two `uAdd`s on positive numerators compose to the step equation. -/
theorem stepEq_18_1_5_5_5_6_7_8 : uStep T8_1_5_5_5_6_7_8_15 (5 : Fin 7) (3 : Fin 7) (41 : ℚ) (31 : ℚ) (33 : ℚ) = some T8_1_5_5_5_6_7_8_15 :=
  uStep_eq_some' (by norm_num) (by norm_num) (by norm_num) addEq_35_1_5_5_5_6_7_8 addEq_36_1_5_5_5_6_7_8

#print axioms stepEq_18_1_5_5_5_6_7_8

/-- Step 19 of the attesting chain: its two `uAdd`s on positive numerators compose to the step equation. -/
theorem stepEq_19_1_5_5_5_6_7_8 : uStep T8_1_5_5_5_6_7_8_15 (3 : Fin 7) (6 : Fin 7) (33 : ℚ) (47 : ℚ) (49 : ℚ) = some T8_1_5_5_5_6_7_8_16 :=
  uStep_eq_some' (by norm_num) (by norm_num) (by norm_num) addEq_37_1_5_5_5_6_7_8 addEq_38_1_5_5_5_6_7_8

#print axioms stepEq_19_1_5_5_5_6_7_8

/-- The 19-step prefix run's trace table IS `T8_1_5_5_5_6_7_8_16` (peel the first 19 step equations; entries only tighten along a run). -/
theorem traceP_1_5_5_5_6_7_8_p19 {V : UTable} {af : Fin 7} {Af : ℚ}
    (hrun : chainRun (mkOf (![1, 5, 5, 5, 6, 7, 8] : Fin 7 → ℤ)) 0 1 steps8_1_5_5_5_6_7_8 = some (V, af, Af)) :
    V = T8_1_5_5_5_6_7_8_16 := by
  simp only [steps8_1_5_5_5_6_7_8,
    chainRun_step_some stepEq_1_1_5_5_5_6_7_8,
    chainRun_step_some stepEq_2_1_5_5_5_6_7_8,
    chainRun_step_some stepEq_3_1_5_5_5_6_7_8,
    chainRun_step_some stepEq_4_1_5_5_5_6_7_8,
    chainRun_step_some stepEq_5_1_5_5_5_6_7_8,
    chainRun_step_some stepEq_6_1_5_5_5_6_7_8,
    chainRun_step_some stepEq_7_1_5_5_5_6_7_8,
    chainRun_step_some stepEq_8_1_5_5_5_6_7_8,
    chainRun_step_some stepEq_9_1_5_5_5_6_7_8,
    chainRun_step_some stepEq_10_1_5_5_5_6_7_8,
    chainRun_step_some stepEq_11_1_5_5_5_6_7_8,
    chainRun_step_some stepEq_12_1_5_5_5_6_7_8,
    chainRun_step_some stepEq_13_1_5_5_5_6_7_8,
    chainRun_step_some stepEq_14_1_5_5_5_6_7_8,
    chainRun_step_some stepEq_15_1_5_5_5_6_7_8,
    chainRun_step_some stepEq_16_1_5_5_5_6_7_8,
    chainRun_step_some stepEq_17_1_5_5_5_6_7_8,
    chainRun_step_some stepEq_18_1_5_5_5_6_7_8,
    chainRun_step_some stepEq_19_1_5_5_5_6_7_8,
    chainRun_nil, Option.some.injEq, Prod.mk.injEq] at hrun
  exact hrun.1.symm

#print axioms traceP_1_5_5_5_6_7_8_p19

/-- The per-record attestation: the 19-step prefix chain's closed-trace entry at
(0, 6) is 6358/49491, dominating the record's cap 6358/49491. -/
theorem attests_1_5_5_5_6_7_8_r0 : Attests8 (![1, 5, 5, 5, 6, 7, 8] : Fin 7 → ℤ) ⟨6, 0, 73, 15, [(6, (6358 / 49491 : ℝ))]⟩ steps8_1_5_5_5_6_7_8 :=
  by
  intro V af Af hrun
  have hV := traceP_1_5_5_5_6_7_8_p19 hrun
  rw [hV]
  exact capsDom_single ⟨(6358 / 49491 : ℚ), true, by simp [T8_1_5_5_5_6_7_8_16], by norm_num⟩

#print axioms attests_1_5_5_5_6_7_8_r0

/-- The per-record attestation: the 19-step prefix chain's closed-trace entry at
(1, 6) is 3179/5499, dominating the record's cap 3179/5499. -/
theorem attests_1_5_5_5_6_7_8_r1 : Attests8 (![1, 5, 5, 5, 6, 7, 8] : Fin 7 → ℤ) ⟨6, 1, 73, 47, [(6, (3179 / 5499 : ℝ))]⟩ steps8_1_5_5_5_6_7_8 :=
  by
  intro V af Af hrun
  have hV := traceP_1_5_5_5_6_7_8_p19 hrun
  rw [hV]
  exact capsDom_single ⟨(3179 / 5499 : ℚ), true, by simp [T8_1_5_5_5_6_7_8_16], by norm_num⟩

#print axioms attests_1_5_5_5_6_7_8_r1

/-- The per-record attestation: the 19-step prefix chain's closed-trace entry at
(1, 6) is 3179/5499, dominating the record's cap 3179/5499. -/
theorem attests_1_5_5_5_6_7_8_r2 : Attests8 (![1, 5, 5, 5, 6, 7, 8] : Fin 7 → ℤ) ⟨6, 1, 73, 55, [(6, (3179 / 5499 : ℝ))]⟩ steps8_1_5_5_5_6_7_8 :=
  by
  intro V af Af hrun
  have hV := traceP_1_5_5_5_6_7_8_p19 hrun
  rw [hV]
  exact capsDom_single ⟨(3179 / 5499 : ℚ), true, by simp [T8_1_5_5_5_6_7_8_16], by norm_num⟩

#print axioms attests_1_5_5_5_6_7_8_r2

/-- The per-record attestation: the 19-step prefix chain's closed-trace entry at
(1, 6) is 3179/5499, dominating the record's cap 3179/5499. -/
theorem attests_1_5_5_5_6_7_8_r3 : Attests8 (![1, 5, 5, 5, 6, 7, 8] : Fin 7 → ℤ) ⟨6, 1, 73, 63, [(6, (3179 / 5499 : ℝ))]⟩ steps8_1_5_5_5_6_7_8 :=
  by
  intro V af Af hrun
  have hV := traceP_1_5_5_5_6_7_8_p19 hrun
  rw [hV]
  exact capsDom_single ⟨(3179 / 5499 : ℚ), true, by simp [T8_1_5_5_5_6_7_8_16], by norm_num⟩

#print axioms attests_1_5_5_5_6_7_8_r3

/-- Per-record attestation for this box:
box (1, 5, 5, 5, 6, 7, 8)'s strict-class family carries the faithful per-record datum from the
transcribed full closure -- every record is attested by a nested prefix of the one
attesting chain (records sharing a pair share the witness). -/
theorem chainDomPerRecord8_1_5_5_5_6_7_8 :
    ChainDomPerRecord8 (![1, 5, 5, 5, 6, 7, 8] : Fin 7 → ℤ) dumpFam_1_5_5_5_6_7_8 := by
  intro e he
  simp only [dumpFam_1_5_5_5_6_7_8, List.mem_cons] at he
  rcases he with rfl | rfl | rfl | rfl | h0
  · exact ⟨steps8_1_5_5_5_6_7_8, attests_1_5_5_5_6_7_8_r0⟩
  · exact ⟨steps8_1_5_5_5_6_7_8, attests_1_5_5_5_6_7_8_r1⟩
  · exact ⟨steps8_1_5_5_5_6_7_8, attests_1_5_5_5_6_7_8_r2⟩
  · exact ⟨steps8_1_5_5_5_6_7_8, attests_1_5_5_5_6_7_8_r3⟩
  · exact absurd h0 (by simp)

#print axioms chainDomPerRecord8_1_5_5_5_6_7_8


end Fresh.ChainDomPerRec8
