import LonelyRunner.LRC.SmallN.IntLRC_7_BS.Section7_M1_Stage2
import LonelyRunner.LRC.SmallN.IntLRC_7_BS.Section7_M1_Exc63

/-!
# n = 7 (Barajas–Serra) — §7 stage 2 over ALL 63 exceptional sets

Split from `Section7_M1_Stage2.lean` for the same reason that file was split from
`Section7_M1.lean`: one heavy kernel `rfl` per module keeps `lake build` within
the default elaboration stack.
-/

namespace IntLRC7BS
namespace Section7M1

/-! ## Stage 2 over ALL exceptional sets, not only BS's three representatives

BS check only their three published representatives. A faithful transcription
needs every exceptional 5-set, because an arbitrary `D` arrives as some dilate,
and reducing it to a representative would require a separate normalization
argument in Lean. `exc63` is all 63, so quantifying over it removes that step.
-/

/-- The `gcd = 1` configurations over `N' = 98` arising from a given list of
5-sets that admit no good multiplier. -/
def bad2Of (Es : List (List Nat)) : List (List Nat) :=
  (Es.flatMap fun E => (liftsOf E).flatMap fun L => d6vals.map fun d6 => d6 :: L)
    |>.filter fun D => gcdAll D == 1 && !solvable98 D

/-- `bad2Of` distributes over list append: it is a `flatMap` followed by a
`filter`, and both distribute. This is what lets the search be chunked without
ever forcing all 63 sets inside one kernel reduction. -/
theorem bad2Of_append (a b : List (List Nat)) :
    bad2Of (a ++ b) = bad2Of a ++ bad2Of b := by
  simp [bad2Of, List.flatMap_append, List.filter_append]

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8000000 in
theorem stage2_chunk0 : bad2Of (exc63.take 16) = [] := by rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8000000 in
theorem stage2_chunk1 : bad2Of ((exc63.drop 16).take 16) = [] := by rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8000000 in
theorem stage2_chunk2 : bad2Of ((exc63.drop 32).take 16) = [] := by rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8000000 in
theorem stage2_chunk3 : bad2Of (exc63.drop 48) = [] := by rfl

/-- `exc63` split into the four chunks the theorems above cover. Pure list
surgery on a literal, so this `rfl` is shallow. -/
theorem exc63_split :
    exc63 = exc63.take 16 ++ (exc63.drop 16).take 16 ++
            ((exc63.drop 32).take 16 ++ exc63.drop 48) := by rfl

/-- **BS §7 stage 2, over all 63 exceptional sets.** Every `gcd = 1`
configuration over `N' = 98` whose 5-set is exceptional mod 49 admits a
multiplier placing all six elements at circle distance `≥ 1/7`.

This is the form the `m = 1` case needs: no dilation-normalization to BS's three
published representatives is required, because the quantification already runs
over every exceptional set. 23802 configurations survive the `gcd = 1` filter. -/
theorem stage2_all_clean : bad2Of exc63 = [] := by
  rw [exc63_split, bad2Of_append, bad2Of_append, bad2Of_append,
    stage2_chunk0, stage2_chunk1, stage2_chunk2, stage2_chunk3]
  rfl

end Section7M1
end IntLRC7BS
