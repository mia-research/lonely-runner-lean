import LonelyRunner.LRC.SmallN.IntLRC_7_BS.Section7_M1

/-!
# n = 7 (Barajas–Serra) — the 63 exceptional 5-sets, pinned as literals

`bad` (in `Section7_M1.lean`) computes the exceptional sets by filtering all
20349 five-subsets. Forcing that computation inside another theorem's kernel
`rfl` — as stage 2 must, since it quantifies over the exceptional sets — nests
two large reductions and overflows the elaboration stack under `lake build`.

Pinning the 63 sets as literals and proving them equal to `bad` once, here,
breaks that nesting: stage 2 then quantifies over a literal list.
-/

namespace IntLRC7BS
namespace Section7M1

/-- The 63 exceptional 5-sets, as literals. Pinning them lets stage 2 quantify
over the exceptional sets WITHOUT re-running stage 1's 20349-subset search inside
its own kernel `rfl` — that nesting is what overflows the elaboration stack. -/
def exc63 : List (List Nat) :=
  [[1, 4, 11, 39, 43], [1, 4, 18, 22, 29], [1, 4, 18, 44, 46],
   [1, 4, 22, 39, 43], [1, 8, 9, 36, 44], [1, 8, 18, 29, 32],
   [1, 8, 18, 32, 39], [1, 8, 22, 30, 46], [1, 9, 16, 30, 39],
   [1, 11, 29, 36, 37], [1, 15, 16, 18, 43], [1, 15, 22, 23, 37],
   [1, 22, 23, 30, 37], [1, 29, 30, 37, 44], [1, 29, 30, 43, 44],
   [2, 8, 9, 36, 44], [2, 8, 22, 29, 37], [2, 8, 29, 37, 44],
   [2, 8, 36, 39, 43], [2, 9, 11, 25, 39], [2, 9, 11, 37, 39],
   [2, 9, 15, 16, 36], [2, 9, 22, 23, 25], [2, 11, 16, 43, 44],
   [2, 11, 18, 29, 32], [2, 11, 25, 44, 46], [2, 15, 16, 29, 36],
   [2, 16, 18, 23, 39], [2, 25, 30, 44, 46], [2, 30, 32, 36, 37],
   [4, 9, 15, 22, 36], [4, 9, 16, 25, 39], [4, 9, 16, 25, 44],
   [4, 9, 23, 30, 32], [4, 11, 15, 23, 25], [4, 16, 18, 23, 39],
   [4, 16, 23, 29, 37], [4, 18, 22, 25, 29], [4, 18, 23, 30, 32],
   [4, 22, 32, 37, 39], [4, 29, 32, 36, 46], [8, 9, 15, 23, 43],
   [8, 9, 25, 32, 46], [8, 11, 15, 18, 46], [8, 11, 15, 36, 46],
   [8, 15, 25, 29, 44], [8, 18, 23, 30, 44], [8, 29, 32, 36, 46],
   [9, 15, 16, 23, 43], [9, 15, 37, 44, 46], [11, 15, 25, 36, 43],
   [11, 16, 36, 39, 46], [11, 23, 32, 37, 44], [11, 25, 32, 36, 43],
   [11, 32, 37, 44, 46], [15, 22, 25, 39, 43], [15, 22, 25, 39, 46],
   [16, 18, 30, 37, 46], [16, 22, 23, 30, 43], [16, 22, 30, 36, 43],
   [18, 25, 30, 39, 43], [18, 30, 32, 37, 46], [22, 23, 29, 32, 43]]

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8000000 in
/-- Every exceptional set is among the pinned literals. Stated as a `List.all`
rather than `exc63 = bad`: comparing the two list structures nests a deep
equality test inside `bad`'s own reduction and overflows the stack under
`lake build`, whereas membership checks stay shallow. -/
theorem bad_subset_exc63 : bad.all (fun T => exc63.contains T) = true := by rfl

end Section7M1
end IntLRC7BS
