import LonelyRunner.LRC.Spec.OrderSevenS7M1N

/-!
# n = 7 (Barajas–Serra) — §7: fewer than five distinct residues is never exceptional

The `m = 1` bridge has to handle five level-0 elements whose residues mod 49 are
**not** distinct: `dᵢ ≠ dⱼ` as integers does not give `dᵢ ≢ dⱼ (mod 49)`. When two
coincide, the five arcs collapse to at most four distinct values, and the tuple
is not among the strictly-increasing 5-subsets that `bad` ranges over — so
`stage1` says nothing about it directly.

It does not need to: **every** subset of the 21 residues of size at most 4 admits
a good multiplier at `N = 49`. The exceptional sets exist only at size exactly 5.
So the collapsed case is discharged immediately, and BS's `N' = 98` detour is
needed only when all five residues are distinct.

| size | subsets | unsolvable at `N = 49` |
|---|---|---|
| 1 | 21 | 0 |
| 2 | 210 | 0 |
| 3 | 1330 | 0 |
| 4 | 5985 | 0 |
| 5 | 20349 | **63** |
-/

namespace LRC.OrderSevenN
namespace Section7M1

/-- All 5985 four-element subsets of `S21`, as strictly increasing lists. -/
def subs4 : List (List Nat) :=
  S21.flatMap fun a => (S21.filter (a < ·)).flatMap fun b =>
  (S21.filter (b < ·)).flatMap fun c => (S21.filter (c < ·)).map fun d => [a, b, c, d]

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8000000 in
/-- **Every four-element subset is solvable at `N = 49`.** Hence so is every
smaller one, since `solvable` only weakens as elements are removed. Combined with
`stage1_bad_count`, this says the exceptional sets occur at size exactly 5. -/
theorem subs4_all_solvable : subs4.all solvable = true := by rfl

end Section7M1
end LRC.OrderSevenN
