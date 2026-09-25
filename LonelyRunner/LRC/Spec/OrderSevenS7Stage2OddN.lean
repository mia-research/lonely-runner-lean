import LonelyRunner.LRC.Spec.OrderSevenS7Stage2AllN

/-!
# n = 7 (Barajas–Serra) — §7 stage 2, the configurations `stage2_all_clean` misses

`stage2_all_clean` resolves every `N' = 98` configuration whose **residues** have
`gcdAll = 1`. That is *not* the hypothesis the bridge can supply. The LRC
normalization gives `gcd(d₁,…,d₅,d₆) = 1` for the **integers**, and a prime `p`
dividing all six residues mod `98` divides all six integers only when `p ∣ 98`,
i.e. `p ∈ {2,7}`. So from `gcd(D) = 1` one gets exactly

* `7 ∤ gcdAll` (already from `¬ 7 ∣ dᵢ`), and
* `2 ∤ gcdAll`, i.e. **some residue is odd**,

and nothing more. Over the 24192 configurations of the enumeration the residue
`gcdAll` takes the values `1`, `2` and `3`; the 12 configurations with
`gcdAll = 3` are odd, are genuinely reachable from an integer configuration with
`gcd = 1`, and are invisible to `stage2_all_clean`.

This file closes exactly that hole, and nothing else: it re-runs the enumeration
with the filter `odd ∧ gcdAll ≠ 1`, so `solvable98` is evaluated on only those 12
configurations (the `&&` short-circuits) and the kernel work is the cheap
`gcdAll` pass. Together with `stage2_all_clean` it gives

  `D` in the enumeration and some entry of `D` odd  ⟹  `solvable98 D`,

which is what `OrderSevenS7BridgeN` consumes. Chunked in four for the same reason as
`OrderSevenS7Stage2AllN`.
-/

namespace LRC.OrderSevenN
namespace Section7M1

/-- `gcd = 1` is replaced by the pair (some entry odd, `gcdAll ≠ 1`): the odd
configurations that `stage2_all_clean` does not already cover. -/
def bad2OddOf (Es : List (List Nat)) : List (List Nat) :=
  (Es.flatMap fun E => (liftsOf E).flatMap fun L => d6vals.map fun d6 => d6 :: L)
    |>.filter fun D => D.any (fun x => x % 2 == 1) && (gcdAll D != 1) && !solvable98 D

theorem bad2OddOf_append (a b : List (List Nat)) :
    bad2OddOf (a ++ b) = bad2OddOf a ++ bad2OddOf b := by
  simp [bad2OddOf, List.flatMap_append, List.filter_append]

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8000000 in
theorem stage2odd_chunk0 : bad2OddOf (exc63.take 16) = [] := by rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8000000 in
theorem stage2odd_chunk1 : bad2OddOf ((exc63.drop 16).take 16) = [] := by rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8000000 in
theorem stage2odd_chunk2 : bad2OddOf ((exc63.drop 32).take 16) = [] := by rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8000000 in
theorem stage2odd_chunk3 : bad2OddOf (exc63.drop 48) = [] := by rfl

/-- **The odd, non-unit-`gcdAll` configurations are all solvable at `N' = 98`.** -/
theorem stage2_odd_nonunit_clean : bad2OddOf exc63 = [] := by
  rw [exc63_split, bad2OddOf_append, bad2OddOf_append, bad2OddOf_append,
    stage2odd_chunk0, stage2odd_chunk1, stage2odd_chunk2, stage2odd_chunk3]
  rfl

end Section7M1
end LRC.OrderSevenN
