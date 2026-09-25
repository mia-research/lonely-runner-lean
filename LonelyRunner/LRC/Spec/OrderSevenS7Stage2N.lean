import LonelyRunner.LRC.Spec.OrderSevenS7M1N

/-!
# n = 7 (Barajas–Serra) — §7 stage 2: the `N' = 98` vocabulary

Definitions shared by the stage-2 searches: the 32 lifts of a 5-set from
`ZMod 49` to `ZMod 98`, the admissible `d₆` values, and solvability at
`N' = 98` (where the multiplier ranges over ALL of `1..97`, not just the units —
restricting to units manufactures a spurious exception with `gcd = 1`).

The searches themselves are in `OrderSevenS7Stage2AllN` and
`OrderSevenS7Stage2OddN`, one heavy kernel `rfl` per module: `lake build` also
emits C and overflows the elaboration stack where `lake env lean` does not.
-/

namespace LRC.OrderSevenN
namespace Section7M1

/-! ## Stage 2 — `N' = 98` -/

/-- The 32 lifts of a 5-set from `ZMod 49` to `ZMod 98` (`x` or `x + 49` each). -/
def liftsOf (T : List Nat) : List (List Nat) :=
  T.foldr (fun x acc => acc.flatMap fun L => [x :: L, (x + 49) :: L]) [[]]

/-- Candidate `d₆` mod 98: the level-1 elements, `7 ∣ d₆` and `49 ∤ d₆`. -/
def d6vals : List Nat :=
  (List.range 14).filterMap (fun k =>
    let v := 7 * k; if k == 0 || v % 49 == 0 || v ≥ 98 then none else some v)

def gcdAll (L : List Nat) : Nat := L.foldr Nat.gcd 0

/-- Some multiplier in `1..97` gives every element circular distance `≥ 1/7`
at `N' = 98`. Note this ranges over ALL residues, not just the units. -/
def solvable98 (D : List Nat) : Bool :=
  (List.range 98).any fun lam =>
    lam > 0 && D.all fun x => let v := (lam * x) % 98; 14 ≤ v && v ≤ 84

end Section7M1
end LRC.OrderSevenN
