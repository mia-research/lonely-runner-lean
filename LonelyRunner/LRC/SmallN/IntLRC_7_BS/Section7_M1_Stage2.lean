import LonelyRunner.LRC.SmallN.IntLRC_7_BS.Section7_M1

/-!
# n = 7 (Barajas–Serra) — §7 stage 2, the `N' = 98` search

Split out of `Section7_M1.lean`: with both stages in one module, `lake build`
overflows the elaboration stack on the kernel `rfl` checks (`lake env lean`,
which does not also emit C, still succeeds). One heavy `rfl` per module keeps the
build within the default stack, so no `weakLeanArgs` change is needed.

Stage 1 (`Section7_M1.lean`) identifies the 63 exceptional 5-sets at `N = 49`.
This file shows they are all resolved at `N' = 2·49 = 98` once `d₆` is taken into
account and `gcd(D) = 1` is imposed — which is BS §7's second search.
-/

namespace IntLRC7BS
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

/-- `gcd = 1` configurations over `N' = 98` admitting no good multiplier. -/
def bad2 : List (List Nat) :=
  (exc.flatMap fun E => (liftsOf E).flatMap fun L => d6vals.map fun d6 => d6 :: L)
    |>.filter fun D => gcdAll D == 1 && !solvable98 D

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8000000 in
/-- **BS §7 stage 2, kernel-verified.** Every `gcd = 1` configuration over
`N' = 98` reducing to an exceptional 5-set admits a good multiplier. -/
theorem stage2_clean : bad2 = [] := by rfl

end Section7M1
end IntLRC7BS
