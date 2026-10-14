-- Can the Lean KERNEL run a search of the size BS §7 stage 1 needs?
-- 20349 five-subsets of a 21-element set, times 21 multipliers, times 5 members.
-- Written over Nat only (kernel has GMP-accelerated Nat), no Finset, no ZMod.
namespace KernelSize

def S21 : List Nat := (List.range 49).filter (fun x => x % 7 == 1 || x % 7 == 2 || x % 7 == 4)

def okFor (lam : Nat) (T : List Nat) : Bool := T.all (fun t => let v := (lam * t) % 49; 7 ≤ v && v ≤ 42)

def solvable (T : List Nat) : Bool := S21.any (fun lam => okFor lam T)

/-- all 5-element sublists, as ordered choices -/
def subs5 : List (List Nat) :=
  S21.flatMap fun a => (S21.filter (a < ·)).flatMap fun b =>
  (S21.filter (b < ·)).flatMap fun c => (S21.filter (c < ·)).flatMap fun d =>
  (S21.filter (d < ·)).map fun e => [a,b,c,d,e]

def numBad : Nat := (subs5.filter (fun T => !solvable T)).length

-- how many subsets are we actually enumerating?
#eval subs5.length
#eval numBad

-- THE KERNEL TEST: does `decide`/`rfl` reduce this without native code?
example : subs5.length = 20349 := by rfl

end KernelSize
