namespace KernelSize2
def S21 : List Nat := (List.range 49).filter (fun x => x % 7 == 1 || x % 7 == 2 || x % 7 == 4)
def okFor (lam : Nat) (T : List Nat) : Bool := T.all (fun t => let v := (lam * t) % 49; 7 ≤ v && v ≤ 42)
def solvable (T : List Nat) : Bool := S21.any (fun lam => okFor lam T)
def subs5 : List (List Nat) :=
  S21.flatMap fun a => (S21.filter (a < ·)).flatMap fun b =>
  (S21.filter (b < ·)).flatMap fun c => (S21.filter (c < ·)).flatMap fun d =>
  (S21.filter (d < ·)).map fun e => [a,b,c,d,e]
def numBad : Nat := (subs5.filter (fun T => !solvable T)).length

set_option maxRecDepth 4000000 in
example : subs5.length = 20349 := by rfl

end KernelSize2
