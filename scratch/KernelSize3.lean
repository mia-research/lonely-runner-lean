namespace KernelSize3
def S21 : List Nat := (List.range 49).filter (fun x => x % 7 == 1 || x % 7 == 2 || x % 7 == 4)
def okFor (lam : Nat) (T : List Nat) : Bool := T.all (fun t => let v := (lam * t) % 49; 7 ≤ v && v ≤ 42)
def solvable (T : List Nat) : Bool := S21.any (fun lam => okFor lam T)
def subs5 : List (List Nat) :=
  S21.flatMap fun a => (S21.filter (a < ·)).flatMap fun b =>
  (S21.filter (b < ·)).flatMap fun c => (S21.filter (c < ·)).flatMap fun d =>
  (S21.filter (d < ·)).map fun e => [a,b,c,d,e]
def bad : List (List Nat) := subs5.filter (fun T => !solvable T)

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8000000 in
/-- The FULL BS §7 stage-1 search, verified by the Lean kernel: exactly 63
ordered 5-subsets (= 3 dilation orbits x 21) admit no good multiplier. -/
theorem stage1_bad_count : bad.length = 63 := by rfl

end KernelSize3
