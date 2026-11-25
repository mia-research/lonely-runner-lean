import CertDefs
/-! E928 rule 22, the 162 large roots of stripCheck's search: per node of the search tree of `certOf`
(same recursion, depth cap 32), the outcome: LEAF (a pair of cells passes), NOCELL (no cell, i.e. no
R-interval clear for all five slow readings over the box), BLOCKED (cells exist, no pair separates the
fast reading's blockers).  Output per root: counts by depth and outcome, and cuts per coordinate. -/
open Fresh.TailStrip49 Fresh.TailStrip49Cert
structure ProfAcc where
  rows : Array (Nat × Nat × Nat) := #[]      -- per depth: leaf, nocell, blocked
  cuts : Array Nat := #[0,0,0,0,0]
def bump (a : ProfAcc) (d k : Nat) : ProfAcc :=
  let rows := if a.rows.size ≤ d then a.rows ++ (List.replicate (d + 1 - a.rows.size) (0,0,0)).toArray else a.rows
  let (x,y,z) := rows[d]!
  let v := if k = 0 then (x+1,y,z) else if k = 1 then (x,y+1,z) else (x,y,z+1)
  { a with rows := rows.set! d v }
partial def walk (box : Box) (d : Nat) (a : ProfAcc) : ProfAcc :=
  let cs := cellsJ box
  match findPairJ (max minTop (box.lo 4)) [] cs with
  | some (c,e) => if pairCheck box (mkCell box c) (mkCell box e) then bump a d 0 else bump a d 2
  | none =>
    let a := bump a d (if cs.isEmpty then 1 else 2)
    if d ≥ 32 then a else
    let i := widest box
    let a := { a with cuts := a.cuts.set! i.val (a.cuts[i.val]! + 1) }
    walk (right box i) (d+1) (walk (left box i) (d+1) a)
def main (args : List String) : IO Unit := do
  for t in [(1,1,3,23,24), (1,1,4,23,24), (1,1,3,19,20), (1,1,8,9,17), (1,1,10,11,12)] do
    let (p,q,r,s,u) := t
    let a := walk (root p q r s u) 0 {}
    IO.println s!"root {p} {q} {r} {s} {u}: cuts per coordinate {a.cuts.toList}"
    for d in List.range a.rows.size do
      let (x,y,z) := a.rows[d]!
      IO.println s!"  depth {d}: leaf {x} nocell {y} blocked {z}"
