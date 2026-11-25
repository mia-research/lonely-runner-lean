import CertDefs
/-! Prof2: Prof over all roots listed in large_roots.out, one line of totals per root.  Prof docstring:
E928 rule 22, the 162 large roots of stripCheck's search: per node of the search tree of `certOf`
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
  let txt ← IO.FS.readFile (args.head!)
  for line in txt.splitOn "\n" do
    let w := (line.splitOn " ").filter (· ≠ "")
    if w.length ≥ 5 then
      let t := (w.take 5).map String.toNat!
      let a := walk (root t[0]! t[1]! t[2]! t[3]! t[4]!) 0 {}
      let (l, n, b) := a.rows.foldl (fun (acc : Nat × Nat × Nat) (r : Nat × Nat × Nat) => (acc.1 + r.1, acc.2.1 + r.2.1, acc.2.2 + r.2.2)) (0, 0, 0)
      let firstB := (List.range a.rows.size).find? (fun d => (a.rows[d]!).2.2 > 0)
      let lastN := (List.range a.rows.size).reverse.find? (fun d => (a.rows[d]!).2.1 > 0)
      IO.println s!"{t} leaves {l} nocell {n} blocked {b} depth {a.rows.size - 1} first_blocked_depth {firstB} last_nocell_depth {lastN} cuts {a.cuts.toList}"
