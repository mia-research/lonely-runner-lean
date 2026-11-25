import CertDefs
open Fresh.TailStrip49 Fresh.TailStrip49Cert
def lv : Cert → Nat
  | .leaf _ _ => 1
  | .split l r => lv l + lv r
def dp : Cert → Nat
  | .leaf _ _ => 0
  | .split l r => max (dp l) (dp r) + 1
def tuples (a : Nat) : List (Nat × Nat × Nat × Nat × Nat) :=
  (List.range' a (27-a)).flatMap fun b => (List.range' b (27-b)).flatMap fun c =>
  (List.range' c (27-c)).flatMap fun d => (List.range' d (27-d)).map fun e => (a,b,c,d,e)
def main : IO Unit := do
  for a in [1,2,3] do
    for t in tuples a do
      let (a,b,c,d,e) := t
      match certOf (root a b c d e) 32 with
      | some cert => if lv cert > 3000 then IO.println s!"{a} {b} {c} {d} {e} leaves {lv cert} depth {dp cert} cells {(cellsJ (root a b c d e)).length}"
      | none => IO.println s!"{a} {b} {c} {d} {e} MISSING"
