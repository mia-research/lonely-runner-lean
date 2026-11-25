import Fresh.TailStrip49Compute
namespace Fresh.TailStrip49Cert
open Fresh.TailStrip49

/-- A cell named by its first window `w ∈ {0,1}` and one lap per slow reading. -/
structure CellCode where
  w : Nat
  js : List Nat
  deriving Inhabited, Repr

inductive Cert where
  | leaf (c d : CellCode)
  | split (l r : Cert)
  deriving Inhabited, Repr

def initCell (w : Nat) : Cell :=
  if w = 0 then ⟨⟨1,scale⟩,⟨7,scale⟩⟩ else ⟨⟨9,scale⟩,⟨15,scale⟩⟩

def stepCell (box : Box) (c : Cell) (i : Fin 5) (j : Nat) : Cell :=
  ⟨c.lo.max ⟨8*j+1, box.lo i⟩, c.hi.min ⟨8*j+7, box.hi i⟩⟩

def mkCell (box : Box) (code : CellCode) : Cell :=
  (slowIndices.zip code.js).foldl (fun c ij => stepCell box c ij.1 ij.2) (initCell code.w)

def certCheck : Box → Cert → Bool
  | box, .leaf c d => pairCheck box (mkCell box c) (mkCell box d)
  | box, .split l r =>
      certCheck (left box (widest box)) l && certCheck (right box (widest box)) r

def roots (a : Nat) : List Box :=
  (List.range' a (27-a)).flatMap fun b =>
  (List.range' b (27-b)).flatMap fun c =>
  (List.range' c (27-c)).flatMap fun d =>
  (List.range' d (27-d)).map fun e => root a b c d e

def sliceCheck (a : Nat) (certs : List Cert) : Bool :=
  let rs := roots a
  decide (rs.length = certs.length) && (rs.zip certs).all fun p => certCheck p.1 p.2

/-! Extraction (native only). -/
def slowStepJ (box : Box) (i : Fin 5) (cells : List (Cell × CellCode)) : List (Cell × CellCode) :=
  cells.flatMap fun (c, code) =>
    let start := (c.lo.n * box.hi i / c.lo.d - 7) / 8
    let stop := (c.hi.n * box.lo i / c.hi.d - 1) / 8
    (List.range' start (stop+1-start)).filterMap fun j =>
      let lo := c.lo.max ⟨8*j+1, box.lo i⟩
      let hi := c.hi.min ⟨8*j+7, box.hi i⟩
      if lo.le hi then some (⟨lo,hi⟩, ⟨code.w, code.js ++ [j]⟩) else none

def cellsJ (box : Box) : List (Cell × CellCode) :=
  slowIndices.foldl (fun acc i => slowStepJ box i acc)
    [(initCell 0, ⟨0,[]⟩), (initCell 1, ⟨1,[]⟩)]

def findPairJ (lo : Nat) (prev : List ((Cell × CellCode) × List Cell)) :
    List (Cell × CellCode) → Option (CellCode × CellCode)
  | [] => none
  | c :: cs =>
    let bad := blockers c.1 lo
    if bad.isEmpty then some (c.2, c.2)
    else match prev.find? (fun entry => separate entry.2 bad) with
      | some entry => some (entry.1.2, c.2)
      | none => findPairJ lo ((c,bad)::prev) cs

partial def certOf (box : Box) : Nat → Option Cert
  | n =>
    match findPairJ (max minTop (box.lo 4)) [] (cellsJ box) with
    | some (c,d) => if pairCheck box (mkCell box c) (mkCell box d) then some (.leaf c d) else none
    | none => match n with
      | 0 => none
      | k+1 => match certOf (left box (widest box)) k, certOf (right box (widest box)) k with
        | some l, some r => some (.split l r)
        | _, _ => none

def CellCode.src (c : CellCode) : String := s!"⟨{c.w},{c.js}⟩"
partial def Cert.src : Cert → String
  | .leaf c d => s!"(.leaf {c.src} {d.src})"
  | .split l r => s!"(.split {l.src} {r.src})"
end Fresh.TailStrip49Cert
