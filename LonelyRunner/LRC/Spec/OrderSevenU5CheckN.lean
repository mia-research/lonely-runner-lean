import LonelyRunner.LRC.Spec.OrderSevenU5DataN

/-! The AbsU5 certificate checker (E30).  `Claim U r` (in `OrderSevenU5SoundN`): any r table states share a good
instant inside U.  Node: branching instant `l` in `U`; every admissible blocker of `l` (admissible in the listed
classes: blocks at least |X_c| - 2(r-1) members of class c inside U) is kept or dominated by a kept state (good on
all of U ∩ M_k).  Leaves: no state blocks all of U.  Folds are strict (each step forces its accumulator). -/

namespace LRC.O7U5

def bitsList (U : Nat) : List Nat := range210.filter (fun x => U.testBit x)

/-- strict AND of `g x` over a list -/
def andMap (g : Nat → Nat) : List Nat → Nat → Nat
  | [], acc => acc
  | x :: xs, acc => let a := acc &&& g x; if a == 0 then 0 else andMap g xs a

/-- strict OR of `g x` over a list -/
def orMap (g : Nat → Nat) : List Nat → Nat → Nat
  | [], acc => acc
  | x :: xs, acc => let a := acc ||| g x; if a == 0 then orMap g xs 0 else orMap g xs a

/-- states blocking at least `m` of `xs` (plain recursion; used only in proofs of older drafts) -/
def atLeast : List Nat → Nat → Nat
  | _, 0 => ALLS
  | [], _ + 1 => 0
  | x :: xs, m + 1 => (BLK x &&& atLeast xs m) ||| atLeast xs (m + 1)

/-- one DP step: entry `j` = states blocking at least `j` of the elements seen so far -/
def stepV (b : Nat) : List Nat → Nat → List Nat
  | [], _ => []
  | s :: rest, prev => (s ||| (prev &&& b)) :: stepV b rest s

/-- DP over (instant, blocker set) pairs -/
def dpB : List (Nat × Nat) → List Nat → List Nat
  | [], v => v
  | p :: ps, v => dpB ps (stepV p.2 v 0)

def admC (U r c : Nat) : Nat :=
  let ps := (cmemB c).filter (fun p => U.testBit p.1)
  (dpB ps (ALLS :: List.replicate (ps.length - 2 * (r - 1)) 0)).getD (ps.length - 2 * (r - 1)) 0

def admL (U r : Nat) (cs : List Nat) : Nat := andMap (fun c => admC U r c) cs ALLS

def domk (U k : Nat) : Nat := andMap (fun x => BLK x ^^^ ALLS) (bitsList (U &&& MT k)) ALLS

def leafOK (U : Nat) : Bool := andMap BLK (bitsList U) ALLS == 0

def nodeOK (U r l : Nat) (cs K Kd : List Nat) : Bool :=
  U.testBit l &&
    (BLK l &&& admL U r cs &&& ((orMap (fun k => 1 <<< k) K 0 ||| orMap (fun k => domk U k) Kd 0) ^^^ ALLS)) == 0

def node2 (U l : Nat) (cs K : List Nat) : Bool :=
  nodeOK U 2 l cs K [] && K.all (fun k => decide (k < NS) && leafOK (U &&& MT k))

/-- A chunk of depth-2 children of the depth-1 node with uncovered set `U`. -/
def chunkOK (U : Nat) (ch : List (Nat × Nat × List Nat × List Nat)) : Bool :=
  ch.all (fun e => decide (e.1 < NS) && e.2.2.1.all (fun c => decide (c < 42)) &&
    node2 (U &&& MT e.1) e.2.1 e.2.2.1 e.2.2.2)

/-- The coverage check of a depth-1 node (no dominance at depth 1). -/
def covOK (U l : Nat) (cs Ks : List Nat) : Bool := cs.all (fun c => decide (c < 42)) && nodeOK U 3 l cs Ks []

/-- Decoder for packed certificate data (16-bit fields): `n` entries `(k, l, cs, K)`, each written
`k, l, |cs|, cs..., |K|, K...`.  Soundness does not depend on what it decodes. -/
def field (d : Nat) : Nat := d % 65536

def next (d : Nat) : Nat := d >>> 16

def readL : Nat → Nat → List Nat × Nat
  | 0, d => ([], d)
  | n + 1, d => let r := readL n (next d); (field d :: r.1, r.2)

def decode : Nat → Nat → List (Nat × Nat × List Nat × List Nat)
  | 0, _ => []
  | n + 1, d =>
    let k := field d
    let d1 := next d
    let l := field d1
    let d2 := next d1
    let a := readL (field d2) (next d2)
    let b := readL (field a.2) (next a.2)
    (k, l, a.1, b.1) :: decode n b.2

end LRC.O7U5
