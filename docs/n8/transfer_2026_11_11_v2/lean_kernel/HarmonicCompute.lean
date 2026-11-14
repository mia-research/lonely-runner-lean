import Std

namespace Fresh.Harmonic

/-- An integer bound and whether its upper endpoint is excluded. -/
structure Bound where
  value : Int
  strict : Bool := false
  deriving DecidableEq, Hashable, Inhabited

def Bound.add (a b : Bound) : Bound := ⟨a.value+b.value,a.strict||b.strict⟩
def Bound.tighter (a b : Bound) : Bool :=
  decide (a.value < b.value) || (a.value == b.value && a.strict && !b.strict)
def Bound.min (a b : Bound) : Bound := if a.tighter b then a else b

abbrev Matrix (n : Nat) := Vector (Vector Bound n) n
abbrev Choice (n : Nat) := Fin n × Fin n × Bound × Bound
abbrev Clause (n : Nat) := List (Choice n)

def matrix (f : Fin n → Fin n → Bound) : Matrix n :=
  Vector.ofFn fun i => Vector.ofFn fun j => f i j

def constrain (b : Matrix n) (i j : Fin n) (a : Bound) : Option (Matrix n) :=
  if !a.tighter b[i][j] then some b
  else if (a.add b[j][i]).tighter ⟨0,false⟩ then none
  else some (matrix fun p q => b[p][q].min ((b[p][i].add a).add b[j][q]))

def impose (b : Matrix n) (c : Choice n) : Option (Matrix n) := do
  let (i,j,u,v) := c
  let b' ← constrain b i j u
  constrain b' j i v

def possible (b : Matrix n) (c : Choice n) : Bool :=
  let (i,j,u,v) := c
  let zero : Bound := ⟨0,false⟩
  !(u.add b[j][i]).tighter zero && !(v.add b[i][j]).tighter zero &&
    !(u.add v).tighter zero

def implied (b : Matrix n) (c : Choice n) : Bool :=
  let (i,j,u,v) := c
  !u.tighter b[i][j] && !v.tighter b[j][i]

def pending (b : Matrix n) (clauses : List (Clause n)) : List (Clause n) :=
  ((clauses.filter fun c => !c.any (implied b)).map fun c => c.filter (possible b))
    |>.mergeSort (fun a b => a.length ≤ b.length)

def solve (fuel : Nat) (b : Matrix n) (clauses : List (Clause n)) : List (Matrix n) :=
  match fuel with
  | 0 => [b]
  | fuel+1 =>
    match pending b clauses with
    | [] => [b]
    | first :: rest => first.flatMap fun c =>
      match impose b c with
      | none => []
      | some b' => solve fuel b' rest

-- Common multiple of 100*m*p for the checked harmonic ranges.
def slopeProduct (p : Vector Nat n) : Nat := p.toList.foldr (· * ·) 1

def unit (p : Vector Nat n) : Nat := 6000 * slopeProduct p

def root (p : Vector Nat n) : Matrix n :=
  matrix fun i j =>
    if i=j then ⟨0,false⟩
    else if i<j && p[i]==p[j] then ⟨0,false⟩
    else ⟨(unit p/p[i] : Nat),false⟩

def choices (p : Vector Nat n) (m : Nat) (i : Fin n) (j : Nat) : Clause n :=
  (List.finRange n).flatMap fun h =>
    if i=h then [] else
      let u := (unit p / (100*m*p[i]) : Nat)
      let v := (unit p / (100*m*p[h]) : Nat)
      let right := (100*(j : Int)+13)*(u : Int)
      (List.range (2*m*p[h]+p[h]+3)).map fun (k : Nat) =>
        let lap : Int := (k : Int)-(m*p[h]+1 : Nat)
        (i,h,⟨right-(100*lap-13)*(v : Int),false⟩,
          ⟨(100*lap+13)*(v : Int)-right,true⟩)

def clauses (p : Vector Nat n) (m : Nat) : List (Clause n) :=
  (List.finRange n).flatMap fun i => (List.range p[i]).map fun j =>
    (choices p m i j).filter (possible (root p))

instance : Hashable (Matrix n) := ⟨fun b => hash (b.toList.map Vector.toList)⟩
def dedup (xs : List (Matrix n)) : List (Matrix n) :=
  (Std.HashSet.ofList xs).toList

def replay (p : Vector Nat n) (ms : List Nat) : List (Matrix n) :=
  ms.foldl (fun states m =>
    let jobs := clauses p m
    dedup (states.flatMap fun b => solve (jobs.length+1) b jobs)) [root p]

end Fresh.Harmonic

namespace Fresh.Harmonic

def vectors : (n top lo : Nat) → List (Vector Nat n)
  | 0, _, _ => [#v[]]
  | n+1, top, lo => (List.range' lo (top+1-lo)).flatMap fun a =>
    (vectors n top a).map fun v => Vector.ofFn (Fin.cases a (fun i => v[i]))

def mixed (p : Vector Nat n) : Bool :=
  (p.toList.foldl Nat.gcd 0 == 1) && (p.toList.any (fun a => a > 1))

def fiveTimes (p : Vector Nat 5) : List Nat :=
  if p == #v[1,1,1,3,3] then [1,2,3] else [1,2,5]

def fiveCheck : Bool :=
  ((vectors 5 10 1).filter mixed).all fun p => (replay p (fiveTimes p)).isEmpty

def sixCheck : Bool :=
  ((vectors 6 5 1).filter mixed).all fun p => (replay p [1,2,3,4,5]).isEmpty

end Fresh.Harmonic

namespace Fresh.Harmonic

def ratios : List (Nat × Nat) :=
  (List.range' 1 7).flatMap fun a => ((List.range' 1 a).filter fun b => a.gcd b == 1).map (a, ·)

def ratioCompatible (u v : Nat × Nat) : Bool :=
  let a := u.1*v.2
  let b := u.2*v.1
  max a b / a.gcd b ≤ 7

def fourCatalogue : List (Vector Nat 4) :=
  ratios.flatMap fun x => ratios.flatMap fun y => ratios.filterMap fun z =>
    if x.1*y.2 ≤ y.1*x.2 ∧ y.1*z.2 ≤ z.1*y.2 ∧
        ratioCompatible x y ∧ ratioCompatible x z ∧ ratioCompatible y z then
      let d := x.2.lcm (y.2.lcm z.2)
      some #v[d, d/x.2*x.1, d/y.2*y.1, d/z.2*z.1]
    else none

def fiveFrontier : List (Vector Nat 5) :=
  (vectors 5 18 1).filter fun p => 10 < p[4] && mixed p

def cores : List (Vector Nat 4) := [#v[1,1,1,1], #v[1,1,1,3], #v[1,1,2,2]]

def appendSlope (p : Vector Nat 4) (n : Nat) : Vector Nat 5 := p.push n

def fourCatalogueCheck : Bool :=
  fourCatalogue.length == 313 && fourCatalogue.all fun p => (replay p [1,2]).isEmpty

def fiveFrontierCheck : Bool :=
  fiveFrontier.length == 22939 && fiveFrontier.all fun p => (replay p [1,2]).isEmpty

def appendSlopeCheck : Bool :=
  cores.all fun p => (List.range' 11 (26*p[3]-11)).all fun n =>
    (replay (appendSlope p n) [1,2]).isEmpty

end Fresh.Harmonic
