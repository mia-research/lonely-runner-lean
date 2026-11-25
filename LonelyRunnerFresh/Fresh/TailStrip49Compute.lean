import Init

/-! Exact closed-cell arithmetic for the 49–51 strip. The search follows
the X24 cell-pair construction in the handoff. Slow coordinates are
subdivided independently of the last reading. -/

namespace Fresh.TailStrip49


def scale : Nat := 8388608
def minTop : Nat := 49 * scale
def maxTop : Nat := 51 * scale

structure Ratio where
  n : Nat
  d : Nat
  deriving Inhabited, Repr

def Ratio.le (p q : Ratio) : Bool := p.n * q.d ≤ q.n * p.d
def Ratio.lt (p q : Ratio) : Bool := p.n * q.d < q.n * p.d
def Ratio.max (p q : Ratio) : Ratio := if p.le q then q else p
def Ratio.min (p q : Ratio) : Ratio := if p.le q then p else q
def whole (n : Nat) : Ratio := ⟨n, 1⟩

structure Cell where
  lo : Ratio
  hi : Ratio
  deriving Inhabited, Repr

structure Box where
  lo : Fin 5 → Nat
  hi : Fin 5 → Nat

def slowIndices : List (Fin 5) := List.finRange 5

def slowStep (box : Box) (i : Fin 5) (cells : List Cell) : List Cell :=
  cells.flatMap fun c =>
    let start := (c.lo.n * box.hi i / c.lo.d - 7) / 8
    let stop := (c.hi.n * box.lo i / c.hi.d - 1) / 8
    (List.range' start (stop+1-start)).filterMap fun j =>
      let lo := c.lo.max ⟨8*j+1, box.lo i⟩
      let hi := c.hi.min ⟨8*j+7, box.hi i⟩
      if lo.le hi then some ⟨lo,hi⟩ else none

def cells (box : Box) : List Cell :=
  slowIndices.foldl (fun acc i => slowStep box i acc)
    [⟨⟨1,scale⟩,⟨7,scale⟩⟩, ⟨⟨9,scale⟩,⟨15,scale⟩⟩]

def faceCheck (c : Cell) (lo hi : Nat) : Bool :=
  let j := (c.lo.n * lo - c.lo.d) / (8*c.lo.d)
  decide ((8*j+1)*c.lo.d ≤ c.lo.n*lo) && decide (c.hi.n*hi ≤ (8*j+7)*c.hi.d)

def windowCheck (c : Cell) : Bool :=
  decide (0 < c.lo.n) && decide (0 < c.hi.n) &&
  decide (0 < c.lo.d) && decide (0 < c.hi.d) &&
  (⟨1,scale⟩ : Ratio).le c.lo && c.lo.le c.hi && c.hi.le ⟨15,scale⟩ &&
  (c.hi.le ⟨7,scale⟩ || (⟨9,scale⟩ : Ratio).le c.lo)

def slowCheck (box : Box) (c : Cell) : Bool :=
  windowCheck c && slowIndices.all fun i => faceCheck c (box.lo i) (box.hi i)

def obstruction (c : Cell) (j : Nat) : Cell :=
  ⟨⟨(8*j-1)*c.lo.d,c.lo.n⟩, ⟨(8*j+1)*c.hi.d,c.hi.n⟩⟩

def inTopBand (c : Cell) (lo : Nat) : Bool :=
  c.lo.lt c.hi && c.lo.lt (whole maxTop) && (whole lo).lt c.hi

def blockers (c : Cell) (lo : Nat) : List Cell :=
  let start := max 1 ((lo*c.lo.n/c.lo.d-1)/8)
  let stop := (maxTop*c.hi.n/c.hi.d+1)/8
  ((List.range' start (stop+1-start)).map (obstruction c)).filter (inTopBand · lo)

def checkedBlockers (c : Cell) (lo : Nat) : List Cell :=
  ((List.range' 1 95).map (obstruction c)).filter (inTopBand · lo)

def apart (p q : Cell) : Bool := p.hi.le q.lo || q.hi.le p.lo

def separate (bs cs : List Cell) : Bool := bs.all fun p => cs.all (apart p)

def findPair (lo : Nat) (prev : List (Cell × List Cell)) (cs : List Cell) : Option (Cell × Cell) :=
  match cs with
  | [] => none
  | c :: cs =>
    let bad := blockers c lo
    if bad.isEmpty then some (c,c)
    else
      match prev.find? (fun entry => separate entry.2 bad) with
      | some entry => some (entry.1,c)
      | none => findPair lo ((c,bad)::prev) cs

def pairCheck (box : Box) (c d : Cell) : Bool :=
  let lo := max minTop (box.lo 4)
  slowCheck box c && slowCheck box d &&
    separate (checkedBlockers c lo) (checkedBlockers d lo)

def cellCover (box : Box) : Bool :=
  match findPair (max minTop (box.lo 4)) [] (cells box) with
  | some (c,d) => pairCheck box c d
  | none => false

def widest (box : Box) : Fin 5 :=
  slowIndices.foldl (fun k i =>
    if (box.hi i-box.lo i)*box.lo k > (box.hi k-box.lo k)*box.lo i then i else k) 0

def mid (box : Box) (i : Fin 5) : Nat := (box.lo i+box.hi i)/2
def left (box : Box) (i : Fin 5) : Box :=
  ⟨box.lo, fun j => if j=i then mid box i else box.hi j⟩
def right (box : Box) (i : Fin 5) : Box :=
  ⟨fun j => if j=i then mid box i else box.lo j, box.hi⟩

def coverWith (accept : Box → Bool) (box : Box) (depth : Nat) : Bool :=
  if accept box then true else
    match depth with
    | 0 => false
    | n+1 => coverWith accept (left box (widest box)) n && coverWith accept (right box (widest box)) n


def centerFace (k : Nat) : Nat × Nat :=
  (max scale ((2*k-1)*scale), min maxTop ((2*k+1)*scale))

def root (a b c d e : Nat) : Box :=
  let fs (i : Fin 5) : Nat × Nat := match i.val with
    | 0 => centerFace a
    | 1 => centerFace b
    | 2 => centerFace c
    | 3 => centerFace d
    | _ => centerFace e
  ⟨fun i => (fs i).1, fun i => (fs i).2⟩

def checkFirstWith (accept : Box → Bool) (a : Nat) : Bool :=
  (List.range' a (27-a)).all fun b =>
  (List.range' b (27-b)).all fun c =>
  (List.range' c (27-c)).all fun d =>
  (List.range' d (27-d)).all fun e =>
  coverWith accept (root a b c d e) 32

def checkFirst := checkFirstWith cellCover

/-- Check a width of at least 1 / den in the R coordinate. -/
def wideCell (den : Nat) (c : Cell) : Bool :=
  decide (c.hi.d * c.lo.d + (den * scale) * c.lo.n * c.hi.d
    ≤ (den * scale) * c.hi.n * c.lo.d)

def widthCover (den : Nat) (box : Box) : Bool :=
  (cells box).any fun c => wideCell den c && slowCheck box c

/-- Clip to the cap; sorting makes every lower slow coordinate obey it. -/
def cappedWidthCover (cap den : Nat) (box : Box) : Bool :=
  decide (cap * scale < box.lo 4) ||
    widthCover den ⟨box.lo, fun i => min (cap * scale) (box.hi i)⟩

/-- The first `copies` unpinned slots repeat the pinned reading. -/
def paddedWidthCover (copies den : Nat) (box : Box) : Bool :=
  (List.finRange 5).any (fun i => decide (i.val < copies ∧ scale < box.lo i)) ||
    cappedWidthCover 17 den ⟨box.lo, fun i => if i.val < copies then scale else box.hi i⟩

def twoFastWidthCover := paddedWidthCover 1 10

end Fresh.TailStrip49
