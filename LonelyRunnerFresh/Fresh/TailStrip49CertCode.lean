import Fresh.TailStrip49Compute

/-!
# Compact certificate codes for the 49–51 strip (E929): definitions only

Written 2026-11-25.  New file; imports only `Init` (through `TailStrip49Compute`), so the generated data files that
import it start quickly.  Soundness is in `Fresh.TailStrip49CodeSound`.

A certificate for a box is one natural number, read from its low bits:
* bit 0 = 0: a leaf.  The next 20 bits are cell `c`, the 20 after that cell `d`; each cell is a 10-bit low bound
  and a 10-bit high bound.  A bound code `128·src + j` names `(8j+1)/(box.lo src)` (low) or `(8j+7)/(box.hi src)`
  (high) when `src < 5`, and the window endpoint `1, 9` (low) or `7, 15` (high), over `scale`, when `src = 5`.
* bit 0 = 1: a split, as in `coverWith`.  The next 24 bits are the length `L` in bits of the left child's code;
  then the left code (`L` bits), then the right code.

Every cell the native search produces has this form, because `Ratio.max` and `Ratio.min` return one of their
arguments.  Soundness does not depend on that: any decoded cells that pass `pairCheckN` give the conclusion.
-/

namespace Fresh.TailStrip49Cert

open Fresh.TailStrip49

/-- `pairCheck` with the blocker scan restricted to the lap range `blockers` computes. -/
def pairCheckN (box : Box) (c d : Cell) : Bool :=
  let lo := max minTop (box.lo 4)
  slowCheck box c && slowCheck box d && separate (blockers c lo) (blockers d lo)

def faceLo (box : Box) : Nat → Nat
  | 0 => box.lo 0
  | 1 => box.lo 1
  | 2 => box.lo 2
  | 3 => box.lo 3
  | _ => box.lo 4

def faceHi (box : Box) : Nat → Nat
  | 0 => box.hi 0
  | 1 => box.hi 1
  | 2 => box.hi 2
  | 3 => box.hi 3
  | _ => box.hi 4

def boundLo (box : Box) (code : Nat) : Ratio :=
  if code / 128 < 5 then ⟨8 * (code % 128) + 1, faceLo box (code / 128)⟩
  else if code % 128 = 0 then ⟨1, scale⟩ else ⟨9, scale⟩

def boundHi (box : Box) (code : Nat) : Ratio :=
  if code / 128 < 5 then ⟨8 * (code % 128) + 7, faceHi box (code / 128)⟩
  else if code % 128 = 0 then ⟨7, scale⟩ else ⟨15, scale⟩

def decodeCell (box : Box) (code : Nat) : Cell :=
  ⟨boundLo box (code % 1024), boundHi box (code / 1024 % 1024)⟩

/-- Check a coded certificate on a box, with recursion depth `d`. -/
def checkCode : Nat → Box → Nat → Bool
  | 0, _, _ => false
  | d+1, box, code =>
    if code % 2 = 0 then
      pairCheckN box (decodeCell box (code / 2 % 1048576)) (decodeCell box (code / 2097152 % 1048576))
    else
      checkCode d (left box (widest box)) (code / 33554432 % 2 ^ (code / 2 % 16777216)) &&
      checkCode d (right box (widest box)) (code / 33554432 / 2 ^ (code / 2 % 16777216))

/-- The box reached from `b` by a path of halvings (`false` = left, `true` = right), as in `coverWith`. -/
def boxAt (b : Box) (p : List Bool) : Box :=
  p.foldl (fun b x => if x then right b (widest b) else left b (widest b)) b

/-- The box of a root tuple. -/
def rootOf (t : Nat × Nat × Nat × Nat × Nat) : Box := root t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2

/-- The roots of slice `a`, in the order of `checkFirstWith`, as tuples. -/
def rootTuples (a : Nat) : List (Nat × Nat × Nat × Nat × Nat) :=
  (List.range' a (27-a)).flatMap fun b =>
  (List.range' b (27-b)).flatMap fun c =>
  (List.range' c (27-c)).flatMap fun d =>
  (List.range' d (27-d)).map fun e => (a,b,c,d,e)

/-- A run of consecutive roots of slice `a`, from index `s`, each with its code. -/
def codeChunkOK (a s : Nat) (codes : List Nat) : Bool :=
  let ts := ((rootTuples a).drop s).take codes.length
  decide (ts.length = codes.length) && (ts.zip codes).all fun p => checkCode 40 (rootOf p.1) p.2

end Fresh.TailStrip49Cert
