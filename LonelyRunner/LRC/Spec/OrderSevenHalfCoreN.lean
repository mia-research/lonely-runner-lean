import LonelyRunner.LRC.Spec.OrderSevenL3BCoreN

/-!
# Order seven, half-unit certificates (band symmetry `u ↔ 7^a − u`)

Indices `0..146` of `unitL3` are the units `1..171`; indices `0..20` of `unit49` are the units `1..24`.  Since a speed and
its negative are in band at the same instants, it suffices to check these halves.
Generator: `experiments/n7_native/cascade/o7_half_lean_v1.py`.
-/

namespace LRC.O7L3
open LRC.O7Grid

def chunkAH (i2 lo3 hi3 : ℕ) : Bool :=
  let a := maskL3 0 &&& maskL3 i2
  allR (hi3 - lo3) lo3 fun i3 => let b := a &&& maskL3 i3
    allR (147 - i3) i3 fun i4 => let c := b &&& maskL3 i4
      allR (147 - i4) i4 fun i5 => (c &&& maskL3 i5) != 0

def chunkBH (i2 lo3 hi3 : ℕ) : Bool :=
  let a := maskL3 0 &&& maskL3 i2
  allR (hi3 - lo3) lo3 fun i3 => let b := a &&& maskL3 i3
    allR (147 - i3) i3 fun i4 => let c := b &&& maskL3 i4
      allR 21 0 fun t => (c &&& mmL3 t) != 0

def mask2Tab : Array ℕ := #[68719476672, 549739298808, 1098504933372, 2191499194878, 2168907955326, 2147077824318, 4326001898463, 4187181784527, 4251427073775, 3967400245095, 4086372883383, 4083938684343, 3838336947963, 3759639849819, 3762235490139, 3809325276603, 4216512280239, 4249190378223, 3276967345533, 3021878503413, 2909840341653, 2909840341653, 3021878503413, 3276967345533, 4249190378223, 4216512280239, 3809325276603, 3762235490139, 3759639849819, 3838336947963, 4083938684343, 4086372883383, 3967400245095, 4251427073775, 4187181784527, 4326001898463, 2147077824318, 2168907955326, 2191499194878, 1098504933372, 549739298808, 68719476672]

def mask2 (i : ℕ) : ℕ := mask2Tab.getD i 0

def failH : List (ℕ × ℕ × ℕ × ℕ) := [(2, 3, 4, 15), (2, 6, 16, 18), (3, 5, 8, 9), (3, 5, 8, 18), (3, 15, 17, 18), (4, 5, 16, 17), (4, 6, 7, 11), (4, 10, 16, 17), (5, 12, 13, 15), (6, 8, 14, 15), (6, 14, 15, 17), (7, 8, 13, 16), (9, 10, 11, 17), (10, 12, 18, 19), (10, 16, 18, 19)]

def chunkC1 : Bool :=
  allR 21 0 fun a => let x := mask2 0 &&& mask2 a
    allR (21 - a) a fun b => let y := x &&& mask2 b
      allR (21 - b) b fun c => let z := y &&& mask2 c
        allR (21 - c) c fun d => (z &&& mask2 d) != 0 || failH.contains (a, b, c, d)

def idx343 (v : ℕ) : ℕ := v - 1 - v / 7

def chunkC2 (p : ℕ) : Bool :=
  let f := failH.getD p (0, 0, 0, 0)
  allR 7 0 fun x2 => allR 7 0 fun x3 => allR 7 0 fun x4 => allR 7 0 fun x5 =>
    let m := maskL3 0 &&& maskL3 (idx343 (unit49 f.1 + 49 * x2)) &&& maskL3 (idx343 (unit49 f.2.1 + 49 * x3)) &&&
      maskL3 (idx343 (unit49 f.2.2.1 + 49 * x4)) &&& maskL3 (idx343 (unit49 f.2.2.2 + 49 * x5))
    allR 21 0 fun t => (m &&& mmL3 t) != 0

end LRC.O7L3
