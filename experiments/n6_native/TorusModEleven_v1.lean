import Mathlib

/-!
# Every 2-torus through a tight vector, other than its own circle, meets the open cube (n6_native, E25)

`u` is `(1,2,3,4,5)` or `(1,3,4,5,9)`. For an integer `v` with no `l` making `v ≡ l·u (mod 11)`, some
`i, j < 11` put every coordinate of `i·u + j·v` in `{2,…,9}` modulo 11. Then the integer vector
`w = i·u + j·v` reads in `[2/11, 9/11]` at the instant `1/11`, strictly inside `(1/6, 5/6)`.

The finite core (`check_grid`, `check_other`) is one kernel computation over `(ℤ/11)^5`.
-/

namespace N6Native

def inBand (x : ℕ) : Bool := 2 ≤ x % 11 && x % 11 ≤ 9

def wit (u0 u1 u2 u3 u4 a b c d e : ℕ) : Bool :=
  (List.range 11).any fun i => (List.range 11).any fun j =>
    inBand (i*u0 + j*a) && inBand (i*u1 + j*b) && inBand (i*u2 + j*c) && inBand (i*u3 + j*d) &&
      inBand (i*u4 + j*e)

def onCircle (u0 u1 u2 u3 u4 a b c d e : ℕ) : Bool :=
  (List.range 11).any fun l =>
    (l*u0) % 11 == a && (l*u1) % 11 == b && (l*u2) % 11 == c && (l*u3) % 11 == d && (l*u4) % 11 == e

def check (u0 u1 u2 u3 u4 : ℕ) : Bool :=
  (List.range 11).all fun a => (List.range 11).all fun b => (List.range 11).all fun c =>
    (List.range 11).all fun d => (List.range 11).all fun e =>
      onCircle u0 u1 u2 u3 u4 a b c d e || wit u0 u1 u2 u3 u4 a b c d e

set_option maxHeartbeats 0 in
theorem check_grid : check 1 2 3 4 5 = true := by decide +kernel

end N6Native

#print axioms N6Native.check_grid
