import Mathlib

/-!
# Every 2-torus through a tight vector, other than its own circle, meets the open cube (n6_native, E25)

`u` is `(1,2,3,4,5)` or `(1,3,4,5,9)` (first coordinate `1`). Replacing `v` by `v - v₀·u` does not change
the torus `{s u + t v}`, so the finite core takes `v₀ = 0`: for `(b,c,d,e) ∈ (ℤ/11)^4` not zero, some
`i, j < 11` put every coordinate of `i·u + j·(0,b,c,d,e)` in `{2,…,9}` modulo 11 (`check_grid`,
`check_other`, kernel computations). `torus_witness` lifts this to every integer `v` that is not
congruent to a multiple of `u` modulo 11, with the witness `i·u + j·v` (`i, j` integers). Its
coordinates read in `[2/11, 9/11]` at the instant `1/11`, strictly inside `(1/6, 5/6)`
(`witness_lonely`).
-/

namespace N6Native

def inBand (x : ℕ) : Bool := 2 ≤ x % 11 && x % 11 ≤ 9

def wit (u1 u2 u3 u4 b c d e : ℕ) : Bool :=
  (List.range 11).any fun i => (List.range 11).any fun j =>
    inBand i && inBand (i*u1 + j*b) && inBand (i*u2 + j*c) && inBand (i*u3 + j*d) &&
      inBand (i*u4 + j*e)

def check (u1 u2 u3 u4 : ℕ) : Bool :=
  (List.range 11).all fun b => (List.range 11).all fun c =>
    (List.range 11).all fun d => (List.range 11).all fun e =>
      (b == 0 && c == 0 && d == 0 && e == 0) || wit u1 u2 u3 u4 b c d e

set_option maxHeartbeats 0 in
theorem check_grid : check 2 3 4 5 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_other : check 3 4 5 9 = true := by decide +kernel

end N6Native

#print axioms N6Native.check_grid
#print axioms N6Native.check_other
