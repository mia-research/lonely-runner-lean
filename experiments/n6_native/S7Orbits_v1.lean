import Mathlib

/-!
# BHK §7: which meeting-time orbits miss the parallelogram (n6_native, E55)

At the meeting times `k/D` of BHK §7 runners 2 and 3 coincide; the point `({k c₃/n}, {k c₁/n})` of the orbit
`⟨(c₃, c₁)⟩ ⊂ (ℤ/n)²` lies in BHK's parallelogram `P` (a full 3-gap that is a 123-gap) for the ratio `ρ = v₁/v₃`
exactly when `ρ` is at most a bound attached to the point. In §7, `ρ < 1/3`, so the main route can fail only
for an orbit with no point in `P_{1/3}`. In whole numbers, a point `(x/n, y/n)` lies in `P_{1/3}` iff
`n ≤ 6x ≤ 5n` and `6x + 2n ≤ 18y ≤ 10n + 6x` (`inP`).

`check_orbits`: for every order `2 ≤ n ≤ 35` and generator `(a, b)` off the axes with `gcd(a, b, n) = 1`, the
orbit has a point in `P_{1/3}` unless it is `G₄` (`n = 4`, `a ≡ 2`, `b` odd) or `G₇` (`n = 7`, `a ≡ 2b`,
`b ≢ 0`). One kernel computation. For `n ≥ 36`, `orbit_isolation_two_bhk` (framework) with the short-step
bounds of E55 leaves no failure.
-/

namespace N6Native

/-- The point `(x/n, y/n)` lies in BHK's parallelogram at ratio `1/3`. -/
def inP (n x y : ℕ) : Bool := n ≤ 6 * x && 6 * x ≤ 5 * n && 6 * x + 2 * n ≤ 18 * y && 18 * y ≤ 10 * n + 6 * x

/-- BHK's two exceptional orbits. -/
def isExc (n a b : ℕ) : Bool :=
  (n == 4 && a % 4 == 2 && b % 2 == 1) || (n == 7 && b % 7 != 0 && a % 7 == (2 * b) % 7)

def orbitHits (n a b : ℕ) : Bool := (List.range n).any fun k => inP n ((a * k) % n) ((b * k) % n)

def check (N : ℕ) : Bool :=
  (List.range (N + 1)).all fun n => (List.range n).all fun a => (List.range n).all fun b =>
    !(2 ≤ n && 1 ≤ a && 1 ≤ b && Nat.gcd (Nat.gcd a b) n == 1) || isExc n a b || orbitHits n a b

set_option maxHeartbeats 0 in
theorem check_orbits : check 35 = true := by decide +kernel

/-- The finite check, unpacked. -/
theorem orbit_hits_or_exc {n a b : ℕ} (hn2 : 2 ≤ n) (hn : n ≤ 35) (ha : 1 ≤ a) (han : a < n) (hb : 1 ≤ b)
    (hbn : b < n) (hg : Nat.gcd (Nat.gcd a b) n = 1) :
    isExc n a b = true ∨ ∃ k < n, inP n ((a * k) % n) ((b * k) % n) = true := by
  have h := check_orbits
  simp only [check, List.all_eq_true, List.mem_range] at h
  have := h n (by omega) a han b hbn
  simp only [Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not,
    not_le, beq_eq_false_iff_ne, ne_eq] at this
  rcases this with ((((h1 | h1) | h1) | h1) | h1) | h1
  · omega
  · omega
  · omega
  · exact absurd hg h1
  · exact Or.inl h1
  · right
    simp only [orbitHits, List.any_eq_true, List.mem_range] at h1
    obtain ⟨k, hk, hk'⟩ := h1
    exact ⟨k, hk, hk'⟩

/-- The exceptional orbits really miss `P_{1/3}`. -/
theorem g4_misses : orbitHits 4 2 1 = false := by decide
theorem g7_misses : orbitHits 7 2 1 = false := by decide

end N6Native

#print axioms N6Native.check_orbits
#print axioms N6Native.orbit_hits_or_exc
#print axioms N6Native.g4_misses
#print axioms N6Native.g7_misses
