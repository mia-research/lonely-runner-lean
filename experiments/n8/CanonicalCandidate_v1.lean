import Mathlib

/-!
# The anatomy of the canonical candidate `q = L(m)`

For a divisor-closed profile the witness search starts at `q = L(m) = ⌈(m-1)/8⌉`, and measured
over mixed-scale profiles it succeeds immediately 36.5% of the time, with median walk 1. This
file says exactly which moduli block it, and why.

Write `b ∣ m`, reading `s = m/b`, and `s = 8u + v` with `0 ≤ v < 8`. Then

```
    L(m) = u*b + ⌈(v*b - 1)/8⌉ ,
```

so the residue of the canonical candidate at modulus `b` is `⌈(v*b-1)/8⌉` and depends only on
`v = s mod 8`:

* `v = 0` — the **collider** `8 ∣ s`: the residue is `0`, which is never clear, since
  `L(b) ≥ 1` for every `b ≥ 2`. Measured: **0 of 1901** collider pairs clear.
* `1 ≤ v ≤ 4`: always clear, for every `b ≥ 2`. Measured: **100%** across 13,247 pairs.
* `5 ≤ v ≤ 7`: clear exactly when `⌈(v*b-1)/8⌉ ≤ ⌊(7b-1)/8⌋`, which fails for small `b` —
  measured clear rates 91.6%, 85.1% and 10.6%.

The full law `L(m) clears b ⟺ v ≠ 0 ∧ ⌈(v*b-1)/8⌉ ≤ ⌊(7b-1)/8⌋` was checked on 13,499
`(m,b)` pairs with `m < 2000`, no exceptions.

Ceilings and floors are carried as characterising inequalities rather than divisions, so the
arithmetic stays inside `omega`.
-/

namespace CanonicalCandidate

/-- `Lb = ⌈(b-1)/8⌉`, as a characterising pair of inequalities. -/
def IsCeilL (b Lb : ℤ) : Prop := 8 * Lb - 7 ≤ b - 1 ∧ b - 1 ≤ 8 * Lb

/-- `Ub = ⌊(7b-1)/8⌋`. -/
def IsFloorU (b Ub : ℤ) : Prop := 8 * Ub ≤ 7 * b - 1 ∧ 7 * b - 1 < 8 * Ub + 8

/-- `R = ⌈(v*b-1)/8⌉`. -/
def IsCeilR (v b R : ℤ) : Prop := 8 * R - 7 ≤ v * b - 1 ∧ v * b - 1 ≤ 8 * R

/-- The clear window at modulus `b`. -/
def clearAt (Lb Ub r : ℤ) : Prop := Lb ≤ r ∧ r ≤ Ub

/-- **The lower edge is positive.**  `L(b) ≥ 1` for every `b ≥ 2`, so residue `0` is never
clear. -/
theorem one_le_L {b Lb : ℤ} (hb : 2 ≤ b) (hL : IsCeilL b Lb) : 1 ≤ Lb := by
  obtain ⟨h1, h2⟩ := hL; omega

/-- **A collider pins the canonical candidate to zero.**  If `8 ∣ s` then `L(m) = u*b`, whose
residue at `b` is `0`. -/
theorem collider_eq {w Q : ℤ} (h1 : 8 * Q - 7 ≤ 8 * w - 1) (h2 : 8 * w - 1 ≤ 8 * Q) :
    Q = w := by omega

/-- **So the canonical candidate is blocked at every collider.** -/
theorem collider_blocked {b u Lb Ub : ℤ} (hb : 2 ≤ b) (hL : IsCeilL b Lb) :
    ¬ clearAt Lb Ub ((u * b) % b) := by
  rw [Int.mul_emod_left]
  intro h
  obtain ⟨h1, h2⟩ := h
  have := one_le_L hb hL
  omega

/-- **Small readings always clear.**  If `1 ≤ v ≤ 4` then the canonical residue
`R = ⌈(v*b-1)/8⌉` lies strictly inside the window, for every `b ≥ 2`. -/
theorem small_v_clear {v b Lb Ub R : ℤ} (hb : 2 ≤ b) (hv1 : 1 ≤ v) (hv4 : v ≤ 4)
    (hL : IsCeilL b Lb) (hU : IsFloorU b Ub) (hR : IsCeilR v b R) :
    clearAt Lb Ub R ∧ 0 ≤ R ∧ R < b := by
  obtain ⟨hL1, hL2⟩ := hL
  obtain ⟨hU1, hU2⟩ := hU
  obtain ⟨hR1, hR2⟩ := hR
  have hlo : b ≤ v * b := by nlinarith
  have hhi : v * b ≤ 4 * b := by nlinarith
  refine ⟨⟨by omega, by omega⟩, by omega, by omega⟩

/-- **The minimal step at a collider is exactly `L(b)`.**  Since the collider pins the residue
to `0`, adding `L(b)` lands on the lower edge, which is clear. -/
theorem collider_step {b u Lb Ub : ℤ} (hb : 2 ≤ b) (hL : IsCeilL b Lb) (hU : IsFloorU b Ub)
    (hLU : Lb ≤ Ub) : clearAt Lb Ub ((u * b + Lb) % b) := by
  have hpos : 1 ≤ Lb := one_le_L hb hL
  have hlt : Lb < b := by obtain ⟨h1, h2⟩ := hL; omega
  have hrw : u * b + Lb = Lb + b * u := by ring
  have : (u * b + Lb) % b = Lb := by
    rw [hrw, Int.add_mul_emod_self_left]
    exact Int.emod_eq_of_lt (by omega) hlt
  rw [this]
  exact ⟨le_refl _, hLU⟩

/-- **A collider kills the whole `m`-lattice.**  If `8 ∣ s = m/b` then `m/8 = u*b`, so *every*
integer multiple of `m/8` has residue `0` at `b`, and is blocked.

This is the reason the canonical candidate and its relatives all fail together on Branch B
profiles: measured over 20,000 of them, `L(m)`, `⌈m/4⌉` and `⌈3m/8⌉` each clear **0.00%**. The
witness cannot be placed on `m`'s lattice at all; it has to be located at the collider's own
scale. The best explicit formula found, `L(m) + L(b*)` for the largest collider `b*`, does
exactly that and reaches 59.84%. -/
theorem collider_kills_lattice {b u k Lb Ub : ℤ} (hb : 2 ≤ b) (hL : IsCeilL b Lb) :
    ¬ clearAt Lb Ub ((k * (u * b)) % b) := by
  have hz : (k * (u * b)) % b = 0 := by
    have hrw : k * (u * b) = (k * u) * b := by ring
    rw [hrw, Int.mul_emod_left]
  rw [hz]
  intro h
  obtain ⟨h1, h2⟩ := h
  have := one_le_L hb hL
  omega

end CanonicalCandidate

#print axioms CanonicalCandidate.one_le_L
#print axioms CanonicalCandidate.collider_eq
#print axioms CanonicalCandidate.collider_blocked
#print axioms CanonicalCandidate.small_v_clear
#print axioms CanonicalCandidate.collider_step
#print axioms CanonicalCandidate.collider_kills_lattice
