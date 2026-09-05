# Following the ⟨σ,χ2⟩ conservation — the reflection mechanism, and why it lives outside F_p

Date: 2026-07-19. Script `_reflection_symmetry_hunt_v1.py` (+ `_sigma_chi2_scan_v1`). Conservation-
hunt step in the mantra sense: take an EXACT law, find the symmetry that enforces it, look outside
that symmetry. Object = the flap sign σ (μ2-odd, μ3-invariant part of the μ6 action on the
x-coordinate) and the quadratic character χ2, paired over the field.

## The exact conservation (confirmed, 16/16)
`FLD(p) := Σ_{x∈F_p} σ(x)·χ2(x)`. Over p∈[100,1300), p≡1 mod 6, #E prime:
**`FLD(p) ≠ 0  ⟺  p ≡ 3 mod 8`** — nonzero only at p ∈ {163, 211, 547, 907, 1051} (all ≡3 mod 8);
exactly 0 at every p ≡ 1, 5, 7 mod 8. The **p ≡ 7 mod 8 zeros are NOT forced by the μ6 selection
rule** (this is the "not-forced" part the hunt targets; the p≡1 mod 4 zeros are the forced ones).

## The mechanism, followed (rule 13: name a candidate, try to KILL it)
Prior session killed the **multiplicative** candidate: no c∈F_p* with σ·χ2(cx) = −σ·χ2(x). This
session tested the **reflection** candidate — the 6 D₆ reflections z→ζ₆ᵏ z̄ (conjugation ω→ω²
composed with the μ6 rotations), realized as maps R_k(x) = βᵏ·(±1)·τ(x), τ = the ω→ω² substitution
on the Eisenstein lift eis(x).

**KILLED, exactly: 0/16 curves have any R_k with `σ·χ2(R_k x) = −σ·χ2(x)` for all x.**

## Why it is killed — the finding, not a bug
`τ` is **not an involution** (`tau_inv=False`) and **not multiplicative** (`tau_mult=False`) at
every p. This is not a construction defect: conjugation ω→ω² **does not descend to the prime field
F_p**. F_p has no nontrivial field automorphism; the lattice reflection sends the ideal (π_p) to the
**conjugate prime (π̄_p) = the twist / amicable partner**, not back into (π_p). So the reflection is
not an F_p set-map of the required form, and `τ` — being forced to pick a lift representative via
`eis` — cannot close into an involution. The symmetry that would enforce the conservation is
**genuinely outside F_p**, exactly the mantra's prediction.

Consequence: the conservation `FLD≠0 ⟺ p≡3 mod 8` is enforced by **no within-F_p symmetry** — μ6
rotations do not force it, and F_p reflections do not exist. It is an arithmetic (mod-8) law whose
enforcement is external to the field.

## Where the enforcement lives, and how it differs from the flap law
Same geometric setting as the **proven** flap parity law `(−1)^ORB = χ2(2) = (−1)^{(p²−1)/8}`
(`_flap_parity_law_v1.py`): Eisenstein lattice-point counts in the rhombus, where p mod 8 enters via
Gauss's lemma. **But the conservation is a FINER mod-8 law than χ2(2):** χ2(2) only separates
p≡±1 mod 8 from p≡±3 mod 8, so it cannot distinguish 3 from 7 mod 8 — yet the conservation does
(nonzero at 3, zero at 7). So `FLD` is not χ2(2); it is a distinct mod-8 lattice invariant.

## Next mechanism (named, not yet run)
Reduce `FLD(p)` to an Eisenstein-triangle **lattice-point-count parity** (the setting that proved the
flap law), and derive: (i) the p≡3 mod 8 nonvanishing, (ii) why p≡7 mod 8 gives exactly 0 despite
also being 3 mod 4 with χ2(2)=−1. The separation of 3 vs 7 mod 8 is the load-bearing target — it is
what no character of conductor ≤ 8 on its own explains, so it names a second lattice object.

## Scope / exactness
Exact integers throughout (eis, ω_p, σ, χ2). p∈[100,1300), p≡1 mod 6, #E(y²=x³+7) prime. 16 curves.
No float in the signal path. The kill is over ALL x (exact), not a statistical null.
