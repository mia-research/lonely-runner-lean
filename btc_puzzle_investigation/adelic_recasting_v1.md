# Adelic recasting of the φ(n)-framework — resolving the circle/line obstruction
2026-07-10. Verifies the operator-side obstruction (multiplicative circle B vs
additive line C) is not a defect but the signature that the framework's true home
is the idele class group, where B and C are two factors of one group. Grounds the
CM version and the μ₆ sextic decoration concretely (Grossencharacter verified).

## 0. The obstruction (recap, from radial_selfadjointness.md)
- **B** = D_φ = span{e^{±iy}} — the multiplicative averaging domain — wants the
  **circle** (discrete unit-modes, the compact dual of a units group).
- **C** = Mellin probes x^s, s ∈ ℂ — where the zeros live — wants the **line**
  (continuous spectral parameter).
- No boundary condition on ℝ_{>0} bridges them: Ĥ=πA² has deficiency indices
  (1,1) on [1,∞), and a self-adjoint extension picks ONE circle of phase, which
  cannot simultaneously be the continuous line. Circle and line are different
  spaces; naming a boundary condition can't merge two spaces.

## 1. The adele resolves it: B and C are two factors of ONE group
Idele class group of ℚ:  C_ℚ = 𝔸_ℚ^* / ℚ^*  ≅  ℝ_{>0} × Ẑ^*  (Ẑ^* = ∏_p ℤ_p^*).
- **ℝ_{>0}** (archimedean scaling) = the **LINE** = home of Ĥ=πA² and the zeros.
- **Ẑ^* = ∏_p ℤ_p^*** (finite compact units) = the **CIRCLE(s)** = home of the
  P_n averaging and the k=±1 survival.
They are two DIRECT FACTORS of the same locally compact group. Nothing bridges
them because they were never separate — the framework split one object across
places and then noticed the halves don't live on a common ℝ_{>0}. On C_ℚ they do.

### "Line as an incomplete circle" (the user's tool) = the archimedean view
The line ℝ is ONE place. Each finite place ℚ_p carries a compact ℤ_p^* (a circle).
The archimedean line is "incomplete" precisely in that it lacks the finite-place
circles that complete it into the idele. Treating the line as an incomplete
circle is the archimedean-place picture of the adelic completion — it is the
right instinct, and §3 shows it becomes an EXACT polar decomposition in the CM case.

## 2. The dictionary (framework object ↔ adelic object)
| φ(n)-framework                         | adelic / idele class group of ℚ                    |
|----------------------------------------|-----------------------------------------------------|
| Ĥ = πA² on L²(ℝ_{>0}, dx/x)            | scaling action on archimedean ℝ_{>0} (LINE, zeros)  |
| P_n averaging over (ℤ/n)^*             | projection onto ∏_{p|n} ℤ_p^* (finite CIRCLE units) |
| survival k=±1                           | trivial finite idele class character (units of ℤ)   |
| D_φ = span{e^{±iy}} modes              | idele class (Hecke) characters                      |
| spectral wall E(σ) ≥ (4/π²)κσ²log N    | Weil explicit formula = trace over C_ℚ              |
| zeros of ζ / L                          | spectrum ("absorption") of the scaling action       |
This is Connes' adele class space; the framework is a units-averaged slice of it.

## 3. CM version (K = ℚ(√−3)) — where the obstruction is MILDEST
Replace ℚ by K. Idele class group C_K = 𝔸_K^*/K^*. The one archimedean place of K
is **COMPLEX**: K⊗ℝ = ℂ, so the archimedean factor is
        **ℂ^*  =  ℝ_{>0} × S¹  (polar decomposition)**.
- The **radial** ℝ_{>0} = the LINE (Ĥ, the CM scaling, the zeros of the Hecke L).
- The **angular** S¹ = a GENUINE circle AT INFINITY — and ℤ[ω]^* = **μ₆ ⊂ S¹**.

So for K the circle and the line sit at the SAME (archimedean) place, as the two
polar factors of ℂ^*. B (the S¹/μ₆) and C (the ℝ_{>0}/scaling) need no finite
places to be bridged — one complex place carries both. **This is strictly cleaner
than ℚ**, whose archimedean units are only {±1} (a degenerate 2-point "circle"),
forcing the multiplicative circle to come from the finite places. The CM curve's
complex place gives the line and the circle together, natively. The user's
"line as incomplete circle" is here an equality: ℂ^* = (radial line) × (angular circle).

### The Grossencharacter couples line and circle (verified)
The Hecke Grossencharacter ψ of secp256k1 has infinity type (1,0): on ℂ^* it acts
by z ↦ z, i.e. (r,θ) ↦ r·e^{iθ} — it MIXES the radial line and the angular circle.
For split primes ℓ ≡ 1 (mod 3), ℓ = π·π̄ in ℤ[ω], and
        **a_ℓ = ψ(𝔭) + ψ(𝔭̄),   ψ(𝔭) = u·π,   u ∈ μ₆ = the sextic residue character.**
Verified (2Re(u·π) = a_ℓ) for ℓ = 13,19,31,37,43,61,67,73,79 — exact hit each time
(ℓ=7 excluded: 7 | conductor). So μ₆ is literally the angular (S¹) decoration of ψ
at the complex place, and it is ORTHOGONAL to the radial obstruction: the sextic
structure rides on S¹ and survives the recasting intact.

## 4. What is genuinely new here vs. known (Connes)
- **Known / borrowed:** the adele class space and "zeros = spectrum of scaling"
  are Connes–Bost–Consani. The φ(n)-framework recasting is a units-averaged slice.
- **The observation that is ours and clean:** the CM field ℚ(√−3) is the natural
  home of this framework because its complex archimedean place ℂ^* = ℝ_{>0} × S¹
  already contains BOTH the line and the circle as polar factors, with μ₆ sitting
  in S¹ — so the circle/line obstruction that is forced and awkward over ℚ is
  native and mild over K. The Grossencharacter's (1,0) infinity type is the exact
  operator coupling the two. This reframes the analytic gap as "use the complex
  place, not the real line," and tells us the sextic μ₆ is a decoration, not a wall.

## 4b. TEST — "line as incomplete circle" vs ℂ^* polar + μ₆-averaging  [PASSES]
Canonical construction: complete the radial line ℝ_{>0} (log-coord u ∈ [0,L]) to a
circle of circumference L with a boundary twist α (ψ(L)=e^{iα}ψ(0)). The twist α is
exactly the von Neumann extension parameter. Numerics (N=1200 grid, Ĥ=πA²):
- **(1) Self-adjointness resolved.** Twisted-circle BC ⇒ ‖Ĥ−Ĥ†‖=0, max|Im λ|~1e-10:
  REAL discrete spectrum for EVERY twist α (α=0, π/3, 1.0 all checked). The
  deficiency-(1,1) obstruction is not a wall — it is the CIRCLE of completions,
  one self-adjoint Ĥ per point of S¹.
- **(2) μ₆-averaging survives.** The extension parameter is S¹; μ₆ acts by
  α_j = 2πj/6; the six A-spectra are the evenly-shifted lattices (α_j+2πk)/L, which
  tile to a uniform μ₆-invariant density. Averaging is well-defined and selects the
  6th-roots-of-unity twists.
- **(3) Matches ℂ^*.** Those μ₆-selected twists α_j = 2πj/6 ARE the 6th roots of
  unity in S¹ = ℤ[ω]^* = μ₆ — the same angular S¹ that carries ψ(𝔭)=u·π (§3).
So the deficiency circle = the completion circle = the angular S¹ of ℂ^*, and the
sextic μ₆ is the set of 6 canonical self-adjoint completions of the radial line.
The obstruction I flagged as a wall is reinterpreted as the parametrization of
completions, with μ₆ picking the distinguished ones.

**Scope of the test:** this is a CONSISTENCY/model result. The discrete spectrum
here is the free lattice {(α+2πk)/L} — a regularized model, NOT the ζ/Hecke zeros.
Getting the actual zeros needs the correct scaling operator + measure/cutoff on
𝔸_K/K^* (where the conductor/κ(L) enters). The test confirms the construction is
compatible with the ℂ^* structure and survives μ₆; it does not produce the zeros.

## 5. Honest scope
This is a recasting + a structural observation, not a proof of RH or of the Hecke
L GRH. It says WHERE the framework wants to live and WHY the CM version is the
natural one, and it grounds μ₆ as the archimedean-S¹ decoration concretely. The
open work is analytic: realize the zeros of the Hecke L-function as the spectrum
of a self-adjoint scaling operator on L²(𝔸_K/K^*) — Connes' program, now with the
sextic S¹ as extra symmetry. The user's "line as incomplete circle" plugs in at
§3 as the polar decomposition of ℂ^*; the specifics of that construction are the
next thing to fold in.
