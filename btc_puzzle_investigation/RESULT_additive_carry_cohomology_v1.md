# RESULT — the additive carry's class is the CONJUGATE Frobenius π̄_n; ε_LBE is its class-1 generator

**Grade: `[VERIFIED — exact; cohomology class computed, 2/2 curves; algebraic identity so scale-independent]`.**
Date 2026-08-17. Resolves the three open threads from `RESULT_group_carry_conservation_v1` (2-cochain class;
ε_LBE recast; additive↔multiplicative) — they collapse to one statement. Ties to the Frobenius-face synthesis
(`REFLECTIONS_frobenius_face_synthesis_v1`) and N16 (`ε_LBE`, master). Exact ℤ[ω]. No master edited.

## The three threads, resolved as one

**(1) The 2-cochain question — answered: non-trivial, class = π̄_n.**
`ε_add(a,b) = (D(a)+D(b)−D(a+b))/π_n` is the 2-cocycle `δD` of the extension
`0 → (π_n) → ℤ[ω] → ℤ/n → 0`. Verified a **2-cocycle** (`δε_add = 0`, 3000/3000). The extension is
**non-split** (ℤ[ω]≅ℤ² is torsion-free ⇒ no homomorphic section), so the class is non-trivial. Computed:
`class = Σ_{i=0}^{n-1} ε_add(1,i) = n·D(1)/π_n = π̄_n` (the **conjugate Frobenius**) — confirmed exactly:
`n=997 → (23,−13)=π̄_n`; `n=4999 → (62,−15)=π̄_n`. **`ε_add` is NOT a coboundary; its class is `π̄_n`.**

**(2) ε_LBE recast — `ε_add ~ π̄_n · ε_LBE`.**
The scalar carry `ε_LBE(a,b)=[a+b≥n]` (the N16 object, ℤ-valued) is the standard cyclic 2-cocycle, class `1`.
Verified `ε_add − π̄_n·ε_LBE` is a **coboundary** (class `0 mod n`, 2/2 curves). So in ℤ[ω]:
**`ε_add = π̄_n · ε_LBE + (coboundary)`.** `ε_LBE` is exactly the class-1 generator; the full Eisenstein
additive carry is `π̄_n` times it. N16's `ε_LBE` now has a clean cohomological identity.

**(3) additive ↔ multiplicative = the conjugate split `n = π_n·π̄_n`.**
- The **multiplicative** carry (`ĉ`, the island, the gate) is built **on `π_n`** (`ĉ = (ωD − D(λ·))/π_n`;
  `ω ≡ λ mod π_n`).
- The **additive** carry's cohomology **class is `π̄_n`**.
- So the two carry families are the **two primes above `n`** — the conjugate pair `(π_n, π̄_n)` of the CM
  split. The additive–multiplicative duality is not a coincidence; it **is** the splitting of `n` in ℤ[ω].
  (Compare the earlier orbit-bridge `ε₃=−(ĉ(1+ω)+ĉ(λ·))`: that links them *around the λ-orbit*; this links
  them *cohomologically* as `π_n` vs `π̄_n`. Two different, consistent handles.)

## Why this is a strong brick (not a break — stated plainly)
- It **completely characterizes the additive carry**: one non-trivial class, `= π̄_n`. The additive side is no
  longer a loose end — it is `π̄_n · ε_LBE` up to a coboundary.
- It gives **N16's `ε_LBE` a home**: the class-1 generator of `H²(ℤ/n, ℤ)`, lifted to ℤ[ω] with weight `π̄_n`.
  This does not leak `d` (a cohomology class is d-independent), and no such claim is made — but it tells any
  future `ε_LBE`-based probe *exactly* what algebraic object it is manipulating.
- It closes the additive/multiplicative picture on the **conjugate-split** axis, complementing the
  orbit-conservation (P17-twin) axis. The carry world now has: field/group faces (`Q(c)`), a ¾-gate on each,
  an orbit-conservation on each, and — this — a conjugate `π_n`/`π̄_n` split between multiplicative and additive.

## Scope / caveats
- The class computation `Σ_i ε_add(1,i) = π̄_n` is an exact algebraic identity (`Σ D(i) = Σ D(1+i)` cancels,
  leaving `n·D(1)/π_n = π̄_n`), so it holds at all scales; verified small (`n ≤ 4999`).
- "Class = π̄_n" is up to the chosen associate/lift convention (`D(1)=(1,0)`), like the other carry
  presentations; the *non-triviality* and the *`π_n` vs `π̄_n`* split are convention-independent.
- Cohomology class is d-homogeneous — structure, not a per-key leak. The per-key content lives in the
  *value* `ε_LBE(a,b)=[a+b≥n]`, whose cohomological weight this identifies as `π̄_n`.

## Where the additive/joint-set sides stand now
- **Additive side: characterized.** `ε_add = π̄_n·ε_LBE (+coboundary)`; class `π̄_n`. The one open additive
  object is resolved. What remains *open* is the **VALUE-level** per-key behavior of `ε_LBE` on structured key
  sets (the joint-set test), for which the forced symmetries are now all in hand:
  conservation (P17-twin) + orbit-bridge + this conjugate-split class.
- **Joint-set side: ready.** A joint-set leak test in carry coordinates can now match-control for *all three*
  forced symmetries. That is the next concrete experiment (pre-register it).
