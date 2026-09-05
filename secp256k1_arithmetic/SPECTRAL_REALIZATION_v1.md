# The spectral realization of the zeros of L(ψ,s) — what is proven, what is open

**2026-07-11.** A disciplined map of the Hilbert–Pólya question for
`L(ψ,s) = L(E,s)`, `E: y²=x³+7`, the CM (by ℤ[ω]) elliptic curve secp256k1
reduces from. Companion computation: `thread_spectral_v1.py`. **This document
claims no operator.** It states precisely which spectral structures are theorems,
which are the open frontier, and where the μ₆/CM symmetry actually sits — because
this is the exact place the project's earlier φ(n)-residue "RH programme"
overclaimed (memory: Moment-Pumping FALSE, operator indices (1,1)≠(0,0),
"spectrally optimal" false). The value here is an honest boundary, not a claim.

---

## 0. What "spectral realization" would mean

A Hilbert–Pólya realization of L(ψ,s) is a self-adjoint operator `H` on a Hilbert
space whose eigenvalues are exactly the ordinates `γ` of the nontrivial zeros
`s = 1 + iγ`. Its existence would force RH for L(ψ,s) (real eigenvalues ⇒ zeros
on the critical line). No such `H` is known for any L-function; the question is
what *structure* exists short of it.

Three tiers, from most-proven to most-open:

| Tier | Statement | Status |
|---|---|---|
| I | The zeros satisfy the **Weil explicit formula** (a trace-formula-shaped identity linking Σ over zeros to Σ over primes) | **Theorem** (Weil; Guinand) |
| II | The zeros are the spectrum of a **canonical operator on a specific space** — Connes' scaling action on the idele class space, ψ-isotypic part | **Conditional / partial** (Connes 1999): the trace formula ⟺ RH is a theorem; the *positivity* that would prove RH is open |
| III | A genuinely self-adjoint `H` with these eigenvalues, unconditionally | **Open** (the actual Hilbert–Pólya conjecture) |
| — | A **local** (p-adic, per-Euler-factor) self-adjoint realization | **Theorem** with a proven **global obstruction** (arXiv:2605.17645, 2026) |

---

## 1. Tier I — the explicit formula (theorem, and we test it)

The Weil–Guinand explicit formula is the rigorous, unconditional bridge:
for a suitable even test function `h` with transform `g`,

```
Σ_γ h(γ)  =  [archimedean term from the Γ-factor + conductor log N]
           −  Σ_{n≥2} (Λ_E(n)/√n) g(log n),
```

where `Λ_E(n)` are the coefficients of `−L'/L(s)` (prime-power Frobenius traces).
This says the zeros and the primes are two Fourier-dual readouts of one object —
the weak sense in which the zeros already "are a spectrum" (of the prime-sum
distribution). **It is a theorem; no RH needed.** `thread_spectral_v1.py`
verifies its *integrated* (counting) form:
`#{γ < T} = (T/π)(log(√N·T/2π) − 1) + O(log T)` — the Riemann–von Mangoldt law
for a degree-2 conductor-21168 L-function — against the computed zeros. [results
in that script's (N) block]

## 2. Tier II — the Connes framework and where μ₆ enters

For a Hecke Grössencharacter ψ of `K = ℚ(√−3)`, `L(ψ,s)` is an automorphic
L-function on `GL₁(𝔸_K)` (Tate's thesis). Connes' 1999 construction gives a
spectral *interpretation*: the zeros appear in the spectrum of the scaling action
of the idele class group `𝔸_K^*/K^*` on a space of functions (the "adele class
space" `L²` cut by a cutoff), **in the ψ-isotypic component**. Precisely:

- The idele class group of `K` has an archimedean factor from the **single
  complex place** of `K`, `ℂ^* = ℝ_{>0} × S¹` (Tate's thesis §archimedean).
- ψ has ∞-type `(1,0)`; its zeros live in the `ψ`-eigenspace of the scaling
  operator. **Two distinct μ₆'s must be kept apart** (this is the base-level
  correction of 2026-07-11, `SPECTRAL_CHECK_v1.md` / `adelic_recasting_v2.md`):
  - the **archimedean angular `S¹`** of `ℂ^* = ℝ_{>0}×S¹` carries the *continuous*
    ∞-type angle `e^{iθ}` of `ψ_∞(z)=z` (for the 256-bit Frobenius, `θ_p=50.55°`,
    generic — **not** a multiple of 60°);
  - the **finite ray-class character `χ = −(28/π)₆⁻¹`** (derived, thread A) is a
    *discrete* μ₆-valued character on `Ẑ_K^*` mod `𝔣 = (2²)(√−3)²(7)`.

  `ψ = ψ_∞·ψ_fin`; χ is the finite part. It selects **which** of the six sextic
  ray-class characters ψ is — i.e. the `L²(𝔸_K^*/K^*)` isotypic component — via
  the *finite* places, not the archimedean angle.

**This is where the survival-law operator model of §6 belongs, and its exact
scope.** The `Ĥ_CM = π(A_r² + A_θ²)` picture is the *heuristic* shadow of the
**archimedean** factor only: `A_r` is the radial dilation on `ℝ_{>0}` (the line),
`A_θ` is the angular operator on the archimedean `S¹` — and its six `m ≡ 0 (mod 6)`
sectors are **archimedean angular** modes, *not* the finite ray-class characters.
The finite χ is a **separate, finite-place** object that names the isotypic
component; it is Pontryagin-dual to the archimedean units, linked on global units
but not identical to the angular sectors. **What is a theorem:** Connes' trace
formula is *equivalent* to RH for `L(ψ,s)`. **What is open:** the positivity the
trace formula needs. **Two base caveats on the operator model itself** (not glossed):
(a) the radial factor `A_r = πA²` on the half-line `[1,∞)` has **deficiency indices
(1,1), not (0,0)** (`radial_selfadjointness.md`, independently re-verified) — its
self-adjointness needs the full-line fix, which empties `D_φ` under the normalized
multiplier (a normalization clash); the angular `A_θ` on the *compact* `S¹` is
genuinely (0,0). (b) The finite conductor at 2,3,7 (hence `log N`, the zero density)
is **not** in the archimedean `ℂ^*` at all. So the μ₆ operator model is a
consistency/selection statement on the archimedean factor, **not** a construction
of the zeros, and it does **not** rely on the φ(n)-programme's broken forcing step
(§Base audit).

## 3. The local Hilbert–Pólya and its proven global obstruction

arXiv:2605.17645 (May 2026) builds, for each good prime `p`, a genuinely
self-adjoint local operator whose characteristic data encode the Euler factor
`L_p(s) = (1 − a_p p^{-s} + p^{1-2s})^{-1}`. For our CM curve this is concrete:
at a good split prime the Frobenius has eigenvalues `π_p, π̄_p` (the two primes
above p, `|π_p| = √p`), and the local operator's "eigenvalues" are their phases —
`e^{±iθ_p}`, `cos θ_p = a_p/(2√p)` (the Sato–Tate angle). The **local** spectral
realization thus *exists* prime by prime.

The paper then **proves an interpolation obstruction**: these local operators
cannot be glued into a single global self-adjoint operator whose spectrum is the
global zero set — the global L-function is structurally inaccessible to any one
local operator. This is exactly the boundary the project's earlier notes
identified independently (KNOWN_FACTS §12: "proven locally, open globally"). For
a CM curve the local side is especially clean (the θ_p are equidistributed by
Hecke, with the μ₆/inert-supersingular dichotomy of §3), which makes the
*local-realization + global-obstruction* picture fully explicit here — arguably
the cleanest worked instance.

## 4. Tier III evidence — do the zeros *look* like operator eigenvalues?

The standard empirical signature of an underlying self-adjoint operator is
**GUE (random-matrix) statistics** in the zeros (Montgomery–Odlyzko). If the
zeros were "structureless" (Poisson) there would be no repulsion and Hilbert–Pólya
would be implausible; GUE-like level repulsion is the positive signature.

**Result on a VERIFIED-COMPLETE list** (`thread_spectral_v3.py`; the v1/v2
finders silently missed zeros — v3 uses bisection + a completeness assert
against `θ(T)/π`, and the unfolded mean spacing came out **0.991 ≈ 1.0**,
confirming no zeros are missing). On the 37 zeros with `0 < γ < 22` (36 spacings):
- **Level repulsion is present: GUE beats Poisson.** KS distance to the GUE
  Wigner surmise **0.269** vs to Poisson **0.360** — GUE closer.
- **Small gaps are strongly suppressed:** `P(spacing < 0.5) = 0.056` vs Poisson
  0.393 (and even below GUE's 0.273); `P(< 0.7) = 0.222` vs Poisson 0.503. Very
  few near-collisions — the hallmark of an underlying self-adjoint operator, and
  the *opposite* of the v1 artifact (where a low `P(<0.5)` came from **missing**
  close zeros; here the list is verified complete, so it is genuine repulsion).

**Honest caveats:** 36 spacings is a small sample and these are *low-lying* zeros
(height < 22), which are known to be **stiffer than bulk GUE** (finite-conductor +
central-point repulsion push the first zeros toward regularity — so `P(<0.5)`
below even GUE is expected, not super-GUE structure). KS 0.269 is not a tight GUE
fit at n=36 (5% critical ≈ 0.227) — the honest statement is **"repulsion present,
Poisson excluded, GUE favored; asymptotic RMT needs Odlyzko-scale heights,"** not a
decisive GUE identification. The value added over v1: the list is now *provably
complete*, so the repulsion is real rather than a sampling artifact.

## 5. The bottom line (no overclaim)

- **Proven and verified here:** the explicit formula / counting law (Tier I); the
  local self-adjoint realization per prime (§3); the exact zeros to 10 digits,
  LMFDB-confirmed (thread E).
- **Proven in the literature, structurally clear here:** the Connes trace-formula
  ⟺ RH equivalence (Tier II) with the μ₆ sector identified via the derived χ;
  the global interpolation obstruction (arXiv:2605.17645).
- **Open — the actual spectral realization:** no self-adjoint `H` with these
  eigenvalues exists (Tier III), and nothing here constructs one. The μ₆ operator
  model is a *selection/consistency* statement on the correct (CM, complex-place)
  space, not a proof. RH for L(ψ,s) is open (though it is a CM L-function, so it
  inherits no special unconditional RH).

The genuinely-ours contributions to *this* map: (i) the derived χ = −(28/π)₆⁻¹
that names the μ₆ isotypic sector precisely (thread A); (ii) the fully explicit
local data (Sato–Tate phases with the inert-supersingular dichotomy) that make
the local-HP/global-obstruction boundary concrete for this curve; (iii) the
computed, LMFDB-checked zeros the diagnostics run on. The wall — a global
self-adjoint operator — is where it has always been; we have mapped right up to
it without pretending to cross it.
