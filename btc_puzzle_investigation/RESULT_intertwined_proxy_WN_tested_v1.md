# RESULT — the "Intertwined Fourier Proxy" `W_N`: the 1-D mixed-character extraction route, tested

**Date:** 2026-08-10.
**Object graded:** the *proposed extraction mechanism* `W_N` (below), **not** the sub-Rayleigh deficit.
**Grade of this finding:** `[VERIFIED — decidable artifact]` for the mechanism incoherence (§2.1–2.2);
`[structural — coherent object identified, exact bound pending citation-verifier]` for §2.3.
**Artifacts:** `scratchpad/test_intertwined_proxy.py` (+ run log), reproduced against secp256k1 with the
GLV constants derived from scratch (not trusted hex).

---

## 0. What was tested

An external paste proposed to convert the real, documented sub-Rayleigh deficit
(`RETROSPECTIVE_FINDING_01_subrayleigh_demotion_v1.md`, pooled Stouffer `Z=−13.99`, `[EMPIRICAL —
7 primes, pre-registered, control-surviving]`) into a **discrete-log extraction**. Its mechanism:
fold the μ₃/GLV geometry proxy `F(P)=x_P·y_P` and the scalar character `e_n(a·d)` onto a single index `d`,

> `W_N(a) = Σ_{d=1}^{N} (x_d·y_d)·e_n(a·d)`,   `x_d,y_d = coords of [d]G`,

and choose a frequency `a₀` so that the GLV rotation `β` on the geometry side is "unwound" by the phase
of `e_n`, giving an orbit-invariant, KS-shielded sum. The stated claim: KS/Weil "do not cover mixed
character sums where the additive character's argument is a polynomial on the p-lattice weighted by a
character of the n-torsion," so `W_N(a₀)` extracts the shadow past the `√p` floor.

## 1. The parts that hold (verified — recorded so the audit is not one-sided)

- **Δ-identity** `x(P+Q)−x(P−Q) = −4y₁y₂/(x₁−x₂)²`: standard affine Weierstrass algebra, correct
  (`λ₊²−λ₋²` collapses the `x₁+x₂`; numerator `(y₂−y₁)²−(y₂+y₁)² = −4y₁y₂`).
- **Isotype selection** `F=xy`, odd under `[−1]`, μ₃-weight 1: verified on secp256k1 —
  `φ(P)=(βx,y)=[λ]P` and `F(φP) ≡ β·F(P) (mod p)` for `d=1..59` (script items A,B, both `True`).

## 2. The finding — the phase-lock does not exist (three readings, all closed)

**2.1 Literal reading is type-incoherent.** `β` is a **255-bit residue in `F_p`** (order 3 in `F_p*`);
`e_n(·)` is a complex `n`-th root of unity. The requirement `β·e_n(λad)=e_n(ad)` multiplies an `F_p`
element by a complex phase — no `F_p ↪ ℂ` sends `β` to the complex cube root `ω=e^{2πi/3}`. Concretely the
additive image `e_p(β)=exp(2πiβ/p)` is a `p`-th root of unity with `|e_p(β)−ω| = 0.89`, not 0.

**2.2 Steelman still fails.** The one coherent way to make `β` act as `ω` is a **cubic multiplicative**
character `χ₃` (β has order 3, so `χ₃(β)=ω`). Then each GLV orbit `{d,λd,λ²d}` contributes
`χ₃(F)·[e_n(ad)+ω·e_n(aλd)+ω²·e_n(aλ²d)]`, and a single `a₀` "locks" it only if, **for all `d`**,
`e_n(a(λ−1)d)=ω^{-1}`. But `a(λ−1)≢0 (mod n)`, so the left side is a **nontrivial additive character of
`d`**: over 20000 `d`, `|mean_d e_n(a(λ−1)d)| ≈ 5×10⁻⁵` for every `a` tried (incl. `a≈n/3`) — a spread,
never a constant of modulus 1. **The geometric phase `ω^j` is `d`-independent; the scalar phase is
`d`-dependent. They share no index to lock on.** No `a₀` exists.

**2.3 The coherent object is inside the KS family, not outside it.** Written coherently (a proper
character on the geometry), the statistic is
`Σ_{d} χ(F([d]G))·e_n(a d)` over `⟨G⟩` — a **mixed character sum over the cyclic point group**, which is
exactly the Kohel–Shparlinski / Lange–Shparlinski / Weil family. The `e_n(ad)` twist is the *generic*
case those bounds are built for; folding it in tends to **increase** cancellation, not open a shielded
channel. The "checkmate" is inverted. *(Exact theorem statement pending `citation-verifier` before this
line moves any grade.)*

## 3. Scope of the closure (graded, per the burden-of-proof rule)

- **Object closed:** the 1-D single-frequency extraction `W_N(a)` that collapses the μ₃ geometry weight
  and the scalar character onto one index `d`.
- **Class:** mixed additive-character sums over `⟨G⟩` with the GLV weight folded into the summand value.
- **Power:** the phase-lock has **no** solution `a₀` — verified for all `a` (the obstruction is
  structural: `a(λ−1)≢0`), not a null over sampled `a`.
- **Scope / what this does NOT touch:** the sub-Rayleigh deficit lives in the **2-D** object
  `U(a,b,c)=Σ_d e_p(bx_d+cy_d)e_n(ad)` where the geometry frequency `b` and the scalar frequency `a` are
  **separate axes**. Nothing here bounds that object; it remains mechanism-open. This result closes a
  *route to* the deficit, not the deficit.

## 4. Why it is worth recording — the trap it fences off

The single error was treating `β` (a mod-`p` cube root of unity) as the complex `ω`. Any future arc that
"projects onto the ζ₃ eigenspace" must keep the geometry's μ₃ index and the scalar's phase on **separate
axes** (the 2-D `(a,b)` grid), never collapsed onto `d`. The productive descendant — the μ₃/GLV
**frequency-support** test on `U(a,b,c)` — does exactly that, and uses the *exact* pullback
`U(a,b,c)=U(λa,βb,c)` (verified, `scratchpad/verify_U_pullback.py`, max|Δ|=4.4e-15). Caution carried
forward to its pre-registration: that pullback **couples `a` and `b`**, so binning the full `(a,b)`
diagonal orbit measures a forced zero (`var|U|²≡0`), and on a fixed deficit-carrying slice `a₀≠0` the
`b↦βb` grouping is informative but **not** licensed by the pullback (forced only on `a₀≡0`). Routed to
`experiment-designer`.

## 5. Artifacts
- `scratchpad/test_intertwined_proxy.py` — secp256k1: GLV pair derived, items A/B `True`,
  `|e_p(β)−ω|=0.89`, per-`a` `|mean_d e_n(a(λ−1)d)|≈5e−5`.
- `scratchpad/verify_U_pullback.py` — model curve `F_61`: pullback exact; T-fixed locus `= {a≡0∧b≡0}`;
  `a₀≠0` slice `b↦βb` unforced (|U| differs O(10)).
