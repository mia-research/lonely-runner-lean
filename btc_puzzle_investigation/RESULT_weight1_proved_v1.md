# RESULT — the weight-1 premise is PROVED for all `p`; the N1 phase FORMULA is now unconditional

*2026-07-24. Item 1 of the post-N1 programme. Citation verified by `citation-verifier` **and**
independently spot-checked against the source PDF. De-risk sweep pre-registered
(`PREREG_weight1_derisk_v1.md`) with a fired off-weight control; instrument-limited (see §4).
Companion: `weil_deligne_character_bound_v1.md` §6′, `RESULT_n1_phase_cap_v3.md`.*

**No leakage, key-recovery or ECDLP claim. This concerns only the analytic structure of the
character sum; it makes the readout *less* concentrated than its dimension permits.**

---

## 1. What is now proved

> **`[PROVED — all `p`, Weil II 3.2.3 / Kohel–Shparlinski Prop 2]`
> All four Frobenius eigenvalues of `H¹_c(U, L_{χ₂(y)} ⊗ L_{χ_a})` have modulus EXACTLY `√p`
> (weight exactly 1), for every `p ≡ 1 mod 3` and every `a ≠ 0`.**

This upgrades the premise from `[VERIFIED at p = 13, 43 only — six unforced cells]` to `[PROVED]`,
and it removes the modulus half of the proxy tag that governed every phase-language sentence of
`RESULT_n1_phase_cap_v3.md`.

**Two independent routes, both from inputs the record already cites:**

**(A) Kohel–Shparlinski, ANTS-IV 2000, Prop 1 + Prop 2** (`kohel_shparlinski_ants4_2000.pdf` p. 3,
read directly). `χ = χ₂(y)·χ_a` is a character of the divisor group of `F_p(E)`; `χ_a` (the
Lang-torsor character of `E(F_p)≅ℤ/n`) is **totally unramified**, so Prop 1's product clause gives
`deg f(χ) = deg f(χ₂(y)) + 0 = 4` and `D = 2g−2+deg f(χ) = 4`. Since `H⁰_c = H²_c = 0` (the note's
§4), `L(C,t,χ) = det(1 − t·Frob | H¹_c)`, so its `D=4` zeros **are** the four eigenvalues. **Prop 2
(Weil's function-field RH; Bombieri 1966 / Weil BNT ch. 7) states verbatim: "each zero satisfies
`|ϑᵢ| = q^{1/2}`."** Equality, all four. Quoted text confirmed from the PDF, not the agent summary.

**(B) Deligne, Weil II (1980), Cor. 3.2.3(2)** (via Katz, *Four Lectures on Weil II*). `F` is rank 1,
lisse, pure of weight 0 on `U = E ∖ {r₁,r₂,r₃,O}`. At each of the four punctures the local monodromy
is the **nontrivial** order-2 Kummer character of `L_{χ₂(y)}` (`L_{χ_a}` is unramified everywhere),
so `F^{I_x} = 0` and the forget-supports map `H¹_c(U,F) → H¹(U,F)` is an isomorphism. Cor. 3.2.3(2)
then gives `H¹_c` **pure of weight 1**. The record had invoked only the weaker Target Theorem
(weight `≤ 1`) from the *same* source; 3.2.3 upgrades it once one notes `F^{I_x}=0`.

## 2. Consequence — the phase formula is now unconditional

The chain of `RESULT_n1_phase_cap_v3.md` §2, re-graded:

1. Four eigenvalues, all modulus `√p` — **`[PROVED — all p]`** (§1 above; was `[VERIFIED, 2 primes]`).
2. Multiset closed under `α ↦ −ᾱ` — **`[PROVED — FORCED]`**, from the exact `P ↦ −P` substitution:
   `conj(V_k(a)) = χ₂^{(k)}(−1)·V_k(a)`. Confirmed to `≤9×10⁻¹⁵` at `p = 13, 43, 61`. (This is *not*
   a purity consequence — Poincaré duality pairs `a` with `−a` — it is a separate exact identity, and
   it is what supplies the 2+2 conjugate structure.)
3. Therefore the four unit vectors form two pairs `{√p e^{iθ}, √p e^{i(π−θ)}}` and
   **`|V(a)| = 2√p·|sin θ₁ + sin θ₂|`** (ODD) — **`[PROVED]`**, both inputs now proved.

> **So the identity `|V(a)| = 2√p·|sin θ₁ + sin θ₂|` holds for all `p`, unconditionally.** The `½`
> saturation is a proved consequence of a proved weight-1, proved-forced phase pairing.

## 3. What remains open — exactly one inequality

> **`|sin θ₁ + sin θ₂| ≤ 1`  (equivalently `S_y ≤ 2`).**

This is **not** implied by weight-1 (which gives only `S_y ≤ 4`) nor by the `α↦−ᾱ` closure. It is the
constraint on the two surviving phase parameters, and it is `[VERIFIED — out-of-sample, 120 frozen
primes, 4.7M cells]` (`RESULT_n1_phase_cap_v3.md`) but not proved. **This is now the single open link
in the entire N1 story.** Natural attack unchanged: integrality of the coefficients of
`det(1−t·Frob|H¹_c) = L(C,t,χ)` in `ℤ[ζ_n]` — a degree-4 polynomial with all roots on `|z|=√p` and
the `θ↦π−θ` symmetry, whose middle coefficient controls `sin θ₁ + sin θ₂`.

## 4. The de-risk sweep — pre-registered, control fired, instrument-limited (honest scope)

`PREREG_weight1_derisk_v1.md` froze an exhaustive list `{13,43,61,67,79,97}` (`P_max=100`, 53 μ₆
cells) to confirm `W(p) = max_{cells,i} ‖α_i‖/√p − 1‖ < τ = 10⁻⁶` — insurance against a mis-applied
citation.

- **Off-weight firing control FIRES** (the check v1 lacked): a planted tuple with one eigenvalue at
  `0.999√p` reads `W = 1.0×10⁻³ ≫ τ`; the gross plant `{√p,√p,1,p}` reads `W = 5.56`. An all-weight-1
  tuple reads `W = 0`. **The pipeline would report weight≠1 if it occurred** — it does not pass
  vacuously.
- **`W(13) ≈ 4.4×10⁻¹⁶`, `W(43) ≈ 8.9×10⁻¹⁵`** (the C1 weight check of the original eigenvalue run).
- ⚠ **`p ≥ 61` exceeds the practical budget with the current instrument.** The `O(p⁴)` enumeration
  runs in Sage's elliptic-point object layer at ≈10× the prereg's assumed rate: `p=61` alone did not
  finish in 9 min. This is an **instrument-speed deviation** from the frozen `P_max=100` (filed in
  `PREREG_weight1_derisk_v1_DEVIATIONS.md`). `p=61` is running in the background; `{67,79,97}` need a
  raw-arithmetic rewrite of the histogram to be reachable. **The sweep is confirmation of a proved
  fact, not its basis** — the proof (§1) does not depend on it.

## 5. Status

- **N1 / §XI.10:** weight-1 `[PROVED all p]`; phase formula `[PROVED]`; the cap `S_y ≤ 2` is the lone
  remaining `[VERIFIED — not proved]` link.
- **Two edits owed to earlier documents** (versioning bars in-place edits; carry into successors):
  `weil_deligne_character_bound_v1.md:72` understated "weight `≤ 1`" — the correct statement is
  "`= 1` by Cor. 3.2.3 / KS Prop 2"; and its §2 "wild at O, Swan 3" describes the *additive* object,
  not this Kummer `F` (tame at O). Neither affects any downstream number.
- **Next (item 2):** whether the `2√p` cap is provable via the μ₄-cover / 2-dimensional isotypic
  reading — the one lead that could turn the last inequality into a theorem.
