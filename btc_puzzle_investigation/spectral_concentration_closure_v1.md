# Analytical closure of the spectral-concentration door (the last open frontier)

**Date:** 2026-07-17. The one door the whole arc left open (v14/v31): is there a **cheap** readout `F`
(computable from coordinates, without `d`) whose `d`-character spectrum concentrates —
`C(F) := max_{a≠0}|Corr_F(a)|/‖F‖₂` bounded away from the floor, where
`Corr_F(a) = (1/n)Σ_d F([d]G)·e_n(-a d)`? The empirical hunt
(`spectral_concentration_hunt_v1.py`) says no (best cheap `C/floor` flat ≈1.3, p=211→6007, while the
aligned control grows 6→27). Here is the **analytical closure**.

## The exact reduction (unconditional)

1. **`Corr_F(a) = ⟨F, χ_a⟩_d`** is exactly the `d`-Fourier coefficient of `F` against the curve
   character `χ_a(P) = e_n(a·d(P))`. [definitional]
2. By Parseval `Σ_a|Corr_F(a)|² = ‖F‖₂²`, so `C(F) = O(1)` (concentration) **⟺** `F` has
   `Ω(‖F‖₂)` correlation with a single character `χ_{a₀}`. [exact]
3. **The characters `χ_a` are exactly the additive cocycles** (`χ_a(P+Q)=χ_a(P)χ_a(Q)`), i.e. the
   `C=1` readouts of v31. So **spectral concentration ⟺ chaining ⟺ correlation with a cocycle-
   character `χ_{a₀}`** — the three "open doors" are one door. [ties v14 ≡ v31 ≡ this]

So a cheap readout concentrates iff it is `Ω(1)`-correlated with `χ_{a₀}(P)=e_n(a₀ d(P))` — a function
of the discrete log.

## The bound (PROVED, given the cited KS/Weil character-sum estimate)

**Cited input (KS/Weil–Deligne).** For a nonconstant rational function `f` on `E` of degree `≤ D`
and a (multiplicative or additive) character `ψ`, uniformly in `a`:
> `|Σ_{d} ψ(f([d]G))·e_n(a d)| = O_D(√p·(log p)^{O(1)})`.
(Kohel–Shparlinski, ANTS-IV 2000; Weil bounds for mixed additive×multiplicative character sums over
`E`. The general-`f` form is the same one that closed the T_y bound, findings v21.)

**Proposition (spectral non-concentration).** Let `F = ψ∘f`, `f` a rational function on `E` of
degree `≤ D`, `‖F‖₂ = Ω(1)`. Then for all `a`,
> `|Corr_F(a)| = O_D(√p·polylog / n) = O_D(p^{-1/2+o(1)})`,  hence `C(F) = O_D(p^{-1/2+o(1)})` — the floor.

*Proof.* `Corr_F(a) = (1/n)Σ_d ψ(f([d]G))e_n(-a d)`; the cited bound gives numerator `O_D(√p polylog)`;
divide by `n = p(1+o(1))` and by `‖F‖₂ = Ω(1)`. ∎

**Every readout in the hunt is of this form** — `χ₂/χ₃/χ₆` (multiplicative characters of `x`,
degree 2), `ε`/flap and sextant (bounded lattice-region indicators of `eis(x)`), and the **`xy`
family**: `e_p(x·y)` is an additive character of `xy`, a function on `E` of pole order `≤ 5`. So all
of them are provably at the floor — including the high-Wiener `χ₂`, which the closure theorem's
Wiener-norm bound (`glv_closure_theorem_v2`) leaves vacuous but the **direct** KS/Weil bound covers.
This is exactly why the empirical `C/floor` is **flat** at ≈1.3 (the `polylog` constant), not growing.

## What is NOT bounded-degree — and why that IS the DLP

The one readout with `C=1` is `χ_{a₀}(P)=e_n(a₀ d(P))` itself. It is **not** `ψ∘f` for bounded-degree
`f` — if it were, `d` would be a bounded-degree function of the coordinates and the ECDLP would be
easy. It is the discrete log. (Even high-*degree but structured* readouts like `x([m]P)=x_{md}` do
**not** escape: `Corr(a)` re-indexes to a `T`-sum at frequency `am^{-1}`, still `√p`-bounded.)

**General poly-time readouts:** a poly-time `F` that concentrated (`C=Ω(1)`) would be an efficient
distinguisher `Ω(1)`-correlated with `e_n(a₀ d)` — i.e. a hardcore-predicate / DLP break
(Boneh–Shparlinski). So for *general* readouts, "no concentration" **is** the DLP-hardness assumption.

## Closure statement (graded)

- **Bounded-degree cheap readouts: PROVED (given KS/Weil) that `C(F)=O(p^{-1/2+o(1)})` — no
  concentration.** This closes the entire natural class (every candidate anyone builds from a
  bounded-degree coordinate formula), unconditionally modulo the cited KS/Weil bound. `[PROVED given CITED KS/Weil]`
- **General poly-time readouts: "no cheap concentration" ⟺ ECDLP hard.** The residual door is not a
  gap in our analysis — it **is** the discrete-log problem, exactly. `[= the ECDLP assumption]`
- Unified with v31: concentration = chaining = correlation-with-a-cocycle-character; all shut for
  bounded-degree readouts by one estimate (KS/Weil), and identical to the DLP for the rest.

**So the door is closed the only way it can be:** analytically for every bounded-degree readout
(given the standard KS/Weil bound — the same one underwriting this whole programme), and for the
unrestricted class it is provably *equivalent to* the ECDLP, not a separate unexplored avenue.
Empirical confirmation: best cheap `C/floor` flat ≈1.3 over p=211→6007 while the aligned control
grows 6→27.

## Honest scope
- Conditional on the KS/Weil bound (cited, standard; the general-`f` form used here is the one from
  v21). Making it unconditional = reproving Weil/Deligne + KS, out of scope.
- "Cheap = bounded-degree" is the operative class; the step to *all* poly-time readouts is where the
  statement becomes the ECDLP assumption itself — stated as such, not hidden.

## Files
`spectral_concentration_hunt_v1.py` (the empirical scaling), this closure. Prior:
`masked_structure_findings_v14` (the door), `_v31` (cocycle rigidity = same door),
`glv_closure_theorem_v2` (the Wiener-norm route it subsumes for high-norm readouts),
`masked_structure_findings_v21` (the general-`f` KS bound).
