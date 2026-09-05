# Independent reproduction of the 120° law premise (`g=2`, `α₂/α₁=ζ₃`) — from scratch, exact

**Date:** 2026-08-10 · **Trigger:** a "did you test the idea or just the method?" challenge after the
n1/A_new synthesis was checked only for *inter-file consistency* (the COMPENDIUM_v1 failure mode —
a document cannot witness its own audit; [[feedback-verification-claim-needs-artifact-2026-07-24]]).

**No leakage / key-recovery / ECDLP claim.** This is a curve-arithmetic verification of a public-math
statement about Frobenius eigenvalues of a twisted sheaf. It says nothing about any scalar `d`.

## What was independently recomputed (not re-run from the project's own instrument)

Own implementation from the object definition — `V_m(a) = −Σ_{Q∈E(F_{p^m})} χ₂(y_Q)·χ_a(Norm Q)`,
`E: y²=x³+7`, `χ_a` the character of `E(F_p)≅ℤ/n`, `Norm=Σ Frobⁱ`. From `V₁..V₃`: Newton → `L*(T)`;
then `g = deg gcd(L*(T), L*(ζ₃T))`. **No float in the signal path** (finite fields + `Fraction` +
length-`n` cyclotomic integer vectors). Scripts on disk:
`n1_120deg_g2_honest_reproduction_v1.py`, `n1_120deg_g2_modular_breadth_v1.py`,
`n1_omega_descent_reproduction_v1.py`.

## Results

| claim (v3 grade) | this reproduction | grade here |
|---|---|---|
| ω-descent `V₁(a)=V₁(λa)`, `λ` order 3 (v3 §2 `[CONFIRMED]`) | **exact, all cells**, `p∈{43,67,79,127,163,211}`; control (non-order-3 `μ`) breaks every cell | **`[REPRODUCED-exact]`** |
| `α₂/α₁=ζ₃` i.e. `g=2` (v3 §1 `[PROVED-exact]`, the load-bearing re-scope) | **`g=2` at every cell** — see below | **`[REPRODUCED-exact, per-cell, p≤211]`** |

**Honest anchor (`e₁,e₂,e₃` all computed from `V₁,V₂,V₃`, nothing assumed except `e₄`):**
- `p=43` (`≡7 mod12`, secp's class): all 30 cells `g(ζ₃)=2`; the forced relation
  **`e₃ == χ₂(−1)·p·e₁` holds exactly** at every cell (this is the instrument-validation control —
  `e₃` is honest, and it lands on its predicted value, so the `F_{p³}` character-sum + Norm
  base-change pipeline is correct).
- `p=67`: 9 cells, same, fully honest.

**Firing controls (all fire):** `g(ζ₆)=0` (the `=2` is specific to `ζ₃`), `g(1)=4` (self-gcd sanity),
and **`g(ζ₃ | e₄:=p²+1)=0`** — a *wrong* `e₄` collapses `g` to 0, so the result is not an artifact of
the one assumed input.

**Breadth (modular `g` over `𝔽_ℓ`, `ℓ≡1 mod 3n`, cross-checked at two `ℓ` each; `V₁,V₂` honest,
`e₃,e₄` from the relations validated at the anchor):** `g(ζ₃)=2` at **all cells** of
`p=67,79,127,163,211` — 606 cells total.

## The one assumed input, and why it is not a hole

`e₄ = p²` was taken from **Deligne purity (`[PROVED]`, weight 1) + the ι-pairing `α↦−ᾱ`
(`[PROVED — FORCED]`)**: two `{α,−ᾱ}` pairs give `e₄=(−p)(−p)=p²`. It was **not** recomputed via `V₄`
(the `F_{p⁴}` enumeration is `O(p⁴)`, ≥3.4M points at the smallest non-degenerate prime `p=43` —
infeasible in pure Python this session). It is corroborated two ways: the **companion** relation
`e₃=χ₂(−1)·p·e₁` (same functional-equation origin) was verified *honestly*, and the `e₄`-sensitivity
control shows `g=2` genuinely depends on the correct `e₄`. Owed: an honest `V₄`/`e₄=p²` at one prime.

## Scope and what is NOT shown (`[CONDITIONAL NEGATIVE — method + sample]`)

- Verified at **`p ≤ 211`**, all in secp's class `p≡7 mod12`; `n=#E(F_p)` prime, `n≡1 mod3`.
  `p=13` is **degenerate** (χ₂ constant on the cycle ⇒ trivial twist, no 4-dim structure) and is
  correctly outside the census; it is the only such case below 260.
- This reproduces the **per-cell** statement only. It does **NOT** touch **uniformity** — `α₂/α₁=ζ₃`
  for *all* `a`, *all* `p`, up to secp's `p≈2²⁵⁶`. That is exactly the sole open frontier v3 §4
  leaves (levers: `L-Stick` Stickelberger, `L-mono` geometric monodromy), and **no finite sweep,
  including this one, can close it.** The primes here sit ~3 orders below even the `p≤547` empirical
  banner and ~76 orders below secp.
- `Stickelberger (D2)` remains `[CITATION UNVERIFIED]` (three failed `citation-verifier` runs); this
  reproduction does not bear on it.

## Net

v3's per-cell `[PROVED-exact]` for the 120° premise **survives an independent, from-scratch, exact
recomputation with a validated instrument and firing controls** at 6 primes / 606+ cells. The synthesis
that relayed it was right to call it strong; it is now recomputed, not merely relayed. The open frontier
is unchanged and is uniformity, not the per-cell fact.
