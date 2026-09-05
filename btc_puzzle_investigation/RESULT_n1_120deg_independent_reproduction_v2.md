# Independent reproduction of the 120° law premise (`g=2`, `α₂/α₁=ζ₃`) — v2, `e₄` gap now CLOSED

**Date:** 2026-08-10 · **Supersedes** `RESULT_n1_120deg_independent_reproduction_v1.md` (which recorded
`e₄=p²` as the one assumed input, "owed"). That debt is now discharged: `e₄=p²` is computed organically
from an honest `V₄` over `F_{43⁴}`. **No leakage / key-recovery / ECDLP claim** (curve-arithmetic
verification of a public statement about Frobenius eigenvalues; no bearing on any scalar `d`).

## The one change from v1: `e₄=p²` is now recomputed, not assumed

v1 took `e₄=p²` from Deligne purity + the ι-pairing (theoretically airtight — it is the Weil-pairing
determinant, RH for varieties over finite fields — but not recomputed there). Now done directly:

- **`V₄(a)` computed by a dedicated C program** over all `43⁴ = 3,418,801` points of `F_{43⁴}`
  (`n1_120deg_e4_honest_V4_p43_v1.c`, runtime ~35 s: encoded field elements + sqrt/Frobenius tables +
  Fermat inversion; exact integers, no float).
- **Instrument validation (hard gate):** the C program's `V₁,V₂,V₃` (a=1 and a=2) match the trusted
  Python (`gfull2`) **bitwise** — same length-31 cyclotomic vectors. Same code therefore trustworthy on
  `V₄`.
- **Newton on the honest `p₁,p₂,p₃,p₄`** (`n1_120deg_e4_newton_check_v1.py`): at a=1 and a=2,
  **`e₄ == p² == 1849` exactly**, `e₃ == χ₂(−1)·p·e₁` exactly, all `e_k` integral.

> **⇒ At `p=43`, every input to `L*(T)` is now computed from the curve. `g=2` there rests on ZERO
> assumed parameters.** `[REPRODUCED-exact, no assumptions, p=43]`

## Full status (carried from v1, unchanged except `e₄`)

| item | grade |
|---|---|
| ω-descent `V₁(a)=V₁(λa)`, control breaks every cell; `p∈{43,67,79,127,163,211}` | `[REPRODUCED-exact]` |
| `g=2` at every cell, honest `e₁,e₂,e₃` (V₁,V₂,V₃), `p=43` (30 cells) + `p=67` (9 cells) | `[REPRODUCED-exact]` |
| **`e₄=p²` from honest `V₄` over `F_{43⁴}`** (a=1,2) | **`[REPRODUCED-exact]` — was assumed in v1** |
| `g=2` breadth, modular gcd over `𝔽_ℓ` (2 ℓ each), `p=67,79,127,163,211`, all 606 cells | `[REPRODUCED-exact | e₃,e₄ from p=43-validated relations]` |
| firing controls: `g(ζ₆)=0`, `g(1)=4`, `g(ζ₃ | e₄=p²+1)=0` | all fire |

## Scope and what is still NOT shown (`[CONDITIONAL NEGATIVE — method + sample]`)

- Verified at `p ≤ 211`, all `p≡7 mod 12` (secp's class), `n=#E(F_p)` prime `≡1 mod3`. `p=13` is the
  sole degenerate prime below 260 (χ₂ constant on the cycle ⇒ trivial twist), correctly out of census.
- **Per-cell only.** This does not touch **uniformity** — `α₂/α₁=ζ₃` for *all* `a`, *all* `p`, to secp's
  `p≈2²⁵⁶`. That is v3 §4's sole open frontier (levers `L-Stick` Stickelberger / `L-mono` monodromy) and
  **no finite sweep can close it.** These primes sit ~76 orders below secp.
- `Stickelberger (D2)` remains `[CITATION UNVERIFIED]`; untouched here.

## Net

v3's per-cell `[PROVED-exact]` for the 120° premise now survives an independent from-scratch exact
recomputation **with no assumed inputs at `p=43`** (honest `V₁..V₄`, validated instrument, firing
controls) and holds across 6 primes / 606+ cells. The frontier is unchanged: uniformity, not the
per-cell fact.

## Reproduction
- `n1_120deg_e4_honest_V4_p43_v1.c` → `V₁..V₄` at p=43 (`cc -O2`; ~35 s).
- `n1_120deg_e4_newton_check_v1.py` → Newton, checks `e₄==p²`, `e₃==χ₂(−1)p·e₁`.
- `n1_120deg_g2_honest_reproduction_v1.py` (honest `g` via `ℚ(ζₙ,ζ₃)` gcd), `n1_120deg_g2_modular_breadth_v1.py` (modular `g`), `n1_omega_descent_reproduction_v1.py`.
