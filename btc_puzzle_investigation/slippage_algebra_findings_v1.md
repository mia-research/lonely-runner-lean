# The exact amicable slippage — an algebraic result (v1, 2026-07-17)

**The algebraic route** on `π_n = π_p − 1` (instead of another MI sweep). The question was proof-shaped:
does the amicable near-coincidence force an *exact* relation between `eis_p(X_d)` (field lift of the
public `x`) and `eis_n(d)` (scalar lift of the secret `d`)? Answer: it forces a **parity obstruction**
on the linear channel — a real obstruction, not a magnitude reading. Verified exactly on secp in
`verify_slippage_algebra_v1.py` (exact integer curve arithmetic + lifts; no-float guard clean).

## Verified structure  `[VERIFIED exact]`
1. **`ℤ[ω]/(π_n)` module identity.** `π_n = π_p − 1 = Frob − 1` annihilates `E(F_p)`:
   `[a−1]G + [b][ω]G = O`, with the CM endomorphism `[ω]:(x,y)↦(β x, y)`, `β = 89408…` a primitive
   cube root of 1 mod p (closes exactly; the other root/sign do not). So `E(F_p) ≅ ℤ[ω]/(π_n)` as a
   `ℤ[ω]`-module, and `eis_n(d)` is exactly the canonical small representative of the ring element
   `↔ [d]G`. This is the precise meaning of "the scalar lift," pinned to the amicable prime.
2. **Parity of each lift in `d`.**
   - `eis_p(X_d)` is **EVEN** in `d` — because `X_{n−d} = x(−[d]G) = x([d]G) = X_d`. (400/400; odd-in-`d`
     energy = **exactly 0**.)
   - `eis_n(d)` is **ODD** in `d` — because `(−d,0) ≡ −(d,0) mod L_n` and the rhombus is centred at 0.
     (400/400, 0 boundary exceptions; even-in-`d` energy = **exactly 0**.)

## The result  `[PROVED obstruction]`
`eis_p(X_d)` lives in the **even** subspace of functions `ℤ/n → ℤ[ω]` (under `d ↦ −d`); `eis_n(d)` lives
in the **odd** subspace. A `ℤ[ω]`-linear map preserves parity and affine adds only an even constant, so
any affine relation `M·eis_n(d) + c = eis_p(X_d)` forces `M·eis_n(d) ≡ 0`, hence `M = 0`. More
generally *any* function `G(eis_p(X_d))` is even in `d`, while `eis_n(d)` is odd and nonzero — an even
object cannot equal an odd one. **Therefore the linear/affine channel `eis_p(X_d) → eis_n(d)` is exactly
zero, for all `d`.** The slippage `(0,1)/(1,1)` is a fixed, `d`-independent lattice perturbation, i.e.
**parity-neutral**, so it cannot bridge even↔odd — it cannot manufacture the missing odd component.

- This is the **same parity** that gives `x` even / `y` odd in `d` and `σ ⊥ s_y` (master doc Part V). So
  the amicable slippage is **not a new wall** — it is blocked by the parity structure already on record.
- `δ(X) = eis_p(X) − eis_n(X)` (same value, both lattices) is a **deterministic function of the public
  `X`** (the closed form `(−c2, −c1−c2)` from `X`'s `L_p`-coefficients holds only 113/200 — the `L_n`
  and `L_p` roundings disagree on the rest, so it is *not* a clean identity). Either way `δ` carries no
  `d`-information beyond `X` — the algebraic reason the `δ`-probe read null.

## What this is NOT, and what stays open  (read literally)
- **NOT a closure of the avenue.** The obstruction is on the *linear* channel to `eis_n(d)` only.
  - **The odd sector is reachable via `y`.** `y_d` is odd in `d`; a readout using `y` (e.g. `sign(xy)`,
    the joint `(x,y)`) is exactly the parity-correct channel into the odd half. The parity result
    **points at `y`** as the way past it — it does not forbid a leak, it says the `x`-lift alone is
    parity-blocked. This is the same live "odd-half-via-`y`" thread as the joint-shadow work; whether a
    *cheap* `y`-readout reaches `eis_n(d)` is open.
  - **Non-linear** relations `eis_p(X_d) ↔ eis_n(d)` are untouched; `eis_p(X_d)` still determines
    `eis_n(d)` **up to the `±` (d vs n−d) sign**, gated by inverting `x` = the DLP.
  - **Scope:** this argument is about the scalar **CM lift** `eis_n(d)`, which is parity-antisymmetric.
    It says nothing about the **band decomposition** `derr/n/k` (defined on the band `[A,2A)`, not
    symmetric under `d↦n−d`) — that channel is a separate question (Parts 1–2).

*Grades: VERIFIED exact (module identity, both parities, δ determinism) · PROVED (linear-channel parity
obstruction, exact ∀d) · NOT a closure (non-linear + `y`-channel + band channel all open).*
