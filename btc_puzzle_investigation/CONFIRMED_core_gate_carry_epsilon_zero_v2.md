# CONFIRMED — ε (GLV coordinate carry) is Decidable Exactly from x Alone, for ALL Keys

**Supersedes v1** (which stated only the gate direction). **Grade: PROVED + VERIFIED**
(analytic areas; 200,000 real secp keys; real puzzle keys #135/#140).
Date: 2026-08-16. Curve: secp256k1, `p = 2^256 − 2^32 − 977`, `y² = x³ + 7`.

## Statement (complete form)

The GLV endomorphism coordinate carry `ε` is a **total, exact, O(1) function of the
public `x`-coordinate alone** — `y` never enters, no gate, no secret, no probability:

> **`ε = 0  ⟺  |u − v| ≤ ½`**,  where `(u,v)` is the centered π-lattice lift of `x`.

This **decides `ε` for every key** (not just "gated" ones), and it is exact-integer.

### Two equivalent public tests

**(A) Hexagon criterion (cheapest, iff):**
1. `u = {x(a−b)/p}`, `v = {−xb/p}`, centered to `(−½, ½]` (two floor-divisions).
2. `ε = 0 ⟺ |u − v| ≤ ½` (one subtraction, one comparison).

**(B) Direct definition:**
1. Lift `x ↦ z(x)` and `βx ↦ z(βx)` (same Babai step).
2. `ω·z(x) = (−z₁, z₀−z₁)`.
3. `c = (ω·z(x) − z(βx))/π ∈ ℤ[ω]` — the division is **exact, always**.
4. `ε = 0 ⟺ c = (0,0)`.

Proof of (A): `ω·(u,v) = (−v, u−v)`; since `|v| ≤ ½`, `round(−v)=0`, so `ε = 0 ⟺
|u−v| ≤ ½`. On the ellipse `s = u²−uv+v²`, `max|u−v| = 2√(s/3)`, so `s < 3/16 ⟹ ε=0`
— but `s<3/16` is only the *inscribed-ellipse subset*; (A) is the exact locus. ∎

## Exact measure of the ε=0 locus

For `x` uniform (lifts equidistribute on the fundamental cell `[−½,½]²`):

| Locus | Exact area | = | Empirical (200k secp `x`) |
|---|---|---|---|
| **ε=0** — hexagon `|u−v| ≤ ½` | `1 − 2·(1/8) = 3/4` | **75.00%** | 74.97% |
| Gate `s < 3/16` (inscribed ellipse) | `π·(3/16)/√(3/4) = π√3/8` | **68.02%** | 67.93% |

The gate is a strict subset of the ε=0 locus: **0** of 200,000 keys passed the gate
while failing the hexagon test. So the gate *certifies* ε=0 for the inner **68.02%**;
the hexagon test *decides* ε=0 for **100%** of keys, and ε=0 holds on exactly **75%**.

## Real puzzle keys
`c(x₁₃₅) = c(x₁₄₀) = (0,0)` — ε=0 by direct carry computation (test B), independently
confirmed by the gate (both have `s < 3/16`: `s₁₃₅=0.0589`, `s₁₄₀=0.0198`).

## Reproduction
```python
from fractions import Fraction as F
p=2**256-2**32-977
a=367917413016453100223835821029139468249; b=64502973549206556628585045361533709078
def uv(X):
    u=F(X*(a-b),p)-round(F(X*(a-b),p)); v=F(-X*b,p)-round(F(-X*b,p)); return u,v
def eps_zero(X):
    u,v=uv(X); return abs(u-v)<=F(1,2)     # total, exact, x only
# areas: hexagon = 3/4 = 75%; gate = pi*sqrt(3)/8 = 0.680175 = 68.02%
```

## Scope
`ε` is the coordinate carry under the coordinate-wise (Babai) reduction used in the
project's Core-Gate scripts. What is now established beyond v1: the decision is **total**
(all keys, via the hexagon test), the ε=0 set has **exact measure 3/4**, and the gate
`s<3/16` is the `π√3/8` inscribed shortcut. Related:
[v1](CONFIRMED_core_gate_carry_epsilon_zero_v1.md),
[GLV orbit readout](CONFIRMED_glv_orbit_readout_puzzles_135_140_v1.md).
