# CONFIRMED — The Public Key Determines the GLV Carry `ε = 0` (Core Gate, s < 3/16)

**Grade: PROVED (derivation below) + VERIFIED (2,000,000 lift points, 0 violations;
real puzzle keys #135/#140; firing control).**
Date: 2026-08-16. Curve: secp256k1, `p = 2^256 − 2^32 − 977`, `y² = x³ + 7`.

## Statement

From the **public** `x`-coordinate alone we compute the normalized Eisenstein lift
norm `s = u² − uv + v² ∈ [0, 3/4]` (exact rational arithmetic). Then:

> **`s < 3/16`  ⟹  the GLV endomorphism carry `ε = 0`**, and `3/16` is the exact
> tight threshold.

Therefore for any public key with `s < 3/16` — including **#135** (`s = 0.058933`)
and **#140** (`s = 0.019792`) — `ε = 0` is **determined from public data alone**.

## Proof

The GLV endomorphism `β` on `𝔽_p` corresponds to multiplication by `ω` on the
Eisenstein lift. With lift coordinates `(u,v)` (each reduced to `[−½, ½]`), representing
`u + vω`:

```
ω·(u + vω) = uω + vω² = uω + v(−1−ω) = −v + (u−v)ω   ⇒   (u,v) ↦ (−v, u−v).
```

The carry is the rounding that returns this to the cell:
`ε = (round(−v), round(u−v))`. Since `|v| ≤ ½`, `round(−v) = 0`, so

```
ε = 0   ⇔   |u − v| ≤ ½.
```

Maximize the linear form `ℓ = u − v` on the ellipse `Q(u,v) = u² − uv + v² = s`.
With `Q = [[1, −½], [−½, 1]]`, `det Q = 3/4`, `Q⁻¹ = (4/3)[[1, ½], [½, 1]]`,
and `ℓ = (1, −1)`:

```
max |u − v| = √( s · ℓᵀ Q⁻¹ ℓ ) = √(4s/3) = 2√(s/3).
2√(s/3) ≤ ½   ⟺   s ≤ 3/16.
```

Hence `s < 3/16 ⟹ |u−v| < ½ ⟹ ε = 0`. ∎  The bound is tight: at `s = 3/16` the
extremal lift has `|u−v| = ½` exactly.

## Verification

- **Geometry (2,000,000 random lifts):** points with `s < 3/16` and `ε ≠ 0`: **0**.
  Max `s` among `ε=0` points = `0.24988`; min `s` among `ε≠0` points = `0.18754`.
  Boundary sits exactly on `3/16 = 0.18750`. Exact check `2√((3/16)/3) = 0.500000`.
- **Real keys:** #135 and #140 both give carry `(0,0)`, verified against the *actual*
  lift of `βx`: `eis(βx) = ω·eis(x) − ε` holds with `ε = 0` (not assumed — checked).
- **Firing control:** for `x` with `s ≥ 3/16`, only `200/951 ≈ 21%` have `ε = 0`
  (the gate does real work; carry is genuinely nonzero 79% of the time above threshold).

## Reproduction

```python
from fractions import Fraction as F
p = 2**256 - 2**32 - 977
a = 367917413016453100223835821029139468249
b = 64502973549206556628585045361533709078
beta = 0x7ae96a2b657c07106e64479eac3434e99cf0497512f58995c1396c28719501ee
def lift_uv(X):
    u = F(X*(a-b), p) - round(F(X*(a-b), p))
    v = F(-X*b, p)   - round(F(-X*b, p))
    return u, v
def carry(X):
    u, v = lift_uv(X)
    up, vp = -v, (u - v)                     # apply omega
    cu, cv = round(up), round(vp)            # carry epsilon
    ubx, vbx = lift_uv((beta*X) % p)         # actual lift of beta*X
    return (cu, cv), (up-cu == ubx and vp-cv == vbx)
x135 = 0x145d2611c823a396ef6712ce0f712f09b9b4f3135e3e0aa3230fb9b6d08d1e16
x140 = 0x1f6a332d3c5c4f2de2378c012f429cd109ba07d69690c6c701b6bb87860d6640
print(carry(x135))   # -> ((0, 0), True)
print(carry(x140))   # -> ((0, 0), True)
```

## Scope of the object

`ε` here is the carry under the **coordinate-wise reduction** used in the project's
Core-Gate scripts (`eisenstein-core-gate-real-keys.py`) — the exact `ε` the Core Gate
refers to. The result: this `ε` is not merely asserted but **provably** zero whenever
`s < 3/16`, and that condition is a public, exactly-computable function of `x`.

Related: [CONFIRMED_glv_orbit_readout_puzzles_135_140_v1.md](CONFIRMED_glv_orbit_readout_puzzles_135_140_v1.md),
[CAPABILITIES_glv_orbit_readout_what_it_enables_v1.md](CAPABILITIES_glv_orbit_readout_what_it_enables_v1.md).
