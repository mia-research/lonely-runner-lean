# Can the grid architecture reach non-grids by density?

2026-09-13. n = 8, individual isolation, threshold 1/8. Tests the proposal that since grids are
infinite and scale, the grid theorem of `GRID_THEOREM_v1` should cover everything.

---

## 1. Grids are dense — the premise is right  `[PROVED — construction]`

Given any `V` and any `ε > 0`, there is a grid within `ε` of it. Take gcd `g = 1/q` and place
`w_i = v_1 + m_i/q` with the `m_i` chosen to have distinct residues mod 8; as `q` grows the `m_i`
can hit their targets to within `1/q`. So the grid family is dense in configuration space.

Worked on `(1,2,3,4,5,6,7,9)`, a non-grid (r1 and r8 share residue 1):

| `q` | max `|w − v|` | is a grid | `g` | `d_min(r1)` | `d_min = g`? | r1's moment |
|---|---|---|---|---|---|---|
| 8 | 0.5000 | yes | 1/8 | 9/8 | **no** | 9/68 |
| 64 | 0.0625 | yes | 1/64 | 65/64 | **no** | 6/43 |
| 256 | **0.0156** | yes | 1/256 | 257/256 | **no** | **8/57 = 0.14035** |

and the true value for `V` is `9/64 = 0.140625`. **The moments do converge.**

## 2. But the theorem does not ride along  `[VERIFIED]`

`GRID_THEOREM_v1` requires `d_min = g` for every runner. In every approximating grid above,
`g → 0` like `1/q` while `d_min(r1)` stays near 1 — the runners' actual neighbour gaps do not
shrink just because the gcd does. **The hypothesis fails for all of them**, so the theorem says
nothing about any approximating grid, however close.

The theorem's reach is `s = d/g ∈ ℤ` *and* `d_min = g`. Fine grids keep the first and lose the
second.

## 3. And the moment is discontinuous  `[VERIFIED — exact]`

Approaching the AP by varying r1:

| r1 | 0.5 | 0.9 | 0.99 | 0.999 | **1** | 1.001 | 1.01 | 1.1 |
|---|---|---|---|---|---|---|---|---|
| r1's moment | 0.0833 | 0.1136 | 0.1238 | 0.1249 | **0.1250** | **0.6251** | 0.6263 | 0.4529 |

**From below the moment tends to `1/8`; from above it tends to `1/2`.** A one-sided jump by a
factor of five, at the configuration the whole series is organised around.

So no stability estimate of the form *"`W` within `δ` of `V` ⟹ moments within `f(δ)`"* can hold —
and the configurations where it fails are the degenerate ones, where a constraint sits exactly on
the threshold. Those are precisely the hard cases. An approximation argument would have to survive
exactly where it breaks.

## 4. Conclusion

| | |
|---|---|
| grids infinite and dense | **true** |
| moments converge under grid approximation at ordinary configurations | **true** |
| the grid theorem transfers | **no** — its hypothesis fails for every fine approximating grid |
| density gives a proof for non-grids | **no** — the moment is discontinuous at the degenerate configurations, which are the hard ones |

The grid case is closed because a grid makes `s = d/g` an **integer**, so "within 1 of a multiple
of 8" collapses to "`≡ 0 mod 8`", which distinct residues forbid. A non-grid has `s` irrational or
merely non-integral, and no amount of rescaling changes that — grid-ness is scale-invariant, since
dilating by `k` multiplies both `d` and `g` by `k`.

**What would be needed** is not a denser family but a handle on `dist(s, 8ℤ)` for non-integral
`s` — a Diophantine question about the difference set, not a covering argument.

## 5. Status

`[PROVED — construction]` §1's density.
`[VERIFIED — exact]` §1's convergence table; §2's hypothesis failure; §3's discontinuity.
`[CONCLUDED]` §4 — the architecture does not extend to non-grids by density.

**n = 8 is not proved here.** The open first-interval claim of `ANALYTIC_STATUS_v1` is untouched.
