# The dichotomy without the 8 — general `n`

2026-09-11. Script `experiments/n8/ok_general_n_dichotomy_v1.py`. Exact `Fraction`.
Owner's correction: the modulus 8 was incidental; the structure is mod `n`. Generalises
`CROWDING_DICHOTOMY_v1` and `GRID_CERTIFICATE_v1`, which were stated only at `n = 8`.

---

## 1. Global isolation, general `n`  `[PROVED — 5 lines, from the φ(n) law]`

`n` runners: one stationary at 0 plus `n−1` distinct positive speeds `E`, `gcd(E) = 1` (WLOG
by dilation-invariance).

**Step 1 (gap-sum).** `n` points on the circle have `n` gaps summing to 1. Global isolation
demands each `≥ 1/n`; `n` numbers each `≥ 1/n` summing to 1 are all exactly `1/n`. The
configuration is the exact `n`-grid, and it contains 0, so it is `{k/n}`.

**Step 2 (denominator).** Hence `n·e_j·t ∈ ℤ` for all `j`. With `t = p/q` in lowest terms,
`q | n·e_j` for every `j`, so **`q | n·gcd(E)`** — primitivity is load-bearing here — giving
`q | n`. And `q < n` yields at most `q < n` sites. So `t = p/n`, `gcd(p,n) = 1`.

**Step 3 (φ(n)'s own algebra).** At `t = p/n`, `e_j t ≡ (e_j p mod n)/n`, and multiplication
by `p` permutes `ℤ/nℤ` because `gcd(p,n) = 1` — the identical step the φ(n) law uses.

> **Global isolation ⟺ `{e_j mod n}` is a bijection onto `{1,…,n−1}`, and it then occurs at
> exactly the `φ(n)` times `t = p/n`, `gcd(p,n) = 1`.**

This is the φ(n) law with the **AP hypothesis removed**. The AP is the identity representative
of the residue system; nothing about arithmetic progression is used. Worked cases:

| runners | residues mod `n` | grid? |
|---|---|---|
| `n=4`, `{1,2,3}` | `0,1,2,3` | ✓ at `t = 1/4` |
| `n=4`, `{1,2,3,4}` (no stationary) | `0,1,2,3` | ✓ at `t = 1/4` |
| `n=6`, `{1,2,3,4,5}` + stationary | `0,…,5` | ✓ at `t = 1/6` |
| `n=6`, **`{1,2,3,4,6}`** + stationary | `0,0,1,2,3,4` | **✗ — no grid time exists** |
| `n=6`, `{1,2,3,4,11}` | `0,…,5` | ✓ (`11 ≡ 5`) |
| `n=6`, `{7,2,9,4,5}` | `0,…,5` | ✓ (scrambled) |

`{1,2,3,4,6}` fails because `6 ≡ 0 (mod 6)`: that runner lands on the stationary one. The
valid fifth speeds are exactly `≡ 5 (mod 6)`.

## 2. The certificate, general `n`  `[PROVED]`

At `t = a/n + ε`, `a ∈ (ℤ/n)*`, with `r_j = e_j a mod n`, runner `j` needs
`‖r_j/n + e_j ε‖ ≥ 1/n`; the admissible interval containing `ε = 0` is
`[(1−r_j)/(n e_j), (n−1−r_j)/(n e_j)]`. So

> `L(a) = max_j (1−r_j)/(n e_j)`, `U(a) = min_j (n−1−r_j)/(n e_j)`; **`L(a) ≤ U(a)` ⟹ every
> `ε ∈ [L,U]` is a witness.**

## 3. The three claims, verified at every small `n`  `[VERIFIED — exhaustive, 0 failures]`

| | `n=4`, `[1..26]` | `n=5`, `[1..22]` | `n=6`, `[1..18]` | `n=7`, `[1..16]` |
|---|---|---|---|---|
| primitive tuples | 2251 | 6949 | 8436 | 7980 |
| **C1** bijection ⟹ `L=U=0` (tight) | 0 fail | 0 fail | 0 fail | 0 fail |
| **C2** some `e ≡ 0 (n)` ⟹ a vacancy at every `a` | 0 fail | 0 fail | 0 fail | 0 fail |
| **C3** steerable ⟺ occupied units `≠` all units | 0 fail | 0 fail | 0 fail | 0 fail |
| **control** fired certificate is a real witness | 0 fail | 0 fail | 0 fail | 0 fail |

Together with `n = 8` (`CROWDING_DICHOTOMY_v1`, 1152 / 81 396 / 31 788 checks, 0 failures),
the dichotomy holds at `n = 4,5,6,7,8`:

- **No crowding** (residues a bijection) = the grid = **tight**, `L = U = 0`, zero slack.
- **Crowding** ⟹ a vacancy in `{1,…,n−1}`, which is room.
- The vacancy is **steerable onto `n−1`** iff the occupied units are a proper subset of
  `(ℤ/n)*` — multiplication by a unit permutes the units transitively, and `n−1 ≡ −1` is a
  unit. Full occupancy of the units is the Unit-Complete obstruction, at every `n`.

## 4. What this does and does not settle

**Does.** The structure is `n`-generic, not an artefact of `2³`. The grid base is a residue
system mod `n`, not an arithmetic progression; global isolation has a five-line criterion and
an exact count `φ(n)`; and the crowding/steering/Unit-Complete trichotomy is the same at every
`n` tested.

**Does not.** Nothing here is a coverage theorem. `GRID_CERTIFICATE_v1` §4's rates and
`RESIDUAL_ANGLE_v1`'s remain exhaustive **in a box**, with the wrap depth `K` unbounded a
priori, and `K_STATISTIC_RETRACTION_v1` records that `K` is anti-correlated with difficulty —
so large `K` is not itself the obstruction. LRC is not proved at any `n` by this route; the
small-`n` cases stand on their existing proofs.

## 5. Ledger

`[PROVED]` §1, the general global-isolation criterion and the `φ(n)` count, from the gap-sum
plus the φ(n) law's own permutation step; §2 the general certificate.
`[VERIFIED — exhaustive, 0 failures]` §3 at `n = 4,5,6,7`, with a fired-certificate control.
`[CORRECTED]` `n=6`, `{1,2,3,4,6}` does **not** achieve global isolation (`6 ≡ 0 mod 6`);
`{1,2,3,4,5}` and `{1,2,3,4,11}` do.
`[SCOPE]` §3's tables are complete within the stated speed ranges; the claims themselves are
statements about residues and are unconditional.

`n = 8` is **not proved**, and nothing here moves a grade.
