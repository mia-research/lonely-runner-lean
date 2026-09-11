# The residual: the denominator route is equivalent, and the `Σα` bound is an equality at `E*`

2026-09-11. Scripts `experiments/n8/ok_modfamily_v1.py`, `ok_margin_decomp_v1.py`. Exact
arithmetic. Runs the test pre-registered at `CRT_STAR_STRUCTURE_v1` §7.

---

## 1. The adapted family, and why it cannot be the answer  `[PROVED / VERIFIED]`

`PRIME_BOUND_NULL_v1` §2 gives `ρ(d) = 3/4 + 1/d` for `8 | d`, maximal at `d = 8`; and at
`d = 8m` a multiple-of-8 speed demotes, `‖8δ·a/(8m)‖ = ‖δ·a/m‖`. That is the 2-adic
filtration — the shape Barajas–Serra used at `p = 7` for n=7. Predicted family: `d = 8m`.

| family | coverage of the complete `[1..18]` residual (6250) |
|---|---|
| `{8m : m ≤ 15}` | **100.00%** |
| `{16,24,40,56}` | 99.02% |
| `{24}` alone | 69.39% |
| greedy minimum over `9..40` | `{31, 23, 16, 13}` — 4 moduli, 100% |

Greedy prefers `d = 31` (97.5% alone), not a multiple of 8, because the expected count is
`φ(d)·ρ(d)^7` and `φ` growing beats `ρ` decaying. And the fixed family degrades with the box:
uncovered 0.040% / 0.343% / 0.938% / **1.615%** at `[1..30] / [1..80] / [1..400] / [1..4000]`,
consistent with the `lcm` adversary of `DENOMINATOR_TOWER_v1` §4.

**The route is equivalent to the problem, not a reduction.** `[VERIFIED — exact]` At
`E* = (2,6,7,8,10,13,14)`, with `|G| = 93/14560 = 0.00638736`:

| `d` | 31 | 101 | 401 | 1601 | 6401 | 25601 | 102401 |
|---|---|---|---|---|---|---|---|
| `N_d/d` ÷ `\|G\|` | 0 | 3.100 | 1.562 | 0.978 | 1.027 | 1.003 | **0.9999** |

`N_d/d → |G|`, so "some `d` has `N_d > 0`" ⟺ `|G| > 0`. The denominator route makes the easy
69.29% explicit and **cannot close the residual**. Recorded so the route is not re-opened.

## 2. The pre-registered test, and its committed falsification  `[FALSIFIED as pre-registered]`

**Control, committed in advance** (`CRT_STAR_STRUCTURE_v1` §7): the three tight instances must
give margin exactly `0`. They do — `min_O Σα` is **exactly 1** at all three, with the
minimising splits `H = (1,4,6,7)`, `(1,4,7,12)`, `(4,5,11,13)`.

At `E*`: `H = (2,6,8,10,14)`, `O = {7,13}`, `min Σα = 973/1066`. Star components of `S_x/x`:

| index set | contribution to the LHS |
|---|---|
| `{2}` (64) | `857/44590` = **+0.019220** |
| `{2,5}` | `11/455` = **+0.024176** |
| `{2,7}` | `−235/17836` = **−0.013176** |

**The components do not share a sign.** The 5-component pushes the wrong way, the 7-component
rescues it, and the criterion holds only after they are combined:
`LHS = 11/364 = 0.030220 < 41/1120 = 0.036607 = RHS`. The pre-registered falsification
condition — "if the margin cannot be written as a sum of local contributions each bounded away
from the wrong sign" — **is met**. So the star decomposition is **descriptive, not probative**
for this criterion, exactly as §7 committed. No grade moves.

## 3. What the test found that was not asked for  `[PROVED — exact, two independent routes]`

    |G_H| · (1 − Σα)  =  (41/560)(93/1066)  =  93/14560  =  |G(E*)|

and the §5 criterion's own margin `|G_H|/2 − (S_x/x + S_y/y)` is **also** `93/14560`. `|G(E*)|`
was computed independently by exact breakpoint cells over `lcm(E)`, never touching `α`.

> **The `Σα` bound is an *equality* at `E*`, not an inequality.**

By `ALPHA_v1` §3 equality holds exactly when the concentrations are disjoint, so
`A₇ ∩ G(H)` and `A₁₃ ∩ G(H)` are disjoint at `E*`. This places `E*` in the same class as the
three tight instances — all four are equality cases — separated only by `Σα < 1` versus
`Σα = 1`.

**The consequence is a caution, and it is the honest reading.** Where the bound is an equality
it is not lossy, so proving the criterion at `E*` is proving `|G(E*)| > 0` — no easier.
`SIGMA_ALPHA_v1` §4 flagged this as possible ("this may be a reformulation, not a reduction");
§3 here **confirms it at the extremum**, by exact identity rather than by failure to find a
counterexample.

## 4. Where that leaves the residual

Three routes are now measured to be equivalent to `|G| > 0` rather than reductions of it: the
denominator route (§1, by `N_d/d → |G|`), the `Σα` criterion at the extremum (§3, by exact
equality), and — from `WHERE_THE_PROOF_IS_v2` §1 — pure positivity, which is impossible. What
survives is unchanged: `ov ≤ 4` covering 96.3% of Case 2 with `min |G| = 0.014881`, and no
method for that 96.3%.

**The sharp equality case is still the asset.** A criterion whose boundary is exactly the zero
set of `|G|` is the shape a provable inequality has; what §3 shows is that the proof cannot
come from splitting it into independent local pieces, because at the extremum the pieces carry
opposite signs and the true margin is their cancellation.

## 5. Ledger

`[VERIFIED — exact]` §1 the coverage table, the box-degradation row, and `N_d/d → |G|` at `E*`.
`[PROVED — exact]` §2 the control (`min_O Σα = 1` at all three tight instances) and the
three star components; §3 the identity `|G_H|(1−Σα) = |G(E*)| = 93/14560`, confirmed by two
independent computations.
`[FALSIFIED — as pre-registered]` §2, the margin does not split into same-signed local parts.
`[NEGATIVE — scoped]` §1, the denominator route for the residual: object = `N_d`, observable =
witness existence at rational `t = a/d`, power = exact at `E*` to `d = 102401`, scope = `E*`
plus the box coverage tables.

`n = 8` is **not proved**, and nothing here moves a grade.
