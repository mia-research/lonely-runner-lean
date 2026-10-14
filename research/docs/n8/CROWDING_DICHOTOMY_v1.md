# The crowding dichotomy — a complete structural decomposition of n=8 at the grid

2026-09-11. Script `experiments/n8/ok_dichotomy_v1.py`. Exact `Fraction`, complete
enumeration of `[1..18]`. Formalises the owner's framing: *any arrangement is either runners
off the AP positions, or — if there is crowding — the grid.*

---

## 1. The setting

At `t = a/8`, `a ∈ (ℤ/8)*`, the seven runners land on residues `r_j = e_j a mod 8`, joining
the stationary runner on site 0. Eight sites, eight runners. Either the `r_j` are a bijection
onto `{1,…,7}` — **no crowding, the AP pattern** — or two share a site, **crowding**, and then
by counting some residue of `{1,…,7}` is **vacant**.

Throughout, `L(a) = max_j (1−r_j)/(8e_j)` and `U(a) = min_j (7−r_j)/(8e_j)` are the certificate
bounds of `GRID_CERTIFICATE_v1` §2; `L ≤ U` gives a witness at `t = a/8 + ε` for every
`ε ∈ [L,U]`.

## 2. Four claims, all exact  `[PROVED — complete enumeration, 0 failures each]`

| | claim | check |
|---|---|---|
| **1** | **No crowding ⟹ tight.** If `{r_j}` is a bijection onto `{1..7}` then `L = U = 0` — a witness, with zero slack. | 1152 (tuple, `a`) pairs, **0** failures |
| **2** | **Case 2 ⟹ a vacancy, always.** If some `e ≡ 0 (mod 8)` then at every `a` at least one residue of `{1..7}` is unoccupied. | 81 396 pairs, **0** failures |
| **3** | **The vacancy is steerable iff not Unit-Complete.** `∃a` with residue 7 vacant ⟺ `{e mod 8} ⊉ {1,3,5,7}`. | 31 788 tuples, **0** failures |
| **4** | **After steering, what remains is a speed condition.** With 7 vacated and `e₀` the smallest multiple of 8, `L ≤ U` ⟺ `e_j ≤ (7−r_j)·e₀` for every `j` with `r_j ≠ 0`. | 18 149 tuples, **0** failures |

Claim 1 says the AP pattern *is* the extremal configuration — full occupancy, no vacancy, no
slack. Claim 2 is the pigeonhole that makes crowding unavoidable once a multiple of 8 exists:
it holds site 0 at every `a`, leaving at most six of seven sites for the rest.

Claim 3's mechanism: multiplication by `a` permutes the units `{1,3,5,7}` transitively, so the
occupied odd set `S` becomes `aS`, and `7 ∉ aS` for some `a` iff `S` is a **proper** subset.
Unit-Complete is precisely full occupancy of the units — the AP pattern restricted to the odd
residues.

Claim 4 is the part worth having: once the vacancy sits at 7, the certificate is no longer
about residues at all. It is **`e_j ≤ (7−r_j)·e₀`** — no runner may exceed `(7−r_j)` times the
*slowest* multiple of 8. An explicit, interpretable inequality between speeds.

## 3. The decomposition, exhaustive over `[1..18]`  `[VERIFIED — exhaustive in box]`

| regime | count | share | what happens |
|---|---|---|---|
| Site 0 free at some `a` (Case 1) | 11 439 | **35.99%** | witness at `t = a/8`, no perturbation needed |
| Case 2, crowding steerable (not Unit-Complete) | 18 149 | **57.09%** | vacate 7, then the speed condition — holds for **63.34%** of them |
| Case 2, Unit-Complete | 2 200 | **6.92%** | units fully occupied; no first-order direction exists |

So the two residual obstacles are named exactly: the speed condition failing inside the
steerable class (≈ 20.9% of all tuples), and Unit-Complete (6.92%). Both are largely absorbed
by allowing wraps — `GRID_CERTIFICATE_v1` §4 records `K = 1` covering **99.94%** of Case 2 and
`K = 2` covering 100% in this box.

## 4. What this buys, and what it does not

**Buys.** A complete trichotomy at the grid, each branch with an exact criterion rather than a
residue-shape enumeration. `CASE_TREE_AUDIT_v1` found the previous case tree covered only
54.5% of residue shapes with `|R_non| = 5` "**assumed** … never derived"; this decomposition
has no shape list, no assumption on `|R_non|`, and every branch verified with zero failures.
It also explains *why* the AP is tight (Claim 1: full occupancy means no vacancy means no
slack) and *why* Unit-Complete is hard (Claim 3: the vacancy cannot be steered onto 7).

**Does not.** Claim 4's speed condition holds for 63.34% of the steerable class, not all of it,
and the wrapped coverage is exhaustive **in a box** with `K` unbounded a priori. Nothing here
proves `n = 8`. The honest statement is that the problem now factors into two named finite
questions — bound `K`, and handle Unit-Complete — rather than 27 residue shapes.

## 5. Ledger

`[PROVED — complete enumeration]` §2, all four claims, 0 failures at 1152 / 81 396 / 31 788 /
18 149 checks respectively.
`[VERIFIED — exhaustive in box]` §3's decomposition and the 63.34% rate.
`[SCOPE]` Claims 1–4 are unconditional in the speeds (they are statements about residues and
an inequality); the *rates* in §3 are box-dependent.

`n = 8` is **not proved**, and nothing here moves a grade.
