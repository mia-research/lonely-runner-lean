# Unified Alpha-State Geometry Framework (M1–M3) v1
Date: 2026-03-04

## 0. Purpose
This note defines a single shared geometry for the current open chains (`Y`, `Z`, `V`, `W`) so agents can prove against one object instead of piecemeal lemmas.

The shared object is the **alpha-state arrangement**:
- `alpha = b/L in I_div := [1/n, (n-1)/n]`
- `tau(alpha) = ( floor(e*alpha) )_{e in E_fix}`
- `U_fix(tau) = union_{e in E_fix} bad_set(e, tau_e, n)`
- `R_fix(tau) = Z_n \ U_fix(tau)`

All open obligations are projections of this arrangement.

---

## 1. Scope
Default scope `S0` (unless overridden in a sub-lemma):
- Case-2 one-divisible near-complete family.
- `n >= 6`, `E_div = {n}`, `|E_fix| = n-3`.
- `L = L0*M`, `gcd(M, nL0)=1`.
- `B_div = [L/n, (n-1)L/n] intersect Z`.

Case-iiib specialization (Gap-4 blocker):
- `n` composite,
- `1, n-1 in E_fix`,
- `U_fix(tau=0)=Z_n`.

---

## 2. Core definitions
For `r in Z_n`:
- `Cov_e(r) := union_{t: r in bad_set(e,t,n)} ( [t/e,(t+1)/e) intersect I_div )`
- `Miss(r) := I_div \ union_{e in E_fix} Cov_e(r)`
- `m(r) := meas(Miss(r))`

State graph `G=(V,E)`:
- nodes `V`: feasible states `tau` realized on at least one fiber in `B_div`
- directed edge `tau -> tau'`: appears when moving from fiber `b` to `b+1` changes state
- edge label: changed coordinates `Delta(tau,tau')`

---

## 3. Lemma M1 — Transition Algebra
### Statement M1
Across a non-coincident floor boundary `alpha = m/e*` (i.e., only one runner boundary is crossed), only coordinate `e*` changes:
- `tau'_e = tau_e` for `e != e*`
- `tau'_{e*} = tau_{e*} + 1`

Hence only one runner contribution changes in `U_fix`:
- `U_fix(tau') = ( U_fix(tau) \setminus B_old ) union B_new` up to overlap bookkeeping,
  where `B_old = bad_set(e*, tau_{e*}, n)`,
  `B_new = bad_set(e*, tau_{e*}+1, n)`.

### Corollary M1.C (local variation bound)
`|U_fix(tau') - U_fix(tau)| <= |B_old triangle B_new|`.
For general composite arithmetic, this is bounded by `<= 2*gcd(e*,n)` at set-cardinality scale.

### Status
`OPEN` as a formal global proof including coincident-boundary handling.
(Probe script classifies and isolates coincident boundaries.)

---

## 4. Lemma M2 — Miss-Interval Existence
### Statement M2
In Case-iiib, there exists `r* in Z_n` with `Miss(r*) != empty`.
Equivalent discrete statement: there exists a state/fiber with `r* notin U_fix`.

### Reduction target
`M2` is equivalent to proving the covered alpha-set
`union_e Cov_e(r)`
fails to fill `I_div` for at least one residue `r`.

### Status
`PROVED-UNDER-H` in locked sub-scope `Siiib-U`: one-div near-complete Case-iiib with unit dropped runners (`gcd(a,n)=gcd(b,n)=1`, `n>=10`), via Sole Cover witness (`lrc_dropped_runner_witness_v1.md` §11).

Residual outside this sub-scope remains open (notably extensions beyond unit-dropped Case-iiib and full Case-2 universal scope).

---

## 5. Lemma M3 — Counting Bridge
### Statement M3
For any interval `I subset I_div` and `L=L0*M`:
- `N_I(M) := # { b in B_div : b/L in I }`
- `N_I(M) = |I|*L + O(1)`
with explicit integer bounds via floor/ceil endpoints.

In particular, if `|I| >= c > 0`, then
`N_I(M) >= c*L0*M - C` for an absolute template constant `C`.

### Consequence
Any positive-measure miss interval from `M2` yields linear-in-`M` safe mass (`Lambda_eff>0`).
This is the bridge from continuous alpha-geometry to discrete fiber counts.

### Status
`PROVED-UNDER-H` (standard floor/ceil counting; used in current chain).

---

## 6. Master theorem template
### Theorem M* (Conditional closure schema)
Assume `M1` + `M2` + `M3` under `S0`.
Then:
1. `M2 + M3` => `Lambda_eff > 0` (positive slope of safe mass).
2. `M1` supplies local transition control needed for run/period summation bounds.
3. Therefore the Case-iiib branch closes in the same asymptotic + finite-check framework.

So the remaining analytic work is concentrated in globalizing `M2` beyond `Siiib-U` and completing coincident-boundary handling in `M1`.

---

## 7. Agent task split
- Agent A: Prove `M1` for non-coincident boundaries; isolate coincident events.
- Agent B: Extend `M2` beyond `Siiib-U` (unit-dropped Case-iiib already closed).
- Agent C: Package `M3` with exact constants for current scope.
- Integrator: combine into Theorem `M*` and map to `Y/Z/V/W` claims.

---

## 8. Reporting requirements
For any attempted lemma in this framework, report:
1. ID (`M1`, `M2`, `M3`, or sub-lemma)
2. status
3. exact scope
4. derivation (5–10 lines)
5. dependencies
6. blocker (if open)
7. artifact path
