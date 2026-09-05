# Gap-2 Multi-Divisible Boundary Certifier (v1)

Status: implementation progress artifact for Gap 2. Not a theorem closure claim.

## Added tool

`lrc_case2_multidiv_boundary_certifier_v1.py`

Purpose:
- Computes exact `x0` and `B_safe` for multi-divisible families using boundary/event aggregation.
- Uses interval-intersection `B_div` geometry (no per-`b` scan to build `B_div`).
- Avoids per-`b` evaluation across all fibers in production mode.
- Optional `--validate-bruteforce` cross-check runs a reference per-`b` kernel.

## Core method

For each `M`:
1. Build `L = L0*M`, `L0 = lcm(E_fixed U E_div)`.
2. Compute `B_div` as a finite union of integer components from
   `S = ⋂_f {x: frac(fx) in [1/n,(n-1)/n]}`.
3. For each component, split into fixed-event cells (`kL/e`, `kL/e+1`) so fixed signature is frozen per cell.
4. Count free-runner classes on each cell analytically via `(t_M mod n, z_M)` block counts.
5. Aggregate exact `x0`, `B_safe`, `B_div`.

Also emits a component-wise D.2-style diagnostic lower bound:
- `d2_lb_floor` from band intersections + additive error terms.
- Used for asymptotic tracking only in this note.

## Validation performed

All runs below used `n=13`, `E_fixed={1..9}`, `M={11,17,19}` with `--validate-bruteforce`:

- `E_div=(13,26)` -> exact parity vs brute-force.
- `E_div=(13,39)` -> exact parity vs brute-force.
- `E_div=(26,39)` -> exact parity vs brute-force.
- `E_div=(13,26,39)` -> exact parity vs brute-force.

No mismatches observed in `x0`, `B_safe`, `B_div`, or component count.

## Gap relevance

This closes the computational kernel needed for component-wise multi-divisible certification:
- interval `B_div` geometry from `v2`, plus
- exact boundary/event counting over component unions.

Remaining work for formal Gap 2 closure:
1. Prove the component-wise D.2-style bound (currently diagnostic) in the theorem chain.
2. Add template builder/checkset logic for `|E_div|>=2` families and batch artifacts.
