# LRC `n=all` Synthesis Dependency Graph (v1)
**Date:** 2026-03-07  
**Purpose:** compress the current proof architecture into one blocker graph with only genuine frontier branches.

## 1) Target theorem
For every `n >= 3` and every gcd-1 Case-2 tuple `E` of size `n-1`,

`x0(E) >= phi(n)`.

Equivalent discrete reformulations already in pack:
- `B_safe >= n-1` on the fiber model where that reduction is valid,
- `|U_e D_e| < N`,
- `N + sum_{k=1}^{n-1} (-1)^k S_k > 0`.

## 2) Compressed blocker graph

```text
n=all LRC
├── Irrational branch ........................................ PROVED
├── Rational Case 1 (no e divisible by n) .................... PROVED
└── Rational Case 2 (some e divisible by n)
    ├── Small-L base branches (L=n, L=2n) .................... PROVED
    └── Large-L regime (L>2n)
        ├── Prime n, |E_div|=1 near-complete base chain ...... PROVED in scoped Gap-1 program
        │   └── Xi residual / outside-band mass ............... OPEN
        │       maps into ..................................... S3-GENERAL
        ├── |E_div|>=2 multidiv regime ........................ OPEN
        │   └── composite/non-unit residuals overlap with ..... COMPOSITE-N
        └── Composite-n general regime ........................ OPEN
            └── complementarity branch ........................ G4B-COMP-CAP
                ├── local unit z=0 branch ..................... PROVED-UNDER-H
                ├── at_B_div_end branch ........................ PROVED-UNDER-H
                ├── pure non-unit exit existential branch ..... PROVED-UNDER-H
                └── branch integration / component cap ........ OPEN

Global closure target above all large-L branches:
S3-GENERAL .................................................... OPEN-PROGRESS
```

## 3) Genuine blockers only
A statement counts as a genuine blocker only if removing it would leave no theorem-grade route to the target theorem in its branch.

By that rule:
- `G4B-NONUNIT-Z0` is not a top-level blocker anymore.
- `E2-E4` are not top-level blockers; they are composite-n bridge obligations.
- prime regular-`k` multidiv is not open.
- unit-dropped Case-iiib is not open.

## 4) Branch definitions

### Branch A: `G4B-COMP-CAP`
Target:
- prove `|O cap C| <= |C| - n` on each `B_div` component.

Depends on:
- event-local exposure lemmas,
- exit partition correctness,
- branch integration from local exits to component cap.

If closed:
- yields composite complementarity route,
- feeds conditional `G4.C`,
- likely resolves a large piece of `COMPOSITE-N`.

### Branch B: `MULTI-DIV`
Target:
- theorem-grade all-family closure for `|E_div| >= 2`.

Current obstruction:
- finite-window evidence and partial prime closure exist,
- but no universal affine/global theorem binds all families.

### Branch C: `COMPOSITE-N`
Target:
- template-free composite non-unit closure beyond current scoped lemmas and certified slices.

Current obstruction:
- non-unit geometry is understood locally but not globally packaged.

### Branch D: `S3-GENERAL`
Target:
- one structural inequality strong enough to imply `x0(E) >= phi(n)` in the remaining rational large-`L` frontier.

Current manifestations:
- complementarity cap on composite branches,
- outside-band safe mass on prime residual branches,
- multidiv global occupancy on `|E_div|>=2` branches.

## 5) Support layers below the blockers

These are support layers, not frontier branches:
- TM/TCP and canonical band machinery,
- `M1-M3` alpha-state geometry,
- pure-exit NZ0 existential theorem,
- E1 unit essentiality,
- certified event-path and boundary packs,
- exact low-order overlap formulas and CRT identities.

## 6) Blocker interaction

The current graph suggests two kinds of dependence:

1. **Local geometric dependence**
   - `G4B-COMP-CAP`
   - `COMPOSITE-N`

2. **Global occupancy dependence**
   - `MULTI-DIV`
   - `S3-GENERAL`
   - Xi residual / outside-band mass

This is the main synthesis signal: the frontier may compress further to two master problems even if it does not collapse to one.

## 7) Immediate use
Any new theorem attempt should be tagged with exactly one of:
- `BLOCKER:G4B-COMP-CAP`
- `BLOCKER:MULTI-DIV`
- `BLOCKER:COMPOSITE-N`
- `BLOCKER:S3-GENERAL`

If it cannot be tagged this way, it is support or housekeeping, not a frontier move.
