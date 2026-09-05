# LRC Case-2 TM Lemma Chain (Checkpoint)

Date: 2026-03-01

This document records the mechanism-first theorem block for the large-L Case-2 gap.

## Setup

Work in normalized lattice `N = nL` with `|E|=n-1`, `gcd(E)=1`.
Let `F` be fixed runners and `M` the free runner.

For runner `e` and fiber `b`:
- `t_e(b) = floor(e b / L)`
- `s_e(b) = e b mod L`

For each fiber:
- `U_fix(b)` = bad-a union from fixed runners
- `U_M(b)` = bad-a set from free runner
- `R_fix(b) = Z_n \\ U_fix(b)` (fixed missing set)

Define `C_bad(I)` as the number of bad fibers in interval `I`.

## Lemma TM1 (exact 2-point obstruction)

Assume on fiber `b`:
- `|R_fix(b)| = 2`
- `|U_M(b)| = 2` (equivalently `s_M(b) != 0`)

Then:

`b` is bad iff `U_M(b) = R_fix(b)`.

So badness is an exact 2-point matching condition.

## Lemma TM2 (free-pair rotation on frozen-fixed band)

Let `I` be a contiguous band where all fixed floors are constant:
`forall e in F, t_e(b) = tau_e` on `I`.

Then `R_fix(b)` is constant on `I`; write it `R_fix`.
Let `alpha = M^{-1} mod n`, `t=t_M(b)`.
On `I`:

`U_M(b) = { -t alpha, -(t+1) alpha }`.

So each `t -> t+1` translates the free bad pair by `-alpha` in `Z_n`.

## Lemma TM3 (single residue class cap)

Write `R_fix={u,v}` and `delta_fix = v-u` (unordered up to sign).

1. If `delta_fix != +-alpha (mod n)`, then `C_bad(I)=0`.
2. If `delta_fix = +-alpha`, bad fibers in `I` can only occur when
   `t_M(b)` lies in at most one residue class mod `n`.

Hence (up to boundary/exception terms) bad-fiber density in `I` is at most `1/n`.

## Theorem C2-large-L (band-density form)

Suppose a family has a band `I_M subset B_div` with:
1. `|I_M| = lambda M + beta`, `lambda > 0`
2. fixed floors frozen on `I_M`
3. `|R_fix|=2` on `I_M`
4. exceptional set `Z_M={b in I_M : s_M(b)=0}` satisfies `|Z_M| <= zeta` uniformly

Then there exists `K` such that

`C_bad(I_M) <= |I_M|/n + K`

and therefore

`B_safe >= |I_M| - C_bad(I_M) >= ((n-1)/n)|I_M| - K`.

Since `|I_M|` is linear in `M`, this implies `B_safe >= n-1` for all large `M`; finite verification closes small `M`.

## Next immediate insertion

Specialized corollary for F1246689:
- `L=792M`
- `I_M=[72M,88M-1]`
- fixed `t_e=0` on `I_M`
- fixed union misses 3 residues while free runner contributes at most 2
- therefore all fibers in `I_M` are safe and `B_safe >= 16M >= n-1`.
