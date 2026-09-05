# Gap 1 Analytic Route (Band-Aggregate, Anchor-Free)
**Date:** 2026-03-03  
**Status:** Theorem-link chain complete; global closure pending all-n analytic de-enumeration

## Purpose

This note records the active analytic route for Gap 1 without anchor-local claims.
It is constrained to the proved TM / D.1' / D.2' framework and event-cell counting.

## Scope

Template class:

- prime `n`
- one divisible speed `n`
- all-distinct non-divisible class `E = E_fixed union {M}` with `|E_fixed| = n-3`
- one-parameter form `L = L0*M`, `gcd(M,nL0)=1`

Target statement:

- close Gap 1 for this class analytically beyond finite certified `n`,
- without using anchor-only safety claims.

## Proved Inputs Reused

From `lrc_ap_grid_extremizer_theorem_sequence_v11.md`:

- TM1/TM2/TM3 (`§14`)
- D.1' (`§16.7`)
- D.2' (`§16.8`)
- canonical band construction (`§16.9`)
- exact identity `x0 = sum_b A_b` with `B_safe` lower-bound interface (`§5`)

From implementation artifacts:

- boundary/event exact checker kernel
  `lrc_case2_d3_batch_certify_boundary_v1.py`
- certified overlap consistency against earlier certifiers on existing ranges.

## Candidate Lemma Chain (Gap-1 analytic track)

### G1.A Event-cell partition on canonical bands

Partition `I_tot = I_lo union I_hi` by boundary events:

- fixed-floor jump points `floor(kL/e)` and `+1` for each fixed `e` and `0<=k<=e`,
- free-floor block edges `uL0` and `uL0+1` for relevant block indices `u`,
- band endpoints.

On each cell, fixed runner states are constant.

Status: canonical partition construction now used in `v11` §17.8.

### G1.B Cellwise bad-count cap without anchor assumptions

On each event cell `C` in the frozen-fixed regime, combine TM3 with residue/block counts
to obtain a cap of form:

`C_bad(C) <= |C|/n + delta(C)`,

where `delta(C)` is endpoint-only (no linear `|C|` term).

Status: inserted in canonical sequence as Lemma G1.B (`v11` §17.7) with explicit endpoint constant `delta(C)=2L0` under explicit TM 2-miss cell hypotheses.

### G1.C Global aggregate defect bound

Summing cellwise caps over `I_tot` should yield:

`C_bad(I_tot) <= |I_tot|/n + K_F`,

with `K_F` depending on event complexity (cell count and endpoint effects), not on `M`.

Status: inserted in canonical sequence as Lemma G1.C (`v11` §17.8) with explicit `M`-independent constant `K_F^*=2L0(2+4S_F)`.

### G1.D D.2-style safe-mass conversion

From `B_safe = |I_tot| - C_bad`:

`B_safe(I_tot) >= ((n-1)/n)|I_tot| - K_F`.

Combine with canonical band-size lower bound from `§16.9`:

`|I_tot| >= 2L*(1/e_max - 1/n) - c0_F`, `L=L0*M`,

to produce affine lower bound:

`B_safe >= a_F*M + b_F` with explicit `a_F>0`.

Status: inserted in canonical sequence as Corollary G1.D (`v11` §17.9) with explicit `(a_F,b_F,M0)` formulas under §17.8 hypotheses.

### G1.E Residual small-`M` bridge

Define finite checkset

`T_G1(F) = {1 <= M < M0(F) : gcd(M,nL0)=1}`

with `M0(F)` from G1.D.

Status: inserted in canonical sequence as Theorem G1.E (`v11` §17.10), reducing each template to finite exact checks below `M0(F)` plus analytic tail for `M>=M0(F)`.

### G1.F Template-free M0 envelope (de-enumeration step)

Analytically bound `M0(F)` by an `n`-only polynomial envelope.

Status: inserted in canonical sequence as Lemma G1.F (`v11` §17.11):
`M0(F) <= n^2(3+4S_F)+1 <= 3n^4+1`.


### G1.G Finite-strip reduction

Use G1.E + G1.F to move all residual small-`M` checks into template-free bounded envelope
`U_n^* = {1 <= M < 3n^4+1, gcd(M,n)=1}`.

Status: inserted in canonical sequence as Theorem G1.G (`v11` §17.12).

### G1.I Canonical fixed-signature complexity bound

On prime one-divisible all-distinct canonical bands, fixed-signature partition complexity is at most
three cells (`m_tot<=3`).

Status: inserted in canonical sequence as Lemma G1.I (`v11` §17.17).

### G1.J Sharpened aggregate constant and M0 envelope

Using G1.I with the G1.B cell cap gives:

`C_bad(I_tot) <= |I_tot|/n + 6L0`,

hence a sharpened affine tail and template-free threshold envelope
`M0^sh(F) <= 4n^2+1` (improving the prior `O(n^4)` envelope).

Status: inserted in canonical sequence as Corollary G1.J (`v11` §17.18).

### G1.K Exact reduced Delta_tr criterion

On the `m_tot<=3` reduced geometry, define

`Delta_tr^sh = |I_tot|/n + K_loc^sh - C_bad(I_tot)`, `K_loc^sh=2L0*m_tot`.

Then `Delta_tr^sh>=0` and Gap-1 strip closure is equivalent to uniform
`Xi_tr(F,M)=0` (explicit residual form in `v11` §17.19).

Status: inserted in canonical sequence as Theorem G1.K (`v11` §17.19).


## Why this route is validly scoped

- No use of "all nontrivial anchors are safe" type claims.
- No reliance on invalid `lcm(E_fixed)` shortcuts.
- Compatible with existing TM/D.1'/D.2' logic and boundary certifier model.

## Remaining closure work for Gap 1

1. TM2 obstruction is now eliminated in prime Gap-1 scope by `§17.16` (`O_tm2=empty`, hence `E_tm2=0`).
2. Prove the bounded-strip uniform analytic claim (G1.G.2) via target theorem G1.H / G1.K reduced form, i.e., establish uniform `Xi_tr(F,M)=0` (equivalently the `Delta_tr` threshold inequality).

Gap 1 remains open at this analytic de-enumeration layer; additional certified `n` runs are support evidence only.
