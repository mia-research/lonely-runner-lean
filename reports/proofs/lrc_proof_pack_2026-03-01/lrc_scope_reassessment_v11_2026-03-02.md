# Scope Reassessment Memo for v11
**Date:** 2026-03-02

## Purpose
This memo records the status reset after parallel-agent updates introduced closure claims that exceeded
validated hypotheses.

## Why reassessment was required

1. Canonical-status conflict appeared between theorem sequence and open-gaps text.
2. Some closure arguments depended on hypotheses not established in canonical proofs.
3. Finite-window certification strength increased materially and needed preservation without asymptotic overclaim.

## Canonical decisions adopted in v11

1. Re-freeze canonical truth to `lrc_ap_grid_extremizer_theorem_sequence_v11.md` and
   `lrc_claim_status_table_v1.csv`.
2. Downgrade post-hoc Gap-closure claims to candidate hypothesis-track unless inserted with full proof in v11.
3. Keep one-divisible certified scope unchanged: all templates for `n in {7,8,9,10,11}` remain certified.
4. Keep multi-divisible widened results as finite-window certified evidence not asymptotic closure.

## Specific downgraded items

- Gap-1 global closure claim using the `lcm(E_fixed)` bound as written.
- Prime-anchor universal closure claims that require additional anchor-membership scope control.
- Composite universal closure claims that need direct compatibility with the canonical `B_div` feasibility criterion.
- Universal S3 closure claims not yet reconciled with full canonical assumptions.

## Preserved strong progress

- Multi-divisible boundary/event certifier and TCP-affine builder are in place.
- Widened n=13 evidence is strong:
  - `3300` templates and `70263` exact seed checks with zero violations.
  - `195448` TCP-affine target checks with zero phi and zero affine-LB violations.

## Open theorem items after reset

1. General TCP extension beyond certified one-divisible range.
2. Multi-divisible asymptotic theorem promotion of component-wise D.2 constants.
3. General composite-`n` Case-2 closure.
4. Universal S3 theorem.

## Immediate next workflow

1. Use v11 as sole status authority.
2. Promote one candidate theorem at a time with explicit hypotheses and contradiction checks against v11.
3. Only then update status rows from OPEN to PROVED/CERTIFIED.
