# G4.OT Blocker Memo (v1)
**Date:** 2026-03-07  
**Purpose:** record why the proposed `G4.OT` / `§17.35` closure is not canonizable in the current pack, and isolate the correct repair target.

## 0) Verdict
The proposed `G4.OT` closure should **not** be promoted to the canonical proof track.

Reason:
- the attempted proof does contain salvageable interval lemmas,
- but the main Case-B / Case-iiib argument leaves the locked H1-H7 object language and does not prove the live blocker.

So the correct status remains:

`Case-B (n>=10) positivity / existence = OPEN`.

## 1) Canonical blocker being targeted
In the live Case-B near-complete track, the remaining Case-iiib theorem target is:

`exists tau in B_div path with U_fix(tau) != Z_n`

equivalently

`exists r in Z_n with Miss(r) != empty`,

where

`Miss(r) = I_div \ union_{e in E_fix} Cov_e(r)`.

This is the fixed-side miss geometry statement recorded in:
- `lrc_g4open_near_complete_lemma_v1.md`
- `lrc_g4open_sl1b_track_v3.md`
- `lrc_gap4_scope_lock_audit_v1.md`

## 2) Why the attempted `G4.OT` proof is not theorem-grade

### Blocker A: scope mismatch
The attempted Case-B proof reasons with the dropped runner `a` as if its bad set contributes to

`U_fix(tau)`.

But in the locked near-complete setup:
- `E_fix = {1,...,n-1} \ {a,b}`,
- `U_fix(tau) = union_{e in E_fix} bad_set(e,tau_e,n)`.

So any proof step of the form

`U_fix = U_unit union B_a`

is outside the live theorem target.

This is the central failure mode.

### Blocker B: false τ=0 identity
The attempted text asserts that when both dropped elements are non-units, the unit contribution at `tau=0`
already gives all of `Z_n`.

That is false as stated for composite `n`:
- the unit runners cover the unit residues (and `0`) at `tau=0`,
- non-unit residues require non-unit contributions.

So the attempted Step B.1 is not correct in the current notation.

### Blocker C: non-coincidence lemma unproved
The proposed floor-change non-coincidence argument does not prove that some

`k/a`

avoids all unit floor-change positions.

The denominator / prime-factor separation heuristic is not enough:
- equal rationals can coincide after reduction,
- the argument does not produce a valid exclusion criterion for the full union of unit floor-change sets.

So the key transition step is still open.

### Blocker D: cardinality route is not load-bearing
The proof itself finds the failure:

`2 phi(n) <= n-2`

is false for many composite `n` (for example `n=15`).

So even after the scope mismatch, the proposed contradiction route is not robust enough to close Case-B globally.

## 3) What is salvageable
Two auxiliary facts from the attempted `G4.OT` writeup are still useful:

1. **Unit coverability threshold for `r=1`.**
   For a unit runner `e`, residue `1` is coverable only when `e >= ceil(n/2)`.

2. **Contiguous interval structure for `Cov_e(1)`.**
   For active unit `e`, the coverage set of residue `1` is a single contiguous interval in `alpha`.

3. **Unit/non-unit floor-change separation at `alpha=1/a`.**
   If dropped `a` is non-unit, then `alpha=1/a` is not a floor-change point for any unit runner.

These belong naturally in the fixed-side `Miss(r)` program, not in a closure theorem.

They are extracted cleanly in:
- `lrc_g4open_caseb_interval_lemmas_v1.md`
- `lrc_g4open_alpha1_over_a_observation_v1.md`

## 4) Correct repair target
The repair target is **not** "fix the `pq` case" inside the attempted `G4.OT` proof.

The real repair target is:

> prove the Case-B / Case-iiib existence lemma entirely in the fixed-side miss language
> `Miss(r)` / `Cov_e(r)` / `U_fix(tau)`,
> without using dropped-runner coverage as if it were part of `U_fix`.

So the next theorem step should look like one of:
- an existence-only miss lemma in the style of `SL1-O1`,
- a constructive `alpha*` witness in fixed-side coordinates,
- or a direct desynchronization theorem for `Cov_e(r)` unions.

It should **not** be phrased as a dropped-runner coset-shift theorem unless that statement is first translated back into `Miss(r)` on the fixed side.

## 5) Program consequence
No canonical status should be upgraded from this attempted proof.

In particular:
- do not mark `G4.9*` or Case-B `n>=10` as proved,
- do not change the scope guardrail,
- do not replace the existing OPEN status in the audit.

The correct update is narrower:
- keep Case-B existence OPEN,
- retain the empirical evidence,
- promote only the auxiliary interval lemmas that are actually proved.

## 6) Second-pass note on `lrc_g4ot_proof_v1.md`
The later draft improves one local point:
- the claim that `alpha=1/a` cannot be a unit floor-change position is correct and now packaged separately.

But it still does **not** close the main blocker, for two additional reasons:

1. **Unit-only obstruction is not fixed-side obstruction.**
   The `mod-q` lemma in the draft shows at best that a residue is not covered by the unit part
   `U_unit`.
   That does not imply the residue is missing from
   `U_fix`,
   because fixed non-unit runners remain in the union and are not ruled out.

2. **Adjacent-band comparison freezes the wrong background.**
   At `alpha=1/p`, unit runners are frozen, but fixed non-unit runners divisible by `p`
   can also change floor there.
   So the draft's Step-6 comparison does not have a constant non-unit background across the band pair.

3. **Prime-power branch remains non-analytic.**
   The draft explicitly leaves odd prime-power `n=p^k` on computational verification only.
   So even on its own stated route, the theorem status cannot be `PROVED`.

## 7) Status
`CANONICAL-BLOCKER-MEMO`.
