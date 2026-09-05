# GATE OWED + self-audit — `PREREG_semaev_cm_relation_yield_v3.md`

> **✅ RESOLVED 2026-08-07 — GATE CLEARED.** After the 11:30am Brisbane rate-limit reset, the
> `experiment-designer` third pass completed and returned **"cleared to run — no blocking findings"**
> (4 non-blocking cosmetic cleanups only; the remaining v2 blocker — κ as a single-target-`quo`
> benchmark — confirmed RESOLVED, §5/§7 conflict gone, α/MDE arithmetic self-consistent, H1+Scaling
> sound). **The gate is no longer owed; the run is GRADEABLE, not provisional.** The three frame items
> the self-audit flagged as uncovered were examined by the completed isolated pass. The record below is
> retained for the audit trail.

**[Historical, while the gate was unavailable]** Status of outputs until the gate cleared:
`[PROVISIONAL — experiment-designer gate unavailable]`. Per CLAUDE.md §2a (gate UNAVAILABLE ≠ gate FAILED).

## Owed-gate record (condition 3)
- **Gate:** `experiment-designer`, third pass, verifying the v2→v3 delta.
- **Attempted:** 2026-08-07 (agent `aa9ac854ec20be5ae`, resumed on v3).
- **Why it did not run:** terminated by an API **session/rate limit** ("You've hit your session limit ·
  resets 11:30am Australia/Brisbane"). Infrastructure, not a finding — this is the §2a rate-limit branch,
  not "the gate is slow / I am confident."
- **Re-run owed:** at/after the 11:30am Brisbane reset. Until then, no grade promotion (condition 4).
- **Prior coverage (not a substitute, but relevant):** v1 pass (3 blocking, incl. the benchmark + `#E`
  identification worries) and v2 pass (B2 `#E`-confound RESOLVED, B3 power RESOLVED, H1+Scaling declared
  sound; one remaining blocking = the κ/H2 benchmark, which is exactly what v3 fixes) both completed
  context-isolated. The v3 delta is **corrective** (removes the κ overclaim, removes the conservation
  ceiling), not a new mechanism.

## Self-audit of the v3 delta (condition 2) — what it can and cannot discharge

Per the §2a table, a self-audit (no context isolation) discharges **mechanical** layers with the
artifact, and does **NOT** discharge **frame** layers. Stated honestly for each v3 change:

### Mechanical — self-audit + artifact SUFFICIENT
- **α/MDE arithmetic (§7).** Verified by direct computation: one-sided α=0.01, `z=2.326`, `SE=0.029` →
  power-0.8 MDE `=(2.326+0.842)·0.029 = 0.092` ✓ (H1); two-sided α=0.01, `z=2.576`, `SE=0.051` →
  `(2.576+0.842)·0.051 = 0.174` ✓ (H2). Self-consistent.
- **R2 null validity (§3,§5).** The βinv↔rand label-swap is exchangeable and centers `R2` at 1, so the
  two-sided `#{permuted |log R2| ≥ observed}` is a valid exact null for `R2≠1`. No κ-centered null is
  invoked anywhere; the v2 §5/§7 conflict is removed. Sound.
- **The "`Σ_t quo` curve-dependent" claim (§0,A2).** Discharged by a **run**, not an argument:
  `conservation_check.py` gave secp 28 / nonCM 16 / j1728 12 at p=43 (m=2,|V|=4) and 3 other cells, all
  curve-dependent and below `|V|^m·2^{m-1}`. Refutes the v2 conservation-equality premise.
- **κ removed as a `quo` benchmark.** This strictly REMOVES a claim (H2 is now unbenchmarked). Removing an
  overclaim cannot introduce a new overclaim; the moving-target fact (`S(ωx,ωt)=ω^w S(x,t)` ⇒ κ-images
  decompose `ωt≠t`) is elementary equivariance.

### Frame — self-audit NOT sufficient; relies on the prior EXTERNAL passes, and these are the OWED items
- **UNCHANGED from v2 and already externally cleared** (so covered, but by v1/v2 isolation, not by this
  self-audit): H1 matched-`#E` paired design (v2 B2 RESOLVED); consistent-regime discipline; F2 handling
  (CM-vs-nonCM, j0/j1728 separate levels); tautology guard; disjoint construction; scope banner +
  falsification cells; C2 `#E`-match adequacy; C4 `#E`-stratified control.
- **NEW in v3 and NOT discharged by this self-audit (explicitly owed for the re-run):**
  1. **Does the unbenchmarked H2 still have a purpose?** Removing the κ benchmark may have left H2 as an
     "does x-closure move `quo`" test whose value/interpretation a fresh isolated pass should confirm (or
     recommend dropping H2 entirely).
  2. **Over-correction check.** The suppression flag cut one way; the fix must not have swung the other —
     did removing the ceiling framing drop a *legitimate* bound? (A frame-isolation review is the right
     place to check I didn't over-open in reaction to the flag.)
  3. **Whether the moving-target argument has a case I can't see from inside the frame** (isolation is the
     mechanism precisely for the errors invisible from within).

**Consequence (condition 1 + 4):** any RESULT produced by running this spec now carries
`[PROVISIONAL — experiment-designer v3-delta gate owed]` in its grade slot, names items (1)–(3) above as
uncovered, and **cannot be promoted to a graded finding** until the re-run clears. A provisional run
produces evidence, not a grade.
