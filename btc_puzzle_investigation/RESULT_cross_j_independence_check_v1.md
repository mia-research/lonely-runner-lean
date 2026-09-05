# RESULT: cross-j j-independence — instrument READY, measurement GATE-BLOCKED (arm runner unwritten)

**Date:** 2026-08-01
**Item C.2** of the 2026-08-01 plan. Follows `NOTE_cross_j_relevance_v1.md` (C.1: cross-j is NOT retired; it discriminates the Aut-routed mechanism, still live, and measures j-independence orthogonally).
**Register:** purist.

---

## 0. The state, honestly

C.1 established that the cross-j contrast is **not** vacated by existing data (secp256k1 is $j=0$ = positive $\mu_3$-Aut arm; the $j=1728$ arm is the discriminating negative arm) and should be pursued as both a mechanism discriminator and an orthogonal j-independence measurement. C.2 attempted the measurement.

**The measurement cannot run.** `jclass_120deg_discriminator_v1.py` has two modes:
- `--check` — instrument validation only (order check, plant controls, reproduction of published $j=0$ numbers). **Runs no arm, touches no new curve class.** Pre-gate legal.
- `--arms` — the actual cross-j measurement. **GATED**: refuses without `--i-have-the-gate` (the experiment-designer gate, failed 3×), and even with the flag the arm runner **is not written** (`"arm runner not yet written -- v2 spec must fix the prime class first (D1)."`).

Per the standing order ("do NOT bypass the gate silently"), this is where C.2 stops.

## 1. What `--check` confirms (the instrument is READY)

Running `--check` validates the machinery any future arm would use:
- **C-ORDER:** `root_of_order` exact for $k\in\{3,4,6,12\}$ over 5 primes — PASS.
- **C-PLANT** (over $\mathbb{F}_{73}$): all planted quartics fire correctly — PLANT-3/4/6 read $g_k=0$ off-lock and $g=2$ on-lock; lock-free controls (orders $\le12$) verified; PLANT-N3/N4/N6 read 0. ALL FIRE.
- **C-REPRO:** the generalized pipeline reproduces the published $j=0$ census cell-for-cell at $p=43,67,79,127$ — MATCH on all four.

**OVERALL: READY.** The instrument is correct and reproduces the published numbers. The blocker is the gate + the missing arm runner, not the instrument.

## 2. What is needed to run the measurement (deferred)

- **The experiment-designer gate** (failed 3×) must return, OR the gate-stance decision must be made explicitly (v2 §B revival fixes: drop prime-order requirement, MEASURE $b_1$ from $\#C(\mathbb{F}_p)$ at $p\equiv1\bmod4$, order F-EMPTY first).
- **The arm runner** must be written. v2 §B specifies the construction ($j=1728$ curves with cofactor $h\le8$ at 11/12 primes; $\chi_2(-A)=-1$ selects the cyclic $\mathbb{Z}/2n'$ branch; $j=0$ never has cofactor 2 so the arms run at both cofactors as the internal control).
- **v2 standing repairs** must apply (C-NEG $n\ge20$; readout-parity $\times$ index-set-parity check; precompute pool table; no `tail` pipe; OOS before naming).

## 3. Interpretation held open

C.1's framing stands: a $j=1728$ reproduction of the $120°$ lock would extend the $SU(2)$-trace monodromy claim's empirical base across $j$ and refute any Aut-routed mechanism contribution; a failure would localize the lock to $j=0$ and reopen the Aut-routed mechanism. Either is a contribution; neither is predicted by the current record. Consistent with item B (arithmetic Galois object is branch-dependent; whether the geometric monodromy is j-dependent is the separate open question).

## 4. Files

- `jclass_120deg_discriminator_v1.py --check` — instrument validation (READY); `--arms` gated + unwritten.
- This note records the gate-boundary stop; no new curve class was touched, no arm run.
