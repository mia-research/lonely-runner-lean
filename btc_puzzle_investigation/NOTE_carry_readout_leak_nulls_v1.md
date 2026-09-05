# NOTE — the public coordinate carry, tested as a d-readout: scoped nulls (logged so they aren't re-run)

**Grade: `[EMPIRICAL — scoped null, firing controls fire; small scale n=967]`.** Date 2026-08-17. Active
leak-hunt on the one carry that is PUBLIC (the coordinate carry `eps(X)`, unique to secp/j=0 per
`RESULT_cm_ring_universality_v1`). NOT closures — single/orbit-level probes; per doctrine per-point readouts
are Farey-generic. Reproduction: `scratchpad/eps_leak.py`, `carry_fourier.py`, `eps_pair.py`.

## Probes and results (curve y²=x³+11/F_1009, n=967; firing control fires each time, p≈0.001)
1. **`eps(x([d]G))` single readout vs `d`**: MI ≤ 0.013 vs `d mod {2,3,6,7}`, `jac(d,n)`, `hi2(d)`,
   `d∈[n/2,n)`; matched-perm **p = 0.27–1.0, none survive**. Null.
2. **`eps` as a hidden character** (DFT of the signed carry over `m∈ℤ/n`): **flat** — max power / mean = 7.68
   (firing control planted-character = 19.0), power spread across conjugate-pair frequencies, no single peak.
   So `f(m)=eps(x([m]G))` is not shift-extractable; the "observe `f(d+d₁)` for known `d₁`, correlate for `d`"
   lever does not fire (f is not a character, and is not cheaply computable — the correlation needs the full
   `f`, i.e. the DLP).
3. **Joint carry-pair `(eps(X), eps(βX))`** (the full per-orbit info; third value fixed by the P17
   conservation): 6 distinct values, MI ≤ 0.02 vs the same targets, **p = 0.39–0.98, none survive**. Null.

## Reading (honest, non-closing)
- The **A-class** (per-point / per-orbit PUBLIC observable → `d`) is now well-tested null on the carry, on top
  of the earlier null on the GLV label (N15) and the isotype readouts (M20). Consistent with doctrine: a
  per-point readout that recovered the key WOULD be a break, so its being Farey-generic is expected. This is a
  scoped null on the tested observables/targets, **not** a claim the avenue is dead.
- The carry is the observable **unique to secp** (j=0), so it was the most likely A-class candidate; its
  nullity says the secp-specific *geometric* carry does not, by itself, keyed-leak.

## Where a lever could still live (the map after this)
- **A-class (per-point public readout):** robustly null. Continuing to grind variants is unproductive.
- **B-class (joint property of the key SET):** the only ECDLP-surviving class per doctrine — but of the
  *generator's* set, which is the out-of-scope generation boundary. In-scope joint objects are curve
  conservations (which are d-homogeneous, don't leak).
- **C-class (computational break/avoidance):** interval-DLP speedup beyond negation's √2, or index calculus
  below the μ₆ constant-factor. The honest location of a real break; hard (no known subexponential prime-field
  ECDLP). λ-folding shown 2⁵⁸× worse (`RESULT_curve_island_lambda_folding`).
- **Additive channel (`ε_LBE`):** the one per-key object that CONTAINS `d` (not d-homogeneous), now with the
  cohomology `ε_add = π̄_n·ε_LBE`. But the carry-ceiling work-invariance (P19) shows the additive carry is
  work-invariant — no free lunch unless a *public* observable of it is found (none so far; N16 open).

**Net: the readout class is null; the live lever-space is the computational side and the additive/`ε_LBE`
channel. ECDLP assumed hard, not proven — the hunt continues; the readout vector is retired as scoped-null.**

## Addendum 2026-08-17 — REAL secp, 131-bit keys, checksum-validated carry tool
Methodology (user): the 6 exposed puzzle keys are the **checksum** (anti-answer-injection); the **test bed**
is self-generated keys with KNOWN `d` on the real curve. Built a real-secp256k1 tool (`scratchpad/hunt2.py`,
`eps_fix.py`): `π_p` via exact-integer Eisenstein lattice reduction (`N(π_p)=p`), coordinate carry
`c(X)=(ω·z(X)−z(βX))/π_p`.
- **Checksum caught a real bug:** first version used an arbitrary cube root; the carry needs `β = ω mod π_p
  = wr`. First version matched the ledger 2/6; **`β=wr` matches 5/6 exactly** (all five c=0 keys) and the 6th
  (#145) only by the conjugate sign `+ω` vs `−ω` (my `π_p` = the ledger's conjugate associate). Tool validated.
  The corrected carry shows the right **`{¾,⅛,⅛}`** law on real keys (1136/183/181 of 1500).
- **Leak hunt with the validated tool, 1500 known 131-bit real-secp keys:** GLV label `e`, sign `s`, carry
  `c(X)` (¾-law), lift-norm bucket — **0/24 survive** vs `d mod {2,3,6,7}`, hi-bits, bit-40; firing control
  fires (p=0.001). Checksum-clean per-point-readout NULL at the real scale and real key regime.
- **Exposed-key relations** (`scratchpad/relations.py`): no `P_i=[s]φ^k P_j` in the scanned windows (adjacent
  pairs fully covered, s∈16–64), no Aut₆ relation — confirms the exclusion ledger; the exposed keys are
  algebraically independent at this scope.
- **Tool is reusable** (validated) for any future real-secp per-point CM computation. This is a detailed
  fence feature (per-point readout Farey-generic at real scale), NOT a wall.
