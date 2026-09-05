# Next-session prompt — BTC/secp256k1 thread (handoff from 2026-07-30/31)

## Orientation (read first)
Resume the secp256k1 ECDLP-structure investigation in `~/Desktop/Math Ex/btc_puzzle_investigation`.
This is collaboration/investigation mode — lens-open, counter-prior in force, proof-not-test as the
close bar. Read `CLAUDE.md` (project intent), `COUNTERPRIOR_and_closure_grade_spec_v1.md` (closure
rules), and the two synthesis docs before acting:
- `STRUCTURAL_IMPLICATIONS_2026-07-30_v1.md` (the spine: the π-separation thesis, the queue, the
  confidence table — UPDATED 2026-07-31 with what the recent chases established/refuted)
- `NEW_INSIGHTS_REVIEW_2026-07-30_v1.md` (the findings review)

## Where the structural/mechanism side landed (2026-07-30/31, now measurement-complete)
- **Char-poly collapse** $e_2=e_1^2+p$ verified at scale; cap chain has ONE open link (uniform #26).
  See `RESULT_e2_identity_extended_verification_v1.md` + `verify_e2_identity_extended_v1.sage`.
- **Power-sum ladder (Route A, no closure assumed)** — the control an external critique correctly
  identified as missing. $e_2,e_3,e_4$ now MEASURED independently (not forced), both $\chi_2(-1)$
  branches, to ~1e-43. Closes the circularity gap. `RESULT_powersum_ladder_routeA_control_v1.md`.
- **Monodromy** — 1-point marginal is SU(2)-Sato-Tate at scale (p=100003, 49833 cells, 8 moments
  to 4-5 sig figs): `RESULT_monodromy_sato_tane_at_scale_v1.md`. 2-point level statistics already
  DONE and NULL by the record (`RESULT_semicircle_null` — spectrum is iid, not GUE-rigid). NOTE:
  the marginal identifies only the *connected-component trace behavior*; the full group is narrowed,
  not pinned.
- **Algebraic-number layer (NEW, a law)** — eigenvalue splitting field: minpoly degree $4(n-1)/3$,
  multiplicity EXACTLY 3 (the μ₃ signature) at p=43,67,127. Full tower:
  $\mathbb{Q} \subset \mathbb{Q}(\omega)[\deg2] \subset L[\deg20]$, the two deg-20 factors are
  $\omega\leftrightarrow\omega^2$ conjugates and EVEN in T. Galois group: non-abelian,
  $G \subseteq A_{40}$ (disc is a square), generic Frobenius cycle type $(10,10,10,10)$, all cycle
  lengths divide 10. `RESULT_algebraic_number_layer_v1.md`.
- **Commutative-CM-commutation mechanism REFUTED** at every level (non-abelian eigenvalue field,
  non-abelian splitting field). The SL₂-on-tensor-structure monodromy candidate is the SURVIVING
  mechanism: field-confirmed non-commutative, consistent with cycle data, right block shape
  (deg-4 outer × deg-10 inner). NOT proven (needs the exact group / a monodromy theorem).
- **The mechanism question is now measurement-complete.** What remains structural is a PROOF that
  the monodromy forces the 120° pairing uniformly (#26 as a monodromy theorem) — a proof, not a
  measurement.

## The cryptographic side (C-chase) — the next measurement thread, IN PROGRESS
The c-side non-algebraic index correlation (the CDH/inversion channel, the one wall Weil doesn't
close) was run for the first time: `RESULT_cside_nonalgebraic_correlation_v1.md`,
`cside_orbitlevel_v1.py`. Status:
- **Family-wise NULL** on the `inv` map: 18 large primes (orbits ~3600-4400), firing control
  clearing the gate at every prime, max|z|=2.39, NO cell survives Bonferroni.
- **BUT a flagged sub-detection lead**: small consistent NEGATIVE bias (T_inv<0 in 15/18 primes,
  pooled Stouffer z ~ -2.1 to -2.6) that SURVIVES a null-calibration control (pure-random data
  gives pooled z +1.02, so the tilt is real, not a null artifact). Sub-detection, not a finding,
  not nothing — an open thread per the counter-prior.

## What to do next (the agreed queue)
The structural side is measurement-complete; the next measurement thread is the C-chase. Two
concrete next steps on it:
1. **Settle the C pooled-tilt lead**: ~30-50 large primes with a calibrated (permutation) pooled
   p-value (NOT z-inflation — the calibration std was 0.79, so z's are mildly inflated) + an OOS
   retest of the most-negative cells. Cheap. Resolves whether the tilt is a real small effect
   (~T_inv ≈ -0.02, below the ~0.5 detection floor) or the tail of noise.
2. **The shortscalar arm at the 2^128 scale** (`PREREG_incomplete_shortscalar_v2`) is the
   operationally-decisive form of C — but it's the one BLOCKED by the experiment-designer gate
   (failed 3x). It can be run on constructed reference sets without the gate, but the real-82-keys
   verdict has a process gate — DO NOT bypass that silently.

Also still open (lower priority): non-archimedean (p-adic) Weil-number purity (item 2's true
residual — archimedean "every embedding" reduces to "all frequencies", which is done).

## Disciplines that paid off this session — keep them
- **Check the record before building** (twice avoided reimplementing done tests: the 2-point
  level statistics, and nearly the archimedean-purity-at-embeddings). Recon first.
- **The firing control must be GENUINELY INDEPENDENT** of the data's forced structure, and it must
  CLEAR THE GATE before any data result is trusted. (The first C-control echoed the data; the first
  2-point number-variance used rank-unfolding that destroyed the signal.)
- **Compute the relationship before building the test** (σ_k(L_a)=L_{ka} showed archimedean
  purity-at-embeddings is not independent; the GLV μ₃-orbit constancy of c set the C-chase power).
- **Honest scope on small p**: p=13/n=7 is a degenerate artifact for the algebraic-number layer
  (coeffs collapse to Q); generalize from p>=43 there.
- **A clean scoped null is a valid result** (C family-wise null); a surviving pooled tilt is to be
  CHASED, not buried (the counter-prior's point).

## Process note
The experiment-designer / citation-verifier gates have been chronically unavailable this project
(citation-verifier failed 4x; experiment-designer 3x). (D2) — the KS/Weil citation chain the cap
chain grade-promotion depends on — is still unverified; after 4 tool failures the move is to read
Ireland-Rosen Ch.14 / Berndt-Evans-Williams Ch.11 BY HAND, not via the verifier.

---

## UPDATE 2026-07-31 (session continuation) — C pooled-tilt lead SETTLED

Queue item C, step 1 ("settle the C pooled-tilt lead") is **done** — `RESULT_cside_pooled_tilt_settlement_v1.md` (+ `PREREG…v1.md` frozen pre-data, `cside_pooled_tilt_settlement_v1.py`).

**Verdict: the `inv` pooled tilt is CLOSED as a candidate** (calibrated permutation pooled $p=0.265$ on 36 primes, 14/30 negative; OOS K=2 hash-fold fails — one fold sign-flips). v1's $z=-2.64$ did not reproduce even in v1's own primes with the calibrated method (mean $z=+0.24$ in the $\le15919$ range) — confirming it was the **z-inflation correction** v1 itself flagged as wrong. The per-prime family-wise `inv` null stands.

**One open sub-lead surfaced and was NOT promoted:** `pow7` pooled $Z=-2.73$, $p_{2s}=0.006$, Holm-sig over the secondary family — but it **did not replicate OOS** (fold 0 $p=0.13$, fold 1 $p=0.0035$). Per the counter-prior it is a pooled-but-unreplicated sub-detection lead, same status v1's `inv` tilt held. Not buried, not promoted (P1–P3).

**C queue status now:**
- Orbit-level `inv` at $p\sim10^4$: settled (null). `pow7` at $p\sim10^4$: sub-detection, unreplicated.
- **The channel at $2^{128}$ is NOT closed** — the operationally-decisive form is still the gate-blocked shortscalar arm (`PREREG_incomplete_shortscalar_v2`).
- Next measurement on C (if the experiment-designer gate ever clears): shortscalar at $2^{128}$, OR a `pow7`-focused larger sweep if that sub-lead is worth chasing (lower priority — it failed OOS).

Discipline confirmed this session: PREREG-then-run held; `check_no_float.py` passes on the new script (v1's did not); the secondary hit went through the pre-committed symmetric OOS gate rather than being quietly dropped.
