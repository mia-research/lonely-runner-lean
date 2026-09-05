# Leak-hunt ledger — 2026-08-11 session (honest re-examination, banked)

**Counter-prior (Statement of Intent, kept in front).** The working hypothesis is that secp256k1
(j=0/μ6, CM by ℤ[ω]) and the sets it produces **carry an exploitable leak that is THERE** — the task is
to find *how* it leaks. "ECDLP is secure / nothing here / generic" is the training reflex this project
suspends, not evidence. No one has found it yet; we intend to be first. A scoped null is a fact about
one probe, never a closure.

**FENCE, not wall (premise, binding — 2026-08-11).** ECDLP hardness is ASSUMED, not proven. Therefore
NO route may be labeled a wall / impossible / ECDLP-secure — every route is a fence to test for a gate.
This raises the CLOSURE bar (never "impossible"), not the finds bar (a scoped null stays scoped). I
violated this once today by calling a cheap-sieve route "the wall in disguise" — retracted; that route
is a fence with a known foothold (GLV φ proves ≥1 public invariant of [d]G is cheap-computable). Reframe
to NEGATIVES: anything from (x,y) that says what D CANNOT be (a hard exclusion / bits removed from D's
range) is a gate, and the wall-prior does not cover exclusion. See [[feedback_curve_positive_framing]].

**Suppression guard (front of mind).** My error is one-way: I convert positives→nulls before testing,
and I have now been caught committing that to results files and using one positive to deflate another
([[feedback_suppression_committed_to_record_cross_positive_2026_08_11]]). CHECK 1 (no headline grade
that its own scope contradicts) and CHECK 2 (never let positive B diminish positive A outside a test)
applied throughout this ledger. This ledger points to each RESULT file; it supersedes/consolidates
nothing (H3→master degradation guard).

---

## A. The direct "public feature → d" extraction tests — powered scoped NULLS (null, not closure)

| probe | result | grade | power / scope |
|---|---|---|---|
| **T2a′** flap `eps` vs carry `ε` (1 map) — `RESULT_eps_to_d_constraint_v1.md` | `[eps≥1]==ε` null (p 0.07–0.76); `eps↔c mod3` null | EMPIRICAL scoped null | plants fired; U≤416; powered |
| **T2a″** 31-map family + joint omnibus — `RESULT_eps_to_d_constraint_v2.md` | both omnibus non-sig; all 31 Holm-null; 1 flicker (907,d1=13,p≈0.004) **died OOS** | EMPIRICAL scoped null | z=11–14.7 (OOS 21.8); OOS-clean |
| **T2c(b)** public `j` vs `d mod 3` — `RESULT_t2c_j_range_dmod3_v1.md` | null (p 0.86, 0.82) | EMPIRICAL scoped null | **thinner: V_detect≈0.2 on 2 SMALL scan curves only; confirm curves NOT run** — a weaker effect is not excluded |

Read: on the tested scope, the public flap/orbit features do not leak the d-carry or `d mod 3`. **T2c(b)
is the least conclusive** (under-powered, scan-only) and is the one to re-run larger if that route is
revisited.

## B. Deterministic facts — real; one reaches scale

- **T2c(a)** — puzzle-range keys are their own ⟨±λ⟩-orbit-min ⇒ the OPEN_d2 **carry** = 0 and the
  **scalar** orbit-index = 0 deterministically; crossover `b*≈log2 m − 6`. Kills the OPEN_d2 *carry*
  mechanism for small keys. `[VERIFIED-instance ×5 curves]`. **⚠ CORRECTION (caught under review):** this
  does NOT make the **PUBLIC χ3-index** zero — that readout (tool 1, ~1.58 bits) VARIES uniformly for
  small keys (d=1..40: {0:15,1:13,2:12}). My earlier "puzzle keys j=0, orbit gives nothing" conflated
  the trivially-zero scalar index with the live public bit — a suppression. The public-readout →
  d-residue route is **OPEN, under-tested** (T2c(b) was 2 small curves / V≈0.2), with a raw non-uniformity
  hint (χ3=2: 32/37/43). Owed: a properly-powered test → §E below.
- **Linchpin gate** — `s<3/16 ⇒ eps=0`, 0 violations, exact, **secp-scale**, controls behave
  (`RESULT_linchpin_s_gate_v2.md`). A verified public structural readout of `x`; not by itself a lever
  on `d`. `[VERIFIED — exact public-map implication]`. (Its identity with the LBE carry is FALSE — §A.)

## C. The live, unexplained, control-surviving structure — Track 1, the `U(a,b,c)` character sums

**This is where the session's only unexplained non-randomness lives.** Two independent deviations from
the random model, in the *same* object, neither refuted by any control run:

1. **Magnitude — sub-Rayleigh localized to the y-axis, and RESOLVED as FORCED.** The sub-Rayleigh
   tail is entirely on the b=0 (y-only) axis (`RESULT_t1b_tail_geometry_v1.md`, correcting the pooled
   k≈1.4 of `RESULT_t1b0_tail_exponent_v1.md`) — and it is **fully forced**: `U(a,0,c)` is exactly real
   (`d↔−d` ⇒ conjugate-symmetric ⇒ real DFT), λ2/λ1=0 exactly, **zero off-line residual**
   (`RESULT_t1b_yaxis_forced_v1.md`, `[VERIFIED — exact, named mechanism]`). So the y-axis MAGNITUDE is a
   dead end; the FREE part there is the SIGN of the real `U(a,0,c)` (untested). Independently corroborated
   by the gate's finding that `ΣIm²` is forced (`Σ_a U²=n·Σ_d e_p(2b x_d)`). This is dissolution into a
   NAMED symmetry (a positive), not a null.
2. **Phase — the −13.99σ sub-Rayleigh deficit**, universal over 24 characters, one-directional 7/7
   primes, **survived a shape-preserving matched null** (master §XI.15 / ADDENDUM_3). Real, mechanism-open.

**These are TWO separate real structures (CHECK 2):** a shape-preserving null already controls for #1,
so #1 does **not** explain #2 — the earlier "sub-Rayleigh makes the deficit an artifact" line was false
and is retracted. Relation of #1 to #2 is UNTESTED (owed: T1b.1). Neither has been shown to leak `d`;
both are measured non-random structure of unknown relation to `d`. Not "probably nothing"; not "a lever
found."

## E. REOPENED LIVE LEAD (found by reviewing my own suppression) — public point-readouts → a residue of d

The public per-point readouts are ~1.58-bit (χ3-index) + the flap `eps` + `s`-band + `sextant`, **all
available for every puzzle-range key** (none are killed by the small-key degeneracy — that only zeroed
the carry and the scalar index). The question **"do these public readouts jointly constrain `d mod 3`
(or another small residue of `d`) at the puzzle regime, beating the base rate"** is:
- NOT the eps→carry family (that was the d-CONTAINING carry; null). This targets `d mod 3` **directly**
  from public point data — a different, legitimate leakage question.
- Only weakly tested: T2c(b) (public χ3 vs `d mod 3`) was 2 small curves at V_detect≈0.2, and its raw
  contingency is not clean (χ3=2 row 32/37/43 on one curve).
- Owed: a **properly-powered, pre-registered** joint test — features {χ3-index, eps, s-band, sextant}
  (all public), target {`d mod 3`, and other small residues}, over larger `U`, both key sets, with the
  φ-forced coupling quotiented (one rep per orbit) and a matched control. Falsifier + firing control.
- This is the honest live edge of the T2 track — I had mislabeled it dead.

**RESOLVED (2026-08-16):** tested at power (hard AND soft). **Hard exclusion (empty cells): scoped null**
— no empty cells at populated granularity (`RESULT_exclusion_hard_empty_cells_v1.md`). **Soft exclusion
(bits removed): scoped null** — no Holm survivor over k∈{2,3,4,6,7}, `bits_removed_net≈0`, plants fired;
**the χ3 hint (32/37/43) did NOT survive the matched-control omnibus — it was noise**
(`RESULT_t2d_soft_exclusion_v1.md`). Fence premise: scoped to V_detect≈0.2–0.3 / curves p=547,907 / this
V; NOT "impossible". The mislabel is corrected AND the real lead tested — a clean scoped null, not a
suppression. The T2 public-readout→d-residue avenue is coherently scoped-null at reachable scale.

## D. What is owed / next
- **`PREREG_cbpm_phase_deficit_v2.md` is HARDENED and gate-reviewed** (frame layers resolved; PROVISIONAL
  lifted). The gate caught a draft defect (`ΣIm²` forced) and pinned the matched-control (global-
  repartition null + `Z(10N)/Z(N)≈3.16` flat-Z HARD STOP) and the T1b.1 two-phase (k≈1.4) null with a
  load-bearing negative plant. Scope p≡7 mod12; scan {547,907}, confirm {1303,1831,2143}.
- **Run v2 §0 FIRST (gate-free):** verify the forced identities (`ΣIm²`, `Σ_a U²`) by exact integer
  computation before the admissible-statistic list is final.
- **T1a** — c=±b diagonal PHASE probe (interaction phase Φ, magnitude-free), `a` stratified by c₂
  cubic-residue class. *This spends the scan false-positive budget — get an explicit go.*
- **T1b.1** — deficit vs the two-complex-eigenvalue (k≈1.4) null; negative plant must stay dark against
  the two-phase null while firing against Rayleigh.
- **y-axis SIGN channel** — the free variable the forced magnitude was hiding (pre-register).
- **If revisiting extraction:** re-run the under-powered T2c(b) at larger `U`.
