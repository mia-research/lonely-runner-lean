# PLAN — R1 (prime-field Semaev CM relation-yield lever): finalize the strong positive run, decide lever-vs-constant

**Date 2026-08-07.** Situates and completes the R1 thread — the one lever candidate that plausibly clears
**both** walls a secp lever must clear. No ECDLP/extraction/security claim; model-scale.

---

## 1. Why R1 is the right target (the two walls)

A secp lever must be (i) **computable at 2²⁵⁶ without enumerating the group** and (ii) a **joint /
unscrambling** handle (single-index bounded-degree readouts are analytically closed — KS/Weil +
Boneh–Shparlinski). Almost everything in the record clears only one:
- The **deficit / spectral family** (this week) clears neither wall for a lever — it needs the whole group
  (a `p×p` FFT). It is pure-arithmetic curve study. *(Correction to my earlier "nothing transfers": that
  is true of the enumerable spectral statistics only. Exact algebraic facts — supersingularity,
  amicability, the sextic-twist class, the μ₆ automorphism structure — are scale-free and DO transfer;
  the record grades several `[holds at secp]`. R1's mechanism is in that scale-free class.)*
- **R1 (prime-field Semaev index calculus)** is literally an **unscrambling** attack (decompose a target
  into factor-base points = solve the DLP), and its candidate mechanism — the μ₆ **automorphism
  structure** raising the relation yield — is an **exact algebraic property that is scale-free**. So R1 is
  the one direction where a positive result could clear the scale wall by a *mechanism* argument, not a
  measurement at 2²⁵⁶.

## 2. Current state (gate-cleared, run executed, NOT finalized)

- `PREREG_semaev_cm_relation_yield_v3.md` — **`experiment-designer` gate CLEARED 2026-08-07**
  (`..._GATE_OWED_selfaudit.md`: "cleared to run, no blocking findings"). Gradeable.
- Schedule frozen + SHA'd (`_SCHEDULE_..._v3.sha256` = f92cb4bb…), 24 primes `p≡1 mod 3` in [523, ~8000],
  `j0`(μ₆) / `j1728`(μ₄) / ≥5 non-CM per prime, matched-`#E` pairs, `K=25` targets, `|V|∈{4,5}`, `m=3`.
- Instrument built (`semaev_cm_relation_yield_v3.py`); run executed (`..._v3.log`).
- **Run output (ungraded):** H1 `T1_j0`=0.207 (p<1e-4, 21/24, above the 0.092 floor); `T1_j1728`=0.135
  (p=0.004); H2 `R2`≈1.9 (p<1e-4); **C4 #E-leakage control NULL (p=0.30)**; C1 fires; C2 gap 0.013 ≪ cap.
- **Missing:** the **Scaling** verdict (T1 growth over `|V|` and `m` — the lever-decider), the `m=4` arm,
  `results.jsonl`, and the graded `RESULT` with the §8 outcome. No instrument-vs-spec verification yet.

**Reading (held pre-grade):** a real, novel, `#E`-controlled CM relation-yield effect is present and the
control that would expose a group-order artifact (C4) is silent. This is the strongest lever signal in the
record. It is **not yet graded** and is **not** a lever until Scaling is in and the finalization gate runs.

## 3. The one question that decides lever-vs-constant

`T1` measures a single-target `quo` (relation-yield) increase on a **random** base — so it is **not** the
known automorphism factor-base-SIZE speedup (bounded `≤κ=3`, which lives in target orbits, per prereg A2).
The decision:
- **Scaling FLAT** (`T1` const over `|V|,m`) → outcome **A2**: a bounded CM relation-yield constant. Real,
  novel, but constant factors do not move the subexponential asymptotics. Not a lever.
- **Scaling GROWS** (`T1` rises ≥0.10/step) → outcome **A1**: **candidate lever** — a CM relation-yield
  advantage that grows with system size, whose mechanism (μ₆ automorphism structure) is **scale-free ⇒
  transfers**. Next probe: does the growing yield actually lower relation-collection COST at larger `m`.

## 4. Completion steps (this is the plan)

1. **Verify instrument vs frozen spec** (trust-but-verify). Read `semaev_cm_relation_yield_v3.py`; confirm
   it implements §3/§4: matched-`#E` nearest-pairing, **within-pair** label-swap null (not a global
   permutation), C4 `#E`-stratified non-CM(high)/non-CM(low), the `|V|` sweep, `κ` read from `(A,B)` not
   `quo`, exact GF(p)/no-float. Re-run `check_no_float.sh` on the statistic module. If the instrument
   diverges from the spec, that is a defect to fix before any grade.
2. **Extract Scaling** from the existing run (it has `|V|=4` and `|V|=5` blocks): compute the `T1_j0`
   slope over `|V|`, sign test; add the `m=4` arm where `S₅` resolves `quo` in the time box (else log
   `unresolved`, drop — not data). This is the lever-decider (§3).
3. **Finalize** → `results.jsonl` (full per-cell `quo` vectors), and the graded `RESULT_semaev_cm_relation_
   yield_v3.md` per the §8 table: A1 (grows) / A2 (flat) / A3 (Scaling underpowered) for H1; plus the H2
   `R2≈1.9` finding (A4 X-closure — x-closing the base ≈doubles single-target `quo`, contradicting the
   moving-target `R2≈1` prediction — a second novel mechanism, report as its own signed magnitude).
4. **Grade gate.** Per project rule, a promoted RESULT that moves the lever question goes through the
   finalization checks: `compile-diff` if it supersedes/re-scopes a predecessor (it re-scopes
   `RESULT_semaev_cm_lever_v1`), and the grade stays `[EMPIRICAL — model-scale]` with the §0 scope banner.
   **No ECDLP/security claim** regardless of A1/A2.
5. **Transfer analysis (the user's point, done right).** If A1: state the scale-free mechanism explicitly
   (μ₆ gives `κ=3` x-images; the yield effect is automorphism-structural, not `p`-specific) and name the
   secp-scale consequence as a **mechanism inference**, not a measurement — with the honest caveat that a
   yield/relation-collection advantage is a factor in cost, not an asymptotic break, until the cost probe
   (step 3 "next probe") runs.

## 5. What R1 does NOT use, and the parallel track

- **The 36k keys are not R1's object.** R1 is about the *algorithm's* decomposition structure (CM vs
  non-CM), tested on synthetic decomposable targets. The 36k keys (and freely-constructed keys) feed the
  **other** live direction — the scale-surviving **joint-lift set reading** (scalar-lift `κ=k₁+k₂ω` vs
  coordinate-lift, a set-level statistic computable at 2²⁵⁶). Run that in parallel, not inside R1.
- **After R1, regardless of outcome:** if A1, the cost probe (does growing yield lower relation-collection
  cost, larger `m`); if A2/A4, the x-closure mechanism (H2) is itself a novel unbenchmarked effect worth
  its own characterization. Neither outcome closes R1 — both name the next object.

## 6. Discipline held on this thread
- H1's positive is **surfaced and to be finalized, not deflated** (the suppression bias would explain away
  a p<1e-4, C4-clean, 21/24 effect — it must not).
- Equally, it is **not graded a lever** until Scaling is in, the instrument is verified, and the gate runs
  — a novel constant (A2) is a real result but not a lever, and the automorphism factor is an explicitly
  bounded `κ≤3` unless Scaling shows growth.
- Every number stays model-scale under the §0 banner; transfer is a *mechanism* argument, flagged as such.
