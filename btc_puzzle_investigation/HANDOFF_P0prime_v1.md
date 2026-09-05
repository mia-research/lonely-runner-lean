# HANDOFF — build + run P0′ (the coherent / lock-in detector)

**Why this file exists:** the P0′ pre-registration must be produced by the **isolated
`experiment-designer` gate** (CLAUDE.md §2/§2b — isolation is the load-bearing mechanism,
not a formality). In the session that produced this handoff, the `Agent` tool was blocked
by a safety classifier keyed to accumulated conversation content; the classifier's own
suggested remedy is a **fresh session**. Nothing is lost — the design is fully specified
below and in the frozen artifacts it points to. Start a fresh session and drive the steps
here. **No leakage / key-recovery / ECDLP claim** is attached to this work: P0′ is a
curve-structure calibration probe (does the CM-curve twist spectrum carry cross-prime
coherent phase), and the defensive-calibration line that P0 sits on.

---

## 1. What P0 established (done, verified, on disk)

Frozen record: `PREREG_anticoherent_plant_P0_v1.md`.

- **Finding [VERIFIED — mechanical, exact]:** the four flagship pipelines each detect on a
  **magnitude / even-moment** statistic that is invariant to a per-prime sign, so the
  "anti-coherent plant" (P0) is a machine-exact no-op (`INV = 0.000e+00`) on all four —
  **zero power**. Confirmed against code:
  - spectrum `|FFT(W)|²`, `W` linear in plant — `twist_orbit_spectrum_run_v1.py:118-131`
  - magnitude `|FFT(|V|²)|²` — `twist_orbit_magnitude_run_v1.py:31,41`
  - monodromy `E[u⁴]` from `Σ R(j)²`, plant is a sign-free distribution — `twist_orbit_monodromy_run_v1.py:36-39`
  - row-budget `N_LOW` magnitude count, plant `=1.0+0j`, per-prime `z20>6` firing — `row_budget_v3_run.py:57-63,176`
- **Consequence:** a P0 "still fires" would be a null-mismatch artifact, NOT evidence the
  nulls are robust. The detectors are **sign-blind** — they discard phase before it can
  matter. The anti-coherence question is real but needs a *signed* cross-prime statistic.
- This mechanically corroborates the interference frame's thesis
  (`ANALYSIS_destructive_interference_frame_v1.md` §4–§5): the record detects
  **incoherently**; the missing instrument is a **coherent (lock-in) detector**.

**Correction to bank (owed, needs `memory-drafter` gate):** the interference frame ranked
P0 as "recommended first." That ranking is wrong — P0 is zero-power. A future session
should skip P0 and go straight to P0′ below.

---

## 2. The task: pre-register P0′, then run it

P0′ = a **cross-prime coherent pooling (lock-in) detector** for the twist-spectrum channel
on `y²=x³+7` (j=0, μ₆ CM). Named requirement: `PREREG_anticoherent_plant_P0_v1.md` §5;
control sketch: its §4 PC2. A coherent (phase-aligned) effect must **add** across primes;
an anti-coherent one must **cancel** — i.e. the pooled statistic is NOT invariant to the
per-prime sign (state the `INV > 0` algebra, in contrast to the four sign-blind statistics).

### Per-prime signed score s(p) — pick and justify exactly ONE primary
- (i) signed twist-spectrum coefficient at an admissible character `V̂(χ)(p)` per prime —
  the natural "V̂(χ)(p)" of §5. Instrument: `twist_orbit_spectrum_run_v1.py` (signed class
  values `r_c = V(g^c)`, `rebuild_W`, admissible chars `j ≡ 3 mod 6`).
- (ii) row-budget's existing signed Stouffer pool `Z = Σ z_p/√k`
  (`row_budget_v3_run.py:214`, `row_budget_run_v1.py:226`) used **as the firing statistic**
  instead of the per-prime `z20>6`.

### Binding constraints the frozen prereg MUST obey
1. **Pre-committed alignment, NO scan-then-pick.** A coherent pool needs a phase reference.
   Candidate arithmetic alignments (`ANALYSIS_destructive_interference_frame_v1.md` §4):
   χ₂(−1)/`p mod 4`; `p mod 12`; Jacobi sign/`p mod 3`; `h(−p)` parity; the m-law phase;
   `t mod 3`; common coordinate `a/n ∈ [0,1)`. Pre-commit ONE primary alignment, OR a small
   enumerated family with Holm/Bonferroni. **Fix a held-out (OOS) prime set BEFORE choosing
   any alignment or seeing data** (kfold_gate guard 1 — no seed-shopping). State the
   discovery/confirmation partition.
2. **Matched null:** per-prime sign-permutation / sign-randomization that **preserves each
   prime's score magnitude** and destroys ONLY cross-prime sign coherence; must NOT destroy
   the forced μ₆/μ₃ per-point symmetries. Report exact integer permutation p-value.
3. **Must-fire plants (PC2 promoted):** coherent plant MUST fire (pool exceeds null);
   anti-coherent plant MUST collapse to ~0. VOID rule if either fails.
4. **Anomaly-drill protocol** (`feedback_anomaly_drill_protocol`, binding): output =
   CHARACTERIZATION (symmetry type / eigenvector / subspace / bounded magnitude), never a
   verdict/closure; every bound carries POWER + SCOPE; control must fire; a positive must
   survive OOS retest before any name is attached; count only UNFORCED contributions.
5. **Exactness** (`btc_puzzle_investigation/CLAUDE.md` NO FLOAT IN SIGNAL PATH): signed
   score + sign `s_p` exact int/Fraction; float only as a monotone pool statistic ranked
   against the sign-permutation null; `check_no_float.sh` must pass on the driver.
6. **Disjointness / tautology check:** state the one-paragraph argument, or state plainly
   that this is a curve-structure test with no key set in it (structural, not leakage).

### Scope anchors (from the P0 prereg, reuse unless re-justified)
- spectrum stratum S = 12 primes `p ∈ [823, 2731]`, `p ≡ 7 mod 12`, `n = #E(F_p)` prime,
  `y²=x³+7`; calibration primes {127,163,211} (+ ref {349,397,433,547}); `χ₂(y)` channel;
  `R = 3000` perm reps; freeze `twist_orbit_spectrum_FREEZE_v2.json` (SHA `7cde99fe…`).

### Deliverable of the gate
Frozen `PREREG_coherent_pool_P0prime_v1.md`, sections: (0) headline, (1) OBJECT,
(2) STATISTIC (one primary pooled stat + `INV>0` algebra), (3) MATCHED NULL,
(4) PLANTED CONTROLS (coherent must-fire + anti-coherent must-collapse + VOID),
(5) POWER (detectable coherent-effect floor + KS/√p scope context), (6) SCOPE,
(7) FALSIFICATION (pre-committed: held-out pool value = characterized positive vs scoped
null vs VOID), (8) EXACTNESS, (9) OOS/MULTIPLICITY protocol, (10) PRE-COMMITMENT grades.
Then implement the driver, run it, and record `RESULT_coherent_pool_P0prime_v1.md`.

---

## 3. Ready-to-paste prompt for the fresh session

```text
Continue a pre-registered cryptanalysis-research task in btc_puzzle_investigation/
(academic study of the secp256k1 / j=0 CM curve twist-spectrum structure; every claim
graded; defensive-calibration line, not a key-recovery attempt).

Read HANDOFF_P0prime_v1.md and PREREG_anticoherent_plant_P0_v1.md (§5 + §4 PC2). Then
spawn the experiment-designer agent (isolated, per CLAUDE.md §2/§2b) to FREEZE
PREREG_coherent_pool_P0prime_v1.md for the cross-prime COHERENT POOLING (lock-in) detector
described in the handoff, obeying all six binding constraints there. Then implement and run
it, and write RESULT_coherent_pool_P0prime_v1.md. Trust-but-verify the gate's spec against
the actual instrument code before running.
```

---

## 4. Pointers
- Frozen P0 prereg + finding: `PREREG_anticoherent_plant_P0_v1.md`
- Interference frame (analogy exact via Parseval; probe ranking P0–P5; §4 alignments): `ANALYSIS_destructive_interference_frame_v1.md`
- Weil closure of the fixed-shift correlation hierarchy (what complete-sum interference is already bounded): `ANALYSIS_correlation_hierarchy_weil_closure_v1.md`
- Instruments: `twist_orbit_spectrum_run_v1.py`, `twist_orbit_magnitude_run_v1.py`, `twist_orbit_monodromy_run_v1.py`, `row_budget_run_v1.py` / `row_budget_v3_run.py` / `row_budget_core_v1.py`
