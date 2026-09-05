# RESULT — Semaev CM Lever: Cost-Side, Mechanism, Extrapolation (PREREG v5)

**Date:** 2026-08-15
**Pre-registration:** `PREREG_semaev_cm_lever_capability_v5.md` (registered 2026-08-15, PRE-RUN)
**Instrument:** `semaev_elimination_v1.py` (frozen, byte-identical to v3/v4 runs)
**Run scripts:** `semaev_cm_lever_capability_v5.py` (Arms A, C), `semaev_mechanism_nt_v5.py` (Arm B),
  `semaev_symbolic_quasi_v5.py` (B-S1/B-S2, exact)
**Gate:** ⏳ ISOLATED DESIGN-GATE OWED (first agent died on usage limit pre-verdict; relaunch
  after the 17:30 reset, on the final post-smoke artifacts). Smoke tests PASSED pre-gate
  (instrument validation only — see §7 process notes).
**Schedule SHAs:** Arm A: *[PENDING — full run]* (expected f92cb4bb-identical: same primes/curve
  construction as v4); Arm B: *[PENDING — full run]* (smoke froze c19012ad on its own 2-prime
  schedule before smoke quos; the 12-prime full run freezes its own); Arm C: *[PENDING]*.
**Grade:** UNGRADED (pre-draft skeleton; symbolic arms final, measurement arms pending)

---

## §0 Scope Banner

- Arm A: the v4 24-prime schedule (p ≡ 1 mod 3, [523,823]), |V| ∈ {4,5,6}, K=15.
- Arm B: 12 primes p ≡ 1 mod 3, p ∈ [211, 367], |V| ∈ {4,5,6}, K=10, exact N_T per (curve,target).
- Arm C: |V|=9, K=10, first 16 primes; |V|=10, K=8, first 12 primes, conditional on C-stop
  (runs iff T1(9) − T1(8) ≥ 0.05).
- All measurements at small p. **Nothing transfers to secp's 2²⁵⁶. No secp break; no
  ECDLP/extraction/security claim.** The v4 power-law reading (ratio ≈ 0.35·|V|^{0.9}) is a
  model-scale statement; Arm C characterizes the bend, it does not license extrapolation.
- Signal path: exact int/GF(p)/numpy-int64-modular throughout; float only in log-ratio
  statistics ranked against permutation nulls and in the pre-committed model fits (dual
  weighting; raw-AICc-primary with `[LOW-BOOTSTRAP-SUPPORT]` flag rule — the v4 D4 lesson,
  fixed prospectively).

---

## §1 Controls

| Control | Status | Evidence |
|---|---|---|
| **C1 (firing plant)** | *[PENDING full runs]* | Smoke: quo=18, dim=0, made=3, sizeV=7 — fires in both Arm A and Arm B scripts. |
| **C2 (#E-match)** | *[PENDING]* | Smoke: median rel-gap 0.0287 < cap 0.0860. |
| **C3 (\|V\| equality)** | *[PENDING]* | Code-asserted. |
| **C4 (nonCM null)** | *[PENDING]* | — |
| **C5 (group-law)** | *[PENDING]* | — |
| **C6 (v4 consistency)** | *[PENDING]* | Smoke: j0 z=0.2, j1728 z=0.4 — PASS at n=3. |
| **C7 (N_T cross-validation)** | *[PENDING full]* | **Smoke: 3/3 EXACT MATCH** (axis0 vs axis2 recomputation, integer equality). |
| **C8 (d_solv sanity)** | *[PENDING]* | Smoke: d_solv ∈ {21,22,23}, 0 < d_solv ≤ Dmax. |
| **Schedule SHAs** | *[PENDING]* | Frozen before first quo per arm. |

---

## §2 Results

### §2.0 Symbolic arms — FINAL (deterministic, exact ℚ(ω); complete pre-draft)

**B-S1 — PROVED.** For A=0 and B an indeterminate, the instrument's own S₃ satisfies
$$S_3(\omega a, \omega b, \omega c) = \omega \cdot S_3(a,b,c), \qquad \omega^3 = 1,$$
verified identically zero in ℚ(ω)[B,a,b,c]. **Control:** the identity fails for symbolic A ≠ 0 —
the quasi-homogeneity is specific to the j=0 form (A=0).

**B-S2 — PROVED, k=0.** The m=3 summation polynomial (built by the instrument's exact
two-S₃ resultant route, B symbolic) is **μ₃-invariant**:
$$S_4(\omega x_1, \omega x_2, \omega x_3, \omega t) = S_4(x_1, x_2, x_3, t).$$
Mechanism: isobaric — every monomial of S₄ has z-degree + 3·(B-power) = 12 ≡ 0 (mod 3)
(consistent with MASTER Part VIII's "S₄ wt 12"). Equivalently via resultants:
Res(f_ω, g_ω) = Res(f, g) since both S₃ factors quasi-homogenize with weight 1.

**B-S2b — obstruction computed (fixed target).** S₄(ωx₁,ωx₂,ωx₃, t) is NOT proportional to
S₄(x₁,x₂,x₃,t): the difference has **114 monomials** (of S₄'s 191).

**Consequences (interpretive, exact-input):**
- The invariance ties (target t, base V) ↔ (ωt, ωV). At FIXED t there is no orbit symmetry —
  **H1's random-base advantage provably cannot be an orbit artifact** (closing the loop the v4
  RESULT left open at "not the closure mechanism").
- On β-invariant V (ωV = V), the three orbit targets t, ωt, ω²t have equal quo — the structural
  content behind H2's bounded x-closure effect (M26).
- *[SMOKE — n=2, instrument-validation only, NOT verdict data]:* T1_excess ≈ T1 for j0 at all
  three |V| levels and j0's N_T/#E² ≈ 0.93–0.95 vs nonCM ≈ 1.0015 — see §6 for the registered
  interpretation pending full Arm B.

### §2.1 Arm A — cost side *[PENDING]*

- A-H1 (paired d_solv, two-sided): *[PENDING — 24 primes × 3 |V| × 2 CM levels]*
- A-H2 (d_ff, d_gb): *[PENDING]*
- A-H3 (economics, Σquo/elapsed, one-sided): *[PENDING]*
- **M9 relation (prereg A6):** M9 (MASTER Part VIII) verified d_solv/d_ff curve-blind at
  p≤307, m≤4, |V|=3 on identical systems. Arm A extends to per-curve systems, |V|∈{4,5,6},
  p∈[523,823]. M9 predicts A1c (null). A1a/A1b firing contradicts a verified fact in the
  extended regime and is reported as such.
- C6 consistency table vs v4 T1: *[PENDING]*

### §2.2 Arm B — mechanism *[PENDING]*

- N_T diagnostics (N_T vs #E² by class): *[PENDING — 12 primes]*
- B-H1 (T1_excess, two-sided sign-flip per |V|): *[PENDING]*
- B-H2 routing (pre-committed): T1_excess ≈ T1 (CIs overlap, same sign) → **B1 distributional**;
  T1_excess ≈ 0 with T1 > 0 → **B2 count-driven** (#E-independence investigation owed).
- Character-sum reading (if B1): the CM decomposition surface's F_p-points concentrate on
  sampled tori beyond uniform density — anchored by B-S1/B-S2.

### §2.3 Arm C — extrapolation *[PENDING]*

- C-H1 (H1 at |V|=9): *[PENDING]*
- C-Scaling verdict (flat/linear/log/log2, dual weighting, raw-AICc-primary with bootstrap
  flag): *[PENDING]*
- C-stop evaluation (T1(9) − T1(8) vs 0.05) → |V|=10 arm runs or not: *[PENDING]*

---

## §3 §8 Verdict Routing *[PENDING]*

Pre-committed outcome table (prereg §3): A1a (cost lever, compounding) / A1b (cost anti-lever,
A-H3 arbitrates) / A1c (levers independent — M9 extension confirms) / A2 (economics) /
B1 (distributional) / B2 (count-driven) / C1 GROWS-LOG / C2 GROWS-CURVED (saturation onset —
the extrapolation boundary) / C3 INCONCLUSIVE / D (control failure → arm uninformative).

Routing: *[PENDING measurement arms]*

---

## §4 Interpretation *[DRAFT — conditional framing]*

- **If A1a** (CM lower d_solv): yield and algebra-cost levers compound; report the implied
  Macaulay-matrix size ratio at d_solv difference Δd (columns grow ~ C(D,3)-like in the
  truncation degree). This would ALSO be the first observed break of M9's curve-blindness —
  boundary conditions (per-curve systems vs identical systems; |V| regime) become the
  explanatory target.
- **If A1c** (null): the M9 curve-blindness extends to |V|∈{4,5,6}, p∈[523,823], per-curve
  systems. The yield lever is then confined to the relation-collection phase (quo), exactly as
  v4 characterized it.
- **If B1** (distributional): the mechanism is clustering of the j0 surface's F_p-points on
  sampled tori — a character-sum phenomenon consistent with (and now anchored by) the proved
  μ₃ structure. The j0 N_T/#E² < 1 deficit (if it holds at n=12) sharpens this: fewer total
  points, denser on tori.
- **If B2** (count-driven): the #E-independence reading of v4 is weakened; investigation owed.
- **If C2** (GROWS-CURVED): the bend location enters the ledger as the extrapolation boundary;
  report the fitted curvature scale against the torus-saturation ceiling |V| ~ p^{1/2}.
- **If C1** (GROWS-LOG): the power law extends to |V|=9(,10) without curvature; N12 stays open.

---

## §5 Power Summary *[PENDING]*

Prereg §7 floors: A-H1 detects median degree shift ≥1 on ≥70% of pairs (p<0.01); A-H3 detects
ratio ≥1.15×; B-H1 detects |T1_excess| ≥ 0.15 at power ≈0.7; C level-mean SE ≈ 0.14 at |V|=9
(directional increment test, pre-registered as such).

---

## §6 Unprojected Covariates *[PENDING; flagged from smoke]*

- j1728 sign contrast: negative at p∈{211,223} (Arm B range) vs positive at p∈[523,823] (v4
  range) — p-dependence of the j1728 lever to be characterized from Arm B's 12 primes.
- Per-level Var(T1) (logged in Arm C per the D5 fix — dual-weighting sensitivity computable).

---

## §7 Deviations & Process Notes

- **Process — gate timing:** the isolated design-gate agent died on a 5-hour usage limit
  before returning a verdict; relaunch owed after the 17:30 reset, BEFORE any full-run launch.
  Smoke tests were run pre-gate as instrument validation only (v4 precedent: smoke → D1
  decision documented in prereg). No confirmatory statistic has been computed from any
  measurement arm.
- **D1 (candidate, if it fires) — smoke schedule SHAs:** the Arm B smoke froze its own
  2-prime schedule SHA (c19012ad) before smoke quos; the full 12-prime run freezes a fresh
  SHA. Harmless (smoke is not verdict data); documented for the hash ledger.
- **Script note:** the Arm A smoke tag was corrected from extra=2/“V=6” to extra=3 before the
  full run (label only; C6 in smoke correctly compared at |V|=5).

---

## §8 Files

| File | Description |
|---|---|
| `PREREG_semaev_cm_lever_capability_v5.md` | Frozen pre-registration (A6/M9 included) |
| `semaev_symbolic_quasi_v5.py` + output | B-S1/B-S2 proofs (FINAL) |
| `semaev_cm_lever_capability_v5.py` / `.log` | Arm A / Arm C run script + output *[PENDING]* |
| `semaev_mechanism_nt_v5.py` / `.log` | Arm B run script + output *[PENDING]* |
| `_SCHEDULE_v5_A/B/C.json` + `.sha256` | Frozen schedules *[PENDING]* |

---

## §9 Summary for POSITIVE_FINDINGS_MASTER *[PENDING]*

The symbolic lemmas (B-S1, B-S2 k=0, B-S2b obstruction) are final and master-ready now
(candidates: Part VIII-bis extension anchoring N11; the fixed-t obstruction closes v4's
"not-the-closure-mechanism" argument exactly). Measurement-arm ledger updates wait for the
full runs + gate.
