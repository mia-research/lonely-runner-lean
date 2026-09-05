# DEVIATIONS — PREREG_cm_jointset_excess_v3.md (A-joint)

Post-freeze notes, disclosed per the prereg's freeze protocol.

---

## Second-read gate: DISCHARGED (2026-08-22) — v3 RUNNABLE AS FROZEN

An independent `experiment-designer` second read audited the v3 deltas against the frozen runner
(verifying in code, CM arm q=541, N=5000). **All 5 items PASS; verdict: runnable as frozen.**
- **Omnibus estimable + genuine guard:** the coarsened `Î(L_sum;J|Φ^pt)` 3×3|27 table has **243/243
  cells occupied, 0 with count ≤1** (mean 20.6/cell) at N=5000 — vs v2's object which fragmented to
  ~1/cell (the identically-0 statistic). It is a DISTINCT channel: `Ψ==L_sum` on only 33.9% of sets;
  `L_sum` varies in 27/27 strata.
- **PC-COMBO fires + non-degenerate:** p=0.0001 monotone (mi 0.031→0.062→0.167→0.536), distinct_lsum=3,
  ~3 draws/plant. The naive `d₃=−(d₁+d₂)` collapse was independently confirmed exactly (L_sum constant
  in 27/27 strata, `L_sum==(φ₁+φ₂+φ₃)` on 3000/3000); PC-COMBO's independent `P₃` avoids it.
- **No regression:** v3 reproduces the v2 discovery + controls logs byte-for-byte (only the printed SHA
  differs); the primary is computed before the omnibus and the omnibus path consumes no extra RNG, so it
  provably cannot perturb the primary. `check_no_float.sh` exits 0. Anomalous exclusion intact
  (non-CM traces −29/31/−35, none = 1).
- **Scope/falsification:** §9 rows reference the additive-combo channel actually tested; no
  ECDLP/extraction claim; no dismissal vocabulary.

The Owed-gate "second independent experiment-designer read of THIS v3" is **DISCHARGED**.

## Disclosure 1 (fixed) — stale "v2" labels in the runner
The run header (`tier()`) printed `== A-joint v2 ==` and the docstring usage lines named
`cm_jointset_excess_v2.py`. The verdict output always printed the correct v3 prereg SHA (`3560eb73…`),
so provenance was intact. **Fixed:** header → "A-joint v3", docstring usage → `cm_jointset_excess_v3.py`.

## Disclosure 2 (noted) — freeze-protocol partially manual
The prereg's freeze protocol says the runner "prints this file's SHA-256 into the RESULT and opens the
DEVIATIONS file." The SHA is printed in `tier()` (the verdict path) but not in `controls()`; the
DEVIATIONS file (this file) is created manually. Non-blocking for the statistic; recorded so no deviation
is silently unlogged. Any future run that banks a deviation must append it here.

## Disclosure 3 (benign) — PC-COMBO p quoted at smoke vs full R
The prereg §4/change-log quotes PC-COMBO "p=0.0020 at ρ≥0.3" (an R=500 smoke, floor 1/501); at the
frozen R=10⁴ it is p=0.0001. Both satisfy the pre-committed p<0.01; the statistic is unchanged.

## Design note (from the second-read, not a defect)
A PC-COMBO failure VOIDs the whole arm including the PC-SEM-certified primary — conservative co-primary
coupling, internally consistent with §9's "Î_prim AND Î_omni within null" scoped-null row. Kept as
designed.

---

## D-LADDER (2026-08-22) — ladder non-CM matching uses a bounded random search

**Change.** For the **ladder tier only**, the §6 non-CM matching rule "minimizing `|N_non−N_CM|` over a
deterministic enumeration of `(A,B)`" is replaced by `select_jgen_random(q, target_N, budget=1500,
seed=q)` — a bounded random search over `(A,B)` keeping the best ordinary `j∉{0,1728}`, `|t²−4q|≥⌊√q⌋`,
`t≠1` curve, early-exiting on an exact order match. Discovery and confirmation tiers are UNCHANGED
(enumerative `select_jgen`), so those frozen results are untouched.

**Reason.** Enumerative `select_jgen` is `O(q²)` and does not early-exit without an exact match; at
`q ∈ {16417, 65539}` it exceeds 30s (intractable). The random search reuses one QR sieve across draws.

**Impact — negligible on arm quality.** Verified: the random matcher finds an **EXACT order match**
(`|N_non − N_CM| = 0`) at all four ladder primes {1033, 4111, 16417, 65539} (traces −53/109/−29/253, all
non-anomalous), in 0.0–4.1s. So the arm's order matches target exactly, identical in quality to the
enumerative match; only the specific `(A,B)` realizing that order differs. Deterministic (`seed=q`).
Statistic/null/power unchanged. Infra self-test still passes; `check_no_float.sh` exits 0.

## Result so far (discovery tier, R=10⁴) — logged for provenance
CM arm, all three channels within the within-stratum null at all 3 discovery primes {541,571,577}:
primary Semaev-μ₃ p∈{0.19,0.79,0.23}; combo-omnibus p∈{0.88,0.73,0.97}; interval-secondary
p∈{0.28,0.39,0.25}; Δ∈{+0.0009,−0.0049,−0.0003} (Δ>0 on 1/3). All firing controls fired. This is the
`[VERIFIED-scope — scoped null]` outcome at the discovery tier; confirmation (OOS {2029,2053,2089}) and
ladder are the remaining tiers. `|Δ| < MI_min(5k)=7.9×10⁻³`. NOT a closure (model scale, q≲2¹⁶).
