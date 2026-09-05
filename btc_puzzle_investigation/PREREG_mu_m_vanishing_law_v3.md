# PREREG v3 — `μ_m` vanishing law, RERUN with the complete control set (SUPERSEDES v2)

**Written 2026-08-02, after the v2 run completed and was audited.** v2's *design* was sound; its
**implementation omitted two pre-registered controls and the cross-instrument comparison**. This is
the rerun. v1 and v2 retained unmodified.

---

## 0. Why the v2 run does not establish its own conclusions

Audit of `mu_m_vanishing_law_v1.sage` against `PREREG_mu_m_vanishing_law_v2.md` §3:

| pre-registered control | implemented? |
|---|---|
| **C1** point-count `p`-rank `≤ S` | yes — **but only the `pc > S` half** |
| **C1, cross-instrument** — point-count vs Cartier | **NO.** The two instruments were **never compared.** `prank_pointcount`, the load-bearing independent readout, went into the run **entirely unvalidated** |
| **C2** wrong-pairing firing control, `p ≢ ±1 (mod m)` | **NO.** The script's only prime loop is `q % m == m-1`; C2 never ran |
| **C4a** entrywise `m=4` regression | yes — PASS |
| **C4b** `(4,3)` anchor vs independently computed `a_p(E)` | **NO.** Never implemented — and it is the only check that would have validated `prank_pointcount` |
| **K-plant** | yes — PASS |
| **K-attain** | reported, **never asserted** as pass/fail |

**An unrun control is not a passed control.** The v2 run's headline ("the pairing mechanism survives
out-of-sample") was stated at a strength its control set did not support. It is withdrawn pending
this rerun.

**What the audit found when the missing controls were run separately**
(`audit_mu_m_missing_controls_v1.sage` / `.log`) — both healthy, which is why this is a rerun and not
a retraction:
- **C4b: 37 rows, 0 mismatches** — `prank_pointcount` agrees with `p`-rank`(E)` from `a_p`, **and**
  the two instruments agree with each other on every row.
- **C2 FIRES: 4/4 eligible cells** — at `p ≢ ±1 (mod m)` the true orbit bound is `0` while `S = 2`,
  and the measured `p`-rank differs from `S` on every row. `S` is specific to the `b ↔ m−b` pairing.

**Contamination.** The v2 outcome is known to me. Per the standing rule (a result whose controls are
completed *after* the outcome is known cannot carry a primary claim), the **v2 sample is marked
`[CONTAMINATED — controls completed after outcome known]`** and this rerun uses **fresh `f`**.

## 1. Sample

**Seed `20260806`** (v2 used `20260805`). Prime schedule unchanged — it is *determined* by
`p ≡ −1 (mod m)`, `p > d`, `p ≤ 200` and the C1 budget, not chosen by me, so primes necessarily
overlap. **The sampled covers `(p, f)` are disjoint from v2's**, since every `f` is a fresh draw.
Stated precisely: *disjoint covers, overlapping primes* — not "a fully disjoint sample".

Everything else in v2 §1, §2, §4, §5, §6 is carried unchanged: objects, `S`/`S_new` predictions,
`N_F = 40`, `N_C1 = 8`, budget `p^g ≤ 5·10⁶`, `(5,4)` uncovered and instrument-internal, the
permitted-conclusion table, and the scope statement.

## 2. The complete control set — every item asserted, not merely printed

| id | statement | pass condition |
|---|---|---|
| **C1a** | point-count `p`-rank `≤ S` at every covered row | 0 violations; **a violation refutes the pairing mechanism** |
| **C1b** *(new)* | **point-count `p`-rank `==` Cartier stable rank**, per row, every covered row | 0 disagreements; else **VOID** — the two instruments are then not measuring the same object |
| **C2** *(new)* | wrong-pairing arm, `p ≢ ±1 (mod m)`: `S` must **mispredict** the measured `p`-rank | ≥1 row per eligible cell, **all** cells with `S_true < S` mispredict; else **VOID** — `S` would be a generic bound, not a test of the pairing |
| **C4a** | entrywise `m=4` regression against `anew_m_support_v2.sage` | exact match |
| **C4b** *(new)* | `(4,3)`: `p`-rank `= 1` **exactly** where `a_p(E) ≢ 0 (mod p)`, `a_p` from Sage's `EllipticCurve`. The supersingular-`E` exception is **expected**, not a failure | 0 mismatches |
| **K-plant** | readout reports a planted stable rank, all achievable (i.e. even on non-self-paired pairs) values | all reported |
| **K-attain** | pipeline reaches `S` at least once per `(m,d)` — **now asserted** | ≥1 attaining row per `(m,d)`; else that `(m,d)` is instrument-suspect and its P2 datum is withdrawn |

**Cost note, measured not assumed.** I previously claimed a per-field power-residue table would cut
the runtime "several-fold". **Benchmarked: it is 0.4–0.6× — i.e. slower** (Sage's `v**e` is optimised;
hashing field elements into a set is not). The counter is therefore left as-is and the rerun costs
about what v2 did (~57 min CPU + ~10 for the added controls). No compute-driven change to the sample.

## 3. What changes about the permitted conclusions

Nothing is added. One is removed: **the v2 run's conclusion is withdrawn**, and the rerun's
conclusion is admissible only if C1a, C1b, C2, C4a, C4b, K-plant and K-attain all pass. If any fails,
the outcome is VOID and reported as such, with no support statement in either direction.

*Frozen at first v3 script execution. Deviations → `PREREG_mu_m_vanishing_law_v3_DEVIATIONS.md`.*
