# AUDIT — `RESULT_mu_m_vanishing_law_v1.md`: methods, results, conclusions

**2026-08-02, user-requested audit.** Verdict: **the run's control set was incomplete, so the run
does not establish its conclusions.** Three control defects, two reporting overstatements.
`RESULT_..._v1.md` is **superseded**; its headline is withdrawn pending the rerun under
`PREREG_mu_m_vanishing_law_v3.md`.

The conclusions are **unrefuted**: the two omitted controls, run separately afterwards, passed
(C4b, 37 rows, 0 mismatches) and fired (C2, 4/4 cells) — see §D. Unrefuted is not established, and
what the rerun returns is not predicted here.

---

## A. METHODS — three defects

**A1. Two pre-registered controls were never implemented.** Established by grep against the script,
not from recollection: the only prime loop is `q % m == m-1`.

| control | prereg v2 §3 | in `mu_m_vanishing_law_v1.sage` |
|---|---|---|
| **C2** wrong-pairing firing control, `p ≢ ±1 (mod m)` | specified with a pre-registered `S′` table | **absent** |
| **C4b** `(4,3)` anchor vs independently computed `a_p(E)` | specified | **absent** |

C2 is the control that establishes `S` is *specific to the `b ↔ m−b` pairing* rather than a bound
that holds regardless. C4b was the only specified check that would have validated
`prank_pointcount`.

**A2. C1 was half-implemented.** It tested `pc > S` only. **The two instruments were never compared**
— no `pc == cartier` check anywhere — so `prank_pointcount`, the readout carrying the entire result,
entered the run **unvalidated**. *(Independently identified by the user.)*

**A3. K-attain was printed, never asserted.** It passed everywhere, but the script had no failure path
for it.

**On `prank_pointcount` itself:** audited line by line and **correct** — power sums `s_n = p^n+1−N_n`;
Newton's identities; functional-equation extension `e_j = p^{j−g}e_{2g−j}`; `p`-rank
`= max{j : v_p(e_j) = 0}`. But correct-on-inspection is not validated, and inspection is precisely
what this project's record shows does not catch defects.

**Standing rule applied: an unrun control is not a passed control.**

## B. RESULTS — two overstatements

**B1. The `m = 7` and `m = 8` evidence is one prime each.** The C1 budget admits only `p = 13` for
`(7,3)` and only `p = 7` for `(8,3)` (confirmed in the rerun's own printed prime lists). So:

| `(m,d)` | C1 primes | C1 rows |
|---|---|---|
| (4,3) | 20 | 160 |
| (3,4) | 19 | 152 |
| (3,5) | 6 | 48 |
| (5,3) | 2 | 16 |
| (4,5) | 2 | 16 |
| **(7,3)** | **1** (`p=13`) | 8 |
| **(8,3)** | **1** (`p=7`) | 8 |

*"Survives out-of-sample at `m ∈ {3,5,7,8}`"* is carried by **8 covers at a single prime** for two of
those four values. The broad coverage is `(4,3)` and `(3,4)` — the small-`m` cases. v1 stated the
breadth without this.

**B2. P3's headline came from the descriptive instrument.** The `387/400` at `(5,3)` is `pair_ranks`
on the **Cartier** matrix, which the prereg itself says carries no weight. Only the **16** C1 rows
have independent backing, and indirectly at that: total `p`-rank `= 2` with `{1,4}` forced to `0`
gives `{2,3} = 2`. v1 wrote "387 of 400 rows" as if all were independently established.

**Passing coherence check, found during the audit and not in v1:** `(4,3)` has 14/160 non-attaining
rows = 8.75%, matching the expected frequency of supersingular `E`.

## C. CONCLUSIONS — the inferential chain holds

- `p`-rank `≤ S` is a **consequence** of the pairing, so confirming it is corroboration, not proof —
  and v1 graded it `[VERIFIED]`, not `[PROVED]`. Correct.
- The point-count readout shares essentially nothing with the Cartier code (only `genus()` and the
  parameters), so agreement between them is meaningful rather than circular.
- The test has real discriminating power: were the grading claim false, the `p`-rank could reach `g`
  (3 rather than `≤1` at `(4,3)`).
- The `(4,3)`-specific correction — the vanishing is **`d`-dependent**, condition
  `min(b,m−b)·d < m` for all `b` coprime to `m` — is independently derived and **stands**.
- Scope discipline held: no ECDLP or hardness statement anywhere.

## D. The missing controls, run separately

`audit_mu_m_missing_controls_v1.sage` / `.log`:

- **C4b — 37 rows, 0 mismatches.** `prank_pointcount` agrees with `p`-rank`(E)` from `a_p`, **and**
  the two instruments agree with each other on every row.
- **C2 — FIRES, 4/4 eligible cells.** At `p ≢ ±1 (mod m)`, `S_true = 0 < S = 2`, and the measured
  `p`-rank differs from `S` on every row.

**So the conclusions survive.** But the outcome was known before these controls were completed, so
the v2 sample is `[CONTAMINATED — controls completed after outcome known]` and cannot carry the
claim. Hence the rerun on fresh `f`.

## E. Process defects recorded, without spin

- **Third occurrence this session** of the Sage-`Integer` seed bug (`random.Random(int(SEED) + 100)`
  re-promotes to `Integer`). Caught each time by a launch check, never by inspection.
- The two bugs caught pre-run in v1 (the `exec` clobbering `PMAX`/`SEED`; the K-plant planting an
  unachievable odd rank) are already recorded in `RESULT_mu_m_vanishing_law_v1.md` §3.
- **A claim of mine that measurement refuted:** I stated twice that a per-field power-residue table
  would cut the point-count runtime "several-fold". **Benchmarked at 0.4–0.6× — slower.** Sage's
  `v**e` is optimised; hashing field elements into a set is not.

These are ordinary implementation errors caught by cheap checks. They are not evidence that the
control philosophy works; the philosophy failed here, in that three specified controls were simply
not written.

## F. Disposition

| item | status |
|---|---|
| `RESULT_mu_m_vanishing_law_v1.md` | **SUPERSEDED**; headline withdrawn |
| P1 "pairing survives out-of-sample" | **withdrawn pending rerun**; and when restated must carry the per-`(m,d)` prime counts of §B1 |
| P3 at `(5,3)` | **withdrawn pending rerun**; when restated, the independent count is 16, not 400 |
| the `(4,3)`-vs-`m=4` correction | **stands** — derived, not measured |
| v2 sample | `[CONTAMINATED — controls completed after outcome known]` |
