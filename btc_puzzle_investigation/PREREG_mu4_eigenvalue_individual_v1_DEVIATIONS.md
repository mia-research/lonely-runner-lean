# DEVIATIONS — `PREREG_mu4_eigenvalue_individual_v1.md`

Run: `mu4_eigenvalue_individual_v1.py` → `mu4_eigenvalue_individual_v1.log`, 2026-07-20.
Every deviation below is recorded before the result is read.

| # | Pre-committed | Actual | Handling |
|---|---|---|---|
| 1 | H2 distinct configs `K2 = 22` (computed a priori from scope) | script computed **26** distinct `(p, cubic class of B)` | **The pre-committed 22 is used in every significance statement** (smaller, and it was frozen before the run). Both numbers printed. The prereg's a-priori *cell sizes* `{7:6, 2:5, 11:1}` were reproduced exactly, so the discrepancy is in the total-count convention, not in the arm's composition. |
| 2 | H2b tested by **7** configurations | only **3** configurations (same `p`, same cubic class, differing quadratic class) exist in the window | H2b is underpowered **relative to its own prereg**, not just to the `K≥10` bar. Reported as "consistent, K=3"; **not** reported as confirmed independence. |
| 3 | 156 rows, "no skips expected" | **155** rows; `nCM x^3-x+3` at `p=239` skipped (`4A³+27B² = 239 ≡ 0`, singular reduction) | Row key and reason printed as §4 requires. The skipped row is in the **exploratory** arm; no CM row was skipped, so H1/H2 row counts are unaffected (42 and 36 as pre-committed). |
| 4 | cost "tens of minutes"; truncation to `p<400` permitted if needed | **564 s**, full `200<p<500` window | **No truncation used.** Route A reads the quartic class of each `u ∈ F_q` off a cached generator-walk table (`q` multiplications) instead of `q` exponentiations. Route B is unchanged and still uses the literal prereg formula with per-element exponentiation, so the two routes remain separate code paths. |
| 5 | Plant 3: `b1 ≠ 0` on ≥1 of the four `p ≡ 1 mod 4` rows | fired **2/4** (`p=229, 241`); `b1 = 0` also at `p=233, 257` | Bar met (≥1). **Recorded as an observation, not a hypothesis:** `b1 = 0` is not exclusive to `p ≡ 3 mod 4`. The μ₄ argument gives `p ≡ 3 mod 4 ⇒ b1 = 0`; the converse was never claimed and these two rows show it is false. |

**Not deviations, recorded for completeness:** Control 1 passed on 155/155 out-of-sample rows and
30/30 in-sample readout re-checks; Plant 1 fired with 42 violations; Plant 2 fired 1/3 (bar ≥1);
the forced columns (`b1 = 0`, `p | b2`, `|m| ≤ 2`) held on every `p ≡ 3 mod 4` row and are reported
as forced, contributing zero evidence.
