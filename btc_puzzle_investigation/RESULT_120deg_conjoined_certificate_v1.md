# RESULT: the 120° census certificate, repaired (conjoined)

**Date:** 2026-08-01
**Script:** `verify_120deg_conjoined_certificate_v1.py` (reuses `verify_120deg_symbolic_factorization_v1.py`, `verify_120deg_exact_certificate_v2.py`, `run_n1_120deg_v1.py`, `audit_n1_vsign_v2_core.py`).
**Grade:** `[PROVED-exact — conjoined: PART 1 (symbolic, unconditional) + PART 2 (exact integer residual) + census (exact modular upper bound)]` at 22 primes / 3585 cells.
**Register:** purist. Item A of the 2026-08-01 plan; repairs `CORRECTION_120deg_census_certification_direction_v1.md`.

---

## 0. What was wrong, and what this repairs

`run_n1_120deg_v1.py` reported $g=\min_\ell g_\ell$ and read a computed $2$ as "$g=2$". That is one-sided: reduction only **raises** gcd degree, so $\min_\ell g_\ell \ge g_{\text{true}}$ — a computed $2$ certifies only $g_{\text{true}}\le 2$ (consistent with $g_{\text{true}}\in\{0,1,2\}$). The census's headline ($=2$) was the uncertified direction. This **does not retract the 120° law**; it corrects the *certification*, hence the *grade*.

## 1. The repair — a conjunction of two exact halves

Neither half alone yields $g=2$; together they do.

**(Lower bound, $g\ge 2$.)** PART 1 (`verify_120deg_symbolic_factorization_v1.py`) proves, with $e_1$ and $p$ free indeterminates and $\varepsilon=\chi_2(-1)$ of either sign, the identities
$$e_2=e_1^2-\varepsilon p,\qquad e_3=\varepsilon p\,e_1,\qquad e_4=p^2,$$
from which $L(T)=D(T)\,\overline D(T)$ and $L(\zeta_3 T)=\zeta_3\,(T^2+e_1 T+\varepsilon p)\,D(T)$ with $D(T)=T^2+\zeta_3 e_1 T+\varepsilon p\,\zeta_3^2$ monic and non-degenerate, hence $\deg\gcd(L(T),L(\zeta_3 T))\ge 2$ **unconditionally** — a degree-2 common factor over $\mathbb{Q}[\varepsilon,p,\zeta_3][T]\subseteq\mathbb{Q}(\zeta_M)[T]$, $M=\operatorname{lcm}(n,3)$, with **no finite-field embedding or inflation** in the lower bound. PART 2 (`verify_120deg_exact_certificate_v2.check_identity`) measures the one empirical input exactly, per prime, uniform over every cell $a\ne 0$:
$$V_2(a)-V_1(a)^2=-2\varepsilon p.$$
A prime that "holds" (PART 1 symbolic proof + PART 2 exact residual) has $g\ge 2$ at **every** surviving cell.

**(Upper bound, $g\le 2$.)** The census $\min_\ell g_\ell==2$ for that cell (`run_n1_120deg_v1.g_and_flags`). Here, where PART 1 already supplies $g\ge 2$, the computed upper bound $g\le 2$ is exactly what closes the gap.

**Conjunction:** $\;\text{holds}(p)\;\wedge\;\min_\ell g_\ell(a)=2\;\Longrightarrow\;g_{\text{true}}(a)=2\;$ exactly.

## 2. Self-test — the conjunction is not vacuous

The CORRECTION's witness PLANT-B ($\alpha=3+2i,\ \beta=2+3i$, both of norm $13$; ratio $\beta/\alpha=i$, not a cube root of unity; **true $g_3=0$**) reads $\min_\ell g_\ell=2$ when reduced mod $l=13$ — the inflation mechanism the CORRECTION identified, made real. The conjoined verdict **correctly refuses to certify** it: the algebraic identity $e_2-e_1^2\equiv-\varepsilon p\pmod l$ fails ($11\not\equiv 0$ at $l=13$, $\varepsilon=+1$, $p=13$). A $g=2$ census reading does **not** trigger a $g=2$ certificate here. The conjunction catches exactly the failure the standalone census could not.

## 3. Result — all 22 primes wholly exact

| stratum | primes | $\varepsilon$ | cells | certified $g=2$ exact | null ($g=0$) | uncertain | abstain |
|---|---|---|---|---|---|---|---|
| IN-SAMPLE | 7 | $-1$ | 197 | 197 | 0 | 0 | 0 |
| **STRATUM S (PRIMARY)** | **10** | **$-1$** | **2464** | **2464** | **0** | **0** | **0** |
| STRATUM C (+1 branch) | 5 | $+1$ | 924 | 924 | 0 | 0 | 0 |

**Verdict:** $22/22$ primes wholly exact, $3585/3585$ cells certified. The $g=2$ reading at the 2464 S-stratum cells (previously `[VERIFIED — exact upper bound $g\le 2$]`) is now certified exactly; the $+1$ branch ($p\equiv1\bmod4$, $\varepsilon=+1$) is certified by the same conjunction. Per-cell spreads $\max_\ell g_\ell-\min_\ell g_\ell$ are recorded in `RESULT_120deg_conjoined_certificate_v1.json` alongside every cell.

Exact integer/modular arithmetic only; no float in the signal path.

## 4. Scope, held honestly

- **This promotes the 2464 S-stratum cells back to `[PROVED-exact (conjoined)]`.** Both halves are exact; the lower bound carries no probabilistic/embedding argument once PART 1's symbolic factorization is conjoined.
- **Not uniformity.** This certifies $g=2$ at every surviving cell of the 22 frozen primes. It does **not** prove the 120° lock for every $a$, every $p\equiv7\bmod 12$ (frontier #26). "No finite sweep can" prove uniformity; that is a proof target (Stickelberger/Iwasawa coefficient-ring form of $e_2(a)=e_1(a)^2+p$), not a measurement.
- **Independent corroboration unchanged.** The eigenvalue-level observation of `ANALYSIS_n1_charpoly_collapse_v1.md` §3 (ratio to $\zeta_3^k\le4.5\times10^{-44}$ at $p=43,67,127$) still supplies the lower-bound direction, numerically, at small primes.

## 5. What this opens / closes

- **Closes:** the certification defect of `CORRECTION_120deg_census_certification_direction_v1.md`; promotes the census $g=2$ headline (and the $+1$ branch) to genuinely exact, conjoined.
- **Unblocks (downstream):** the Kronecker/Stickelberger-route premise and `ANALYSIS_n1_charpoly_collapse_v1.md` item 1, which leaned on "$g=2$ at every cell," now rest on an exact conjunction rather than a one-sided bound.
- **Leaves open:** uniformity (#26 — a proof, not a measurement); the purer direct-gcd $Z[\zeta_M]$-resultant form (item A2 of the plan, an independent cross-check of this conjunction, not required for the grade).
