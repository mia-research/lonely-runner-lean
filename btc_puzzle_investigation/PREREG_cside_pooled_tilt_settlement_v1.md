# PREREG — c-side `inv` pooled-tilt settlement — v1 (FROZEN before data)

**Date:** 2026-07-31
**Status:** FROZEN pre-data. SHA-256 recorded below in §FREEZE. The decision rule (§2.2, §9) is fixed before any run; the RESULT grades strictly against §9.
**Queue item:** C — the c-side non-algebraic index correlation, the one wall the Weil closure does not cover (`STRUCTURAL_IMPLICATIONS_2026-07-30_v1.md` §5.3, §8; `NEXT_SESSION_PROMPT_2026-07-31_v1.md` step 1).
**Register:** purist.
**Prior artifact:** `RESULT_cside_nonalgebraic_correlation_v1.md` (v1) + `cside_orbitlevel_v1.py`.

---

## 0. OBJECT

Settle the flagged lead from v1: a small consistent **negative** bias of the orbit-level `inv`-map statistic $T_{\text{inv}}$ across 18 large primes (mean $z=-0.622$, 15/18 negative, Stouffer $z=-2.64$), which survived a calibration control but was **below per-prime detection and did not survive family-wise correction** — "not a finding, not nothing." The defect in v1's pooled number is methodological: it rests on **z-deflation by a measured calibration std (0.793)**, i.e. z-inflation correction applied after the fact. The record explicitly names the correct tool: a **calibrated (permutation) pooled p-value** rather than z-inflation (`RESULT_cside_nonalgebraic_correlation_v1.md` §4; `NEXT_SESSION_PROMPT_2026-07-31_v1.md` step 1).

**The binary to settle:** is the pooled tilt a **real small effect** ($T_{\text{inv}}\approx-0.02$, below the ~0.5 per-prime detection floor but consistent across primes) or the **tail of noise**? We settle it with ~36 large primes, a calibrated permutation pooled p-value, and an OOS replication gate. This is a **candidate** settle, not an avenue closure (see §10).

---

## 1. STATISTIC

### 1.1 Per-prime statistic (exact signal path)
For prime $p$ with prime group order $n=\#E(\mathbb{F}_p)$ and curve $y^2=x^3+7$, $p\equiv 7\pmod{12}$:

- $c[d]=\chi_2(y_{[d]G})\in\{-1,0,+1\}$, the Legendre symbol of the $y$-coordinate of $[d]G$ (exact `int64`, source `twist_orbit_spectrum_run_v1.signal`).
- **GLV reduction (forced, verified):** $c$ is constant on each $\mu_3$-orbit $\{d,\lambda d,\lambda^2 d\}$ ($\lambda=g^{(n-1)/3}$). Effective sample size $=$ orbit count $=(n-1)/3$, **not** $n$.
- `inv` map sends orbits to orbits: $f(d)=d^{-1}\bmod n$.
- **Per-prime statistic:** $T_{\text{inv}}(p) = \frac{1}{N_{\text{orb}}}\sum_{r} c_r\,c_{f(r)}$, the orbit-level mean product ($c_r$ = the constant value on orbit $r$). This is an **integer cross-product** $/N_{\text{orb}}$; the division is exact (ranked statistic, never a data threshold — `# noqa: float`).

### 1.2 Within-prime null (matched)
Orbit-label permutation: shuffle which $\pm1$ sits on which orbit, $R=2000$ draws. **Preserves the forced $\mu_3$-orbit structure** (the signal's symmetry) and the $\pm1$ multiset; destroys only arrangement. Per-prime null mean $\mu_p$, std $\sigma_p$ (the under-dispersion $\sigma_p\approx 0.79$ measured in v1 enters **here**, automatically, not as an after-the-fact deflation). Per-prime $z$-score $z_p = (T_{\text{inv}}-\mu_p)/\sigma_p$ (float, ranked vs the same null — `# noqa: float`).

### 1.3 Pooled statistic — ★ PRIMARY DECISION RULE
Stouffer on the per-prime $z_p$:
$$Z_{\text{pool}} = \frac{1}{\sqrt{N_P}}\sum_{p} z_p .$$
Stouffer is the correct combiner because the v1 lead is a **consistent mean shift**, not a sparse strong effect (the latter would call for Fisher / min-P). The **calibrated one-sided (left) pooled p-value** is built from the null directly — see §3.

### 1.4 Characterization fields (non-decisional, printed for transparency)
- Per-prime family-wise: Bonferroni over $N_P$ primes, and exact Holm.
- Sign count: $\#\{z_p<0\}/N_P$.
- **Legacy comparability**: the v1 0.793-deflated pooled $z$ (i.e. $Z_{\text{pool}}/0.793$) is recomputed and printed **for comparison with v1 only**; it is NOT a decision input.

---

## 2. MATCHED NULL

Orbit-label permutation (§1.2). Unchanged from v1 — v1's null was judged correct; the defect was in the **pooled** inference (z-deflation), not the per-prime null. The null shares the signal's forced $\mu_3$-orbit symmetry by construction.

---

## 3. POOLED-NULL CONSTRUCTION — the methodological fix

The calibrated pooled p-value is the empirical null distribution of $Z_{\text{pool}}$ itself:

1. Store the full per-prime null $z$-array: $Z_{\text{null}}[p]\in\mathbb{R}^{R}$ for each prime $p$ (the $R=2000$ standardized within-prime permutation statistics).
2. For $b=1,\dots,B$ with $B=10^5$: draw **one** within-prime null index $i_p\sim\text{Unif}\{1,\dots,R\}$ per prime (independent across primes), form $Z_{\text{pool}}^{(b)}=\frac{1}{\sqrt{N_P}}\sum_p Z_{\text{null}}[p][i_p]$.
3. **Calibrated one-sided (left) pooled p-value** $=$ exact integer count:
$$p_{\text{pool}}^{\text{cal}} = \frac{\#\{b : Z_{\text{pool}}^{(b)} \le Z_{\text{pool}}^{\text{data}}\}}{B}.$$

This builds the per-prime under-dispersion **into** the pooled null (each $Z_{\text{null}}[p]$ carries its own $\sigma_p$), so no post-hoc deflation is needed or applied. Pre-committed: $R=2000$, $B=10^5$.

---

## 4. FIRING CONTROL (must clear the gate at every prime)

The 80%-agreement plant (v1, corrected for exactness): a **fresh** random orbit-value assignment on independent RNG (seeded $1000p+\text{hash}(\text{fname})$, independent of $c$'s GLV structure), with a fraction `agree` of orbits forced to satisfy $v[f(r)]=v[r]$. The plant must land outside the within-prime null band at the **1%** tail on either side:
$$\text{gate fires} \iff (\#\{T_{\text{null}}\ge T_{\text{plant}}\}\le \lfloor R/100\rfloor)\ \text{or}\ (\#\{T_{\text{null}}\le T_{\text{plant}}\}\le \lfloor R/100\rfloor).$$

- `agree` expressed exactly: `nagree = (4*norb)//5` (no float literal).
- 1% tail expressed exactly: `ge_p*100 <= R` (integer cross-product, no `0.01`).
- **Any prime where the plant fails to fire is EXCLUDED from the pool AND recorded** ("[NO POWER]" primes). This is the v1 discipline; it stays.

---

## 5. POWER

- Pooled SE under the global null: $1/\sqrt{N_P}\approx 1/\sqrt{36}\approx 0.167$.
- v1 consistent mean $z\approx-0.6$ ⇒ fold-level expected $Z_{\text{pool}}\approx-0.6\cdot\sqrt{36}=-3.6$ if real at that magnitude across all primes; at $N_P=36$ a true mean-z of $-0.4$ still gives $Z_{\text{pool}}\approx-2.4$.
- Detection floor (per-prime, 4σ): $|T_{\text{inv}}|\gtrsim 0.5$ (v1). The putative effect $T_{\text{inv}}\approx-0.02$ is far below per-prime detection; **only pooling can see it**, which is exactly why the calibrated pooled p is the decision statistic.

---

## 6. SCOPE / FAMILY-WISE

- **Primary family = the `inv` map across $N_P$ primes.** Pre-committed pooled one-sided (left) $\alpha = \mathbf{0.01}$.
- Per-prime family-wise (characterization): Bonferroni $|z|>z_{1-\alpha/(2N_P)}$ and exact Holm at $\alpha=0.05$.
- **Secondary family = `pow-k` maps** ($k\in\{5,7,11,13\}$, admissible $\gcd(k,n-1)=1$) at the same $N_P$ primes: same calibrated pooled p construction, Holm over the secondary family at $\alpha=0.05$. Reported as a **channel bound**, never as a discovery channel (any pow-k hit goes through the same OOS gate as `inv` before any grade moves).

---

## 7. OOS (two layers; both run)

### 7a. PRIMARY — magnitude-blind hash-fold, K=2 (kfold_gate style)
Partition the $N_P$ primes into 2 folds by `fold_of(p, seed=FROZEN, K=2)` — SHA-256 of `"seed:repr(p)"`, **magnitude-blind** (a range split would confound fold with prime size). Compute, **independently in each fold**, the calibrated pooled p (§3). **Replication = AND-gate:** same sign (both folds negative) **AND** each fold's calibrated pooled $p<0.05$. One lucky fold does not replicate. (Idiom: `kfold_gate_v1.py` — builtin `hash()` forbidden, salted per-process.)

### 7b. SECONDARY — fresh-seed edge retest (the record's named convention)
Re-run the **3 most-negative primes from v1** (p=11503, 13147, 15607) on **fresh** independent within-prime null seeds; characterize regression to noise (if the tilt is a draw of the statistic, per-cell $z$ regresses toward 0). Characterization, not a gate.

---

## 8. EXACTNESS (no float in signal path — CLAUDE.md)

- $c[d]$: exact `int64` Legendre symbol (source `signal()`).
- Orbit construction, `inv`/`pow-k` maps, fold assignment: integer / SHA-256 only.
- $T_{\text{inv}}$: integer sum, exact cross-product for any threshold; the `/N_{\text{orb}}` mean is a ranked statistic (`# noqa: float`).
- $z_p$, $Z_{\text{pool}}$, $Z_{\text{pool}}^{(b)}$: float, **ranked vs the matched permutation null only**, never a data threshold (`# noqa: float`).
- $p_{\text{pool}}^{\text{cal}}$: exact integer count $/B$.
- The script **must pass `check_no_float.py`**. (v1's `cside_orbitlevel_v1.py` does NOT — it uses bare `0.8`/`0.01` literals in the gate; this PREREG's gate uses `nagree=(4*norb)//5` and `ge_p*100<=R` so the AST guard is clean.)
- The `0.793` legacy-deflation factor (§1.4) is applied to a **display-only** quantity; no float decision depends on it.

---

## 9. PRE-COMMITTED OUTCOME TABLE (the verdict, fixed before data)

| result | verdict / grade |
|---|---|
| $p_{\text{pool}}^{\text{cal}}<0.01$ (left) **AND** OOS 7a both folds replicate (same sign, each fold $p<0.05$) | lead **PROMOTED**: `[EMPIRICAL — consistent sub-detection effect, OOS-replicated]`. Still sub-per-prime-detection; not a per-prime finding. |
| $0.01\le p_{\text{pool}}^{\text{cal}}<0.05$, **OR** $p<0.01$ but partial OOS replication | **AMBIGUOUS / still open**. Lead neither closed nor promoted. |
| $p_{\text{pool}}^{\text{cal}}\ge 0.05$ **OR** OOS 7a fails (sign flips or a fold $p\ge0.05$) | lead **CLOSED as a candidate**. Scoped per-prime null retained. **Not an avenue closure** (§10). |

The counter-prior is honored in all three rows: a clean scoped null is a valid result; a surviving tilt is chased (here, by pooling); P1–P3 do **not** license manufacturing positives (no candidate moves up without the matched null + firing control + OOS + exactness + grade).

---

## 10. SCOPE CEILING (what this does NOT close)

- Regime: $p\sim 10^4$, orbits $\sim 3$–$5\times10^3$. This is **three orders of magnitude below** the puzzle's $\sqrt n\sim 2^{128}$ threshold where complete-sum bounds go vacuous.
- This run **cannot** close the c-side channel at the puzzle's native scale. The operationally-decisive form is the **shortscalar arm at $2^{128}$** (`PREREG_incomplete_shortscalar_v2`), which is **gate-blocked** (experiment-designer failed 3×) and is NOT touched here. No real-82-keys verdict is claimed or implied.
- A "lead closed as a candidate" verdict here means: *at the orbit level at $p\sim10^4$, the pooled `inv` tilt is consistent with noise.* It does not say the channel is inert at $2^{128}$.

---

## Tooling inventory
- `twist_orbit_spectrum_run_v1.signal` — exact int64 signal source (Legendre of $y_{[d]G}$).
- `cside_orbitlevel_v1.py` — the v1 orbit-level test (reference; this PREREG supersedes its pooled inference).
- `kfold_gate_v1.py` — `fold_of` (SHA-256 magnitude-blind fold) + exact `_passes` idiom (referenced for §7a).
- `check_no_float.py` — AST exactness guard (must pass).
- New: `cside_pooled_tilt_settlement_v1.py` (the run), `cside_pooled_tilt_settlement_v1.json` (the captured numbers for the RESULT).

## Ill-posed points disclosed (not assumed away)
1. **Marginal-vs-structure.** $T_{\text{inv}}$ is an orbit-level *mean product*; a per-point marginal null does not settle it. We use the orbit-label permutation (matched to the forced symmetry), consistent with CLAUDE.md.
2. **Selection of "most-negative" cells for 7b.** Selecting the top-3 after seeing data is an inherently weaker OOS; that is why 7a (magnitude-blind fold, pre-committable) is PRIMARY and 7b is characterization only.
3. **Prime set is discovery-free?** The prime set is sampled by an upward `nextprime` scan (p≡7 mod 12, #E prime, orbits≥~3000), not cherry-picked from v1's 18; the only v1-tied primes are the three named in 7b (explicitly disclosed).
4. **`B=10^5` MC error.** At $p\sim0.01$, the binomial MC std on the calibrated p is $\sim\sqrt{0.01\cdot0.99/10^5}\approx 3\times10^{-4}$ — well inside the 0.01 vs 0.05 decision gap. Reported with the p-value.

---

## FREEZE
SHA-256 of this file (computed post-write, recorded in the RESULT):
`e4a95ca3eaded16afd7ae14c84b9ca27c79b95020b0f46cba2c1e2931ae5d5e5`
(Frozen 2026-07-31. Note: recording this SHA inside the file changes the file's own hash; the frozen content is everything above this FREEZE section. The RESULT will cite both this placeholder-line hash and, for full reproducibility, a hash of the file with the FREEZE section stripped.)
