# PREREG — is the sub-Rayleigh deficit's prime-to-prime scatter an ARITHMETIC function of the curve?

**File:** `PREREG_subrayleigh_deficit_arithmetic_scatter_v1.md`  **Date:** 2026-08-06
**Status: PRE-RUN / DRAFT for `experiment-designer`.** No confirmatory statistic in §3 has been
computed. The existing 30-prime table of `RESULT_subrayleigh_deficit_scaling_v1.md` is used **only**
to *fix the hypothesis and its sign* (§2); it is frozen as the TRAINING set and may not appear in any
confirmation number. Every confirmatory number comes from primes/twists NOT in that table.

**Provenance of this spec.** Follows `RESULT_subrayleigh_deficit_scaling_v1.md`, whose level-2
verdict was `ABSTAIN / UNRESOLVED_PERSISTENT` with `χ²_red = 204`: no smooth model (const, 1/log p,
power) fits `D(p)`, because of large **prime-to-prime scatter**. The scaling run named neither an
exponent nor a cause. This spec asks the successor question the scatter poses: **is that scatter a
low-complexity arithmetic function of the curve, or is it high-complexity (only reproduced by
recomputing the sum)?** The two have different consequences and only the first is a handle.

---

## §0 SCOPE BANNER (inherited by every number this run produces)

Enumerable model curves `E : y² = x³ + 7·g^k` over `F_p` (`k = 0` is the base curve; `g` a fixed
sextic non-residue mod p gives the five sister twists), `p ≡ 1 (mod 3)`, group order `#E`
enumerated in full, cyclic part only. `p = 2²⁵⁶−2³²−977` is **not** enumerable and **nothing here
transfers to it** — every object below is a full group sum over all group elements. No ECDLP,
extraction, key-recovery, or security claim is made or may be derived from any outcome. This studies
the *structure of a spectral statistic of a curve*, nothing downstream.

---

## §1 OBJECT

For a cyclic `E/F_p` of order `n` with canonical generator `G` (`canonical_generator(p,n)`), index
group elements `P_d = d·G`, `d = 1..n`, coordinates `(x_d, y_d)` (exact int EC arithmetic,
`ec_add`). Reusing the FROZEN instrument `subrayleigh_deficit_scaling_v1.py`:

```
U(b,c)   = Σ_{d} e_n(d) · e_p(b·x_d + c·y_d)                  (b,c) ∈ [0,p)²,  S = (b,c)≠(0,0)
M_char   = mean_{S} |U(b,c)|                                  (character weight g(d)=e_n(d))
mu(p,k)  = E_null[ mean_S |U| ]   estimated by K Hermitian-matched null draws (null_weight)
δ(p,k)   = ( mu − M_char ) / mu                               (the deficit; run_prime returns it as D)
SE_δ     = sdM / (mu·√K)                                      (estimation error of δ; run_prime SE_D)
```

**δ is DETERMINISTIC given the curve.** `M_char` has no sampling noise — it is the exact character-sum
magnitude profile of `E`. The only estimation error is in `mu` (how well K null draws pin the null
mean), which is `SE_δ` and is tiny (≤ 8e-5 at every prime in the training table). Therefore the
prime-to-prime variation of δ, above `SE_δ`, is **real deterministic structure of the curve**, not
measurement noise. The question is not *"is there scatter"* (there is) but *"does the scatter
COMPRESS to a compact invariant."*

**The candidate compact invariant — the signed Frobenius trace.**
```
a_p(k) = p + 1 − #E_k                          (EXACT integer; #E from the point enumeration)
t(p,k) = a_p(k) / (2√p) ∈ [−1, 1]              (signed normalized Frobenius / Sato–Tate cosine)
```
`a_p` is a **global point count**; δ is a **spectral-shape statistic of the magnitude distribution**.
They are different functionals of the same curve — **disjointly constructed** (project
disjoint-construction rule): neither is computable from the other without re-deriving the curve. A
correlation between them is therefore not a residue-vs-component tautology. (Tautology guard, §4.)

---

## §2 HYPOTHESES — committed now, sign fixed from the TRAINING table only

The training table (30 primes, `RESULT_subrayleigh_deficit_scaling_v1`) shows δ largest at `t≈+1`
(p=2671: t=+0.997, D=1.109e-3) and smallest at `t≈−1` (p=4177: t=−0.967, D=0.884e-3; p=12043:
t=−0.989, D=0.964e-3). **This fixes the pre-committed sign: δ INCREASES with signed `t`.** Using the
training data to fix a directional hypothesis is legitimate; using it to *confirm* is not — hence all
confirmation is out-of-sample (§6).

- **H1 (PRIMARY — within-p, p held exactly constant).** Across the six sextic twists at a fixed p,
  δ(p,k) is a **positively monotone** function of `a_p(k)`. This is the p-controlled form: p, the CM
  field `Q(ω)`, |S|, and the instrument are identical across the six twists; only the Frobenius
  `a_p(k)` (equivalently which twist) varies. If δ tracks `a_p` here, `a_p` is the driver, with the
  p-confound removed by construction.
- **H2 (SUPPORTING — between-p, out-of-sample).** On a NEW schedule of base curves `y²=x³+7` at
  primes not in the training table, δ(p) rank-correlates **positively** with `t(p)`, one-sided at the
  pre-committed sign.
- **H0 (NULL — an explicitly valid, pre-committed positive outcome).** δ does NOT compress to `a_p`:
  either H1's within-p ranks are inconsistent / null, or H2's OOS correlation is null at the committed
  sign. Reported as *"the deficit's scatter is not a low-complexity function of the Frobenius trace at
  this scope"* — a scoped null with named power, NOT a closure of "arithmetic structure" in general,
  and NOT a statement about the mechanism (row-budget) or about other invariants (§9 tertiary).

**Multiplicity is controlled by design:** exactly ONE primary (H1) and ONE supporting (H2), both with
the sign pre-fixed. A "CONFIRMED" verdict requires BOTH to fire at the committed sign. Other invariants
(§9 tertiary) are exploratory, Holm-corrected, and cannot produce a verdict.

---

## §3 STATISTICS — one primary, named now

| id | statistic (the only verdict-bearing form) | null distribution |
|---|---|---|
| **H1** | For each twist-schedule prime p: the **one-sided rank slope** of δ(p,·) vs `a_p(·)` over the (≤6) cyclic twists — Spearman `ρ_p` (exact, all `≤6!` orderings enumerable). Combine across the `P_tw` twist-primes by **Stouffer** `Z_within = Σ_p z(ρ_p)/√P_tw`, one-sided (positive). | per-prime exact permutation of the twist-label↔δ pairing; Stouffer under independence across primes |
| **H2** | **Spearman ρ(δ, t)** over the OOS between-p schedule, one-sided positive. | exact permutation of the (p ↔ t) labels, ≥1e5 shuffles or full if feasible; integer-count p-value |
| tertiary | for each secondary invariant (§9): its own exact permutation rank-correlation with δ, **Holm at FWER 0.05**, reported only if H1 fires, non-verdict | permutation of (p ↔ invariant) |

Secondary/reported-not-verdict: the fitted monotone shape δ vs t (isotonic, for display only); the
per-twist δ table with exact `a_p`; leave-one-prime-out on both H1 and H2.

---

## §4 MATCHED CONTROLS, FIRING CONTROLS, TAUTOLOGY GUARD

- **Disjoint construction (structural).** `a_p` = point count; δ = spectral magnitude shape. The
  permutation nulls shuffle only the (curve ↔ invariant) pairing, holding both computations fixed.
- **Tautology guard (must PASS before any verdict).** Confirm δ is **not** an affine/monotone image of
  a quantity already inside its own definition. Specifically: `M_char`, `mu`, and `#E` are logged;
  assert that `a_p` is NOT recoverable from `δ` alone across the training table to better than the
  residual scatter (i.e. δ→a_p has large irreducible error), so a correlation is compression, not
  identity. If δ turns out to be a deterministic function of `a_p` to within `SE_δ` (perfect
  compression), that is the STRONGEST positive, reported as such — but flagged, because a *too-perfect*
  fit is examined for a hidden definitional link (e.g. `mu` or `|S|` carrying `a_p` via `n`).
- **p-confound firing control (H1's reason to exist).** H1 holds p exactly fixed; any between-p
  correlation (H2) that is NOT reproduced within-p (H1) is attributed to a p-covariate, not to `a_p`.
  H2 without H1 may not be read as "`a_p` drives δ."
- **The scatter-vs-estimation check (state, trivially expected to pass).** Confirm the between-curve
  spread of δ exceeds `SE_δ` by the pre-committed margin at the large primes (≥10×). At p=12043,
  `SE_δ = 2.6e-6` and δ ≈ 1e-3, ratio ~400 — the scatter is ~400× the estimation error; there is
  genuine deterministic structure to explain. (If this failed, the premise would be void — it does
  not, per the training table, but it is asserted in code, not assumed.)

---

## §5 PLANTED POSITIVE CONTROLS — all must fire before any verdict

| id | plant | must fire in | pass criterion |
|---|---|---|---|
| **P1** | inject a synthetic deficit `δ'(p,k) = c·t(p,k) + baseline` (c>0) onto the real `a_p`/twist labels, `c` ≈ observed spread | H1, H2 | recovered ρ > 0 one-sided at p < 0.01 |
| **P2** | shuffle the (curve ↔ `a_p`) labels on the SAME δ values (negative control — must be SILENT) | H1, H2 | ρ null; one-sided p not significant, at the nominal rate |
| **P3** | brute-force `#E` (hence `a_p`) at two twist-primes by two independent methods (Schoof-free full enumeration vs. baby-step/giant-step order) — **integer-identical** | invariant path | `a_p` agrees exactly; twist construction verified (six distinct `a_p`, summing to 0) |
| **P4** | re-measure δ at 3 training primes with independent null seeds; δ stable to `≤ 2·SE_δ` | instrument | stable ⇒ δ is the deterministic quantity claimed |

**If any of P1–P4 fails, the corresponding arm reports "control did not fire; result uninformative"
and issues no verdict.**

---

## §6 SCOPE & SCHEDULE

- **Training (direction only, FROZEN, never in a confirmation number):** the 30 primes of
  `RESULT_subrayleigh_deficit_scaling_v1` (p ∈ [151, 12043]).
- **H1 twist schedule (PRIMARY):** a pre-committed set of `P_tw ≥ 12` primes `p ≡ 1 (mod 3)`,
  disjoint from the training set, spanning `p ∈ [~1500, ~12000]` (large enough that `SE_δ ≪` the
  δ-spread). At each, construct all six sextic twists `y²=x³+7·g^k` (`g` = smallest sextic non-residue
  mod p); include a twist only if `E_k` is **cyclic** (needed for the `d`-indexing); require ≥4 cyclic
  twists per prime or the prime is dropped and logged. `a_p(k)` from full point count.
- **H2 OOS schedule (SUPPORTING):** `≥ 30` NEW base curves `y²=x³+7` at primes `p ≡ 1 (mod 3)`,
  disjoint from training and (where possible) from the H1 set, spanning the same range, chosen by a
  deterministic rule (e.g. the next qualifying primes above each training prime) — the rule is frozen
  here so the set cannot be chosen to help.
- **Cost.** One `p×p` complex128 FFT per (curve, K-draw), as in the scaling run; at p≈12000,
  `~1.15e8` complex128 ≈ 1.8 GB per array — the binding constraint, identical to the scaling run's
  ceiling; K per prime as `Kfor(p)`. Six twists × 12 primes + 30 OOS ≈ 100 curve-measurements — hours,
  feasible. If the top primes exhaust memory they are dropped and the set used is logged.
- **Frozen numbers to record before running:** the exact H1 and H2 prime lists, `g` per prime, and
  the cyclic-twist count per prime — appended as `_SCHEDULE.txt` and SHA-256'd with this spec.

---

## §7 POWER

- **H2 (between-p, OOS).** With 30 primes a true Spearman `ρ = 0.5` is detected one-sided at α=0.01
  with power ≈ 0.9; `ρ = 0.4` ≈ 0.7. The training-table Spearman (direction-fixing only, not a test)
  is ρ ≈ +0.45 at the 12 largest primes — so IF that holds OOS, H2 is adequately powered at 30 primes.
  **If the true effect is `ρ < 0.35`, 30 primes is underpowered — declared now; a null H2 at 30
  primes is then reported as `[UNDERPOWERED below ρ≈0.35]`, not as a refutation.**
- **H1 (within-p).** Per prime, ≤6 points give a coarse `ρ_p`, but `P_tw ≥ 12` independent primes
  Stouffer-combine. If the within-p monotonicity is real with per-prime `ρ_p ≈ 0.6`, `Z_within ≈ 12·
  E[z]`; even `ρ_p ≈ 0.5` over 12 primes clears `Z_within > 3`. If most primes yield only 4 cyclic
  twists, power drops — `experiment-designer` to recompute against the realized cyclic-twist counts.
- The powered claim is the CONJUNCTION H1∧H2 at the committed sign; each is individually stated with
  its floor.

---

## §8 EXACTNESS (project no-float-in-signal-path rule)

- **Exact int:** all EC arithmetic (`ec_add`, `all_points`, `canonical_generator`), `#E`, `a_p =
  p+1−#E`, twist construction (`g^k`), the six-`a_p`-sum-to-zero check, all permutation/rank counts and
  p-values (integer counts over integer denominators).
- **Ranking without float deciding a verdict:** `t = a_p/2√p` uses √p only as a monotone
  normalization; **ranks are computed by exact integer cross-multiplication** (`a/√p ≷ a'/√p'` ⇔
  `sign`-tracked `a²·p' ≷ a'²·p`), so no verdict-bearing comparison is decided by float precision.
- **Sanctioned float carve-out (analytic size only, no key/scalar bits in the path):** the `p×p` FFT
  producing `|U|`, the trig factor `e_n(·)`. Justification identical to the scaling run (§8 there):
  magnitudes of an analytic sum, error `≤1e-12 ≪ δ ≈ 1e-3`, common-mode-cancelling between char and
  null. complex128 only (no complex64 — float32 round-off ~1e-3 ≈ δ).
- `check_no_float.sh` must pass on the invariant/statistic module before any verdict.

---

## §9 PRE-COMMITTED OUTCOME TABLE

Filled in before the run. Every row is a positive result naming what the scatter is or is not. No row
licenses an ECDLP/extraction/security statement, a mechanism claim (that is the row-budget thread), or
the words *generic / benign / no structure / at the floor*.

| # | Outcome | Conclusion reported |
|---|---|---|
| **A1** | H1 fires (`Z_within > 3`, positive) **AND** H2 fires (OOS ρ>0, p<0.01) | **CONFIRMED: the deficit's prime-to-prime scatter is (at least partly) the signed Frobenius trace `a_p`, p-confound removed.** Report `Z_within`, per-twist δ vs `a_p`, OOS ρ, and the isotonic shape. Name the residual scatter after removing `t` as the NEXT object (is the remainder a further invariant, or the row-budget mechanism's signature?). This reframes level-2 of the scaling run: `D(p)` is not smooth in p because it is smooth in `a_p`, which is not smooth in p. |
| **A2** | H1 fires, H2 null-but-`[UNDERPOWERED]` | within-p (p-controlled) evidence that `a_p` drives δ, not yet corroborated between-p. Report H1 as the finding; H2 needs more OOS primes. Do NOT claim CONFIRMED. |
| **A3** | H1 null, H2 fires | between-p correlation with `t` that does NOT survive the p-controlled test ⇒ attributed to a **p-covariate co-varying with `a_p`**, not to `a_p`. Report both; name what p-covariate (log p residual, |S|) as the candidate; `a_p`-as-driver is NOT supported. |
| **A4** | H1 null AND H2 null (both adequately powered) | **H0: the scatter does not compress to `a_p` at this scope.** Report the power floors (H2 ρ-sensitivity, H1 realized twist counts). Scoped null; the scatter remains real and unexplained by `a_p`; tertiary invariants and the mechanism thread remain open. Not a closure of "arithmetic structure." |
| **A5** | Tautology guard fails (δ ≈ affine image of `a_p` to `≤SE_δ`, and a definitional link is found) | Report the definitional link (e.g. `mu` or `|S|`-normalization carrying `n`); the "correlation" is bookkeeping, not structure. A negative-but-important result: it names a readout artifact. |
| **A6** | Any of P1–P4 fails | corresponding arm reports "planted/negative control did not behave; result uninformative"; no verdict. |
| **A7** | Tertiary: after A1, a secondary invariant (M from `4p=L²+27M²`, `v₂(n−1)`, `n mod 9`, `p mod 12`) survives Holm | reported as an ADDITIONAL exploratory handle requiring its own prereg; never folded into the A1 verdict. |

**Effect-in-an-unprojected-covariate clause (mandatory).** If both H1 and H2 come back null, the run
must NOT report "the scatter is noise." It must report: (i) the confirmed real spread (≥10×`SE_δ`) with
its scope; (ii) the residual after the best isotonic `t`-fit, so the unexplained fraction is a number;
(iii) an explicit list of invariants not tested (higher-degree Frobenius data, `a_p mod ℓ`, twist-class
of 7, class-number-related data of the ring of definition), which are the next candidates, not
absences.

**Output type, pre-committed:** a characterization plus its power number and §0 scope. Never a verdict
about ECDLP, extraction, or security; never a mechanism claim.
