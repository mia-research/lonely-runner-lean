# PREREG — does a CARRY-PARTITION-guided interval-DLP kangaroo cost fewer group operations than a plain interval kangaroo, and does any reduction GROW with the interval bit-length k? — v1

**File:** `PREREG_t2c_carry_partition_kangaroo_bench_v1.md`  **Date:** 2026-08-26
**Status: SPEC ONLY — no runner has executed; no outcome asserted.**
**Kind:** group-operation-COUNT benchmark (algorithm vs matched baseline), model scale. This is **not** a
statistical-leakage test — but the object is a *reduction/advantage* claim, which is the gate that
requires this pre-registration.
**Prior art it extends / must not re-run:** `RESULT_t2c_range_carry_skew_exact_v1.md` (the exact public
partition `P_k` and the ε_LBE interval map) and `RESULT_curve_island_lambda_folding_v1.md` (the CLOSED
endomorphism-fold — see §0, explicitly NOT what this designs).

---

## §0 SCOPE BANNER

- **Model scale only, zero secp power.** Curves are small enough (`n` prime, ~2³⁰–2⁴⁰) that the interval
  DLP on `I=[2^(k−1),2^k)` is **brute-force solvable**, so the true `d` is known and every group-operation
  count is an **exact integer** with a verified solve. secp256k1's DLP is not solvable; nothing here
  transfers to 2²⁵⁶. This measures the **mechanism** — does the carry partition move the op-count
  *exponent* at model scale — not any secp attack.
- **This is the CARRY-PARTITION variant, which STAYS INSIDE `I`. It is NOT the endomorphism (λ) fold.**
  `RESULT_curve_island_lambda_folding_v1.md` already CLOSED the orbit-identification λ-fold at 2⁵⁸×
  **worse** than plain interval kangaroo, named reason `λI≠I` ⇒ representatives delocalize to n-scale (the
  interval bound `L≪n` is worth more than √6). **The runner MUST NOT canonicalize points by their βx-orbit
  class, MUST NOT identify `d` with `λd`/`λ²d`, and MUST NOT search outside `I`.** All walks/herds/DPs live
  in `I`; the partition only reorders/confines the search within `I`, never folds the interval.
- **The provable ceiling this spec is built around (state it, then test against it).** ε_LBE is a **single
  bit**. Conditioning a search on one bit removes at most 1 bit of location entropy — a **constant factor,
  never exponent movement** (information-theoretic). A **free** oracle for the target's ε cuts the interval
  to the ε-matched sub-region of measure `P_k` or `1−P_k`; the resulting kangaroo op-count factor is
  `≥ P_k^{3/2}+(1−P_k)^{3/2} ≥ 1/√2` (a ≤√2 speedup, **maximal at the balanced bit P_k=½ and SMALLER as
  P_k skews** — concavity of √W). In bits the prior is worth `1−H(P_k)`: ≈0.056 at k=131, ≈0.03 at k=135,
  ≈10⁻⁶ at k≥140 on secp. **No k makes this super-constant.**
- Both the SCOPED NULL (ratio bounded by the constant ceiling) and a RETAINED (ratio shrinks
  super-constantly in k) are pre-committed verbatim in §7/§9. RETAINED contradicts the single-bit bound and
  therefore triggers a mandatory artifact hunt *before* it may be believed.

## §1 OBJECT — the two solvers and the non-circular use of the partition

**Ambient (per model curve).** A j=0/μ₆-CM curve `E:y²=x³+B` over `F_q`, prime order `n`, generator `G`,
endomorphism `(β,λ)` — from `model_curve_infra_v1.build_j0_arm`/`select_j0_prime_order` (`J0Arm(q,B,N,
beta,lam,Gx,Gy)`, `[lam]G=(beta·Gx,Gy)`, `λ³≡1 (mod n)` asserted). Target `P=[d]G`, `d` **uniform** on
`I=[2^(k−1),2^k)⊂[1,n)`.

**The public partition (per curve, per k).** Port `t2c_range_carry_skew_exact_v1`'s `_gauss`/`_rdiv`/`glv`/
`eps`/`rounding_boundaries`/`exact_skew` to arbitrary `(n,λ)`: reduce the GLV lattice `{(x,y):x+λy≡0
(mod n)}` for THIS curve, giving `(a,b)=glv(d)` and `ε_LBE(d)=[(a mod n)+(b mod n)≥n]`. `exact_skew(k)`
returns the exact integer count of `ε=1` and the ordered list of contiguous **runs** `[lo_r,hi_r)` on which
`ε` is constant (endpoint-verified per run). `P_k=#{ε=1}/2^(k−1)` exact. **This map is computed from public
data `(n,λ,I)` only — no secret `d` enters it.**

- **BASELINE (matched, plain interval kangaroo).** Two-herd (tame+wild) distinguished-point interval
  kangaroo confined to the full `I`, in the confined-DP style of `interval_dlp_bench.solve`, re-hosted on
  `model_curve_infra_v1.Curve.add`/`.mul` with **integer** jump sizing via `isqrt` (§8). Op-count = number
  of group operations to the tame–wild collision yielding `d` with `mul(d)·G==P`.
- **VARIANT (carry-partition, PRIOR-GUIDED, non-oracle).** Identical engine, jump set, `K`, DP mask, and
  per-region budget constant `c` as the baseline. The ONLY addition: read the public runs from
  `exact_skew(k)`, group them into the two ε-classes, and search them **in descending order of prior mass**
  (the larger-measure class first), running a kangaroo *confined to each class-region in turn* with
  per-region budget `c·⌊√width⌋`, advancing on budget exhaustion. Op-count = total group ops across all
  regions to the verified solve. Fully specified pre-run; no post-hoc freedom over ordering/budget/regions.

**Non-circular use (load-bearing).** The variant consumes the public **prior/label** of each sub-region,
never the target's ε. It does **not** evaluate `ε(d)` (that is the ORACLE = firing control, §4). For a
target uniform on `I`, the partition is a *labeling*, not a *localizer*: `Pr[d∈R]=|R|/|I|` regardless of
`R`'s ε-label. The variant is a *bet* — search the higher-prior class first — that still pays full cost
when `d` lands in the lower-prior class. Its expected op-count is bounded below by the ORACLE's (§4),
bounded by the §0 ceiling.

## §2 STATISTIC — one, named now; the verdict is its k-trend

Per curve and per k: draw `T` independent trials `(d,seed)` (§6). For each, run BASELINE and VARIANT on the
**same** `(d,P,seed)` (paired). Record integer op-counts `{b_t}`, `{v_t}`.

- **Point statistic (per k):** `R_k = median_t v_t / median_t b_t` — a ratio of two integer order
  statistics, kept as an exact `Fraction`. `R_k<1` ⇒ partition helped; `R_k≥1` ⇒ it did not.
- **VERDICT statistic:** the **k-trend of `log₂ R_k`** across the frozen k-schedule (§6), classified as:
  (1) **CONSTANT/no help:** `R_k≈1` (within noise, §5) at every k; (2) **CONSTANT-factor help:** `R_k=r<1`
  roughly flat, or tracking the ceiling `r≥P_k^{3/2}+(1−P_k)^{3/2}`, no downward drift in k; (3)
  **SUPER-CONSTANT / exponent movement:** `log₂ R_k` decreasing ~linearly in k (`R_k~2^(−αk)`, `α>0`) — the
  only genuine-advantage shape, the one the §0 bound forbids.
  The verdict is which of {1,2,3} the measured `{R_k}` realizes, decided by §7. A pooled/targeted trend
  across the k-schedule is the statistic — **not** a max/min-over-k of `R_k` (a min-over-noisy-ratios is
  downward-biased and would fake shape 2/3).

**Distributions, not instances.** Report the full op-count deciles for BASELINE and VARIANT at each k, plus
`R_k` with a bootstrap CI (integer resample), never a single trial.

## §2R ANTI-CIRCULARITY — exactly what each arm consumes, and that it is public

| Information | Public? | BASELINE | VARIANT | ORACLE (§4 only) |
|---|---|---|---|---|
| `I`, `n`, `λ`, `G`, `B`, `q` | yes | ✓ | ✓ | ✓ |
| curve GLV lattice ⇒ `d↦ε(d)` fn + run list | yes (from n,λ) | ✗ | ✓ (labels/priors only) | ✓ |
| `P_k` + per-region prior mass | yes | ✗ | ✓ | ✓ |
| **`ε(d_target)` — the secret's carry bit** | **NO** (fn of secret d) | ✗ | **✗ (forbidden)** | ✓ |
| the secret `d` | NO | ✗ | ✗ | ✗ |

- The VARIANT is a circularity **fail** iff it evaluates `ε` at the secret `d`, restricts to only the
  target's true region, or uses `d` to pick order. All three forbidden: order fixed by *prior mass*
  (public), every region searched until solve. **Static check (run + log):** the VARIANT source contains no
  `eps(d_target)`/`glv(d_target)` call and no read of the secret before the verified-solve line.
- Distinct from the closed `r=v−w` tautology (feedback 2026-07-14): feature (public partition) and target
  (secret `d`'s location) share **no** construction — the partition is a public fn of `(n,λ)`, the target
  an independent uniform draw.

## §3 MATCHED BASELINE — isolates the partition, not a tuning difference

BASELINE and VARIANT share, byte-for-byte, the same engine: same `Curve.add`/`.mul`, jump-size ladder
(integer, `isqrt`-derived), `K`, DP mask `dp_bits`, walk length, per-region budget `c`, RNG seeding per
trial. ONLY delta: the partition-ordering/confinement wrapper.
- BASELINE = VARIANT run with a **single region = `I`** (trivial partition) ⇒ `R_k` isolates the
  partition's effect; a tuning artifact would move `R_k` off 1 *at k where the partition is trivial*.
  Run-time invariant: at any k with `P_k∈{0,1}` the partition has one region and `R_k≡1` exactly.
- **No re-tuning of the variant.** Jump mean, `K`, `c`, `dp_bits` frozen in the schedule (§6) and shared;
  any per-arm change is a disclosed DEVIATION.
- Report, per k, the **bounding-box width** of each ε-class region vs its measure. If a class's runs are
  interleaved so its bbox ≈ `I`, confinement is mechanically worthless there — a *correct* reason for
  `R_k≈1`, shown not hidden (a mechanism of the null, not a bug).

## §4 FIRING CONTROL — the ORACLE variant MUST fire, or the run is VOID

**Positive control (known effect, known size).** ORACLE = same engine, *given the target's true ε*,
confined to the single contiguous partition **run containing `d`** (width `w_run(d)`, from the public run
list + the oracle's knowledge of which run). Predicted per-trial op-count ≈ `c'·√w_run(d)` vs baseline
`c'·√|I|`, so predicted ratio ≈ `√(w_run(d)/|I|)`; the median over uniform `d` is **exactly precomputable**
from the run-width distribution `exact_skew(k)` returns.
- **Fire condition (every non-trivial-partition k):** measured ORACLE/baseline median ratio matches
  `median_d √(w_run(d)/|I|)` within the §5 noise floor (strong-skew k: runs ≪ `I` ⇒ visible drop; balanced
  k: two-region oracle recovers ≈√2). Secondary coarser oracle confined to the whole ε-matched class
  (measure `P_k`/`1−P_k`) must show ratio ≈ `√(bbox_v/|I|)` where its bbox is sub-`I`.
- **If the ORACLE does not fire** (op-count does not drop by the predicted, exactly-known sqrt-factor), the
  harness/counter/confinement is broken and the entire run is **VOID** — no verdict on the VARIANT. The
  oracle firing proves the counter can *see* a real interval-shrink; only then is a VARIANT null informative.

**Sanity plants:** (a) `P_k∈{0,1}` ⇒ one region ⇒ `R_k≡1` exactly (matched-baseline invariant); (b) an
injected contiguous width-`W/4` sub-interval known to contain `d` ⇒ ratio ≈ ½ (`√(1/4)`) — validates the
confinement counter independent of the partition.

## §5 POWER — trials, noise floor, ceiling reference

- Kangaroo solve-op-count has median ≈ 2–4·√|I| with CV ≈ 0.5–0.7. Paired trials ⇒ log-median-ratio s.d. ≈
  `CV·√(2/T)`.
- `T=1000` paired trials per `(curve,k)` ⇒ noise floor on `R_k` ≈ ±3% (3σ). Resolves any constant-factor
  difference ≥10% at every k, the √2 oracle ceiling (`R=0.707`) at <100 trials, and a super-constant trend
  `R_k~2^(−αk)` (even α=0.02) across a ≥5-point k-schedule.
- **Reference bound:** oracle speedup ≤√2, k-independent up to the `P_k→½` drift; non-oracle variant
  localizes a uniform target by 0 bits ⇒ predicted `R_k≥1`. Any `R_k` **below** the oracle's own `R_k` at
  the same k is impossible (variant cannot beat oracle) and flags a counter bug.
- **Underpowered guard:** where the partition is trivial or bbox ≈ `I` (confinement worthless), that k has
  **structural** zero VARIANT power (not a null); reported as such, never folded into "no effect". The
  k-schedule ensures ≥3 points with a non-trivial, sub-`I`-bbox partition where the VARIANT *could* show an
  effect.

## §6 SCOPE & SCHEDULE (frozen, SHA-256'd pre-run)

- **Curves:** ≥3 j=0/μ₆ prime-order model curves from `select_j0_prime_order(q, exclude_anomalous=True)`,
  `n` prime in bands ~2³⁰, ~2³⁵, ~2⁴⁰ (anomalous trace-1 excluded). Each `(q,B,n,β,λ,G)` frozen + SHA'd.
- **k-schedule (per curve, by RULE):** compute `P_k` exactly via ported `exact_skew` for `k=1..⌈log₂n⌉`.
  Select by pre-committed deterministic rules on public data: `k_strong=argmax_k|P_k−½|`;
  `k_mid=` smallest `k>k_strong` with `|P_k−½|` closest to `1/10`; `k_weak=` largest `k≤⌈log₂n⌉` with
  `|P_k−½|<1/100`; plus two interpolating k's — ≥5 k's per curve.
- **Trials:** `T=1000` paired `(d,seed)` per `(curve,k)`, `d` uniform on `I`, frozen seed list (shared
  BASELINE/VARIANT/ORACLE per trial).
- **Engine params:** `K`, jump mean `⌈√|I|⌉/2` (integer), `dp_bits=⌊k/2⌋−c₀`, budget `c` — frozen per
  schedule, shared across arms.
- **Cost:** each solve ≲ few×2^(k/2); 3 curves × 5 k × 1000 trials × 3 arms ≈ 4.5×10⁴ solves.
- **Frozen artifact** `_SCHEDULE_t2c_carry_partition_v1.json` (SHA'd): curves+`(q,B,n,β,λ,G)`, per-curve
  k-schedule with exact `P_k` and run-width distribution, engine params, seed list.

## §7 FALSIFICATION (written before the run)

- **SCOPED NULL (default form):** `R_k` **bounded by the constant ceiling with NO exponent movement** —
  `log₂ R_k` has no significant negative slope in k, and every `R_k ≥` the ORACLE's `R_k` at that k and
  `≥ P_k^{3/2}+(1−P_k)^{3/2}`. Stated *with the op-count numbers*: the per-k `R_k` table, the flat/positive
  trend slope with CI, the ceiling values `P_k^{3/2}+(1−P_k)^{3/2}` and `1−H(P_k)` bits per k. Reported as:
  *the carry partition gives at most the single-bit constant factor and no advantage growth with interval
  length, at model scale* — a backed, scoped null, not a closure of carry-structure.
- **RETAINED:** `log₂ R_k` **decreases super-constantly** — significant negative slope consistent with
  `R_k~2^(−αk)`, `α>0` (at §5 power). Because this contradicts the single-bit bound (§0), RETAINED does NOT
  promote until a mandatory artifact hunt clears: (i) VARIANT never reads `ε(d_target)` (§2R static check);
  (ii) the trend is not the ε-region bbox coincidentally shrinking with k (report bbox widths); (iii) the
  counter counts group ops identically across arms; (iv) not a censoring/solve-rate artifact (equal solve
  fractions). Only a RETAINED surviving all four, restated as a *characterization* (which region the growth
  lives in), is a finding — never a bare verdict.
- **VOID:** the ORACLE firing control (§4) fails the exactly-predicted sqrt-drop at any non-trivial k ⇒
  counter/confinement broken ⇒ no verdict.

## §8 EXACTNESS

- **Signal path int-only.** Group ops via `model_curve_infra_v1.Curve.add`/`.mul` (exact F_q). ε/partition
  via ported `glv`/`eps`/`exact_skew` (exact `int`/`Fraction`). Op-counts integers; medians integer order
  statistics; `R_k` and trend comparisons `Fraction` cross-products; k-selection compares `|P_k−½|` as
  `Fraction`. `P_k` exact from `exact_skew`.
- **Named carve-out (analytic size only, no key in path):** jump-size *sizing* and per-region *budget* use
  `math.isqrt` (integer floor sqrt) — a solver knob, integer, no float. **The existing
  `kangaroo_jumptune.py`/`kangaroo_tuning.py` `W**0.5`/`int(W**0.5)` float idiom is FORBIDDEN in the runner;
  replace with `isqrt`.** No `/`, `float(...)`, `**0.5`, or `math.sqrt` on any key-derived value.
- **Validation ports (must pass before any trial):** ported `glv`/`eps` reproduce
  `t2c_range_carry_skew_exact_v1.glv`/`eps` on secp `(n,λ)` over 500 random `d`; ported `exact_skew` count =
  brute-force `Σε` on a small model range; every run endpoint-verified via direct `eps`. `check_no_float.sh`
  passes on the runner.

## §9 PRE-COMMITMENT TABLE

| # | Outcome (measured `{R_k}` over the k-schedule) | Reported as |
|---|---|---|
| **A1 — SCOPED NULL** | No negative k-slope in `log₂R_k` (at power); `R_k` bounded by ceiling (≥ oracle `R_k`, ≥ `P_k^{3/2}+(1−P_k)^{3/2}`). | **BOUNDED, no exponent movement.** Carry partition gives at most the single-bit constant factor; a public labeling does not localize a uniform target, so the non-oracle variant shows `R_k≳1`. Report the `R_k` table, flat-slope CI, per-k ceiling numbers. Scoped model-scale null; **not** a closure of ε-structure (which stays live as an oracle-conditioned ≤√2 factor). |
| **A2 — RETAINED (guarded)** | Significant negative k-slope, `R_k~2^(−αk)`, at power, **and all four §7 checks clear.** | **Anomaly — advantage grows with k, contradicting the single-bit bound.** Do NOT declare a speedup. Characterize *where* the growth lives, publish the four-check audit, re-gate (2nd experiment-designer read) before any claim. Fails any check → A3/VOID. |
| **A3 — CONSTANT help** | `R_k=r<1` roughly flat, tracking oracle/ceiling, no drift. | **Constant-factor speedup at the single-bit ceiling**, k-independent. Report `r` vs predicted ceiling; bounded, no exponent movement. |
| **A4 — VOID** | ORACLE firing control fails at any non-trivial k. | Counter/confinement broken; **no verdict**. Fix and re-run. |
| **A5 — structural low-power** | Partitions trivial or bbox ≈ `I` at all k. | No VARIANT power at model scale for this curve set; a scope/power limit, **not** a null. Widen curve/k-schedule. |

**Unprojected clause.** Any null reports (i) the full `R_k` table with CIs and ceiling numbers; (ii) the
oracle-fired reference so the ceiling is a measured number; (iii) untested refinements (larger `n` bands,
finer k, run-level confinement, other CM discriminants). A magnitude is a **size**, not "no structure" —
the ε-channel's oracle-conditioned ≤√2 factor survives every null here.

## §10 OWED GATES

1. **Second `experiment-designer` read OWED before any RETAINED (A2) promotes** past "anomaly under audit".
2. **`compile-diff` OWED** if folded into a master/handover.
3. **`check_no_float.sh` passes** on the runner before the first trial; log the pass.
4. Deviations (variant ordering/budget/region rule, k-selection rule, engine params, trial count after
   freeze) go in `PREREG_t2c_carry_partition_kangaroo_bench_v1_DEVIATIONS.md`, disclosed.

## §11 Files
`t2c_carry_partition_kangaroo_bench_v1.py`; `_SCHEDULE_t2c_carry_partition_v1.json`(+`.sha256`);
`..._v1.log`; `RESULT_t2c_carry_partition_kangaroo_bench_v1.md`; `..._v1_DEVIATIONS.md`.

---

**Provenance.** Pre-registered via the `experiment-designer` gate (context-isolated: baseline kangaroo +
T2c partition + `model_curve_infra` + the λ-fold closure + the single-bit ceiling as isolated context; no
session narrative, no expected outcome). The ceiling math (oracle speedup `P_k^{3/2}+(1−P_k)^{3/2}`,
maximal √2 at balanced P_k, smaller as P_k skews) was independently re-derived in the main session before
persistence. This is SPEC ONLY.
