# PREREG — Boundary D: does a CM/GLV cross-representation invariant + the interval
# side-info d∈[0,W) beat the automorphism-accelerated kangaroo (sub-√(W/6))? — v1

**File:** `PREREG_boundary_D_short_interval_CM_invariant_v1.md`  **Date:** 2026-08-13
**Status:** PRE-RUN. Spec written before any op-count data. Exact ℤ/n arithmetic; op-counts are
integers; `s` kept as `Fraction`. No floats in the signal path (the only floats are analytic sizes:
`√(W/6)`, `log₂6`, and the ratio thresholds — no key in the path).
**Object = group-operation COST of recovering `d`**, not a proxy. Not an ECDLP / secp-scale claim.

This spec routes the hypothesis through two DECIDABLE gates FIRST (circularity, collapse), then
— because a rejection on this project must be a measured artifact, not a prose verdict (project
CLAUDE.md: burden of proof is on the closure; surface-and-test, never pre-deflate) — pre-registers
the op-count measurement that would EMPIRICALLY confirm the predicted collapse and would CATCH a
genuine lever if the routing is wrong, anchored by two firing controls proving the instrument has
power.

---

## 0. THE FOUR CANDIDATE INVARIANTS (named now, so nothing is chosen post-hoc)

- **I1 — per-point CM readout of Q as an in-orbit localizer:** `χ₃(x(Q)) ∈ {1,ω,ω²}` (cubic-residue /
  GLV index) and `s = N(eis(x(Q)))/p ∈ [0,¾]` (Eisenstein lift norm), used to pin *where inside its
  interval-orbit* `d` sits.
- **I2 — the GLV vector `(d₁,d₂)` of the secret `d`** (`d ≡ d₁ + d₂λ mod n`, `(d₁,d₂)=(d,0)` reduced
  mod the CM lattice `L={(a,c): a+cλ≡0 mod n}`), claimed to be forced by the interval into a
  publicly-localizable region.
- **I3 — a "public function of Q localizes the GLV region"** cross-representation invariant.
- **I4 — a coupled algorithm** (interval bound × ⟨φ⟩-orbit × CM lattice geometry) with total group
  ops `< √(W/6)`.

---

## 1. CIRCULARITY / DISJOINTNESS CHECK  (decidable; runs first)

Rule: an invariant is admissible only if computable from public `{E,p,n,G,Q,β,λ,W}` WITHOUT `d`.
Search algorithms pass trivially (the win is algorithmic, not a leak). A putative per-point invariant
that secretly needs `d` is circular — a tautology before the run.

- **I1 — PUBLIC (passes circularity), but ALREADY-KNOWN-NULL.** `χ₃(x(Q))`, `s(x(Q))` are computable
  from `Q` alone. But they are *lone-point readouts*, and the setup grants (established) that these
  carry ~0 bits about `d` beyond the orbit label. **Decidable identity confirming this:** the "≈2.58
  bits of orbit/domain info" `= log₂ 6 = log₂ #Aut` (checked: `log₂6 = 2.5849…`). That is EXACTLY the
  orbit label — 6 = #Aut — and nothing more; it is a **constant** (does not grow with `N=log₂W`), so
  it cannot localize `d` *within* an orbit as `W` grows. A fresh test of a lone readout re-tests a
  question the setup already answers. **Arm I1 rejected as already-known.** (It survives only as an
  input to I4, where §2 shows it buys exactly the banked √6.)
- **I2 — CIRCULAR.** Computing `(d₁,d₂)` is a closest-vector reduction of `(d,0)` mod `L`; it takes
  `d` as input. From `Q` alone, producing `(d₁,d₂)` *is* solving the DLP. **Arm I2 rejected as
  circular; stop.**
- **I3 — no independent content.** "A public function of `Q`" is either (a) a per-point readout of
  `Q` ⇒ reduces to **I1** (already-known 0-bit), or (b) a search/algorithm ⇒ reduces to **I4**. There
  is no third kind of public function of one point. **I3 collapses into I1 or I4.**

**Verdict of §1:** the only arm with independent, admissible content is **I4** (an algorithm). I1 is
already-answered; I2 is circular; I3 has no content of its own.

---

## 2. COLLAPSE CHECK  (decidable; the √#Aut question)

Does I4, on inspection, merely re-derive the √6 already in the baseline?

**Decidable geometric facts (verified numerically, exact integer arithmetic, `n=967` toy):**
1. The GLV map `ψ: d ↦ (d₁,d₂)` is a **ℤ-linear bijection** on `[0,n)`; restricted to `[0,W)` it is
   injective with image of cardinality **exactly W** (distinct cosets, since `(d−d',0)∈L ⇔ d≡d' mod n`).
2. The image `ψ([0,W))` is a **line-direction `(1,0)` set**: consecutive `d,d+1` differ by `(1,0)`
   except at rare lattice-cell crossings (measured **95.8%** unit steps), giving ≈`W/√n` short
   segments.
3. The coordinates **do NOT shrink**: median `|d₁|+|d₂| ~ √n` (measured 16 vs `√n=31`). The interval
   RE-PARAMETERIZES the GLV coordinates; it does not make them small.

**Consequence (the collapse).** A bijective linear change of coordinates cannot reduce the
candidate-set cardinality below `W`, hence cannot reduce group-op cost below `Θ(√W)` for a generic
search or `Θ(√(W/6))` after folding by the automorphism group. The group `μ₆ = {±1}·⟨φ⟩` is precisely
Aut(E); folding `[0,W)` by its scalar action (`d ↦ ±λ^k d`) IS the Galbraith–Ruprai acceleration, so
the √6 recovered this way is **exactly the banked factor**. Feeding I1 into I4 supplies exactly
`log₂6` bits (the orbit label, §1) ⇒ exactly the √6. **I4 restricted to {group + φ + I1} COLLAPSES to
√(W/6).**

**To PROCEED, I4 must name a NON-GENERIC quantity returning position-WITHIN-orbit information that
GROWS with `N=log₂W`.** The three offered ingredients do not: I1 is a constant orbit label; I2 is
circular. Within the given ingredients, no such quantity exists — so the collapse-escape is not
realized by anything on offer.

---

## 2b. LOWER-BOUND BLOCK  (the only escape from §2, and why it is checkably absent here)

Beating `√(W/6)` requires **non-generic** structure (Shoup: interval DLP with automorphisms needs
`Ω(√(W/#Aut))` using only the abstract group + Aut). The non-generic escapes for a `j=0` CM curve,
each a **decidable per-instance check**:

- **MOV/Weil-pairing transfer:** needs small embedding degree `k` (`n | p^k−1`). For a random
  `n`-prime `j=0` curve `k` is large ⇒ no subexponential transfer. **Check:** `ord of p in (ℤ/n)*`;
  reject instance if small.
- **SSSA anomalous transfer:** needs trace `t = p+1−n = 1` (`n=p`), making the **FULL** DLP
  polynomial — not an interval-specific lever, and measure-zero. **Check:** `t≠1`. **Excluded by
  scope** (we require non-anomalous `n≠p`); it reappears only as firing control FC1.
- **`j=0` elliptic-log / formal-group lift:** the elliptic-log homomorphism **degenerates on `j=0`
  CM curves** (given caveat). Any interval-lift ingredient that needs a well-behaved elliptic log is
  **unavailable** here — flag it if an arm invokes one; FC1 is the meaningful test of whether such a
  lift can fire at all.

**Verdict of §2b:** the non-generic-transfer escape is, for in-scope instances, **checkably absent**
(large embedding degree, non-anomalous) or is the **out-of-scope anomalous full-DLP case**. The
interval-specific sub-√(W/6) lever has no realization in the given ingredients ⇒ **LOWER-BOUND-BLOCKED**.

---

## 2c. STANDING VERDICT (pre-run, and the reason the run still happens)

By §1–§2b the hypothesis, instantiated with `{χ₃, s, GLV-decomp}`, has **no proceed-able winning
arm**: I2 circular, I1 already-known-null (= the banked orbit label), I4 collapses to √(W/6), the
non-generic escape is checkably absent or out of scope. **Pre-committed prediction: COLLAPSE / SCOPED
NULL.**

This is a decidable routing, not a futility verdict — each rejection is a check or an identity, not
prose. But a prediction of collapse must be **demonstrated by a measurement with a firing control**,
never asserted (project rule: closures carry the PROVED bar; the suppression-bias memory forbids
pre-deflating a lead). §3–§6 pre-register that measurement so (i) the collapse is an artifact, and
(ii) a genuine lever is CAUGHT if the routing above is wrong.

---

## 3. STATISTIC + WORK MODEL (frozen)

- **Cost = group operations** (point add/double), counted exactly as an integer, plus a secondary
  ledger of field ops. No wall-clock.
- **Primary statistic:** `R = median_ops(candidate) / median_ops(baseline)` over `M` matched
  instances at **equal success probability** (both tuned to ≥0.99 recovery; abort-and-retry counted).
- **Secondary statistic (asymptotic tell):** the fitted slope of `log₂(median_ops)` vs `N` across
  ≥3 interval scales. Collapse ⇒ slope `≈ ½`; a genuine lever ⇒ slope `< ½` and `R` decreasing in `N`.
- **"Beats kangaroo"** ≡ `R < 1` strictly, replicated, AND slope `< ½` across scales. A single-scale
  `R<1` is NOT a claim (kangaroo op-count has ~30% relative spread).

Exact-arithmetic note: `χ₃` via exact `(p−1)/3`-power residue in `𝔽_p`; `s = N(eis(x))/p` as
`Fraction`; lattice reduction over ℤ; op-counter is an `int`. Verdict rides the integer op-count and
an exact permutation null on per-instance op-counts (Outcome D), never a float threshold.

---

## 4. MATCHED BASELINE (measured, not assumed)

Implement the **μ₆ automorphism-accelerated interval kangaroo** (Galbraith–Ruprai style: equivalence
classes under `d ↦ ±λ^k d`, distinguished points on class representatives, tame/wild herds sized to
the folded interval `≈ W/6`). **MEASURE** its median op-count on the SAME instances the candidate
runs on. The candidate must beat THIS measured number — never the naive `√W`, and never the analytic
`√(W/6)` (which is only a sanity check on the baseline's own calibration).

---

## 5. FIRING CONTROLS (two; BOTH must fire or the null is uninformative)

- **FC1 — anomalous curve (a real sub-√(W/6) win exists).** A trace-1 curve (`n=p`, `j=0` if
  reachable at scale else any) where SSSA makes interval DLP **polynomial**. The candidate/instrument
  op-count must **crash to polylog(W)**; pass threshold `R_FC1 ≤ W^{-0.3}` (i.e. ops ≪ baseline by an
  exponential factor). Proves the measurement can SEE a genuine sub-√(W/6) win, and exercises the
  `j=0` elliptic-log lift (§2b).
- **FC2 — planted graded leak (known size).** Publish a rigged public oracle encoding the top `t`
  bits of `d` (e.g. `s(x(Q))` engineered to carry `⌊d / 2^{N−t}⌋`, or a side value revealing `t`
  high bits of a GLV coordinate). The residual interval shrinks by `2^t`; op-count must drop by
  `2^{t/2}`. **Pass threshold:** measured `R_FC2 ∈ [2^{-t/2}·0.7, 2^{-t/2}·1.4]` for planted
  `t ∈ {4,8,12}`, monotone in `t`. Proves the instrument resolves a graded win of KNOWN magnitude.

If EITHER firing control fails to fire, the instrument is underpowered at that scale ⇒ **ABSTAIN**
(Outcome C); bank no null; report the power ceiling and the `N`,`M` needed
(`feedback_prereg_abstention_is_the_finding`).

---

## 6. POWER · SCOPE · EXACTNESS · FALSIFICATION · PRE-COMMITMENT

**SCOPE (every reported number inherits this).** `j=0` curves `E: y²=x³+b / 𝔽_p`, `n` prime `≡1 mod
3`, **non-anomalous** (`t=p+1−n ≠ 1`), large embedding degree; three scales `n ≈ 2^40, 2^48, 2^56`;
intervals `W=2^N` with `N ∈ {20, 24, 28}` (`W ≪ n`); `M ≥ 100` matched instances per (scale, N),
`d` drawn uniformly in `[0,W)` with a pinned seed recorded in the run. All ℤ/n exact; `s` as
`Fraction`; op-count integer. Scale banner is TOTAL: `n ≤ 2^56` is ~200 binary orders below the
`2^256` target and has **zero power** against it — this measures the MECHANISM, not the real curve.

**POWER.** Kangaroo op-count relative std ≈ 0.3 ⇒ `M=100` resolves a ≥~15% median shift at one scale.
A genuine asymptotic lever `ops ~ W^{1/2−Δ}` gives `R = √6 · 2^{−NΔ}` (baseline `= 2^{N/2}/√6`):
- `Δ ≳ 0.10`: `R` runs `0.61 → 0.35` over `N=20→28` — clearly `<1` and decreasing ⇒ **robustly
  detected**.
- `Δ ≲ 0.05`: `R` runs `1.22 → 0.93` — not even below baseline at the small scales ⇒ **NOT
  distinguishable from collapse** at this scale/`M`; that exponent gap is the **detection ceiling
  `Δ_min ≈ 0.08`** reported with any null.

**EXACTNESS carve-out.** Only `√(W/6)`, `log₂6`, and the `R`/`Δ` thresholds are floats — analytic
sizes, no key or op-count in the path. Signal path (curve arithmetic, `χ₃`, `s`, GLV reduction, op
counter, permutation null) is int/Fraction. `check_no_float.sh` must pass before the run.

**TAUTOLOGY note.** The op-count comparison is an algorithm benchmark — feature (recovered-`d`
candidate) and target (`d`) are related only through the DLP map, which is the hard direction, so
there is no leakage-tautology. The ONE tautology risk is arm I2 (invariant computed FROM `d`); it is
rejected at §1. No arm in the run uses `d` in the signal path.

**FALSIFICATION (pre-committed).** The hypothesis (a CM/interval cross-representation lever beats
√(W/6)) is FALSIFIED at this scope if `R ≥ 0.9` with slope `≈ ½`, stable across all three scales,
**with FC1 and FC2 having fired**. That is a magnitude bound on THIS mechanism at THIS scale — NOT a
closure of the avenue and NOT an ECDLP statement.

**PRE-COMMITMENT TABLE (decision rule fixed before any data):**

| Outcome | Trigger | Pre-committed conclusion |
|---|---|---|
| **A — COLLAPSE / SCOPED NULL** *(predicted)* | `R∈[0.9,1.1]`, slope `≈½`, stable over 3 scales; FC1+FC2 fired | `[EMPIRICAL — SCOPED NULL]`: the `{χ₃, s, GLV-decomp}` cross-representation gives **no sub-√(W/6) lever** at `n≤2^56`, `N∈{20,24,28}`, `M=100`; ceiling `Δ_min≈0.08`. A BOUND, not a closure; residual info localized to the orbit label (`log₂6` bits) only. Avenue NOT declared dead. |
| **B — LEVER** *(routing wrong)* | `R<1` strictly AND decreasing across ≥3 scales (slope `<½`); FC1+FC2 fired; perm-null on op-count flat | Candidate cross-representation interval lever. FREEZE witnesses + the exact non-generic quantity used; open a replication prereg at the next scale. Do NOT narrate as an ECDLP break here. |
| **C — ABSTENTION** | FC1 or FC2 did not fire | Instrument underpowered; bank NO null; report power ceiling + `N,M` needed. |
| **D — OUT-OF-PROJECTION SUBSPACE** | `R≈1` but per-instance op-count residual correlates (exact permutation p ≤ 0.01) with a CM coordinate we did NOT fold — e.g. a `χ₃`-sector or sextic-twist `χ₂(x³+b)` split of the op-count | Effect may live in a sub-representation not projected onto. Record the sector-split statistic as a **named next probe** (split `Σ = FIELD + CURVE·χ₂` per the `j=0` drill corollary); do NOT report Outcome A. |

Outcome D is mandatory: it prevents reading "`R≈1`" as "no structure." Structure would live in the
symmetry-type / sector split of the op-count, not only in its magnitude.

---

## 7. WHAT THIS SPEC DECIDES

- **Circularity:** I2 circular (needs `d`); I1/I4 public. **PASS** for I4 as an algorithm.
- **Collapse:** I4 on {group + φ + orbit-label} **COLLAPSES to √(W/6)** (bijective re-coordinatization
  + banked μ₆ fold); I1 supplies exactly `log₂6` = the orbit label. Escape needs a non-generic,
  N-growing quantity — **none on offer**; the transfer escape is checkably absent (embedding degree,
  non-anomalous) or out-of-scope anomalous. **Standing prediction: SCOPED NULL / collapse.**
- The run exists to make that prediction a **measured artifact** (Outcome A) with firing controls
  proving power, and to CATCH a lever (Outcome B) or a sub-representation effect (Outcome D) if the
  routing is wrong.
