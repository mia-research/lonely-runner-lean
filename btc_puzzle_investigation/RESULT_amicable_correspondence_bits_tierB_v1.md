# RESULT — Amicable-partner correspondence, Tier B graded arm + owed plants (v1)

**Spec:** `PREREG_amicable_correspondence_bits_v3.md`, deviations D1–D8. **Companion:**
`RESULT_amicable_correspondence_bits_tierA_v1.md` (exact arm, A2-1, A2-2).
**Code:** `amicable_correspondence_tierB_v1.py`. **Raw:** `amicable_tierB_results_20000.json`,
`amicable_tierB_run_v1.log`. **Date:** 2026-07-23.

> ## TIER B LINE — quote verbatim beside every number below
> Same rule with `p < 20000`: **21 amicable 2-cycles × 2 orientations = 42 curves**, 42 matched
> controls, `Σn = 6.50 × 10⁵`, `max n = 19687`, divisor cells per unit 4 to 57. Contrast floor
> **0.333**. Max `p` is **14.25 bits**; secp is **256 bits**. This run spans none of that gap.

---

## 1. Controls — all fire; the arm has measured power

| control | requirement (§4) | result |
|---|---|---|
| **P2** graded plant | must fire; smallest clearing `ε` **is** `e_min(n)` | **fires on 84/84 curves, 0 failures** |
| **B1** (`β := 1`) | descent holds on every non-collision `x` | 42/42 both arms — **but see §1a: cannot fail** |
| **B2** (random mult., order > 3) | agreement exactly its forced no-wrap set, zero unforced | 42/42 both arms — **but see §1a: cannot fail** |
| **B3** (identity map, same law both sides) | support exactly `0` (only `O`) | **42/42 amicable, 42/42 control** |
| **B4** (random bijection) | support full to sampling resolution | **DEFECTIVE AS CODED — see §4a** |

**Measured `e_min(n)` — the detection floor every null below must quote:**

| `e_min` | 0.02 | 0.05 | 0.20 |
|---|---|---|---|
| amicable curves | 35 | 6 | 1 |
| control curves | 32 | 8 | 2 (at 0.10) |

Worst amicable floor is `e_min = 0.20` at `p = 79` (`n = 67`, the smallest unit, 4 divisor cells);
35 of 42 curves reach `e_min = 0.02`. Per-curve table in the raw JSON.

### 1a. B1/B2 do NOT validate A2-2 — both are instances of one forced identity

These two plants were owed by §4 and were not run in the Tier A pass. They were run here and both
behave on 84/84 curves. **That does not validate A2-2, because neither plant can fail.**

For **every** multiplier `m`, agreement equals the no-wrap set `{x : mx < p}` exactly — a theorem, not
a measurement (proof and exhaustive verification over all `p−1` multipliers on four curves: see
`RESULT_amicable_correspondence_bits_tierA_v1.md` §3, A2-2 reclassification box). `B1` is that identity
at `m = 1` (full agreement); `B2` is it at a generic `m` (its own no-wrap set). A two-sided control
requires one side that *could* come out wrong; here neither can.

**Consequence.** A2-2's registered question — does the μ₆/GLV action descend affinely through the legal
reduction — is **not answered**, §9 cell 14 is **not entered**, and the statistic needs a non-forced
replacement under a new pre-registration. The Tier A arithmetic is unaffected and remains correct.

**This does not bear on the ARM-A arms.** P1, P2 and the `Γ*`/graded machinery are independent of A2-2;
P1's plant recovers a *planted* `Γ_k` that is genuinely absent from unplanted data, and P2's `e_min`
ladder is measured against the same M1 null the real statistic uses. Their firing is informative.

---

## 2. ARM-A graded arm (§2b) — `z_max` vs 199 M1 replicates, exact integer rank

| feature | amicable: significant at `α=0.01` | control | min rank (amic) | median rank (amic) |
|---|---|---|---|---|
| `ΦA` | **0 / 42** | 1 / 42 | 5/200 | 83/200 |
| `ΦB` | **0 / 42** | 1 / 42 | 5/200 | 89/200 |
| `ΦC` | **0 / 42** | 1 / 42 | 3/200 | 125/200 |
| `ΦD` | **0 / 42** | 0 / 42 | 3/200 | 41/200 |

At `α = 0.01` over 42 curves the chance expectation is ≈ 0.42 hits per feature; the control's
1/42 on three features sits at that level and is not named. **On the amicable arm, all 21 2-cycles
(42 curves, both orientation strata) are within the M1 null on all four features.**

---

## 3. §9 cell 5 is now reached — scoped null with power

Tier A gave the exact arm at forced value everywhere with P1 firing on 432/432 curves and all gates
clean. Tier B gives the graded arm within the M1 null on **21/21** 2-cycles with P2 firing on 84/84.
That is every condition of cell 5. Its mandatory statement form, with the measured floor filled in:

> Among the 4 frozen partner-side features, on `E_7/F_p` for the 108 amicable 2-cycles with
> `p < 200000` (both orientations), **no symmetry beyond `μ₆`-forced was detected exactly**; and on
> the 21 Tier-B units, **none approximately above `ε = e_min(n)`**, measured per curve as
> `e_min = 0.02` (35 curves), `0.05` (6), `0.20` (1).

**Followed verbatim, as §7 requires:**

> **What this design cannot falsify, stated now:** (i) features outside the frozen §2 list; (ii) effects
> below the measured `e_min` (ARM-A) or below 0.0079 support resolution (A2-3); (iii) effects appearing
> only at `p ≫ 200000`; (iv) non-group-structured fibre patterns that are neither exact `Γ_k`-orbits nor
> `t_k`-approximate — partially covered by the reported fibre-size multiset, by neither statistic.

**This is not a closure of the amicable channel and may not be written as one.** Per the standing
project stance, an empirical null is a scoped fact about the tested statistic at the tested scale; only
a rigorous analytical proof closes an avenue.

---

## 4. A2-3 is VOID as specified — vacuous construction, not instrument failure

**The statistic has no data to operate on, on any curve in the frame.**

A2-3 measures the support of `δ_ρ(P,Q) := ρ(P+Q) ⊖ (ρ(P) ⊕ ρ(Q))` with `⊕` the `Ẽ(F_n)` group law,
`⊥`-tagged when an operand is off-curve. But `ρ(P) = (x mod n, y mod n)` lies on `Ẽ(F_n)` only when
`ȳ² ≡ x̄³ + 7 (mod n)` holds by coincidence — a rate of order `c/n`:

| | `ρ(P)` on `Ẽ(F_n)` | usable pairs |
|---|---|---|
| amicable | **42 / 325,686** | **0** |
| control | **37 / 324,504** | **0** |

A2-3 requires **three** simultaneous on-curve conditions (`P`, `Q`, `P+Q`), so usable pairs occur at
rate ~`(c/n)³`. Zero were obtained — including under **full enumeration** of all `(n−1)²` pairs for
`n ≤ 1000` (933,156 pairs at `p=907`, all `⊥`).

**This is not §9 cell 17 (plant misbehaviour): the B3 plant fires correctly on 42/42 curves**, so the
instrument works. The construction itself is empty. Per the design rule that an unspecifiable statistic
is reported rather than patched at run time, A2-3 yields **no number in either direction** and §9 cells
15/16 are **not entered**. The gap F4 leaves open — how far the legal reduction is from intertwining
the two group laws — therefore remains **unmeasured**, and needs a reformulated statistic under a new
pre-registration. Candidate direction, not run and not registered: `ρ` composed with a map that lands
on `Ẽ(F_n)` by construction, rather than by coincidence.

---

### 4a. B4 was not reported and does not meet its criterion as coded

`B4` (§4, the second A2-3 plant) appears in neither this document's original tables nor the Tier A
document. As coded it draws `M = 20000` random pairs over a label set of size `nE ≈ n`, so expected
coverage is `1 − e^{−M/nE}`, which falls to **0.634** and is `< 1` on **34/42** amicable curves — it
therefore cannot demonstrate "support full to within the sampling resolution". This is **immaterial to
the A2-3 verdict**, which is void by vacuity (zero usable pairs) regardless of any plant. But `B4` must
not be reused as coded; it needs `M ≫ nE·ln(nE)` or an exact coverage argument.

---

## 5. Implementation defects found and fixed before the run (disclosed)

1. **P2 could not fire as first implemented, for a structural reason.** The plant `Φ^plant_k` is a
   scalar-side construction and M1 swaps only the reduction modulus, so M1 does not touch the plant.
   Injecting the plant into the null replicates as well as the real data left the two identical and the
   positive control could never clear — which would have voided the run under §9 cell 6 for a reason
   unrelated to the curve. The null is now the **unplanted** matched null, the same one the real
   statistic is ranked against.
2. **P2 swept only `k = n−1`**, the degenerate full group (`|image| = 1`). It now sweeps every cell
   `k | (n−1)`, `k > 6`, and reports the smallest clearing `ε` over the sweep.
3. **B2 used an arbitrary threshold.** Replaced with an object-level criterion (zero unforced
   agreement). This made the criterion correct but did not rescue the control — §1a shows the criterion
   is satisfied by construction for every multiplier.
4. **Found after the run, by adversarial audit of the memory draft:** A2-2's forcedness (§1a) and B4's
   coverage defect (§4a). Both are recorded here rather than silently corrected.

`check_no_float.sh` passes on the run script. The §8 carve-out (a) — `z(k)` as a monotone display
re-expression of the integer count `a(k)`, with the exact integer rank deciding — is marked in source
with `# noqa: float` at each site; per-cell Holm ordering uses `Fraction`, not float comparison.

---

## 6. Open after Tier A + Tier B

1. **A2-3's question** — how far the legal reduction is from intertwining the two group laws — remains
   unmeasured; needs a reformulated statistic and a new prereg.
2. **Features outside the frozen §2 list.** A new feature may not be added to this grid and re-run.
3. **`p ≫ 200000`** — exact arm at `10⁶` is pre-declared and contingent on a faster implementation
   (`Σn ≈ 3.94 × 10⁸`), requiring a new DEVIATIONS entry.
4. **Everything above 14.25 / 17.60 bits**, i.e. the whole distance to secp.
