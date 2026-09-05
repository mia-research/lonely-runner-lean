# The band denominator `k_den` has a φ level-set law — verified exactly, and derivable (v1, 2026-07-23)

**Spec:** `PREREG_kden_ramanujan_comb_v1.md` (frozen before any level set, count, or endpoint table
was computed). **Deviations:** `PREREG_kden_ramanujan_comb_v1_DEVIATIONS.md` (W1-plant fix; H3 not
run). **Script:** `kden_ramanujan_comb_v1.py`. **Run:** `kden_ramanujan_run_v1.out`.
**Endpoint tables + hashes:** `endpoints_*.tsv`, `kden_endpoint_hashes.txt`.

---

## 1. Result

For the band best-approximation denominator
`k_den(off; A, M) = argmin_{1≤den≤M} |den·off − round(den·off/A)·A|` on `off ∈ [0, A)`:

**HYP-G — the level set `L_q = {off : k_den(off) = q}` is exactly the disjoint union of `φ(q)`
intervals of `ℤ/A`, one centred on each fraction `j/q` with `gcd(j,q) = 1`.**

`[VERIFIED EXACTLY — and derivable]` over the 8 pre-committed out-of-sample configurations:

| config | bexp | A | M | M type | predicted intervals | Σφ(q) | mismatch (interior / boundary) |
|---|---|---|---|---|---|---|---|
| W1 | 17 | 65536 | 31 | prime | 308 | 308 | 0 / 0 |
| W2 | 17 | 65536 | 36 | highly composite | 396 | 396 | 0 / 0 |
| W3 | 19 | 262144 | 41 | prime | 530 | 530 | 0 / 0 |
| W4 | 19 | 262144 | 60 | highly composite | 1102 | 1102 | 0 / 0 |
| T1 | 12 | 2048 | 43 | prime | 584 | 584 | 0 / 0 |
| T2 | 12 | 2048 | 45 | composite | 628 | 628 | 0 / 0 |
| T3 | 14 | 8192 | 101 | prime | **3138** | 3144 | 0 / 0 |
| T4 | 14 | 8192 | 100 | highly composite | **3040** | 3044 | 0 / 0 |

```
POOLED  intervals = 9726   mismatch_interior = 0   mismatch_boundary = 0
POOLED  H2a-safe  314/314 informative safe cells        (r_q = φ(q))
POOLED  H2a-tight 127/127 informative deficiency cells  (r_q = r̂_q where r̂_q < φ(q))
```

The predicted intervals **tile the band exactly** — covered offsets = `A` for every configuration,
`675840` offsets in total, with no offset unassigned and none doubly assigned.

**The two tallies land on numbers the spec computed from `φ` alone, before any data:** §2.4 of the
frozen prereg pre-states "**314** informative safe cells" and "**127** informative deficiency cells."
Both were hit exactly. `q ∈ {1,2}` (16 cells) are excluded as forced (`φ = 1` ⇒ one run trivially).

**The T3/T4 rows are the non-trivial half.** There `Σφ(q)` exceeds the interval count (3144 vs 3138;
3044 vs 3040): in the tight regime `A < 2M²` the largest `q` have intervals shorter than one integer
step, so some predicted intervals contain **no** integer offset. §0.4 predicts exactly which, via
`Q_safe = {q ≤ M : q(q+M) ≤ A}`. All **127/127** of those deficiency cells were predicted correctly,
out of sample — the seen configurations S1/S2 sat in this regime, S3 did not, and the prediction was
frozen before any of C was computed.

## 2. Controls

All three wrong-prediction plants fire on every configuration (§4.1); the comparator can report
mismatch, including endpoint-level mismatch:

| plant | what it gets wrong | mismatch range over C |
|---|---|---|
| W1 (all `j`, no coprimality) | count: `q` intervals not `φ(q)` | 481 … 63406 |
| W2 (centres at `(2j+1)/2q`) | centres | 2048 … 262144 (total) |
| W3 (half widths) | **endpoints only**, centres correct | 1032 … 131050 |

W3 firing is what makes H2b stronger than a count check: the comparator is sensitive to endpoint
positions, not merely to which centres exist.

**Ordering was enforced.** For each configuration `predict_levelsets(A, M)` derives endpoints in
closed form from `(A, M, q, j)` only — it never minimises over `d` for a given `off` — writes
`endpoints_<id>.tsv`, and records its SHA-256 **before** `k_den` is computed. This is the §0.3 T-1
anti-tautology gate: without it, "agreement" would measure code equivalence.

## 3. What this is, and what it is not

**It is not a discovery.** §0.4 of the prereg, written before the run, derives the containment
direction from Dirichlet's theorem plus a three-distance argument: any `off` with `k_den = q`
satisfies `‖qθ‖ ≤ 1/(M+1)`, hence lies within `1/(q(M+1))` of some `j/q`; and if `gcd(j,q) = g > 1`
then `q/g` wins there. The honest grade is **`[VERIFIED + derivable]`** — verified exactly at 8 fresh
configurations, and following from a stated argument. The spec required this wording in advance.

The coprimality filter is not an assumption imposed on the geometry — it falls out of it. This
surfaced through a control failure: the W1-plant initially could not fire, because at a non-primitive
centre some `d ≤ M` gives `u_d = (d·j) mod q = 0`, collapsing the derived half-width to zero. The
non-primitive intervals are *empty by construction*. That mechanism is precisely why the count is
`φ(q)` and not `q` (see DEVIATIONS D1).

**Scope (§5.1), inherited by every number above.** `bexp ∈ {12,14,17,19}`;
`M ∈ {31,36,41,43,45,60,100,101}`; `A` a power of two; `A/M²` spanning `0.80` (T3) to `156` (W3),
i.e. both the tight regime `A < 2M²` (T-block, where the deficiency bites) and the wide regime
(W-block). Not covered: `M > 101`, non-power-of-two `A`, `A/M² > 156`.

**A scope correction to the prior result.** `lift_band_joint_findings_v1.md` Part 2 reported the
`k_den` low-frequency excess as "growing with curve size" across three curves
(`n = 2089, 8293, 33151`). `k_den(off; A, M)` **depends only on `(off, A, M)` — no elliptic curve
enters.** The curve appeared there only through the constraint `2A ≤ n`, and `bexp`, `M` and `n` moved
together, so that trend was three-way confounded. The present design crosses `bexp` and `M`
deliberately. This corrects the axis on which the prior trend should be read; it does not refute the
excess itself, which is untested here (H3 not run).

**No leakage or ECDLP content.** `k_den` is a function of the band offset alone. A law describing it
says nothing about recovering `d`, and nothing here touches the curve, the lift, `derr`, or the
`d`-side. Per §9, no sentence in this document may be read outside its `(bexp, M)` configuration.

## 4. Open — H3 not run

The spectral arm is **not executed** (DEVIATIONS D2). Under Branch A of the outcome table H3 is
characterization-only regardless of result — given the exact geometry, spectral quantities are
derived properties of a determined step function, not independent evidence. But nothing may yet be
said about:

- whether the **equal-width Ramanujan factorization** `Σ_q q·Ŵ(w̄_q,f)·c_q(f)` governs the spectrum
  (HYP-S — *not* forced by HYP-G, §0.3 F-1);
- the observed **`|f| = 12/24/24` top mode** and whether above-floor modes concentrate at highly
  composite `f`;
- the pre-committed **`M = 100` vs `M = 101`** contrast, which decides whether the comb depends on
  `M` only through the cutoff or whether `M`'s own factorization enters.

That contrast is the sharpest thing this design can still deliver, and it is untouched by today's
result.

*Grade legend: PROVED · VERIFIED (exact/numeric at scale) · EMPIRICAL (scoped, controls fired) ·
HYPOTHESIS · CITED.*
