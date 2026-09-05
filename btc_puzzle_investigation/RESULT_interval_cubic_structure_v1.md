# RESULT — interval confinement of `d` leaves no cubic signature in `x([d]G)` at the tested power

**Executes:** `PREREG_interval_cubic_structure_v1.md`, freeze SHA-256
`8bea62ab67857b0b7aafecac139e8e3fa1f8477bd0442f261ead94193cb4045d`.
**Script:** `interval_cubic_structure_v1.py`. **Date:** 2026-07-31.

> `[EXPLORATORY — user-authorised gate relaxation, no `experiment-designer` sign-off]`.
> **No grade moves on any number here** until a gated replication runs.

**Constructed scalars only. No puzzle keys. No generator pool anywhere in the design.** The object
is the curve map `d ↦ x([d]G)` restricted to an interval — a property of scalar multiplication on
secp256k1 at its own prime, not of how any integer was chosen.

---

## 1. Headline

> **`[EMPIRICAL — bounded magnitude, powered, controls fire]`** Confining `d` to
> `[2^{k−1}, 2^k)` produces **no cubic-class concentration in the pairwise differences of
> `x([d]G)` above a ≈7.7% single-class excess**, at `k ∈ {40, 64, 96, 128, 135, 160, 200}`,
> `M = 80`, `R = 1000`, at secp256k1's own `p`.

**This is a magnitude, not a closure.** `E₃` reads only the *marginal cubic-class counts of the
pairwise difference multiset*. It is blind by construction to phase, to orientation-odd channels,
to joint/triple objects, and to any structure in a subspace it does not project onto. Nothing
below licenses a statement about those.

## 2. Controls — all three behaved, and one is load-bearing

| control | result |
|---|---|
| **C-PLANT** — difference-set cubic bias, greedy over real curve points | classes `[1395, 897, 868]`, `E₃ = 263287`, **100.0 pctile — FIRES** |
| **C-GLV** — `β`-closed set (`β³ ≡ 1 mod p`), forced to exactly equal classes | classes **`[1001, 1001, 1001]`, `E₃ = 0`** — exact |
| **C-NEG** — `d` uniform in `[1, n)`, i.e. drawn from the null's own distribution | `E₃ = 1417`, **35.6 pctile — quiet** |

**C-GLV is the strongest evidence the instrument is reading the intended object.** A set closed
under `x ↦ βx` has its difference multiset closed under multiplication by `β`, and
`1 + χ₃(β) + χ₃(β)² = 0`, so the three classes are *forced* exactly equal. They came out exactly
equal — **independently reproducing the forcing theorem of
`CORRECTION_v32_mu3_diffset_controls_v2.md` §2 through a separate code path.**

**C-NEG is exactly matched, and this is why:** secp has **cofactor 1**, so every point of `E(F_P)`
lies in the prime-order group. The null pool is built by sampling `x` until `x³+7` is a QR — **no
scalar multiplication at all** — so "uniform random curve point" = "uniform random group element" =
"`[d]G` for `d` uniform in `[1,n)`". The null cannot inherit a property of the scalar map.

### ★ C-PLANT v1 DID NOT FIRE, and the failure is recorded rather than overwritten

The first plant selected `x` with `χ₃(x) = 0` and scored **31.6 pctile — F-VOID fired and no arm
number was read.** The defect: `E₃` measures the cubic class of `x_i − x_j`, and forcing every `x`
into one class says nothing about the *differences*. **A control aimed at the wrong object** — the
"trace the object, not the tag" failure named in `btc_puzzle_investigation/CLAUDE.md`, committed
inside the control built to catch it. The pre-committed F-VOID rule caught it before any arm was
read, which is the only reason it did not silently become a null.

## 3. Arms — all null

`d` uniform in `[2^{k−1}, 2^k)`, `M = 80` points, `C(80,2) = 3160` pairs per arm.

| `k` | classes | `E₃` | pctile | verdict |
|---|---|---|---|---|
| 40 | `[1012, 1078, 1070]` | 3892 | 70.2 | null |
| 64 | `[1076, 1058, 1026]` | 1924 | 44.0 | null |
| 96 | `[1074, 1063, 1023]` | 2161 | 48.0 | null |
| 128 | `[1029, 1100, 1031]` | 4903 | 79.5 | null |
| **135** | `[1076, 1065, 1019]` | 2743 | 55.7 | null |
| 160 | `[1056, 1038, 1066]` | 604 | 18.7 | null |
| 200 | `[1065, 1036, 1059]` | 703 | 20.1 | null |

Null distribution: median 2281, 95th 9649, 99th 14911, max 22876. **No arm reaches the 95th.**
Pre-committed rule: fire at ≥99th, null at <95th, indeterminate between. **Outcome: F-NULL.**

`k = 135` is one arm of seven and is reported with the rest; it holds no special status in this
design and its value (55.7 pctile) is unremarkable within the set.

## 4. POWER and SCOPE — the part that carries the meaning

**Minimum detectable effect.** With `T = 3160` pairs, a single-class excess `δ` over `T/3 = 1053.3`
gives `E₃ = 9δ²/4`. Firing at the 99th percentile (`E₃ = 14911`) requires `δ ≈ 81`, i.e. a
**≈7.7% excess in one cubic class**. The plant achieved ≈32% and fired at 100.0.

> **SCOPE: this detects a ≳7.7% single-class excess at `M = 80`. It is BLIND below that.**

**`M` is limited by compute, not by sample.** `C(M,2)` modular exponentiations dominate; `M` and `R`
can be raised arbitrarily because the scalars are constructed. `δ` scales like `√(C(M,2))`, so the
detectable excess falls like `1/M`: `M = 400` would reach ≈1.5%, `M = 2000` ≈0.3%. **A design built
on a fixed set of keys cannot do this** — which is the substantive reason this framing replaces the
`E₃`-on-82-keys line (`PREREG_e3_twist_and_cm_controls_v1.md`, WITHDRAWN as generation-side).

**Not tested here:** other readouts (`χ₂`, `χ₆`, sextant), the group-law difference `x(P_i − P_j)`
rather than the field difference, phase structure, intervals not of the form `[2^{k−1}, 2^k)`,
non-uniform sampling within an interval, and `M > 80`.

## 5. Why this regime was chosen

`ANALYSIS_correlation_hierarchy_weil_closure_v1.md` §2: complete character sums of bounded-degree
readouts over `E(F_p)` are `O(k√p)` — closed. §3.2: completing an **interval** sum costs `log p`,
and the bound `O(√p log p)` exceeds `|I|` once `|I| ≲ √p`, at which point it is vacuous.
**Incomplete sums are the one regime the closure does not reach**, and constructed scalars sample
them at unlimited `N`. This run is a first, low-power pass through that regime; the natural
continuation is larger `M` (the detectable excess falls like `1/M`) and the other readouts.

## 6. Deviations

1. **C-PLANT rebuilt after v1 failed** (§2). v1 is recorded, not deleted. The rebuilt plant selects
   from the null pool rather than from a scalar interval, so it exercises the readout and statistic
   path end to end but **not** point generation — stated as a scope limit of the control.
2. **C-GLV added** after the freeze, as an additional forced-value instrument check. It can only
   tighten the instrument claim, and its expected value is forced (not fitted).
