# ⊘ SCOPE-WITHDRAWN — CORRECTION — the E3 curve-swap establishes a key-set × curve INTERACTION

> ## STATUS 2026-07-31: the LOGIC of §1–§2 stands; the CONCLUSION and the §5 programme are WITHDRAWN as out of scope.
>
> **What stands (§1–§2, mechanical):** in a two-arm design where both arms share the same 82 keys
> and the same matched null, a property of the curve *alone* is present in both arms and **cancels
> in the contrast**, so it cannot produce a 98.4th percentile. The predecessor's headline
> *"curve fingerprint, not key fingerprint"* does not follow from its own design. That is arithmetic
> and it is unaffected by anything below.
>
> **What is withdrawn:** the conclusion I drew from it — that the interaction's *key-set half* "is
> the component a leakage channel is made of" — and the entire §5 control programme.
>
> **Why.** `E₃`'s null is drawn from `constructed_keys_1to160_100k.csv`, a **known-MT19937 pool**.
> The estimand of every arm is *"do the real puzzle integers differ from a known generator's
> output?"* — the generation mechanism, out of scope
> (`btc_puzzle_investigation/CLAUDE.md` Scope; `feedback_no_prng_generation_side_2026_07_14`).
> Varying the curve changes the instrument, not the object. **And #135 is unsolved: no statistic on
> solved keys transfers to it except through a generation model.**
>
> So this file corrected a real inference error inside a line of work that should not be pursued.
> **The correction was right and the direction it pointed was out of bounds** — §3's *"a structural
> reason to pursue it"* is withdrawn outright, and §5's controls (`j=1728`, second `j=0` prime,
> group-law E₃) are withdrawn with it. `PREREG_e3_twist_and_cm_controls_v1.md`, which acted on §5,
> is **WITHDRAWN before any run**; its gate was killed before producing an artifact.
>
> **The tell, recorded for reuse:** *if the matched null is drawn from a generator pool, the test is
> a generator test, whatever the instrument.* **Check the null's provenance before the curve's.**

---

*Original text retained below. Read §1–§2 for the mechanical point; do not act on §3 or §5.*

# CORRECTION — the E3 curve-swap establishes a key-set × curve INTERACTION, not "curve fingerprint, not key fingerprint"

**Date:** 2026-07-31. **Target:** `RESULT_diffset_cubic_cmvanishing_v1.md` — its headline, its
Interpretation section, and its *"Rules out"* clause. **Nothing in its measurements is corrected;**
the numbers stand and are not in question. What is corrected is the **inference drawn from the
two-arm design**.

**Direction of the correction:** it *widens* what the result leaves open. Per
`btc_puzzle_investigation/CLAUDE.md`, the burden is on the closure, and the sentence corrected here
is a closure.

---

## 1. The design, and what a two-arm contrast can carry

Both arms use **the same 82 real keys** and **the same bit-length-matched null** (82-subsets of the
100k known-MT19937 pool). Only the curve changes.

| arm | curve | real-82 `E₃` | null mean | pctile | `p` |
|---|---|---|---|---|---|
| secp | `j=0`, CM | 13125 | 3274 | 98.4th | 0.033 |
| `E'` | `j≠0`, non-CM | 3711 | 3349 | 67.1st | 0.660 |

Each arm's statistic is a **contrast between real keys and matched-random keys, through one curve**.

> **A property of the curve alone is present in BOTH the real and the null arm and therefore CANCELS
> in the contrast.** It cannot produce a 98.4th percentile on secp.

## 2. What is therefore corrected

The file's headline reads *"The secp anomaly is a `j=0` curve fingerprint, not a `d`-fingerprint"*,
its Interpretation repeats *"a curve fingerprint, not a key fingerprint"*, and its **Rules out**
clause states *"a `d`-structural reading of the E3 anomaly … The PRNG-fingerprint / puzzle-generator
hypothesis is not supported."*

**A pure curve fingerprint is not what either arm measures.** What the pair establishes is:

> **The real 82 keys differ from bit-length-matched random keys in a way that is visible through
> secp's map `d ↦ X` and not through `E'`'s — i.e. a KEY-SET × CURVE INTERACTION, whose key-set half
> is the component a leakage channel is made of.**

The file's own body says exactly this — *"a property of the interaction between the `d`-set's band
structure and secp's `j=0` endomorphism"* — so the correction is to the **headline and the Rules-out
clause**, which are stronger than the body and stronger than the design.

**What the `E'` arm does correctly rule out:** a **curve-independent** `d`-structural reading — the
82 keys do not carry cubic-residue structure that would make `E₃` anomalous *through any curve*.
A **CM-mediated** `d`-structural reading is untouched, and is what the data points at.

**Error class:** a null in one arm read as closing the hypothesis the *other* arm raised, when the
two arms differ in the curve and share the keys. It is the closure-grade failure named in
`feedback_negative_bias_enlarge_nulls_2026_07_17` (a scoped null enlarged to a closure), and the
scope-widening in `feedback_scope_negatives_tightly_2026_07_10`.

## 3. Why this matters more than the size of the effect suggests

`ANALYSIS_correlation_hierarchy_weil_closure_v1.md` §2 shows that every fixed-shift correlation of a
curve readout of every fixed order is `O(k√p)` by Weil, uniformly. §3.2 records the boundary of that
closure: Weil bounds **complete** sums, and for a restricted sum the completion cost makes the bound
vacuous once the index range falls below `≈ √p`.

**`E₃` is an incomplete sum** — over the 3321 pairwise differences, not over `E(F_p)`. Its complete
analogue is Deligne-bounded and carries nothing. So the E3 observation sits in **precisely the regime
the closure cannot reach**, which is a structural reason to pursue it, independent of any lens. This
is a property of how the statistic is built; no claim about any key set is involved.

*(An earlier revision cited a bit-length property of the solved key corpus here. Retracted — out of
scope, and wrong in direction; see that file's §4.)*

## 4. Confound the original design does not name

`E'` has `n' ≈ 2^{180}` against secp's `n ≈ 2^{256}`, so the two point sets have very different
densities in `F_P` (`≈ 2^{−76}`). The arms differ in **two** ways, not one: CM, and density. Likely
second-order for a statistic on 3321 differences, but unnamed.

## 5. The controls that would settle it — none blocked by the `(0,0)` obstruction

**`E₃` requires no prime group order**, so the 2-torsion fact that empties the `j=1728` arm of
`PREREG_jclass_120deg_discriminator_v2.md` (`(0,0)` is always on `y² = x³+Ax`) **does not apply
here**. All three controls below are cheap and available:

1. **`j = 1728` (CM by `ℤ[i]`, `μ₄`) at secp's `p`, near-prime order.** The current design conflates
   *"`μ₃`/cubic"* with *"CM at all"*: `E'` is non-CM, so a positive on secp is consistent with either.
   `j=1728` has CM and extra automorphisms but the **wrong** one. If `E₃` fires on `j=0` and not on
   `j=1728`, the effect is specifically cubic. Choosing near-prime order also removes §4's density
   confound for free. **This is the discriminator the current pair lacks.**
2. **A second `j=0` curve over a different prime**, same 82 keys — does the effect track `j=0`, or
   secp's particular `p`?
3. **Group-law `E₃`** (`χ₃(x(P_i − P_j))`, Frontier #29) — the CM endomorphism's native operation,
   a different subspace from the field difference. Relevant because `RESULT_spectral_decomp_v1.md`
   found secp's excess confined to the all-ones mode with the orthogonal modes *quieter* than random
   (6.5th pctile) — a rank-1 excess with compensating suppression, which is a constraint signature
   rather than noise.

**Power ceiling, stated so this is not over-sold.** `N = 82` is the entire available sample and
cannot grow. `p ≈ 0.033` will not become strong on this statistic under any number of repetitions.
Progress requires a statistic extracting more from the *same* 82 keys — triples
(`C(82,3) = 88,560`), the group-law object, or band-localized structure — not more runs of `E₃`.

## 6. What this correction does NOT claim

No signal in the real keys is asserted here. The secp arm is `p ≈ 0.033`, **Bonferroni-non-significant
at the family level**, exactly as the original file states. `RESULT_spectral_decomp_v1.md` further
bounds any coherent mode at `≥ 24%` of the key set in either cell. This correction changes **what the
`E'` null licenses**, not what the secp arm shows.
