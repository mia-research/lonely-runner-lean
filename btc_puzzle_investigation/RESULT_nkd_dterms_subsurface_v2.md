# The D-terms sub-surface, mechanism: T=1 is the Dirichlet reciprocal-floor lattice

**Date:** 2026-07-21 · **Scripts:** `nkd_dterms_mechanism_v1.py` (+ v1 machinery). Exact integers.
Supersedes the "next probe" of `RESULT_nkd_dterms_subsurface_v1.md` §4.1 — that probe is now
**resolved**, and its guessed mechanism (**2-adic**) is **corrected** to Dirichlet-generic.

> ## ⚠ SCOPE
> d-side reconstruction geometry, **no leakage / ECDLP claim.** Exact identity + full-fiber
> enumeration + a matched non-power-of-2 control. Fibers: `N∈{26,28}`, `(n,k)∈{(2,1),(3,1)}`.
> Grades: the identity is `[PROVED]` (direct from the recursion) **and** `[VERIFIED]` (identical
> sets on the fibers); the 2-adic correction is `[VERIFIED]` against a matched control.

---

## 1. The exact law — T=1 = reciprocal-floor lattice  `[PROVED + VERIFIED identical sets]`

From the `d_terms` recursion, one greedy step on residual `D>0` gives
`err₁ = D − ⌊lo/⌊lo/D⌋⌋`, so
```
T(D) = 1   ⟺   D = ⌊ lo / ⌊ lo / D ⌋ ⌋            (lo = 2^{N−1})
```
The fixed points of `f(D)=⌊lo/⌊lo/D⌋⌋` are **exactly** the reciprocal-floor set
`{ ⌊lo/q⌋ : q ≥ 1 }` (the Dirichlet hyperbola; `f` is idempotent, image = fixed-point set).
Verified as **identical sets** against direct `d_terms` enumeration:

| N (n,k) | Dmax | \|A₁\| via d_terms | \|A₁\| via ⌊lo/⌊lo/D⌋⌋ | identical? |
|---|---|---|---|---|
| 28 (2,1) | 131 586 | 22 150 | 22 150 | **True** |
| 26 (3,1) | 22 018 | 10 061 | 10 061 | **True** |

**⇒ The low-complexity (T=1) stratum of the (n,k,D) domain is exactly `{ base ± ⌊lo/q⌋ }` — a
closed-form, classical object (the Dirichlet reciprocal lattice), not an empirical set.**

---

## 2. The islands have an EXACT boundary at √lo  `[PROVED + VERIFIED]`

Standard floor fact: for `v ≤ √lo`, `⌊lo/⌊lo/v⌋⌋ = v`, so **the entire block `[1, ⌊√lo⌋]` is T=1**
(one contiguous component). Above `√lo` the reciprocal-floors are spaced `~ lo/q² > 1` apart, hence
**isolated singletons**. Measured (N=28 (2,1), `√lo = 11 585`):

- points `≤ √lo`: **11 585, forming exactly 1 run** (the full block `[1,√lo]`);
- points `> √lo`: 10 565, of which **7 762 are isolated singletons** (rest merge just above √lo);
- **#components = 8 579** (positive side; ×2 for ± ⇒ 17 157 = v1's measured total ✓).

**So the low-complexity islands sit exactly in `(√lo, Dmax]`, and everything below √lo is one solid
continent.** `√lo = 2^{(N−1)/2}` is the exact merge/island boundary a reconstruction algorithm sees:
below it every residual is 1-term; above it only the sparse `⌊lo/q⌋` are.

---

## 3. This EXPLAINS the ≈0.5 clustering (v1 §3)  `[the mechanism]`

v1 found real/ctrl `≈ 0.45–0.68` (< 1, sub-generic). Mechanism: the contiguous block `[1,√lo]`
collapses `~√lo` low-complexity points into **one** component, where a random arrangement of the same
`|A₁|` points would break them into `~√lo/2` runs. That single block is what halves the component
count. The clustering was never random — it is the reciprocal lattice's block-below-√lo geometry.

---

## 4. Correction: NOT 2-adic — Dirichlet-generic in L  `[VERIFIED — matched control]`

v1 §4.1 guessed the clustering was 2-adic (because `lo = 2^{N−1}`). **Tested and refuted.** Recomputing
`A₁` for a matched **odd prime** `L ≈ 1.33·lo` gives the same shape:

| L | \|A₁\| | #components | #islands (> √L) |
|---|---|---|---|
| `2^27` (N=28) | 22 150 | 8 579 | 10 565 |
| odd prime ≈ 1.33·2^27 | 25 394 | 9 724 | 12 017 |

Same block-plus-islands structure; the counts differ only by `L`'s size (more floors ≤ Dmax). **The
law is the Dirichlet reciprocal lattice — generic in `L`, with NO special role for the power of two.**
(Correcting the guess is the finding here, per "verify a mechanism before repeating it.")

---

## 5. Characterization + open doors

**Exact statement.** Under the reconstruction-complexity filter, the `(n,k,D)` domain's `T=1` stratum
is the **Dirichlet reciprocal-floor lattice `{base ± ⌊lo/q⌋}`**: a solid block for residuals `≤ √lo`,
isolated islands for residuals in `(√lo, Dmax]`, boundary exactly `√lo = 2^{(N−1)/2}`. This is the
exact map of where "1-term" scalars live — a sharp structural lever-candidate on the d-side.

**Named next probes:**
1. **Curve-side image.** Does `{ d = base ± ⌊lo/q⌋ }` (the T=1 islands) have any non-generic image
   under `d ↦ (X,Y)`? This is the only step that could turn the d-side map into a curve lever; a
   matched-control joint-set test (not a per-point readout) is the honest form.
2. **T=2 substructure.** The `T≤2` stratum is the whole fiber; is there a *second* reciprocal lattice
   (nested Dirichlet) inside it — `⌊lo/q₁⌋ ± ⌊lo/q₂⌋` — with its own finer islands?
3. **Does T=3 ever open?** Push a fiber past `10⁷` (§v1 probe 2 still open).

---

## 6. Reproduction
```
python3 nkd_dterms_mechanism_v1.py 28 2 1     # identity, sqrt(lo) islands, 2-adic-vs-Dirichlet control
python3 nkd_dterms_mechanism_v1.py 26 3 1
```
Exact integers; `A₁` via `lo//(lo//D)` and via `d_terms` cross-checked identical. No signal-path float.
