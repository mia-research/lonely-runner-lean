# The (n,k,D) validity domain as a static manifold — Betti numbers, Euler characteristic, symmetry

**Date:** 2026-07-21 · **Script:** `nkd_topology_v1.py` (exact integers, passes `check_no_float`).
Object: the canonical-label validity domain of the `(n,k,D)` decomposition
(`PRIMER_secp256k1_nkd_dataset.md` §4), treated **purely as a static geometric object** — no
generation/PRNG content, no ordering, no per-key readout. Prior: `nkd_validity_domain_v1.py`
(reachability: coprimality necessary+sufficient; D-fiber width `~lo/n²`; N=256 overflow).

> ## ⚠ SCOPE
> This is the **d-side** object (the scalar's decomposition), not the curve/(X,Y) side. It is
> **exact and COMPLETE up to the true cap `n ≤ 256`** — not a scale-limited sample. It makes **no
> leakage / ECDLP claim**: it characterizes the *shape* of the label set, not any map to keys.
> Grades: `[PROVED]` = exact combinatorics or full enumeration; `[VERIFIED]` = matched-control.

---

## 0. The object

The canonical labels are exactly the coprime lattice points
`P_Q = {(n,k) : 1≤n≤Q, 1≤k≤n, gcd(n,k)=1}`, `Q=256` — i.e. the **Farey fractions of order 256**
`u = k/n ∈ (0,1]`. Each `(n,k)` carries a residual fiber `D` (the Farey-gap interval). Two honest
geometric realizations: the **Farey tessellation** (mediant triangles — the "surface") and the
**integer-grid net** (unit adjacency — the "discrete lattice"). Both computed exactly.

---

## 1. The surface is a CONTRACTIBLE DISK  `[PROVED — exact, all Q]`

Farey tessellation of order `Q` (vertices = fractions denom ≤ Q, triangles = mediant triples
`{a/b, c/d, (a+c)/(b+d)}` with `b+d ≤ Q`):

| Q | V | E | F(tri) | χ | β₀ | β₁ |
|---|---|---|---|---|---|---|
| 32 | 325 | 647 | 323 | **1** | **1** | **0** |
| 64 | 1261 | 2519 | 1259 | **1** | **1** | **0** |
| 128 | 5023 | 10043 | 5021 | **1** | **1** | **0** |
| 256 | 19949 | 39895 | 19947 | **1** | **1** | **0** |

**χ = 1, β₀ = 1, β₁ = 0 at every order.** The validity surface is a simply-connected disk — **no
holes, no handles, no disconnected components.** Topologically it is the smoothest possible 2-cell.

---

## 2. The fiber is a SOLID SEGMENT ⇒ the full 3-D domain is a CONTRACTIBLE SOLID  `[PROVED — full enumeration]`

For a fixed canonical `(n,k)`, `D = d − base` with `base` fixed, so consecutive `d` give consecutive
`D`: the fiber is a **contiguous integer interval** by construction. Verified by **complete
enumeration** (every key, not sampled):

| N | keys enumerated | distinct (n,k) columns | non-contiguous D-columns |
|---|---|---|---|
| 14 | 8 192 | 7 661 | **0** |
| 16 | 32 768 | 19 237 | **0** |
| 18 | 131 072 | 19 949 | **0** |

(At N=18 the count of realized labels **= 19 949 = the Farey-256 vertex count**: the domain has
**saturated** — every order-256 label is already reached.) Contractible base (§1) × contractible
interval fiber ⇒ **the (n,k,D) validity domain is a contractible solid: β₀=1, β₁=0, β₂=0.**

**⇒ The user's hypothesis — non-trivial topology (holes / components) enforced by μ₆ — is NOT borne
out at the surface/solid level. Valid configurations form a smooth, simply-connected phase space.**
Reporting the negative *as the measured shape*, not a wall.

---

## 3. Where rigidity DOES live: the domain is intrinsically 1-DIMENSIONAL  `[PROVED]`

A parity obstruction: among the 4 corners of any unit square `(n,k),(n+1,k),(n,k+1),(n+1,k+1)`,
exactly one has **both coordinates even** ⇒ `gcd ≥ 2` ⇒ non-coprime. **So no unit square is ever
fully coprime — `F = 0` in the grid realization at every Q.** The valid set, at unit resolution, is
**a net/filament network, never a filled sheet.** This is the precise sense in which it *is* a
"fragmented lattice": not holes in a surface, but the absence of any 2-cell — the domain is a graph.

---

## 4. The net connectivity is ARITHMETIC-STRUCTURED, not generic  `[VERIFIED — matched control, Q=128]`

Grid-net `(β₀, β₁)` of the valid domain vs matched nulls:

| set | V | β₀ | β₁ |
|---|---|---|---|
| **coprime (VALID)** | 5022 | **116** | **396** |
| full triangle (no sieve) | 8256 | 1 | 0 |
| random, density-matched (8 seeds) | ~5020 | 206–246 | 105–157 (mean 129) |
| odd–odd-forbidden (one congruence) | 6176 | 1 | 1953 |

The valid net is **both more connected (β₀ 116 vs ~226) and ~3× more cyclic (β₁ 396 vs ~129)** than a
density-matched random set — a genuine, matched-control-validated signature that the connectivity is
not a generic consequence of the ~`6/π²` density. (Control fires cleanly: full triangle → trivial;
one congruence → over-fragmented; random → an intermediate band the valid domain sits outside.)
*Power/scope:* global-density matched null; a per-`n`-density null is the natural refinement.

---

## 5. μ₆ / GLV placement, and the actual symmetry  `[PROVED]`

- **μ₆/GLV acts on the curve side**: `(X,Y) ↦ (βX, Y)`, `d ↦ λd mod N_ord`, `λ ~ 2¹²⁸`. On the
  `(n,k,D)` **band-position** side, `λd` scrambles the band ⇒ **no μ₃/μ₆ action on the domain.**
  μ₆ sits on the `(X,Y)` image, across the ECDLP bijection — not on this object.
- **The domain's actual symmetry is a ℤ/2**: `k ↦ n−k` (`u ↦ 1−u`, within-band negation). It
  preserves coprimality (`gcd(n,n−k)=gcd(n,k)`), is free except the single center `(2,1)`, and acts
  on the disk as a reflection. Any β₁ cycles of the net come in ℤ/2-symmetric pairs.

---

## 6. What this is — and the open doors (not closures)

**Positive characterization.** The `(n,k,D)` validity domain is a **contractible Farey solid**
(β₀=1, β₁=0, β₂=0, χ=1), realized discretely as a **1-dimensional coprimality net** whose
connectivity is measurably non-generic (β₁ ≈ 3× a density-matched null, and more connected), carrying
a **ℤ/2 reflection** symmetry. Complete up to the true cap `n=256`. μ₆ is not a symmetry of this
object; it lives on the curve image.

**Named next probes** (each a natural sub-object where topology *could* become non-trivial):
1. **D-terms sub-surface:** `{(n,k) reachable with ≤ t D-recursion terms}` carves a subset of the
   disk. Does bounding reconstruction complexity punch holes? (Dataset has `D_terms`.)
2. **Finite-N reachable growth:** at fixed small `N` the reached labels are a finite subset of the
   disk; its percolation/β₀ as `N → 18` (the saturation point).
3. **Which cycles:** the net's excess β₁ — are the loops organized by Stern-Brocot depth / the
   continued-fraction tree? A structured-vs-random *location* test, not just a count.

---

## 7. Reproduction
```
python3 nkd_topology_v1.py            # §1 tessellation, §3-4 net+controls, §5 symmetry, §2 fiber enum
python3 nkd_topology_v1.py 16 256     # any set of orders Q
```
Exact integers throughout; `check_no_float` passes. No dataset needed (self-generating);
`exact_core` used only for the §2 full-enumeration fiber check.
