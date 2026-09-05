# The D-terms sub-surface: where the (n,k,D) domain DOES fragment — and how

**Date:** 2026-07-21 · **Scripts:** `nkd_dterms_subsurface_v1.py` (full-band enum, small N),
`nkd_dterms_subsurface_v2.py` (single wide fiber by boundary search). Exact integers; the
fragmentation control is a component-count permutation statistic (no float threshold on data).
Parent: `RESULT_nkd_validity_topology_v1.md` (full domain = contractible solid).

> ## ⚠ SCOPE
> d-side object (the scalar's reconstruction complexity), **no leakage / ECDLP claim.** Exact,
> full-fiber enumeration (not sampled). Fibers probed: widths 4·10⁴–7·10⁵, `n∈{2,3,5,8}`, `N∈{26,28,30}`.
> Grades: `[PROVED]` = exact enumeration; `[VERIFIED]` = matched permutation control.

---

## 0. The refinement

The full `(n,k,D)` domain is a contractible solid (parent result). Filter it by **reconstruction
complexity** `T(D) = d_terms` (length of the greedy reciprocal expansion of the residual). The
sublevel sub-surface `A_t = { D in fiber : T(D) ≤ t }` is where a rigidity/fragmentation, if any,
must show. Under full enumeration each fiber is the complete contiguous interval `[Dmin,Dmax]`, so
`A_t` fragmenting into disconnected runs = **holes punched by the complexity bound**;
`#components(A_t) = β₀` of the sub-fiber.

---

## 1. The fiber stratifies into exactly THREE complexity levels  `[PROVED — exact, all fibers probed]`

Every wide fiber has `T ∈ {0, 1, 2}` — **max D-terms = 2** (widths up to 7·10⁵):

| N (n,k) | width | #{T=0} | #{T=1} | #{T=2} |
|---|---|---|---|---|
| 30 (3,1) | 701 803 | 1 | 89 619 | 612 183 |
| 28 (2,1) | 263 173 | 1 | 44 300 | 218 872 |
| 26 (2,1) | 65 793 | 1 | 21 130 | 44 662 |
| 28 (8,3) | 66 577 | 1 | 38 276 | 28 300 |

So the sub-solid has three strata: `T=0` (the single base point `D=0`), `T≤1` (a fragmented
sub-fiber), `T≤2` (the whole contiguous fiber). **The only non-trivial level is `t=1`.** (`t=0`:
one point; `t≥2`: the whole interval, one component.) *Scope: max-T may grow past 2 for still-wider
fibers — untested above 7·10⁵.*

---

## 2. At t=1 the sub-surface SHATTERS — β₀ up to 3.5·10⁴  `[PROVED — exact]`

`{D_terms ≤ 1}` is broken into tens of thousands of disconnected components:

| N (n,k) | |A₁| | **β₀ (components)** | holes = β₀−1 |
|---|---|---|---|
| 30 (3,1) | 89 620 | **35 332** | 35 331 |
| 28 (2,1) | 44 301 | **17 157** | 17 156 |
| 28 (5,2) | 41 291 | **14 147** | 14 146 |
| 26 (2,1) | 21 131 | **7 559** | 7 558 |

**This is the non-trivial topology the full domain lacked.** Bounding reconstruction complexity to a
single term turns the smooth fiber-interval into a set with tens of thousands of components — a rigid,
fragmented object, exactly the qualitative picture the "fragmented lattice" hypothesis anticipated
(now located precisely: it is the `T=1` stratum, not the full domain).

---

## 3. The fragmentation is ARITHMETIC-STRUCTURED, not generic  `[VERIFIED — matched permutation control]`

Control = permute the `T`-multiset within the fiber (fixes `|A₁|`, randomizes arrangement),
20 seeds. Real component count vs control mean:

| N (n,k) | real β₀ | control β₀ (mean) | **real/ctrl** |
|---|---|---|---|
| 28 (2,1) | 17 157 | 36 859 | **0.465** |
| 30 (3,1) | 35 332 | 78 189 | **0.452** |
| 26 (2,1) | 7 559 | 14 354 | **0.527** |
| 28 (5,2) | 14 147 | 25 284 | **0.560** |
| 26 (3,1) | 6 538 | 10 891 | **0.600** |
| 28 (8,3) | 11 133 | 16 277 | **0.684** |

**real/ctrl ≈ 0.45–0.68, always < 1, and stable across a 16× width range** — the low-complexity
points **cluster** into ~2× longer contiguous runs than a random arrangement of the same multiset
would give. So the sub-surface is fragmented **but sub-generically** — an arithmetic clustering law,
not random shattering. The control fires cleanly (random arrangement ≈ 2× more components). A weak
`n`-trend: clustering is strongest at small `n` (≈0.46 at n=2) and relaxes toward n=8 (≈0.68).

---

## 4. Characterization (not a closure)

**The (n,k,D) validity domain is a contractible solid whose reconstruction-complexity filtration is
where rigidity lives:** three strata (`T∈{0,1,2}`), with the `T≤1` stratum shattered into `β₀ ~ 10⁴`
components — **but the shattering is arithmetic-structured (sub-generic clustering, real/ctrl ≈ 0.5,
stable across scale)**, not generic noise. Both halves are the finding: complexity-bounding *does*
fragment the domain (answering the hypothesis in the affirmative for the sub-surface), *and* the
fragmentation carries a scale-stable clustering law.

**Named next probes** (per the drill protocol — a sharper law, not a verdict):
1. **Mechanism of `T=1`.** `T=1 ⟺ D = ±⌊lo/⌊lo/|D|⌋⌋` exactly — a "round-reciprocal" condition on
   `D` against `lo = 2^{N−1}`. Since `lo` is a **pure power of two**, the clustering is almost
   certainly **2-adic** (runs aligned to `2`-power divisors). Test: locate the `T=1` runs and regress
   run boundaries on `ν₂(D)` / powers of 2. This would turn the `≈0.5` into an exact law.
2. **Does max-T grow?** Push a fiber past `10⁶`–`10⁷` and check whether a `T=3` stratum opens (a
   second fragmentation level `t=2`).
3. **The `n`-trend of real/ctrl** (0.46→0.68 as n: 2→8): is the clustering exponent a function of `n`
   (or of `ν₂(n)`)?

---

## 5. Reproduction
```
python3 nkd_dterms_subsurface_v1.py 18 12      # full-band enum, small N (fibers too narrow to frag)
python3 nkd_dterms_subsurface_v2.py 30 3 1     # single wide fiber (N,n,k): T-hist + A_t frag vs control
python3 nkd_dterms_subsurface_v2.py 28 2 1
```
Exact integers; single-fiber boundaries by exponential+binary search on the (proven) contiguous
fiber. `d_terms` per the canonical `exact_core`. No float in the signal path (ratios are report-only).
