# Masked-Structure — Findings v6: the three deep probes, built

**Date:** 2026-07-16 · the frontier list of v5 §2, now built rather than flagged.
Scripts: `odd_s3_harness_v1.py`, `bilinear_diffset_v1.py`. Exact signal path throughout;
float only as a ranked/analytic-size display statistic.

The three pointers were: (1) the bilinear / two-point difference set — "the deepest, built
zero times"; (2) the y-coordinate / odd half, and specifically its *interaction* with the
bilinear; (3) the joint `(u,v)` in **3-D with S3**, not 2-D. They are one structure seen
three ways — **x is even in `d`, y is odd in `d`, and S3 is an odd-order moment** — so the
odd/antisymmetric direction ties all three together.

**Bottom line:** all three are generic, but each is now *built with power* (not declared),
and two surfaced exact structural facts — the **GLV μ₃ zero** and the **first construction
of the difference-set object**.

---

## 1. S3 — the full third-order tensor over curve points  [VERIFIED generic]

The 2nd moment is symmetry-pinned (Int.1 = ½). The 3rd is the first odd-order object, and
`Σz³ = 0` over the field *only because* the field is `x→−x` symmetric; curve points are
QR-restricted (`x³+7` a QR), breaking it, so **S3 is the first odd-order curve signature.**
Full real tensor `S_uuu, S_uuv, S_uvv, S_vvv` (exact integer), over all curve x-coords:

| p | Nc | Suuu/p² | Suuv/p² | Suvv/p² | Svvv/p² | \|S3\|/p² |
|---|---|---|---|---|---|---|
| 523 | 244 | 0.0021 | 0.0175 | 0.0041 | 0.0360 | 0.0403 |
| 2281 | 1101 | 0.0284 | 0.0037 | 0.0031 | −0.0031 | 0.0289 |
| 5323 | 2716 | −0.1168 | 0.0257 | −0.0260 | −0.0141 | 0.1232 |
| 12613 | 6318 | −0.0606 | 0.0061 | 0.0197 | 0.0196 | 0.0669 |
| 59971 | 29820 | 0.0470 | −0.0089 | 0.0016 | −0.0160 | 0.0505 |

All components O(0.01–0.1), scattered around 0, **flat while √p grows 10×** ⇒ `|S3| ~ p²`
(the √-cancellation scale; no-cancel would be `p^2.5`). The full 3-D third-order structure
of the lift over curve points is generic — extends v2 §A2 (a single complex contraction) to
the whole tensor. **No enhanced component.**

---

## 2. The y-coordinate unlocks the odd spectrum — and reveals the GLV μ₃ zero

**Mechanism (confirmed):** `x([d]G)=x([−d]G)` ⇒ every x-readout is even in `d` ⇒ odd scalar
characters give **exactly 0** (v5). `s_y(d) = (−1)^{y([d]G) mod 2}` flips sign under
`d→−d` (`p` odd ⇒ parity of `p−y` differs), so it is **odd in `d`** and un-zeros them.
Tested on `m ≡ 3 mod 4` curves (quadratic `ψ` is odd):
- `Σ_d ψ(d) χ_k(x_d)` (no y) = **0.000 exactly** — confirms odd-invisible-to-x.
- `Σ_d ψ(d) s_y(d)` and `Σ_d ψ(d) χ₂(x_d) s_y(d)` — **un-zeroed** by y.

**New exact structural fact — the GLV μ₃ zero  [PROVED + VERIFIED]:**
`Σ_d ψ(d) χ₃(x_d) s_y(d) = 0` exactly, at every prime tested. Reason: the GLV endomorphism
`β:(x,y)↦(βx,y)` realises `[λd]G` (`λ³=1 mod m`), multiplying `x` by a cube root ⇒ shifting
`χ₃(x)` by a fixed nonzero amount, while **leaving `y` unchanged**. Since `d↦λd` is a
bijection of the group,
```
   S = Σ_d ψ(d) χ₃(x_d) s_y(d) = ψ(λ)·ζ₃·S   ⇒   S(1 − ψ(λ)ζ₃) = 0   ⇒   S = 0.
```
(Verified: χ₃ labels over the orbit are exactly balanced 434:434:434 — the μ₃ signature;
brute-force complex sum = 0.0000.) So **any (cubic-character-of-x)×(function-of-y) readout
is annihilated by GLV.** More generally `d↦λd` constrains all these odd probes: the
quadratic/`s_y` probes survive only when `ψ(λ)=+1`.

**The residual beyond GLV is generic.** Scaling the surviving probes over `√m` from 26 → 348
(~13×): `Σψ·s_y /√m` and `Σψ·χ₂·s_y /√m` stay O(1), flat; the occasional spike (5.15, 6.41)
is single-point fluctuation (not at the largest m; random control fluctuates as much). So
the y-coordinate unlocks the odd spectrum, GLV μ₃ carves an exact zero into it, and what
remains is generic square-root cancellation.

---

## 3. The bilinear / two-point difference set — BUILT (first time)  [VERIFIED generic, powered]

Closure's own named complement (Lemma R bounds single sums; the stance principle "only a
joint property of the SET survives the ECDLP scramble" is exactly this). Flagged four
sessions, built in none — now built.

**Object:** the difference set `{P_i − P_j : i>j}` of the 82 solved keys (3321 points,
exact point subtraction `P_i + (−P_j)`), probed by (1) **flap fraction** (Cap-Law generic =
0.25; a joint additive relation among the `d_i` would distort the difference-lift
distribution) and (2) the **exact S3** `|Σz³|²` (the 3-D ask). Matched null = 120
random-82-key sets in the **same dyadic bands** (our-own-pipeline set).

| set | flap_frac | rank | S3 rank |
|---|---|---|---|
| **[ctrl]** held-out random-82 | — | 0.183 | 0.058 |
| **REAL 82 keys** | 0.2520 | **0.683 → null** | **0.267 → null** |
| null flap_frac | mean 0.2498, sd 0.0070 | real z = **+0.31** | |

**Power (the thing missing from every prior 82-key test):** null `sd(flap_frac)=0.0070` ⇒ a
coherent shift of **1.4% (47 of 3321 pairs)** is detectable at 2σ. The difference set gives
3321 pairs of power, not 82 points of none. The real set sits squarely in the null bulk.

**Known-structure check (stated before running):** `d_i ∈ [2^{P_i−1},2^{P_i})` distinct
bands ⇒ differences are well-mixed ~160-bit scalars ⇒ lifts generic for real *and* null
(non-degenerate). The **y-antisymmetric** part is *degenerate for these keys* — every
positive difference `δ < n/2` ⇒ `sign(y([δ]G))` pinned = the known smallness — so it was
**not** tested (would only re-measure smallness). Correctly excluded, not overlooked.

---

## 4. Net + honest scope

| probe | status | new fact |
|---|---|---|
| S3 full tensor (3-D) | VERIFIED generic (√p ×10) | extends A2 to the whole tensor |
| y unlocks odd spectrum | mechanism confirmed; residual VERIFIED generic (√m ×13) | **GLV μ₃ zero** [PROVED] |
| bilinear difference set | **BUILT** (first time); VERIFIED generic, powered to 1.4% | joint-SET object now exists |

**What "generic" means here (grade discipline):** each is a *scoped* VERIFIED null — named
set, named statistic, named power — not a closure. Specifically **still open**:
- the difference set on **more statistics** — the full joint `(u,v)` distribution of the
  difference lifts, higher moments, and **additive-energy / collision counts** (the canonical
  AP/coset detector; degenerate on raw one-per-band `d_i` but not on the curve-lift image);
- the difference set at **larger key sets** than 82 (more solved puzzles → more pairs);
- the odd spectrum with **richer y-readouts** than `s_y` (e.g. lifting `y`, `eis_p(y)`), and
  odd probes *quotiented by the GLV μ₃ action* (to see past the exact zero);
- everything at **secp's actual p** (all scaling here is small-to-moderate p).

The three deepest pointers are no longer "flagged, unbuilt." Two are built-and-generic with
power; the y/odd one additionally produced an exact GLV identity. None overturns the
picture; all three sharpen *where a leak could still be* — which, for these objects, is now
"in a statistic finer than flap/S3, or past the GLV μ₃ quotient," not "unexamined."
