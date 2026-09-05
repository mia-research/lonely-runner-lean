# RESULT — Dirichlet reciprocal-floor islands: curve-image JOINT-SET test (executed)

**Grade: `[EMPIRICAL — scoped null, pre-registered, all controls live]`.** Executes
`PREREG_islands_curveimage_jointset_v1.md` **verbatim** — no parameter changed after the
spec was frozen (2026-07-21). This is a *scoped bound at tested power*, **NOT** "no
structure / avenue dead / closed" (the spec pre-committed this framing in §7).

Run date 2026-08-06. Implementation `islands_curveimage_jointset_v1.py` (exact integers).

## Pre-flight gates (all passed before any data was read)

- **No-float gate:** `check_no_float.sh islands_curveimage_jointset_v1.py` → `OK`.
- **Curve arithmetic verified:** `1·G = (Gx,Gy)`; sampled points on `y²=x³+7 mod p`;
  `(N_ord−1)·G = −G`. Island builder: `M` distinct, all in `[2^{N−1},2^N)`.
- **Machinery (S0 control) fires** in every cell: islands & AP group/scalar additive
  energy ≫ Null-B point-mass. **Planted positives fire** at B=999 (see below).

## The frozen 12-cell Bonferroni family — `{S1,S2,S3,S4} × N∈{64,128,252}`, M=1024, B=999

`α* = 0.05/12 = 5/1200 = 1/240`. Null-B: `M` uniform scalars in-band, `seed=20260721`,
same `d·G` map. S1/S2/S3 null distribution is a **point-mass at `2M²−M = 2,096,128`**
(exact-collision detectors; blind to approximate). S4 null ≈ Poisson, mean `2M=2048`,
sd `√(2M)=45.3`.

| N | S1 (x add) | S2 (x mul) | S3 (y add) | S4 (x window) | p_MC(S4) | z(S4) | S0 ctrl | PC-2/3/4 |
|---|---|---|---|---|---|---|---|---|
| 64  | 2,096,128 null | 2,096,128 null | 2,096,128 null | 2,112 null | 172/1000 | +1.41 | fires (3.43e6) | ✓✓✓ fire |
| **128** | **2,096,128 null** | 2,096,128 null | 2,096,128 null | 1,982 null | 860/1000 | −1.46 | fires (3.33e6) | ✓✓✓ fire |
| 252 | 2,096,128 null | 2,096,128 null | 2,096,128 null | 2,058 null | 424/1000 | +0.22 | fires (3.35e6) | ✓✓✓ fire |

- **All 12 cells NULL.** S1/S2/S3 sit exactly on the point-mass (`p_MC = 1000/1000`) ⇒
  **no exact additive or multiplicative x- or y-quadruple** in the islands' curve image.
  S4 within `±z√(2M)` (in fact ≤ +1.4σ; N=128 and the power cell are *below* the mean) ⇒
  **no approximate x-clustering**.
- **The AP arm is null on S1–S4 too** (S1(AP) = 2,096,128 point-mass; S4(AP) within null)
  while S0(AP) is maximal (7.16e8). Corroborating fact: a *maximally* structured d-set
  (perfect arithmetic progression) has huge **scalar-side** additive energy (S0) that
  **does not survive** the `d↦x(dG)` map into curve-image joint structure (S1–S4). The
  ECDLP-side scramble erases interval/AP structure of the scalars, as expected.
- **Positive controls fire at B=999** (min p = 1/1000 < α*): PC-2 (curve `±`-pair, S1)
  excess +8,186 → `p_MC=1/1000`; PC-3 (residue AP, S1) and PC-4 (residue GP, S2) excess
  +7.14e8 → `p_MC=1/1000`. Detection down to **one exact quadruple**, power ≈ 1.

## S4-power cell — N=128, M=4096, B=199 (not a Bonferroni cell; §4 "for S4 power")

S1/S2/S3 = point-mass `33,550,336` (null); **S4 = 7,924** inside null `[7,836 – 8,500]`,
`p_MC=195/200`, `z = −2.96` (*fewer* close pairs than random) ⇒ **no clustering at the
higher M** (the design's `c≳17` power point is met and null). S0 control fires
(islands 5.25e7, AP 4.58e10 ≫ null).

**Disclosed granularity (honest, not a VOID):** at B=199 the minimum achievable p is
`1/200 = 0.005 > α* = 0.004167`, so **no statistic — including a planted positive — can
cross α* in this cell**. The PC excesses are nonetheless enormous and unambiguous (PC-3
sits +4.58e10 above a null that never leaves baseline), so the detectors are demonstrably
live; the "FAIL" tag the script prints for this cell is the fixed-α*-vs-B=199 threshold
granularity, disclosed here. The FIRE/VOID rule (§6) is therefore **not applied** to this
cell; it serves only its stated role (S4 power), where the reading is unambiguous null.

## Verdict against the pre-committed table (§6 / §7)

**PRIMARY cell S1 @ N=128, M=1024 does NOT fire, and S1(AP) is inert.** By §7 this is the
pre-committed branch:

> **GENERIC AT TESTED POWER (hypothesis abandoned at this scope)** ⇔ S1,S2,S3 at baseline
> `2M²−M` (`p_MC=1`) AND S4 within `±z√(2M)` while every PC fired.

Reported, in the spec's own required words, as a **scoped bound**:
*"generic in additive/multiplicative/near-collision functionals of raw affine coords at
this power"* — **never** "no signal / avenue dead / closed."

### What this rules out (power ≈ 1 for the smallest detectable effect)
- **≥1 exact additive or multiplicative relation** among the islands' curve-image
  `x`- or `y`-coordinates (S1/S2/S3), at N∈{64,128,252}, M∈{1024,4096}.
- **Approximate x-clustering** of `c ≳ 12` near-coincident coordinates at M=1024, and
  `c ≳ 17` at M=4096 (S4).

### What is NOT excluded (the live scope boundary — the honest next probes, §4)
The null is scoped to S1–S4 **only**; it is *not* "the set is generic." Structure is not
excluded in: (i) the **GLV/μ₃ eigen-coordinate `βX`** (islands are not `×β`-closed, so
this is the natural next arm); (ii) **rational coordinates** (`y/x`, …); (iii) **≥3-point
group invariants** beyond additive energy; (iv) **2-adic / formal-group filtration**;
(v) **any statistic coupling `X` and `Y` jointly** (S1–S4 treat them separately). These
remain open and are the sanctioned continuation, not a closure.

## Relation to the two adjacent results

- This is the **valid, disjoint-construction** form of "do the islands leave a curve-side
  fingerprint": feature = field-coordinate map `x(·),y(·)`; target = reciprocal-floor
  island label — disjointly constructed (spec §0 tautology check).
- It is **distinct from** `RESULT_sidechannel_island_leak_infeasibility_v1.md` (2026-08-06),
  which showed a *side-channel* observable of island/T-membership is construction-infeasible.
  That closure explicitly left this curve-image test open; this run addresses it and returns
  a scoped null on S1–S4, with the §4 functionals still live.

## Provenance / replication

- Spec: `PREREG_islands_curveimage_jointset_v1.md` (frozen 2026-07-21).
- Code: `islands_curveimage_jointset_v1.py`; exact int group law (Jacobian + batch inverse),
  `pow(z,p−2,p)`. Re-run: `python3 islands_curveimage_jointset_v1.py <N> <M> <B>` for
  `(128,1024,999)` primary; `(64,1024,999)`, `(252,1024,999)`; `(128,4096,199)` power.
- Raw logs: `scratchpad/out_N{64,128,252}_M1024_B999.txt`, `out_N128_M4096_B199.txt`.
- Parent context: `RESULT_nkd_dterms_subsurface_v2.md` (T=1 islands = Dirichlet
  reciprocal-floor lattice, d-side, exact).
