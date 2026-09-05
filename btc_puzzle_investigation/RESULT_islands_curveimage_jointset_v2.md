# RESULT v2 — Dirichlet reciprocal-floor islands: curve-image JOINT-SET test (executed + audited)

**Supersedes `RESULT_islands_curveimage_jointset_v1.md`** (same run; v1 overclaimed on two
points that a post-run audit caught — corrected here). v1 retained for the audit trail.

**Grade: `[EMPIRICAL — scoped null on S1/S2/S3 only, pre-registered, controls live]`.**
Executes `PREREG_islands_curveimage_jointset_v1.md` verbatim (spec frozen 2026-07-21; no
parameter changed post-freeze). Run + audit date 2026-08-06. The scoped null is **NOT**
"no structure / avenue dead / closed" (§7 pre-committed framing).

## What changed from v1 (post-run audit corrections)

Audit = (a) 5 mechanical checks I re-ran with the artifact + (b) an independent
**context-isolated `experiment-designer`** given only the frozen spec + raw logs (blocked
from reading v1). Two v1 claims are **withdrawn**:

1. **The M=4096 / B=199 cell is VOID, not a valid null.** With B=199 the minimum achievable
   `p_MC = 1/200 = 0.005` **exceeds** the frozen `α* = 5/1200 = 1/240 ≈ 0.004167`, so **no
   statistic — including every positive control — can FIRE** in that cell. By §6's VOID gate
   ("any designated PC does not fire ⇒ null uninformative — halt, no verdict") the whole cell
   yields no verdict. This is a **spec-parameter defect** (§3 verified α*-achievability only
   for B=999 and never re-checked the B=199 secondary cell); the implementation computes the
   FAILs correctly and the log disclosed them. v1 read this cell as "S4 power, rules out c≳17
   clustering" — **withdrawn**.
2. **The S4 arm has no working positive control; its "no approximate clustering" claim is
   withdrawn.** PC-2 is S4's designated control (§2), but the implementation only ever passes
   PC-2 through `add_energy` (S1) — `window_count` is never applied to the PC-2 set (line 272).
   And even if it were, PC-2 at `c∈{1,2,4}` injects ~`2c ≤ 8` sub-Δ pairs vs the ≳136 (`c≳12`)
   the spec's own §3 power calc requires — 2 orders of magnitude short. So per §6 **S4 reads
   VOID (uninformative)** in every cell. v1's "rules out c≳12 (M=1024)/c≳17 (M=4096) approximate
   clustering" is **unsupported — withdrawn**.

**Unchanged:** the S1/S2/S3 exact-collision arms and the primary headline — those are fully
controlled and stand (below).

## Pre-flight + mechanical verification (all passed, with artifact)

- **No-float gate** `check_no_float.sh islands_curveimage_jointset_v1.py` → `OK`. Signal path
  int-only (group law `% P`, inverse `pow(z,P−2,P)`, integer energies, `Δ=-(-P//M)`, p-values
  exact `(num,den)`, `fires()` integer cross-multiply). Audit Finding 5 confirms.
- **Curve arithmetic:** `1·G=(Gx,Gy)`; sampled points on `y²=x³+7 mod p`; `(N_ord−1)·G=−G`.
- **CHECK-1** island x-coords all distinct (1024/1024) ⇒ any S1 hit is a genuine relation, not
  a ±P artifact (matches §0 no-collision proof).
- **CHECK-2 (load-bearing):** independent brute-force `Counter` recomputation of primary S1 =
  **2,096,128 = fast-path value = baseline `2M²−M`.** The Sidon fast-path is **not** hiding a
  collision — the islands' curve image is genuinely Sidon.
- **CHECK-3:** injecting one genuine **distinct-value** additive quadruple moves S1 by +8 ⇒ the
  exact detector catches distinct-x relations (not only duplicated-x). Smallest detectable = 1
  quadruple → `p_MC=1/1000`.
- **CHECK-4:** 1022/1024 island scalars closed under `d↦2·base−d` ⇒ S0 fires for the correct
  **tautological** (scalar-lattice) reason; carries no leakage.
- **CHECK-5:** a fresh random null has S1 exactly at baseline ⇒ Null-B point-mass is correct
  behavior (collision prob ~2⁻²³⁶), not a degenerate null.

## The frozen 12-cell family — S1/S2/S3/S4 × N∈{64,128,252}, M=1024, B=999

`α*=1/240`. Null-B: `M` uniform in-band scalars, `seed=20260721`, same `d·G` map. S1/S2/S3 null
is a **point-mass at `2M²−M = 2,096,128`**; S4 null ≈ Poisson (mean `2M=2048`, sd `45.3`).

| N | S1 (x-add) | S2 (x-mul) | S3 (y-add) | S4 (x-window) | z(S4) | S0 ctrl | PC-2/3/4 |
|---|---|---|---|---|---|---|---|
| 64  | 2,096,128 null | null | null | 2,112 | +1.41 | fires (3.43e6) | ✓✓✓ fire |
| **128** | **2,096,128 null** | null | null | 1,982 | −1.46 | fires (3.33e6) | ✓✓✓ fire |
| 252 | 2,096,128 null | null | null | 2,058 | +0.22 | fires (3.35e6) | ✓✓✓ fire |

S4 column is recorded for completeness but is **uninformative** (no firing control — see
withdrawal #2). M=4096/B=199 cell **VOID** (withdrawal #1).

## Verdict (per the pre-committed §7 table)

**PRIMARY cell S1 @ N=128, M=1024 does NOT fire, and S1(AP) is inert.** All B=999 positive
controls fired (PC-2 under S1 `p=1/1000`; PC-3 `1/1000`; PC-4 `1/1000`; S0 islands & AP ≫ null).
§7 mapping: NON-GENERIC needs S1 FIRES → no; VOID needs a PC/S0 failure → no; so the primary
lands in:

> **GENERIC AT TESTED POWER** (hypothesis abandoned at this scope), reported as a **scoped bound**:
> *"generic in additive / multiplicative / near-collision functionals of raw affine coords at this
> power"* — never "no signal / dead / closed." (N=64, N=252 reproduce the same pattern.)

### What the (controlled) null rules out — power ≈ 1
- **≥1 exact additive OR multiplicative relation** among the islands' curve-image `x`- or
  `y`-coordinates (S1/S2/S3), at N∈{64,128,252}, M=1024. Detector is exact (CHECK-2/3) and
  controlled (PC-3/PC-4 fired); one relation would fire at `p=1/1000`.

### What this does NOT license (over-/under-claim boundary — audit Finding 6)
- **Approximate x-clustering (S4): UNTESTED**, not excluded — no firing control (withdrawal #2).
- **μ₃ / GLV eigen-coordinate `βX`: UNTESTED**, not excluded — S2 never fired, so the §4
  "check β-related x's before naming μ₃" branch is moot; μ₃ structure is simply untested. This
  is the natural next arm (islands are not `×β`-closed).
- **Also open (§4):** rational coords (`y/x`…), ≥3-point group invariants beyond additive energy,
  2-adic / formal-group filtration, any statistic coupling `X` & `Y` **jointly** (S1–S4 treat them
  separately). §1a first-moment / binned / slope / collinearity stats are KS-floored or S0-tautological.
- Reading this as "islands leave no curve-image fingerprint" would be an **overclaim**: the design
  has demonstrated sensitivity only to **exact** coordinate relations. The AP arm (maximal
  *scalar-side* structure, S0=7.16e8) is itself **null on S1–S4**, so structured-scalar → Sidon-image
  is the generic outcome and the design has **no calibrated sensitivity to non-exact d-side structure
  through the `d↦x(dG)` map** (spec discloses this in §2, "no cheap curve-point set with planted
  distinct-x additive energy exists").

## Minor disclosures (audit Finding 5)
- **PC-2 band-match imperfect:** its planted pair uses `d_a=(N_ord//3)+7 ≈ 2²⁵⁴`, **out of the
  N=128 band** `[2¹²⁷,2¹²⁸)`; only the `M−2c` filler points are band-matched. Does not undermine
  PC-2's S1 firing (shared-x injection worked), but the band-match is not exact.
- **S0/PC-1** firing is printed as raw values without an explicit FIRE tag; derivable, not adjudicated
  in-log.

## Owed (to lift the two withdrawals — labeled EXPLORATORY if run)
1. **S4 control:** apply `window_count` to a plant of `c≳12` genuinely near-coincident x-coords
   (not a duplicated-x ±pair), confirm it fires, then re-read S4. Until then S4 = VOID.
2. **M=4096 cell:** re-run at `B≥239` (min-p < α*) so its controls can fire — but note this does
   NOT rescue S4 (still no S4 control), so it only matters for higher-M S1/S2/S3.
Both are re-runs at parameters differing from the frozen spec ⇒ **EXPLORATORY supplements**, not
the frozen result.

## Relation to adjacent results
- Valid disjoint-construction form of "do the islands leave a curve-side fingerprint" (feature =
  coord map `x,y`; target = reciprocal-floor label; §0 tautology check).
- Distinct from `RESULT_sidechannel_island_leak_infeasibility_v1.md` (side-channel observable of
  island/T-membership is construction-infeasible). That closure left this curve-image test open;
  this run returns a controlled **exact-relation** null on S1/S2/S3, with S4 + all §4 functionals + μ₃ still live.

## Provenance / replication
- Spec `PREREG_islands_curveimage_jointset_v1.md`; code `islands_curveimage_jointset_v1.py`.
- `python3 islands_curveimage_jointset_v1.py 128 1024 999` (primary); `64/252 …1024 999`;
  `128 4096 199` (VOID). Raw logs `scratchpad/out_N{64,128,252}_M1024_B999.txt`,
  `out_N128_M4096_B199.txt`. Parent context `RESULT_nkd_dterms_subsurface_v2.md`.
