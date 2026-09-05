# DEVIATIONS — PREREG_n15_joint_readout_confinement_v1.md

Freeze protocol: post-freeze changes disclosed here. The frozen spec's OBJECT,
grade cap (EMPIRICAL), datasets, exact-arithmetic rule, matched-null philosophy
(permute T against the predictor, within band), firing-control requirement, and
falsification table are UNCHANGED. Only the estimator form of the primary changed,
because the RUN found the frozen form unestimable — the same class of finding that
forced `PREREG_cm_jointset_excess_v2 → v3` to coarsen its omnibus.

---

## D1 — [RUN] §2a primary estimator: full-joint-C MI → low-order cheap-predictor family

**Frozen (§2a).** `S = Î(C(d); T | band b)`, a single Miller–Madow MI between the
FULL joint 9-component cheap-predictor vector `C(d)` and the 18-cell readout `T`,
"run on the realized-support contingency table."

**RUN finding (shakeout, `n15_readout_confinement_runner_v1.py`, band b=32, N=3000,
B=300).** The full joint `C` has realized support `K = 2662 ≈ N`, so the
`K × 18` contingency table has ≤1 count per occupied cell; the plug-in MI is
bias-saturated (S ≈ 3.46 bits, MI floor `df/2N ln2 ≈ 10.9`), and — decisively —
the **required ε=1 firing plant did NOT fire** (p_perm = 0.003 at 300 perms,
non-monotone across the ε ladder): adding a perfectly predictive `c*≡e` to an
already-shattered `C` alphabet does not raise the ranked statistic, because both the
real and the T-permuted tables are already saturated. Under the frozen §7 VOID
rule this is instrument-dead. The full joint `C` alphabet (even reduced to its
irreducible part `d mod 252 × jacobi × cube-res × hi₃ × lo₃ ≈ 48k` cells) is
unestimable at any feasible N; the §2a "keep df moderate on realized support"
clause cannot be met by a single joint-C table.

**Deviation (D1).** Replace the single joint-C MI with a **frozen family of
low-order cheap predictors**, each vs `T`, under one family-wise permutation
control:
- **Family F** = the 9 singletons `{d mod 3, d mod 6, d mod 7, d mod 9, d mod 12,
  jacobi(d,n), cube-res(d,n), hi₃(d,b), lo₃(d)}` PLUS all 36 pairs of them
  (45 predictors total). Each predictor is dense-coded over its realized support
  (small: singleton ≤12, pair ≤108), so every `pred × T` table is estimable
  (≥ tens/cell at N ≥ 10⁵).
- **Primary statistic** `S = max_{f∈F} Î(f; T)` (plug-in bits), with the family-wise
  permutation p = rank of the observed max against the per-shuffle max (permuting
  `T`, B shuffles, exact integer count). Each predictor also carries its own
  single-test permutation p (reported, uncorrected, for transparency).
- **Object unchanged.** "Does a cheap function of d predict the joint readout T
  beyond chance" — a positive `S` is still an operational keyspace pre-filter. This
  is the #4 baseline ("max MI over cheap fns") extended from the single readout `e`
  to the full 18-cell `T`, plus low-order predictor combinations.
- **Higher-order cheap predictability** (functions of 3+ C-components jointly, or
  the full joint) that is invisible to all singletons and pairs becomes a NAMED
  untested channel in any scoped-null verdict (added to §7's untested list) — not a
  reason to keep an unestimable primary.

**Chain-rule (§2b) & diagnostics (§2c) adjustment.** The frozen chain-rule used the
same full joint `C` (`Î(C;e)`, `Î(C;s|e)`, `Î(C;yp|e,s)`) and inherits the same
non-estimability. Replaced by the estimable per-readout breakdown: for each
predictor `f∈F`, report `Î(f;e)`, `Î(f;s)`, `Î(f;yp)` — so "beyond individual
readouts" is answered by whether any cheap predictor carries `s` or `yp`
information not already in its `e` prediction. Diagnostics `H(T|I)` (ceiling
`log₂18`), `H(d|T,I)`, and total correlation `TC(e,s,yp)` are computed on the small
`e/s/yp` alphabets exactly as frozen (these were always estimable) and are
unchanged.

**Everything else stands:** the 3 readout definitions (e = cubic char, s-class =
3-class Eisenstein carry `carry_c` {¾,⅛,⅛}, y-parity = `2y≥p`), the frozen `C`
component list, both dataset arms (constructed on-demand power arm + real-82 OOS),
the within-band `T`-permutation matched null, the ε-plant firing control + VOID
rule, the hard-null FP calibration, the no-float gate, and the §7/§9 pre-committed
verdict table (with the added untested-channel note above).

Recorded 2026-08-25, at first shakeout, before any banked result.
