# AUDIT — the R1 CM-relation-yield INSTRUMENT vs its gate-cleared prereg (v3)

**Date 2026-08-07.** Trust-but-verify pass on `semaev_cm_relation_yield_v3.py` + harness
`semaev_elimination_v1.py` against `PREREG_semaev_cm_relation_yield_v3.md` (gate-cleared) and the
executed `..._v3.log`. **The prereg is sound; the INSTRUMENT does not implement it in several
load-bearing ways.** The strong `T1_j0` signal (0.21, p<1e-4, 12/12 |V|-growth) is therefore **not
gradeable as-is** — and the two most serious gaps are exactly the controls the prereg added to rule
out that the effect is a twist-selection / `#E` artifact.

## BLOCKING — instrument violates the frozen prereg §4 (must fix + re-run before any grade)

- **F1 — the CM twist is NOT randomized; it takes the SMALLEST B/A.** `build_curves` (lines 34–37)
  does `for B in range(1,p): ... break` → **j0 = (0, B=1)** always, and **j1728 = (A=1, 0)** always.
  Prereg §4 pre-run check explicitly requires: *"randomize the CM twist — draw B0/A0 over all valid
  residues, not 'smallest' — if the CM traces cluster to one side."* Fixing `B=1` pins j0 to ONE sextic
  class at every prime, so its trace/`#E` can cluster systematically — **the precise confound the
  randomization requirement exists to prevent.** A fixed-twist selection could itself drive `T1`.
- **F2 — the `#E` common-support / bracket check is ABSENT.** Prereg §4 requires asserting each CM `#E`
  lies inside the non-CM `#E` support with **≥2 non-CM below and ≥2 above**, regrowing if the CM traces
  cluster. `build_curves` grabs 5 random non-CM with **no bracket assertion and no regrow**. So the
  `match_nearest` pairing can be systematically **one-sided** in `#E`, and the structural `#E` control is
  missing — the very thing C4 is meant to catch, uncontrolled at construction.

## SIGNIFICANT — weaken the H1 signal / spec non-compliance

- **F3 — C4 is a much weaker control than specified.** Prereg §4 C4 = **high-`#E`-half vs low-`#E`-half**
  non-CM. The instrument (lines 121–125) instead diffs the **two lowest-order of the 3 leftover** non-CM
  curves — a tiny `#E` contrast. So the "C4 null (p=0.30)" is weak evidence that the design doesn't leak
  `#E`; the strong-contrast test the prereg wanted was never run.
- **F4 — H1's j0 (B=1) ≠ H2's j0 (B=7).** `mu3_lever_test` hardcodes the **(0,7)** curve (harness lines
  312, 341–342), while H1's j0 is **(0,1)**. The two arms test **different sextic twists**; "j0" is not a
  single object across the run. *(Not a scale bug — `mu3_lever_test` uses `F=GF(p)`, the model prime, not
  the 2²⁵⁶ secp curve; the "secp" naming is just "B=7 form.")*
- **F5 — Scaling is incomplete; the lever-decider is not obtainable.** Only `|V|∈{4,5}` is coded (no
  `m∈{3,4}` arm), and the executed **`|V|=5` run stopped at 12/24 primes** (no aggregate). The 12/12
  `T1`-growth peek is suggestive but is not the graded Scaling verdict.
- **F6 — H2 per-prime R2 does not reproduce.** Isolated `mu3_lever_test(577,3,2,27) = −0.4055` (matches
  the **V=4** log) but the **V=5** log shows **−0.6931** for the identical call (`kk=2, Dm=27` in both).
  `E.gens()` and `mu3` are stable under Sage-RNG variation (tested), so this is a **context-dependence /
  logging-path** defect, not clean determinism. H2's per-prime output is untrustworthy until pinned.

## MODERATE

- **F7 — `n_noncm=5` undersized.** After j0 and j1728 take their two nearest matches, only **3** non-CM
  remain — too few to bracket both CM `#E` (F2) or run a real high/low C4 (F3).
- **F8 — cyclicity unchecked.** `decomposable_target`/`mu3` use `E.gens()[0]` as *the* generator; on a
  non-cyclic `E(F_p)` this samples only a cyclic subgroup, and CM vs non-CM curves need not be cyclic at
  the same rate — a possible differential bias in `quo`.
- **F9 — no `results.jsonl`.** Per-cell `quo` vectors are discarded (only log aggregates kept); the
  prereg §3 "full K-vector logged" and §9 `results.jsonl` are not produced — no audit trail / reanalysis.

## VERIFIED-OK (checked, not defects)

- **`quo` is EXACT** — `I.vector_space_dimension()` when `dim=0` (harness 224–225), **not** capped by
  `Dmax`; `Dmax` bounds only `d_solv` (non-verdict per A3). The H1/H2 statistic is exact. ✓
- Within-pair sign-flip null (instrument 70–76) — correct within-pair label swap, one-sided for T1. ✓
- `κ` read from `(A,B)`/label, never from `quo` (35–45). ✓
- Schedule frozen deterministically (seed `1000+p`) **before** the first `quo`, and rebuilt identically in
  `run()` — the SHA pins the curve set. ✓ (but the curve set itself is the un-randomized F1 one.)
- `mu3_lever_test` operates at the **model prime**, not secp. ✓

## Disposition

`T1_j0`=0.21 (p<1e-4) and the 12/12 `|V|`-growth are a **real lead**, but they sit on an instrument that
**omits the two anti-confound controls the prereg added for exactly this** (F1 twist-randomization, F2
`#E`-bracket) and whose Scaling (F5) and H2 (F6) are incomplete/irreproducible. **Not gradeable.** The fix
is not cosmetic: randomizing the twist and enforcing the `#E` bracket, then re-running, is a genuine test
of whether the effect **survives** — it could shrink, vanish, or hold. Only after F1–F6 are fixed and the
run completed (with `results.jsonl`, F9) does the CM relation-yield lever question get a graded answer.

**Next:** rebuild the instrument to the spec (F1–F4, F7–F9), complete Scaling incl. `m=4` (F5), pin H2
reproducibility (F6); no re-gate of the prereg needed (these bring the instrument INTO compliance, they
do not change the spec).
