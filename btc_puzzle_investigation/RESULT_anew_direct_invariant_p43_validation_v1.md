# RESULT — PREREG_anew_direct_invariant_partialinfo_v1: p=43 pipeline validation (machinery GO; verdict arm still owed on R1)

**Date:** 2026-08-22. Executes the VALIDATION rows (only) of the frozen pre-reg
`PREREG_anew_direct_invariant_partialinfo_v1.md`. **This is a machinery validation, NOT a
verdict on whether `A_new` leaks** — the pre-reg's own §4/§6 mark p=43 as underpowered and
its self-audit slot 1 marks the powered arm INERT until the R1 scale engine exists. Nothing
here promotes any grade on the leakage question.

Scripts (all on disk, `scratchpad/anew_p43_validation/`): `val_p43_gen.sage` (R3 realization,
exact-integer data), `val_stats.py` (int-only stats; `check_no_float.sh` PASS), `plant_power_calib.py`
(synthetic power calibration; PASS). Reproduce: `sage val_p43_gen.sage && python3 val_stats.py val_p43_data.json && python3 plant_power_calib.py`.

## What was checked, and the result

| Check | Result | Grade |
|---|---|---|
| **Pipeline runs end-to-end** (Sage geometry → exact-int data → int-only decoder + K=9999 permutation null) | runs; verdict decided by integer exceedance `E`, no float in path | `[VERIFIED]` |
| **N14 object reproduced** via the difference-lift `S` (order-1893 `A_new` at p=43, nE=31, λ=25) | covariance `ℓ(λd)=k·ℓ(d)` with `k∈{1849,587}` = `{p², p⁴}` mod 1893 (the two cube roots); affine-in-`d` 13/15; homomorphism 0/3 | `[VERIFIED — matches prior object]` |
| **MATCHED control premise** (`S_closed` = Galois-closed lift → forced trivial on `A_new` by `Hom(E,A_new)=0`) | distinct `S_closed` `A_new`-parts across all d = **1** (d-independent); `f5(S_closed)=0` constant | `[VERIFIED — slot-3 MECHANICAL part discharged at p=43]` |
| **COLLAPSE null** (shuffle Q↔d, real invariant f5) | at floor for all `m∈M(n)={5,7,11,13}` (`E=9999`, fires=False) | `[VERIFIED]` |
| **MATCHED control statistic** (run T on `f5(S_closed)`) | at floor for all `m` (fires=False) | `[VERIFIED]` |
| **FIRING PLANT — power** (synthetic `f=d mod m` corrupted at rate `1−π`) | pipeline HAS power: fires at π=1 by **N=20**, floor sharpens to **π=1/8 at N=1000**; **π=0 never fires (no false-positive defect)** | `[VERIFIED — detector powered, monotone floor]` |
| Firing plant at p=43's actual sample (**N=5 orbits**) | does NOT fire even at π=1 (TRAIN=2 cannot cover the m≥5 label space) | the pre-reg's predicted UNDERPOWERED regime |

## Reading (form-at-scope, not an object verdict)

- **The pipeline and both null controls are validated, and the detector is calibrated-powered.**
  The machinery the powered run will use is sound: exact arithmetic, controls sit where they must,
  the detector fires on a planted leak and never on noise.
- **The p=43 real-invariant test is UNINFORMATIVE, not null.** With N=5 orbit reps the design cannot
  fire even a total plant at the E=0 bar — so it says *nothing* about whether `f5` (or any menu-`F`
  invariant) of `Q_d` carries partial `d`-info. This is banked progress toward the swing, not a
  closure of the avenue: it converts "the powered arm is blocked" into the sharper "the powered arm
  needs N ≳ 50–500, i.e. p ≳ 3000 with a real `A_new` realization" — which is exactly R1.
- **The matched control is real:** `S_closed` is provably d-independent here, so a future powered
  positive that also lights up `S_closed` is a pipeline artifact — the discriminator works.

## Owed (unchanged from the pre-reg self-audit, now with the p=43 evidence attached)

1. **R1 scale engine — the one blocker for a verdict (slot 1).** Compute the real `S([d]G)` off
   Sage's function-field Jacobian at p ≳ 3000 (hand-rolled `F_p`/`F_{p³}`, dlog never computed).
   Until then only the underpowered validation rows run. **This is #2 of the plan.**
2. **Faithfulness of the invariant read at scale (slot 2)** — smoke-check injectivity when the read
   moves to the `F_{p³}` embedding.
3. **Frame slots (3-frame, 5, 6) — need isolation, not self-audit (CLAUDE.md §2a):** matched-control
   adequacy beyond p=43, the scale banner, and invariant-menu/subspace completeness. The Outcome-B
   null (if reached) stays bounded to menu `F` and first-order, with higher-order/joint invariants
   the pre-committed next probe.

*No ECDLP, key-recovery, or leakage claim is made. Grades here attach to the PIPELINE, not to the
`A_new` leakage question, which remains OPEN and unrun at power.*
