# RESULT — R1 scale engine works (no hand-rolling); f5 arm of PREREG_anew_direct_invariant tested on an N-ladder

**Date:** 2026-08-22. Continues `RESULT_anew_direct_invariant_p43_validation_v1.md`. Executes the pre-reg's
realizability slot (self-audit slot 1) and the **f5** arm of the frozen invariant menu across a size ladder.
**Not a full verdict:** only ONE of the frozen invariants (f5, the ℓ₀-torsion label) is exercised, and
the pre-reg's powered bar (N_test ≥ 500, ≥2 primes) is not yet reached. No leakage/ECDLP grade is promoted.

Scripts (`scratchpad/anew_p43_validation/`): `scale_probe.sage`, `scale_diag.sage` (realizability),
`powered_gen.sage` (generalized R1 generator), `val_stats.py` (int-only stats, `check_no_float` PASS),
`find_primes.sage` (ladder-prime search).

## Headline — the pre-reg's slot-1 blocker is DISCHARGED

The prior "Sage hangs above p=43" was the **O(|A_new|) dlog-table build and `S.order()`** — *not* the
Jacobian group law. Skipping both, the genus-3 group law runs fast and correctly at scale (confirmed
p=499, 691, 1009, 2011 in the diagnostic; the only growing cost is the O(p) place enumeration, ~10s at
p=2011). **R1 needs no hand-rolling.** `|A_new(F_p)| = p²+p+1` verified at every prime (1893, 478173,
2095257 = p²+p+1 at p=43, 691, 1447); ℓ₀=3.

## The f5 ladder (real invariant = ℓ₀=3 torsion label of Q_d = S([d]G), DLP-free)

| p | nE (prime) | N (orbit reps) | N_test | plant fires to | collapse | matched S_closed | **f5 → d mod m** |
|---|---|---|---|---|---|---|---|
| 43 | 31 | 5 | 3 | — (N too small) | floor | floor (d-indep) | uninformative |
| 691 | 643 | 107 | 54 | π=1/2 (π=1/4 @m=13) | floor | floor (d-indep) | **no fire**; mild m=7 p≈0.06 |
| 1447 | 1489 | 248 | 124 | **π=1/4** (all m) | floor | floor (d-indep) | **no fire**; mild m=13 p≈0.08 |

- **Controls — with their roles kept distinct (this matters):**
  - **COLLAPSE null** (real f5 distribution, shuffled Q↔d association): at floor throughout — this is
    the load-bearing false-positive control.
  - **FIRING PLANT**: fires on planted signal, floor sharpening as N grows (π=1/2 at N=107 → π=1/4 at
    N=248), and **π=0 never fires** — the detector has power and no FP defect.
  - **MATCHED `S_closed`**: at floor, but its feature is a **constant** (f5(S_closed) = a single value,
    `[0]`/`[1]`), because S_closed is d-independent (distinct A_new-part = 1). So its floor-pass is a
    **premise verification** (S_closed really is d-independent, as Hom(E,A_new)=0 predicts), NOT an
    independent FP control — a constant feature cannot leak. A stronger discriminator (a d-DEPENDENT,
    A_new-structure-free control) is not yet built; owed.
- **f5 result (form-at-scope, NOT an object closure):** the ℓ₀=3 torsion label of `Q_d` shows **no
  detectable `d mod m` recovery down to a ~π=1/4 leak-strength floor at N=248.** Two mild blips appear
  (m=7 at p=691, p≈0.06; m=13 at p=1447, p≈0.08), both non-significant. They are at moduli **not shared
  between the two curves' M(n)** (m=7 is in p=691's set, m=11 replaces it at p=1447), so **no like-for-like
  replication was tested** — treated as noise pending a shared-modulus retest, not a failed replication.

## Reading (banked progress, not a declared null)

A **moderate (π≳1/4) partial-`d` leak in the 3-torsion channel `f5` is ruled out at N≤248.** This narrows
the live target; it does **not** close the A_new avenue. Explicitly still open (the sharper target):
1. **The high-resolution invariants f1–f4** — the F_{p³}-pairing coordinates of `Q_d`, which read the
   *joint* A_new structure (f5 is only a 3-valued label; f6 is near-marginal). **Untested** — needs a
   Tate pairing (Miller) on `Jac(C)` or the `A_new(F_p) ≅ μ_{p²+p+1} ⊂ F_{p³}*` embedding. This is the
   invariant class that actually tests the hypothesis. (Corollary C does NOT close this: it forbids
   recovering `d` by *solving* the F_{p³} dlog, not reading cheap *coordinates* of a pairing value.)
2. **Weaker leaks (π < 1/4)** — need the pre-reg's powered bar N_test ≥ 500 (p≈5827/5839, N≈987; located).
3. **Higher-order / joint invariants** — the pre-reg's Outcome-B next probe, untouched.

## Owed / next
- Implement f1–f4 (pairing) — the high-value arm; OR scale f5 (+cheap f6) to N_test≥500 for a bounded
  verdict on the low-resolution channel. (Decision pending.)
- Frame slots 3(beyond p=1447)/5/6 remain isolation-owed per CLAUDE.md §2a.

*No ECDLP/key-recovery/leakage claim. Grades attach to the PIPELINE and to the scoped f5 negative
(object = ℓ₀-torsion label; power = π≈1/4 at N=248; scope = the three-prime ladder), not to the A_new
leakage question, which remains OPEN and only partly probed.*
