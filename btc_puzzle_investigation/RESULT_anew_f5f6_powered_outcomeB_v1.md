# RESULT — PREREG_anew_direct_invariant: powered Outcome B for the f5 + f6 channels (two primes, N_test≈490)

**Date:** 2026-08-22. The pre-reg's POWERED arm, run for the two DLP-free non-pairing invariants of the
frozen menu (f5 = ℓ₀=3 torsion label of Q_d = S([d]G); f6 = parity+sextant of the C-lift w-coordinate).
Reaches the pre-reg's powered bar (N_test ≥ ~500) at two primes. **The pairing invariants f1–f4 are NOT
in this run** — they are the pre-committed next probe (Phase 2). No ECDLP/leakage grade is promoted.

Data: `powered_p5827_data.json` (nE=5923, N=987), `powered_p5839_data.json` (nE=5881, N=980); |A_new| =
p²+p+1 at both; ℓ₀=3. Stats: `val_stats.py` (int-only, `check_no_float` PASS).

## Preconditions for a verdict (pre-reg §6) — MET

| control | p=5827 | p=5839 | role |
|---|---|---|---|
| FIRING PLANT | fires to **π=1/8** (all m) | fires to **π=1/8** (all m) | power; π=0 never fires (no FP defect) |
| COLLAPSE null | at floor (min cell p=0.04/16 cells) | at floor | **the false-positive control** |
| MATCHED S_closed | at floor | at floor | premise check only — f5(S_closed) is CONSTANT (`[1]`), so a floor-pass here confirms S_closed's d-independence; it is NOT an independent FP control |

## The statistic — f5, f6 recovery of d mod m (out-of-sample, K=9999 permutation null)

- **f5: no fire at either prime, no significant recovery.** Every (p,m) sits in the null band; smallest
  permutation p = 0.10 (m=5, p=5839), unremarkable over the 8 modulus-cells. m∈{5,7,11,13,47} (p=5827),
  {5,7,13} (p=5839).
- **f6: marginal null** — collapse at floor and recovery in the null band at every (p,m). Consistent with
  √y being a Farey-generic per-point readout (expected null under the project stance).

## Verdict (pre-registered, both-ways decision rule) — OUTCOME B for f5 + f6, BOUNDED

Preconditions met AND all f∈{f5,f6}, all m∈M(n), recovery within the null band ⇒ **no first-order
partial-`d` information in the ℓ₀-torsion label (f5) or the w-coordinate marginal (f6)**, graded at the
counter-prior's bar:

- **OBJECT** = { the ℓ₀=3 torsion-label invariant f5, and the w-coordinate invariant f6, of Q_d=S([d]G) }.
  **NOT** f1–f4 (the F_{p³}-pairing invariants that read the joint A_new structure).
- **CLASS closed** = first-order out-of-sample MAP recovery of `d mod m`, `m∈M(n)`, from these two invariants.
- **POWER** = detection floor **≈ π=1/8** (the plant fires to 1/8 but not reliably 1/16) at N_test≈490.
  A leak supplying < 1/8 of the `d mod m` information is NOT excluded.
- **SCOPE** = p ∈ {5827, 5839} at the powered bar (and the ladder p=691,1447 below), j=0, prime-order,
  p≡7 mod 12. **No claim at p≈2²⁵⁶** (scale banner; the MOV second hop is dead at scale, Corollary C).
- **EXPLICITLY NOT CLOSED** (a bound is a size, not "no structure"): **f1–f4 (pairing invariants)**;
  higher-order / joint invariants; leaks below π=1/8; anything at cryptographic scale.

## Progress reading (not a declared null)

The two CHEAP channels of the frozen menu are now cleanly bounded at powered scale: a first-order leak of
strength ≥ π=1/8 in the 3-torsion label or the w-coordinate is ruled out on two ~6000-scale primes. That
**narrows the live A_new question to the pairing invariants f1–f4** — the class that reads the joint
structure and the reason the avenue is interesting. It does not close the avenue.

## Next probe (pre-committed) — Phase 2
Implement f1–f4: the Tate pairing on Jac(C) (or the A_new(F_p) ≅ μ_{p²+p+1} ⊂ F_{p³}* embedding).
First step is a feasibility check (does Sage's function-field Jacobian expose a pairing; if not, the
genus-2 Prym model of A_new). Cost unknown until that check. Also owed: a d-DEPENDENT, A_new-structure-free
matched control (the current S_closed is constant, hence a premise check only).

*No ECDLP/key-recovery/leakage claim. The Outcome-B grade attaches to f5+f6, first-order, at the stated
power and scope — not to A_new, which stays OPEN pending f1–f4.*
