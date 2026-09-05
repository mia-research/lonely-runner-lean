# VOID — the Cartier-arm adjudication of 2026-08-02, control C4 fired

**Date 2026-08-02.** Governing spec: `PREREG_anew_supersingularity_reaudit_v2.md` §3 (C4), §6.
Run: `anew_cartier_audit_v1.sage` → `anew_cartier_audit_v1.log` (elapsed 173.3s, exit 0).
Diagnostic: `c4_diagnose_v1.sage` → `c4_diagnose_v1.log`.

---

## 1. What fired

Pre-registered C4, verbatim from v2 §3:

> **C4** | Perturbation, **entrywise**: recompute with `t_b → t_b + 1` and require the **matrix to
> change** … Applied separately to `t₂` (must break C1) and `t₃` … | **pass condition: both
> perturbations change their target** | *a corrupted exponent that changes nothing ⇒ the routine is
> not reading `t` ⇒ **VOID***

Executed result (`anew_cartier_audit_v1.log`, C4 block):

```
C4  t2+1 breaks C1 everywhere                     : False
C4  t3+1 changes new-block (CTRL/PLNT)            : True
```

`t₂+1` failed to break C1 at **7 of 18** tested primes: MAIN `p = 11, 23`; CTRL `p = 5, 17, 29, 41`;
PLNT `p = 7`. Pass condition was "both". **C4 FAILED.**

## 2. Consequence, applied without argument

v2 §6: *"The **run** is void if C1, C2, C4 or C5 fails, independent of what H-A/H-B look like."*

- **The Cartier arm (H-B, H-C) is VOID.** Its numbers are recorded below as raw output only. They
  are **not** adjudicated, they do **not** move any grade, and they may **not** be cited as evidence.
- **Marked `[CONTAMINATED — outcome known before corrected control]`.** Per session rule 2, this
  sample can never carry a primary claim, even under a corrected control, because its outcome is now
  known. A corrected control must be run on **unread data**.
- **H-A (`anew_step3_witness_v1.sage`) is also marked contaminated**, under v2 §6's blanket wording
  *"the run is void … independent of what H-A/H-B look like"*. C4 is a control on the Cartier routine
  and H-A's script shares no code with it, so a narrower reading is available — **but choosing the
  narrower reading now, after seeing that H-A passed, is exactly the post-hoc rescue rule 2 forbids.**
  The ambiguity is resolved against my own result and both arms are re-run on disjoint data.

**No post-hoc rescue is attempted.** In particular the following are *not* offered as arguments that
the run stands: that the `t₃` leg passed; that C1/C3/C5 passed at 320/320, 320/320, 296/296; that the
main-arm result is forced by an inequality anyway. Each may be true and none of them is admissible.

## 3. Cause, established by executed diagnostic (not by reasoning)

`c4_diagnose_v1.log`, `f = x³+2`, the cubic C4 used for `D = 3`:

| p | p mod 3 | `a_p(E) mod p` | true `Tr` | perturbed `Tr` | breaks C1 |
|---|---|---|---|---|---|
| 7 | 1 | 6 | 6 | 1 | True |
| 11 | 2 | 0 | 0 | 0 | **False** |
| 19 | 1 | 7 | 7 | 17 | True |
| 23 | 2 | 0 | 0 | 0 | **False** |
| 31 | 1 | 27 | 27 | 20 | True |
| 43 | 1 | 35 | 35 | 13 | True |
| 5 | 2 | 0 | 0 | 0 | **False** |
| 13 | 1 | 8 | 8 | 10 | True |
| 17 | 2 | 0 | 0 | 0 | **False** |
| 29 | 2 | 0 | 0 | 0 | **False** |
| 37 | 1 | 26 | 26 | 29 | True |
| 41 | 2 | 0 | 0 | 0 | **False** |

Correlation is 12/12: the leg fails exactly at `p ≡ 2 mod 3`. There `E : y² = x³+2` is supersingular,
so the true Hasse invariant is `0`; the corrupted exponent also yields `0`; `0 ≡ 0`, so C1 still
passes on corrupted input.

**C4's `t₂` leg is a control that cannot fire on a supersingular `E`.** I fixed the curve `x³+2` for
the control without checking that its `E` is ordinary at the tested primes.

## 4. Recording, per rule 4 — no smoothing

This is a basic design error, caught by a safety net. It is not evidence that the control philosophy
works. It is the **same defect class** the `experiment-designer` gate had already flagged in this
session's own v1 spec — *"a control whose expected count is ~0 by construction"* — and I reproduced
it in a control I wrote **in response to** that finding. Prior occurrences on this project:
`feedback_positive_control_forced_zero_offchannel_2026_07_30`, `SELFAUDIT_items1to6` A5. Third
recorded instance of the same failure mode.

Second, smaller defect logged: on the MAIN arm the `t₃` leg reported `False` at all 6 primes. That is
**not** an instrument failure — the main-arm block is forced to zero, so no exponent perturbation can
move it. v2 §3 nevertheless wrote the `t₃` pass condition without excluding the main arm. The MAIN
arm has, in fact, **no C4 leg at all**; `PC` is its only control. v2 §4 said this and v2 §3 did not
follow it.

## 5. Raw output, quarantined (NOT evidence, NOT adjudicated)

From `anew_cartier_audit_v1.log` summary block, reproduced verbatim for the record only:

```
MAIN    (D=3, p=3 mod 4) : N=320 rows (blind 195 / observed 125)
   C1 pass 320/320 | C3 pass 320/320 | C5 pass 296/296 | off-basis image 0
   new-part block NON-ZERO : 0/320  (blind subset: 0/195)
   a-number(new part) distribution : {2: 320}
CONTROL (D=3, p=1 mod 4) : N=287 rows (blind 168 / observed 119)
   new-part block NON-ZERO : 287/287  (blind subset: 168/168)
   a-number(new part) distribution : {0: 287}
PLANTED (D=5, p=3 mod 4) : N=150 rows
   new-part block NON-ZERO : 150/150
PC  planted-control firing rate : 150/150   [need >= 1/3]
C2  control-arm firing rate, BLIND : 168/168   [need >= 1/3]
```

Pre-committed exclusions matched the exclusions actually hit, exactly:
`{(7,x³+7), (7,x³+2x+5), (11,x³+11), (31,x³+x+1), (101,x³+2x+5)}`.

**These numbers are void.** They are listed so that the contaminated sample is identifiable and is
never silently re-used.

## 6. Remedy

`PREREG_anew_supersingularity_reaudit_v3.md`, written before any v3 script is executed:
corrected C4, and a **disjoint sample** (primes and seeds not touched by the v1/v2 runs), so that the
corrected control runs on unread data and the result can carry a primary claim.
