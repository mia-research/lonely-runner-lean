# `n = 11` AP Dependency Ledger

**Date:** 2026-03-30
**Outcome:** `B. n = 11 not yet proved from this corpus`
**Audit scope:** canonical AP route only

## Classification Key

- `already theorem-grade and dependency-clean`
- `theorem-grade but needs internalization into one final document`
- `not theorem-grade`

## Load-Bearing Dependencies

| Item | Source | Classification | Audit note |
|---|---|---|---|
| Bounded-ratio case `e_10 / e_1 <= 10` | `lrc_n11_ap_paper_v22.md`, Sections 2-9 | `theorem-grade but needs internalization into one final document` | The explicit witness `t* = 10/(11 e_10)` route is self-contained in the paper. No concrete blocker was found in this pass. |
| Irrational-ratio case | `lrc_n11_ap_paper_v22.md`, Section 10.2 | `theorem-grade but needs internalization into one final document` | The Weyl/equidistribution route looks structurally standard, but the final proof bundle would still need a cleaner standalone statement of the torus reduction. No blocker found here. |
| Static Core Theorem | `lrc_n11_static_core_theorem_v1.md` | `theorem-grade but needs internalization into one final document` | This note is a wrapper theorem. It appears sound as a package, but it still imports its real work from Theorem U and Lemmas S1/S2. |
| Theorem U (`sigma_2 = +1`) | `lrc_n11_universalincompat_v3.md` | `theorem-grade but needs internalization into one final document` | No concrete unresolved dependency was identified in this audit. The note still contains packaging roughness and some inherited references to earlier versions, but no explicit blocker was found before the phase-uniform step. |
| Lemma S1 | `lrc_n11_lemma_s1_runner2_elimination_v1.md` | `already theorem-grade and dependency-clean` | Short exact-rational lemma. The proof is closed and local. |
| Lemma S2 (`sigma_2 = -1`) | `lrc_n11_lemma_s2_proof_v2.md` | `theorem-grade but needs internalization into one final document` | The note is a real theorem container with exact arithmetic. No concrete blocker was found in this pass. |
| W_ref window geometry | `lrc_n11_periodicity_lemma_v1.md`, lines 20-40 | `theorem-grade but needs internalization into one final document` | The definition of `W_ref` and the fact that runner `e_1` is isolated there are straightforward. This is not the blocker. |
| Lemma P (width invariance) | `lrc_n11_periodicity_lemma_v1.md`, lines 44-50 | `already theorem-grade and dependency-clean` | The width computation is exact and local. |
| `W_1` argument | `lrc_n11_w1_argument_v1.md` | `not theorem-grade` | The file labels itself as mixed computation plus analysis, uses `Proof sketch`, contains a `Key Caveat and Open General Case` section, and includes informal `wait...` reasoning. It cannot serve as a final proof dependency. |
| Lemma C (phase-independence of the UB cascade) | `lrc_n11_periodicity_lemma_v1.md`, lines 54-88 | `not theorem-grade` | The note proves width invariance but does not fully prove phase-conjugacy of the slot incidence structure. Chain B and PSM are asserted as analogous, and the Chain A proof still contains a live `wait...` sentence. |
| Theorem PU / Theorem PU_{-1} | `lrc_n11_periodicity_lemma_v1.md`, lines 92-132 | `not theorem-grade` | Both theorems rely on Lemma C to transfer the cycle-0 static core to arbitrary pacemaker sub-cycles. That transfer is exactly the unresolved step. |
| Theorem W_ref | `lrc_n11_ap_paper_v22.md`, lines 673-705 | `not theorem-grade` | This closure depends on Theorem PU and still cites `lrc_n11_w1_argument_v1.md` as a source file. It also contains arithmetic/packaging slips, so it is not the minimal clean theorem container. |
| Final Theorem C | `lrc_n11_ap_paper_v22.md`, lines 710-722 | `not theorem-grade` | Blocked only by the failure of Theorem W_ref in the commensurable large-ratio case. |

## Minimal Blocker

The smallest unresolved load-bearing claim found in this audit is:

> **Phase-Uniform Static-Core Transfer Theorem.**
> For every commensurable large-ratio EFN configuration with `a_1 < 1`, and every pacemaker sub-cycle `W_ref[m]` contained in `W_ref = [1/(11 a_1), 10/(11 a_1)]`, the cycle-relative bad-interval arrangement of runners `2,...,10` satisfies the same obstruction alternatives as in cycle `W_0`. Equivalently, whenever runners `2` and `9` leave a right gap in `I_9^(m)`, either that gap survives or one of the PSM / Chain A / Chain B obstructions yields positive good fraction in some slot `I_k^(m)`.

Once that theorem is proved rigorously, the current AP route can close Case `R>` and therefore close `n = 11`.

## Packaging Findings

- `lrc_n11_static_core_theorem_v1.md` still says it depends on `lrc_n11_universalincompat_v1.md`; the canonical file is `lrc_n11_universalincompat_v3.md`.
- `lrc_n11_ap_paper_v22.md` still points readers to `lrc_n11_lemma_s1_proof_v1.md` in one place, while the canonical note is `lrc_n11_lemma_s1_runner2_elimination_v1.md`.
- `lrc_n11_ap_paper_v22.md` Section 10.6 labels Theorem R1 as a proof sketch and still treats `lrc_n11_w1_argument_v1.md` as part of the dependency chain.

