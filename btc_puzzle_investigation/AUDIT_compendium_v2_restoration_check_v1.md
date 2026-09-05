# RE-AUDIT — did COMPENDIUM_v2 restore the losses the v1 audit named?

**Date:** 2026-07-25 · Checks `BRIDGE_PROGRAMME_COMPENDIUM_v2.md` against the loss report the
`compile-diff` agent produced on v1. **Mechanical grep check, evidence shown** — this is a *named-item
restoration* check, **not** a fresh full audit (see scope caveat at the end).

## Why this file exists (and is not itself a self-certification)

The `compile-diff` re-audit of v2 was spawned but **hung** (~9h, no completion; harness lost the
process, killed). Rather than assert v2 is clean on my own say-so — the exact defect v1 committed —
this file records the **decidable** check I can run: does each item the first audit named as
DROPPED/WEAKENED now appear in v2? Per
`memory/feedback_verification_claim_needs_artifact_2026_07_24.md`, a completeness claim needs a named
artifact; **this is that artifact**, and it states its own limits.

## Result — 22/22 named items restored (grep-verified)

| item (first audit's finding #) | v2 | evidence |
|---|---|---|
| #11 B2 citation: "NOT IR Prop 9.3.3" | ✓ | line ~72 |
| #11 B2 citation: Sun *Acta Arith.* 84 (1998) 291 | ✓ | " |
| #11 B2 identity check `3659/3659` | ✓ | " |
| #12 `D=−12` counterexample `6028/6028` | ✓ | §4 corrections |
| #13 `D≡5 mod 8 ⇒ odd order` false, `p=7` orders `{3,4,7,9,12,13}` | ✓ | " |
| #14 Euler/Gauss attribution | ✓ | " |
| #14 "Rajwade" replacement | ✓ | " |
| #15 K0 control `4000/4000` | ✓ | §1 control table |
| #15 K1 control `1200/1200` | ✓ | " |
| #15 K2 `0.3395` vs `0.3250` | ✓ | " |
| #16 ord_n "Controls fire in every table" | ✓ | §1 |
| #17 positive control `0.1920` vs `0.1185` | ✓ | §1 |
| #18 reduction `n ≡ p (mod U)` | ✓ | §0 |
| #18 reduction abelian/non-abelian | ✓ | §0 |
| #19 ord_n DEV5: 40–64 bit rows carry no weight on the rate law | ✓ | §4 deviations |
| #20 cubic_sextic DEV2: `e_λ(ω)` tested not assumed | ✓ | §4 deviations (lines 170–171) |
| #21 `N=6790` H-sextic sample | ✓ | §2 |
| #21 M1 power `29.5σ` | ✓ | §3 table |
| #21 M1 matched-control `27.5σ` | ✓ | §3 table |
| #21 `w=2` discriminant list `−11/−19/−43/−67/−163` | ✓ | §3 table |
| #21 `h=2` discriminant list (ten) | ✓ | §3 table |
| #21 ord_n(2) selection bases `2,79,137,199,367` | ✓ | §2 |

Both of v1's false self-certifications are **gone**: "compile-diff was run before this file was
promoted" (absent) and "none dropped" (now quoted only as the documented v1 error). No **new**
self-certifying completeness claim was found by an `-iE` scan for `all…carried / none dropped / fully
consolidated / was run before`.

## Scope — what this check does NOT establish

- It confirms the **22 items the first audit named** are present. It does **not** re-derive the item
  list from the ten predecessors, so an item **both** audits missed would not be caught here.
- It does **not** re-check for **new** WEAKENED items (a figure present but softened) beyond the
  self-cert scan — a full independent re-audit would. That re-audit **hung and was not completed.**
- Grep confirms presence of a string, not that its surrounding claim is graded correctly. Grades were
  checked by eye against the two AUDIT files, not mechanically here.

**Honest status:** v2's named losses are restored (this file is the evidence). v2 has **not** had a
completed fresh full audit; the one attempted hung. That caveat stays in v2's own footer.
