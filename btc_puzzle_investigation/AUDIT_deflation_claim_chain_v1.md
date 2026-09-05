# AUDIT — the "deflationary for the leak hunt" claim chain

**Date:** 2026-08-01. **Target:** my own summary statement, and every link feeding it.
**Trigger:** user challenge that the statement carries overclaim. It does — 4 defects, one of which
**partially reverses** the conclusion and revives a spec I withdrew an hour earlier.

The audited sentence:
> *"This is deflationary for the leak hunt. 'The 120° law is a secp-specific signature' is gone as a
> lead. The spine already names this divergence … and today moved both, in opposite directions."*

---

## 1. The chain, link by link

| # | link | verdict |
|---|---|---|
| L1 | `e₂ = e₁² − εp` measured at generic `j`, 30/30 | **SOUND, scoped** |
| L2 | `e₃ = εp·e₁`, `e₄ = p²` forced by closure + purity; closure verified `j`-independent | **PARTIAL — purity is untested at generic `j`** |
| L3 | ⟹ the 120° law holds at generic `j` | **NOT ESTABLISHED** (inherits L2) |
| L4 | ⟹ the 120° law is not `j=0`-specific | **OVERSTATED** — only the `e₂` relation is |
| L5 | ⟹ "secp-specific signature" is gone as a lead | **OVERCLAIM** (repeat of an error retracted the same day) |
| L6 | ⟹ deflationary for the leak hunt | **OVERCLAIM** — global closure claim with no named object |

## 2. D-1 (decisive) — L2/L3: purity is verified at `j=0` and UNTESTED at generic `j`

The asymmetry I glossed over:

| | `e₂` relation | purity `\|α\|² = p` | 120° at eigenvalue level |
|---|---|---|---|
| `j = 0` | measured, 22 primes | **verified** numerically, 160-bit, `p = 43,67,127` (`ANALYSIS_n1_charpoly_collapse_v1.md` §3) | **verified directly**, same source |
| generic `j` | measured, 30 curves | **never tested** | **never tested** |

At generic `j` I measured **only** `e₂`. `e₃` and `e₄` were *inferred* as forced — but forced
**given purity**, which is `[CITED]`/untested there. So L3 runs through an untested premise **on the
very arm that needs it**. That is structurally the same defect the gate flagged as M-5, committed in
the opposite direction: M-5 said T3/T4 are forced *given* the premises; I then treated the premises
as available at generic `j` without checking.

**What is actually established: the `e₂` relation is not `j=0`-specific.** Not the 120° law.

### ⇒ The withdrawn spec was MISLABELLED, not worthless — and this revives it

The gate said so explicitly: *"What T3/T4 actually test is purity at every embedding … That is a
real and worthwhile object; it is not the object §1 names."* I read that as "the spec is void" and
withdrew it wholesale. Correct reading: **the spec's statistics are right and its stated object was
wrong.** Running T3/T4 at generic `j` is exactly what upgrades L4 from the `e₂` relation to the 120°
law — because at generic `j`, T3/T4 are *not* forced in any way I have verified: purity is untested
there, so they are a genuine test of it.

`PREREG_deflation_120deg_generic_j_v1_DEVIATIONS.md` §3 already anticipated this
(*"a future spec … must name a different object: does purity at every embedding hold at generic `j`"*)
but treated it as optional future work. It is not optional — **it is load-bearing for a claim I
already made.** All 13 gate defects still require repair before any such run.

## 3. D-2 — L5: "gone as a lead" repeats an error retracted the same day

`CORRECTION_deflation_overreach_v1.md` §2(c), written ~1 h earlier, states: *"generic ⊅ says nothing
about secp256k1 — secp has odd prime `n`, so it lies INSIDE the class."* The audited sentence then
re-commits it. Even granting L3–L4 in full, what dies is narrower: *"the 120° law is evidence of
special `μ₃`/CM structure in secp"*. The law itself remains true of secp and is not "gone".

## 4. D-3 — L6: a global closure claim with no object, class, power, or scope

"Deflationary for the leak hunt" names no object and no class of observable. Per `CLAUDE.md`
(*burden of proof on the closure*) that is an overclaim at the PROVED bar. "The leak hunt" is not an
object; it is the whole investigation. This is
`feedback_negative_bias_enlarge_nulls_2026_07_17` — a scoped result enlarged into a verdict — and at
maximal width. Third instance today of the same failure mode
(§4 of the B check → corrected; the `μ₆` "successor object" → retracted; this).

## 5. D-4 — "today moved both, in opposite directions" is factually wrong

Today touched **only** the structural side. No cryptographic statistic was computed, no C-side or
interval object was run. The sentence asserts a movement on the cryptographic side that did not
occur. The spine's divergence (§7) is real and pre-existing; today did not move both arms of it.

## 6. D-5 — a smaller one, same family: "zero new structure"

My priorities message said the session yielded *"three corrections and zero new structure."* False:
the corrected general law `e₂ = e₁² − χ₂(−1)·p` (a branch the record had wrong) and the exhibited
factorization `D(T) = T² + ζ₃e₁T + χ₂(−1)pζ₃²` are both new structure. Negative-bias again —
undercounting positives on a disliked-direction session.

## 7. Corrected statement

> The **`e₂` relation** `e₂ = e₁² − χ₂(−1)p` is not `j=0`-specific — measured, 30 curves with
> `Aut = μ₂`, `p ≤ 211`, `p ≡ 1 mod 3`, odd cyclic `n`, self-chosen sample, firing control fires.
> Whether the **120° law** is likewise non-specific is **NOT established**: it needs `e₃`/`e₄` at
> generic `j`, which need purity, which is untested there. What weakens is one reading —
> *"the 120° law is evidence of special `μ₃`/CM structure in secp"* — not the law, not its use, and
> not any avenue. No claim about "the leak hunt" is supported by anything measured today.

## 8. What survives of the strategic read

The **#26 reframing survives**, because it depends only on L1: the `e₂` relation — which *is* the
open link (`ANALYSIS_n1_charpoly_collapse_v1.md` §2: *"the open item is therefore prove
`e₂(a) = e₁(a)² + p`"*) — holds at `Aut = μ₂`. So the target is a general identity and the
`μ₃`-specific proof machinery (Stickelberger) is aimed at structure that is not carrying it. That
inference needs no purity premise and no claim about the 120° law.

The **priority ordering survives**; the *justification* for it does not. #26 is first because it is
better-posed, **not** because anything was deflated.
