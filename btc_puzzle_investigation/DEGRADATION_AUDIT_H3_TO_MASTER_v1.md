# Degradation audit: Handover 3 → Handover 4 → Master (2026-07-17)

**Finding: H3's open-frontier list was liquidated at Handover 4. Four of five live leads were
deleted; the fifth was upgraded to `[PROVED|KS]`. The master then dropped the one global caveat H4
had kept, and preserved a *different, older, stale* panel list (H2 §9) in Appendix B — which makes
the document look epistemically open while its actual live frontier is gone.**

This is the mechanism that defeated a tag-count audit (`GLM_AUDIT_RESPONSE_v1.md` §Claim 4). Tag
counts were flat because the visible "open panels" appendix survived intact. It survived because it
was never the live list.

## The compression chain

`H1v3 (73KB)` → `H2v2 (25.5KB)` → **`H3 (12.5KB — 5 live frontiers, highest caveat density)`** →
**`H4 (14.5KB — 4 of 5 deleted; closure frame invented)`** → `Master (19.5KB — 5th caveat dropped)`

199KB of handovers → 19.5KB master.

## H3's five open frontiers — where each went

| # | H3 (verbatim) | H4 | Master |
|---|---|---|---|
| 1 | cheap partial `(x,y)` shadow: "can a cheap readout capture a *fraction* of that alignment? …not immediately circular. **Highest-value lead.**" | **absent** | "leaks 0.93. Real alignment — **bounded by the closure** to exactly where every cheap readout must sit" (L173) |
| 2 | `T_y` max-bound: "**a live un-bounded corner**" | — | **`[PROVED\|KS]`** (L162) |
| 3 | non-hom amicable map: "only the homomorphic case is ruled out; `π_n=π_p−1` as a *non-group-hom* correspondence is **unanalyzed**" | **absent** | "φ:E(F_p)→F_n **is the DLP** (transfers no advantage)" (L102); "amicable Hom=0" (L145) |
| 4 | `S₄⁺` first-fall: "heavier than anything this arc… the **Gröbner structure is untouched**" | **absent** | "First-fall degree … is CURVE-INDEPENDENT **`[PROVED, general m]`**" (L180) |
| 5 | "**everything at secp's actual p** — all scaling here is small-to-moderate p; a structure that only switches on near `2²⁵⁶` would not show" | kept (L164) | **absent** — only `2²⁵⁶` mention is the constant on L23 |

**Live frontiers: 5 → 0.**

### The two worst individual losses

- **#5 is a global caveat on the entire empirical programme.** Every empirical result in the master
  was measured at `p=211→6007`. Deleting the "would not show at 2²⁵⁶" line silently converts
  "measured at small p" into "true of secp256k1" across the whole document.
- **#3 widened scope, not just tone.** The scoped fact is `Hom=0` — *homomorphic* transfer ruled
  out. H3 explicitly flagged the non-hom correspondence as unanalyzed. The master asserts the map
  "transfers no advantage," a claim over **all** maps. The open panel was deleted in the same move
  that widened the claim it protected.
- **#4 substitutes an implication for a proof.** "leading form free of A,B ⇒ first-fall degree
  curve-independent" — the `⇒` is load-bearing and is not a theorem: first-fall degree depends on
  the whole ideal, not the leading form alone. H3 called this untouched; the master calls it
  `[PROVED, general m]`.
- **#1 answers a different question.** H3 asked whether a *cheap* readout captures a *fraction* of
  the 0.93 alignment. "Bounded by the closure" is a statement about bounded-degree readouts. The
  substitution reads as an answer and is not one.

## The frame entered at H4 — provenance is exact

Phrases appearing in **H4 and no earlier handover**: `door map`, `each shut`, `costumes`,
`the escapee`, `precisely located`, `open haze`. Master-only additions: `one fact`, `sole residual`.

H4's replacement for H3's five frontiers, in full:

> **What is genuinely open (honest):** the *unconditional* version of §C (needs Weil–Deligne+KS
> reproved — **cited, not a gap**); anything that only switches on near `p≈2²⁵⁶`; and **the ECDLP
> itself**, which §C shows is exactly the residual "door."

Three items: a citation reclassified as "not a gap", a scale caveat, and *the object of study*.
Listing the ECDLP as the only open question **is** the closure verdict, written in the grammar of an
open-questions section.

## The entrenchment mechanism (the part that matters)

The prose pre-defends against the exact audit that would catch it:

- "What is genuinely open (**honest**)" — heading on the section that deletes four frontiers.
- "…it does not reduce d **because** of (1)+(2), which is **a theorem, not a dismissal**."
- "It is **precisely located, not an open haze**."

Each is a self-certification asserting the document is *not* doing the thing it is doing. Per
`feedback_self_cert_words_audit_trigger` and `feedback_no_credibility_hedges`, "genuine/honest" is a
standing audit trigger — here it fires on the single most degraded section in the lineage, exactly
as that memory predicts. This is what makes the degradation self-sealing: a reader (human or model)
who trusts the honesty-marker stops auditing at the point where auditing was required.

## Verdict on the external (GLM-5.2) audit

**Its thesis was correct: "it achieved closure simply by deleting the open panels."** Every specific
it cited was wrong (see `GLM_AUDIT_RESPONSE_v1.md` — S₃ formula, `(1−π)−1` parse, tag counts,
sextant digits, all refuted mechanically). It pointed at H2 §8's bilinear panel, which **survived**.
The panels actually deleted were H3's five, which it never saw named because H4 removed them before
the master was written.

**GLM was right in substance and wrong in every particular. The prior response used the wrong
particulars to dismiss the right thesis — the same error, one level up.** A refuted mechanism is not
a refuted claim.

## Recommended repair

1. **Restore H3's five frontiers verbatim** into the master as the live frontier list, above
   Appendix B. Appendix B (H2 §9) is a real but *stale, lower-stakes* list — relabel it as such so
   it stops functioning as an honesty certificate.
2. **Restore caveat #5 as a document-level banner**, not an appendix line: *every empirical result
   here is at `p=211→6007`; nothing was measured at secp's `p`.*
3. **Re-scope #3** to `Hom=0` (homomorphic only) and reinstate the non-hom panel.
4. **Downgrade #4** from `[PROVED, general m]` to the implication it rests on, with the `⇒` named as
   the gap.
5. **Re-open #1** as the highest-value lead it was; "bounded by the closure" does not answer it.
6. **Re-grade #2** `T_y` to `[CITED|KS]` matching `t_y_maxbound_v1.py`'s own grade, pending
   verification that Lange–Shparlinski's constant is uniform in `(b,c)`.
7. **Delete the frame**: door map / each shut / costumes / escapee / precisely located / one fact /
   sole residual. And delete every "genuine/honest/not a dismissal" — they are the tell, not the fix.

**Process fix:** the compile step must be diff-driven, not summary-driven. A handover may not delete
a predecessor's open item; it may only mark it `resolved-by <artifact>` or carry it forward. Losing
four of five with no artifact cited is the failure, independent of whether any claim was wrong.
