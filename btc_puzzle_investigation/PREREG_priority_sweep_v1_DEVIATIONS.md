# DEVIATIONS — `PREREG_priority_sweep_v1.md`

*2026-07-24. Filed with `RESULT_priority_sweep_v1.md`.*

## D1 — databases were not queried as separate D1–D4; `WebSearch` aggregates them

The spec froze D1 Google Scholar, D2 arXiv, D3 zbMATH, D4 MathSciNet (or Semantic Scholar + Crossref
substitute) as **separate** databases with per-database hit ledgers. The available instrument
(`WebSearch`) returns an **aggregate** over Scholar / arXiv / Semantic Scholar / publisher sites in a
single query, so per-database hit counts were not separable and **MathSciNet (D4) was not directly
accessed**. The frozen substitute (Semantic Scholar + Crossref, surfaced inside the aggregate)
applied. **Effect:** the coverage is real but its *depth per database* is not auditable as the spec
intended; this **lowers the confidence of the NO-PRIOR-LOCATED verdicts**, which is why the result
states them as *bounded searches*, never "novel." The gate (3 positive controls recovered) still
passed, so the aggregate instrument demonstrably finds published work.

## D2 — ~3 variants per claim via aggregate search, not ≥12 (3×4) discrete queries

The spec's power floor was ≥3 variants × D1–D4 = ≥12 queries per claim. Because `WebSearch` is an
aggregate (D1), each executed query already spans multiple databases, so ~3 aggregate queries per
claim were run, plus targeted `WebFetch` on decisive hits. This meets the *variant* floor but not the
literal *variant × separate-database* product. Recorded as a coverage reduction.

## D3 — ⚠ HALF THE VERDICTS WERE PRE-KNOWN; the sweep was partly confirmatory, and I over-ranked it

Flagged by the user mid-run, and correct. For **5 of 10 the grade was known before any query** (#8
Parseval — proved *this session*; #6-framework — the record's own text; #1/#2/#10 — textbook), and the
prereg pre-committed #6/#8 to FOUND "by construction." I had ranked this item **#1, "highest value,
lowest risk."** The lowest-risk framing was right; the highest-value framing was **not** — half the
list was confirmatory bookkeeping. The genuinely new content was 5 items (#3 actionable, #5/#7/#9
specific papers, #6-instance), and the one nugget (#3 Berndt–Evans → `(†)`) was reachable directly
without a 10-claim sweep. **Lesson (recorded, recurring): "low overclaim risk" is not "high value,"
and I justified the #1 ranking by framing confirmation as discovery.** The `RESULT §1` headline now
carries this accounting.
