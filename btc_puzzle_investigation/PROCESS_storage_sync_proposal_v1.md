# Storage / sync proposal — for review

**Date:** 2026-08-08 · **Status:** PROPOSAL, not adopted · Author: session (Claude)
**Trigger:** P13 grade-lag (master v6 says `[PROVED]`; newer RESULT downgraded to
`not-[PROVED]`/`[UNREVIEWED DERIVATION]`) + user question "are we keeping things in too
many places and not syncing them."

---

## 1. Diagnosis (measured, not guessed)

| layer | where | count | failure |
|---|---|---|---|
| leaf / findings | `RESULT_*`, `PREREG_*`, `ANALYSIS_*`, `AUDIT_*` | 208 + 149 + 15 + 18 | the ASSET — keep all |
| summary | `POSITIVE_FINDINGS_MASTER_v1..6`, `BRIDGE_..._COMPENDIUM_v1..2`, HANDOFFs | ~9 | hand-copied grades go stale |
| index | `btc_puzzle_INDEX.md` (3114 lines) | 1 | not an index — a 3rd compendium |
| memory | `memory/*.md` + `MEMORY.md` + nested `*_INDEX.md` | 193 + 2 | pointers duplicate grade/status |

**Root cause — one atom, four copies.** A claim's *grade + scope* (e.g. P13 `Hom(E,A_new)=0`,
CAP `|V(a)|≤2√p`, 120°-anchor, amicable) is re-stated by hand in the RESULT, the MASTER, the
INDEX, and a memory pointer. Update the RESULT and three copies silently drift. That is the
P13 failure exactly.

**Two aggravators:**
- **No CURRENT marker.** 30/208 RESULT files have a status header; ~20 lineages have 2–4 live
  versions. "Which version is authoritative" is not greppable → summaries cite stale versions.
- **The consolidation reflex manufactures the drift.** Every hand-written v5→v6 master / H3→H4
  handover is a lossy re-copy. `DEGRADATION_AUDIT_H3_TO_MASTER_v1.md` already measured the cost
  (5 live frontiers → 0). New masters are minted faster than they can be kept consistent.

**NOT the problem:** the 208 leaf files. Deleting findings is the suppression trap (CORE BIAS).
Leaf files are cheap and are the record of what was tried. Leave them.

---

## 2. Target end-state

A claim's grade+scope lives in exactly **TWO** places:
1. its **authoritative RESULT file** (the derivation), and
2. **one ledger row** (the roll-up).

Everything else (master narrative, index, memory) **links** to those and never re-states a
grade. That is the minimum that kills the P13 failure mode.

---

## 3. Options (pick any subset — ranked by leverage ÷ disruption)

### S2 — Grade-drift detector  ⭐ cheapest, do first
A script `check_grade_sync.py`: for each grade tag in a MASTER, find the RESULT file it cites,
read that file's grade for the same claim, flag mismatches. Run before promoting any master.
This is exactly what would have caught P13 automatically. **Detector, not a reorg — zero
disruption.** Makes the existing `compile-diff` gate a runnable check instead of a subagent
judgment call.

### S1 — One grade ledger = single source of truth  ⭐ highest structural leverage
`CLAIMS_LEDGER.md` (or `.tsv`): one row per *named* claim —
`claim-id | grade | one-line-scope | authoritative-file:line | date`.
Rule: **grades live ONLY here.** Master/index/memory cite `claim-id` and link; they never
re-state a grade. Start with the ~15–30 live/load-bearing claims, not all 208. Collapses "the
grade" from 4 copies to 1.

### S3 — CURRENT/SUPERSEDED lifecycle header
One-line header on versioned leaf files: `STATUS: CURRENT` or `STATUS: SUPERSEDED-BY <file>`.
Then "which version is authoritative" is greppable and the ledger/detector can cite the current
one mechanically. Optional: move SUPERSEDED versions to `archive/` so the working dir shows
only current.

### S4 — Demote the 3114-line "index"
Either (a) regenerate `btc_puzzle_INDEX.md` mechanically as a pure one-line-per-file pointer
list (derived ⇒ can't go stale), or (b) if it carries synthesis content, **rename** it
`..._COMPENDIUM.md` so it's honest that it needs maintenance. An index you can't trust is worse
than none.

### S5 — Freeze the "mint a new master" reflex
Stop hand-writing v7. The master becomes a *view*: either generated/diffed from the ledger +
current leaf files via `compile-diff`, or at minimum it carries **no grade that isn't a link to
the ledger**. Archive v1–v5; keep v6 as the last hand-written one.

---

## 4. Recommended minimal starter (if you want just one move)

**S2 + S1 together.** The detector (S2) stops the bleeding today; the ledger (S1) removes the
cause. S3/S4/S5 are hygiene that make both cheaper to maintain. Everything else in the record
stays exactly where it is.

## 5. What this does NOT touch
- No findings deleted. No RESULT/PREREG/ANALYSIS files moved except superseded versions (S3, opt).
- Existing gates (`compile-diff`, `experiment-designer`, `citation-verifier`) unchanged — S2
  complements `compile-diff`, it doesn't replace it.
- Memory discipline unchanged; memory pointers just point at the ledger for *status* and at
  RESULT files for *detail*, instead of restating grades.
