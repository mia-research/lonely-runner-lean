# Order 8 working rules (v3, 2026-10-05). Supersedes v2 (kept unchanged); only rule 7 differs. Read before EVERY reply on n=8.

Source: each rule cites owner messages by id in `docs/n8/OWNER_INSTRUCTIONS_EXTRACT_v1.md` (101 owner messages, 2026-10-02 03:44Z to 2026-10-04 05:34Z; verbatim, script-checked). Earlier sessions (before E290) were not read. A rule marked **[mine]** has no owner message behind it in that range and is unconfirmed; the owner strikes or keeps it.

Every n=8 reply opens with `Rules:` and the rule numbers the step touches. Every draft reply, subagent brief and log entry goes to `rules-auditor` before it is sent.

## The two goals (M051, M055, M056, M080, M086, M088, M092)
G1. Understand the cascade: map what it does and why, in the framework's own objects, for any arrangement. Not a proxy.
G2. Catalogue arrangements by outcome (how the cascade finds the isolation) to show a finite set, with d_min and d_max taking care of the continuous values (M060) and scale taken care of by the AP/grid (M075).
Order of work: pattern, then rule, then mechanism, then proof; each step matters (M060, M061, M089). Staying on the mapping when asked to map; no jumping to another topic (M039).

## Existence frame (M000, M002, M005, M018, M036, M038)
1. Existence of the isolation is already proved at the AP/grid. The cascade converts any arrangement into an AP/grid arrangement plus a deviation (M036). Changing a speed away from the AP/grid does not destroy the isolation; it **displaces** it, and the cascade shows where and why (M005, M018, M038). What is to be shown is that this displacement is forced.
2. Isolation is individual per runner: a runner needs the others at distance at least 1/8; if its two neighbours are known, the other six lie anywhere in the other 6/8 of the circle (M001, M002).
3. Freezing some runners and moving the others does not change the isolation point of the frozen ones (M037).
4. Two runners can never be at the same speed: however close, the faster separates from the other every revolution; this is the structure that rules out a limit with no isolation, and it is already proved in Lean elsewhere (M005).
5. **No runner is ever stationary or at speed 0** (M015, M016).
6. Banned as imported: other frameworks' obligations such as density or coverage (M051, M009). Before using any step ask whether the cascade needs it or whether it is being imported (M009, M020). A missing step the cascade itself does not have is not a gap.
7. The window-floor idea: if the cascade does not need the floor, the floor idea is wrong (M091). Still banned as the SHAPE of an existence argument: supply against demand, termination or move budgets, caps, a uniform formula, covering as a statement form, window floors or ceilings, any bound with slack (the AP has none). **Relaxed 2026-10-05 (owner, "we will relax rule 7 for this approach, as long as it is flagged it is provisional"):** a counting step used as a TOOL (pigeonhole, residue counts, equally spaced points against an arc), as `MANUSCRIPT_v20` section 0 allows, is permitted for the direct whole-number / case-list approach, provided every use is tagged **[PROVISIONAL: counting tool]** at the step, with the claim it supports named. The tag is required in replies, log entries and briefs; an untagged counting step is a breach. Provisional means the owner may withdraw the relaxation and the steps resting on it.

## Method
8. Check proxy versus cascade whenever stuck, and before every new test (M043, M077, M088). A finite union of polyhedral cells is a proxy until tested through the cascade; exceptions are understood, not ignored (M045).
9. What the cascade does that is not understood is the next test; "what it doesn't show" is the next target (M040). Keep testing until no arrangement change is unknown to you (M040).
10. Test new arrangements, not restatements: d_min handles transitions, the AP/grid handles scale (M075). Log what looks like a different arrangement but is not (M044). Look for outcomes that are d_min/d_max at another scale, or repeats (M064, M071).
11. Arrangements are suggested by the cascade's results, not by my theory; if the theory and the results disagree, the theory is adjusted (M062, M043). Hold ideas loosely (M045).
12. Search clever, not dumb (M062); jitter, perturb, permute to explain (M066, M067).
13. Look at the full record before acting: all of `docs/n8` and the Lean library, not a sample and not the later entries only (M006-M008, M053, M082). Check for something to reuse before rebuilding (M028). Memory and the prompts above are read, not skipped (M053).
14. Full data sets, not half sets (M054). The cascade is deterministic: nothing is random (M049).
15. No floating point, no slack presented as fact (M063). **[mine, with E337]** exact Fractions or "undecided"; floats steer only.

## Lean (M003, M004, M022, M023, M024, M026)
16. Lean is paused here (M026; owner E222 in the log: not until the map is complete). When Lean is in use: reuse existing proofs; add nothing wrongly conceived (M003); Lean needs correctness, not a picture of what it "looks like" (M022, M023); reason through the code (M024).

## Conduct
17. Efficiency of tokens is not a concern; tokens are plentiful; do the work properly and keep running autonomously with subagents (M008, M042, M046, M047, M056, M059, M072).
18. Do not claim what is not done: "full mechanism" and similar words on a partial result are banned (M094; log E379). **[mine]** grade claims [P] [L] [T n/N] [TREE] [OBS] [OWED].
19. Consolidated documents are brief, one line per finding in the form "E355 found x and y", not explanatory (M081).
20. Hand-overs before context compaction are written (M048); this file and the extract are the first things read after one.
21. **[mine]** No new proof-scaffolding or architecture documents; no unrequested "one thing to think about"; never overwrite a versioned file; Lean files and the foreign gate untouched; subagent output and system notifications are not the owner.
