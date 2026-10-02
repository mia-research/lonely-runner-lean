# compile-diff: MECHANISM_MAP_v4.md against v3 and log E220–E268 (condensed)

2026-10-02. Run by the `compile-diff` agent on the first draft of v4 (inputs: v3, v4, log E220–E268; no session narrative).
**Headline:** v3's text carried byte-identical except the header and the appended `(v4)` text in C1 and C14 (16 lines altered, none
deleted); 0 grades moved up without an artifact; 0 re-claims of a retracted statement; every E220–E268 number checked against the log
matched except one (B2). The first draft had 9 losses (A), 5 widened scopes (B), 3 correction gaps (C) and 4 internal conflicts (D).

**Findings and their repairs (all applied to v4; the phrases verified present by grep after the repair):**
- A1 `L₀` ladder verified-not-proved (31,066 of 31,066): lost. Repaired: §9 C23, §2 J, §8, C18's withdrawals 4–5.
- A2 E262's result (588,559 six-sets, 58, first-rule counts 30/19/5/4, "not a mechanism"): lost. Repaired: §2 K E262 bullet.
- A3 E266's "needs `EightResidual`?" (landing at `c` in 2,493 of 12,000 random): lost. Repaired: Q9.
- A4 owed `WindowConstantFive`, `SyncBlockN` (288,288): lost. Repaired: §2 J, §8.
- A5 E253/E254 sampling artefact (`c = 1000`; E60's reach): lost. Repaired: §9 C21.
- A6 E242 ruling and plan (step 4 "formalise" under the Lean hold): lost. Repaired: §0.
- A7 D3's graded result (86,301 sets; 0 failures): lost. Repaired: §2 J.
- A8 E230 withdrawals 4 and 5 not enumerated. Repaired: F18, C18.
- A9 smaller: E252 R5 (`max ĝ ≥ 1/3`, the four triples), E255's unit-filtering target and Theorem 6.27, E235's 27/4, C.6/C.7/A.12/B.11, E225's three kinds of laps: Repaired: §2 J, §2 K.
- B1 "no set anywhere with all six" scoped to the populations read. B2 the E243 pair (25,495 of 25,706) and `q ≤ 16` added. B3 R16 scoped to the
  E235/E243 hole configurations; the `q = 2` selection note and the withdrawn reading added. B4 W6(7) carried with its window-shape / cap flag.
  B5 E260's "step not in Lean", E261's depth caveat, nested windows excluded by construction, Q9's `≥ 9c` against data `≥ 25c`, the `f ≥ 4`
  sampling scope: all added.
- C gaps: E230 withdrawals 4–5 (see A8); E262's count correction (A2); the two superseded scripts (`restricted_b_v1` Part 3,
  `slow_flank_mech_v1` Part 3) noted in §10a; E258's withdrawn reading (B3). R17's "retracted" for E260's "547 of 547" now says the
  generalisation is retracted and the count stands as a count.
- D1 the dangling "excision table in §2 K" (no such table) re-pointed. D2 C19's title scoped. D3 stale v3 owed/next-step items marked
  (compile-diff run; `CASCADE_DESIGN_v3` approved E221; §7's v3 paragraph superseded). D4 (b), (c) and "the owner's mechanism" defined.

**Artifacts (checked after the run, by `find`):** every script named in v4 §10a exists (47 names; `TwoWalker_v1.lean` is in the outer repo's `experiments/n8/`, the rest under `LonelyRunner/experiments/`).

**Not repaired:**
Low-weight: Q8 (v3)'s "Design pending" line is overtaken by the v4 Q8 status block rather than edited.
