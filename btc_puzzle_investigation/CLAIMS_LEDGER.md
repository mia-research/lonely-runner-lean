# CLAIMS LEDGER — single source of truth for claim grades

> **[PROVISIONAL — compile-diff gate OWED]** This ledger consolidates grades + caveats from ~7
> predecessor RESULT files and was seeded in a single ungated pass (2026-08-08). Per CLAUDE.md §2
> a `compile-diff` pass is mandatory before a consolidated/summary document is trusted, to confirm
> no open item, caveat, or grade was lost or inflated in the compression. **Owed:** run
> `compile-diff` (RESULT files → these rows); attempted 2026-08-08, not yet run. Until it clears,
> no ledger row may be cited as authoritative over its own RESULT file, and no grade here may be
> promoted. The seed grades are a transcription draft, not a cleared source of truth.

**A claim's grade + scope lives HERE and in its authoritative file, nowhere else.**
Master / index / memory must *link* to a claim-id and never re-state a grade. Drift between this
ledger and the masters is detected by `check_grade_sync.py`.

## Conventions
- **Grade vocabulary** (controlled — the detector ranks these; stronger to weaker):
  `PROVED > VERIFIED > CITED > EMPIRICAL > {CONDITIONAL, UNREVIEWED, PROVISIONAL} > {HEURISTIC, ASSERTED, GAP} > {VOID, CONTAMINATED}`.
  A master asserting a grade *stronger* than the ledger's = an OVERCLAIM (detector exits 1).
- **master-refs** = `file:line` site(s), `;`-separated, where a master asserts this claim's grade
  (the drift targets the detector reads). `—` = RESULT-authoritative only, asserted in no master.
- **anchor** = a keyword that must appear within a few lines of each master-ref. If it does not,
  the pin has drifted under an edit and the detector flags STALE-REF instead of trusting the line.
- **authoritative** = `file:line` whose grade this row transcribes. Update the row when that file's
  grade changes.
- **No pipe characters (`|`) anywhere in a cell** — they break the table parse (use `abs()`,
  `sqrt(p)`, etc.). Column order is fixed; the detector parses it positionally.
- Seed set = the live / load-bearing claims (the audit's + one clean control row, CHI2-4rtp).
  Extend as needed; this is not yet the full claim inventory.

## Ledger

| claim-id | grade | master-refs | anchor | authoritative | scope | date |
|---|---|---|---|---|---|---|
| P13 | CONDITIONAL | POSITIVE_FINDINGS_MASTER_v6.md:185;POSITIVE_FINDINGS_MASTER_v6.md:496 | Hom | RESULT_anew_supersingularity_step3_gap_and_cartier_route_v1.md:208 | Hom(E,A_new)=0 now rests on the §3 UNREVIEWED derivation, not a reviewed proof; kills the homomorphic cover route only. Was [PROVED] in master v6 | 2026-08-08 |
| ANEW-SS | VERIFIED | POSITIVE_FINDINGS_MASTER_v6.md:470 | automorphisms | RESULT_anew_supersingularity_step3_gap_and_cartier_route_v1.md:208 | A_new supersingular at p=3mod4: VERIFIED 287 blind classes + UNREVIEWED Cartier derivation; NOT [PROVED]. "PROVED from automorphisms" is the refuted mechanism (mu4 witness is ordinary) | 2026-08-08 |
| CAP-2rtp | VERIFIED | — | — | RESULT_cap_reducibility_analysis_v1.md:226 | abs(V(a)) <= 2sqrt(p) is a GENUINE GAP; provable bound is 4sqrt(p); 2sqrt(p) = VERIFIED out-of-sample 120 primes, reduced to one monodromy target; NOT [PROVED]; not asserted PROVED in any master | 2026-08-08 |
| CHI2-4rtp | PROVED | POSITIVE_FINDINGS_MASTER_v6.md:177 | Kummer | weil_deligne_character_bound_v1.md:11 | y-sum char bound <= 4sqrt(p) (Kummer sheaf, R=4) and x-sum <= 2sqrt(p) (R=2), Weil-Deligne; the CORRECT provable bound, distinct from the 2sqrt(p) y-sum CAP. Clean control row (master and ledger agree) | 2026-08-08 |
| DEG120-ANCHOR | PROVED | — | — | RESULT_120deg_anchor_from_mlaw_v1.md:160 | 120deg identity exact at the a=0 untwisted-supersingular anchor for all p=7mod12 incl secp; ZERO power over any a!=0 cell; absolute rigidity measured NOT to survive the twist. Anchor only, not the uniform family | 2026-08-08 |
| AMICABLE | PROVED | — | — | RESULT_secp_amicable_pair_v1.md:10 | (p,N_ord) is a CM aliquot 2-cycle for y^2=x^3+7, exact full-scale; curve/CM fact only: no private key, no d-side, no ECDLP consequence; ~1-in-4 CM event, not miraculous | 2026-08-08 |
| BRIDGE-MOV | VERIFIED | — | — | RESULT_anew_bridge_end_to_end_corollary_v1.md:37 | Two-hop A_new-pairing route can match MOV but never beat it; ord identity confirmed 354/354 cells; deduction single-author (VERIFIED not PROVED; was self-graded PROVED in seed pass, corrected). DEPENDS-ON ANEW-SS: closure premise (A_new supersingular at secp) is cited [PROVED] in bridge files 2026-08-06 but was downgraded 2026-08-02; if A_new is ordinary/mixed at secp the gate is void (v2 §5). No attack leverage | 2026-08-08 |
