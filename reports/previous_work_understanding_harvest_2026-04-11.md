# Previous Work Understanding Harvest

Generated: 2026-04-11
Workspace: `/Users/trentpalelei/Desktop/Math Ex`

## Purpose

The earlier Math Ex work is still valuable even where it no longer carries the main proof burden.

Its main value is not:

- unresolved theorem closure,
- stale registry state,
- or old cycle governance.

Its main value is:

- conceptual compression,
- mechanism discovery,
- reusable object language,
- exact finite-window pattern detection,
- and verification methodology.

This note records the parts most worth preserving for understanding.

## 1. The old work already found the right explanatory objects

The strongest conceptual contribution of the earlier all-`n` program is that it repeatedly rewrote different branches into the same small set of objects.

Best sources:

- `reports/proofs/lrc_proof_pack_2026-03-01/lrc_n_all_structure_review_memo_v1.md`
- `reports/proofs/lrc_proof_pack_2026-03-01/lrc_n_all_shared_object_dictionary_v1.md`
- `reports/proofs/lrc_proof_pack_2026-03-01/lrc_master_theorem_synthesis_v1.md`
- `reports/proofs/lrc_proof_pack_2026-03-01/lrc_n_all_forced_conclusion_memo_v1.md`

Durable insight:

- the rational/discrete frontier was not naturally about many unrelated branches;
- it kept collapsing into the same geometry:
  - alpha-state transitions,
  - residue multiplicities,
  - dangerous-set occupancy,
  - coset exposure for non-units,
  - obstruction components / runs,
  - period-summed safe mass.

This is still useful now because it gives a clean language for explaining why older branch notes were often “the same theorem at different resolutions.”

## 2. The old work found a real explanatory split: local instability vs global positivity

The earlier synthesis pass seems to have correctly identified a deep structural split:

- **local exposure / complementarity geometry**
- **global occupancy / period-summed positivity**

Best sources:

- `reports/proofs/lrc_proof_pack_2026-03-01/lrc_n_all_forced_conclusion_memo_v1.md`
- `reports/proofs/lrc_proof_pack_2026-03-01/lrc_n_all_canonical_frontier_map_v1.md`

Durable insight:

- some routes were really local handoff-failure theorems,
- others were really global counting / occupancy theorems,
- and the program got clearer once these were separated instead of mixed.

Even though the later proof chain moved on, this split is still a good mental model for organizing spillover ideas.

## 3. The earlier “elegant sketch” recovered the human-readable skeleton

Best source:

- `lrc_elegant_proof_sketch_v1.md`

Durable insight:

- bounded ratio gives an explicit constructive witness (`Theorem GB`);
- large ratio should be understood as a gap/clumping phenomenon;
- the heavy n=11 machinery can be read as the formal version of:
  - missing slot,
  - pooled blocking power,
  - gap-to-witness translation.

This note is valuable because it recovers the intuitive story that the formal papers can hide:

- AP / bounded-ratio configurations are the clean extremal template;
- clumping or missing-slot behavior reduces effective obstruction;
- coupling/complementary-pairs are not arbitrary inventions, but the formalization of that reduction.

## 4. The finite-window certification work taught us where the mechanisms are robust

Best sources:

- `reports/proofs/lrc_proof_pack_2026-03-01/lrc_case2_d3_batch_summary_n7n11_v2.md`
- `reports/proofs/lrc_proof_pack_2026-03-01/lrc_gap2_multidiv_batch_certify_v1_note.md`
- `reports/proofs/lrc_proof_pack_2026-03-01/lrc_gap2_multidiv_analysis_v1.md`

Durable insight:

- the certification program did not prove asymptotic theorems,
- but it did identify very strong stable patterns:
  - D3 one-divisible packs had zero violations across large template/check sets,
  - multidiv `n=13` packs had zero phi violations across 20k+ exact checks,
  - margins were often much larger than the bare threshold.

So these runs matter not as proof substitutes, but as:

- regime maps,
- conjecture filters,
- and evidence about where obstruction is genuinely fragile versus where it only looked hard symbolically.

## 5. The Case R> investigations found strong dynamical regularity

Best source:

- `reports/investigations/INV-CASE-R-EXT-001/summary_v1.md`

Durable insight:

- the Iterated Left-Entry / containment dynamics were overwhelmingly shallow;
- all 9163 tested configs succeeded;
- containment margins were large;
- extremal depth existed, but extreme persistence was rare.

This matters because it supports a qualitative picture:

- the hard commensurable regime was not chaotic;
- it had a narrow, structured obstruction anatomy;
- witness-finding dynamics tended to terminate quickly.

That is explanatory value, even where the exact route was later superseded.

## 6. The branch-diagnostic sweeps identified low-complexity witness structure

Best sources:

- `reports/proofs/lrc_proof_pack_2026-03-01/lrc_br_witness_classifier_summary_v1.md`
- `reports/proofs/lrc_proof_pack_2026-03-01/lrc_br_sigma_summary_v1.md`

Durable insight:

- many hard-looking tuples still admitted very low-complexity witnesses;
- `k<=2` witness hypotheses were strongly supported in the Case-B sweeps;
- sigma-based classification produced clean invariant buckets with zero structural violations in the sampled ranges.

This is helpful because it suggests the obstruction mechanisms were often lower-rank than their raw case splits made them seem.

## 7. The verification harnesses are reusable methodology, not just evidence

Best source:

- `reports/lrc_n11_verification/README.md`

Durable insight:

- exact symbolic verification and event-complete boundary-set witness search are a strong pattern for future theorem support;
- the important methodological idea is completeness by boundary events:
  isolation status only changes at threshold crossings, so midpoint testing is exhaustive within the chosen window.

This is worth keeping as a standard verification pattern whenever a route gives:

- a finite candidate window,
- rational constants,
- or a chamber/cell decomposition.

## 8. The transport language was a genuine conceptual advance

Best source:

- `lrc_transport_completeness_v2.md`

Durable insight:

- the residue problem can be read as a transport system:
  support is handed off across chamber boundaries, and full obstruction means every residue stays solvent forever.

Even though some specific transport claims remained open in that note, the language itself is strong:

- “persistent full obstruction”,
- “handoff rule”,
- “solvent transport”,
- “support intermittency” for non-units.

That vocabulary is useful because it explains why local transition lemmas and global counting lemmas keep interacting.

## 9. The canonical frontier maps taught an important discipline

Best source:

- `reports/proofs/lrc_proof_pack_2026-03-01/lrc_n_all_canonical_frontier_map_v1.md`

Durable insight:

- distinguish sharply between:
  - `PROVED`,
  - `PROVED-UNDER-H`,
  - `CERTIFIED-FINITE-WINDOW`,
  - `HEURISTIC`,
  - `OPEN`.

This was not just bookkeeping. It prevented strong empirical support from quietly mutating into theorem claims.

That discipline is still very useful now that the proof program has advanced: it helps keep explanatory spillover separated from canonical theorem authority.

## 10. What to preserve vs what to ignore

### Preserve

- shared-object language
- branch compression notes
- elegant constructive skeleton
- finite-window regime maps
- containment / witness-classifier structural summaries
- boundary-set verification methodology
- transport / residue-handoff vocabulary

### Treat carefully

- scoped partial theorems that were later absorbed or superseded
- proof-pack gap labels that were accurate then but not now

### Ignore for current understanding

- old registry promotions
- quorum state as a proxy for mathematical value
- stale open-status files that predate the later proof closures

## Working conclusion

The earlier work did contribute real additional understanding.

Its best contribution was not a second proof route. It was a better map of the terrain:

- what the hard objects were,
- which phenomena were local versus global,
- which empirical patterns were stable enough to trust as guides,
- and which verification methods were complete enough to be reusable.

So the right way to “circle back” is not to reopen the old queue as if it were still the main proof program.

It is to mine it as:

- a mechanism archive,
- a notation/compression archive,
- and a source of reusable structural heuristics for explaining the proofs we now have.
