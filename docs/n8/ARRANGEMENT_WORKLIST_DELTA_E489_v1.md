# E489 — fast-pair resumption: worklist update

Rules v4:1–16,18,20. Addendum to [the frozen arrangement worklist](ARRANGEMENT_WORKLIST_v1.md); original reductions, moving subject and whole-lap provenance remain in force. Auditor waiver retained.

| Worklist interaction | New standing |
|---|---|
| G05: pair resumption after outside displacement | **[L]** The pair itself resolves from any carried-in real start. The only longer setter episode is fast→slow→fast; the last fast separation retains the slower member's clearance. No disparity separation factor or bounded lap labels. |
| Same/mixed-lap pair and wide pair | **[L]** One common mechanism. Ratio≤3 gives the shorter two-setter episode; arbitrary ratio permits the three-setter episode. The explicit pair `{1,16}` from7/8 requires all three moves. |
| H05/H06: full core transfer | **[L conditional]** Clearance of the core at the pair's COMPUTED output transfers that output to the full arrangement. Intermediate core captures and changed full setters are permitted. |
| Computed core isolation followed by pair resumption | **[L conditional]** Any established core path can be composed with the native pair resumption; its output need not be visited on the original full path. Core clearance at the resulting computed pair output closes this branch. |
| Returning core after pair separation | **[NEXT]** Retain which core reading returns, its lap, and the earlier core/pair capture constraints; follow its forced separation and all newly carried readings. |
| G07/G08/G09 and other placements | Pair and transfer laws are reusable without the G05 largest-gap geometry. No larger-group or universal residual closure claimed. |

- E489 checked every1,029 displaced largest-gap5|2 input in the full52,000 stored survey; immediate outside-separation→pair resumption rejoins the full output in842 controls.
- E489 computed the WHOLE slow core's isolation before pair resumption; this rejoins in1,011 controls. Every one of the other18 has exactly one core reading captured at the pair output. Counts are diagnostic populations, not numbers of unproved residual cases.
- E489 followed all18 returns:17 have the next core→pair continuation clear; one carries a DIFFERENT core member into the way. No universal group-cycle bound is inferred.
- E489 rechecked both recorded primitive residual controls and all recorded fields. The same top-two pair construction closes one control; the other has a core return. These are diagnostic memberships, not new Lean EightResidual-membership proofs.

**Next input type:** the computed pair is clear at V and exactly one core reading d is captured there. The actual full move is forced to d's opening. Follow which pair/core readings enter there, retaining the derived original arrangement hypotheses. A newly captured core member is an allowed continuation; do not assume only the same d can return or that V is visited by the original path.

Proof: [FastPairResumptionN.lean](../../LonelyRunner/LonelyRunner/LRC/Spec/FastPairResumptionN.lean). Data: [complete G05 record](../../experiments/n8/fast_pair_resumption_2026_10_20/analysis.json), [whole-core comparisons](../../experiments/n8/fast_pair_resumption_2026_10_20/core_comparison.json), [all18 returns](../../experiments/n8/fast_pair_resumption_2026_10_20/return_cases.json), [retained residual controls](../../experiments/n8/fast_pair_resumption_2026_10_20/residual_controls.json).
