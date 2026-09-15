# MANUSCRIPT_v8 — revision list

Started 2026-09-15 for `MANUSCRIPT_v8_2.md`. **v8.2 is frozen (owner, 2026-09-15)**: no edits to it; accepted items go into `MANUSCRIPT_v8_3.md`. The v7 list, `V7_REVISION_LIST_v1.md`, is closed at item
53 ("applied in v8") and kept as the record. **Append only; nothing is removed when it is done** — mark it and say where it
went. Edits to the manuscript go in a new version (`MANUSCRIPT_v8_3.md`, …).

---

## 1. Appendix C — a second statement linking the output to the conjecture  `[OPEN — owner to confirm]`

Owner ruling (v8 plan, conjecture relation): the conjecture is named once, in §9 — *"If Existence held for every runner,
the conjecture at eight runners would follow."*

`MANUSCRIPT_v8_2.md` Appendix C, "Objections that do not apply", last row: objection *"Producing an instant does not settle
the conjecture"*, outcome *"an instant at which a runner is lonely is what the conjecture asks of that runner (§9)"*. Both
cells name the conjecture outside §9. The row comes from `OBJECTION_LEDGER_v1.md` Part 1, row 9.

**Proposed change (v8_3):** objection *"Producing an instant is not what is asked"*; outcome *"an instant at which a runner is
lonely is exactly what is asked of each runner (§9)"*.

Not affected: the abstract's opening statement of the problem, the reference titles, and Appendix B's quotations of v7.
(Found by the memory audit of 2026-09-15: `grep -in conjecture MANUSCRIPT_v8_2.md`.)

---

## Carried open work (from `V7_REVISION_LIST_v1.md` item 53; listed here so this list is complete)

- Existence at order 8 (`MANUSCRIPT_v8_2` §6.7) `[OPEN]`.
- The gap-frame obligation (§4.6) `[OPEN]`.
- Fitting between AP locations: how the fit feeds each runner's reading (§2.3; v7 list item 24) `[OPEN]`.
- Order 5: the cap `R < 4` (§8.2; v7 list item 52) `[OPEN]`.
- `k = 5` differences at `n = 6 … 15` (§8.2) `[OPEN]`.
- Promotion of `MANUSCRIPT_v8_2` (or its successor) as the manuscript of record — owner decision. The four fixes made in v8_2
  have not had their own compile-diff; run one on whichever version is proposed for promotion.

---

## 2. Targets after review  `[OPEN — see TARGETS_v1.md]`

Three ideas and four ranked openings, thought through in `TARGETS_v1.md` with exact checks (`experiments/n8/targets_premises_v1.py`,
`targets_long_chains_v1.py`). Outcome:
- **T1** order 5, `R < 4`, via a two-return lemma that prices returns by depth and skipped laps — first action a recon.
- **T2** Existence for `k` differences at every `n > 2k`, derived from step factors and per-runner laps — **owner ruling needed**:
  it reaches the same threshold as the excised `AdvanceBudget`.
- **T3** state `R ≤ 2n − 1` as an empirical conjecture.
- Dropped, with reasons: the dead-lattice escape valve; the residue rule as a route to Existence.
- Reduction recorded: Existence for a runner iff its `R_N` is bounded (`exists_fixed_of_capped`); lap bookkeeping alone cannot reach
  the diagonal at any order.

**Addendum to item 2 (2026-09-15).** `TARGETS_v2.md` supersedes v1: it corrects two overstatements found by the memory audit
(per-runner lap distinctness is not a standalone Lean theorem; only "bounded `R` ⇒ stops" is in Lean) and adds own proposals —
**T0** per-runner lap distinctness in Lean; **T1a** order 5 `R < 4` for spread `S ≤ s₀` by first exceedance plus an exact
strict-feasibility linear program per word (owner ruling on fit needed); **T1b** the large-spread regime. Supporting data:
`experiments/n8/targets_length_vs_reading_v1.out` (longest order-5 chain grows with the largest reading while `R` falls).

**Addendum 2 to item 2 (2026-09-15).** `TARGETS_v3.md` supersedes v2. It withdraws two verdicts reached by reasoning errors:
the dead-lattice idea was answered only in its cascade-scale form, while its lattice-witness form (`WHY_IT_PREDICTS_v1`) is
live and half proved (**T4**); and the residue rule was set aside by the wrong criterion (whether the cascade ends on a
lattice instant), where Existence needs only some lonely instant. Data: `experiments/n8/lattice_witness_nowindow_v1.out`.
Owner instruction the same day: try T2 (the `n > 2k` derivation) in Lean.
