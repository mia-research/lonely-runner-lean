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

---

## 3. T2 proved in Lean: `k` differences at every `n > 2k`  `[PROVED-LEAN — for v8_3]`

Added 2026-09-15 (owner: "try 1"). `LonelyRunner/LRC/Cascade/ManyDifferences.lean`:
- `stops_when_twice_card_lt` — with `2·card ds < n`, some step of the cascade from `1/(n·m)` is fixed;
- `many_diffs` — the Version B form (lonely and first).

**The proof is not the paper derivation of `TARGETS_v3` §3.1.** It uses a potential: `Ψ(t)`, the product over runners of the
lap factors `(r + 1/n)/(r − 1/n)` of the laps each has passed by `t`.
- A move set at lap `Q` raises `Ψ` by at least that lap's factor (`potential_step`), and multiplies `t` by less
  (`move_growth`). So `t_N·Ψ(t_0) ≤ t_0·Ψ(t_N)` (`time_le_potential`), with no bookkeeping of distinct laps.
- A Bernoulli bound gives `Ψ(t)^n ≤ C^k·(∏_x (x + 1/t_0))²·t^{2k}` in integer powers (`lapFactor_pow_le`, `lapProd_pow_le`,
  `potential_pow_le`). So `t^{n−2k} ≤ B`, and `exists_fixed_of_capped` finishes.
- No zone widths or interval lengths enter.

Gate `scripts/cascade/gate.sh`: build 3,351 jobs, 0 `sorry`, **152 of 152 theorems axiom-clean**. The gate's axiom check had a
hardcoded file list and first reported 135, missing the new module. It now reads every module and was tested to fail on a
planted `sorry` in the new file. Cascade digest now `ddf633f48d6fce9dfba1942f0d5f8ea38b64f93f3735e4108cff90d8bdd9ca8c`.

**Freeze bookkeeping.** v8.2 §7/§10 quote 135 theorems and digest `9657ea89…`; that state is commit `21a7748` in the
`LonelyRunner` repository, tagged `manuscript-v8.2-cascade`. v8.2 stays as it is. For v8_3: §7 counts and digest, the §8.2 table
(new row: `k` differences, every `n > 2k`; improves on `max(9, 2^(k−1))` for every `k ≥ 5`), §10.

**Still for the owner.** It reaches the same threshold, `n > 2k`, as the excised `AdvanceBudget` (zone-width count). This proof
contains no zone width or interval length, only lap factors of laps passed. Whether that settles the nativeness question is your
call; nothing else is built on it yet. It does not reach the diagonal `k = n − 1` at any order (`TARGETS_v3` §3.2).

---

## 4. Framework boundary audit  `[OPEN — owner decisions A2, A3, A6]`

Added 2026-09-15 at the owner's request: `FRAMEWORK_BOUNDARY_AUDIT_v2.md` (v1 plus the basis of the reading stated). Nine self-imposed blocks were found (B1–B9). The main
ones:
- the target was recast as a bound on `R` (a "when");
- the order-5 cap `R < 4` is the first window again;
- "the lattice route needs rational readings" came from residue-class machinery. Checked exactly on `a + b√2` readings and
  withdrawn (`experiments/n8/lattice_witness_irrational_v1.out`);
- "dead lattices are integer scales" was read off an `ℕ` statement.

The boundary is the scale rule for relocations (owner's items 16, 20, 24, v7 list). Proposed first native computation (A4): at
one scale, the relocations that block all of `r = 1, 3, 5, 7`, by slot residues.

**Addendum to item 4 (2026-09-15).** Owner corrections: the scale is directed by the speeds, not picked; that rule is in the Lean
cascade work; the ideal does not depend on the scale. `FRAMEWORK_BOUNDARY_AUDIT_v3.md` withdraws v2's §3 boundary and A6. A4 done:
`A4_SPINE_BLOCKING_v1.md`.
- The in-the-way pattern at spines 1, 3, 5, 7 depends only on slot mod 8 and deviation (exact table; 95,776 checks from speeds).
- Spine 1 needs a near-sharer, which at depth `δ` is in the way at exactly the spines `r < 1/δ`.
- Other slots are in the way at two spines at most (`{3, 7}` or `{5, 7}`).
- A cascade step is one dilation of every reading, and the setter lands on the ideal.

---

## 5. What still stops a proof  `[OPEN — see WHAT_STOPS_PROOF_v1.md]`

Added 2026-09-15.
- **Retire as mistranslations:** M1 (lap-bookkeeping limit read as an obstacle), M2 (T1 `R < 4`, T3 `R ≤ 2n − 1`), M3 (T4
  periodicity), M4 (unstated scale rule).
- **Genuine obstacles, one mechanism, resonance:**
  - **G1:** one scale cannot decide. Three runners with no near-sharer hold every odd spine 3–31 in the way; their readings are
    near multiples of `8/6`, near-sharers at lattice 6 (`experiments/n8/spine_runs_min_runners_v1.out`).
  - **G2:** a step drifts every reading by `g·d_y/d_x`, with fixed ratios.
  - **G3:** zero one-sided margin at the ideal's instants.
- **Ways in:** W1 resonance dichotomy (exact computation first), W2 two-scale transition, W3 commensurate limit through the ideal.

**Addendum to item 5 (2026-09-15).** `WHAT_STOPS_PROOF_v2.md` supersedes v1.
- **G1 reclassified:** it concerned a fixed scale, which the framework never uses. Run through the cascade, the examples are lonely
  at the bound or after one move.
- **G2 reclassified:** a step count, ledger Part 4's test.
- **G3 corrected:** perfect isolation, both flanks, not positive speeds.
- **W3 at one lattice:** 4 runners with no near-sharer hold every `p/8`, `p ≤ 24`, in the way. Their readings are near-sharers of
  lattices 2, 3 and 12, the dead-lattice ladder.
- **Stable-speed proposal assessed, owner decision:** `Lonely` is closed, not open. The margin is zero at ideals. Rational
  arrangements are not settled at order 8. The firewall bans a stability radius. Irrationals are not treated separately by the
  framework.

## 6. Naming: "predictor" → "determinator"  `[OPEN — owner suggestion]`

Owner, 2026-09-15: *"our 'predictor' (we might need to rename it as a determinator)"*. The cascade does not predict; it
determines the instant from the speeds. Candidate for v8_3 wording and future documents; script and file names left as they are.
