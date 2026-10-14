# MANUSCRIPT_v8 — revision list

Started 2026-09-15 for `MANUSCRIPT_v8_2.md`. **v8.2 was frozen (owner, 2026-09-15); `MANUSCRIPT_v9_1.md` is now frozen too (owner, 2026-09-15), after its compile-diff.** Accepted items go into `MANUSCRIPT_v9_2.md`.

**`MANUSCRIPT_v9_2.md` is frozen as THE MANUSCRIPT OF RECORD (owner, 2026-09-17.)** Edits go to `MANUSCRIPT_v9_3.md`. It was
promoted after: two compile-diffs against v9.1, the second reporting no losses and five internal notes, all addressed; the
cascade gate at 4,669 of 4,669 axiom-clean with coverage 4,669 of 4,669 on disk; the §5 nativeness pass, enumerating every
non-local identifier the additions use; a review against v1 and v7, which closed three sketch sections absent from every
version since the v1 audit named them on 2026-09-13; Appendix B completed and renumbered B.1–B.5, the chain unbroken from v7;
and the order-5 certificate re-run so its deposited output reproduces from its script. Its byline had carried v9.1's stamp
through the edit and was corrected at the freeze. Earlier note: **v8.2 is frozen**: no edits to it; accepted items go into `MANUSCRIPT_v8_3.md`. The v7 list, `V7_REVISION_LIST_v1.md`, is closed at item
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

---

## 7. T4 / W3 started — flanks  `[IN PROGRESS — T4_FLANKS_v3.md]`

Added 2026-09-15.
- **"Gap ≤ c" is not bounded:** adversarial order 5 gap 6; exhaustive order 8 gap 4; lattice numbering was the wrong coordinate.
- **Flanks:** Existence ⟺ some flank (difference) has a lonely opening (Prop 6.1). At a flank's openings, integer-ratio runners
  never move; each fractional ratio blocks `k` exactly when `k·f mod 1` is in an open arc of length `2/n` (0 disagreements in
  143,520 checks).
- **Proved:**
  - one fractional runner never shadows a live flank (any real `f`);
  - at order 8, two rational fractional runners shadow only if both fractional parts are `1/2`;
  - a rational–irrational pair never shadows.
- **Exact enumeration:** shadowing triples at order 8 (denominators ≤ 8) are `(2,4,4)`, `(3,3,3)`, `(3,6,6)`, `(5,5,5)`.
- **Target:** not every flank can be shadowed at once. Owner call: §3(b) uses a residue count in a cyclic group.

**Addendum to item 7 (2026-09-15) — T4_FLANKS action 1 done** (`experiments/n8/flank_all_shadowed_v1.out`, exact). Unshadowed
flanks per runner, over every subset and every runner:
- **Order 5,** `[1, 30]`: `{1: 4,086, 2: 56,908, 3: 199,004, 4: 452,532}`.
- **Order 8,** `[1, 20]`: `{1: 16, 2: 4,538, 3: 41,118, 4: 175,806, 5: 354,736, 6: 314,912, 7: 116,634}`.

No runner has every flank shadowed. At order 8 only 16 of 1,007,760 runner-instances are down to a single free flank, and those
contain slot-sharer multiples (e.g. `(1, 3, 4, 5, 6, 7, 8, 17)`, subject 1: the difference 16 is 8 × 2, so flank 2 is dead).
The target "not every flank can be shadowed" has wide margin in this range. The next step is the structure of the near-extreme
cases.

**Addendum 2 to item 7 (2026-09-15) — the two-irrational case done** (`T4_FLANKS_v3.md` §3(d)). The **flank sum criterion** is proved
by pigeonhole (simultaneous approximation) and a residue count: a live flank whose non-integer ratios satisfy
`Σ (2/n + 1/c_j) < 1` (with `1/c = 0` for irrational) has a lonely opening. At order 8, one, two or three irrational ratios never
shadow a flank. Exact checks in `ℚ(√2)`: every random pair and triple has a clear opening; near the half-integer shadowing pair
the first clear opening comes at about `0.44/ε`, with no bound on how soon. Owner call on the pigeonhole and count still stands.

**Addendum 3 to item 7 (2026-09-15) — near-extremes and Lean** (`FLANK_NEAR_EXTREMES_v2.md`).
- **Shadowed flanks where free flanks run out** are dead, small (2–3 runners) or wide (4–6 runners). The wide ones share one small
  denominator.
- **All 16 one-free-flank runners at order 8** in `[1, 20]` are the difference set `{2, …, 7, 16}`. The free flank is the fastest,
  decided at its first opening by the mirror of Theorem 4.8 (other differences in `[d_max/9, 7·d_max/9]`).
- **"A sharer's own flank is free" refuted:** 24,656 failures at order 8.
- **Lean:** `Cascade/Flanks.lean` holds `lonely_iff_exists_flank`, `integer_ratio_clear_iff`, `fractional_ratio_circDist`,
  `exists_clear_step` and `lonely_opening_of_one_fractional`. Gate 161 of 161.
- **Not yet in Lean:** the flank sum criterion and the half-integer pair result (counting; owner ruling pending).

**Addendum 4 to item 7 (2026-09-15) — the sharer failures read** (`SHARER_FLANK_RULE_v2.md`). Owner: the failures should say what the
rule is. Exhaustive over every 8-subset of `[1, 20]` (374,556 sharer pairs, none breaking it): a sharer's own flank is shadowed only if
- some runner sits at a symmetric point of the sharer's AP (ratio denominator 2, the antipode, or 4, the quarter points), or
- five or more runners sit at its fine slots (denominators 8, 16).

The only shadowed cases without a symmetric-point runner are 14, all at `s = 16`. It is necessary, not sufficient. Proof and a test
beyond the range are to do. Owner's AP picture recorded in §1: the flank pair sets the gap, isolation at that gap is absolute, and
speed ordering is bookkeeping.

---

## 8. Consistency audit of v8.2 and redraft as v9  `[APPLIED — MANUSCRIPT_v9.md; nothing removed from this list]`

Added 2026-09-15 at the owner's request: audit v8.2 for internal consistency, uniform treatment, and legacy views (single window,
cascade as search, imports from other Lonely Runner work), then redraft as v9.

**Two passes.**
- Own pass: `V8_2_OWN_AUDIT_v1.md`, 17 findings.
- Isolated pass: `V8_2_ISOLATED_AUDIT_v1.md`, 54 findings, run in a fresh context with only v8.2 and the framework's rules.

**Checked independently before applying** (`experiments/n8/v9_checks_v1.py`, `.out`):
- the §6.8 irrational runner's cascade instant is `(497/8)/(7 − √2/100) ≈ 8.8930` after 2 moves, not `75√2/4`;
- the adversarial climb is 28 moves, not 29;
- every `Construction8` theorem is axiom-clean (`v9_construction8_all_axioms_v1.lean`, `.out`: 85 of 85 within the three
  axioms);
- `first_stretch_overlap` and `consecutive_break` exist;
- the §8.1 per-form ranges match the Lean hypotheses.

**v9** applies:
- items 1 (Appendix C conjecture link), 3 (`n > 2k` row), 6 (determinator wording) and 7 (flanks, §6.9);
- the A4 spine pattern and the dilation step from item 4;
- G3 from item 5;
- every audit finding, except two not applied with reasons given in v9 Appendix B.2.

Item-by-item map: v9 Appendix B.2. v8.2 unchanged. Compile-diff on v9 owed before promotion.

**Addendum to item 8 (2026-09-15) — compile-diff of v9, corrections in `MANUSCRIPT_v9_1.md`.** The loss audit found:
0 audit findings unaddressed (54 isolated: 52 applied, 2 recorded; 17 own: all applied); 22 numbered results present at the same
grade; 4 retraction records carried, none re-claimed; 114 Lean names all exist; 26 figures new to v9 all sourced; the Cascade
digest, theorem count, tag and commit recomputed on disk.

Fixed in v9.1: seven small losses (the `v8_axiom_check_v1.out` result, the `W/(8g)` slot-multiple bound, the citations of item 21
and `WHY_IT_PREDICTS_v1` §2, "not sampled", "the local restrictions tighten as `n` grows", the `Cascade/Iteration.lean`
reference, Appendix C's "the first three rows above withdrew those objections"); the sharer refutation record and the census
range; the open triple list; five differences at `n = 6 … 10` stated open; the own audit credited in Appendix B.2; the "not
applied" record corrected (the `v_8 ≤ 40` scope is stated in the sweep description, not as a limitation); a B.2 row for the
§4.5(a) widening to every spine instant; **T3 recorded as not carried into the manuscript**, with the reason. Six contradictions
the redraft introduced were removed: `ρ`, `q`, `m` collisions (now `z`, `κ`, `w`, `b`, `ρ_j`), and §8.1's generalisation now
excludes §6.6's order-8 spine paragraph.

Owner decisions still open: promotion of a version as the manuscript of record; the counting/pigeonhole ruling (Props 6.10–6.11);
the nativeness of `n > 2k` (§8.2); A2 (re-aim T1a).

---

## 9. Ruling: imported tools versus native targets  `[SETTLED — owner, 2026-09-15]`

Owner: *"The flank session did import two standard tools — Dirichlet's pigeonhole and residue counting — and we ruled them
admissible because they appear only on the resonant side, per your dichotomy. That's the boundary of 'not chasing someone
else's': tools are fine, targets and statements are what must stay native. The check to apply whenever a new target appears is
the one you just applied: does the statement exist without the other literature, in your vocabulary alone?"*

- **Admissible:** Dirichlet's pigeonhole and residue counting in Propositions 6.10–6.11 (`MANUSCRIPT_v9_1` §6.9), because they
  appear only on the resonant side of the dichotomy. The pending ruling of item 7 is closed.
- **The standing test for any new target:** can the statement be made in the framework's own vocabulary, without the other
  literature? The two-return lemma passes it.
- **Read across to item 3 (`n > 2k`, `ManyDifferences`):** its statement — with `k` differences and `2k < n`, the cascade from
  the bound reaches a fixed point — is in the framework's vocabulary; the potential and the Bernoulli bound are tools inside the
  proof. On the principle above that makes it admissible. Flagged here because the owner stated the principle for the flank
  session; say if the reading is wrong.
**Addendum (owner, 2026-09-15): the read-across is confirmed, with a qualification.** *"if the n > 2k result's statement is in
framework vocabulary and the potential and Bernoulli bound appear only inside the proof, that's exactly the admissible pattern:
tools on the working side, targets native."* The qualification to hold with it: *"the potential must not secretly be a
measure/density claim in disguise (e.g. 'almost every state has property P' as an intermediate step would violate the ledger
even inside a proof, since the framework's final statements are exact). As long as the n > 2k argument is exact inequalities end
to end, it's admissible."* `ManyDifferences` is exact throughout — `potential_step`, `time_le_potential`, `lapFactor_pow_le`,
`lapProd_pow_le`, `potential_pow_le`, `stops_when_twice_card_lt` are inequalities between real quantities with no "almost every"
step — so it is admissible. `MANUSCRIPT_v9_1` §9 still lists nativeness as pending; correct that in v9_2, not in place.

- **Not changed:** what must stay native is the target and the statement. Window bounds, search framings and coverage shares
  remain excluded however convenient the tool.

---

## 10. Order 5: census, walks, and the two-return lemma  `[IN PROGRESS — ORDER5_TWO_RETURN_v1.md]`

Added 2026-09-15 (owner: run the order-5 three-ratio flank census with the criterion sums, then the walk transcripts).
- **Census** (2,776,410 flanks, every 5-subset of `[1,30]`): the flank criterion is sound — 0 shadowed flanks with `Σ < 1` and no
  dead ratio. Every shadowed flank is dead or flagged.
- **But the correspondence is one-directional:** 886,730 flagged flanks are clear at the first opening and 9,826 unflagged ones
  are late, so "near-blocked = flagged" is not an equivalence. Shadowed signatures are small and uniform; late ones are large
  primes.
- **Walks** (212,520 runners, `[1,24]`): 5,890 runners with one return, **42** with two. Pricing (`return_growth`) holds in all
  6,456 returns. Intervening setters are commonly at ratio denominator 5 to the returner.
- **Two-return cases** are six difference sets up to dilation; the returner is the largest difference, intervening laps 2 and 3,
  ratios near one half, `R` between 1.55 and 1.80.
- **A settings cap is not available** (resonant chains: 150 settings by one runner), so the lemma must price returns.
- Next: the same transcripts in the resonant regime; then whether pricing plus distinct laps bounds the growth between a
  runner's first and last setting.

**Addendum to item 10 (2026-09-16) — corrections and the refuted measure** (`ORDER5_TWO_RETURN_v2.md`).
- **v1's §2 was wrong**: it read truncated print output (`most_common(6)`, `rows[:4]`) as totals. Full re-run: `V = 24` has 42
  two-return runners in **4** difference sets; `V = 30` has 186 in **7**; the returner is the largest difference in 180 of 186,
  not all; lap triples include `(2,3,4)` and `(3,4,5)`; intervening laps include 1 and go to 8; `R` reaches `63/26 ≈ 2.4231`.
  The thesis survives; the figures did not. Found by the memory audit, verified here independently.
- **The candidate well-founded measure is refuted at both ends**: nested returns sit at laps below the parent's in 0 of 138
  (integer, `[1,24]`) and 2 of 463 (resonant). What v1 saw was the weaker "all intervening laps below the parent" (2,820 of
  6,456 stretches). The recursion must rest on the lap deficit below a first exceedance instead.
- **Resonant end**: 7,200 walks, moves to 244, one runner setting 122 times, `R` max 1.4142, pricing 1,509 of 1,509.
- **The shift constant is settled**: `g = 5N + 1 − s_x`, which is `1 + δ` below the multiple and `1 − e` above, never `δ`;
  `MANUSCRIPT_v9_1` §6.2 is correct as written.
- **Process note.** Two runs hung for ten hours: a `multiprocessing.Pool` script fed to Python through a heredoc cannot spawn
  workers (no importable main module), and the failing workers wrote ~1 GB each of error text. Both were killed, the output
  files deleted at the owner's direction, and the runs repeated from `.py` files. **Any script using `multiprocessing` is
  written to a file and run from the file.**

---

## 11. Order 5: the growth identity and the wall  `[IN PROGRESS — ORDER5_GROWTH_v1.md]`

Added 2026-09-16 (owner: derive the growth bound from the pricing plus the first-exceedance measure, test both ends, then
formalise).
- **Why the refuted measure had to fail** `[PROVED]`: laps are monotone in time and nesting runs forward in time, so a nested
  return's laps are read later than its parent's. Verified 138/138 and 11/11, including 14 cases where the inner runner is slower.
  No increasing quantity can found the recursion.
- **The growth identity** `[PROVED; verified on 127,610 walks, 0 failures]`: `R = R₁ + Σ (2 − n·δ_j)/s_j`. Each move adds the zone
  width it still had to cross, divided by its reading. `R₁ ≤ 3/2` always.
- **The order-5 cap restated** `[PROVED]`: `R < 4` ⟺ the nearest runner is never in the way after the bound.
- **First exceedance gives finiteness** `[PROVED; 0 violations in 199,248 + 3,005]`: before the first step reaching `C`, runner `x`
  sets at most `max(⌊(C·s−1)/5⌋, 1)` times, and "bound minus current lap" decreases.
- **The wall** `[PROVED]`: charging each zone crossing its full width bounds the total only when `2k/n < 1` — the `n > 2k`
  threshold again, now from the additive side. Order 5 needs the depths.
- **What the depths must supply** `[VERIFIED]`: crude bound 6.4 against a true maximum of 1.73; per-runner budgets give 5.03,
  still above 4. Terms decay with setting index (medians 0.232, 0.125, 0.096).
- **Next:** the depth at repeat settings as a function of the previous stretch, at both ends; then the lemma; then Lean.

**Addendum (2026-09-16) — run guard.** `scripts/run_job.sh` (owner asked for it after the ten-hour hang). It refuses a script
read from stdin and a `multiprocessing` script with no `__main__` guard; kills a job whose CPU time stops advancing (default
300 s — the exact signature of that hang), whose output passes 50 MB, or which runs past 6 h; and reports why it stopped with
elapsed time, CPU time and output size. Tested: a stalled job killed in 30 s, a normal job run to completion, an unguarded
multiprocessing script refused. Use it for every long computation.

**Addendum to item 11 (2026-09-16) — `ORDER5_GROWTH_v2.md`: two refutations and a ledger.**
- **The other session's shift accounting is this document's identity** (`g = 2 − n·δ`); one constant, settled. Its gap constant is
  `n − 2` — **3 at order 5, not 6**; an order-5 census run at 6 would discard live cases.
- **Proved and verified ledger**: a return of `x` costs `ΔR > (n−2)/s_x`, so `Σ_x (returns)/s_x < 1` under the cap (10,096 of
  10,096 integer, 193 of 193 resonant; ledger max 0.5257).
- **The depth floor is refuted**: depths at repeat settings reach 0.00004; no argument may assume one.
- **Uniform-constant pricing is refuted**: closure needs the return-cost constant above `2k/(n−2) = 8/3`; the measured minima are
  1.150 (integer) and 1.095 (resonant), and the worst-case-charge ratio falls to 1.000. So the two-return lemma cannot close
  order 5 as a uniform pricing statement. Cost and gain are both proportional to `1/s`, so the reading cancels and only `k`
  survives — the same cancellation behind both earlier walls.
- **What remains**: the finite certificate under first exceedance, and the flank coupling. Both need the joint structure, not a
  per-move charge.
- Also assessed from the other session: the "machine cycle with an identical gap sequence each period" holds only for
  commensurate ratios; "irrational cases are perturbations of rational ones" is a stability-radius argument the firewall bans and
  margins at ideals are zero; a strictly decreasing potential gives no finiteness without a floor, and §9 shows there is none.

---

## 12. Order 5: Existence proved for bounded spread  `[PROVED — ORDER5_CERTIFICATE_v1.md]`

Added 2026-09-16. With uniform pricing refuted (item 11), the finite certificate closes the bounded-spread case.
- **First exceedance makes it finite**: before `R` reaches 4 the nearest never sets, every lap is `< (4S+1)/5`, laps increase per
  runner, so the words are finite and each word's conditions are linear in the readings.
- **The boundary discipline is load-bearing**: closed inequalities return the known 4.125 artefact on an all-boundary word;
  enforcing a positive margin discards it.
- **Result**: at order 5 with spread `S ≤ 6`, `sup R = 27/8 = 3.375 < 4`, so the cascade stops and Existence holds for every such
  runner. The optimum is the lap-1 ladder `(3/2)³`, now derived rather than assumed.
- **Scope**: finite exact verification over words at spread ≤ 6; complete for that range, silent beyond it. `S = 8` running.
- **Next**: push the spread bound; then either cover unbounded spread or reduce it to the bounded case; then Lean.

---

## 13. Order 5: the ratio sweep, margin realisability, and the certificate's finiteness bounds in Lean  `[ORDER5_CERTIFICATE_v2.md]`

Added 2026-09-16. Supersedes item 12's scope and **corrects two of its claims**.

- **Ratio `S ≤ 18`, not 6** `[PROVED — exact finite certificate]`. `sup R = 27/8` for `S ≤ 9`; `31/9 = 3.4444` for `S = 10…18`.
  The enumeration is exact rational arithmetic throughout; `order5_certificate_v3.py` solves each word's LP by exact simplex
  instead of vertex enumeration and **reproduces v2's answers exactly** at `S = 5, 6` (same value, same word, same margin),
  which is what licenses the faster solver. Cost doubles about every two steps of `S` (52 s at `S=14`, 198 s at `S=18`).
- **`[CORRECTS item 12]` The lap-1 ladder is extremal only up to `S = 9`.** From `S = 10` the optimum is the six-move word
  `(1,2), (2,1), (1,3), (3,1), (2,2), (1,6)`, in which runner 1 sets four times with two intervening returns. Item 12 recorded
  the old lap-1 `(3/2)³` assumption as *discharged* — that discharge stands only for `S ≤ 9`. Returns are not outside the
  extremal regime; from `S = 10` they are it.
- **`[CORRECTS item 12]` "Artefact" was loose.** The closed-inequality LP is a valid relaxation whose bound is merely too weak
  (its feasible set is a superset, so 4.125 is a true upper bound over that superset), not a false computation. What is not
  realisable is the *word*, which carries `max τ = 0` exactly. A closed relaxation elsewhere is not thereby an error to fix.
- **`sup R(S)` is flat, and a worry was raised then refuted.** The first two values (`27/8 → 31/9`, numerator `+4`, denominator
  `+1`) extrapolate to the family `(27+4j)/(8+j) → 4`, which would deny any uniform margin. The sweep to `S = 18` kills it:
  nine consecutive ratio bounds all return `31/9`, the same extremal word throughout, the same margin `132/4165` from `S = 11`,
  while the lap bound grows 7 → 14 and the word-length bound 21 → 42. Growing the search space stopped producing better words.
- **Margin realisability, proved** `[PROVED]`. The margin threshold and the R-supremum are two readings of **one** convex
  polytope `P(w)` in `(u, τ)`, not two sequential steps: since `τ` is a coordinate, every `τ = 0` feasible point is a limit of
  `τ > 0` feasible points, so the supremum over strictly realisable configurations is exactly `(5Q+1)/m*(w)`. This closes the
  `ε → 0` escape — a word realisable only with vanishing margin cannot smuggle in a larger `R`.
- **Lean: the three finiteness bounds are formalised** `[PROVED — LonelyRunner/LRC/Cascade/Certificate.lean]`. `cascadeR_zoneHi`
  (a setting of `x` at lap `Q` lands at `R = (n·Q+1)/u`), `nearest_setting_ge` / `nearest_never_sets`, `lap_lt_of_cascadeR_lt`
  and `lap_lt_of_ratio_le`, `laps_strictly_increase`, `lap_mem_Icc`. Cascade gate: **170 theorems, axiom-clean, no `sorry`**.
  **Owed**: the word LP and the value `31/9` are not yet formalised.
- **Cross-shift: one null was forced, and is recorded as a defect of the query.** The first cross-shift script answered "the
  chains stay in one cluster" over 7200 walks — but its generator drew the large speeds as a base times a multiplier in `[1,3]`,
  so no straddling window was available to observe. Re-run with separated scales, cross-cluster handovers do occur (1255 and
  1713 of 4800), and the chains containing them are short (≤ 6 moves); every chain of ≥ 10 moves came from the clustered
  control and showed none. Length and cross-cluster traversal are anti-correlated — consistent with the reduction, weak
  evidence for it, since random sampling tops out at `R = 1.30` against the certificate's `3.44`.
- **Next**: `S = 22, 26` running; the reduction of unbounded to bounded ratio is still open; the pricing lemma stays warm
  (item 11) — and the correction above is the reason, since returns sit *inside* the extremal word.
- **Notation fix (found by the framework-integrity check, 2026-09-16).** This line of work had been calling `S = d_max/d_min`
  "the spread". The manuscript reserves **spread** for `W = v_8 − v_1`; `S` is the **ratio** of largest to smallest difference.
  That is the collision audit finding C1 removed and manuscript v9.1 separated again — reintroduced here by our own drafting,
  not by any imported source. Corrected in `ORDER5_CERTIFICATE_v2.md`, item 13, `Certificate.lean` and the scripts; v1 is left
  as the historical record. No result changes: every number was always about `d_max/d_min`.

---

## 14. Framework-integrity check  `[owner-requested, 2026-09-16]`

Owner's concern: the programme's biggest threat is adopting someone else's measures, since the framework is built
differently and prior tools are not necessarily compatible. Test applied throughout (owner's ruling 2026-09-15): *tools are
fine; targets and statements must stay native* — does the statement exist without the other literature, in our vocabulary alone.

**Mechanical scan.** Every occurrence of measure, density, equidistribution, Weyl, Fourier, discrepancy, Bohr, ergodic,
Lebesgue, probabilistic, expectation, "almost all", Minkowski, covering, lattice, Dirichlet, pigeonhole, residue and CRT, across
the nine cascade Lean modules and `MANUSCRIPT_v9_1.md`.

- **Lean**: the Cascade modules' own `import` lines name only `Analysis.Complex.ExponentialBounds`,
  `Analysis.Real.Pi.Bounds`, `Analysis.Real.Pi.Irrational` and `NumberTheory.Real.Irrational`.
  **`[CORRECTS the first draft of this item]`** That was written up as "no measure theory is imported at all", which is false
  transitively: `LRC/Defs.lean` imports `Mathlib.MeasureTheory.Measure.Lebesgue.Basic`, and `Defs` is in the Cascade tree's
  transitive closure — it is shared with the older measure-based general-`n` lineage, which is where that import is used. **An
  import grep is therefore not the nativeness check**, and the structural claim built on one was overstated. What does hold, and
  is what the check actually rests on: no Cascade *statement* or *proof* contains measure-theoretic content — the scan below is
  over statements and proof text, and `exists_clear_step`'s proof was read in full (three cases on `f`, closed by
  `linarith`/`nlinarith`/`omega`). Two hits, both benign: `Certificate.lean` "measured at the nearest difference" (plain English) and `SmallOrders.setter_repeat`, an *abstract*
  pigeonhole (`k+1` values in a set of size `≤ k`) proved from scratch, cited to nobody.
- **Manuscript**: every hit is the firewall **banning** the thing (`No measure or density`), the objections table explaining why
  it is inapplicable, or the phrase "no equidistribution, no result at another order, no proof sketch". None is a use.
- **`ManyDifferences` (nativeness was recorded open)**: the potential is built only from lap-zone objects — `lapFactor =
  (r + 1/n)/(r − 1/n)`, `lapsPassed = ⌊x·t − 1/n⌋`, `potential = ∏ lapProd` — and every step (`potential_step`,
  `time_le_potential`, `lapProd_pow_le`, `potential_pow_le`, `stops_when_twice_card_lt`) is an exact inequality between real
  quantities. **It meets the owner's qualification: no measure or density claim in disguise.** The statement — *the cascade from
  the bound stops whenever `2k < n`* — is native.
- **`Flanks`**: every statement is in our vocabulary (flank openings, readings, ratios, clear / in the way, lonely, stops). The
  imported tools sit inside proofs only, as ruled.
- **This session's new work**: the certificate's linear programs are a *solving method* for inequalities that are themselves the
  framework's own (in-the-way, advancement, readings); the statement — `R ≤ 31/9` over realisable words at ratio bound `S` — is
  native. The margin `τ > 0` is not an imported device; it is the firewall's **Boundary discipline is mandatory** row enforced
  numerically. The word enumeration is **not** a search in the banned sense: it enumerates possible `(setter, lap)` sequences to
  bound every case, and picks no candidate instant — the cascade remains fixed by the speeds.

**The one drift found is ours, not imported.** The order-5 certificate line had been calling `S = d_max/d_min` "the spread".
The manuscript reserves **spread** for `W = v_8 − v_1`, a difference of speeds; `S` is a **ratio**. This is the collision audit
finding C1 removed and manuscript v9.1 separated again, reintroduced by our own drafting. Corrected in
`ORDER5_CERTIFICATE_v2.md`, item 13, `Certificate.lean` (`lap_lt_of_spread` → `lap_lt_of_ratio_le`) and the scripts;
`ORDER5_CERTIFICATE_v1.md` keeps the old wording as the historical record. **No number changes** — the quantity was always
`d_max/d_min`.

**Owed to `MANUSCRIPT_v9_2.md`** (v9.1 is frozen, so these are recorded, not applied): the Lean map says Cascade = **161
theorems**; the tree is now **170** with `Certificate.lean` added, so §7, the Appendix table (`| theorems | 85 | 161 |`) and the
module list in the artefact section are stale. §9's counting-ruling staleness, already on the list, is unchanged.

---

## 15. The eighth-family: verified, corrected, and formalised  `[PROVED — Lean, axiom-clean]`

Added 2026-09-16. Relayed by the owner from a parallel session's `EIGHTH_FAMILY_v1.md`
(`~/ZCodeProject/lrc-n8/notes/`). Re-derived here from its own instruments; write-up `EIGHTH_FAMILY_v2.md`,
check `experiments/n8/eighth_family_check_v1.py`, Lean `LRC/Cascade/EighthFamily.lean`.

- **Confirmed**: the six fixed differences of `Δ(x) = {1,3,4,5,7,x,8}` leave exactly `k ≡ 1, 3 (mod 7)`
  uncovered at the flank of difference 7. Every integer `x ∈ {1,…,7}` is served by `k ∈ {1,3}`; 4000 random
  non-integer rationals all found a clear opening (largest index `j = 9`).
- **`[CORRECTS v1]`** v1's proof paragraph says `‖9x/56‖ ≥ 1/8` for every integer `x`, so "`k = 1` is free
  outright". False at `x = 6`: `54/56` gives `1/28 < 1/8`, blocked. The theorem survives — `x = 6` is clear
  at `k = 3`, as v1's own *Anchors* paragraph says — so v1 contradicts itself within a page.
- **The irrational case needs no approximation theory.** v1 closes it with *"the orbit is dense"*, and the
  working session was preparing to import Kronecker or a Dirichlet argument while uneasy about the firewall.
  The unease was right and the import is unnecessary: `Flanks.exists_clear_step` (already in the artefact,
  native, axiom-clean) gives `∃k, 1/n ≤ circDist (k·f + c)` for `0 < f < 1`. Along `k = 1 + 7j` the sixth
  difference's phase is an integer shift of `j·Int.fract x + 9x/56`, so the lemma applies directly and
  **covers rational and irrational `x` in one case**. v1's rational/irrational split and its grid argument
  are both unnecessary.
- **Formalised**: `eighth_family_lonely` (normalised) and `eighth_family_lonely_scaled` (any `E > 0`), with
  `clear_of_band`, `fixed_clear_one`, `fixed_clear_three`, `int_clear_one`, `free_clear_of_not_int`.
  Cascade gate **177 theorems, axiom-clean, no `sorry`** (was 170). The relayed draft carried a `sorry` and
  a broken tactic block; nothing of it is reused.
- **Boundary discipline is load-bearing again**: the flank's own runner sits at exactly `1/8` at every one of
  these openings, clear only because the zones are open (§1.2) — the same discipline that decided the
  order-5 certificate's `27/8` against the closed-inequality `33/8`.
- **Scope, stated plainly.** This closes the family that shadows the largest flank; **Existence at order 8
  remains open and the gate still reports it unstated.** Closing it outright needs uniqueness of the eighth
  pattern at all denominators (no other minimal largest-flank cover) — unproved; the `A = 0` census at
  `c > 8` and the bounded-overhang lemma are the two routes. Until then the disjunction "free largest flank
  or eighth-family" holds only within the census range, denominators ≤ 8.

---

## 16. Route A verdict: uniqueness refuted, the mechanism generalises  `[ROUTE_A_VERDICT_v1.md]`

Added 2026-09-16, answering the owner's Route A instruction and its named highest-value check.

- **`exists_clear_step` does force something, but about essential ratios, not the free parameter.** If every
  ratio of a cover but one is rational with period `L`, and they leave a residue class uncovered, the
  remaining ratio `ρ` must have `ρL ∈ ℤ` — else `exists_clear_step` clears it on that class and the flank is
  free. So **a cover cannot be rationals plus exactly one irrational.** Two or more irrationals sharing a
  class is beyond a one-ratio lemma; that gap is the honest limit.
- **The stronger hope fails for a simple reason**: at the largest flank the five fixed ratios shadow on their
  own, so the free parameter is unconstrained *there*. It is constrained at the `7/8` flank — which is the
  eighth-family theorem already formalised (item 15).
- **`[REFUTES the uniqueness premise]`** Minimal covers of the largest flank exist at `c = 9, 10, 11, 12, 16`
  that are not the eighth pattern. Verified witness: `{1/10, 1/5, 3/10, 1/2, 7/10}` — differences
  `{1,2,3,5,7}` at `d_max = 10` — shadows every opening mod 10 and is minimal (every member has private
  openings). The census reproduces `FLANK_SIGNATURES_v1` §6 exactly at `c ≤ 8` (one cover, the eighth
  pattern), which is what makes the disagreement above it meaningful. **Route A is closed as stated: no
  census extension and no rigidity argument can prove a false premise.**
- **What survives is better.** Every minimal cover found has some *other* flank with an uncovered residue
  class — the eighth-family mechanism, generalising. So the target is not uniqueness but **"no difference
  set has every flank shadowed at once"**, which via `lonely_iff_exists_flank` **is** Existence, stated
  natively.
- **Routes.** A closed; B (bounded overhang) is live by the owner's own conditional; no formalisation started,
  per the instruction not to run two in parallel. The essential-ratio lemma is native and not yet in Lean.
- **Scope**: Existence at order 8 remains open; the gate still reports it unstated.

---

## 17. Route B refuted; the target restated  `[ROUTE_A_VERDICT_v1.md companion]`

Added 2026-09-16. Route B was authorised to be *stated and tested* up front, with only formalisation gated on
A's verdict; it was tested only after the owner asked for its results, which was a misreading of the
instruction on this agent's part.

- **`[REFUTED]` Shadowing the largest flank does not bound the overhang.** Minimal shadowing covers of size
  ≤ 6 exist at **every** denominator `c` from 8 to 40 (`route_b_overhang_v1.out`); a cover containing the
  ratio `1/c` means `d_min/d_max = 1/c`, so `S = d_max/d_min` is unbounded among shadowing sets. Route B's
  premise fails the same way Route A's did.
- **No designated pair of flanks works either.** The largest and second-largest are both shadowed in 21 of
  40,000 random integer sets; the second-largest alone is free in 98.1% of 20,000, not all.
- **`[EMPIRICAL]` But the margin is real**: over 40,000 random integer difference sets (`d_max ≤ 80`), the
  number of free flanks was **never below 2** — distribution `{2: 254, 3: 403, 4: 1132, 5: 3797, 6: 10949,
  7: 23465}`. The extremal case is the near-AP `[1,2,3,4,5,7,8]`, free only at flanks 5 and 7.
- **The forced-overlap counting bound** `[PROVED — elementary]`: at a flank of period `c`, every ratio below 1
  blocks opening `k = 0`, so if `m` blocking sets contain 0 the union misses at least `m − 1`, and shadowing
  requires `Σ_j |S_j| ≥ c + m − 1`. This **proves no shadow exists below `c = 8`** (matching the census: none
  at `c = 4…7`) and the `c = 8, 12, 16` covers sit at **exact equality** — the rigidity the owner predicted,
  found where it actually lives. It has slack at larger `c` (6 at `c = 20`, 16 at `c = 40`), so it does not
  close the problem alone.
- **The restated target**: some flank is always free — which via `lonely_iff_exists_flank` **is** Existence.
  The per-flank mechanism is already proved and formalised (item 15's template: an uncovered residue class,
  then `exists_clear_step` for the free ratio). What is missing is the uniform statement that some flank
  always has an uncovered residue class.
- **`[CORRECTS item 14]`** see that item: the "no measure theory imported at all" claim was false transitively
  (`LRC/Defs.lean` imports `Mathlib.MeasureTheory.Measure.Lebesgue.Basic`), and an import grep is not the
  nativeness check.
- **Scope**: Existence at order 8 remains open; the gate still reports it unstated.

---

## 18. The divisibility test: a theorem, a refutation of its own route, and one critical set  `[FLANK_OVERDETERMINATION_v1.md]`

Added 2026-09-16, testing the arithmetic-side idea proposed after Routes A and B were refuted.

- **`[PROVED — elementary]` The divisibility hook is real.** The fraction of a flank's openings a ratio
  blocks depends only on `c = e/gcd(d,e)`: density 1/2 at `c = 2`, 2/5 at `c = 5`, 1/4 in the large-`c`
  limit. With the forced overlap at `k = 0`, shadowing needs `Σ density(e/gcd(d_j,e)) ≥ 1 + (m−1)/e`. This
  **forbids a shadow at `e = 4, 5, 7`** — **`[CORRECTS this item's first draft]`** not "below `c = 8`": at
  `e = 6` the budget is exactly met (3/2 vs 3/2) and no cover exists anyway, so counting explains three of
  the four empty cases, not four. The first draft reasoned from six *generic* density-1/4 ratios, imposing
  the large-`c` limit on small flanks where densities are higher. Density also depends on the numerator, not
  the denominator alone; the published table is the max over numerators (safe for a necessary condition).
  The
  eighth pattern spends exactly `3/2` against a requirement of exactly `3/2` — **exactly saturated**, closing
  the gap only via `d = 4` (`gcd = 4`, `c = 2`, density 1/2). The rigidity predicted for Route A is real and
  lives here, in the overlap budget.
- **`[REFUTES the route]` The condition is necessary, not sufficient, and cannot close Existence.** On the
  critical set `{2,3,4,5,6,7,16}` at flank 16 the budget is 1.5 against a requirement of 1.3125 — sufficient
  for a shadow — and the flank is free regardless. Counting cannot predict freeness once the budget is met;
  the arrangement decides. The over-determination argument has no contradiction to derive at such a flank.
  This was the session's own proposal, endorsed on its recommendation, and it does not reach the target.
- **`[PROVED — finite verification]` Exhaustive: every 7-subset of `{1..30}`** (2,035,800 sets, exact integer
  arithmetic) has a free flank — Existence holds for all of them — and **exactly one set is tight**:
  `{2,3,4,5,6,7,16}`, free only at flank 16, six consecutive integers plus an outlier, set gcd 1. Every other
  set has at least two free flanks. Earlier random sampling suggested a minimum of two free flanks; that was
  a sampling artefact, and exhaustive search found the thinner margin.
- **The target in native arithmetic form**: opening `k` of flank `e` is free iff, with `u = 8k+1`, `M = 8e`,
  every `d_j·u mod M` lies in `[e, M−e]`. So Existence is a simultaneous-avoidance statement — no measure,
  density or covering language. That is the form to attack and to formalise.
- **Scope**: integer differences, seven distinct values, `d_max ≤ 30`. Existence at order 8 remains open and
  the gate still reports it unstated.

---

## 19. The near-AP extremal is an infinite family, and it is proved  `[PROVED — Lean, axiom-clean]`

Added 2026-09-16. Follows item 18's exhaustive search, which found exactly one critical set.

- **`{2,3,4,5,6,7,16}` is not isolated.** `{2,3,4,5,6,7,N}` has exactly one free flank **precisely when
  `16 ∣ N`** (checked against every `N` from 8 to 400 — the characterisation is exact, no exceptions), and
  the free flank is always `N` itself at opening `k = N/16`. So the critical configuration is the first
  member of the infinite family `Δ_m = {2,3,4,5,6,7,16m}`.
- **The whole family is lonely** `[PROVED — LRC/Cascade/NearAP.lean]` at the explicit instant
  `t_m = (8m+1)/(128m)`: the consecutive block sits at `d·t_m = d/16 + d/(128m) ∈ [1/8, 1/2]` for
  `2 ≤ d ≤ 7`, `m ≥ 1`; the outlier sits at exactly `m + 1/8`. Theorems `circDist_of_le_half`,
  `block_clear`, `outlier_clear`, `near_ap_lonely`. Cascade gate **181 theorems, axiom-clean, no `sorry`**.
- **Why it is extremal, exactly.** The minimum distance over the set is **exactly `1/8`, attained by the
  outlier** — the order-8 bound is tight on this family, and loneliness holds because `Lonely` asks for
  `1/n ≤ circDist`, i.e. the threshold attained, not exceeded. The block's own margin is `d/(128m)` at
  `d = 2`, which tends to 0 as `m → ∞`. **This is the fourth result decided by boundary discipline**
  (after `33/8` vs `27/8`, the eighth-family flank at exactly `1/8`, and its `x = 7` case).
- **No counterexample anywhere near it**: `{2,…,7,N}` for `N ≤ 2000` and every consecutive block `a…a+5`
  with outlier `N ≤ 600` — not one set with zero free flanks.
- **Scope**: Existence at order 8 remains open; the gate still reports it unstated.

---

## 20. The ladder bound — a closed form, and a proof structure for review  `[LADDER_BOUND_v1.md]`

Added 2026-09-16, out of the abandoned order-8 enumeration.

- **`[measured]` The order-8 word enumeration is infeasible and was abandoned.** Pass rate flat at ~16%,
  growth 4.7×/level through level 6, max length 36, full space 7.25×10^26; level 16 alone would be months.
  Branch-and-bound against the cap does not bite (bound 62.7 at depth 1, still 22.1 at depth 6, never below
  7). The cap `n−1` sits far above the true supremum, so realisability prunes almost nothing — the margin
  that makes order 8 easier mathematically makes it harder combinatorially.
- **`[VERIFIED]` The enumeration is faithful**: each LP-realisable word's own witness readings, run through
  the actual cascade (latest-next-opening), reproduced the claimed word 100% of the time at every length
  tested. The word space is real cascade behaviour, not a relaxation artefact — a hypothesis tested and
  refuted, not assumed.
- **`[EMPIRICAL — exact]` The extremal readings are forced into a closed form**: `u_k = (n−1)·((n−1)/(n+1))^(k−1)`,
  matching the LP's minima digit for digit at order 8 (7, 49/9, 343/81, 2401/729, 16807/6561, 117649/59049).
  Hence `R = ((n+1)/(n−1))^(n−2)`, since the ladder needs one runner per rung and only `n−2` runners exist.
- **It reproduces a theorem we own**: at `n = 5` the formula gives `27/8`, exactly the order-5 certificate's
  proven value. At `n = 8` it gives 4.5172 against a cap of 7. Holds for every `n ≥ 4`; `n = 3` is the
  boundary case (2 vs 2) and is already proved separately.
- **Two named gaps**: ladder maximality (observed at every depth, and the pattern breaks at `d = 7` exactly
  when runners run out — `33/7` instead of `(9/7)^7`), and a bound on the return correction (+2% at order 5,
  +4% at order 8; unbounded in general). Lemma A and B are in hand; Lemma C is open.
- **Scope**: Existence at order 8 remains open; the gate still reports it unstated.
