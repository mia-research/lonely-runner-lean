# compile-diff: MECHANISM_MAP_v1 against log E100–E188 and v21 §17C–§17E

2026-09-30. The `compile-diff` agent's loss report, saved as returned (lightly reflowed; every quote and line number is
the agent's). Successor `docs/n8/MECHANISM_MAP_v1.md`; sources `docs/n8/RUNNING_LOG_order8_v1.md` lines 3267–6271 and
`docs/n8/MANUSCRIPT_v21.md` lines 3483–3615. Repairs are carried by `MECHANISM_MAP_v2.md` (log E191).

**Range note.** Log lines 3458–3837 hold a second series headed E36–E48; E106 (l.3843): "Cite the second series as
E36b–E48b." v1's scope line does not mention them and cites none.

## Global caveats

- **G1 — v21 §17E density premise, MISSING from R3.** v21 l.3583–3585: "Any family of about fifty or more instants
  therefore succeeds on most sets by density alone. A family counts as evidence of mechanism only when it beats a null of
  the same size." l.3589: rung-selection verdict "**structure**: 2,998 of 3,000 against 2,687 for uniform instants and
  2,837 for random numerators". l.3607–3608: "So far only the rung-selection rule's numerators beat a same-size null."
  v1 R3 gives "12,309 of 12,309 … 91,523 of 91,523" and "no exception in these windows" with no null comparison; the
  2/3,000 misses of the `q ≤ 8` family (`family_null_v1.out`) not carried.
- **G2 — v21 §17D "not progress", carried reworded, partly.** v21 l.3576–3579. v1 R3 l.136–137 and §5 l.207 carry the
  growth of `q` and the restatement; "not progress" is not attached to the §3 counts.
- **G3 — E114 range caveat, MISSING as a global statement.** E114 l.4039–4043 ("larger ranges have turned up things
  smaller ones did not"); E131 l.4653–4654 classes it global; E170 l.5515–5517 corrects the `2k+1` item to an
  order-five fact.
- **G4 — v21 §17C field usability, MISSING.** v21 l.3544–3547: "The first nine are positive arithmetic, usable by any
  proof … The other ten are negated certificate families, usable only by a proof that goes through those same
  families." v1 Q5 relies on the case-list form without this.
- **G5 — owner rulings on tools, MISSING.** E101 l.3301–3303 (a measure argument inside a single window, provisional);
  E131 l.4682–4683 (not withdrawn); E112 l.3967–3972 (density, coverage, counting as tools when they "arrive
  organically"). v1 §0 l.37 says "no density, no coverage, no rate as an answer" without them.
- G6 (O1, E109) carried reworded; G7 (E177) carried.

## (A) Items bearing on a v1 statement, absent or weakened

- **A1** §2A l.76 "(so a run has at most 7 moves)": E171 l.5544 (waves, at most seven moves), E172 l.5584 (a move
  budget is an imported shape), E173 l.5619–5621, E184 l.6038–6040 ("E183's target was a cap"). v1's own F1 names move
  budgets.
- **A2** `grid_class_clear`: E129 l.4624 "one class, any number of readings per edge, small-deviation conditions";
  v1 l.73 (following E162 l.5386–5388) omits the condition.
- **A3** `lonely_of_separation`, `move_eq_separation`: E159 l.5263–5264 "if each keeps its band, all are clear there";
  E160 l.5310–5311 "a separation whose other readings keep their bands is exactly the cascade's next move". v1 l.74
  omits it.
- **A4** D1 was first found in E102 l.3338–3339 ("346,104 of 346,104"), denominators l.3340–3342, corrected in E105
  l.3448–3449. v1 attributes D1 to E188 only.
- **A5** E187 multipliers: "(relayed, their files not on disk)" (l.6174) and "local stability (`hopen`), and it does
  not bear on (B)" (l.6178–6179) dropped in v1 l.102.
- **A6** `WindowBound` OWED (E115 l.4088, l.4093); `CaseB8`, `CaseC8`, `WindowBound` OWED (E156 l.5211–5212,
  l.5243–5244); `Cover8` OWED (E166 l.5446–5450, E170 l.5523); "whether `Cover8 2 ⇔ NB(15)` is open" (E170
  l.5473–5474). v1 lists `lonelyRunnerAt8_of_window` as tracked and never names `WindowBound`; §8 lists no OWED Prop.
- **A7** E116 grade `[reasoned in the text; the pieces cited are proved]` (l.4168) and "⇐ … not in Lean"
  (l.4177–4179) dropped (v1 l.111).
- **A8** Local stability widened: E131 l.4662 (`pinch_eventually_lonely` needs a common period); E178 l.5805–5806
  ("Not proved: that an open window always coexists at every pinch after s = 0"); E180 l.5880–5881 (multi-pinches and
  the bounded-time half left open). The one-runner-move form is proved (E115 l.4105–4107; O4 l.4113–4118; E186
  l.6110–6111). v1 R7 says "Local stability, proved" of the straight deformation.
- **A9** R7 partial reflection: E181 l.5896–5898 (each other reading keeps its label and is strictly clear at `λt`);
  l.5919 `[reasoned; the pairing verified on these subsamples]` (1,712/1,712 deaths, 1,449/1,449 births). v1 l.155
  unconditional.
- **A10** E179 l.5835–5836 (the AP-window protector refuted on samples); E181 l.5923–5924 (bounded-time half open);
  E182 l.5967–5970 (a single separation is the minority; needs one global fact equivalent to the conjecture). Absent
  from v1 R7.
- **A11** R5: E183 l.5991–5992 `[VERIFIED — these samples]` (subsamples; 26%/11%/31% at l.6002) and E184's cap flag.
- **A12** R4: E188 l.6241–6244 multi-host caveat (28,764; 520).
- **A13** R8: v21 l.3600 "whether the effect is about multiples of 8 or a totient effect (author) is not settled";
  l.3596 "52% … against 18%".
- **A14** R9: E162 l.5374–5375 second scope ("counted doubled slots anywhere on the circle").
- **A15** R1: E103 l.3376–3377 ("'Lap 2 or later' measured the setter's lap, not the displacement").
- **A16** Rung row: E102 l.3339–3340 "every multiple of q lies in [e, 7e] is **false** …; the condition is residues mod
  8e in [e, 7e]". v1's condition is the corrected one; its label "R1 on the multiples" (v21 l.3589) is R1's `[m, 7m]`
  form.
- **A17** `EightResidual` field count: E108 l.3894 (21), E117 l.4230 (22nd, `no_one_free`); the Lean structure
  (`OrderEightCasesN.lean:770`) has 22; v21 l.3541 says 19; v1 cites v21 only.
- **§6 instances missing** (class: source, log lines): F7: O2 (3974–3981), O3 (4045–4048), O6 (4223–4226), E172
  "E170's 'correction to E114' was already on disk" (5588–5589); F7/F4: O9 "E143's rotation form is Theorem 6.15"
  (4933–4936); F5: E136 (4768–4770), E143 (4921), E150 (5048–5049), E152 (5113–5119); F4/F5: E137 (4793–4797); F4:
  E159 (5266–5268); F1: E171 waves (5544–5547; E172 l.5580–5584), E177 (5755–5758); F2: v21 §17E mirror meetings
  "density: 2,994 against 2,991" (l.3590), extra laps "density … Not to be pursued as a mechanism" (l.3591); no class:
  E111 proxy "The proxy is wrong, not the cascade." (3957–3961; E131 l.4658); O7 range-forced (4378–4382; E151 l.5086;
  E153 l.5145–5146).

## (B) Numbers, names and entry numbers that do not match

- **B1** "3,897 misses (E175)": the figure is in E174 (l.5649, l.5660), not E175.
- **B2** F3 "E126 'the unsettled are captured readings'": source is E129–E130 l.4630.
- **B3** F6 "E126's control against tautology": source is E129–E130 l.4632.
- **B4** "(so a run has at most 7 moves)" citing E183: E183 l.5985 says "at most `7 (U + 1)` setters"; seven per wave
  is E171/E173; observed chains are longer (E170 l.5504: Case B max 19, late shapes 17–25).
- **B5** `first_isolation_of_fixed` under "Equivalences": E109 l.3907–3909 calls it a by-product, not an equivalence.
- **B6** "`existenceAt8_iff_residual` … (difference-set form; sufficient)" and "Standing: whether `EightResidual` is the
  obligation": E104 l.3393–3394 and E156 l.5211 record `OrderEightN.lonelyRunnerAt8_iff_residual`, both directions,
  on disk at `OrderEightCasesN.lean:982`.
- **B7** "9 on [1,30], 16 on [1,40], §17E": the figures are in `LonelyRunner/experiments/nN/rung_selection_v1.out`, not
  in v21 §17E's text.
- **B8** Q3 "§17D's 12, 15, 16": v21 l.3571–3572 "The rational-opening families would need **N** = 12, 15, 16" — the
  rational-opening `N`, not the rung `q`.
- Verified without mismatch: "692 of the 768" (`place_768_v1.out:26`); 1,329 = 91,523 − 90,194; the other R1–R9 and D
  figures; §0's "(log E189)".

## (C) Open items and retractions in range not carried, bearing on nothing v1 states

Second series: E36b (lap `j` not examined; ordering lemma not stated; coarse class untested); E37b (mechanism from one
trace; DoorArrives vs DoorFlank the author's call); E38b ((a), (b) open; type test not run); E39b (overstate/miss
caveats; no extrapolation to 6-D); E40b (not proved or formalised; one family); E41b (end-case table does not carry
over); E42b (no law for general grids); E47b (`413ρ` outliers not examined); E48b (`omega` incompleteness mod 8).

Main series: E102 (owed reverse R1, bound-grid lemma, Lonely8 wrappers; two docstring defects); E104 ([1,40] residual
empty is a window, not a proof; stale handover item); E105 (existential correction; converse graded too high, owed
`classClear_iff_band`; `not_fast` one-sided); E108 (neighbourhood theorems untested); E109 (v7 never loss-checked);
E110 (failure modes at a general lattice `D` owed); E115 (what `WindowBound` contains, not in Lean; E134 correction);
E117 (one-free reach not progress); E118 (plan v2 correction; C1 not proved); E119 (analytic Case B open); E120 (band
categories exhaust not proved; four stalled routes); E121 (what bounds the jump); E122 (copy-0/copy-1 open); E123 (band
certificate not the analytic proof); E124 (exhaustion by computation; Lean translation not done); E125 (junction step
open; refutations not the mechanism); E126 (Case B not phase-free; crowd run-out not done); E127 (simultaneity not
derived); E128 (`(j, m ≤ f(S), c)` not derived); E129–E130 (O8 label slip); E131, E132, E134 (handover items; `c ≤ 7`
closed by E159); E135 (doubled edges; example-list bug); E136 (crossing edges ⇒ two-block, next); E137 (derivation
per level `K` owed); E141 (sweep decomposition not checked on all chains); E144 (scope of the null); E146 (composition
not the decider); E148, E149, E151 (fast group in the slow group's block owed); E152 (recursive R1 splitting the wrong
cut); E153 (six-window lemma false on fine shapes); E155 (hill climbs explain nothing); E156–E158 (CoverB8/CoverC8 OWED,
retired E166; ad hoc regime list not used); E160 (residues alone do not determine the transport); E161 (open core:
bridges cannot sustain the chain); E163 (what is left); E164–E166 (CaseB8/CaseC8 off the path, still OWED); E170 (gap
E167–E169; joint rank not tested; band cover untracked); E173 (quote not on disk; 484 late-shape hosts); E184 item 2
(in-place edits to E174, E175); E177 (next place-test step); E179 (Case C naming weak); E185 (R8 check not exercised).

v21: §17C (first-lap clearance provisional; last class adds no case; `resolutionCap8 = 64` a case boundary; mirror
centre reaches the certificate only through its cell); §17E (robust order-six lemma false as stated; order-five recipe
fails; length step fails on 801 of 38,760; fast-pair constant 0 of 28; sign rule not re-derived; item 2 not a uniform
lower-order bound; item 5 ladder vs rational openings not worked out).

## Mechanical

34 of 34 declarations resolve (line checks included); 19 of 19 modules match `git ls-files` (14 tracked; 5 untracked as
v1 says); 7 of 7 paths exist; commit `3ea9feb` exists; 3 of 3 memory files exist. No retracted numerical claim returns.
