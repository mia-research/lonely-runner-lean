# Unfreezing v7 — the plan for v8

2026-09-15. Inputs: `MANUSCRIPT_v7.md` (683 lines, read in full), `V7_REVISION_LIST_v1.md` items 1–52,
`OBJECTION_LEDGER_v1.md` Parts 1–7, `LOST_FUNCTIONS_v1.md`. Nothing in v7 is changed; v8 is a new file.
Framework rules that bind every line of v8: outcomes stated in the framework's objects; no density, covering or
blocking framing; any import found is excised and replaced (items 50–51, ledger Part 7).

Legend — **A** apply; **D** needs the owner's decision (§3); **S** superseded by a later item (the later item is
applied instead); **N** no manuscript change (record only).

---

## 1. Triage of the revision list

| item | v7 place | action | what goes into v8 |
|---|---|---|---|
| 1 | §1.3, §7.1 | **S** by 12, 27–31 | no window anywhere in the construction ("free `D`" is not the framework's object, item 12) |
| 2 | §7.4 | **S** by 27, 31–32 | the two-family Claim is replaced by the cascade's open statement |
| 3 | §1.3 | **A** | §1.3's over-strong window target removed; the time is the end of the cascade, named exactly |
| 4 | §7.2 | **S** by 25 | completeness over openings at every lap is `reading_complete` (in the frozen digest) |
| 5 | §7.3 | **A** | soundness stated on the cascade's fixed point (`lonely_of_fixed`) |
| 6 | Lean `procedure_sound` | **D** (Q1) | rename/restate on the cascade, or leave `ConstructionN` untouched |
| 7 | §8 | **A** | table row: the clearing test at a scale is `coord_iff` (commensurate) / the band identity (real) |
| 8 | §9 | **A** | `two_sigma_zone_inside` needs `3 < n` |
| 9 | — | **A** after reading sources | restore H1, wrap gap / global start / gap migration, relay anatomy (231,294 / 0 reaching the end), Part II perturbation mechanisms (`LOST_FUNCTIONS_v1` §§E–H; source `PROOF_DEV_v1`) — each stated in framework objects, or recorded as not restored with the reason |
| 10 | §1.1 | **A** | "reading `v_j − v_i` is what `i` is lonely means; not a WLOG" |
| 11, 13 | §1.1, §2.2, §7, §8 | **A** | the method is real-valued; `coord_iff` is its exact integer representation for commensurate arrangements; the AP reference is commensurate necessarily (`commensurable`) |
| 12 | §7.1, §7.4 | **A** | the cascade in the owner's words; the hard cases' times on the `d_min` lattice: `43/240` (`u = 5 + 3/8`), `17/15792` (`u = 2 + 1/8`) |
| 14 | several | **A** | every listed defect corrected: §7.2 "always an opening" (true for the cascade, false for v7's second family — moot once the families go); §7.4 nesting ("every grid satisfies the residue test" false); **§1.2 cell decision by an interior point, not by two ends**; §1.3 vs §7.1 contradiction (moot); abstract's "every result asserted as proved is formally verified" (restate precisely); gate check [4] greps names only; §7.1 ceiling prose (`8D > mp`); §5 understates (2(b) derived — see below); minor items (parts 1–7 undefined; §6.1 "subject" → end runner; §9 ratio bounds' section; "descent" undefined; `Reference.lean` docstring) |
| 15 | §7 evidence, §8 | **A** | `IrrationalCascade_v1.lean`: every runner of `(1, 1+√2/100, 3, …, 8)` in Lean, irrational time `75√2/4` |
| 16 | §4.3–4.4, §7.1 | **A** (with 29) | the cascade is deviation from an ideal (AP of any real gap; `CascadeRule_v1.lean` declarations); the scale is given by the recursion of item 29 — **owner to confirm this is the cascade's statement (Q2)** |
| 17, 19, 20 | — | **S** by 22, 34 | gcd-lattice frame left behind; the mechanism is restated as the own-AP residue rule (item 34) |
| 18 | §7, §8, gate | **A** | the dead lattice (`dead_iff`, `dead_downward`, `exists_live`) stated in the `d_min` frame; §8 rows; gate headline list |
| 21 | §4.5 | **A** | per-runner spread bound `⌊d_max/(8·d_min)⌋ + 1` for the first live lattice (item 22); Thm 4.9's relation to `S/7` clarified |
| 22 | §7 | **A** | the frame: the AP scale for a runner is its own `d_min` (`RESIDUE_BAND_v1`) |
| 23 | §7A | **A** | "no global clock" keeps the ban on *needing* a shared event, and states (a) the AP reference **is** globally isolated (φ(n) law), (b) the slowest runner's lap is the cycle |
| 24 | §4 | **D** (Q4) | fitting between AP locations: stated, but "how the fit feeds each reading" is open — include as a stated open item or leave out |
| 25 | §7.2, §8 | **A** | `reading_complete`, `localisation_free`, `spine_all_or_nothing`, `step_ceiling`, `blocked_lands_on_threshold`, `unblocked_stays_clear` in §8; §8's "Prop 7.1 only outside the digest" corrected |
| 26 | §7 | **N** / optional | `BufferRoom` (computed move over real readings) — a special case of the cascade's move; one sentence at most |
| 27 | §7 | **A** | **the construction: the moment iteration** — from `1/(8·d_min)` move to the largest next opening of the runners in the way (207,464 of 207,464 = BSM) |
| 28 | §7 | **A** | the flank at the first isolation time; setters change at every move |
| 29 | §7 | **A** | the scale recursion `D_{n+1} = D_n · min{s/(8N+1) : |s − 8N| < 1}`, time `1/(8·D_final)` |
| 30 | §7 | **A** | the chain is the run of lap-completion zones; drift lines at own-AP instants; scale bridge (`inWay_at_scale_iff`, `nextOpening_at_scale`); the refuted product formula recorded |
| 31 | §7 | **A** | first isolation time = end of the run of lap zones from the bound (`first_isolation_as_zone_run`) |
| 32 | §7 | **A**, one sentence **excised** | finiteness and `lonely_iff_run_ends`; drift lines. **Excised:** "the framework's open statement and LRC(8) for that runner are now one statement" (a relabel) — replaced by the statement in framework objects |
| 33, 34 | §7 | **A** | slot-sharers remove every own-AP instant; the own-AP residue rule at every reading denominator (40,000 of 40,000) |
| 35, 36 | §7 evidence | **A** | the time ratio `R = d_min/D_final`: largest found ≈ 11.96 at `S ≈ 7.44`; no `R ≥ 16` found; depth has no ceiling at 24 — graded EMPIRICAL |
| 37–48 | §9 | **D** (Q3) | moment iteration at every threshold `1/n`; termination at small orders (Version B rows) |
| 49–51 | — | **N** | document hygiene; v8 must satisfy item 51's excisions |
| 52 | §4 / §9 | **A** (order 8) + **D** (order 5, Q3) | at order 8: exact AP readings with no index `≡ 0 (mod 8)` give `R = 1` (derived; run on 7,950 arrangements); with a slot-sharer `R ≤ 5/2` in that sample. Order-5 mechanism with Q3 |

## 2. Triage of the objection ledger and `LOST_FUNCTIONS_v1`

| source | action |
|---|---|
| Ledger Part 1 (nine objections that do not apply) | **D** (Q4) — referee-facing section, or omitted |
| Ledger Part 2 (objections that apply) and Part 4 (false blockers) | v8 must not state Part 4's false blockers; Part 2's surviving content is the open statement of §7 and "the evidence is finite" |
| Ledger Part 5 | = items 11, 13 |
| Ledger Part 6 | = item 12 and the Lean instances of items 13, 15 |
| Ledger Part 7 | v8 carries none of the excised imports |
| `LOST_FUNCTIONS` §A (four spine instants), §B (residue test beyond grids), §C (dilation invariance) | **A** — v7 restored the four-instant row; §B's reach beyond grids and §C's ratio-native reading go into §2/§7 |
| `LOST_FUNCTIONS` §D (W1 two cases, 91,456) | **A** — the start spine *or* one eighth past a lap line: this is the cascade's bound and openings (item 27); graded count restored |
| `LOST_FUNCTIONS` §§E–H | item 9 |
| `LOST_FUNCTIONS` §I (ten verification counts dropped) | **A** where the underlying statement stays in v8 |

## 3. Decisions for the owner

- **Q1 — the Lean artefact.** v7's artefact is `Construction8` (frozen digest `578022e0…`, gate `scripts/n8/gate.sh`). The
  cascade's Lean (`MomentIteration_v1–v6`, `MomentIterationN_v14`, `CascadeRule_v1`, the irrational instances) lives in
  `experiments/`, outside every tree. Options: move it into `LonelyRunner/LRC/` as a new module set with its own gate
  (Construction8 stays frozen); cite the experiment files by SHA-256 as they are; or unfreeze Construction8.
- **Q2 — what v8 establishes, and how it is stated.** Proposed: three framework outcomes —
  **Construction** (the cascade's fixed point is lonely and first; proved), **Localisation** (every lonely time is at or
  after the cascade's time, which is an opening; proved), **Existence** (the cascade reaches a clear scale — equivalently
  the run of lap zones from the bound ends; open) — with one sentence afterwards on the relation to the conjecture as a
  consequence. Also: confirm item 29's recursion as the cascade's statement, and whether §7A's "no first-instant
  demand" row stays (the first-ness is now a proved property of the output, not a demand).
- **Q3 — the general-order and small-order results** (items 37–48, 52's order 5). In v8 §9, in a companion document, or
  out.
- **Q4 — §6 negative results and the ledger's Part 1.** v7 §6 refutes routes (bounding how little the in-the-way sets
  amount to; the relay; the `s = 8` count). Keep as contributions stated in framework objects, cut, or move to an
  appendix; and whether a referee-facing "objections that do not apply" section is wanted. Same question for item 24.

## 4. Proposed v8 outline (pending §3)

| § | content | from |
|---|---|---|
| Abstract | the framework, the cascade, what is proved (Construction, Localisation), what is open (Existence), the Lean artefact | v7 abstract rewritten; item 14 |
| 1 | the shift; per-runner reading (not a WLOG); BSM with cells decided by interior points; exactness for commensurate, band test for real | v7 §1.1–1.2; items 10, 11, 13, 14 |
| 2 | local scale `d_min` and readings; ratio-native / dilation invariance; `(a, m)` test as the commensurate representation | v7 §2; `LOST_FUNCTIONS` §C; items 11, 13 |
| 3 | local restrictions | v7 §3 unchanged except item 14 minor fixes |
| 4 | gaps, the regular `n`-gon, the AP reference and its survival; exact AP readings (`R = 1` without a slot-sharer); the settled cases 4.8, 4.9 with the spread bound | v7 §4; items 21, 23, 52 |
| 5 | no external dependency: 2(b) derived in `ConstructionN/Instants.lean` (`isolation_iff_coprime`, `card_coprime_eq_totient`, `isolation_forces_coprime_grid`) | v7 §5; item 14 |
| 6 | negative results | v7 §6 (Q4) |
| 7 | **the cascade**: the move; the scale recursion; completeness over openings; soundness and first-ness; the run of lap zones; the flank; own-AP instants — drift lines, slot-sharers, the residue rule; the dead lattice and spread bound; the open statement (Existence); evidence (207,464 = BSM; hard cases; irrational instances; `R` searches) | items 12, 15, 16, 18, 22, 25, 27–36 |
| 7A | the firewall, with item 23's qualifications and Q2's ruling on first-ness | v7 §7A |
| 8 | formal verification: every numbered result → declaration, per artefact | v7 §8; items 7, 18, 25; Q1 |
| 9 | generalisation | v7 §9; item 8; Q3 |
| 10 | what is and is not established, in the three outcomes | v7 §10; Q2 |
| 11 | data and code | v7 §11; Q1 |

## 5. Process

1. Owner rules on Q1–Q4.
2. Read `PROOF_DEV_v1` Parts II and V for item 9 (§§E–H).
3. Write `MANUSCRIPT_v8.md` section by section, each claim with its grade and artefact.
4. Loss audit before promoting v8 (`compile-diff`, CLAUDE.md §2): old side = v7 **and** the last full-corpus sources
   (`PROOF_CANDIDATE_v3`, `PROOF_DEV_v1`, `HANDOVER_2026_09_13_v1`), new side = v8; every open item, retraction, caveat
   and grade tracked by name.
5. Update both lists: items applied are marked in a new "applied in v8" item; nothing removed.
