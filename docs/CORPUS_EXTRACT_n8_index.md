# Corpus extract — supersession-aware index of `docs/n8/`

2026-09-07 corpus, indexed 2026-09-07. **This is a reference index, not a review.** No
quality assessment, no defect hunt, no opinion. Every claim recorded below is a verbatim
quote with file and line number, obtained by opening the file at that line.

## The object tracked

For each file in `docs/n8/`: **(a) what it claims, (b) at what grade, (c) whether a later
file supersedes it.** Each of the three is checked directly against the file's own text —
(a) from its title and section headings, (b) from the grade tokens it actually contains
(counted mechanically per file, then read in place), (c) from an in-file supersession
sentence where one exists. Where a file states no supersession relation for itself, it is
marked **"supersession not stated in-file"** rather than inferred.

Scope: the 32 `.md` files in `docs/n8/`. Two files outside that directory are quoted in
§3 only, because `CLAIM_GRADES_v1.md` names a "session summary" that is not in `docs/n8/`
and four of its eight rows trace there; those quotes are labelled `[OUTSIDE docs/n8]`.

---

## 1. VERSION CHAINS

Ordering within a chain is by the file's own supersession sentence where it has one, and
otherwise by modification time (all 32 files carry the in-file date `2026-09-07`).

### 1.1 `D7_ATTACK_v1 → v2 → v3 → v4 → v5` (five versions)

This chain uses **"Continues"**, never "Supersedes", and one link (v2→v3) is unstated.

| version | in-file relation sentence | status |
|---|---|---|
| v1 | none — opens `# Attacking D7 in the n=8 setting — the width route, and why it does not close` (`D7_ATTACK_v1.md:1`) | **SUPERSEDED** by v2/v3 in continuation, but v1 §1's width formula is carried forward, not withdrawn. Supersession not stated in-file. |
| v2 | `D7_ATTACK_v2.md:3` — "2026-09-07. Continues `D7_ATTACK_v1.md` (width route: refuted). Artifacts:" | **SUPERSEDED** by v3. **v3 does not say so.** Supersession not stated in-file — established here by `diff`: v3 is byte-identical to v2 except that v2's §5 direction 2 is struck out and replaced by a retraction section. |
| v3 | `D7_ATTACK_v3.md:3` — "2026-09-07. Continues `D7_ATTACK_v1.md` (width route: refuted). Artifacts:" (identical wording to v2; v3 never names v2) | **SUPERSEDED** by v4, which names it. |
| v4 | `D7_ATTACK_v4.md:3` — "2026-09-07. Continues `D7_ATTACK_v3.md`. Two questions asked and answered; both" | **SUPERSEDED** by v5, which names it. |
| v5 | `D7_ATTACK_v5.md:3` — "2026-09-07. Continues `D7_ATTACK_v4.md`. The blocking-grammar frame" | **CURRENT** in this chain. |

The one substantive v2→v3 delta, quoted in full at `D7_ATTACK_v3.md:92`:

> "2. ~~**Count the blocks, not the points.**~~ **RETRACTED — see below.**"

### 1.2 `SEARCH_REDUCTION_v1 → v2 → v3 → v4 → v5` (five versions)

The most explicit chain in the directory: each version names every predecessor and gives
the reason.

| version | in-file relation sentence | status |
|---|---|---|
| v1 | none | **SUPERSEDED** — named by v2, v3, v4, v5 as "wrong prime set". Supersession not stated in v1 itself. |
| v2 | `SEARCH_REDUCTION_v2.md:3` — "2026-09-07. Supersedes `SEARCH_REDUCTION_v1.md`, which named the wrong prime set" (continues line 4: "and left the validation incomplete.") | **SUPERSEDED** by v3–v5. |
| v3 | `SEARCH_REDUCTION_v3.md:3-4` — "2026-09-07. Supersedes v1 (wrong prime set) and v2 (§1 wrongly accused / `WHY_13_AND_19_v2.md` of inverting the p=41 exception; it did not)." | **SUPERSEDED** by v4, v5. |
| v4 | `SEARCH_REDUCTION_v4.md:3-5` — "2026-09-07. Supersedes v1 (wrong prime set), v2 (§1 wrongly accused / `WHY_13_AND_19_v2.md` of inverting the p=41 exception; it did not) and v3 / (§4 overstated the validation as "every published data point" — see §4 below)." | **SUPERSEDED** by v5. |
| v5 | `SEARCH_REDUCTION_v5.md:3-6` — "2026-09-07. Supersedes v1 (wrong prime set), v2 (§1 wrongly accused / `WHY_13_AND_19_v2.md` of inverting the p=41 exception; it did not) v3 / (§4 overstated the validation as "every published data point") and v4 (§1's LR-property / figure was computed in floating point — replaced below by an exact certificate)." | **CURRENT.** |

### 1.3 `COLLAPSE_Z163_v1 → v2` (two versions)

| version | in-file relation sentence | status |
|---|---|---|
| v1 | `COLLAPSE_Z163_v1.md:3` — "2026-09-07, continuing `P163_ARGUMENT_v1.md` §6. Target: understand why the" | **SUPERSEDED** by v2, which names the defect. Supersession not stated in v1 itself. |
| v2 | `COLLAPSE_Z163_v2.md:3` — "2026-09-07, continuing `P163_ARGUMENT_v1.md` §6. **v2 corrects one number in §5**: v1 reported the `|D|` distribution as "concentrated at `|D| ≤ 7` (48 699 pairs)". That figure is an addition slip and matches no cumulative of the histogram — the correct value is **51 184** (46 739 at `≤5`, 49 920 at `≤6`), out of 52 326. Caught by an independent re-run of `x5_two_odd_v1.py`, not by re-reading. Every other figure in this document reproduced exactly." | **CURRENT.** |

`diff` confirms the only content changes are line 1 (title), line 3 (the sentence above)
and line 129 (the corrected figure).

### 1.4 `WHY_13_AND_19_v1 → v2` (two versions)

| version | in-file relation sentence | status |
|---|---|---|
| v1 | none | **SUPERSEDED**, named by v2 with a reason. Supersession not stated in v1 itself. |
| v2 | `WHY_13_AND_19_v2.md:3-4` — "2026-09-07. Supersedes `WHY_13_AND_19_v1.md` (which lacked the `k=7` validation / and the corpus synthesis)." | **CURRENT.** |

### 1.5 `F_LOWER_BOUND_v1 → v2` (two versions)

| version | in-file relation sentence | status |
|---|---|---|
| v1 | none | **SUPERSEDED.** v2 states the delta only in its title, never in a body sentence naming v1 — so v1 carries no supersession statement and v2 carries no explicit "supersedes v1" sentence. **Supersession not stated in-file on either side**; established here by title and `diff`. |
| v2 | `F_LOWER_BOUND_v2.md:1` — "# `f(8,p) ≥ 6` is FALSE as stated — three counterexamples, and what survives (v2: range extended to 700)" | **CURRENT.** |

`diff` confirms the only changes are the title and the range `300 → 700` at lines 45, 47-48.

### 1.6 `RIGID_CLASS_v1 → v2` (two versions, plus a pre-registration)

| version | in-file relation sentence | status |
|---|---|---|
| v1 | `RIGID_CLASS_v1.md:3` — "2026-09-07. Follows `EXACT_PHI_N_AP_v1.md` §3, which surfaced an open item and did not" | **SUPERSEDED** by v2, which names two defects. |
| v2 | `RIGID_CLASS_v2.md:3-5` — "2026-09-07. Supersedes `RIGID_CLASS_v1.md`. Two changes: **v1's Corollary A was stated / without a hypothesis its own Lemma A carries**, and the exhaustive sweep specified by / `PREREG_RIGID_CLASS_v1.md` turned up a second missing condition. Both are now proved." | **CURRENT.** |
| `PREREG_RIGID_CLASS_v1.md` | `PREREG_RIGID_CLASS_v1.md:3` — "**Status: PRE-REGISTRATION, written before any rigidity datum is seen. Not a result.** 2026-09-07." | **CURRENT** — a specification, not a version of v1/v2; it sits between them by mtime (v1 11:37, prereg 11:42, v2 11:53). |

**Dangling reference.** `RIGID_CLASS_v2.md:6` — "Run and results: `RIGID_SWEEP_RESULTS_v1.md`."
and `RIGID_CLASS_v2.md:83` — "**Sufficiency is false**, and not marginally — see `RIGID_SWEEP_RESULTS_v1.md`. The four".
A `find` over the whole `Math Ex` tree returns no file of that name. Recorded as a fact
about the reference, not a judgment about the claim.

### 1.7 The AUDIT / CLAIM / grade-authority files (no chain — each is `v1`)

| file | in-file relation sentence | status |
|---|---|---|
| `CLAIM_GRADES_v1.md` | `CLAIM_GRADES_v1.md:3-4` — "The session summary and `D7_ATTACK_v1–v5` / `P163_ARGUMENT_v1` state several / results at a higher grade than the evidence carries." | **CURRENT** — the grade authority. Re-grades eight claims; see §3. Not itself superseded by any file in the directory. |
| `EXACTNESS_AUDIT_v1.md` | none | **CURRENT.** Supersession not stated in-file. Its finding is folded into `SEARCH_REDUCTION_v5.md:44-45`. |
| `P163_ARGUMENT_v1.md` | `P163_ARGUMENT_v1.md:3-4` — "2026-09-07. Target: the 32-hour verification of Lemma 7 at `k = 7`, `p = 163` / (`N = 1304`, `H = 652`). Not achieved." | **SUPERSEDED IN PART** — its §1 framing is corrected by `COLLAPSE_Z163_v1.md:139-142` and by `CLAIM_GRADES_v1.md:19`; the correction is stated in those files, not in `P163_ARGUMENT_v1.md` itself. Supersession not stated in-file. |
| `PLAN_ANALYTIC_v1.md` | `PLAN_ANALYTIC_v1.md:5` — "`project_n8_rosenfeld_2026_09_07`. Supersedes nothing; there was no prior plan." | **CURRENT.** |

### 1.8 Single-version files with no chain

`CAP_TABLE_UNIFORM_v1.md`, `EXACT_PHI_N_AP_v1.md`, `N11_TRANSLATION_v1.md`,
`PHI_N_GRANULARITY_v1.md`, `P_UNIFORMITY_v1.md`, `ROSENFELD_REVIEW_v1.md`,
`THEOREM2_CITATION_VERIFIED_v1.md`, `TOP_GAP_v1.md`, `source_integrity.md`. None states a
supersession relation for itself: **supersession not stated in-file** for all nine. Two
carry partial in-file corrections of their own earlier content or of a cited artefact —
see §5.

---

## 2. ONE ROW PER FILE

Grade tags are those the file actually contains, collected mechanically then read in
place. `—` means the file uses **no bracketed grade tag**; where such a file uses a
prose grade word instead, that word is given in quotation marks. Times are modification
times, used only for chain ordering; every file's in-file date is `2026-09-07`.

| filename | date | one-sentence subject | current or superseded (and by what) | grade tags it uses |
|---|---|---|---|---|
| `ROSENFELD_REVIEW_v1.md` | 2026-09-07 (07:13) | Review of Rosenfeld arXiv:2509.14111v2, its architecture, its 32-hour `p = 163` cost, and the analytic target named in his §7. | CURRENT — supersession not stated in-file | `CITED` |
| `THEOREM2_CITATION_VERIFIED_v1.md` | 2026-09-07 (07:32) | Verification that Rosenfeld's Theorem 2 is MSS 2025 Theorem A, with the runners-vs-speeds convention delta. | CURRENT — supersession not stated in-file | `CITED`, `[CITED — peer-reviewed]`, `PROVED` (in "needs Theorem A to be `[PROVED]`") |
| `source_integrity.md` | 2026-09-07 (07:32) | SHA-256 table for the four PDF sources plus the Giri–Kravitz version-pin warning. | CURRENT — supersession not stated in-file | — |
| `WHY_13_AND_19_v1.md` | 2026-09-07 (07:45) | The `k = 6` Lemma 7 exception pattern explained by one tuple's lonely window against the grid. | SUPERSEDED by `WHY_13_AND_19_v2.md` (stated in v2:3) | — ("**verified computationally**", line 106) |
| `WHY_13_AND_19_v2.md` | 2026-09-07 (07:48) | Same mechanism extended to `k = 7`'s `p = 41` exception, plus the identification with the n=11 `x₀(E)` count and Conjecture 5.2-SR-H. | CURRENT | — ("exact rational arithmetic", line 122) |
| `D7_ATTACK_v1.md` | 2026-09-07 (08:10) | The exact lonely-window width formula and `kill(T)`, and why the uniformisation over tuples fails. | SUPERSEDED (continued by v2/v3, then v4, v5) — supersession not stated in-file | — ("**proved and verified**", "**refuted**", lines 87, 89) |
| `D7_ATTACK_v2.md` | 2026-09-07 (08:17) | The `j = 1, 2, 3, …` chain: at `j = tp` it recovers Lemma 4; the new content is exact block self-similarity. | SUPERSEDED by `D7_ATTACK_v3.md` — **supersession not stated in-file** (established by `diff`) | — ("**derived and verified exactly**", line 105) |
| `D7_ATTACK_v3.md` | 2026-09-07 (08:19) | v2 plus a retraction of its own §5 direction 2 (block counting). | SUPERSEDED by `D7_ATTACK_v4.md` (stated in v4:3) | — ("**derived and verified exactly**", line 124) |
| `D7_ATTACK_v4.md` | 2026-09-07 (08:23) | The φ(n) law gives no leverage, and the block recursion has no exclusive zone. | SUPERSEDED by `D7_ATTACK_v5.md` (stated in v5:3) | — |
| `D7_ATTACK_v5.md` | 2026-09-07 (08:27) | Under `x = j/p` normalisation, "Lemma 6 for all large `p`" is LRC for `k` itself; the tractable target is the 27 fixed primes. | CURRENT in this chain | — ("**derived and verified**", line 101) |
| `P163_ARGUMENT_v1.md` | 2026-09-07 (08:34) | First attempt to replace the 32-hour `p = 163` search; the gcd condition in closed form as a two-odd-speeds parity condition. | SUPERSEDED IN PART — §1 framing corrected by `COLLAPSE_Z163_v1.md:139-142` and `CLAIM_GRADES_v1.md:19`; not stated in-file | — ("**established**", line 86) |
| `CLAIM_GRADES_v1.md` | 2026-09-07 (09:04) | Re-grades eight claims made in the session summary, `D7_ATTACK_v1–v5` and `P163_ARGUMENT_v1`. | CURRENT — the grade authority | `PROVED`, `VERIFIED-INSTANCE`, `EMPIRICAL`, `CITED`, `ASSERTED` |
| `COLLAPSE_Z163_v1.md` | 2026-09-07 (09:04) | The `8 | v` collapse to `ℤ/163`, the 2-adic cap table, `f(8,163) = 7`, and the `x = 5` sector decided. | SUPERSEDED by `COLLAPSE_Z163_v2.md` (stated in v2:3) | `PROVED`, `VERIFIED EXHAUSTIVELY` |
| `SEARCH_REDUCTION_v1.md` | 2026-09-07 (09:09) | Two reductions of the Lemma 7 search: WLOG `1 ∈ T` by unit scaling, and a forced coarse speed. | SUPERSEDED by v2–v5 (stated in v2:3, v3:3, v4:3, v5:3) | `PROVED`, `VERIFIED against` |
| `SEARCH_REDUCTION_v2.md` | 2026-09-07 (09:34) | Same two reductions plus the correction that `S` has 27 primes, 41 omitted. | SUPERSEDED by v3–v5 (stated in v3:3-4, v4:3-5, v5:3-6) | `PROVED`, `CITED`, `VERIFIED against` |
| `SEARCH_REDUCTION_v3.md` | 2026-09-07 (09:35) | v2 with §1's accusation against `WHY_13_AND_19_v2.md` retracted. | SUPERSEDED by v4, v5 (stated in v4:3-5, v5:3-6) | `PROVED`, `CITED`, `VERIFIED against` |
| `SEARCH_REDUCTION_v4.md` | 2026-09-07 (09:35, listed 10:00) | v3 with the validation scope corrected and the `k = 4` `p = 13` item resolved. | SUPERSEDED by v5 (stated in v5:3-6) | `PROVED`, `CITED` |
| `SEARCH_REDUCTION_v5.md` | 2026-09-07 (10:15) | v4 with the `p = 41` LR-property figure replaced by an exact certificate `1/7` at `t = 5/28`. | CURRENT | `PROVED`, `CITED` |
| `PHI_N_GRANULARITY_v1.md` | 2026-09-07 (09:54) | The per-class coverage granularity law `g = gcd(v,n)`, identifying the n=8 block structure with the φ(n) permutation law at composite `n`. | CURRENT — supersession not stated in-file | `PROVED`, `VERIFIED EXHAUSTIVELY`, `DERIVED` |
| `COLLAPSE_Z163_v2.md` | 2026-09-07 (10:00) | v1 with the `|D| ≤ 7` count corrected from 48 699 to 51 184. | CURRENT | `PROVED`, `VERIFIED EXHAUSTIVELY` |
| `EXACTNESS_AUDIT_v1.md` | 2026-09-07 (10:15) | AST audit of all 20 scripts for float-capable sites; one genuine breach found and replaced by an exact certificate. | CURRENT — supersession not stated in-file | — |
| `EXACT_PHI_N_AP_v1.md` | 2026-09-07 (10:28) | The φ(n) AP law re-verified in exact rationals; the `n = 8` "anomaly" dissolves, and two non-AP rigid witnesses surface. | CURRENT — supersession not stated in-file | `PROVED` |
| `RIGID_CLASS_v1.md` | 2026-09-07 (11:37) | Two necessary conditions (C1), (C2) for a tuple to be rigid, each with a necessity proof; sufficiency left open. | SUPERSEDED by `RIGID_CLASS_v2.md` (stated in v2:3) | `PROVED`, `VERIFIED-INSTANCE` |
| `PREREG_RIGID_CLASS_v1.md` | 2026-09-07 (11:42) | Pre-registration of the C1 & C2 rigidity sweep: statistic, arms, controls, power, scope, falsification, pre-committed conclusions. | CURRENT | `PRE-REGISTRATION`, `EMPIRICAL`, `ABSTAIN` |
| `RIGID_CLASS_v2.md` | 2026-09-07 (11:53) | Four necessary conditions (C0)–(C3) with Corollary A corrected and Lemma C added; sufficiency reported false. | CURRENT | `PROVED` |
| `CAP_TABLE_UNIFORM_v1.md` | 2026-09-07 (12:18) | The 2-adic cap table, pair-type classification and `x ≥ 1` forcing derived for every odd prime, not just `p = 163`. | CURRENT — supersession not stated in-file | `PROVED` |
| `P_UNIFORMITY_v1.md` | 2026-09-07 (12:21) | Which inputs of the sector argument are formulas in `p`: `U_min(1)`, `U_min(2)` closed forms; `maxD(p)` empirical; the filter-only route measured shut across `S`. | CURRENT — supersession not stated in-file | `PROVED`, `EMPIRICAL` |
| `F_LOWER_BOUND_v1.md` | 2026-09-07 (12:27) | `f(8,p) ≥ 6` is false at `p = 11, 17, 19`; the repaired claim holds for primes `23 ≤ p ≤ 300`. | SUPERSEDED by `F_LOWER_BOUND_v2.md` — **supersession not stated in-file on either side** (title and `diff` only) | `PROVED`, `VERIFIED-scope`, `EMPIRICAL` |
| `F_LOWER_BOUND_v2.md` | 2026-09-07 (12:28) | Same, with the verified range extended to `23 ≤ p ≤ 700`. | CURRENT | `PROVED`, `VERIFIED-scope`, `EMPIRICAL` |
| `TOP_GAP_v1.md` | 2026-09-07 (12:42) | A top-gap theorem from machine-verified `intLRC_seven`: any LRC(8) counterexample has `v₇ ≤ 7·v₆`. | CURRENT — supersession not stated in-file | `PROVED`, `EMPIRICAL` |
| `PLAN_ANALYTIC_v1.md` | 2026-09-07 (12:52) | Plan for an analytic `n = 8`: target (B) the 27 fixed primes, three routes R1–R3, the falsification table, and the `citation-verifier` gate. | CURRENT — "Supersedes nothing; there was no prior plan." (line 5) | `CITED` |
| `N11_TRANSLATION_v1.md` | 2026-09-07 (12:56) | Which axiom of the n=11 architecture fails at n=8 (the complementary-pair count, 4 witnesses against 7 speeds) and the `q`-witness ladder that repairs the budget. | CURRENT — supersession not stated in-file | `PROVED` |

---

## 3. THE AUTHORITY FILE — `docs/n8/CLAIM_GRADES_v1.md`

`CLAIM_GRADES_v1.md:3-4` names its own sources:

> "The session summary and `D7_ATTACK_v1–v5` / `P163_ARGUMENT_v1` state several
> results at a higher grade than the evidence carries."

The "session summary" is not in `docs/n8/`. The four rows that trace there trace to
`docs/HANDOVER_2026_09_07.md`, and those quotes are marked `[OUTSIDE docs/n8]`. This
section is the map from each corrected grade back to where the original wording still sits.

### Row 1 — "Barajas–Serra 2008 is **fully machine-verified**, §7 included." → *PROVED for the theorem; overclaim for the paper*

Original sentence, `[OUTSIDE docs/n8]` `docs/HANDOVER_2026_09_07.md:13-14`:

> "`intLRC_three/five/six` re-checked, no regression. Barajas–Serra 2008 fully
> verified, §7 included. Sorries went 7 → 0 this session."

No file in `docs/n8/` carries this sentence. The nearest in-directory statements are
narrower and are not the graded claim: `ROSENFELD_REVIEW_v1.md:103` — "- `intLRC 7` —
machine-verified, axiom-clean. Exactly Lemma 5/6's hypothesis."; and
`THEOREM2_CITATION_VERIFIED_v1.md:70` — "is `intLRC 7`, which this project has
machine-verified and axiom-clean**. The".

### Row 2 — "**Seven routes closed**, each with a reason." → *mixed; mostly EMPIRICAL or VERIFIED-INSTANCE*

Original sentence, `[OUTSIDE docs/n8]` `docs/HANDOVER_2026_09_07.md:85-89`:

> "Routes closed, each with a reason: counting (slack ≈2, `p`-independent); window
> width (`kill(T)` unbounded); the `j = tp` chain (is Lemma 4); block counting
> (sub-tuples nest, not compete); block recursion (no exclusive zone — `r ≡ −1`
> speeds enter at `s·v < 2p`); the φ(n) law (same points, AP-only, measure zero);
> prefix bounds (never exceed `k`)."

The wording still sits in `docs/n8/` at four places:

- `D7_ATTACK_v1.md:96-97` — "No claim here is that D7 is unreachable — two specific routes are closed, with / reasons, and a third (the `j = 1, 2, 3, …` chain) is identified and untested."
- `D7_ATTACK_v2.md:74` and `D7_ATTACK_v3.md:74` — "Combined with `D7_ATTACK_v1.md`, three routes are now closed with reasons:"
- `D7_ATTACK_v2.md:108` and `D7_ATTACK_v3.md:127` — "- §4: three routes closed, each with a stated reason."
- `D7_ATTACK_v4.md:71` — "## 3. Running tally of closed routes"
- `D7_ATTACK_v5.md:69-70` — "That explains, retrospectively and uniformly, why all six routes failed. They were / not near-misses; each was an attempt on something of the same strength as the goal."

### Row 3 — "It isn't a reduction, it's **the problem**. **Don't re-attack it** in full generality." → *PROVED (implication) + ASSERTED (the instruction)*

Original sentences, `[OUTSIDE docs/n8]` `docs/HANDOVER_2026_09_07.md:81-83`:

> "**Do not re-attack D7 in full generality.** With `x = j/p`, a target is uncovered
> iff the normalised speeds have the LR property, so as `p → ∞` "Lemma 6 for all
> large `p`" **implies LRC for `k`**. It is not a reduction; it is the problem."

The wording still sits in `docs/n8/` at:

- `D7_ATTACK_v5.md:66-67` — "own stated open direction" section §4: "`k = 7` that is precisely Theorem 1 — the thing we set out to prove. So the / target named in `ROSENFELD_REVIEW_v1.md` §4 as "the well-posed analytic goal" is / well-posed but **not a reduction**: it is the problem itself, restated." (lines 65-67)
- `D7_ATTACK_v5.md:106-107` — "- **D7 in full generality is not open-and-attackable; it is LRC.** The finite-`p` / version remains genuinely open and is the one worth pursuing."

### Row 4 — "**Covering is NOT the obstruction** — the gcd condition is." → *overclaim; **now corrected***

Original sentences, `docs/n8/P163_ARGUMENT_v1.md`:

- line 7 (section heading) — "## 1. The framing correction: covering is *not* the obstruction"
- lines 10-11 — "Every analysis so far in this session — window/grid, three-distance, the `j`-chain / — treated Lemma 7 as a **covering** problem. It is not, at the primes that matter." (line 12 completes it: "matter.")
- lines 25-26 — "all multiples of `8`. Covering `{1,…,652}` with 7 speeds is **easy**. The search / is hard because of the gcd side condition, not the covering."
- lines 28-30 — "This reverses the emphasis of `D7_ATTACK_v1`–`v5`. The rigidity results there / (three-distance, exact window widths) are about the covering half, which is the / half that is *not* binding."

Also `[OUTSIDE docs/n8]` `docs/HANDOVER_2026_09_07.md:93-94`:

> "The `p = 163` attempt produced a framing correction that supersedes §4's
> emphasis: **covering is not the obstruction — the gcd condition is.**"

The in-directory correction is at `COLLAPSE_Z163_v1.md:139-142` (identical at
`COLLAPSE_Z163_v2.md:139-142`) — see §5.

### Row 5 — "The prefix route is therefore **dead** on its own." → *VERIFIED-INSTANCE*

Original sentence, `docs/n8/P163_ARGUMENT_v1.md:81-82`:

> "**The prefix route is therefore dead on its own**: covering a prefix, or even the
> whole range, never exceeds `k`. Any argument must involve the parity condition."

Restated at `P163_ARGUMENT_v1.md:88` — "- §4: tool built and validated; the route it was
built for is closed."

### Row 6 — "Counting **is refuted**, not merely unproven." → *EMPIRICAL, scoped*

Original sentence, `docs/n8/P163_ARGUMENT_v1.md:87`:

> "- §3: measured; counting is refuted at this prime, not merely unproven."

Supporting sentence at `P163_ARGUMENT_v1.md:66` — "against 652 targets — slack `1.75×`.
**Counting fails again**, by the same / constant factor identified in `D7_ATTACK_v1` §3."
The cognate wording in the chain is `D7_ATTACK_v1.md:33` — "## 2. The route does NOT
uniformize — refuted" and `D7_ATTACK_v1.md:89-90` — "- §2: the natural uniformization is
**refuted** by explicit counterexample / tuples, not merely unproven."

### Row 7 — "The asymmetry is **structural**, not quantitative." → *was ASSERTED; **now PROVED***

Original sentence, `[OUTSIDE docs/n8]` `docs/HANDOVER_2026_09_07.md:109-110`:

> "Odd speeds are **not** weaker — coverage size is 162 (odd) vs 164 (`8|v`), and
> counting still fails at 1.75× slack. The asymmetry is structural:"

And `[OUTSIDE docs/n8]` `docs/HANDOVER_2026_09_07b.md:15`:

> "other way, "the asymmetry is structural, not quantitative" was an assertion and is"

The `docs/n8/` original is `P163_ARGUMENT_v1.md:103-104`:

> "this way; they see the full `ℤ/1304`. **That asymmetry, not size, is where the
> obstruction lives**, and it is the first thing to examine."

This is the one row graded **upward**. The promoting evidence is
`COLLAPSE_Z163_v1.md:46-47` / `COLLAPSE_Z163_v2.md:46-47` — "**[PROVED — the identity of
§1; VERIFIED EXHAUSTIVELY over all 648 admissible / speeds × 163 classes,
`two_adic_blocks_v1.py`, zero cap violations]**" — and it is now also derived for every
odd prime at `CAP_TABLE_UNIFORM_v1.md:43` — "## 3. The cap table  `[PROVED, all odd p]`".

### Row 8 — "It is **the only route not yet closed**." → *inherits #2 and #4*

Original sentence, `[OUTSIDE docs/n8]` `docs/HANDOVER_2026_09_07.md:117-119`:

> "**That collapse, and why two odd speeds break it, is the next thing to examine.**
> It is the mechanism behind the `p = 163` search, it is stated over a small object
> (`ℤ/163`, arc of size 41), and it is the only route not yet closed."

No file in `docs/n8/` carries the phrase "the only route not yet closed"; a grep over all
32 files returns it only inside `CLAIM_GRADES_v1.md:23`, which is the correction itself.
The nearest in-directory antecedent is `P163_ARGUMENT_v1.md:96-104` (§6, "The live
question is narrow and concrete"), which frames the collapse as the single next object.

### The authority file's own standing correction

`CLAIM_GRADES_v1.md:27-31`:

> "Items 2, 4, 5, 6 and 8 are the same move: **a null or a non-yield written up as a
> closure.** Item 4 is the one that cost something — it redirected the line away
> from covering for the rest of the session, and it was wrong. Item 7 is the
> opposite move and is the one that paid: an asymmetry that had been *asserted*
> turned out to be provable, and proving it produced the `x = 5` decision."

---

## 4. CONSOLIDATED OPEN ITEMS

Every statement in `docs/n8/` that says something is open, unproved, untested, not yet
tried, pending, or owed. Listed individually. Items in superseded files are marked
**(in superseded file)** so nothing is lost by supersession.

### `ROSENFELD_REVIEW_v1.md`

- `:108-109` — "Whether its machinery says anything about Lemma 6 for large `p` / is an open question, and the first thing worth checking."
- `:111` — "## 6. Not yet done"
- `:113` — "- The implementation repository [17] has not been fetched or reviewed."
- `:114-115` — "- §8 ("Improving the lacunary case", Theorems 8–10, Corollary 10) is read but / not assessed; it is independent of the `k = 7` proof."
- `:116-118` — "- [13] Malikiosis–Santos–Schymura and [12] Giri–Kravitz have not been obtained; / Theorem 2 is currently `[CITED]`, not verified. It is load-bearing for the / whole argument, so it needs `citation-verifier` before any grade rests on it."

### `THEOREM2_CITATION_VERIFIED_v1.md`

- `:97-98` — "Theorem A's own proof has not been read; it is accepted on peer review. That is / the appropriate grade for a published result we are not attacking."
- `:98-101` — "If a / downstream claim ever needs Theorem A to be `[PROVED]` rather than `[CITED]`, / that proof must be read and, for the Lean route, formalized — and it is / substantial (zonotopal, via their Conjecture A' and the Lonely Vector Property)."
- `:86-87` — "Rosenfeld's citation "arXiv, 2023" predates the fix. If we ever use this as a / second, independent route, **pin v4 or the MPCPS version**."

### `source_integrity.md`

- `:12-13` — "Implementation repository cited in the paper as [17]: / `https://gite.lirmm.fr/mrosenfeld/the-lonely-runner-conjecture` (not fetched)."

### `WHY_13_AND_19_v1.md` **(in superseded file)**

- `:108-110` — "- The general reformulation in §5: a **restatement**, not a theorem. No bound on / window width is proved here, and the uniformity over growing tuple families is / exactly the open part."
- `:111-113` — "- Not yet checked: whether the same single-tuple analysis explains `k = 7`'s lone / exception at `p = 41`. That is the sharpest available test of the mechanism and / is running."

### `WHY_13_AND_19_v2.md`

- `:96-97` — ""the union of blocked sets is not everything" — verified on 34/34 cases, / **analytically open**."
- `:117-118` — "Whether the geometric reframing survives that loss is exactly the / question, and it is untested."
- `:130` — "**Not established:**"
- `:131` — "- No bound on lonely-window width is proved anywhere here."
- `:132` — "- The reformulation in §1 is a restatement, not a theorem."
- `:133` — "- Whether the geometric view helps where `p` is not free (§5) is untested."
- `:134-136` — "- One discrepancy stands: for `k = 4` this implementation finds `p = 13` works, / where the paper's §7 implies `p > 17`. Unresolved; check against the author's / repository." *(later resolved — see `SEARCH_REDUCTION_v4.md:91-99`)*
- `:138-139` — "**The target remains:** a *uniform* lower bound on the widest lonely interval / over all admissible `k`-tuples"

### `D7_ATTACK_v1.md` **(in superseded file)**

- `:82-83` — "Whether that chain can be pushed to a / contradiction is untested."
- `:93-94` — "- §4: the arrangement question is untouched. **D7 remains open**, and this / document narrows rather than closes it."
- `:96-97` — "No claim here is that D7 is unreachable — two specific routes are closed, with / reasons, and a third (the `j = 1, 2, 3, …` chain) is identified and untested."

### `D7_ATTACK_v2.md` **(in superseded file)**

- `:87` — "sub-tuple `T_t`. Two untested directions follow:"
- `:90-91` — "`j = tp` *within that block* to constrain `T_t` further. Whether the nesting / terminates in a contradiction for large `p` is open."
- `:100-101` — "Direction 2 is the one worth trying next: it is specific to `k+1` composite, it / targets exactly `k = 7`, and it has not been attempted." *(retracted at `D7_ATTACK_v3.md:92`)*
- `:109` — "- **D7 remains open.** Nothing here bounds anything uniformly in `p`."

### `D7_ATTACK_v3.md` **(in superseded file)**

- `:87` — "sub-tuple `T_t`. Two untested directions follow:"
- `:90-91` — "`j = tp` *within that block* to constrain `T_t` further. Whether the nesting / terminates in a contradiction for large `p` is open."
- `:119-120` — "That leaves direction 1 (iterating the recursion inside a block) as the only / live continuation from this line, and it is unexamined."
- `:128` — "- **D7 remains open.** Nothing here bounds anything uniformly in `p`."

### `D7_ATTACK_v4.md` **(in superseded file)**

- `:99` — "D7 remains open."

### `D7_ATTACK_v5.md`

- `:96-97` — "Whether that is easier at `p = 163` than the 32-hour search is untested — but it / is the only version of the goal that is not circular."
- `:105` — "- §5 is a **redirection**, untested."
- `:106-107` — "- **D7 in full generality is not open-and-attackable; it is LRC.** The finite-`p` / version remains genuinely open and is the one worth pursuing."

### `P163_ARGUMENT_v1.md` **(in partly superseded file)**

- `:69-70` — "Greedy with two odd speeds forced does fail to complete (leftover 2–4 targets / across several starts), which is suggestive but is not a proof — greedy is not exact." (line 71 completes: "exact.")
- `:89-91` — "- **The `p = 163` search is not replaced.** What has changed is that the question / is now correctly posed — a parity-constrained covering problem — rather than / the covering problem the earlier documents were attacking."
- `:96-98` — "> Why can 7 speeds cover `{1,…,652}` when all are multiples of 8, but not when / two are odd?"
- `:103-104` — "**That asymmetry, not size, is where the / obstruction lives**, and it is the first thing to examine."

### `CLAIM_GRADES_v1.md`

- `:18` — ""Don't re-attack" is advice, not a finding; the finite-`p` version is a different statement and is open."
- `:23` — "With #4 corrected, the covering routes are not shut."

### `COLLAPSE_Z163_v1.md` **(in superseded file)** — identical text at the same line numbers in `COLLAPSE_Z163_v2.md`

- `:133-134` — "Scope: this closes one sector of the `p = 163` verification (`x = 5`), not the / verification. Sectors `x = 0,…,4` are untouched by it."
- `:149` — "Open, in decreasing tractability:"
- `:151-154` — "1. **Sectors `x = 4,3,2,1,0`.** Same machinery, `m = 7−x` non-coarse speeds and / threshold `U_min(x)`. `x = 4` is running. The enumeration grows as `C(567,m)`, / so `x ≤ 2` will need the §2 pair-type structure as a pruning rule rather than / as a filter after the fact."
- `:155-160` — "2. **Whether `f(n,p) = n−1` for all large `p`.** Observed `f(8,163) = 7 = n−1`; … **The relation `f(n,p) ≤ n−3 ⟹ Lemma 7 / fails at (n−1,p)` is a proved one-way implication; the converse is false.**"

### `COLLAPSE_Z163_v2.md`

- `:133-134`, `:149`, `:151-154`, `:155-160` — as listed immediately above, verbatim identical.

### `SEARCH_REDUCTION_v1.md` **(in superseded file)**

- `:66-69` — "Whether `p = 163` completes in a useful time is / **not yet known** — it is running; larger `p` grows both the target count and the / speed count, and the branch factor with them. Nothing here claims the 32-hour / search has been replaced."
- `:34-36` — "*Caveat on scope.* The step "some speed is coprime to `N`" uses `n` a prime power. / For `n` with two distinct prime factors the group still acts, but the normalisation / needs a different representative; do not transcribe it to general `n` unchecked."

### `SEARCH_REDUCTION_v2.md` **(in superseded file)**

- `:63` — "there and the `x = 4` result, the sectors still open at `p = 163` are `x ∈ {1,2,3}`."
- `:80` — "The 32-hour search is **not** replaced."
- `:54-55` — "*Scope*: the step "some speed is coprime to `N`" needs `n` a / prime power — do not transcribe to general `n` unchecked."

### `SEARCH_REDUCTION_v3.md` **(in superseded file)**

- `:72` — "there and the `x = 4` result, the sectors still open at `p = 163` are `x ∈ {1,2,3}`."
- `:89` — "The 32-hour search is **not** replaced."
- `:63-64` — "*Scope*: the step "some speed is coprime to `N`" needs `n` a / prime power — do not transcribe to general `n` unchecked."

### `SEARCH_REDUCTION_v4.md` **(in superseded file)**

- `:73` — "there and the `x = 4` result, the sectors still open at `p = 163` are `x ∈ {1,2,3}`."
- `:78-81` — "It does not: §7 also makes statements about `k = 4` and `k = 5`, which were / not tested. What was tested is `k = 3, 6, 7`. `k = 5` cannot be tested with the / normalised search at all — `n = 6 = 2·3` is not a prime power, so the argument in / §2 for "some speed is coprime to `N`" does not apply."
- `:89` — "| 5 | not tested — `n = 6` is not a prime power | "larger than 23" |"
- `:106` — "The 32-hour search is **not** replaced."

### `SEARCH_REDUCTION_v5.md`

- `:77` — "there and the `x = 4` result, the sectors still open at `p = 163` are `x ∈ {1,2,3}`."
- `:82-85` — "It does not: §7 also makes statements about `k = 4` and `k = 5`, which were / not tested. What was tested is `k = 3, 6, 7`. `k = 5` cannot be tested with the / normalised search at all — `n = 6 = 2·3` is not a prime power, so the argument in / §2 for "some speed is coprime to `N`" does not apply."
- `:93` — "| 5 | not tested — `n = 6` is not a prime power | "larger than 23" |"
- `:68-69` — "*Scope*: the step "some speed is coprime to `N`" needs `n` a / prime power — do not transcribe to general `n` unchecked."
- `:110` — "The 32-hour search is **not** replaced."

### `PHI_N_GRANULARITY_v1.md`

- `:86-87` — "derived expectation about transferability, not a claim that the transfer fails — / the n=11 machinery has not been run against the four-level population."
- `:97` — "- §3 last paragraph: **DERIVED** expectation. Untested."
- `:103-106` — "Whether the granularity law constrains a bad cover enough to close the remaining sectors — / or, in the general-`n` framework, whether it bears on Conjecture 5.2-H at `n = 8` — / is open."

### `EXACTNESS_AUDIT_v1.md`

- `:79-80` — "`float_audit_v1.py` is the check; it is mechanical and should be re-run before any / result is written up."

### `EXACT_PHI_N_AP_v1.md`

- `:50` — "## 3. An open item the exact run surfaced — not dismissed"
- `:65-66` — "**So the AP family is not the only extremal family, and the characterisation of the / rigid class is open.**"
- `:67-70` — "Scope: `n ∈ {4,…,8}`, first 400 non-AP tuples from `{1,…,4n−1}` in lexicographic / order — a biased sample by the project's own diverse-sampling rule, so the two are / existence witnesses and the counts are not a rate."

### `RIGID_CLASS_v1.md` **(in superseded file)**

- `:7-8` — "Sufficiency is **open** / and its test is pre-registered, not run."
- `:78-80` — "Whether (C1) ∧ (C2) is sufficient is **open**; a tuple could in principle carry a short / lonely interval containing no rational of denominator below `n`, which is precisely the / case neither lemma touches."
- `:84-86` — "Ten hand-chosen tuples are a consistency check, not evidence of a / rate; the sweep that would bear on sufficiency is pre-registered separately and has not / been run."

### `RIGID_CLASS_v2.md`

- `:6` — "Run and results: `RIGID_SWEEP_RESULTS_v1.md`." *(no file of that name found anywhere in the `Math Ex` tree)*
- `:83-84` — "**Sufficiency is false**, and not marginally — see `RIGID_SWEEP_RESULTS_v1.md`. The four / conditions are arithmetic (residues and divisibility); what defeats them is a *covering* / failure with no evident arithmetic signature."

### `PREREG_RIGID_CLASS_v1.md`

- `:8` — "`T` is **RIGID** iff …" — the whole file is a specification of a test that has not been reported run inside `docs/n8/`.
- `:149` — "| Any arm not run | **ABSTAIN on that arm, in the grade slot.** Abstention is **not** a closure of the rigid-class question and is not evidence either way. Record the arm as owed, with the reason. |"
- `:150` — "| `K=0` everywhere | Explicitly **not** licence to write "C1 & C2 characterise RIGID". `K=0` on a bounded frame is a bound with a stated power, not a theorem, and the necessity cells are forced (§1) so they add nothing. Still open after a clean run: a rigid tuple with `max(T) > 4n`, or at `n > 12`. |"
- `:111` — "- Exhaustive arms (`n<=8`): power **1** against any counterexample with `max(T) <= 4n`; **zero** power outside it."
- `:113-115` — "**95%** at `eps >= 1.50e-4`, **99%** at / `2.30e-4`, **50%** at `3.47e-5`. Below `eps ~ 1e-5` they have essentially no power; that sentence must / accompany every sampled-arm null."
- `:120-122` — "No claim extends to / `max(T) > 4n`, `n > 12`, multisets, non-integer or negative speeds, or bounds other than `1/n`."

### `CAP_TABLE_UNIFORM_v1.md`

- `:84-87` — "**Does not change.** The sector *decisions* (`x = 5`, `x = 4`) rest on `U_min(x)` and on exact / dilate-coverability, and both remain `p`-specific. This file supplies no bound on `U_min`, and / it decides no cell. `n = 8` is not proved analytically; the count of decided cells is unchanged / at **2 of 135**."

### `P_UNIFORMITY_v1.md`

- `:44` — "**`maxD(p) = ⌊(p+3)/6⌋`.**  `[EMPIRICAL, 27/27]`  No proof. Partial mechanism from"
- `:47-48` — "What is not derived is / how the two speeds' `q`-values co-vary as `r` runs over the classes."
- `:35` — "Verified `27/27` primes — a check of the arithmetic, not evidence for the law."
- `:80` — "measured set is now all 27. Still EMPIRICAL — `f(8,p) ≥ 6` is not proved for any `p`."
- `:84` — "**Decided cells: 2 of 135, unchanged.** Nothing here decides a sector."
- `:87-88` — "The open sectors at `p = 163` remain / `x ∈ {1,2,3}`, and 26 primes remain untouched."

### `F_LOWER_BOUND_v1.md` **(in superseded file)**

- `:48-49` — "only exceptions are `11, 17, 19`. Scope: `n = 8`, this arc, primes to 300. Not a theorem / for any `p ≥ 29`."
- `:83` — "`f(8,p) ≥ 6` is **not proved for any `p ≥ 29`**. Decided cells: **2 of 135, unchanged.**"
- `:85-86` — "noted `f(8,p) ≥ 6` was unproved; that grade stands, with the range now extended and the / statement now known to be **false below 23**."

### `F_LOWER_BOUND_v2.md`

- `:48-49` — "only exceptions are `11, 17, 19` — and the range `[301,700]` (63 primes) is clean. Scope: `n = 8`, this arc, primes to 700. Not a theorem / for any `p ≥ 29`."
- `:83` — "`f(8,p) ≥ 6` is **not proved for any `p ≥ 29`**. Decided cells: **2 of 135, unchanged.**"
- `:85-86` — "noted `f(8,p) ≥ 6` was unproved; that grade stands, with the range now extended and the / statement now known to be **false below 23**."
- `:78-79` — "The `p = 11` and `p = 17` counterexamples are exactly the perfect partitions of / `Z/p ∖ {0}` into such APs, which is where a proof must place its lower bound on `p`."

### `TOP_GAP_v1.md`

- `:55-56` — "So the proved constant `7` is loose by a factor `2.1` on this / frame; the true constant for `n = 8` is at most `10/3` and at least `10/3` / on the frame. `[EMPIRICAL, scope: six-subsets of [1,24]]`"
- `:73-74` — "**Decided cells: 2 of 135, unchanged.** This decides no cell and does not prove `n = 8`."
- `:76` — "Whether `v₇ ≤ 7v₆` prunes the `x = 3` sector enumeration usefully is **untested**."
- `:41-43` — "The argument is / elementary and may well be known in the literature; what is new here is only that its input / for `n = 8` is a machine-verified `LRC(7)`."

### `PLAN_ANALYTIC_v1.md`

- `:47-49` — "**Gate, before anything is graded above CITED: `citation-verifier` on Theorem 2.** / `ROSENFELD_REVIEW_v1` §6 already flags this and it has not been run. It is mandatory under / `CLAUDE.md` §2 and it is the single largest unexamined dependency."
- `:39` — "`[CITED, peer-reviewed, proof not read]`. **Load-bearing for the entire argument.**"
- `:84-85` — "Falsified by exhibiting LR-property / tuples with `ω → 0` and `M ~ 4p`, which is the thing to measure first and has not been."
- `:91-92` — "Progress = / cells decided. **Ceiling: 5 of 135.** Does not generalise by itself, and must not be sold as / if it did."
- `:118-121` — "2. **Measure `ω` on LR-property tuples** — the number that decides whether R1 is alive. If / `ω` is bounded below by a positive constant, R1 is the proof; if it decays with `M`, R1 / is dead and says so cleanly. This has never been measured and is the highest-information / single computation available."
- `:124` — "Pre-registration (`experiment-designer`) is required before step 2, per `CLAUDE.md` §2."
- `:128-129` — "Decided cells **2 of 135**. `n = 8` is not proved analytically. Nothing in today's session / changed the cell count, and this plan does not either."

### `N11_TRANSLATION_v1.md`

- `:9-10` — "**Not yet read:** `eleven_lonely_runners_v33.md` and `lrc_n11_algebraic_lemma_v1.md` / themselves."
- `:83` — "| Coupling Principle (bad intervals move together under the free parameter) | **not translated.** … The n=8 analogue is unidentified. **This is the gap.** |"
- `:84` — "| Baton-Pass Certificate (explicit `t*`) | **not translated.** Needs the coupling analogue first. |"
- `:96-98` — "The ladder is therefore a genuine constraint but / not a decisive one on its own, and the next object is what the free speeds must do — which / is the same shape as the sector decomposition (`x = #{v : 8 ∣ v}`) reached from the / Rosenfeld side, and the two should be checked against each other before either is pushed."
- `:102` — "Nothing here decides a cell or proves `n = 8`."

---

## 5. RETRACTIONS AND SELF-CORRECTIONS

Every retraction, correction or "this was wrong" statement in `docs/n8/`, quoted with file
and line.

### R1 — Two claims of an automated summariser corrected. `ROSENFELD_REVIEW_v1.md:6-16`

> "## 0. Two corrections to the automated summary that fetched it" (line 6)
>
> "A first pass used a summarizer, and two of its claims are **wrong**. Recorded so
> neither propagates:" (lines 8-9)
>
> "- It said the speeds must be "pairwise coprime". They need not be. The only
> normalisation is `gcd(v₁,…,v_k) = 1`, and that is WLOG (divide through)." (lines 11-12)
>
> "- It attributed the minimal-counterexample bound to **Cusick (1973)**. It is
> **Malikiosis–Santos–Schymura**, cited as [13, Theorem A]" (lines 13-14)

### R2 — A convention delta in Rosenfeld's transcription of Theorem 2. `THEOREM2_CITATION_VERIFIED_v1.md:41-60`

> "## 3. The one delta — an off-by-one in the *label*, not the theorem" (line 41)
>
> "Rosenfeld transcribed that sentence verbatim into a paper whose own convention is
> `k` = **speeds**. Read literally in his convention, his Theorem 2 asserts a
> hypothesis *strictly stronger* than MSS need, and its phrase "then it holds for
> `k+1`" does not match its own conclusion object (a `k`-tuple)." (lines 47-50)
>
> "**It would affect us** if we transcribe his Theorem 2 verbatim. This project has
> already been bitten twice by convention slips (the §6.6(b) ratio-2 partner; the
> `v33` introduction's `1/(n+1)`)." (lines 58-60)

### R3 — Direction 2 of the block chain retracted before being attempted. `D7_ATTACK_v3.md:92-117`

> "2. ~~**Count the blocks, not the points.**~~ **RETRACTED — see below.**" (line 92)
>
> "### Retraction of direction 2" (line 94)
>
> "I proposed counting blocks against divisibility-selected sub-tuples, on the
> grounds that for `k+1` composite the `d_t` differ and "the demands may genuinely
> compete". **They do not.**" (lines 96-98)
>
> "**So the entire `j = tp` chain collapses to one requirement — some `v` divisible
> by `k+1` — which is Lemma 4 at `j = k+1` and nothing further.** Direction 2 is
> closed before being attempted, and the composite-`k+1` framing was wrong." (lines 115-117)

The retracted text is preserved verbatim in `D7_ATTACK_v2.md:92-101`.

### R4 — A corollary drawn from the block recursion is false. `D7_ATTACK_v4.md:66-69`

> "`j = p+1` is covered by `v = 5`, and `6 ∤ 5`. The exclusive zone is empty at
> `s = 1`. Consequently the recursion has no base to iterate on, and the corollary
> I had drawn from it — "`T` contains a speed divisible by `k+1` **and** less than
> `p`" — is **false**: here the only `6`-divisible speed is `54 > 19 = p`."

### R5 — "Covering is not the obstruction" reversed. `COLLAPSE_Z163_v1.md:139-142` (identical at `COLLAPSE_Z163_v2.md:139-142`)

> "The framing in `P163_ARGUMENT_v1` §1 — "covering is not the obstruction, the gcd
> condition is" — needs a correction, and it is this document's main revision to
> the record. **Covering is the obstruction; the gcd condition selects which
> covering problem you must solve.**"

Restated as a grade correction at `CLAIM_GRADES_v1.md:19`:

> "| 4 | "**Covering is NOT the obstruction** — the gcd condition is." | overclaim; **now corrected** | Inferred from two witnesses (`k=6,p=31`; `k=7,p=163`). `COLLAPSE_Z163_v1` §4 supersedes it: `f(8,163) = 7` exactly, i.e. the cheapest cover uses all `k` speeds. **Covering is the obstruction; the gcd condition selects which covering problem must be solved.** |"

And at `CLAIM_GRADES_v1.md:28-29`:

> "Item 4 is the one that cost something — it redirected the line away
> from covering for the rest of the session, and it was wrong."

### R6 — An arithmetic slip in the `|D|` histogram. `COLLAPSE_Z163_v2.md:3`

> "**v2 corrects one number in §5**: v1 reported the `|D|` distribution as "concentrated at `|D| ≤ 7` (48 699 pairs)". That figure is an addition slip and matches no cumulative of the histogram — the correct value is **51 184** (46 739 at `≤5`, 49 920 at `≤6`), out of 52 326. Caught by an independent re-run of `x5_two_odd_v1.py`, not by re-reading. Every other figure in this document reproduced exactly."

### R7 — The claim that later needed retracting, preserved. `SEARCH_REDUCTION_v2.md:31-34`

> "This is the same tuple recorded in
> `WHY_13_AND_19_v2.md` as "the `k = 7` obstruction"; **the sense there was
> inverted** — the grid at `p = 41` misses the lonely windows, which is why 41 is an
> exception, not why it works."

### R8 — R7 retracted: the accusation against our own file was false. `SEARCH_REDUCTION_v3.md:15-21` (verbatim identical at `SEARCH_REDUCTION_v4.md:16-22` and `SEARCH_REDUCTION_v5.md:17-23`)

> "**Retraction of a claim made in `SEARCH_REDUCTION_v2.md` §1.** That version said
> the `k = 7` exception at 41 had been recorded "with the sense inverted" in
> `WHY_13_AND_19_v2.md`. **That is false.** §3 of that document states the exception
> correctly and derives it: it lists the four lonely windows of
> `T₇ = {1,4,12,13,14,16,20}`, tabulates which primes' grids hit them, marks `p = 41`
> as the sole miss, and quotes Rosenfeld's sentence verbatim. It was right. The
> check that settles it is reading §3, which v2 did not do before writing."

### R9 — A prime-list error in our own script, and what was *not* wrong. `SEARCH_REDUCTION_v3.md:23-31` (same at v4:24-32, v5:25-33)

> "What *was* wrong is narrower: `run_k7_primes_v1.py`, written earlier today,
> enumerated all 28 primes in `[31,163]`." (lines 23-24)
>
> "The script is corrected and now asserts `len(PRIMES) == 27`.
> `ROSENFELD_REVIEW_v1.md` said "27 primes" and elided the list; it was not wrong." (lines 30-31)

### R10 — Validation scope overstated. `SEARCH_REDUCTION_v4.md:77-81` (same at `SEARCH_REDUCTION_v5.md:81-85`)

> "**Scope correction.** v3 said this reproduces "every data point Rosenfeld states in
> §7". It does not: §7 also makes statements about `k = 4` and `k = 5`, which were
> not tested. What was tested is `k = 3, 6, 7`. `k = 5` cannot be tested with the
> normalised search at all — `n = 6 = 2·3` is not a prime power, so the argument in
> §2 for "some speed is coprime to `N`" does not apply."

### R11 — A `k = 4` discrepancy resolved as never having been a contradiction. `SEARCH_REDUCTION_v4.md:91-99` (same at `SEARCH_REDUCTION_v5.md:95-103`)

> "**The `k = 4` item is resolved, and it was never a contradiction.**
> `lemma7_criterion_v1.py`'s docstring recorded an unresolved discrepancy: our
> search finds `p = 13` works for `k = 4`, while §7 says "larger than 17" and Table 1
> starts `S` at 17. The paper's sentence is upward-closed — it claims every prime
> above 17 works and says nothing about 13 — so 13 working is a sharper threshold,
> not a conflict."

### R12 — A floating-point breach in a reported claim. `EXACTNESS_AUDIT_v1.md:7-8, 14-29`

> "**Result: 9 float-capable sites, one genuine breach. It was mine, it was in a
> reported claim, and it is now replaced by an exact certificate.**" (lines 7-8)
>
> "`SEARCH_REDUCTION_v3/v4` §1 and `HANDOVER_2026_09_07b` §4 state that the bad cover
> `T = {1,4,12,13,14,16,20}` at `p = 41` "has the LR property as real speeds
> (`max_t min_i ‖t v_i‖ = 0.14284 > 1/8`)". That number came from an inline scan over
> `t = a/200000` in IEEE-754 doubles. It was never saved as a script, so it had no
> artifact either." (lines 14-18)
>
> "The float 0.14284 was approximating `1/7 = 0.142857…`. **The claim survives, and now
> has a certificate**" (lines 27-28)

The repair is carried into `SEARCH_REDUCTION_v5.md:3-6` (its supersession sentence) and
`SEARCH_REDUCTION_v5.md:42-45`.

### R13 — A float site flagged by grep and cleared by reading. `EXACTNESS_AUDIT_v1.md:46`

> "| `window_width_v1.py` | 18, 20, 29 | `F(m-1)/v`, `e/v`, `(a+c)/2` | **not floats** — every operand is a `Fraction`, so these are exact rational divisions. Flagged by grep, cleared by reading. |"

### R14 — The published φ(n) paper's "n = 8 anomaly" dissolved. `EXACT_PHI_N_AP_v1.md:22-25`

> "**§6, the "n = 8 computational anomaly".** At `n = 8` the lonely set is exactly
> `{1/8, 3/8, 5/8, 7/8}` — `φ(8) = 4` points — and `min_j ‖j t‖ = 1/8` exactly at each.
> No tolerance appears anywhere in that sentence. The anomaly was an artefact of float
> inputs and does not exist in exact arithmetic."

### R15 — A reading note in the published paper superseded. `EXACT_PHI_N_AP_v1.md:74-80`

> "Not refuted — **re-verified, and at a stricter standard than it claimed.** Every result
> of Theorem 3.1 and §6 that was checked here holds exactly. The reading note in
> `lrc_ap_phi_n_law_v1.md` that excused the float basis ("the tolerance framework here is
> the object of study rather than a contaminated measurement") is superseded: the
> Boundary Set Method makes the exact computation available, so the tolerance framework
> was never necessary for the verification, only for the fragility discussion it
> illustrates."

### R16 — A dropped hypothesis in our own Corollary A. `RIGID_CLASS_v2.md:41-50`

> "**What v1 got wrong.** v1's Corollary A read "all `φ(n)` points isolated ⟺ (C1)", dropping
> Lemma A's standing hypothesis `n ∤ v`. `(C1)` does not imply `(C0)`: `T` may carry the
> units *and* an element `≡ 0 (mod n)`. The sweep located this mechanically" (lines 41-43)
>
> "The ten named
> probes in v1 spanned `n ∈ {5,8,9,12}` but contained no tuple that satisfies `(C1)` *and*
> carries a multiple of `n`, so they could not have exposed it." (lines 48-50)

### R17 — Joint sufficiency of (C1) ∧ (C2) reported false. `RIGID_CLASS_v2.md:83-84`

> "**Sufficiency is false**, and not marginally — see `RIGID_SWEEP_RESULTS_v1.md`. The four
> conditions are arithmetic (residues and divisibility); what defeats them is a *covering*
> failure with no evident arithmetic signature."

*(Recorded as stated. The named results file is not present in the tree — see §1.6.)*

### R18 — A previously targeted uniform bound found false. `F_LOWER_BOUND_v1.md:1-3` and `F_LOWER_BOUND_v2.md:1-3`

> "# `f(8,p) ≥ 6` is FALSE as stated — three counterexamples, and what survives" (v1:1)
>
> "2026-09-07. Task: prove `f(8,p) ≥ 6` uniformly. It does not hold uniformly. Three odd
> primes admit a 5-dilate cover, and one of them admits a 4-dilate cover." (v1:3-4, v2:3-4)
>
> "**a correct proof must use a lower bound on
> `p`.** Any argument that is purely algebraic in `w₁,…,w₅` and blind to the size of `p`
> would prove the false statement, so it is wrong." (v1:52-54, v2:52-54)

### R19 — A one-way implication's converse recorded as false. `COLLAPSE_Z163_v1.md:157-160` and `COLLAPSE_Z163_v2.md:157-160`

> "That is one hit, not a law —
> `f(7,23) = f(7,29) = 5`, and Lemma 7 fails at 23 and 29 too, so the coarse
> sector does not explain those failures. **The relation `f(n,p) ≤ n−3 ⟹ Lemma 7
> fails at (n−1,p)` is a proved one-way implication; the converse is false.**"

### R20 — The stated analytic goal corrected: it is the problem, not a reduction. `D7_ATTACK_v5.md:62-71`

> "## 4. Consequence: D7 in full generality is not a shortcut" (line 62)
>
> "So the
> target named in `ROSENFELD_REVIEW_v1.md` §4 as "the well-posed analytic goal" is
> well-posed but **not a reduction**: it is the problem itself, restated." (lines 65-67)
>
> "That explains, retrospectively and uniformly, why all six routes failed. They were
> not near-misses; each was an attempt on something of the same strength as the
> goal." (lines 69-71)

### R21 — Three process errors in the session that produced most of these files. `PLAN_ANALYTIC_v1.md:7-23`

> "## 0. Process correction" (line 7)
>
> "Today's session produced four results — a `p`-uniform cap table, a top-gap theorem, a
> refutation of `f(8,p) ≥ 6`, and a `U_min(2)` closed form — **without a plan**, each chosen
> because it was the next cheap thing." (lines 9-11)
>
> "- **The top-gap Lemma 2 is not a new idea; it is the corpus's own named target.**
> `WHY_13_AND_19_v2.md` §6 already states it … Today's Lemma 2 is a first instance of exactly that,
> and it was framed as something else because §6 had not been read." (lines 13-17)
>
> "- **A background job was reported "still running" five times on a check that could not tell
> running from hung.** The parent had 2.3 s of CPU in 59 minutes and zero workers. That is
> a proxy-for-object error, the failure mode this project's own agent rules name." (lines 21-23)

### R22 — A disclosed-discrepancy clause written in advance. `PREREG_RIGID_CLASS_v1.md:81-83`

> "**Pass criterion: `RIGID=False` with an interval containing `1/2`.** The owner
> states five components; the run prints the count, and a count other than 5 is a *disclosed
> discrepancy against the owner's figure* — not silently absorbed, and not a pipeline failure."

And the pre-committed retraction rule at `PREREG_RIGID_CLASS_v1.md:146`:

> "| `M1 >= 1` or `M2 >= 1` | A §1 necessity proof is wrong. Report the RIGID tuple, quote the step it breaks, retract the condition. Do not repair the condition and re-test on the same data. |"

### R23 — A pre-emptive guard against merging two numerically equal ratios. `N11_TRANSLATION_v1.md:42-44`

> "*(Numerical aside, not a claim of identity: `1.75` is also the covering slack
> `f(8,163)/⌈163/41⌉ = 7/4`. The two ratios are `(n−1)/φ(n)` and `2(n−1)/n`, which coincide
> at `n = 8` only because `φ(8) = 8/2`. Different quantities; do not merge them.)*"

### R24 — A grade correction folded back into a later measurement. `P_UNIFORMITY_v1.md:79-80`

> "`CLAIM_GRADES_v1` item 6 graded that EMPIRICAL and scoped to "the primes measured"; the
> measured set is now all 27. Still EMPIRICAL — `f(8,p) ≥ 6` is not proved for any `p`."

---

## Coverage — files opened

**Opened and read in full, with line numbers, all 32 `.md` files in `docs/n8/`:**

`CAP_TABLE_UNIFORM_v1.md`, `CLAIM_GRADES_v1.md`, `COLLAPSE_Z163_v1.md`,
`COLLAPSE_Z163_v2.md`, `D7_ATTACK_v1.md`, `D7_ATTACK_v2.md`, `D7_ATTACK_v3.md`,
`D7_ATTACK_v4.md`, `D7_ATTACK_v5.md`, `EXACTNESS_AUDIT_v1.md`, `EXACT_PHI_N_AP_v1.md`,
`F_LOWER_BOUND_v1.md`, `F_LOWER_BOUND_v2.md`, `N11_TRANSLATION_v1.md`,
`P163_ARGUMENT_v1.md`, `PHI_N_GRANULARITY_v1.md`, `PLAN_ANALYTIC_v1.md`,
`PREREG_RIGID_CLASS_v1.md`, `P_UNIFORMITY_v1.md`, `RIGID_CLASS_v1.md`,
`RIGID_CLASS_v2.md`, `ROSENFELD_REVIEW_v1.md`, `SEARCH_REDUCTION_v1.md`,
`SEARCH_REDUCTION_v2.md`, `SEARCH_REDUCTION_v3.md`, `SEARCH_REDUCTION_v4.md`,
`SEARCH_REDUCTION_v5.md`, `THEOREM2_CITATION_VERIFIED_v1.md`, `TOP_GAP_v1.md`,
`WHY_13_AND_19_v1.md`, `WHY_13_AND_19_v2.md`, `source_integrity.md`.

**Head only (not read in full) — files outside `docs/n8/`, opened solely to source the
§3 sentences that `CLAIM_GRADES_v1.md` attributes to "the session summary":**

- `docs/HANDOVER_2026_09_07.md` — lines 1-54 grepped, lines 55-127 read in full. Rows 1, 2, 3, 8 of §3 quote from it.
- `docs/HANDOVER_2026_09_07b.md` — grepped only; one line (`:15`) quoted, in §3 row 7. **Not read in full.**

**Opened and returned nothing:** `find` for `RIGID_SWEEP_RESULTS_v1.md` over the whole
`Math Ex` tree — no match. Referenced twice by `RIGID_CLASS_v2.md` (lines 6 and 83).

**Not opened:** the `experiments/n8/*.py` scripts named throughout, and the four PDF
sources listed in `source_integrity.md`. This index records what the `.md` files say about
them, not what they contain.
