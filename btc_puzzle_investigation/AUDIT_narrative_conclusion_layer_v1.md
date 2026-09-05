# AUDIT — Narrative-Conclusion Layer, Phase 1 (v1)

**Real audit, phase 1.** Target = the *summary* documents future sessions bootstrap from, measured against the fullest graded results. Follows the pilot (`AUDIT_master_lineage_ledger_v1.md`).

**Documents:**
- Under audit (the narrative conclusion): `PROJECT_SUMMARY_secp256k1_v1.md` (2026‑07‑28) and `_v2.md` (2026‑08‑06)
- Source of truth (fullest graded results): `POSITIVE_FINDINGS_MASTER_v9.md` (2026‑08‑11)

**Method:** two isolated agents (no session narrative, no thesis), one per axis. Operating rule enforced: a clean section is checked for *dropped questions against the source*, never against nothing — "tidy is suspect" as a source-check, not a license to manufacture.

**⚠ Load-bearing temporal frame — read before any row below.** The summary (Aug 6) was consolidated from **master v4**. The source-of-truth is **v9** (Aug 11) — *later and fuller*. So a gap between them is one of three different things, and **they must not be collapsed into one verdict**:
- the summary states something **firmer than the current results** (propagation risk),
- the summary is **blind to a layer the results added after Aug 6** (omission risk),
- the summary is **more conservative than the current results** (reverse — results firmer than their own summary).

The dominant distortion in this layer is **staleness + omission, not active inflation.** That is a different mechanism than "nulls inflated to closures," and it needs a different fix. But staleness that firms is still firming *from the reader's chair* — a session reading the Aug‑6 summary today cannot tell it is five master-versions behind. So the STALE items below are live findings, not explained-away ones.

`S:` = `PROJECT_SUMMARY_secp256k1_v2.md`; `M:` = `POSITIVE_FINDINGS_MASTER_v9.md`.

---

## AXIS A — Summary self-drift (v1 → v2): clean, verified-conservative

Byte-diff: the two summary versions are identical except **7 hunks**, all in the P13 / N2 / A1.1 "`A_new` supersingular at secp" cluster, and every hunk moves *conservative*: "Now UNCONDITIONAL" → "NOT unconditional", grade pulled to `[PROVED — conditional; 2 caveats]`, open item N2 **re-opened** and only conditionally re-closed on a named artifact. **Zero firmed, zero re-closed, zero caveats dropped, zero grade-inflated.**

This is a **faithful-clean**, not a suppressed-clean: the cleanliness is proven by a mechanical byte-diff, and the one change is a *downgrade*. Passes "tidy is suspect" legitimately. The narrative conclusion did **not** firm across its own versions.

*(Cosmetic: the v2 file's title line still reads "(v1, 2026‑07‑28)" — a label slip, not a content delta.)*

---

## AXIS B — Summary (v2) fidelity vs current results (v9)

The summary is a **largely faithful** carry (the majority of the Proved ledger P1–P15, the Measured rows M1–M20 incl. the M14 non‑separation caveat verbatim, the full Part F retraction ledger 1–46, Part G scoped nulls, Part H bridge with its caveat stack — all FAITHFUL). The gaps concentrate, and split into three ledgers:

### B1 — FIRMER THAN CURRENT RESULTS  *(the propagation risk — what a reader takes as more-settled than it is)*

| # | Summary says (S line) | Current results say (M line) | Class | Note |
|---|---|---|---|---|
| B1‑a | 120° law is an **EXACT identity**, `[PROVED — exact]`; "upgraded from `[VERIFIED]` to exact" (S:107, S:308) | "the 120° law is `[VERIFIED]`, **not `[PROVED-exact]`** … `min_l g_l ≥ g_true`, one-sided … real inflation witness" (M:28–30, M:286) | **STALE** | master **v8** downgraded it; summary prints the superseded firmer grade |
| B1‑b | "## B.5 … the ½ saturation **RESOLVED** to relative rigidity" (S:296); "the `2√p` cap … **accounts for** ½=2/4" (S:312) | N1: "the one measured anomaly in the set **with no account**. Twice attempted, twice not closed; **no explanation is offered**." (M:295); the Lang‑torsor bridge (D2) is listed as an **unrun next probe** (M:824) | **RE‑CLOSED / over‑stated** | the section *title* says resolved; the summary's **own** A.3 ledger says "**Open on uniformity** (frontier #26)" (S:156). Title contradicts its own body — internal narrative over‑statement, independent of staleness |
| B1‑c | `A_new` supersingular **incl. secp**, proved scale‑free via Cartier ⇒ "valid at 2²⁵⁶" (S:98, S:197) | N2: "verified 24/24 at small p, **not proved for dimension 2** … Extrapolation to 2²⁵⁶ is an **assumption**" (M:296) | **FIRMED / divergent** | genuine divergence, not mere staleness — see Hanging H‑1 |

### B2 — INVISIBLE TO THE SUMMARY  *(the omission risk — live results a summary-only reader never learns exist)*

Every item added to the results in v7–v9, absent from the Aug‑6 summary. Staleness *explains* the omission; it does not *cure* it — a session bootstrapping from the summary today learns none of these:

1. **N8** — census identity `e₂=e₁²−χ₂(−1)p` mechanism **unidentified** (M:302, §XI.16)
2. **N9** — the explicit `W`-piece of `H¹≅W⊕W⊗ζ₃` **unidentified** (M:303)
3. **N10** — degree‑20 non‑abelian tower `L/Q(ω)`, exact Galois group **unpinned** (M:304)
4. **M21 / P16** — the 1171/1171 census-uniformity law + twist-factorization reduction (M:286, M:260)
5. **M22** — twist character constant `ξ(Frob_p)=ζ₃`, 1560/1560 (M:287)
6. **M23** — splitting-field layer, `[L:Q]=40`, `G⊆A₄₀`, non‑abelian ⇒ commutative‑CM ruled out at field level (M:288)
7. **M24 / Part XIV** — the universal phase channel, `k=3`, **NOT CM** (M:289, M:1090)
8. **§XI.19** — cross-curve firing control: census rigidity universal via ζ₄ (**not j=0‑specific**), while the attack channel (GLV+carry) **IS CM‑gated** (M:9, M:1294)
9. **Owed citation** — Katz, Kummer/hypergeometric sheaves `[CITED — TO VERIFY]`, "run citation-verifier before any grade moves up" (M:1264)
10. **★ Part XVI.D — PRIORITY OPEN FRONTIER**: the Eisenstein-lift-norm route, a candidate **public route to ε** ("a positive lights up the whole arsenal … UNTESTED", M:1332) — the current linchpin lead, entirely absent
11. **Part XVI.B / .C** — the conditional d‑shadow arsenal (all gated on a public `c`/`ε`) and its properly-scoped circularity negative (M:1305, M:1320)

**This is the sharpest propagation finding in Phase 1:** the investigation's *current priority lead* (a candidate public route to ε) is invisible to the document a new session would read first.

### B3 — REVERSE: RESULTS FIRMER THAN THEIR OWN SUMMARY  *(surfaced, not buried — these are findings too)*

| # | Summary (S) | Results (M) | Note |
|---|---|---|---|
| B3‑a | P13 demoted to `[PROVED — conditional on Cartier; 2 caveats]` (S:95) | P13 = **`[PROVED]`**, "Secp‑valid, not a small‑p artifact", N2 only inline (M:257) | the **results doc carries the harder, less-hedged tag**; the summary is more honest here |
| B3‑b | Route 3 / cover bound = older "`Õ(p^{4/3})` … **not a family bound**" (S:159) | master v5 upgraded to "**the FAMILY, not one cover** … no genus‑g cover beats Pollard by KNOWN index calculus" (M:298, M:582) | summary is *less* decisive than current results |

---

## HANGING RESULTS (from this pass — preserved, NOT resolved)

**H‑1 — Is `A_new` supersingular at secp actually proved? The two current documents disagree.** This is load-bearing (P13 = `Hom(E,A_new)=0` at secp is one of the closed "doors"). State of play:
- Summary v2: **proved** scale-free via a Cartier-operator derivation (S:197), tag `[PROVED — reviewed replacement; 2 caveats]`.
- Master v9: **open** — "not proved for dimension 2 … an assumption" (N2, M:296); v9 never folded the Cartier work in and still tags P13 `[PROVED]` resting on that inline assumption.
- The Cartier derivation (`RESULT_anew_supersingularity_step3_gap_and_cartier_route_v2.md`, on disk) carries **2 citation caveats + 2 owed citations (Xing / Maisner–Nart) + a verdict-neutral sign-flip owed at `anew_cartier_audit_v2.sage:190`.**
→ Either v9 is stale-on-this-point (the Cartier work closes N2 and v9 didn't update), or the Cartier work is not yet complete (owed sign-flip + citations). **The project owes itself a reconciliation:** proved, or open? A "door" rests on the answer.

**H‑2 — N1 graded three ways *inside the summary itself*.** Title "RESOLVED" (S:296) vs body "structural" candidate account (S:146) vs own ledger "Open on uniformity" (S:156). The heading is the narrative conclusion a skimmer reads; it is the firmest of the three and the least supported.

---

## PHASE‑1 SYNTHESIS  *(kept explicitly un-collapsed — do not reduce to one sentence)*

Three separate statements, all true at once; a future reference must keep them apart:

1. **On its own drift, the summary is conservative** (Axis A, byte-verified). It is not firming itself over time.
2. **Against current results, the summary's distortion is dominantly staleness + omission, with one genuine internal over-statement.** Three items read firmer than v9 (two because v9 walked them back *after* the summary was written — B1‑a, B1‑c; one, N1 "RESOLVED", is an internal title-vs-ledger over-claim independent of staleness — B1‑b). Ten-plus current results, including the **priority lead**, are invisible to it (B2).
3. **On two items the results are firmer than their summary** (B3) — the reverse of the feared direction.

**The mechanism this phase actually implicates** is not "nulls inflated to closures." It is that **the summary has no way to signal it is behind the results.** A reader cannot tell the Aug‑6 conclusion is five master-versions stale. That is a structural gap in how the layer is maintained, and it fixes differently (sync / staleness banner / single source of truth) than an inflation problem would.

---

## RECOMMENDATION

- **Do not "correct" the summary into tidiness.** The hanging results H‑1 and H‑2 and the reverse-direction B3 items are the asset; each wants a named next step, not a grade.
- **Surface the concrete owed items** (do not silently fix): (i) the summary is stale vs v9 and omits the priority lead — it needs a v3 synced to v9, or a staleness banner naming its base version; (ii) H‑1 — the `A_new`-at-secp proved-or-open contradiction needs a decision, since P13 depends on it.
- **Next phase = the memory layer** (`btc_puzzle_INDEX.md` + the `feedback_*`/topic pointers). It is the highest-propagation narrative conclusion of all — read at the *start* of every session — and the pilot + this phase both point to the same risk: the most-read conclusion is the one most likely to be stale or firmer-than-source.
