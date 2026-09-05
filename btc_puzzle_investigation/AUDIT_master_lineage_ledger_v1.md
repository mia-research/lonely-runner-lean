# AUDIT — Results-vs-Conclusion Ledger (PILOT v1)

**Scope of this pilot:** the `POSITIVE_FINDINGS_MASTER` lineage, endpoints **v1 (2026‑07‑17, 253 L) → v9 (2026‑08‑11, 1349 L)**, plus an object-level grade audit of v9. secp/BTC investigation only.

**Purpose:** validate the audit *format* on one lineage before scaling to the rest of the corpus. Not exhaustive.

**Method:** two isolated agents, each given the raw files + criteria only — **no session narrative, no thesis to confirm.** One traced v1→v9 (loss/drift/inflation); one graded v9's claims against the project's own closure-grade rubric. Both were told a clean result is a valid result (so as not to manufacture findings).

**Method limits (size the full sweep against these):**
1. **Endpoints only.** A frontier *born in an intermediate version and killed before v9* is invisible to a v1↔v9 comparison. The full sweep must do consecutive hops.
2. **One lineage.** This is the working *ledger* document. The *summary/compendium* documents (`PROJECT_SUMMARY_*`, `BRIDGE_PROGRAMME_COMPENDIUM_*`) are the tie-it-in-a-bow-by-function documents and were **not** audited here.
3. **v9 object pass samples** the drift-prone tags (all CONTINUUM / BANNER / "no discriminator" / the lone OPEN + ~8 random PROVED), not all ~100 claims.

---

## Pilot meta-findings (read before the tables)

**MF1 — On this lineage, drift is CORRECTIVE, not inflationary.** The narrative-inflation failure mode was real and concentrated in **v1** (= the over-closed master the degradation audit was written against). The v2→v9 restoration work has been actively *undoing* it: grades down, caveats added, three closures reopened. This is a genuine, evidence-backed result — **not** a bow. It says the *master ledger* self-corrected; it says nothing about the summary layer or the intermediate hops.

**MF2 — "1 `[OPEN]` tag" was a proxy, and it fooled the first read (mine).** v9 carries ~10 open items (A.3 ledger N1–N10) + multiple live frontiers (§XI.x), under brackets like "OPEN — not resolved", `[GAP]`, `[UNREPRODUCED]`, not the literal `[OPEN]`. A tag count reports "1 open"; the object trace reports "≥10 open". Trace the object, not the tag — demonstrated on ourselves.

**MF3 — Cross-version cleanliness ≠ within-document cleanliness.** v9 is conservative relative to v1 *and* still carries three standing overclaims + one three-way internal contradiction (§ Artifact 1B). Both true at once.

**MF4 — The buried-live-result pattern is real and specific.** The two standing unexplained anomalies (N1, N7) are each the *next-order correction* of an object whose *leading order* was written up as closed. The closure and the open thread are the same object, filed apart (§ Artifact 3).

---

## Artifact 1 — Claim ledger

### 1A. Cross-version drift, v1 → v9 (material rows only; 47 of 56 rows were SURVIVED-INTACT with no material delta and are omitted)

| Object | v1 (scoped truth, verbatim/line) | v9 conclusion (verbatim/line) | Delta | Direction |
|---|---|---|---|---|
| Amicable transfer | "φ:E(F_p)→F_n **is the DLP** (transfers no advantage)" (L102) | "only the group-homomorphism case is ruled out … non-homomorphic correspondence π_n=π_p−1 is **UNANALYZED — a live frontier**" (L439–441) | closure → reopened frontier | **corrective** |
| Concentration ⟺ ECDLP | "'no concentration' **⟺ ECDLP hard** (Boneh–Shparlinski)" (L155) | "**WITHDRAWN**: ⟸ trivial, ⟹ unproved — no reduction in hand" → `[GAP]` (L498–499) | equivalence → `[GAP]` | **corrective** |
| "Sole residual" synthesis | "Security = the DLP = cheap spectral concentration, **the sole residual** … not an open haze" (L207) | "it does **not** say the DLP is the sole residual … **The frontiers below are live**" (L755–756) | closure → reversed | **corrective** |
| χ₂ bound source | "`[PROVED\|KS]` … **KS covers χ₂**" (L150–153) | "⚠ Does **NOT** cover χ₂ — KS's Ψ is additive, χ₂ multiplicative" → re-graded `[PROVED\|WD]` w/ named artifact (L490–495) | mis-citation withdrawn, re-sourced | **corrective** |
| First-fall degree | "CURVE-INDEPENDENT `[PROVED, general m]` ⇒ no CM/GLV lever" (L180) | "`[HEURISTIC + CITED]` … the implication re-graded" (L621–625) | grade DOWN | **corrective** |
| a_ℓ supersingular rule | "`a_ℓ=0 ⟺ ℓ≡2 mod 3`" asserted as theorem (L91) | "`[CITED — Hasse/Weil]` … **for good reduction only (ℓ∤42)**" (L427–428) | scope caveat added | **corrective** |
| Δ(t) discriminant | "`Δ(t)=−86704128·(t³+7)⁴`" `[PROVED]` (L179) | "`[UNREPRODUCED]` … constant/exponent do not reproduce … not relied on downstream" (L617–620) | grade DOWN | **corrective** |
| Leakage COMPUTATIONAL | "leakage is COMPUTATIONAL … info about d **fully present & bounded-recoverable** 0.37/0.93" (L138–142) | "`[VERIFIED — with the M14 caveat]` … scalar-fidelity control **does not separate** the leaking character from a random target" (L480–486) | major caveat added | **corrective** |
| `p−1`,`n−1` factorizations | "`p−1=2·3·7·13441·C`; `n−1=2⁶·3·149·631·…`" (L30) | absent | **DROPPED** (definitional, not a frontier) | loss (non-load-bearing) |
| 8 embedded sub-facts | see note ▼ | absent | **DROPPED** (definitional sub-clauses) | loss (non-load-bearing) |

▼ Sub-facts dropped between v1 and v9, core claim surviving each: `n_t` factorization; curve-identity `[n]P=(n+k)Q+(n·D)G` + greedy-unit-fraction `D_terms` + dataset cols `a_glv,b_glv,sextant,chi6X/Y`; "orbit-sextant ~98% same parity"; "degree 2^{m−2} per var"; "u=−1 unique unit N(π+u)=n"; explicit formal-group law `F(T₁,T₂)` + `Σ b^k C(3k,k)` family; "Frobenius sieve ℓ|n_t ⟺ eigenvalue −1"; `C_T` numerics `36:6:1`,`{1,⅓,1/9}`,`0.5687≈0.5625`; the `xy`=`(X·Y)mod m ↔ D_terms` "single-key D-shadow" link. **None is an open frontier, retraction, or graded finding.** (The `xy`/D-shadow drop is the one worth a second look — it silently severed a stated `(x,y)↔D` connection; flagged in the register below.)

**Cross-version tallies:** SURVIVED-INTACT 55/56 · WEAKENED-by-dropped-hedge **0** · GRADE-INFLATED **0** · SCOPE-WIDENED **0** · DROPPED 1 row + 8 sub-facts (all definitional). Liquidated frontiers: **none** (all 7 of v1's open panels survive as open, rows 49–55 of the trace).

### 1B. Within-document standing overclaims in v9 (object-level grade audit)

Most sampled tags came back **TAG-JUSTIFIED** (all CONTINUUM items, the `[OPEN]`, the NO-DISCRIMINATOR / NOT-PROVED / UNREVIEWED / BANNER items, 7 of 9 sampled plain `[PROVED]`). The load-bearing exceptions:

| # | Claim (v9 line) | Tag as written | Rubric verdict | The delta |
|---|---|---|---|---|
| O1 | **P13**: "Hom(E,A_new)=0 **at secp** … **Secp-valid, not a small-p artifact**" (L257) | `[PROVED]` | **SCOPE-MISMATCH** | secp instantiation *inherits N2* (A_new supersingular at secp — unproved at dim 2, L296). Tag should read `[PROVED\|N2]`; as written it reads decisive. Document flags the dependency inline but the tag does not encode it. |
| O2 | **L480 heading**: "**Leakage is COMPUTATIONAL, not information-theoretic**" | `[VERIFIED — w/ M14 caveat]` | **OVERCLAIM (unscoped closure)** | The heading closes the information-theoretic avenue in general; the power/scope in the body apply to *one* readout (F̂). Directly contradicts the document's own withdrawn implication (VI‑3 / retraction #9). Exactly the "'must be computational' erased the ensemble channel" pattern the project memory flags. |
| O3 | **Census identity** `e₂=e₁²−χ₂(−1)p` | `[VERIFIED]` (M21) **and** OPEN (N8) **and** `[PROVED — modulo (D2)]` (XVI, L1289) | **INTERNAL CONTRADICTION** | Same object graded three ways in one document. "(D2)" is **never defined** in the master (the only internal "D2" is an apparently-unrelated Lang-torsor bridge). The XVI proof self-flags `[PROVED — UNREVIEWED]`, verified at **2 primes (p=43,67)**. A reader cannot tell what the proof is conditional on. |

---

## Artifact 2 — Hanging-results register (preserved, NOT resolved)

| # | Hanging result (v9 line) | Why it doesn't sit right |
|---|---|---|
| H1 | **N1 — ½-saturation** (L295, 602–607): χ₂(y) reaches 0.470 ≈ ½ of 4√p while same-dim additive readout reaches 0.876; "two distinct real structures; the ½ mechanism is unidentified. Twice attempted, twice not closed." | A same-dim/same-ceiling matched control gives 1.86×. The one measured anomaly in the set with no account. |
| H2 | **N7 — sub-Rayleigh deficit** (L301): the DLP character's harmonics run 0.06–0.10% smaller, pooled **Z = −13.99**, survives the exact matched null; "mechanism unexplained"; two candidate mechanisms refuted *without* refuting the effect. | A ≫8σ one-directional effect with no mechanism. Live residue, not noise. |
| H3 | **"(D2)" undefined** (L5, L1289) — the census proof's modulus is named but never defined in the master. | A headline grade rests on an undefined conditional. |
| H4 | **M10 vs P11/P12** (L275 vs L134/L363): "¾−½=¼ = flap fraction, **exact at tested p**" (M10) vs "flap density ¼ is **continuum-only**, discretization error →0" (P11/P12). | Same ¼ asserted both exact-at-p and continuum-only. The ½-on-core is genuinely exact (integer sums); the ¾-on-lift is the continuum piece — the row conflates them. |
| H5 | **Corr(a₀)=√(πn)/2 under `[PROVED]`** (L519–520). | The π factor marks a Rayleigh *expected value*, bundled with two genuine exact identities under one PROVED tag. |
| H6 | **`xy`↔D-shadow link dropped** (v1 L168 → gone in v9). | v1 stated `(X·Y)mod m ↔ D_terms`; v9 keeps the `xy` object as "#1 OPEN lead" but drops the stated connection to the key residual D. Severed, not refuted. |
| H7 | **M6 open pattern** (L271): supersingular ord(α²/p) CM {1,3} vs non-CM {3,4}, "sample too small to call a law — recorded as open." | Correctly held; noted so a successor does not promote it. |
| H8 | **XV.2 bullet 3 outdated** (L1170 vs L1296): speculates "if N8 proves j=0-specific…" but XVI.A.2 already found the census rigidity is a ζ₄-automorphism invariant, **not** j=0-specific. | Speculation's premise is already disconfirmed elsewhere in the same document. |

---

## Artifact 3 — Intersections map (open ↔ closed, same object)

Each pair: an anomaly held OPEN sits on the *same object* as something graded PROVED/closed. These are the candidate levers — the buried-result recoveries.

| # | Open item | Closed/proved neighbor (same object) | The lever |
|---|---|---|---|
| X1 | **N8** — "why does e₂=e₁²−χ₂(−1)p hold? mechanism unidentified" (L302, 855) | **XVI.A.1 c₂-branch proof** — "proved-modulo-D2 via Stickelberger Jacobi sign law" (L1285–1291) | The c₂ proof is a candidate *answer to* (or contradiction of) N8. Document half-notices in XV.1 (L1143). Not connected in the ledger. |
| X2 | **N2** — "A_new supersingular at secp not proved for dim 2" (L296) | **P13** `[PROVED]` (inherits N2) + **N10/M23** degree-40 field tower `G⊆A₄₀` (L304, 1148) | XV.1 asks: does pinning monodromy over Q(ω) constrain Newton slopes {½,½} vs {0,1} *without* the dim-2 extrapolation? The open tower is the candidate lever to close the gap under the PROVED P13. |
| X3 | **N1** — ½-saturation, "only 2 of 4 eigenvalues carry weight-1 mass" (L295) | **M22/P16** — proved W⊕W⊗ξ (ξ=ζ₃) 2+2 twist-splitting of the same 4-dim Frobenius (L287, 260) | The *proved* 2+2 eigenvalue split is the natural account of the *open* 2-of-4 weight anomaly. §XI.10 names the bridge (D2 / Lang-torsor twist). |
| X4 | **N7** — sub-Rayleigh deficit (L301, 850) | **Σ\|U\|²=p²(n−1)** — the exact conservation that *closed* the concentration hope (M14, L530) | The identity that closed the *leading-order* lead is the same object whose *next-order* correction is the open deficit. N7 itself names the row-budget shadow as its candidate mechanism. |
| X5 | **R1 / prime-field Semaev** — reopened frontier §XI.4 (L785) | **N4 cover family** — bounded vs known index-calculus, `[EMPIRICAL/CITED]` (L298) | The one live lever (prime-field-native Semaev) is the explicitly-named residual R1 of the otherwise-bounded cover object. |

---

## Recommendation for the full sweep

The pilot says the audit *format* works (it caught 3 real standing overclaims, 1 internal contradiction, 8 hanging results, and 5 intersections — while correctly reporting the cross-version drift clean). Two adjustments before scaling:

1. **Re-point at the bow-tie-by-function documents.** The *master ledger* self-corrected. The narrative-to-decisive pressure the investigation is worried about most likely lives in `PROJECT_SUMMARY_secp256k1_v1/v2` and `BRIDGE_PROGRAMME_COMPENDIUM_v1/v2` — documents whose job is to summarize, not to ledger. Audit those next, and audit them *against v9* (does the summary preserve v9's caveats, or re-close what v9 reopened?).
2. **Hops, not endpoints.** Run the consecutive-version trace (v1→v2→…→v9) to catch born-and-killed intermediate frontiers, which endpoint comparison cannot see.

**What the full sweep should NOT do:** re-close H1–H8 or X1–X5 into a tidy verdict. They are the asset. The correct next move on each is a named next-probe, not a grade.
