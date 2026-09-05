# RECOVERED RESULTS — the un-folded addendum layer (v1)

**Purpose.** A reachable top-level home for the results that were dropped at the un-run addendum→master reconcile (audit 2026‑08‑15). These live only in `POSITIVE_FINDINGS_ADDENDUM_1/2/3_v1.md`; `POSITIVE_FINDINGS_MASTER_v9` references them 0 / 1 (a loss-admission) / 0 times. This document is the **reconcile done as an additive ledger** — it does *not* mutate the master.

**Status of the completeness certificate (the #1 correction).** `PROJECT_SUMMARY_secp256k1_v2` Part A (L74) certifies v9 as *"reconciled across master + both addenda."* **That certificate is inaccurate.** The accurate statement: *the addenda were never reconciled into the master; their un-folded items are consolidated here.* Until the summary/master carry this correction in-file, `btc_puzzle_INDEX.md` (session‑start read) and this document hold it.

**Provenance & how to trust this.** Items were transcribed from the addenda via the 2026‑08‑15 audit's isolated agents (verbatim + line). **Grades are INHERITED from the source, not re-derived here.** Every row cites its source `file:line` — verify against it before promoting any item into the master. This is documentary consolidation (transcription fidelity), not an evidentiary re-audit of any lead. Cross-refs: `LIVE_LEADS_MAP_v1.md` (navigation), `AUDIT_narrative_conclusion_layer_v2.md` (how they were lost).

---

## PART 1 — FROM `ADDENDUM_1_v1` (referenced 0× in v9)

### 1A. The d‑side `(n,k,D)` / Dirichlet lattice thread — absent from *every* top‑level document

| Item | Statement (as sourced) | Grade | Source | Owed |
|---|---|---|---|---|
| A1.5 | Dirichlet reciprocal‑floor lattice; island boundary at √lo | structural | ADD1 A1.5 | re‑entry; then the curve‑side image (Frontier 19) |
| A2.8 | Farey solid / 1‑D coprimality net; its ℤ/2 symmetry; non‑genericity vs matched control | VERIFIED‑scope | ADD1 A2.8 | per‑n density null (Frontier 24) |
| A2.9 | three‑level complexity filtration; sub‑generic fragmentation | structural | ADD1 A2.9 | re‑entry |
| A1.4 | Aut(E) orbit bit‑ladder, constant ceiling log₂6; interval‑folding negation‑vs‑λ; "√k double‑count" runtime caveat | structural | ADD1 A1.4 | re‑entry |
| Frontier 22 | T=2 stratum; whether T=3 opens past fiber width 10⁷ (`max T=2` verified only to 7·10⁵) | OPEN | ADD1 L1102‑1104 | extend fiber‑width sweep |
| Frontier 24 | per‑n coprimality‑net density null; "which cycles carry the ~3× β₁ excess" | OPEN | ADD1 L1108‑1111 | the density null + cycle ID |
| Frontier 19 | curve‑side image of the T=1 Dirichlet island lattice; **the d‑side↔curve‑side question across the amicable bridge (§A1.2)** | OPEN | ADD1 L1092‑1095 | the bridge probe (links Thread 1↔2) |
| (pilot H6) | `(X·Y) mod m ↔ D_terms` "single‑key D‑shadow" — the stated (x,y)↔D link | dropped v1→v9 | v1 L168 → gone | severed, not refuted — is it real? |

### 1B. Full‑scale‑at‑secp scoped nulls & the LBE battery

| Item | Statement | Grade | Source | Owed |
|---|---|---|---|---|
| A3.1 | the LBE battery (30×25) + method finding: "χ² Holm alone would have produced a false positive here; **report the empirical rank**" | EMPIRICAL — battery | ADD1 A3.1 | re‑entry (a live method note) |
| A3.2‑A3.6 | full‑scale nulls: island joint‑set; island GLV cross‑set; flap‑ε under the group law (2⁻⁶–2⁻⁹ power ladder); flap density 130‑vs‑256; no d‑free selector | EMPIRICAL — scoped, secp‑scale | ADD1 A3.2‑A3.6 | these are the only secp‑*scale* nulls; v9's Appendix A carries only p≤6397 |
| A1.6 | gauge‑free covariant‑weight form `W_cov` (machinery) | tool | ADD1 A1.6 | supports the λ₃ reframe (see 1D) |
| Frontier 20 | μ₆‑matched feature/target pairs at n>5·10⁴ ("needs its own pre‑registration") | OPEN — live | ADD1 L1096‑1098 | prereg + run |
| Frontier 21 | diffuse family‑wise LBE dependence — **ABSTAINED, not closed** ("more null draws, not re‑analysis") | ABSTAINED | ADD1 L1099‑1101 | more null draws *(abstention IS the finding — do not read as closed)* |
| Frontier 25 | the ≥3‑key / amicable **joint‑SET** object (untouched) | OPEN | ADD1 L1112‑1113 | *(the ε‑carry half of F25 reappears as v9 Part XVI.D; this half is absent)* |

### 1C. N1 sharpening (v9 reverted it to the blunt v4 form)

- **ADD1 §XI.10 (L1047‑1052):** N1 "STILL OPEN, now sharper" — parity‑as‑cause **refuted at 10 primes**; the **bulk‑moment class of statistics disqualified a priori**; anomaly **localized to the extremal tail**; candidate mechanism = the **[−1]‑involution 2+2 parity split**, with a live counterexample (`bx` → 0.909, not ½). v9 (§XI.10 L820‑825) reverted to "no account … no explanation is offered." **Owed:** re‑enter the sharpening, then run D2.

### 1D. Dropped retractions from ADD1 — dead claims left un‑protected  *(re‑enter to re‑protect)*

| # | What it retracts (so it is not re‑used) | Source |
|---|---|---|
| 28 | "m=1 ⇒ eigenvalues √p·{±ζ₁₂,±ζ₁₂⁵}" → FALSE (m=1 gives primitive 3rd/6th roots) | ADD1 L980‑988 |
| 29 | "34/34 configurations confirm the Jacobi reduction" → corrected to **15 distinct** | ADD1 L989‑991 |
| **30 ★** | "λ₃ eigenvector 60→85% μ₃‑covariant, broadband" → **retracted twice** (gauge artifact + no covariant excess) | ADD1 L992‑999 |
| 32 | "transfer map public ⇒ any inversion is an ECDLP solver" → invalid (proves too much; would 'refute' MOV) | ADD1 L1007‑1011 |
| 35 | "4th moment settles starvation vs spreading" → wrong (statistic blind; class disqualified) | ADD1 L1024‑1027 |
| 36 | "D‑term T=1 clustering is 2‑adic" → refuted by matched control (it's the Dirichlet reciprocal lattice) | ADD1 L1028‑1030 |
| 37 | "6000‑sample flap‑density gap 130‑vs‑256" → noise | ADD1 L1031‑1032 |
| 38 | "sub‑Rayleigh mechanism = 4th‑moment excess on Δ=0 quadruples" → **REFUTED by its own pre‑committed threshold** | ADD1 L1033‑1036 |

> **★ H‑3 (contradiction):** retraction 30 says λ₃ is a *dead gauge artifact*; **v9 L1194 re‑asserts it** as "λ₃ up to 85% (real, broadband — OPEN, not resolved)." Resolve before either doc is trusted on λ₃.

---

## PART 2 — FROM `ADDENDUM_2_v1` (referenced 1× — a loss admission)

### 2A. Forced/exact structure on the `V(a)` object (Thread 1) — dropped

| Item | Statement | Grade | Source | Owed |
|---|---|---|---|---|
| B1.7 | Arm II dissolves to the **exact frame identity ⟨f_a,f_b⟩ = nI − J**; Parseval Σ|V(a)|²=n(n−1); **3‑pt multiplicative bispectrum ≡ 0** | PROVED — forced, exact | ADD2 L159‑171 | exact constraints the random‑target nulls fail — a decidable discriminator; re‑enter |
| B1.3 | **S_y ≤ 2 ⇔ sign of one L‑poly coefficient** (a sub‑Weil bound); |V₁(a)| ≤ √3·√p (obs max 1.932√p @ p=547) | PROVED — algebra | ADD2 L96/L106‑107 | prove the sign target ∀a≠0 |
| B1.4 | the v≤0 route to S_y≤2 is FALSE by exact counterexample — **but the inequality is NOT refuted** (v≤0 was sufficient, not necessary) | PROVED — exact | ADD2 L112/L123 | re‑enter as live caveat (don't retry v≤0) |
| B1.6 | the ℓ≥5 ideal‑level CM route **collapses to a rational symbol of U=|t−1|** (forced algebra, not a null) | PROVED — forced | ADD2 L147/L154 | re‑enter |
| B1.2 | v = u²−3/4 exactly; the two Frobenius half‑angles differ by exactly 120°; **max_a v ≤ 1/4 UNCONDITIONAL** | PROVED — exact | ADD2 L86‑91 | v9 kept only the paired `V₂=V₁²` form; the generating mechanism + the unconditional residue bound are owed |
| B3.1 | E[u⁴] consistent with full SU(2), **excludes the 3/8 (torus/CM) reduction** | EMPIRICAL — scoped OOS, controls fired | ADD2 L265 | larger p; higher moments |
| B3.2 | μ₃‑invariance is CM‑specific (C‑JZERO) — twist‑orbit null is structure beyond class‑machinery | VERIFIED | ADD2 L281 | — |

### 2B. The `½=2/4` account, the layer, and the citation debt

| Item | Statement | Grade | Source | Owed |
|---|---|---|---|---|
| B2.3 | the `A_new` channel: absolute rigidity destroyed, **relative rigidity survives**; the 2√p cap is its arithmetic value; **accounts for ½ = 2/4** (4 free eigenvalues, χ₂(y) has 2 × {1,ζ₃}) | structural (framing exact) | ADD2 L221‑237 | v9 reverted N1 to "no account"; this is the delivered account, owed re‑entry as the D2 probe target |
| B3.3 | a char−MN−μ₆ layer **EXISTS** (Arm A pooled Z=+70.50); z‑scale **over‑dispersed ≈1.55× reproducibly**; §XI.17 still OPEN | EMPIRICAL — seen‑data, control‑repaired | ADD2 L287‑298 | v9 kept only the "row‑budget candidate"; the "layer exists" finding + the instrument caveat owed |
| B2.1 | the Stickelberger (D2) citation VERIFIED (Katre) → `[CITED — verified]`; **three load‑bearing caveats travel with it** | CITED — verified, 3 caveats | ADD2 L177‑186 | **H‑2:** v9 M:1289 holds (D2) an owed "debt"; a `[PROVED — modulo D2]` law rests on which is right |
| B2.2 | the a≠0 twisted eigenvalues are NON‑ABELIAN ⇒ the ζ₃ is GEOMETRIC; L‑Stick retired, L‑mono now primary | VERIFIED (p=43,67) | ADD2 L197‑216 | survived (v9 M23/N9/N10, reframed SL₂‑monodromy) |

### 2C. The DLP‑touching object‑class, and the recovered POSITIVE

| Item | Statement | Grade | Source | Owed |
|---|---|---|---|---|
| **B3.4 ★★** | **E3 cubic difference‑set on the real 82 keys: a PRE‑REGISTERED REJECT** — E3(real)=13125 at the **98.4th percentile, p≈0.033**, "not a null‑estimation artifact," interpretation **OPEN** | EMPIRICAL — pre‑registered reject, NOT MC‑corrected | ADD2 L300‑318 | **the one item asking for a MEASUREMENT** — MC‑correction across the prereg family, reproduction (exact), matched Farey/fundamental‑domain null, OOS. **Surface, not re‑assert, not re‑deflate.** v9 buried it to a stale "at the floor" null |
| Frontier 29 | **group‑law joint difference‑set objects**: P_i±P_j via curve addition, χ₃(x_j−x_k), triple/multilinear — the object‑class that **touches the DLP** (each its own prereg) | OPEN — live frontier | ADD2 L453 | re‑enter as a frontier (v9 reverted it to a stale null); B3.4 lives on this class |
| B4.3 | S_diff on the real 82 keys: real ≡ known‑MT, NO REJECT (p=0.59) — **caveat:** the μ₃‑graded χ₃(x_j−x_k) "probes exactly this blind subspace" | MEASURED — scoped null, n=82 | ADD2 L360‑371 | the null + its blind‑subspace caveat both owed |
| B4.1/B4.2 | twist‑orbit single‑character & magnitude nulls, scoped OOS (signed‑low prime ≠ magnitude‑low prime) | EMPIRICAL — scoped OOS | ADD2 L329‑350 | next‑probes (2‑pt/autocorr, multiplicativity) |

### 2D. Dropped ADD2 retractions & other drops

- **Retractions 39‑45** (ADD2 L379‑413) not carried: 39 (two A_new mechanism sketches WRONG), 40 (ω‑descent withdrawn), 41 (**"v>0 generic" WRONG — the ~5% is a suppressed rate**), 42 (E3 "unliftable ceiling / says nothing about the curve" RETRACTED), 44 ("9 of 12 OOS" for G(χ₄) sign RETRACTED), 45 (amicable "unremarked" narrowed). *(43 — `e₃=χ₂(−1)p·e₁` correction — DID survive.)*
- **B2.4** (ADD2 L248‑259) dropped: Silverman–Stange arXiv:0912.1831 as the correct p↔#E citation; Cap‑Law steps 1+3 classical‑input regrade; "Lemma C not located" caveat; amicable narrowing (Pasta `y²=x³+5`).
- **Frontier 27** (S_y sub‑Weil, ADD2 L446) & **Frontier 30** (higher‑order/larger‑p twist‑orbit, ADD2 L458) dropped.

---

## PART 3 — FROM `ADDENDUM_3_v1` (referenced 0×) — the whole session's work, none folded

| Item | Statement | Grade | Source | Owed |
|---|---|---|---|---|
| A | the 1‑D "intertwined Fourier proxy" `W_N` extraction route: **LOCKED (analytical), closed 3 ways** — plus a **standing caution:** "the pullback couples a and b, so the full (a,b) diagonal orbit is a **forced zero**; keep the geometry's μ₃ index and the scalar phase on separate axes" | VERIFIED — decidable artifact | ADD3 L11‑24 | re‑enter; the caution prevents a future symmetry‑mismatched false positive |
| B | deficit characterization 1: μ₃/GLV frequency‑support (magnitude) — **scoped null**, near‑zeros NOT μ₃‑clustered in b to sub‑percent power | EMPIRICAL — scoped null, well‑powered | ADD3 L26‑36 | narrows N7 — owed re‑entry into the deficit frontier |
| C | deficit characterization 2: μ₃ phase‑within‑triple — **scoped null** (+ a caught null‑miscalibration); **NOT closed:** higher‑order phase invariants, the imaginary‑part isotype, c‑column‑specific phase | EMPIRICAL — scoped null | ADD3 L38‑58 | narrows N7 — owed re‑entry |
| Net | the deficit's organization is **NOT** in the μ₃‑graded b‑frequency channel; **next probes:** higher‑order phase invariants; c‑axis / c=±b diagonal; p‑scaling const‑vs‑1/log‑p | frontier update | ADD3 L60‑64 | fold into N7/§XI.15 (which currently lists different candidates) |
| method | **for the master's Anomaly‑Drill layer:** a must‑fire control can MISS a variance‑miscalibration when it doesn't share the signal's correlation structure; the diagnostic is **effect‑size scaling with N** (a pooled Z flat as N grows is a variance artifact) | binding method note | ADD3 L66‑71 | fold into the Anomaly‑Drill rule |

---

## CONTRADICTIONS TO RESOLVE BEFORE FOLDING ANY OF THIS INTO THE MASTER

| # | Contradiction | Where |
|---|---|---|
| H‑1 | `A_new` supersingular at secp: **proved‑via‑Cartier** (summary) vs **open dim‑2 assumption** (v9 N2). Cartier route owes a sign‑flip (`anew_cartier_audit_v2.sage:190`) + 2 citations. | summary vs v9; door P13 rests on it |
| H‑2 | Stickelberger **(D2)** citation: **discharged w/ 3 Katre caveats** (ADD2 B2.1) vs **owed debt** (v9 M:1289); "(D2)" undefined in the master. | ADD2 vs v9 |
| H‑3 | **λ₃**: dead gauge artifact (ADD1 ret. 30, two scripts) vs "real, broadband, OPEN" (v9 L1194). | ADD1 vs v9 |
| H‑4 | **census identity** graded `[VERIFIED]` (M21) / OPEN (N8) / `[PROVED — modulo D2]` (XVI) in one document. | within v9 |

---

## HOW TO PROMOTE (when moving an item from here into the master)

1. Open the cited `source:line`; confirm the statement and grade transcribed faithfully (this doc is a pointer, not the primary).
2. Keep the source grade unless a fresh artifact justifies a change — do **not** firm on transcription.
3. For a recovered **positive** (E3), the promotion path is a **test** (MC/OOS/matched null), not a re‑assertion.
4. For a recovered **retraction/caveat**, re‑insert it to re‑protect the dead claim.
5. Resolve the relevant H‑contradiction first if the item touches it.
