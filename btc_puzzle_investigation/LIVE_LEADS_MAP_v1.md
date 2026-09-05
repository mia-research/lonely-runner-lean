# secp256k1 — What Is Still Live: a map of open leads, hanging results, and intersections (v1)

**What this is.** The usable output of the results-vs-conclusion audit (2026‑08‑15). It pulls every *live* result the audit surfaced — including a large body that is **reachable from no current top-level document** because the addendum layer was never reconciled into the master — into one map, organized by mathematical object so the intersections are visible. A hanging result in one thread is often the missing lever for another; that is what this map is for.

**How to read it.**
- **Grade** is the item's *current, honest* grade (PROVED / VERIFIED‑scope / EMPIRICAL / CITED / HEURISTIC / OPEN / ABSTAINED). Not re‑graded up; not deflated.
- **Lives in** names where the item actually is. Items marked **ADD1/2/3‑only** exist *nowhere* in `POSITIVE_FINDINGS_MASTER_v9`, the summary, or the compendium — a session reading those would never learn they exist.
- **Owed** is the concrete next step (a test, a proof, a reconcile) — never a verdict.
- This map does not close anything. Per the project stance, no empirical null and no single fact closes an avenue; these are levers, stated as levers.

**Provenance / caveats.** Grades are inherited from the source documents and were not independently re‑derived here. Several float‑era numbers remain PROVISIONAL under the exact‑arithmetic rule. The audit ledgers are `AUDIT_master_lineage_ledger_v1.md` (pilot), `AUDIT_narrative_conclusion_layer_v1.md` (Phase 1), `AUDIT_narrative_conclusion_layer_v2.md` (Phase 2).

---

## THREAD 1 — The `A_new` spectral object (`V(a)` / the 4‑dim Frobenius). The densest cluster.

Every item below lives on the *same* object: the new part `A_new` of the genus‑3 cover, its Frobenius eigenvalues, and the character sums `V(a)` built from it. This is where "open anomaly" and "proved structure" sit closest — the richest intersection field in the investigation.

| Item | Grade | Lives in | Owed / next probe |
|---|---|---|---|
| **N1 — ½‑saturation** (χ₂(y) reaches ½·4√p; "2 of 4 eigenvalues carry weight‑1 mass") | OPEN | v9 (blunt); **ADD1/2‑only** (sharp) | the sharp form (parity refuted at 10 primes, bulk‑moment class disqualified, localized to the extremal tail, candidate [−1]‑involution 2+2 split) + the `½=2/4` rigidity‑budget account are owed re‑entry; then run D2 (Lang‑torsor twist bridge) |
| **N7 — sub‑Rayleigh deficit** (DLP character's harmonics run Z=−13.99 smaller) | OPEN | v9; narrowing **ADD3‑only** | ADD3 already excluded the μ₃ b‑frequency channel and the μ₃ real‑part phase isotype — owed re‑entry; next probes: higher‑order phase invariants, c‑axis / c=±b diagonal, p‑scaling const‑vs‑1/log‑p |
| **N8 — census identity mechanism** (why `e₂=e₁²−χ₂(−1)p`?) | OPEN | v9 | reconcile against the c₂‑branch "proof" (see intersection ★1) |
| **N9 — explicit W‑piece** of `H¹≅W⊕W⊗ζ₃` | OPEN | v9 | identify W as an abelian subvariety/motive |
| **N10 — degree‑40 non‑abelian tower** `L/Q(ω)`, `G⊆A₄₀` | OPEN | v9 | pin the exact Galois group (needs Magma; beyond PARI/KASH) |
| **120° law** `α₂/α₁=ζ₃` at cells | **VERIFIED, not PROVED‑exact** (one‑sided `min_l g_l≥g_true`) | v9 | *(watchlist: the summary firmed this to `[PROVED — exact]` — see Overclaims)* |
| **Twist‑orbit forced landscape**: Arm II = exact frame identity `⟨f_a,f_b⟩=nI−J`; Parseval `Σ|V(a)|²=n(n−1)`; 3‑pt multiplicative bispectrum ≡ 0 | PROVED — forced/exact | **ADD2‑only** | owed re‑entry; these are exact constraints the random‑target nulls do *not* satisfy — a decidable discriminator |
| **Sub‑Weil reduction**: `S_y≤2` ⇔ sign of one L‑poly coefficient; `|V₁(a)|≤√3·√p` (obs max 1.932√p @ p=547) | PROVED — algebra | **ADD2‑only** | prove the sign target for all a≠0 (the open inequality reduces to it) |
| **v≤0 route** to `S_y≤2`: FALSE by exact counterexample — but inequality NOT refuted (v≤0 was sufficient, not necessary) | PROVED — exact | **ADD2‑only** | owed re‑entry as a live caveat (don't re‑try the v≤0 route) |
| **`E[u⁴]~SU(2)`** excludes the 3/8 torus/CM reduction | EMPIRICAL — scoped OOS, controls fired | **ADD2‑only** | larger p; higher moments |
| **N2 / `A_new` supersingular at secp** (foundation of P13 door) | **CONTRADICTED** — see H‑1 | v9 (OPEN) vs summary (PROVED‑via‑Cartier) | resolve H‑1 (below) |
| **M21 / P16 / M22 / M23** — the proved/verified census + twist + splitting‑field structure | PROVED / VERIFIED‑scope | v9 | (the proved neighbors that the open items above intersect) |

**Intersections inside Thread 1 (open ↔ proved on the same object — candidate levers):**
- **★1  N8 (open) ↔ c₂‑branch law `[PROVED — modulo (D2)]`** (Part XVI.A.1). The proof may *answer* N8 — or contradict it. Not connected in any ledger. Blocked on H‑2 (is D2 discharged?).
- **★2  N1 (open) ↔ M22/P16 2+2 eigenvalue twist‑split (proved).** The proved 2+2 split is the natural account of the open "2‑of‑4 weight" anomaly. Bridge = D2.
- **★3  N7 (open) ↔ `Σ|U|²` budget conservation (proved).** The exact identity that *closed* the leading‑order concentration hope is the same object whose next‑order correction is the open deficit.
- **★4  N2 (open) ↔ N10 tower (open) ↔ P13 (PROVED, inherits N2).** Pinning the monodromy over Q(ω) may constrain the Newton slopes {½,½} vs {0,1} and settle N2 *without* the dim‑2 extrapolation — closing the gap under a "door."
- **★5  Twist‑orbit forced landscape + sub‑Weil reduction (ADD2, proved) sit on the very `V(a)` whose N1/N7 anomalies are open.** Recovering them gives exact constraints to test the anomalies against — currently unused because they're addendum‑only.

---

## THREAD 2 — The d‑side `(n,k,D)` / Dirichlet lattice.  ★ Invisible to every top‑level document (ADD1‑only). ★

This entire thread was dropped at the un‑run addendum reconcile. It exists only in `POSITIVE_FINDINGS_ADDENDUM_1_v1`.

| Item | Grade | Lives in | Owed / next probe |
|---|---|---|---|
| Dirichlet reciprocal‑floor lattice; island boundary at √lo | structural | ADD1‑only | re‑entry; then the curve‑side image question (Frontier 19) |
| Farey solid / 1‑D coprimality net; its ℤ/2 symmetry; non‑genericity vs matched control | VERIFIED‑scope | ADD1‑only | per‑n density null (Frontier 24) |
| Three‑level complexity filtration; sub‑generic fragmentation | structural | ADD1‑only | re‑entry |
| T=2 stratum; whether T=3 opens past fiber width 10⁷ (`max T=2` verified only to 7·10⁵) | OPEN | ADD1‑only | extend the fiber‑width sweep |
| Per‑n coprimality‑net density null; "which cycles carry the ~3× β₁ excess" | OPEN | ADD1‑only | the density null + cycle identification |
| **`(X·Y) mod m ↔ D_terms` "single‑key D‑shadow" link** | stated in v1, **dropped by v9** (pilot H6) | (severed) | is the (x,y)↔D connection real? severed, not refuted |

**Intersection ✦  Thread 2 ↔ Thread 1's amicable bridge.** ADD1 Frontier 19 explicitly names "the d‑side↔curve‑side question across the now‑verified amicable bridge" — a bridge between this invisible thread and the curve object. Currently unreachable because the d‑side is gone from every top‑level doc.

---

## THREAD 3 — The leakage‑readout frontier & the public route to ε.  Contains the current priority lead.

| Item | Grade | Lives in | Owed / next probe |
|---|---|---|---|
| **★ Part XVI.D — Eisenstein‑lift‑norm route: a candidate PUBLIC route to ε** ("flap‑rate is zero for s<3/16 ⇒ ε=0 forced"; "a positive lights up the whole arsenal") | OPEN — **UNTESTED** | v9 (**invisible to the summary**) | run it — this is the current linchpin lead |
| **Part XVI.B / .C — the conditional d‑shadow arsenal** (correct tools, all gated on a *public* value of carry c / boundary bit ε) + the properly‑scoped circularity negative | OPEN — gated | v9 (invisible to summary) | supply a public c/ε (XVI.D is the candidate) |
| **The xy / joint‑(x,y) shadow** — real structure, "#1 OPEN lead"; best cheap readout `e_p(xy)` reaches 0.93 | VERIFIED‑scope | v9 | connect to N7 (its deficit) and to the D‑shadow (Thread 2) |
| **Group‑law joint difference‑set frontier**: `P_i±P_j` via curve addition, `χ₃(x_j−x_k)`, triple/multilinear — the object‑class that *touches the DLP* | OPEN — live frontier | **ADD2‑only** (reverted to a stale "at the floor" null in v9) | re‑enter as a frontier; run the pre‑registered probes |
| Concentration ≡ chaining ≡ correlation‑with‑a‑character (the reduction) | PROVED — for bounded‑degree readouts | v9 | the unconditional (general poly‑time) version is a `[GAP]` |

**Intersection ✦✦  N7 (Thread 1) ↔ the xy shadow ↔ the D‑shadow (Thread 2).** The sub‑Rayleigh deficit lives on the DLP character; the xy shadow is the best readout of it; the D‑shadow links xy to the key residual D. Three threads meet on one object; the middle link (D‑shadow) is currently severed.

---

## THREAD 4 — The reciprocity bridge (p↔n).

| Item | Grade | Lives in | Owed / next probe |
|---|---|---|---|
| The dichotomy (bridge exists at ℓ=3 only for D=−3; secp on that discriminant) | VERIFIED — bounded | compendium, summary Part H | *(watchlist: compendium §0 firmed this to a "complete necessity" — see Overclaims)* |
| The `ℓ≥5` blind spot: "a hypothetical uniform‑correction bridge would read as absent — wrongly" | OPEN (pre‑committed blind spot) | compendium §4 | more null draws at ℓ≥5 |
| "This carries **no leakage or ECDLP content — every quantity is public**" | deflationary caveat, **dropped** by CMP2 | CMP1‑only | owed re‑entry — the caveat that tells a reader not to over‑read the bridge |
| Compendium's own re‑audit | **HUNG (~9h, killed), not completed** | CMP2 footer | the re‑audit is owed; CMP2‑introduced losses went uncaught |

---

## THREAD 5 — Cover / Semaev / index‑calculus.

| Item | Grade | Lives in | Owed / next probe |
|---|---|---|---|
| N4 cover family bound — "no genus‑g cover beats Pollard by KNOWN index calculus" | EMPIRICAL / CITED (family bound, v5) | v9 (**summary carries the older, weaker non‑family form**) | R1 residual (below) |
| **R1 — prime‑field‑native Semaev** (reopened §XI.4) | OPEN — reopened | v9 | matched, group‑order‑controlled consistent‑regime test |
| The prior Semaev CM‑lever null rested on a **provably curve‑blind statistic**; a generic‑CM decomposition‑count effect surfaced | caveat | v9 §XI.4 + ADD1 | the CM‑lever "clean" arm was the inconsistent regime — the null had no power; retest |
| First‑fall degree curve‑independence | HEURISTIC + CITED (regraded down from PROVED) | v9 | — |

**Intersection ✦  R1 (open) is the named residual of the otherwise‑bounded N4 cover object.** The one live lever left in a thread reported as bounded.

---

## THREAD 6 — Cross‑project bridges.

| Item | Grade | Lives in | Owed / next probe |
|---|---|---|---|
| LRC ↔ μ₆/μ₂ shadow (n mod 3 sets the survival core) | open seed | v9 cross‑project | — |
| Finite‑field zeta as an RH test‑bench | open seed | v9 cross‑project | — |

---

## ★ THE ONE CANDIDATE POSITIVE TO TEST — do not re‑deflate

**E3 cubic difference‑set energy on the real 82 keys** (ADD2 B3.4): a **pre‑registered reject** — `E3(real)=13125` at the **98.4th percentile, p≈0.033**, explicitly "**not a null‑estimation artifact**," interpretation **OPEN**, **not** MC‑corrected. v9 buried it back to a stale H3 "at the floor" null.

This is the audit's single clearest instance of the suppression bias in action: a *fired* pre‑registered reject converted to a null at the consolidation seam — precisely "the very lack of false positives is a worry." It sits on the **group‑law difference‑set object‑class (Thread 3), the one class that touches the DLP.**

**Owed (a test, not a verdict):** MC‑correction across the pre‑registered family; reproduction (exact arithmetic); a matched Farey / fundamental‑domain permutation null sharing the signal's forced symmetries; out‑of‑sample on the constructed known‑generator set. Until then it is neither "signal" nor "noise" — it is an untested candidate.

---

## HANGING RESULTS — contradictions the current documents disagree on (preserved, not resolved)

| # | The contradiction | Why it's load‑bearing |
|---|---|---|
| **H‑1** | Is `A_new` supersingular at secp **proved or open?** Summary: proved scale‑free via a Cartier derivation (carrying an owed sign‑flip at `anew_cartier_audit_v2.sage:190` + 2 owed citations). v9: open dim‑2 assumption (N2). | The door P13 (`Hom(E,A_new)=0` at secp) rests on it. |
| **H‑2** | Is the Stickelberger **(D2)** citation **discharged or owed?** ADD2: discharged with 3 Katre caveats. v9: still an owed "debt." Also: "(D2)" is *never defined* in the master (pilot). | The c₂‑branch law `[PROVED — modulo (D2)]` and intersection ★1 both rest on it. |
| **H‑3** | Is **λ₃** a live lead or a **dead gauge artifact?** ADD1 (two scripts): dead (gauge + no covariant excess), retracted twice. v9: "real, broadband, OPEN, not resolved." | v9 lists a debunked artifact as an open finding. |
| **H‑4** | The **census identity** graded three ways in v9: `[VERIFIED]` (M21) / OPEN (N8) / `[PROVED — modulo D2]` (XVI). | Same object, three grades, one document. |

---

## OVERCLAIMS TO WATCH — narrative firmer than its own evidence (re‑grade candidates, NOT leads)

| Claim | As written | Rubric issue |
|---|---|---|
| P13 `Hom(E,A_new)=0` at secp | `[PROVED]` / "Secp‑valid" | inherits the unproved N2 dim‑2 gap only inline; tag should read `[PROVED\|N2]` |
| "**Leakage is COMPUTATIONAL, not information‑theoretic**" (v9 L480 heading) | `[VERIFIED — w/ M14 caveat]` | unscoped closure of the info‑theoretic avenue; contradicts v9's own withdrawn implication (VI‑3 / retraction #9) |
| 120° law (in the **summary**) | `[PROVED — exact]` | v9 walked it back to `[VERIFIED]`; summary is stale‑firmer |
| N1 "**RESOLVED**" (summary B.5 heading) | heading | the summary's own ledger row says "Open on uniformity" |
| Reciprocity dichotomy (compendium §0) | "the mechanism behind the entire dichotomy" | its rows are `[VERIFIED — bounded]`; §4 admits a class of ℓ≥5 bridges it can't see |

---

## OWED RECONCILES  *(logged per the standing "log only" choice — not acted on)*

1. **The addendum layer (ADD1/2/3) is un‑reconciled into v9, under a false "reconciled across master + both addenda" certificate.** Either run a real reconcile, or strike the cert. Until then every top‑level doc overstates its own completeness. *(This map is a partial stand‑in — it surfaces the dropped items — but it is not the reconcile.)*
2. The **recovered results** (Threads 2, parts of 1 & 3, all of ADD3) need a home in a top‑level doc or they stay invisible.
3. **H‑1 … H‑4** each owe a reconciliation decision.
4. The **E3 pre‑registered reject** owes its test battery.

---

## HOW TO USE THIS MAP

- The **intersections (★ / ✦)** are the point: each pairs an open anomaly with a proved neighbor on the same object — the candidate levers. Thread 1 is where they cluster; ★1–★5 are the ripest.
- The **invisible threads (2, and the ADD‑only rows)** are live results you already have — the cheapest wins are re‑entering them, not new work.
- The **one positive (E3)** is the only item here asking for a *measurement* rather than a proof or a reconcile.
- Nothing here is closed. Every row is a lever toward the gate, with the exact next step named.
