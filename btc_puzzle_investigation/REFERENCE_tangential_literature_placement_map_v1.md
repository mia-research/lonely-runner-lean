# Tangential-Literature Placement Map (v1)

**Date:** 2026-08-05
**Purpose (per user):** NOT a lever list, NOT a benchmark. A **reference frame** for *placement* — when
the investigation stumbles on a structure, use this to situate it against recently-published adjacent
work, so a find can be recognized as (a) already known there, (b) a novel synthesis touching it, or
(c) unrelated. Built from four user-supplied secp256k1-cryptanalysis survey reports (`~/Downloads/`).
**Reliability is the load-bearing property of a placement map** — grading detail and provenance in
`ANALYSIS_external_literature_survey_reconciliation_v1.md`.

## How to use
1. Found a structure? Match it to a **field** below → check the real landmark refs → decide known /
   novel-adjacent / unrelated.
2. **Never place a find against a Quarantined item** — those are phantoms; placing a real result against
   a fake landmark is worse than having no map.
3. When a landmark's *specific figure* is flagged "use source," cite the primary paper, not the survey.

---

## Real landmark fields (situate here)

**1. Algebraic cryptanalysis / index calculus over prime fields**
- Content: Semaev summation polynomials; Weil descent (inapplicable to prime fields — no proper subfield);
  the metric shift **First Fall Degree → Last Fall Degree → Castelnuovo–Mumford regularity**.
- Real refs: Huang–Kosters–Yang–Yeo (~2015, FFD of Semaev polys); Caminata–Gorla, *Solving degree, last
  fall degree, and related invariants*; Semaev–Tenti (Macaulay-matrix probabilistic analysis, J. Algebra
  2021). `[CITED — verified]`
- **Our objects that place here:** `ANALYSIS_n4_cover_family_indexcalculus_*`, `btc_puzzle_semaev_firstfall_*`,
  `ANALYSIS_correlation_hierarchy_weil_closure_*`. If we hit a Gröbner/solving-degree structure, this field
  tells us it's the (strengthened) wall, not an opening.

**2. CM theory / isogenies / small-discriminant geometry**
- Content: `j=0`, `D=−3`; large embedding degree ⇒ no MOV/Frey–Rück transfer; SafeCurves CM-discriminant
  criterion (secp fails it, no known exploit). Classical toolset: Honda–Tate, Weil restriction of scalars,
  CM descent, Oort/Pries superspecial strata.
- Real refs: classical + survey-level (docs treat j=0 as "GLV enabler, no consequence" and stop). `[CITED]`
- **Our objects:** `RESULT_26_*` (scale-free uniformity; `Jac(C)=Res_{𝔽_{p³}/𝔽_p}(E₁)`; 120° lock),
  `RESULT_anew_*` (Honda–Tate stratification of A_new), `ANALYSIS_120deg_*`. **Placement use (collision
  detection — the map's actual job):** if the investigation derives a CM/j=0 structure, these refs are what
  to check it against for a collision with recent work; a collision would surface from the arithmetic-geometry
  literature (Weil restriction of j=0 curves, CM descent, Honda–Tate strata), which the crypto surveys don't
  reach. This is a lookup for recognizing recent prior art **if** we hit it — **not** a verdict on our
  novelty. Our finds stand as declared; the map does not re-litigate them.

**3. Quantum ECDLP resource estimates** (orthogonal — quantum, not classical)
- Content: collapsing logical-qubit estimates for 256-bit ECDLP.
- Real refs + **source figures** (docs' table is garbled — use these): Roetteler et al. 2017 (~2,330
  logical); Häner et al. 2020 (~2,124); Litinski 2023; **Chevignard–Fouque–Schrottenloher, ePrint 2026/280 /
  EUROCRYPT 2026 (~1,098 logical)**; Google Quantum AI Mar-2026 (≤1,200 / ≤1,450 logical, <500k physical);
  magic-state cultivation (Gidney). `[CITED — real; take numbers from source]`
- Places here only if a structural result ever implies a period-finding / circuit consequence (none does now).

**4. Side-channel / HNP / lattice key-recovery** (tangential to the puzzle)
- Content: nonce-leakage → Hidden Number Problem → CVP/SVP lattice recovery.
- Real refs: LadderLeak (ePrint 2020/615); Minerva (ePrint 2020/728); EUCLEAK (Infineon SLE78, NinjaLab
  2024); Boneh–Venkatesan (HNP origin); G6K / progressive BKZ / BDD. `[CITED — real]`
- Note: static puzzle pubkeys don't leak nonces ⇒ this is a landmark for the *ECDSA-nonce* field, not for
  our pure-arithmetic object. Place ECDSA/signature finds here; do not place curve-arithmetic finds here.

**5. ZK proof systems / curve cycles / non-native arithmetic**
- Content: secp256k1/secq256k1 2-cycle; recursive SNARK accumulators; endomorphism simulation in-circuit.
- Real refs: Curve Trees (USENIX Security 2023); "fake-GLV" decomposition; Halo2 / Nova / Spartan-ECDSA;
  CVE-2025-58157 (gnark fake-GLV half-GCD DoS — *liveness*, exact ID unverified). `[CITED — real; one ID unverified]`
- **Our objects:** `btc_puzzle_glv_2point_lift_law_*`, `btc_puzzle_zomega_scalar_is_Fn_*` — place here if a
  GLV/endomorphism identity turns out to have circuit relevance.

**6. Arithmetic optimization** (performance, rarely a placement target)
- Content: complete addition, fast reduction, GLV decomposition.
- Real refs: Renes–Costello–Batina 2015 complete addition (ePrint 2015/1060, 12M); pseudo-Mersenne /
  Crandall reduction; Shamir/wNAF. Pirolo 2026 ILP benchmark = real field, **specific numbers unverified**.

**7. PQ migration / governance** (ecosystem context, not our math object)
- Real refs: NIST FIPS 203/204/205, draft FIPS 206 (FN-DSA); NIST IR 8547 deprecation timeline; BIP-360
  (P2MR), BIP-361 (legacy-signature sunset) — real proposals under active debate. `[CITED — real]`

---

## Quarantine — phantoms; NEVER place a find here
- **"ChronoForge"** secp256k1/TrustZone timing attack — **content-farm fabrication** (demining /
  cryptodeeptech / keyhunters / attacksafe ecosystem). No IACR paper, no CVE, no reputable venue. `[FABRICATED]`
- Doc 3's specific qubit counts (1,193 / 1,425 / 835) — **garbled**; use field-3 source figures instead.
- Pirolo exact benchmarks; specific CVE IDs — **unverified**; cite only from primary source if ever needed.

---

*Companion audit:* `ANALYSIS_external_literature_survey_reconciliation_v1.md` (why each landmark is graded
as it is). *Index pointer:* `btc_puzzle_INDEX.md` 2026-08-05 entry.
