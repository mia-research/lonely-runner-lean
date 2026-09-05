# External Literature Survey — Reconciliation Against the Project (v1)

**Date:** 2026-08-05
**Provenance:** four survey/literature-review reports supplied by the user (in `~/Downloads/`):
`Classical ECC Secp256k1 Cryptanalysis.md`, `secp256k1 Classical Cryptanalysis Review.md`,
`secp256k1 Cryptography Research Updates.md`, `ECLDP and secp Curve Cryptanalysis.md`.
**Primary purpose (clarified by user 2026-08-05):** the reports were commissioned to **document recent
adjacent-field work so a future stumble can be *placed*** — a reference frame, not a lever hunt. The
placement map is `REFERENCE_tangential_literature_placement_map_v1.md`; this file is its reliability
audit (a placement map is only safe if its landmarks are graded real vs. phantom).
**Secondary purpose (this file):** determine whether any of the four contains a *finding that updates the
project's state* (none classical), and record which specific claims are verified / garbled / fabricated so
a future session does not re-review them or fold unverified material into project records.

**BOTTOM LINE `[EMPIRICAL — search/consensus-scoped; a failed search, NOT a proven absence]`:**
No classical-cryptanalytic lever is surfaced by these four docs or by a public-literature search. Per project
discipline (`btc_puzzle_investigation/CLAUDE.md`, burden-of-proof-on-the-closure) this is a *scoped null* —
it bounds the public literature as of 2026-08; it is **not** read as a verified absence, and not as evidence
the avenue is closed. What is defensible: none of the four docs contains a *structural* lever that advances
the curve-structure investigation or the puzzle (verifiable by having read them). The four docs' *core thesis* — no classical break; threat surface is
implementation side-channels + eventual quantum — is correct and is the mainstream consensus. Their
*specific* future-dated claims are of mixed reliability: one confirmed content-farm fabrication, several
garbled figures, some unverified. Grade each before any reuse.

---

## 1. What updates the project: nothing on the classical front

`[EMPIRICAL — search-scoped; not an absence]` A targeted search for a 2025–2026 *classical* index-calculus /
algebraic breakthrough on secp256k1 returns only (a) quantum resource-estimate papers and (b) hobbyist
puzzle-solver repos (e.g. `KrashKrash/KICK-Algorithm`) — no *public* classical break found. A failed search
bounds the public literature; it is not proof of absence. This is consistent with
our own index-calculus nulls (`ANALYSIS_n4_cover_family_indexcalculus_*`, `btc_puzzle_semaev_firstfall_*`,
`ANALYSIS_correlation_hierarchy_weil_closure_*`).

**Puzzle relevance = none.** The puzzle is a *reduced-interval* ECDLP (small-range private keys); the
state of the art there is Pollard kangaroo / BSGS over the interval, which puzzle solvers already run.
None of the four docs improves interval search. The side-channel material (below) requires a live signing
device leaking nonces — inapplicable to static puzzle pubkeys.

## 2. Real and relevant, but already in our records (no new lever)

- `[CITED — mainstream]` **Small CM discriminant `D=−3`, `j=0`.** Docs state: enables GLV; violates the
  SafeCurves large-CM-discriminant criterion; **no known ECDLP consequence** (large embedding degree ⇒ no
  MOV/Frey–Rück transfer; no known isogeny to a weaker curve). This is *consistent with but weaker than*
  our own j=0/CM work (`RESULT_26_*`, `btc_puzzle_eisenstein_twin_density_*` which already records
  "No ECDLP consequence"). Adds nothing beyond what we have.
- `[CITED]` **GLV endomorphism, secp/secq 2-cycle, "fake-GLV" decomposition, Renes–Costello–Batina 2015
  complete addition (12M).** All standard, all already covered by our GLV/lift notes. No new object.
- `[CITED]` **SafeCurves: secp256k1 fails twist security.** True and known; an on-curve-validation
  implementation issue, not a break of the curve; irrelevant to the puzzle (pubkeys are on-curve).

## 3. The one genuinely real + citable *refinement* (a wall-characterization, not an opening)

`[CITED — verified from training]` The modern algebraic-cryptanalysis consensus has moved from the
**First Fall Degree** heuristic to the **Last Fall Degree / Castelnuovo–Mumford regularity** as the
complexity metric for Gröbner-basis solving of Semaev systems (Huang–Kosters–Yang–Yeo ~2015;
Caminata–Gorla, *Solving degree, last fall degree, and related invariants*; Semaev–Tenti, Macaulay-matrix
analysis). The earlier sub-exponential FFD *optimism was wrong*; LFD/CM-reg show the solving degree — and
thus the Macaulay-matrix size — stays exponentially large for prime-field curves.

**Direction matters:** this is a *positive, real* result but it *strengthens* the
index-calculus wall — it is not a lever. It is the correct current
characterization of *why* the door our n4-cover/Semaev-first-fall work probed is closed. It is a
legitimate citation for those notes; it does not move any of our grades.

## 4. Confirmed fabrication — do NOT cite

`[FABRICATED — content-farm]` **"ChronoForge" ARM-TrustZone/nRF52 secp256k1 timing attack.** Doc 1 presents
it as a validated real vulnerability, sourced to `github.com/demining/Chronoforge-Attack`. Web check: the
term traces entirely to the **demining / CryptoDeepTools / cryptodeeptech.ru / keyhunters.ru /
attacksafe.ru** ecosystem — a Russian SEO content-farm mass-producing sensational "Bitcoin private-key
recovery" posts. No IACR paper, no CVE, no reputable venue. Docs 2 & 3 correctly say "disregard it" but
for a *wrong reason* (they call it a mere name-collision with a video game / Ruby engine / RL paper
arXiv:2509.15800; in fact the name *is* used for a purported BTC attack — by the content farm). Net: not a
credible attack; the demining/cryptodeeptech citations in doc 1 (works-cited #7,8,9,10) are a reliability
red flag for doc 1 specifically.

## 5. Real papers, garbled specifics — cite the source, not the doc's numbers

`[CITED — real; doc figures unreliable]` **Quantum qubit-collapse table (doc 3 §"Collapse of Logical
Qubit Requirements").** The underlying papers are real and the qualitative trend (logical-qubit estimates
for 256-bit ECDLP falling to ~1,000–1,450; physical <500k) is real. The doc's *specific numbers are
garbled*:
- Chevignard–Fouque–Schrottenloher, **ePrint 2026/280 / EUROCRYPT 2026** — actual figure **≈1,098 logical
  qubits** (reduction from Häner et al. 2020's ~2,124). Doc 3 wrote **1,193**.
- Google Quantum AI, **March 2026** estimate — **≤1,200 (low-qubit) / ≤1,450 (low-gate)** logical,
  **<500k physical**, ~20× physical-qubit reduction. Doc 3 attributed **1,425** to a "Gidney/Google 2025".
- "Luo et al. 2026 = 835 logical qubits" — not independently confirmed here; treat as unverified.
- Roetteler et al. 2017 (~2,330 logical) and Gidney "magic state cultivation" are real.

**Orthogonal to us:** quantum, not classical; bears on the ecosystem/PQ-migration timeline (BIP-360 P2MR,
BIP-361 legacy-sunset — real proposals under debate), not on the curve-arithmetic object or the puzzle.

## 6. Unverified / irrelevant specifics — not folded into any record

- `[UNVERIFIED]` **Pirolo 2026 ResearchGate preprint** (pseudo-Mersenne reduction "8.6% faster",
  "29,177,890 mults/sec", "MESI physical entropy"). A *performance* claim, not cryptanalysis; hyper-specific;
  past cutoff; not verified. Zero bearing on ECDLP or our object either way.
- `[UNVERIFIED]` **CVE numbers** cited (EUCLEAK "CVE-2024-45678"; "CVE-2025-58157" gnark fake-GLV DoS).
  EUCLEAK itself (NinjaLab, Infineon SLE78, 2024) is real; the fake-GLV DoS is a *liveness* bug, not a
  key-recovery. Exact CVE IDs not verified here. All irrelevant to the puzzle.
- `[CITED — real]` LadderLeak (ePrint 2020/615), Minerva (ePrint 2020/728), HNP/Boneh–Venkatesan,
  G6K/BKZ — all real, all side-channel/nonce-leakage, all inapplicable to static puzzle pubkeys.

## 7. Framing caution (keep our stance; do not adopt the docs' absolutism)

The docs use absolutist language — "absolutely immune", "entirely secure", "unequivocally". Per project
stance (`btc_puzzle_INDEX` top-level; `feedback_closure_grade_*`) this is a **consensus/empirical null, not
an analytical closure**: ECDLP remains *assumed-not-proven*. The correct project reading is the conditional
one — *no classical lever is known to the public literature as of 2026-08*, bounded to that scope. Do not
let "immune/secure" leak into our records.

## Gates / owed

- Citations graded from own web checks (§1,2,5 verified live) + training (§3 pre-cutoff, high-confidence).
  Not routed through `citation-verifier` because **no project grade is moved up** by this file — it records
  external material and explicitly folds none of it into our claims.
- This is an ANALYSIS file, not a promotion of a master/handover ⇒ `compile-diff` gate not triggered.
