# Session State — Math Ex / LRC Proof
**Last updated:** 2026-05-18 (**B2b-UNIT-SAFE proved for safe q_ρ range. Theorem: for n=pq, q_ρ ∈ [1,(q-3)/2] → ALL j ∈ J₁ safe (direct corollary of PS-BLOCK-THRESH). Closes B2b sub-case q_ρ ∈ [0,(q-3)/2]. Dangerous sub-case q_ρ ≥ (q-1)/2 OPEN — n=21 adversary counterexample blocks ALL J₁ integer fibres while leaving continuous safe measure ≈ 0.66L.**)

## Completed This Session (2026-05-18 — B2b-UNIT-SAFE proved, dangerous sub-case understood)

### Key Results

1. **Theorem B2b-UNIT-SAFE (PROVED 2026-05-18)**:
   - For n=pq, q_ρ ∈ [1, ⌊(q-3)/2⌋] for ALL unit runners: every j ∈ J₁ is safe for any (d₁,d₂) ∈ (H_q\{0})².
   - Proof: Direct corollary of PS-BLOCK-THRESH. T_ρ(n+j) ∈ [q_ρ, 2q_ρ+1] ⊆ [1,q-2]. Blocking d ∈ H_q requires T ≡ 0 or q-1 (mod q), impossible in [1,q-2].
   - Verification: all n ∈ {21,33,35,55,77} pass exhaustively.
   - Combined with B2b-SAFE (q_ρ=0): **closes B2b sub-case q_ρ ∈ [0,(q-3)/2]**.
   - File: `lrc_b2b_unit_safe_v1.md`, code: `§1.4t verify_b2b_unit_safe()`.

2. **Dangerous sub-case counterexample (n=21)**:
   - q_map = {1:14,2:8,4:15,5:19,8:9,10:1,11:6,13:14,16:11,17:9,19:5,20:7}
   - Result: ALL 12 j ∈ J₁ blocked (d₁=7, d₂=14).
   - Most q_ρ are ≥ 3 = (q-1)/2 (dangerous). One safe runner (ρ=10, q_ρ=1) doesn't block.
   - KEY INSIGHT: Dangerous runners concentrate bad-sets on J₁ integer fibres. Continuous safe measure ≈ 0.66L (Σ 4/e_ρ ≈ 0.34). Integer fibres can be blocked while [0,L) is mostly safe.
   - **This rules out a discrete-fibre proof for the dangerous sub-case.**

3. **lrc_proof.py updates (2026-05-18)**:
   - §1.4t added: PROOF_B2B_UNIT_SAFE + verify_b2b_unit_safe() (safe q_ρ corollary).
   - §1.4t documents dangerous-runner counterexample (n=21).
   - Dashboard row: "n=pq actual speeds B2b" updated to ⚠ PARTIAL with correct scope.
   - run_all: B2b-UNIT-SAFE verify calls added for n ∈ {21,33,35,55,77}.

### Next Steps (Updated 2026-05-18)

**PRIMARY**: Dangerous q_ρ sub-case for n=pq B2b. q_ρ ≥ (q-1)/2 runners can block all J₁.
- The discrete k=1 integer-fibre approach fails for dangerous runners.
- A continuous safe time DOES exist (Σ 4/e_ρ < 1 for specific adversarial configs), but finding a specific RATIONAL witness is harder.
- **Route D1**: Continuous safe interval → rational witness. Since safe measure > 0, ∃ rational t in the safe interval. Need to identify explicit rational t with full loneliness (unit + non-unit runners).
- **Route D2**: Large q_ρ makes e_ρ → ∞ → unit runners "transparent" in limit. For sufficiently large q_ρ, the unit runners barely overlap any given interval — but the adversary can choose q_ρ to concentrate blocking on J₁.
- **Route D3**: Look at other k-bands (not k=1). With dangerous runners, which k values give safe fibres? Empirically test for n=21.

**SECONDARY**: n=p² Gap C / adversarial large-q (from 2026-05-15).

---

## Completed This Session (2026-05-15 — N-PSQ-MULTIBAND disproof + audit)

### Key Results

1. **N-PSQ-MULTIBAND DISPROVED (2026-05-15)**:
   - Counterexample p=5, pair (5,10): q_map = {1:75, 2:5, 3:2, 4:25, 6:354, 7:1875, 8:599, 9:15, 11:50, 12:0, 13:10, 14:20, 16:1875, 17:309, 18:2, 19:3, 21:174, 22:2, 23:545, 24:117}
   - J₁=20/20 covered AND ALL 500 fibres across full k-period blocked. Max q_ρ=1875=3·5⁴.
   - **Mechanism**: q_ρ >> p² → T_ρ(kp²+j) advances by ~q_ρ per k step → T mod p² cycles O(q_ρ/p²) times → single runner blocks O(q_ρ/p²) k-bands. Earlier "≈4 k-values per runner" assumed q_ρ ≲ p²; fails for large q_ρ.
   - **Why previous "0 failures" was incomplete**: hill-climber only maximised J₁ coverage; never jointly optimised for k≠1 blocking. Dual-objective hill-climber found disproof immediately.

2. **Framework clarification (audit)**:
   - bad_set IS the correct formal blocking criterion (not geometric distance). d ∈ {(-T·ρ⁻¹) mod p², (-(T+1)·ρ⁻¹) mod p²} checks the Beatty-sequence floor-crossing blocking condition.
   - The Q3 "82 geometrically isolated fibres" analysis was conceptually misframed (geometric distance ≠ bad_set criterion).
   
3. **Full k-period vs narrow search**:
   - Searching k ∈ {0,...,p-1} only (p bands) gives FALSE failures — the conjecture fails here because fallbacks are often at k ≥ p.
   - The correct full k-period is {0,...,p²-1} (p² = 25 bands for p=5).
   - With full period: **0 failures** across 487 (dropped_pair, J₁-covering q_map) triples.

4. **N-PSQ-MULTIBAND CERTIFIED (p=5, 2026-05-15)**:
   - Dropped pairs tested: 6 total (all pairs from H\{0} = {5,10,15,20})
3. **lrc_proof.py updates (2026-05-15)**:
   - §1.4s comment block: replaced conjecture text with disproof documentation, counterexample q_map, mechanism, and open directions.
   - Dashboard row: 🔬 → 💥, counterexample description added.
   - Dashboard print line: updated to 💥 DISPROVED.
   - run_all N-PSQ-MULTIBAND verify call: removed (testing a false statement).

4. **What remains proved (unaffected by disproof)**:
   - N-PSQ-UNIFORM-SAFE (proved 2026-05-10): uniform q always has a safe fibre.
   - SAFE-K0-EXT (proved 2026-05-08): q_ρ ≤ p²-1 → bottom strip j∈{1,...,p-1} safe.
   - Both require q_ρ ≤ p²-1; disproof uses q_ρ up to 3·p⁴ >> p²-1.
   - All 8 previously proved lemmas confirmed correctly implemented with no drift.

### Next Steps (Updated 2026-05-15)

**PRIMARY**: New proof approach for n=p², adversarial large-q. Gap C / band-shifting is closed as a strategy.
- **Route A (equidistribution)**: For large q_ρ, gcd(e_ρ,p⁴)=1 → blocking density = 2/p² per runner. Product density (independence assumption): (1-2/p²)^{φ(p²)} ≈ exp(-2) ≈ 13.5% > 0. Need: unconditional proof of Weyl independence assumption.
- **Route B (NUD + divisible structure)**: Dropped runners ∈ H have different bad_set formula (coset of H_g). Combining unit runner bad_set analysis with divisible runner constraints may give algebraic obstruction not captured by current framework.
- **Route C (longer time scale)**: For large q_ρ, natural period ≈ 1/e_ρ << 1/p⁴. A witness time on a different scale may circumvent the blocking entirely.
- **Next concrete step**: Investigate Route A — empirically measure blocking independence for the p=5 disproof q_map. If runners' blocking positions are nearly independent, the density argument gives a quantitative lower bound.

## Completed This Session (2026-05-11 — B2-HIGH ANALYTIC CLOSURE)

**§1.4p added to lrc_proof.py**: Formalises the B2-HIGH analytic closure:

**Key results proved:**
1. **Lemma B2-HIGH-UNIT-BAD (PROVED, unconditional)**: For m₁=1, any unit runner ρ with e_ρ=ρ+q_ρp² (q_ρ ≥ 0 arbitrary), any s with p∤s: EXACTLY 2p² of the p⁴ k-values in {0,...,p⁴-1} have runner ρ bad. Proof: gcd(e_ρ,p⁴)=1 → k↦e_ρk mod p⁴ is a bijection → positions form a complete p⁴-lattice → exactly 2/p² fraction is bad. Verified: `verify_b2high_unit_bad_count(p∈{5,7})`, 0 failures.

2. **Theorem B2-HIGH-CONDITIONAL (PROVED, conditional on Weyl independence)**: Under Weyl independence (no Z-linear relation Σnᵢeᵢ ≡ 0 mod p⁴), joint density of good (k,s) pairs = ((p²-2)/p²)^m ≥ exp(-2) ≈ 13.5% for all p≥5. Gives N_good ≥ 602k for p=13.

3. **Sub-torus dim ≥ 1 (PROVED)**: For any adversarial q_ρ: since gcd(e_ρ,p⁴)=1, the orbit over k=0,...,p⁴-1 is never a single point. The sub-torus T has dim ≥ 1.

4. **Gap C (OPEN)**: Unconditional existence — union bound gives total bad coverage count m·2p² ≥ p⁴ for p≥5, so bad sets COULD tile the k-axis in principle. Empirically: 0 failures over 130+ random configs. Three proof routes (LLL, complementary pairs non-tiling, quantitative Weyl on sub-torus).

**Functions added to lrc_proof.py:**
- `verify_b2high_unit_bad_count(p, trials, seed, verbose)` — verifies exact 2p² count
- `theorem_b2high_conditional_density(p)` — returns density bound, runner count, proof status
- `check_b2high_weyl_independence(p, q_map, m1)` — pairwise Weyl screen

**Companion document:** `lrc_b2high_closure_v1.md`

## Completed This Session (2026-05-11 — B2-HIGH-WITNESS implementation)

**§1.4o added to lrc_proof.py**: Formalises the B2-HIGH witness time construction
t(k,s) = (k·p²+s)/(m₁·p⁶) for super-divisible runners.

**Key results proved:**
1. **Runner D1 safety**: {m₁p⁴·t(k,s)} = s/p² (independent of k). Safe for all s ∈ {2,...,p²-2} with p∤s.
2. **Runner D2 safety (m₁=1 case)**: position = {m₂s/p²} (also independent of k). Safe for all valid s.
3. **D2 general**: safe for (1-2/p²) fraction of (k,s) candidates (uniform distribution over the lattice).
4. **Key correction**: B2-HIGH has only p-3 NUD runners (2 dropped NUD residues replaced by super-div runners). Function `verify_b2_high_witness()` now accepts `dropped_nud` parameter.

**Computational verification:**
- 120 random B2-HIGH configurations across p ∈ {5,7,11,13}: 0 failures
- Adversarial q ∈ {0,1,p,p²,p³} tested. All find explicit witness (k*,s*).
- Safe fraction for p=5, m₁=1, m₂=2, q=0 (2-NUD config): 436/11250 = 3.88% > 0
- Key bugs found and fixed: D2 denominator (m₁p² not m₁p⁴), k-range (m₁p⁴ not m₁), NUD count

**Open gap**: Unconditional analytic proof that ∃(k,s) safe for ALL runners simultaneously.
Equidistribution product bound gives ((p²-2)/p²)^{p²-1} ≥ 13.5%, but requires independence
of runner positions (Gap A). Complementary pairs structure (Gap B) may close it.

**Functions added to lrc_proof.py:**
- `verify_b2_high_witness(p, m1, m2, q_map, dropped_nud, max_k, verbose)` — explicit witness finder
- `b2_high_safe_fraction(p, m1, m2, q_map)` — fraction of candidates simultaneously safe
- `run_b2_high_verification(p_list, trials_per_p, seed)` — systematic multi-prime test

## 👉 Read first: [`handover_2026_05_05.md`](handover_2026_05_05.md) — UNIFIED state & next-session plan (revised after user flagged branching anti-pattern; the previous "three open items" are reframed as instances of one universal claim).

## Current Canonical File
**`lrc_proof_v10_19.md`** — Predecessor: v10.18. Key additions:
- **Conjecture N-PSQ-T02** (k=1 band has safe fibre under any adversarial q_ρ for p ≥ 17), with empirical certificate from `n_psquared_actual_speeds_recon_v1.py`: aggressive adversarial worst-case 72.8%/74.5%/78.6% safe-j at p=29/31/37, monotonically increasing.
- **Theorem N-PSQ-ACT** (conditional Tier 1 closure given N-PSQ-T02).
- **Lemma N-PSQ-T03** (proved 2026-05-05): floor decomposition T_ρ(j) = M(q_ρ,j) + ε(ρ,j) with ε ∈ {0,1,2}; Safe-q Regime: q_ρ ∈ [1, ⌊(p-3)/2⌋] ⟹ no blocking. Verified exhaustively for p ∈ {29,31,37} (812×812, 930×930, 1332×1332, all q in regime, 0 blockings).
- **Certified harness p=29**: 175,770 combos rep-speeds + adversarial divisibles, 0 failures (175 min on 2026-05-05).

**OPEN ITEM (analytic):** Conjecture N-PSQ-T02 for q_ρ ≥ ⌈(p-1)/2⌉ (the "high-q regime" — half the q-axis). Lemma N-PSQ-T03 closes the low-q half unconditionally.

**Predecessors:** v10.17 (N-PSQ-MOD, Weil bound), v10.16 (period-staircase B2b), v10.15 (Silence Fibre, Theorem A squarefree complete), v10.14, v10.13 (ERR-C-01 fix), v10.12, v10.11 (CT.1-FINAL).

## Proof Status Summary (UPDATED 2026-05-04)
- **Tier 1 (x₀ ≥ 1): PARTIAL — one open family:**
  - Prime n: Lemma 5.2 + CT.1-FINAL ✓
  - Composite n dropped-unit: Proposition 11.3-FINAL + Lemma 11.3a' ✓
  - Composite n even unit-complete (Sub-case B1): parity argument ✓
  - Composite n = p^k, k≥3 (Theorem 11.5) ✓; n=9 (G-PRES) ✓
  - **n=p², representative speeds, ALL p≥5: ✅ PROVED (2026-05-04)** — Theorem N-PSQ-REP (Lemmas N-PSQ-T01 + N-PSQ-REP-COUNT in §13)
  - n=p², actual speeds, p∈{5,7,11,13,17,19,23}: ✅ CERTIFIED (adversarial harness)
  - **Open item:** n=p², p≥29, actual speeds — analytic counting over all k-bands pending
  - Composite n odd ≥2 prime factors, both dropped non-units, |E_div|=0: t*=1/n ✓
  - Sub-case B2b (squarefree n=pq, |E_div|=1): representative speeds ALL n ✓ (Theorem B2b-SAFE); actual speeds n=15 ✓; actual speeds n>15 ⚠ OPEN
  - Theorem 12.1 Case B: representative speeds ✓ (Lemmas 12.2/12.3); actual speeds ⚠ OPEN
  - **Theorem A: PROVED for representative speeds all n, actual speeds all squarefree n and n=p² p≤23. OPEN for n=p², p≥29, actual speeds.**
- **Tier 2 (x₀ ≥ φ(n)): PARTIAL** — composite dropped-unit proved. Remaining: Proposition 10.5 (prime n).
- **n=11 (AP paper, Lineage B): INCOMPLETE** — sub-cases D1/D2 (ERR-B-01) and runner 5 at k=3 (ERR-B-02) still open.

## Completed This Session (2026-04-27 — Theorem 12.1 Case B analysis)
- **Bertrand prime witness structure discovered:** For the representative tuple in Thm 12.1 Case B, any prime q∈(n,2n) with k=(-d₁⁻¹ mod q) gives witness t=k/q. Key: d₁k≡-1 (mod q) → d₁ lands at 1/q<1/n (dropped, so irrelevant); all retained residues have distance ≥2/q>1/n. Verified for n=15,21,35 (all (d₁,d₂) pairs). Does NOT extend to general actual speeds.
- **Floor-reset fails for Thm 12.1 Case B:** Divisible runner with q₀=182 (speed 2730) blocks ALL 23 targeting events for n=15,d₁=3,d₂=6 via CRT (same mechanism as Sub-case B2b counterexample). This disproves the earlier note that "the extra-runner CRT obstruction does not apply since there are no extra non-unit runners" — divisible runners provide the same blocking.
- **Universal failure confirmed:** The floor-reset targeting approach is insufficient for BOTH Sub-case B2b and Theorem 12.1 Case B. In both cases, a runner (extra non-unit or divisible) can be chosen with large q to block all targeting events simultaneously.
- **Partial data:** For some (d₁,d₂) pairs, max single-runner blocks <100% of events (e.g., n=15,d₁=9,d₂=10: max 38/43). But with multiple runners chosen adversarially, collective coverage of all events is likely achievable.
- **v10.14 updated:** Theorem 12.1 Case B section updated with accurate gap analysis, Bertrand prime partial result, and honest OPEN status with detailed mechanism description.

## Completed This Session (2026-04-26 — ERR-C-02 gap analysis)
- **Theorem 9.2c'' confirmed FALSE.** Gap in proof: "O(log q_j) pacemakers blocked per extra runner" is wrong because q_j is unbounded and the blocking condition is a CRT-compatible congruence in q.
- **Counterexample verified (Python, 2026-04-26):**
  - n=15, E={1,2,4,5,7,8,9,10,11,12,13,14,30,1189}
  - Unit-Complete ✓, gcd-1 ✓, |E|=14=n-1 ✓, dropped non-units d₁=3,d₂=6 ✓
  - Extra runner 1189 (residue s=4, q=79) satisfies (s·r_dep + floor(1189·m1/e_u)) ≡ 0 mod 15 for ALL 4 valid targeting events: (d=3,eu=13,m1=9,r_dep=4), (d=3,eu=14,m1=10,r_dep=9), (d=6,eu=11,m1=4,r_dep=12), (d=6,eu=13,m1=5,r_dep=2).
  - Note: q=79 was constructed to satisfy all 4 blocking congruences simultaneously via CRT.
- **v10.14 header updated** to document the gap, counterexample, and honest Tier 1 status (OPEN).
- **session_state.md "Next Tasks" updated** with three candidate paths for a new Sub-case B2 proof strategy.
- **Two Python bugs identified and fixed** during analysis:
  1. r_dep formula: correct is -(m-1)·e_u⁻¹ mod n (not -(m-1)·u_d⁻¹ mod n).
  2. Coverage formula: correct is (s·r_dep + T) mod n ∈ {0, n-1} (not coset formula).

## Completed This Session (2026-04-24)
- **v10.13 produced from v10.12.** Two targeted repairs integrated:
  1. **ERR-C-01 fix → Lemma 11.3a':** Correct floor formula $T_e(b^*) = e - q_e - 1$; witness $\hat{b} = b^*-1$ for divisible $k \equiv 1 \pmod n$; iterative chamber-shift for $q_e \geq 1$ runners. Proof Cases I–III fully written. Numerically verified (n=6 examples).
  2. **ERR-C-02 partial fix → Theorem 9.2c':** Proved that no unit q=0 runner has pre-existing bad-set coverage of r_dep at the specific m. Algebraic argument: LOW condition reduces to ρ ≡ d (mod e_u), only ρ = d possible (dropped). HIGH condition excluded via gcd argument. Non-unit retained runners: still open.
- **Dependency map updated** in §13 with honest Tier 1 status table.
- **Numerical verification:** d+e_u > n-1 confirmed for all n in {4,...,20}; Lemma 11.3a' Case (†) counterexample verified (runner 10 n=6 correctly requires shift).

## Completed This Session (2026-04-28 — Sub-case B2b closure + Theorem 12.1 Case B analysis)  [SUPERSEDED — see correction block below]

~~✅ **Sub-case B2b PROVED:**~~  ← **RETRACTED (see below)**

✅ **Theorem 12.1 Case B analysis (still valid):**
- **Bertrand prime partial result**: Verified for representative tuple. Fails exhaustively for general actual speeds.
- **Exhaustive extension test**: No Bertrand prime works for all divisible speeds q_0∈{1,...,500}.
- **Three-speed geometric outline**: Proposed but not proved. Status: OPEN.

## Completed This Session (2026-04-28 — B2b proof retraction + gap analysis)

❌ **Sub-case B2b "PROVED" claim RETRACTED:**

**Error 1 — Lemma B2b-MISS (miss-set formula wrong):** The lemma stated Miss(b*) = H_p−1 ∪ H_q−1, but n−1 ∈ H_p−1 ∩ H_q−1 and n−1 IS covered by unit runners (as the element −1 = n−1 in every unit's bad-set). Correct miss-set: M* = (H_p−1 ∪ H_q−1) \ {n−1}, size p+q−2 (not p+q−1). Fixed in v10.15.

**Error 2 — Theorem B2b-SAFE (invalid extension to actual speeds):** The theorem finds a fibre $\hat{b}$ where non-unit runners are transparent, then applies Lemma B2b-MISS to get unit coverage = {u−1 : u∈U} ∪ {n−1}. But Lemma B2b-MISS holds ONLY at b* for REPRESENTATIVE speeds (q_e=0). For actual speeds, the adversary can shift every unit runner's bad-set pair freely by adjusting q_e.

**Explicit adversarial cover of b* for n=15 (constructed 2026-04-28):**
Unit pairs (spacing = ρ⁻¹, pair = {c, c+ρ⁻¹}):
- ρ=1 (spacing 1): {0,1} | ρ=14 (spacing 14): {2,3} | ρ=8 (spacing 2): {4,6} | ρ=7 (spacing 13): {5,7}
- ρ=4 (spacing 4): {8,12} | ρ=11 (spacing 11): {9,13} | ρ=2 (spacing 8): {3,10} | ρ=13 (spacing 7): {7,14}
Union = {0,1,...,14} (all 15 residues, with 3 and 7 duplicated).
The adversary chooses q_e for each unit runner to place its pair at these positions. Simultaneously, non-unit runners are made transparent. Thus b* is fully covered for this actual-speed tuple.

**Key identity driving the cover:** Since 2φ(n) = 16 > 15 = n for n=15, and each of the φ(n)=8 pairs can be placed anywhere (their spacing ρ⁻¹ is fixed but the centre c is free), the adversary has enough freedom to tile ℤ/nℤ with 1 overlap.

**What IS proved for B2b:**
- Representative-tuple proof at b*: CORRECT. Lemma B2b-MISS (corrected), Lemma B2b-SINGLE, Theorem B2b-SAFE. Written into v10.15 §11.
- Actual speeds: OPEN. A global multi-fibre argument is needed; no correct proof currently known.

**New canonical file:** v10.15 (v10.14 with B2b corrected; v10.14 retained as working draft).

**Tier 1 status update:**
- Sub-case B2a: ✓ PROVED
- Sub-case B2b: ⚠ PARTIAL (representative tuple only)  
- Theorem 12.1 Case B: ⚠ OPEN
- Overall: ~14/18 major branches fully proved (was erroneously claimed 17/18)

📊 **Tier 1 status update (CORRECTED 2026-04-28):**
- **Sub-case B2b**: ⚠ PARTIAL — representative tuple proved; actual speeds OPEN
- **Theorem 12.1 Case B**: ⚠ OPEN
- **Overall**: ~78% (14/18 major branches fully proved; prior 95% claim was wrong)

## Completed This Session (2026-05-04 — N-PSQ-T01 + Theorem N-PSQ-REP)

✅ **Lemma N-PSQ-T01 proved analytically:** For n=p², representative speeds (e_ρ=ρ<p²), at any k=1 band fibre r=p²+j: T_ρ = floor(ρr/p⁴) ∈ {0,1}. Both cases give bad_set ∩ H\{0} = ∅ (T=0: bad={0,-ρ⁻¹}, units not in H; T=1: bad={-ρ⁻¹,-2ρ⁻¹}, both units not in H for p≥3). Verified computationally for p∈{5,7,11,13}: 0 failures.

✅ **Corollary N-PSQ-REP-COUNT proved:** Safe j-count in k=1 band (representative speeds) ≥ p(p-1) − 2(p-3) = p²-3p+6 ≥ 16 for p≥5. Unit runners contribute 0 blockings (by T01). Divisible runners safe by gcd. NUD runners (p-3) block ≤ 2 j-values each.

✅ **Theorem N-PSQ-REP proved analytically (all p≥5):** For n=p², representative-speed Unit-Complete tuples, safe fibre exists in k=1 band. Closes n=p² representative-speeds case for ALL p (no harness needed).

✅ **verify_n_psq_t01(p) function added to lrc_proof.py §13.** Called from theorem_n_psquared_certified() for p∈{5,7,11,13}. Dashboard updated: new ✅ row "n=p², rep speeds, all p≥5".

✅ **lrc_proof_v10_18.md created.** Adds N-PSQ-T01/REP-COUNT/REP lemmas in §13, updates Tier 1 table and dependency map.

**Remaining open:** n=p², p≥29, actual speeds (harness certified to p=23; analytic counting over all k-bands pending).

## ⚠️ MAJOR STATUS UPDATE (2026-05-11) — N-PSQ-T02-RESTRICTED DISPROVED

**N-PSQ-T02-RESTRICTED is FALSE.** The conjecture "non-uniform v_p≠3 q-tuples cannot cover all of J₁" was DISPROVED by adversarial search.

**Counterexample (p=5):** q_map = {1:75, 2:5, 3:2, 4:25, 6:5, 7:1875, 8:1875, 9:15, 11:50, 12:25, 13:10, 14:20, 16:1875, 17:15, 18:2, 19:3, 21:1875, 22:2, 23:50, 24:2500}. All v_p ∈ {0,1,2,4}. Covers ALL 20 fibres of J₁ for d₁=5, d₂=10.

**Mechanism:** v_p=0 runners (small q, e_ρ≈ρ) alone can saturate J₁. ρ=19 (q=3) blocks d₁=5 at 11/20 fibres; ρ=22 (q=2) covers d₂=10 at the remainder. Cross-pair blocking via v_p=0 is the dominant mechanism.

**Additional finding:** H_p-safe fibres in k=0 band are NOT LRC-safe. Runners with q_ρ≡0 mod p give e_ρ mod p⁴ = ρ < p², meaning frac=ρ<p² at r=j — directly LRC-blocking. The H_p framework is a partial approximation that misses blocking events near integers.

**Confirmed counterexamples:** p∈{5,7,11,13} by verify_nonunif_vp2_adversarial (2000 trials, seed=42).

**What remains valid:**
- N-PSQ-UNIFORM-SAFE (proved 2026-05-10 for v_p∈{0,1,2,4+}, uniform q): unaffected
- N-PSQ-REP (representative speeds q_ρ=0, all p≥5): unaffected
- N-PSQ-SAT conjecture (v_p=3 regime): unchanged (still open)

**N-PSQ-MULTIBAND DISPROVED (2026-05-15).** See disproof details in §1.4s and "Completed This Session" above. New primary direction: adversarial large-q proof via equidistribution or different time scale.

## Next Tasks (priority order)

### PRIMARY — New approach for n=p², adversarial large-q (2026-05-15 updated)

**Status:** Gap C / band-shifting CLOSED (disproved). Need new mechanism for Unit-Complete n=p² with q_ρ >> p².

**Route A (equidistribution density):**
  - For any q_ρ, gcd(e_ρ,p⁴)=1 → blocking density 2/p² per runner over k-period.
  - Product density (under Weyl independence): (1-2/p²)^{φ(p²)} ≥ exp(-2) > 0 → safe fibres exist.
  - OPEN: Prove Weyl independence unconditionally (no Z-linear relation Σnᵢeᵢ ≡ 0 mod p⁴ for random q_ρ).

**Route B (NUD + divisible structure):**
  - Dropped runners d₁,d₂ ∈ H = {p,2p,...,(p-1)p} have bad_set = gcd-coset (different from unit runners).
  - Combining unit and divisible runner bad_set constraints may give an algebraic obstruction for joint coverage.

**Approach C (min-uncovered formula — now moot for disproof; still useful for Route B):**
  - Previous empirical: min = p-2 for p=5 (with q_ρ ≤ 200). Now refuted for q_ρ up to 3p⁴.
  - If min = p-2: look for algebraic proof via the p-2 "safe residue classes" in PAIR-BLOCK-EXCLUSION.

**Next concrete step:** Run greedy minimization for p=7 to test the p-2 hypothesis.

### PRIMARY — Close Gap C (B2-HIGH unconditional existence)

**Goal: Prove that for any adversarial q_ρ, ∃(k,s) in B2-HIGH lattice safe for ALL runners.**

Three routes, in order of tractability:

1. **Route B (Complementary pairs non-tiling)**: For each complementary pair (ρ,p²-ρ), their bad sets B_ρ and B_{p²-ρ} each have size 2p² in {0,...,p⁴-1}. By PAIR-SUM (proved 2026-05-08): T_ρ+T_{p²-ρ} = S, blocking condition T ≡ 0 or p-1 mod p for each. Show that no arrangement of p(p-1)/2 pairs of bad-interval pairs can tile {0,...,p⁴-1}. Key: the adversary's freedom to position the pair's intervals is constrained by the PAIR-SUM identity and the specific bad-residue structure.

2. **Route C (Explicit construction for high-q regime)**: For q_ρ ≥ p for all unit runners (the "all-high-q" adversarial case), find an explicit (k*,s*) analytically. Empirical: at k* = p²/2 (midpoint), positions ≈ q_ρ/p (for the leading term) — for q_ρ large, position ≈ q_ρ/p mod 1 cycles through all residues. If q_ρ diverse (not all same residue class mod p), some k* gives all positions in (1/p², 1-1/p²).

3. **Route A (Quantitative sub-torus)**: Use the fact that the orbit has dim ≥ 1 and each coordinate sweeps all p⁴ points. The "density" of good points on the sub-torus T is bounded below by the Haar measure of G ∩ T. For the 1D diagonal sub-torus (worst case): density ≥ (p²-2)/p² > 0. Make quantitative for the finite lattice.

### SECONDARY — Close actual-speeds gap for n=p², p≥29

**Goal: Prove analytically that a safe fibre exists for actual speeds (q_ρ≥1) for all p≥5.**

1. **Tighten the counting argument for actual speeds:** The candidate lemma (lrc_n_psquared_candidate_lemma_v1.md) gives safe j ≥ (p²-5p+12)/2 ≥ 6 for k=1 band, but only for q_ρ ≤ 1. For arbitrary q_ρ: show each unit runner still blocks ≤ 2 j values in k=1 band (width-<1 argument applies regardless of q_ρ since gcd(e_ρ,n²)=1). If this holds, then: unit blockings ≤ 2φ(n) = 2p(p-1) but EACH j blocked by at most 2 distinct runners → by pigeonhole some j is unblocked iff 2φ(n) < 2·(total j), i.e., φ(n) < total j = p(p-1). This is always FALSE (equality). Need a sharper argument: show that the "near 0" and "near n²" j-values for a single runner are ALWAYS different j-values (never the same), halving the effective blocking count.

2. **Extend certified harness to p=29:** Run verify_n_psquared(29) (adversarial q_unit sweep). Estimated: ~3000 combos at ~30s each = ~25 hours (too slow for auto-run). Run via background process or restrict to sampled adversarial tuples.

### SECONDARY — Close actual-speeds gap for general squarefree n=pq

**Goal: Prove bijection impossibility for general n=pq (extends Theorem B2b-ACTUAL from n=15 to all n=pq).**

1. **General bijection impossibility**: Show that for any squarefree n=pq (p<q primes), the seps multiset ((p-1) copies of H_q\{0}) cannot be realized as a bijection σ: P→P on any valid near-tiling P. The n=15 proof (Lemma PS-6) uses: (a) P uniquely determined by doubly-covered element d; (b) sep=p and sep=n-p have exactly p-1 valid sources each; (c) after assigning them, sep=2p has fewer than p-1 valid sources among remaining positions. For general n, the near-tiling P is NOT uniquely determined by d (has multiple doubly-covered elements); the argument needs a different structure.

2. **Key structural insight to exploit**: The seps multiset {(d_1-d_2)·ρ mod n : ρ ∈ U} has (p-1) copies of each element of H_q\{0}. The "smallest sep" s_min = p has (p-1) runners needing (p-1) distinct sources with a+p ∈ P. Count |P ∩ (P-p)|: for general n=pq near-tiling P (with 2φ(n)-n doubly-covered elements), this count can be computed. Show it is always less than p-1 for some sep value.

3. **Alternatively**: Extend the Silence Fibre argument to actual speeds via a different perturbation strategy that blocks the adversarial covering of H_q. Key: the adversary places elements in H_q via ρ∈[1,q), but these form a SPECIFIC algebraic structure (multiples of p·ρ^{-1}); maybe they can't cover all of H_q\{0} simultaneously for BOTH d_1 and d_2.

### TERTIARY — General squarefree n=pq bijection impossibility (B2b)

### TERTIARY — ERR-B-01/02 (n=11 AP paper, separate lineage)
- **ERR-B-01 Sub-cases D1/D2:** Runner 8 at k=2 in ++------ class.
- **ERR-B-02 Runner 5 at k=3:** At a₅∈[4.3,4.5].

### FILE STATUS
- **v10.16**: **CANONICAL** — Period-staircase lemmas (PS-1–PS-6) for B2b actual speeds (n=15); honest status table; Lemma 12.2 scope note. TWO OPEN ITEMS. Use for all future work.
- **v10.15**: Predecessor with incorrect "PROVED" claims for actual speeds. Retained for reference. DO NOT use as canonical.
- **v10.14**: Working draft (Case B OPEN). Retained.
- **v10.13**: Pre-Case-B canonical. DO NOT modify.

## Lineage C Audit Results (2026-04-19 — NEW)
**ERR-C-01 (v10.12 Lemma 11.3a, S2/S3):** v10.11 honestly labeled this as "under repair template"; v10.12 REGRESSION promoted it to "proved for composite n ≥ 4" without fixing actual-speed flaw. Counterexample: n=6, E={7,2,3,10,6}, d=5, b*=175, L=210 — runner 10 (residue 4, q=1) covers s_d via bad(10,8,6)={1,4}; runner 6 (divisible) covers all residues. Proof path at b* fails; global x_0=90 (LRC still holds via other fibres).

**ERR-C-02 (v10.12 Theorem 9.2c, S2):** Representative-form CG2 uniqueness fails for actual speeds. Counterexample: n=6, E={1,8,3,5,6}, d=4, e_u=5, m=2, r_dep=1, L=120, b=48 — runner 8 (residue 2, q=1) satisfies actual CG2 and bad(8,3,6)={1,4} covers r_dep=1. b=48 unsafe; global x_0=56.

**ERR-C-03 (v10.12 §2.7 Theorem 2.4, S2/S3):** General-prime Runner Incompatibility for all prime p≥11 inherits Lineage-B enumeration gaps (ERR-B-01/02). Algebraic identity p²-9p-4 is correct; A₂(p),B₂(p) bounds rest on same lemma schema that leaked at p=11.

**Clean in v10.12:** §5.3 Lemma 5.1a (actual-speed base-fibre patcher), CT.1-FINAL, Lemma 5.2 (prime n), §8 Theorems 8.2/8.3 (correct lcm bound), §9.2a' actual-speed CG criteria, §9.3b/§9.3f analytic bounds, §2.7 algebraic identity.

## v11.1 Verification (2026-04-18)
- Forward-reference grep: 29 cited ↔ 29 defined, zero orphans, zero dangling.
- Stale-language grep ("template/pending/TBD/repair"): zero hits.
- DeepSeek verify §6 (sliding-window termination, prime $n$): **ACCEPT-WITH-MINORS**, confidence 0.95.
- DeepSeek adversarial §§9–10 (floor-reset CG1/CG2, composite late-window): **score 95**, confidence HIGH.
- Qwen §5 second opinion: INCONSISTENT verdict; all 4 issues dissolved on inspection (prose-level, dependencies covered separately).
- Gemma4:26b unavailable (Ollama blob unloadable — "unable to load model"); substituted Qwen.
- Artifacts: `reports/v11_1_verification/{deepseek_sec6,adversarial_sec9_10,qwen_sec5}.log`, `SUMMARY.md`.

## Completed This Session (2026-04-19)
- **v11.3 repair draft**: 8 fixes applied — Lemma 2.5→2.5', Definition 2.8 refs, Thm 8.2 L-bound + Remark 8.4, Lemma 10.2 floor formula + Remark 10.3, Thm 11.1 Case A language, §12.2 certificate disclosure. Harness: 23,238 tuples, 0 failures.
- **ERR-B-01/02 repair doc**: `lrc_n11_incompatibility_repair_v1.md`. Runner 7 at k=5 CLOSED (forces GF(I₇)>0). Runner 8 at k=6 CLOSED (mutually exclusive with ERR-B-01 regime). Runner 8 at k=2 OPEN (sub-cases D1/D2 identified, not closed). Runner 5 at k=3 OPEN.
- **ERR-C-01 repair doc**: `lrc_c_err_repair_v1.md` Part 1. Correct floor formula $T_e(b^*) = e - q_e - 1$ derived. Divisible-runner fix via $\hat{b} = b^*-1$ proved (bad=∅). Counterexample verified: shift to $b=133$ gives $s_d=4$ uncovered. Lemma 11.3a' (corrected statement) written.
- **ERR-C-02 repair doc**: `lrc_c_err_repair_v1.md` Part 2. Root cause: CG1/CG2 only capture reset-triggered coverage; pre-existing bad-set coverage ignored. CG2 formal criterion reanalysed (runner 8 fails CG2 formally: $\sigma_f(8,2)=1 \neq s+u=3$). Deeper: bad-set coverage independent of CG. Repair D (modified m search) defined. Large-$e_u$ existence proved; small-$e_u$ open.

## Next Tasks (priority order)
1. **ERR-B-01 Sub-case D1/D2 (OPEN):** Read `lrc_n11_algebraic_lemma_v1.md` §3 to identify natural slot assignments for runners 4 and 5 in the ++------ class. Determine whether runner 4 (a₄ ∈ [3.62, 4)) or runner 5 (a₅ ∈ [3.62, 4.35]) covering t*=69/275 forces some slot uncovered.
2. **ERR-B-02 Runner 5 at k=3 (OPEN):** At a₅ ∈ [4.3, 4.5], runner 5 covers I₉ via B_{5,3} and t* in I₂ via B_{5,0}. Need: check whether runner 5 at this speed leaves some other slot (I₂ left edge, I₃, I₅?) uncovered.
3. **ERR-C-01 small-L case (OPEN):** For L < n(n-1), the shifted witness ĥ = b*-1 may not be in J. Need: either analytic argument for L ∈ {2n,...,(n-2)n} or harness confirmation.
4. **ERR-C-02 small-e_u case (DEEP ANALYSIS DONE 2026-04-24):** Full analysis in `lrc_c_err_repair_v1.md` §2.5 Addendum. Key findings:
   - Large-$e_u$ claim VACUOUS ($e_u \leq n-1 < 2(n-2)$ for all composite $n \geq 4$).
   - Key Lemma condition INVERTED in repair doc (should be $e_u \mid qm$ not $e_u \nmid qm$; the correct σ formula is $(\alpha q+\rho)m \bmod e_u$ with $\alpha=n\bmod e_u$).
   - CORRECT blocking condition (physical): $m$ bad for runner $e'$ iff $e_u \mid e'm$. Runners with $e_u \nmid e'm$ are automatically in good zone $[1/n,(n-1)/n]$ (proved and verified).
   - Bad-$m$ count per runner: exactly $\gcd(e',e_u)-1$ for non-$e_u$-multiples, $e_u-2$ for $e_u$-multiples.
   - OBSTRUCTION: $e_{\rm obs} = (n-1)e_u$ is always a realizable unit obstruction runner (all m blocked). Pacemaker-switch fails for $n \in \{4,6\}$ (only one viable pacemaker).
   - **PATH R1 CLOSED (negatively, 2026-04-24):** Domain of Theorem 9.2c does NOT exclude $e_{\rm obs}$. $e_{\rm obs}$ has residue $u$ (a unit, must be present in Unit-Complete regime). Actual CG2 gives $\sigma_{e_u}(e_{\rm obs},m) = 0 \equiv 0 \pmod{n}$ for ALL $m$ — covers $r_{\rm dep}$ at every targeted event. Representative-form uniqueness argument is incorrect for actual speeds. Full analysis in lrc_c_err_repair_v1.md §H.
   - **PATH FORWARD: Path R3** — restructure via (a) Corollary 11.0 (Unit Sub-System Overdetermination), (b) alternate pacemaker for $e_{\rm obs}$ case, or (c) apply Theorem 9.2c to the OTHER dropped non-unit $d'$ (whose pacemaker $e_{u'}$ may avoid $e_{\rm obs}$ obstruction).
   - Script: `lrc_c02_small_eu_check.py`.
5. **Cascade-completeness audit:** `lrc_n11_universalincompat_v3.md` — do Chain A/B/PSM fully enumerate candidates? Deferred until ERR-B-01/02 closed.
6. **Deferred:** LaTeX conversion, arXiv prep — blocked until Tier 1 rebuild lands.

**Authoritative review doc:** `lrc_whole_project_review_2026-04-18.md` — error catalog, salvage map, cross-version fingerprint table.

## Completed This Session (Session n=all resumption, 2026-03-31)
- **Option A completed:** `lrc_nall_prime_template_v1.md` — general prime-p proof template (~600 lines)
  - §1 Theorem CP (PROVED): complementary pairs for prime p, slot I_{p-2} unclaimed
  - §2 Lemma CPL (PROVED): coupling principle — all bad intervals scale as 1/a_j
  - §3 Feasible Fillers: all runners j ∈ {2,...,p-2} weakly feasible via k=j-1
  - §4 PSM-j / Chain-j lemmas (structural)
  - §5 Theorem INC: A_2(p) = (p-1)/(p·L_in(p)), B_2(p) = (2p+1)/(p·R_out(p)); general symbolic proof OPEN
  - §6 Theorem PU (PROVED): phase-uniform propagation — direct lift from n=11
  - §7 Theorem UB: universal blocking — conditional on INC
- **Option B completed:** `lrc_nall_option_b_v1.md` — gap analysis + v7.9 text blocks
  - All 4 bridge-document gaps resolved: G4B-COMP-CAP CLOSED, S3-GENERAL CLOSED, MULTI-DIV CLOSED, COMPOSITE-N NOT NEEDED
- **v7.9 produced:** 4 insertions into v7.7:
  1. Lemma 2.1 (Coupling Principle) — §2.1
  2. §2.5 Proof Architecture: Three Mechanisms — after §2.4
  3. Corollary 5.4 (Complementary Pairs) — after Corollary 5.3
  4. Corollary 11.0 (Unit Sub-System Overdetermination) — before Sub-case B1 in §11
- **n=11 paper:** FROZEN at v30, preprinted Zenodo 2026-03-27. Do not modify.

## Completed This Session (n=all INC proof, 2026-03-31 cont.)
- **Theorem INC PROVED** for all prime p ≥ 11 (and not needed for p ≤ 7):
  - Outer runner j₀ = p-2 at I₁-closing speed a* = (p-1)²/(p+1)
  - **L_in(p) = (p-2)/(2p)** — left edge of inner slot I_{(p-3)/2}; proved algebraically
  - **R_out(p) = (p²-3p-1)(p+1)/(p(p-1)²)** — outer runner starts coverage in I_{p-2} at k* = p-4
  - **A₂(p) = 2(p-1)/(p-2), B₂(p) = (2p+1)(p-1)²/((p²-3p-1)(p+1))**
  - Gap = (p-1)(p²-9p-4)/((p-2)(p²-3p-1)(p+1)); polynomial p²-9p-4 ≥ 18 for p ≥ 11
  - Polynomial identity verified by Qwen: 2(p²-3p-1)(p+1) - (2p+1)(p-1)(p-2) = p²-9p-4 ✓
  - Verified: p=11 gap = 5/261 ✓; p=13 gap = 96/3311 ✓
- **Template updated:** `lrc_nall_prime_template_v1.md` §5 now shows PROVED; §9 ledger updated
- **Theorem UB (§7):** Now unconditional (INC fully proved)

## Completed This Session (2026-03-31, cont.)
- **Template completion:** `lrc_nall_prime_template_v1.md` all sections upgraded:
  1. Lemma SRC: proof-by-contrapositive (AP-witness displacement argument, upper + lower bound)
  2. §3 Feasible Fillers: strong/weak distinction resolved; p=13 spot-check corrected (slot formula was wrong: $ps+1$ not $s(p-1)+1$) and full table computed
  3. Lemma PSM-j (§4.1): explicit GF lower bound + baton-pass $t^* = (2p+1)(p+1)/(p(p-1)^2)$; "subsumed by Theorem INC" note added
  4. Lemma CHAIN-j (§4.2): 2-step cascade formula derived; Chain A/B explicit; "subsumed by Theorem INC" note added
  5. INC-CRIT (§5.1) sub-case (a): t* formula fixed to $(2p+1)(p+1)/(p(p-1)^2)$ with n=11 verification
  6. §9 Status Ledger: all items upgraded to PROVED/COMPLETE
- **p=13 feasibility check (Python):** All runners j=2,...,11 weakly feasible; only runner 2 strongly feasible ($a_2 \leq 24/11$). Confirms $F_p^{\rm strong} = \{2\}$ for all $p \geq 11$.

## Next Tasks (n=all — v7.9)
1. **arXiv prep for v7.9:** Fill SHA-256 hashes + repo URL in Data Availability section (user action)
2. **LaTeX conversion:** latex-document-skill → .tex for arXiv submission
3. **Template integration (optional):** Consider whether to integrate the AP-framework template as a new §2.6 in v7.9, or publish as a standalone companion note.

## Completed This Session (Session 21, 2026-03-14)
- v7.5 produced from v7.4 (13 surgical fixes from external review triage):
  1. Abstract: proprietary terms → plain English (Coverage Gate, Sole Cover bijection, floor-reset, B_div removed from abstract)
  2. §1.4: unit-pairing identity scope corrected (bijection uses inversion map, not sum identity)
  3. §2.3: "Coverage Transport Capacity Theorem" → "Coverage Insufficiency Principle (Proof Schema)"
  4. §2.3: "Proof by failure mode" → "Proof outline — each mode is established in the indicated section"
  5. §2.4 table: §11 Unit-Complete row updated to explicitly name Theorem 9.2c for Sub-cases B1–B3
  6. §3 Step 3: Product factorization S=∏Sₗ explained via class partition structure; Weyl cited for equidistribution
  7. §3 Step 4'/Steps 4a–4b: relabeled sub-steps with bold headings
  8. §8.3: 2-sentence proof expanded to 5 sentences (fibre count, transparency verification, counting bridge)
  9. §9.3b: chamber width proved via transition point formula distance ≥ L/(e·e_u) ≥ L/(n(n-1))
  10. §9.3b: 63 constant justified (product of pairwise gcd bounds: 3·7·3 from differences 1,2,3,4,6,7)
  11. §9.3f: same chamber width proof added; Chebyshev lcm(1,...,m)≥2^{m-1} cited for LCM bound
  12. §11 Sub-case B1 n=2^k: bare parity argument replaced by Theorem 9.2c citation; parity kept as remark
  13. Appendix A.4/A.5: pseudocode schemas + companion file references added
  - Fix 4B (§9.0 non-unit coverage claim) intentionally skipped: claim is mathematically incorrect in general
    (e.g., n=6, runner e=3 with gcd(3,6)=3 has H_3={0,2,4} at floor 0, covering p_min=2)
- Rejected critiques (investigated and confirmed invalid):
  - Gemini "Speed Reduction Fallacy": §1.2 never replaces eᵢ with eᵢ mod n
  - DeepSeek "Category error": CG derivation applies to all runners, not just units (DeepSeek self-corrected)
- Qwen prescreen flagged both §3 and §8.3 passages correctly; Qwen verify: accepted on §3 Weyl, rejected
  on chamber width (Qwen's INCONSISTENT was itself incorrect after re-evaluation of the algebra)

## Completed This Session (Session 22, 2026-03-14)
- v7.6 produced from v7.5 (3 surgical fixes from second-round AI reviews Kimi/Gemini/ChatGPT):
  Fix A (§3 Step 3): Q-independence uniqueness justification added (why q_{ji}=0 for i≠i_ℓ, making S=∏Sₗ factorization explicit). Qwen: CONSISTENT.
  Fix B (§8.3 Theorem 8.3): (1) L≥2n(n-1) corrected to L≥n(n-1) with gcd derivation shown (lcm(2n,n-1)=n(n-1) for prime n via gcd(2,n-1)=2); (2) non-exceptional fibres explicitly inherit all Theorem 8.2 hypotheses; (3) Proposition 10.4→10.5. Qwen flagged INCONSISTENT (misread three-way lcm); REJECTED — algebra confirmed correct with added parenthetical.
  Fix C (§9.3f): New Lemma 9.3f-LCM inserted with p-adic valuation proof: lcm(T)=lcm(1,...,n-1)/p^{k-1} exactly (exact formula, not estimate). Bound corrected: 2^{n-1}/p^{k-1}→2^{n-2}/p^{k-1}. Parenthetical compressed derivation replaced by lemma citation. Qwen: CONSISTENT.
- Diff: exactly 3 targeted changes (lines 129, 242, 391–400 in v7.5 numbering).

## Pipeline Results (Session 22, 2026-03-14) — COMPLETE
**matsengrp sweep (v7.6):** ✓ Both agents done. Reports in `reports/matsengrp/`.
**ScholarEval (v7.6):** ✓ 3.875/5 overall (7.75/10). 6/8 dimensions pass.
  - PASS: D1 Problem Formulation 5/5; D2 Literature 4/5; D3 Methodology 4/5; D5 Analysis 4/5; D6 Results 4/5; D7 Writing 4/5
  - FAIL: D4 Data 3/5 (no code-availability statement; Appendix A.1 gap n=13–20); D8 Citations 3/5 (Kuipers-Niederreiter missing from bibliography; Tao 2018 uncited; MSC codes absent)
  - Verdict: **Near-ready (minor fixes)**. Report in `reports/scholareval/`.

## Completed This Session (Session 23, 2026-03-14) — v7.7 from v7.6
8 pre-arXiv fixes applied:
  Fix 1: Header — v7.7, MSC 2020 codes (11B75, 11K60), Keywords added
  Fix 2: Abstract trimmed to 149 words; undefined jargon removed (Sole Cover bijection, Dropped-Runner Targeting, Unit-Complete, CG1/CG2 removed from abstract)
  Fix 3: Tao (2018) cited inline in §1.1 after Czerwiński sentence
  Fix 4: Hardy–Wright (2008) + Kuipers–Niederreiter (1974) added to bibliography; Hardy–Wright cited inline in Lemma 9.3f-LCM (Theorem 414)
  Fix 5: Proof sketches added for Lemma 9.3d (Dangerous-Fibre Count) and Lemma 9.3e (Unit Bijection at Dangerous Floors) — both verified by Qwen
  Fix 6: Appendix A.1 — explanatory note added for missing prime n values (analytically handled by §6) and composite n (subsumed by §11)
  Fix 7: Data and Code Availability section added (SHA-256 placeholders; user fills repo URL before arXiv upload)
  Fix 8: Unit-Complete forward reference "(defined formally in §9.4)" added at first use in §5.2

## Route 3 Work — Session 2026-03-22 (n=11 AP Paper)

**Current focus:** Route 3 Step 4 — prove min GF > 0 analytically for commensurable CB configs.

**Files produced this session (UPDATED end-of-session 2026-03-22):**
- `lrc_n11_route3_framework_v1.md` — CB open, S_M compact, GF Lipschitz (PROVED)
- `lrc_n11_route3_lower_bound_v1.md` — Runner-10 slot structure, sign incompatibility (PARTIAL)
- `lrc_n11_sign_structure_v1.md` — Complementary pairs theorem, sign constraints (PROVED)
- `lrc_n11_gap_map_v1.md` — 9×10 blocking matrix, 256 sign patterns (PROVED)
- `lrc_n11_tightest_escape_v1.md` — Empirical floor: min GF = **0.12%** (updated; was 0.84%)
- `lrc_n11_closing_conditions_v1.md` — Full closing conditions table + §7 whack-a-mole + §8 enum v2 results + **§9 middle-gap analysis** (NEW 2026-03-22)
- `lrc_n11_blocking_enum_v2.py` — 256-pattern enumeration script (NEW 2026-03-22)
- `reports/lrc_n11_blocking_enum_v2_results.json` — Full enumeration results

**Key results (Session 2026-03-22 — COMPLETE):**
- All 247 feasible sign patterns have GF > 0 (9 infeasible patterns found)
- Global min GF: 0.12% (++------ pattern, deep NM 500k grid)
- Extremal config: a₁≈0.9999, a₆≈5.730, a₉≈8.297; good region = two tiny edge-gaps in I₁ (width ≈5×10⁻⁴ each)
- **Proposition 9.1 (NEW PROOF):** No single runner can cover the full middle gap [36/275, 7/44] of I₁ when edges are closed. Proof: requires a_j ≥ 125/18 AND a_j ≤ 48/7 simultaneously; 125/18 − 48/7 = 11/126 > 0. ∎
- Closing I₁ (a₉ ≥ 25/3, a₆ ≤ 40/7): GF(I₁) = 0 but GF(I₂) ≥ 1.33%. Whack-a-mole confirmed.
- Case analysis for ++------: Case A (a₉ < 25/3) and Case B (a₆ > 40/7) give GF(I₁) > 0 directly; Case C (both edges closed) reduces to proving GF(I₂) > 0.

## Baton-Pass Mechanism (Session 2026-03-22 — NEW KEY FINDING)
- **File:** `lrc_n11_baton_pass_v1.md` — full documentation (§1 general principle, §2 Case C explicit, §3 Case D, §4 nested case table, §5 framework connection)
- **Core idea:** Good windows in each slot are bounded by consecutive runner boundary crossings. The "baton" passes from the exiting-bad runner to the entering-bad runner. Between them, all runners are safe → explicit loneliness time.
- **Key result (Case C₁):** With a₉=25/3, a₆=40/7, a₅=100/23 fixed (I₁ closed), runners 5 and 9 simultaneously have position 1/11 at $t^* = 69/275$ (verified exactly by Fraction arithmetic). Good window in I₂ = [69/275, 10/(11·a₃)], positive iff a₃ < 2750/759 ≈ 3.6233.
- **Case D (a₃ ≥ 2750/759):** Runner 3 covers I₂ fully; good window shifts to I₃ (left-gap from runner 6 at a₆=40/7, width ≥ 1/40 ≈ 2.5% of I₃).
- **Nested case structure (++------ class):** Cases A, B → edge gaps in I₁; Case C₁ → baton-pass at t*=69/275 in I₂; Case D → I₃ left gap. Cascade terminates ≤ I₆ (overdetermination argument: 8 runners, 9 slots).

## Structural Mechanism (Session 2026-03-23 — NEW)
- **File:** `lrc_n11_structural_mechanism_v1.md` — unified proof architecture
- **Core insight:** All cases are manifestations of ONE principle — the **Coupling Principle**: tuning a_j moves ALL of runner j's bad intervals simultaneously (they scale as 1/a_j). Cases arise because each runner controls multiple slots at once.
- **Mod-11 structure:** Runner j's primary slot = I_{j⁻¹ mod 11 − 1} (natural blocking witness). Secondary slots via periodic chain. Bijectivity of ×j mod 11 (11 prime) determines the entire coverage graph.
- **Overdetermination Theorem (proposed):** 8 runner speeds, ≥9 independent slot-closing constraints → system has no joint solution within blocking intervals → at least one slot always has GF > 0.
- **Distance-to-resonance bound:** GF(I_{m−1}) ≥ c × min_j ρ_{j,m} where ρ_{j,m} = distance from a_j to nearest resonance speed. The min forced ρ > 0 by overdetermination → explicit GF lower bound.
- **Unified proof architecture replaces nested cases:** (1) characterize all resonance speeds R_{j,m}; (2) show blocking conditions force at least one runner off-resonance; (3) compute min forced distance → GF lower bound.

## Complementary Pairs Structure (Session 2026-03-23 — DECISIVE RESULT)
- **File:** `lrc_n11_structural_mechanism_v1.md` §9 — full algebraic structure
- **Key result:** 8 runners form 4 complementary pairs by mod-11 bijection, each owning 2 slots. Pair (5,6)→I₁,I₈; (3,8)→I₃,I₆; (4,7)→I₂,I₇; (2,9)→I₄,I₅. **I₉ has no primary owner** (unclaimed).
- **Sign conflict:** In ++------, pairs (2,9) and (3,8) both approach the SAME witnesses from opposite sides — creating the lowest-GF structure.
- **Forced gaps when I₁ closed (a₉=25/3, a₆=40/7):** Runner 9 skips I₆ entirely; runner 6 skips I₂,I₄,I₇,I₉. Forced I₆ gap = [168/275, 301/440] width 161/2200 ≈ 7.3%. Requires ≥2 free runners to cover.
- **Counting overdetermination:** After locking runners 9,6 for I₁ and using 4 free runners for I₃+I₆ gaps → only 2 runners left for 6 remaining slots. IMPOSSIBLE.
- **Proof architecture:** (1) a₉<25/3 or a₆>40/7 → I₁ edge gap; (2) both locked → I₃+I₆ forced gaps → counting shows 6 remaining slots need ≥6 runners but only 2 available; (3) continuity extends to near-closing values.

## Route 3 Paper Update (Session 2026-03-23 — UPDATED)
- **`lrc_n11_algebraic_lemma_v1.md`** — v1 updated: Main Claim 5.1 now **PROVED** (exact bounds in §5; cross-refs to incompatibility file).
- **`lrc_n11_incompatibility_v1.md`** — **NEW (2026-03-23).** Complete proof of Runner 2 Incompatibility. Key lemmas: Lemma 3.1 (I₄ forces a₂ ≥ 20/9), Lemma 3.2 (I₉ forces a₂ ≤ 575/261), Theorem 4.1 (incompatible: gap = 5/261 > 0). Exclusivity arguments for runners 3, 5, 7. Corollary 5.1: GF > 0 unconditionally for ++------ class.
- **`lrc_n11_ap_paper_v10.md`** — (2026-03-23). Paper updated to v10. §10.16.5 replaced with proved Theorem 10.16.5 (Runner 2 Incompatibility) with exact rational bounds. Status table updated: Route 3 = PROVED for ++------ class.
- **`lrc_n11_ap_paper_v11.md`** — **NEW (2026-03-23).** Dependency table corrected: all Route 3 rows updated from "Open/pending" to "Proved" throughout. Cases A–D all marked complete. Version header updated to v11.

## Case R> Containment Work — Session 2026-03-23 (Path A)

**Goal:** Prove Containment (C) for all Case R> configs → ILE terminates → LRC for Case R>.

**File:** `reports/investigations/INV-CASE-R-EXT-001/containment_proof_v1.md` (UPDATED 2026-03-23)

**New proved results (2026-03-23):**

1. **Lemma LBS (§7.8):** Left re-entry times ≥ 9/10 have approach windows ≥ 9/10. Equivalently: the ILE cannot first cross 9/10 via a left-blocking advance. Proof: 110k ≥ 99p−10 with gcd(99,110)=11 forces 110k ≥ 99p, i.e., k/p ≥ 9/10.

2. **Corollary LBS-C:** First entry of ILE into [9/10, W_hi) must be via right-blocking.

3. **Proposition RBC (§7.9):** Exact classification — runners p=10m (m=2,...,10) are the ONLY runners that can right-block from t<9/10 into D_11=(109/121,10/11). Each has approach window A_m=((99m-1)/(110m), 9/10) of width 1/(110m). Runners p≥209 (not mult of 10): impossible (modular condition fails). Proved via: condition (1199p-1452)/1331 < k ≤ (99p-101)/110 is satisfiable iff p<209 AND p≡0 (mod 10) via gcd(99,110)=11.

4. **Lemma GR (§7.11):** "Guardian runner" p_g=110m preempts runner 10m in A_m when present. τ(110m) = (1089m+1)/(1210m) < τ(10m) = (99m+1)/(110m) and τ(110m) < D_11_left. Safe landing.

5. **Lemma LBS2 (§7.12):** ANY left-blocking advance from A_m by a non-mult-10 runner p'' has τ < D_11_left = 109/121. Proof: τ ≤ (99p''−11r+10)/(110p'') < 109/121 for r = 9p'' mod 10 ≥ 1. Key: 11p'' + 1331r − 1210 > 0 for r ≥ 1, p'' ≥ 1.

**Consequence of LBS2:** D_11 is reachable ONLY when ALL non-mult-10 runners are isolated at t ∈ A_m. Specifically: if any non-mult-10 runner is left-blocking at t ∈ A_m, it preempts the dangerous right-blocking runner (τ < D_11_left < τ(10m)).

**Remaining open residual (minimal form):**
Prove: the ILE cannot be at t ∈ A_m with every non-mult-10 runner isolated and runner 10m right-blocking.
- Config-dependent; specific test case {1,2,3,4,5,6,11,20,220,300} shows ILE finds witness t*=2872/3300 ≈ 0.870 before A_2 is reached.
- Hypothesis: the ILE always finds a witness in [W_lo, D_11_left) before any approach window A_m is reached with only right-blocking runners present.

## Next Tasks (Route 3 — remaining)
1. **Case C₁ all-runner verification**: At $t \in (69/275, 10/(11a_3))$, confirm runners 2, 4, 5, 7, 8 are simultaneously isolated. Needed for Theorem 10.16.4 to give a complete loneliness certificate (not just baton-pass moment).
2. **Generalise to all 247 sign classes**: Each sign class has a different "conflict witness pair" and different unclaimed slot. Identify the analogous incompatibility for each class.
3. **Case D verification**: Confirm the forced gap $G_3$ in I₃ cannot be covered by runners 2, 4, 5, 7, 8 (needed to fully close Case D of Theorem 10.16.6).
4. **Path A (Containment):** Close the final residual — prove ILE always finds witness before A_m states with all non-mult-10 runners isolated. See session_state §Case R> notes above.

## Next Tasks (v7.8 / arXiv — on hold pending Route 3)
1. Fill SHA-256 hashes in Data Availability section (user action)
2. Add repository URL to Data Availability section (user action)
3. Re-run adversarial review on v7.7 targeting ≥90 score
4. LaTeX conversion via latex-document-skill → .tex for arXiv
5. arXiv upload (manual step — after above complete)

## Current Open Work (Session 19 — STALE, preserved for reference)
1. **Lemma 8.2a update** — PENDING (remove "unit" qualifier, cite lrc_8_2c_nonunit_closure_2026-03-12.md)
2. **Incorporate small-case closure into v6.3** — PENDING (cite lrc_small_cases_analytic_closure_2026-03-13.md)
3. **Lemma CD-n** — OPEN (prove Coverage Deficiency for n∈{6,8,9,10,12})
4. **Prop 9.4 small prime direct analysis** — OPEN (n=5, n=7 Route B case analysis)
5. **PP-T2 Step 4 fix** — OPEN (n=27 case, D'≤0.91 ≠ D'<1/2)
6. **GG2 / PL-KINDEP** — OPEN (Tier 2, work with other agent)
7. **Cycle 005 pipeline** — PENDING

## Completed This Session (Session 19, 2026-03-13)
- B3b Step 4 "small L" escape: CLOSED analytically
  - Lemma B3b-LB: L ≥ 2e_min always (E_fix contains largest power-of-2 ≤ n-1; contradiction if L=e_min)
  - Interval (L/e_min, 2L/e_min) always non-empty → Appendix A.3 demoted to empirical support
- Prop 10.3 Route A: sharpened to exact threshold M ≥ (n-1)φ(n) (vs. old M ≥ (n-1)(φ(n)+1))
  - Lemma SC-EXACT: |I_d ∩ ℤ| = ⌊M/(n-1)⌋ or ⌊M/(n-1)⌋+1, exactly
- Prop 10.3 Route B, n=4: CLOSED via Coverage Deficiency Lemma CD-4
  - Unit bad-sets always miss {1,3} coset, non-unit bad-sets are even-spacing pairs → ∪bad ≠ ℤ₄
- Prop 9.4 Route B analysis: confirmed only n∈{5,7} likely have genuine Route B cases
- Files: `lrc_small_cases_analytic_closure_2026-03-13.md`

## Next 3 Concrete Tasks
1. Prove Lemma CD-n for n=6 (Coverage Deficiency for composite n=6 dropped-unit case)
2. Verify Prop 9.4 Route B is empty for n∈{11,...,29} (confirm L₀ ≥ M₀ threshold analytically)
3. Incorporate B3b-LB + SC-EXACT + CD-4 into v6.3 (targeted edits to §10.2 and §9.5)

## Active Blockers
- Cycle 005: per-config data needed for 000058/000065 before re-queue

## Session Discipline (MANDATORY)
- Start: read this file + 1 target section only (50–80 lines)
- Work: all output to files, never paste proofs inline
- End: update this file with what changed and next tasks
- CRITICAL: responses must stay under token limit — write to files, do NOT paste proofs inline
