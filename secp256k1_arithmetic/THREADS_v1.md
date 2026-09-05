# secp256k1 arithmetic — thread map v1 (2026-07-11)

What the five results expose, thread by thread. Grounding probes:
`thread_probes_v1.py` (P1–P4) and `thread_probes_v2.py` (class-function census),
both run 2026-07-11. Status tags: **[probed ✓]** = today's computation,
**[open]** = defined but not yet executed, **[lit]** = source reading required
before any claim of novelty.

---

## A. The Hecke character is ONE sextic symbol  [DERIVED ✓ 2026-07-11]

**DERIVED, not fit** (`thread_A_reciprocity_v2.py`). The character
`χ(π) = −(4k/π)₆⁻¹` (k=7 ⇒ `−(28/π)₆⁻¹`) follows from the Jacobi-sum
Grössencharacter + sextic reciprocity — the classical Ireland–Rosen ch.18 /
Weil 1949 construction, reconstructed independently and machine-verified link
by link over split primes < 3000:
- **`a_p(k) = −Tr(χ̄₆(k)·A)`**, `A = Σ_s λ(1+s)ρ(s)` the Jacobi sum, `N(A)=p`:
  the classical point-count identity `a_p = −Σ_x λ(x³+k)` reduced via
  `#{x:x³=t}=1+ρ+ρ²`. **1442/1442** (6 twists + k=7), `N(A)=p` 206/206.
- **Canonical form `a_p(k) = Tr(−(4k/π)₆⁻¹·π)`** for all seven twists,
  primitive-root-independent — **1442/1442**. The `4=2²` is the 2-supplement
  (the `(2²)` part of the Hecke conductor); `k` is the curve constant; the `−`
  and inverse exponent are the ψ-normalization.
- Assembled `χ(π)=−(28/π)₆⁻¹` reproduces `a_p(7)`: 206/206.

So the point-count → Jacobi-sum → primary-π → sextic-symbol chain is exact; the
earlier "found by search" symbol is now the endpoint of a derivation. The family
form `−(4k/π)₆⁻¹` also grounds thread B's per-b symbol (was empirical, now
derived). **Done-check MET.**

### (superseded) original empirical finding
**Found (P1).** For primary `π` (π ≡ 2 mod 3-pattern), the ψ-normalized
Frobenius unit is

```
ψ(𝔭) = u·π,   u = −(28/π)₆^{−1}
```

- exhaustive search over `(c, e, u₀, conj)`: the ONLY surviving formulas on 147
  split primes < 2000 are the two equivalent forms `(28, e=1, −1, conj)` /
  `(28, e=5, −1, plain)`; re-validated on 182 more primes to 5000;
- **class-constant mod 28 on primaries** (432 classes = |Cl_𝔣|, 0 violations
  over ~20,000 split primes < 5·10⁵) — an empirical reciprocity statement;
- at the 256-bit `p`: gives unit 1, i.e. trace `t` (capstone reproduced);
- at `n` on the ideal `(1−π_p)`: gives exactly the alignment unit — **the
  amicability of (p, n) is now a single symbol evaluation.**

**Consequence.** Study v1 §3's relayed claim "χ is NOT a single rational sextic
symbol" is **withdrawn**: round 18 tested `(28/π)₆` but not `−(28/π)₆^{−1}`.
The round-20 local product `χ₄·(π/π₇)₆⁵(π/π̄₇)₆⁵` and the single symbol must be
equal — the χ₄ factor is the sextic-reciprocity supplement.

**Remaining pulls.**
1. [lit] Ireland–Rosen ch. 18 / Weil "Jacobi sums as Grössencharaktere": the
   classical trace formula for `y²=x³+D` uses `(4D/π)₆`; ours is `−(28/π)₆^{−1}`
   with 28 = 4·7. Reconcile sign/inverse conventions — expected outcome: our
   formula IS the textbook one, closing the loop point-counts → classical.
2. [open] Prove the equality single-symbol = local-product via sextic
   reciprocity (finite check on generators of (ℤ[ω]/84)^*; machinery in hand).
3. [open] Compute χ_b for b = 1..6 the same way (expect `−(4b/π)₆^{−1}`);
   gives the full sextic-twist family and feeds thread B's per-b constants.

**Done-check:** a derivation (not just table match) of u = −(28/π)₆^{−1} from
cubic/sextic reciprocity + the classical formula, verified by the existing
329-prime table.

---

## B. Amicable density for j=0  [SETTLED ✓ 2026-07-11 — matches S–S Conj 40]

**Resolution (source read: arXiv:0912.1831, Conjectures 40 + 27).** Our closure
probability **is** the Silverman–Stange conjectural value — 13/50 is *their*
number for k=7, not ours. Their **Conjecture 40**: `N_k^[1](X)/N_k(X) → 1/3 +
R(k)` with `R(k)` by `k mod 36`; **Conjecture 27**: amicable pairs
`Q_k ~ ¼ N_k^[1]`. Our `ρ_k = P(close | #E_ℓ prime) = 2Q_k/N_k = (1/2)(1/3 +
R(k))`. For k=7 (case (d), split): `R(7)=2·7/(3(7−2)²)=14/75`, so
`ρ_7=(1/2)(1/3+14/75)=13/50` ✓. Their intro eq (1) `1/6+1/(3(k−3))` for k≡1,19
IS this ρ_k. **Verified EXACTLY** (`census_ss_v1.py`, mod-12k class census =
their rational) for all 12 classes mod 36: k=5,7,11,13,17,19,23,29,31,37 —
rational-equals-rational, zero discrepancy (large-k need X≥5·10⁶ for full class
coverage); direct enumeration (`test_ss_conjecture40_v1.py`) agrees within SE.
**Novelty demoted:** ρ_7=13/50 = an evaluation of S–S's published conjecture for
the k≡7 class they didn't print explicitly. Our part = (a) independent
reconstruction validating Conj 40 across all 12 classes, (b) the explicit
single-symbol Hecke character `χ=−(4k/π)₆⁻¹` driving it, (c) the 256-bit
secp256k1 instance. NOT a new theorem.

### (superseded) Original framing: "13/50, not 1/6"  [probed ✓]

**Found (P3 + v2 census).** Closure of the 2-cycle `ℓ → #E₇(𝔽_ℓ) → ℓ` is a
**residue-class function of the primary Frobenius mod 84**. Exact census: of
432 primary classes, 100 satisfy "both π and π−1 coprime to 84" (= 432 ·
(2/3)·(1/2)·(25/36), local factors at 2, 3, 7), and **26 close: probability
13/50 = 0.26** (vs naive |μ₆|⁻¹ = 1/6 ≈ 0.167). Empirical: 461/1729 = 0.2666
at ℓ < 5·10⁵ (0.6 SE). The naive heuristic is off by +56%; the bias is carried
entirely by the conductor.

**The conjecture this sets up.** For E₇:

```
#{amicable pairs (ℓ, q), ℓ < X} ~ (13/50)·C_pair·X/(log X)²
```

where `C_pair` is the Hardy–Littlewood-type constant for "N(π) and N(π−1)
both prime" (Eisenstein twin-norm primes), with the mod-84 local factors
removed from C_pair to avoid double counting. Compare with the measured
`A(X) ≈ 0.10·X/(log X)²` (round 38).

**Remaining pulls.**
1. [lit — REQUIRED FIRST] Silverman–Stange 0912.1831: they treat j≠0 and
   remark on j=0 anomalies; check whether they or a follow-up (Parks,
   "aliquot cycles on average" line) already computed a j=0 constant. Our
   13/50 mechanism (Hecke-unit alignment as a conductor-class function) is
   the candidate contribution.
2. [open] Derive C_pair as an Euler product over ℤ[ω] primes; multiply out;
   check against 0.10 measured.
3. [probed ✓ 2026-07-11 `rho_b_investigate_v1.py`] Per-b prediction DONE. The
   symbol generalizes to `u_b(π) = −(4b/π)₆⁻¹` (0 mismatches, b=2,3,5,7, split
   ℓ<3000). Exact census: **ρ₂=1/2, ρ₇=13/50, ρ₃=18/101, ρ₅=1/10**. Ordering
   matches direct enumeration to X=20000 (b2=34 > b7=21 > b3=15 > b5=11) **4/4**,
   consistent with round-37. b=1 degenerate (2-torsion). The framework's
   falsifiable check PASSED. Still open: the b-dependent C_HL(b) that turns
   ordering into magnitudes.
4. [open] Length-3 cycles: closure now = two consecutive alignments; expected
   count = Σ (class-census probability)²-weighted twin-triple density — derive
   the explicit expectation and state where the first j=0 3-cycle should
   appear (bounded sweeps found none < 60k; quantify whether that's expected).

**Done-check:** predicted constant (13/50)·C_pair matches the measured A(X)
slope within Monte-Carlo error. [ρ_b ordering vs enumeration: DONE ✓]

---

## C. Supercongruences for 7^k·C(3k,k)  [ADVANCED ✓ 2026-07-11]

**Resolved to a clean characterization + an honest negative
(`thread_C_supercong_v2.py`).**
- **Three-term ASD `b_{ℓ²} − a_ℓ·b_ℓ + ℓ ≡ 0 (mod ℓ²)` holds for ALL 147 split
  ℓ < 2000** (strengthened from 10). This is the correct clean mod-ℓ² statement.
- **The mod-ℓ³ upgrade locus is exactly `{ℓ : a_ℓ ∈ {±1}}`** — on ℓ<2000 that
  is `{37 (a=−1), 61, 127, 397, 547 (a=1, the anomalous primes)}`. The ℓ²→ℓ³
  obstruction `ε_ℓ` vanishes iff the trace is `±1`; but `ε_ℓ/(a_ℓ²−1)` is not
  constant, so `(a²−1)` marks the locus without globally factoring ε (residual
  Gauss-sum content in the cofactor). Clean exact characterization; mechanism
  (why a=±1) not proven.
- **The scalar correction `δ_ℓ=(b_ℓ−a_ℓ)/ℓ` has NO elementary closed form**:
  `δ_ℓ = 0` never (0/147); not a Fermat-quotient combo (v1), not `a·H_{(ℓ−1)/6}`,
  not any `a·(x·H_{(ℓ−1)/6}+y·H_{(ℓ−1)/2})` with |x|,|y|≤6 (v2). It is
  irreducible Jacobi/Gauss-sum content — the "correction" the question asked
  for is captured by the three-term recursion, not a scalar formula.

### (superseded) earlier partial note
- Three-term ASD `b_{ℓ²} − a_ℓ·b_ℓ + ℓ ≡ 0 (mod ℓ²)` holds at all 10 split ℓ
  tested; **mod ℓ³ at ℓ = 37, 61 only** (sporadic upgrades).
- The naive `b_m ≡ a_m (mod m)` fails exactly when m has two coprime
  "norm components" (e.g. 91, 169, 325 = 5²·13) — the congruence is
  prime-power local (Honda), zero-propagated by inert/bad factors. The
  correct object is the three-term family, as for modular-form ASD.
- The mod-ℓ² correction `δ_ℓ = (b_ℓ − a_ℓ)/ℓ · a_ℓ^{−1}` is **not** any small
  rational combination of Fermat quotients q_ℓ(2), q_ℓ(3), q_ℓ(7) (exhaustive
  small-coefficient search failed) ⇒ it carries Bernoulli/Euler-number-type
  content (Lehmer's H_{⌊ℓ/6⌋} congruences have exactly such terms).

**Remaining pulls.**
1. [lit] Coster–van Hamme; Kibelbek–Long–Moss–Sheller–Yuan (1210.4489);
   Z.-W. Sun's supercongruence tables. The classical Jacobi-type congruence
   `C((ℓ−1)/2,(ℓ−1)/6)`-mod-ℓ² for 4ℓ = L²+27M² is the direct antecedent —
   our δ_ℓ data (13→8·a, 19→9·a, 31→16·a, 37→23·a, 43→31·a) should match one
   of their closed forms (candidates involve L, M, and E_{ℓ−3}-terms).
2. [open] Explain the ℓ³-upgrade set {37, 61, …}: extend the scan to ℓ < 2000,
   correlate with a_ℓ, L, M, and anomalous-prime data (61 is anomalous, a=1;
   37 is not — so anomaly alone is not the criterion).
3. [open] At p itself: `t ≡ 7^{(p−1)/6}·C((p−1)/2,(p−1)/6) (mod p)` is the
   Hasse invariant; the mod-p² refinement (unit-root form) is the 256-bit
   showcase statement once the closed form for δ is identified.

**Done-check:** a closed-form δ_ℓ verified on all split ℓ < 2000, with the
ℓ³-upgrade set explained as its vanishing locus.

---

## D. BSD reconciliation of L(1) = Ω  [RESOLVED ✓ 2026-07-11]

**Closed, no tension.** From-scratch `L(E,1) = 3.041417228428` (exact `a_n` to
n ≤ 4000, approximate functional equation; `test_claims_v1.py` T7) gives
`L(1)/Ω = 1.000000000`. `y² = x³ + 7` is a global minimal model
(`Δ = −2⁴·3³·7²`, all `v_ℓ(Δ) < 12`), so `dx/2y` is the Néron differential and
`Ω = 3.0414` is the BSD real period. BSD-rank-0 is a theorem here (CM,
Rubin/Kolyvagin) ⇒ `∏c_ℓ · #Ш / #tors² = 1`, and with trivial torsion **every
`c_ℓ = 1` and `#Ш = 1`** — all three bad fibres are Kodaira Type II. The v2
draft's `∏c ∈ {2,6}` was a mis-read: Kodaira type is not `(v(c₄),v(c₆),v(Δ))`
by inspection; Ogg/Tate with the wild parts at 2, 3 give Type II throughout.
The pasted-table value "Ω ≈ 6.0828" = `2Ω` = `∫|dx/y|` (wrong differential),
which would have faked `L(1)/Ω = 1/2`. **Lesson:** don't read Kodaira types off
valuations; `L(1)/Ω = 1` numerically is the reliable handle.

---

## E. Zeros of L(ψ, s) — computed & LMFDB-confirmed  [DONE ✓ 2026-07-11]

`thread_E_zeros_v1.py` (mpmath, 30 dps), L-function built from the EXACT CM
Hecke eigenvalues (theta series), conductor 21168, W=+1:
- **Functional equation `Λ(s)=W·Λ(2−s)` holds to 0.0** (30-digit residual).
- **L(1)=Ω=3.04141722843, L(1)/Ω=1.0** — matches LMFDB's
  `3.0414172284278810424268528156` to 28 digits (independent BSD re-confirm).
- **First 10 zeros computed**, each `|L(1+iγ)| ~ 10⁻²⁸..10⁻³¹`. First zero
  `γ₁ = 0.8173126364`; **LMFDB gives `0.8173126364220043` — 10-digit match.**
  γ = 0.8173, 1.3299, 2.4074, 3.2203, 3.7669, 4.4424, 5.2815, 5.9135, 6.3184,
  7.0824.
- **Mean gap 0.696 matches the conductor density `π/log(√N·γ̄/2π)=0.6915`** to
  <1% — correct zero density for a weight-2 conductor-21168 L-function.

So the survival-law/adelic section (§6) upgrades from "model" to **verified
instance**: the actual zeros exist, sit on Re(s)=1, are reproduced from CM ideal
counts alone, and agree with LMFDB. The μ₆/unit structure lives in the operator
model (§6), NOT in these zeros (they are a single primitive L's zeros); the
Connes global realization stays open (arXiv:2605.17645 boundary). **No overclaim:
computing zeros ≠ a spectral realization of them.**

**Remaining (optional):** full Weil explicit-formula identity (zero side vs
prime+archimedean side) for a chosen test function — the coarse
`Σ 1/(¼+γ²)=2.07` convergence sanity passed; the full identity needs the tail.

---

## F. ₃F₂ boundary and the non-torsion critical point  [probed ✓, garnish]

**Found (P4).** Radius: `T_c⁶ = 4/(27b)` exactly, from the T-chart ramification
at `x³ = 2b` (family fact, b-independent after scaling). Boundary value:

```
₃F₂(1/6,1/3,2/3; 1/2,7/6; 1) = (27/4)^{1/6} · ∫_{2^{1/3}}^∞ du/(2√(u³+1))
                             = (27/4)^{1/6}/6 · B(1/3; 1/6, 1/3)
```

(numerically 1.18796…, both sides agree). `L(T_c)/Ω = 0.205428…` is not a
small rational — the critical point `((2b)^{1/3}, √(3b))` is **not torsion**
(doubling sends x ↦ −x/2, exact). Worth one lemma in the study; not a thread.

---

## G. Iwasawa invariants along amicable pairs  [open, exploratory]

The pair structure `π_n = π_p − 1` links the split-ordinary Iwasawa settings
at p and at n. Not computable at 256 bits, but the SAME structure exists for
the small members of the family ((67,79) for b=7 — closure re-verified today).
Compute λ-invariants of E_b at both members of small amicable pairs (Rubin
case, Katz p-adic L) and look for a relation. No prediction; a defined
experiment.

---

## H. Parked / small

- **Landau constant for theta sparsity:** the newform support {n = norms} has
  density κ·X/√(log X); compute κ for ℚ(√−3) exactly (Landau–Ramanujan
  analogue) — one-paragraph addendum to the study.
- **3-cycle S-unit framing:** length-3 same-b cycles as unit-alignment chains
  (subsumed by B.4).
- **c-neighbor web:** the graph p → N(π_p − c) for |c| ≤ C generalizes
  amicability (c = 1); the closure analysis of B applies verbatim with
  `1 − π` replaced by `c − π`... defined, unexplored.
- **secp256k1 study v2:** fold A (symbol), B (13/50), C (three-term), F
  (radius) into `secp256k1_arithmetic_v2.md`; v1 stays frozen with the
  now-withdrawn §3 sub-claim noted in v2's changelog.

---

## Priority order  (updated 2026-07-11)

1. **B** (amicable constant) — the ρ_b machinery is built and passes 4/4;
   the ONLY remaining step is the S–S j=0 constant comparison. **Blocked on a
   source read** (WebFetch session-limited today): read arXiv:0912.1831 §j=0,
   extract their conjectural constant for y²=x³+b, compare to ρ_b·C_HL(b).
   This is the sole row that could be a genuine contribution vs a reconstruction.
2. **A** (symbol ↔ classical reciprocity) — `χ=−(28/π)₆⁻¹` in hand; reconcile
   with Ireland–Rosen ch.18 / Weil Jacobi-sum formula (also source-read).
3. **C** (supercongruence δ_ℓ) — data in hand; Coster–van Hamme / Z.-W. Sun.
4. ~~**D** (BSD)~~ — **RESOLVED** ✓ (L(1)/Ω=1, all c_ℓ=1, Ш=1).
5. **E** (zeros/explicit formula) — calibration; needs mpmath for zero-finding.
6. F/G/H as garnish or when blocked on the above.

**Note:** threads B.1 and A both need a literature fetch that hit today's
WebFetch/WebSearch session limit. Source-first discipline says read those
before claiming novelty — so the next actionable *computational* step without
a fetch is **C** (δ_ℓ closed-form hunt) or **E** (mpmath zeros).
