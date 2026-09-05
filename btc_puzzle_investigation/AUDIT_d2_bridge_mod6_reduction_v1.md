# AUDIT: Downloads "D2 Lang-torsor twist bridge" mod-6 keyspace reduction (P135/P140) — v1

**Date:** 2026-08-16
**Grade:** `[PROOF + EMPIRICAL — NULL, source ERRATA]`
**Object:** the six externally produced artifacts in `~/Downloads/`: `d2-bridge-exact-residues.md`, `d2-bridge-search-space-reduction.md`, `farey-coprimality-filament-p135.md`, `farey-coprimality-filament-p140.md`, `farey-coprimality-filament-sieve-p135.py`, `farey-coprimality-filament-sieve-p140.py`, `eisenstein-core-gate-real-keys.py` (citation numbering [506]–[625]: a later batch of the external-doc stream behind Part XVI of the master).
**Claimed:** standalone `d mod 6` extraction from public data on Puzzles 135/140 → keyspace ÷6 (log₂6 ≈ 2.585 bits), plus a "3-Point Semaev S₄ + Babai BDD" sub-microsecond recovery route.
**Closure scope:** exact identities are proofs; correlation claims closed as scoped NULL at N=8000 uniform keys in the actual keyspace `[2¹³⁴, 2¹³⁵)` on secp256k1 (T5 joint 12×6 table, min expected cell ≈ 111; the specific y-LSB law, if true, would give χ² ≈ 2000 — observed 0.39).
**Script:** `audit_d2_bridge_reduction_v1.py` (pure stdlib, seed 20260816, SHA-256 `de90634598a40c7e41399b8d0da1b14ee0e5780f058bdbb7920c8536d7d92dbf`).

---

## 0. Verdict

**Net key information extracted: 0 bits. Net keyspace/work reduction: none.**
The 2.585-bit claim decomposes into a mod-3 leg that is an identity in unknowns
(and as printed, arithmetically wrong), a mod-2 leg that is false, and a
"carry" bridge that equivocates between a public coordinate-side quantity and a
secret scalar-side one. The sandbox "verification" in the source is the
degenerate case d₀ = d, c = 0, i.e. it checks `d % 3 == d % 3`.

---

## 1. Layer A — arithmetic: verified (with two source errors found)

Everything computable was recomputed exactly (integer/Fraction signal path; floats
only for display):

- `p = a² − ab + b²`, `a + b·β₂ ≡ 0`, `(a−b) − b·β₁ ≡ 0 (mod p)`; β₂³ = 1, β₁ = β₂²; λ³ ≡ 1 (mod n); [λ]G = (β₂·x_G, y_G).
- P135/P140 on-curve; cubic exponents e(x₁₃₅) = 1, e(x₁₄₀) = 0; y-parity labels (s = 0, 1); y LSBs (0, 1) — all as claimed.
- Lifts: the claimed z-pairs are exact lifts and reproduce `s(P135) = 0.058932996993`, `s(P140) = 0.019792401440` to all printed digits (their P140 z is a **β₁-lift**; the report never says which root — s is root-independent by conjugation symmetry, verified exactly here for both puzzles).
- CF expansions of `|u_frac|` (first 15/20 terms) and the Egyptian signatures (e.g. 17/61 = [4, 35, 8540]) verified.
- "No fully-coprime unit square" — true, and provable in one line (the four corners realize all four parity classes; the (even, even) corner has gcd ≥ 2). It is a fact about ℤ², unrelated to keys.

**Two arithmetic errors in the source's bridge algebra** (both load-bearing for its printed residues):

1. **n ≡ 1 (mod 3), not 2.** Their P140 headline `d₁₄₀ ≡ −d₀ + 2 (mod 3)` uses n ≡ 2; the truth is d₁₄₀ = n − d₀ exactly (label j=0, s=1), so `d₁₄₀ ≡ −d₀ + 1 (mod 3)`. The printed residue class is wrong.
2. **λ ≡ 2 (mod 3), not 1.** Their stated law `d ≡ (−1)^s d₀ − c·n (mod 3)` folds λ^j → 1. The correct folding is `d ≡ (−1)^s·2^j·d₀ − c·n (mod 3)` (verified 240/240 on random keys). Their form fails on exactly the class {j = 1, d₀ ≢ 0 (mod 3)} — 48/240 = 20.0% of uniform keys (class frequency 2/9 ≈ 22%). So the printed congruence is not even a valid identity on a fifth of the keyspace. Their mock "verification" passed only because its c·n term was 0 and j = 0.

## 2. Layer B — the "Core Gate" (s < 3/16): true, public, and unremarkable

The ellipse {u² − uv + v² ≤ 3/16} is tangent to all four sides of the square
fundamental domain (s(½, ¼) = 3/16): the "core gate" is exactly the inscribed
ellipse. Hence for uniform X ∈ 𝔽_p:

$$\Pr[s < 3/16] = \frac{\pi\sqrt{3}}{8} = 0.680175 \quad (\text{empirical } 0.6795,\ M = 50{,}000),$$
$$F(s) = \frac{2\pi s}{\sqrt{3}} \ \text{ for } s \le 3/16 .$$

This sharpens `RESULT_linchpin_s_gate_v2.md`'s empirical 0.6831 to an exact
value. Consequences: a **uniform random key passes the gate 68.02% of the
time**; P135's s sits at the **21.4th percentile** and P140's at the **7.2nd**
of random keys. "Deep inside the core" is a percentile of a smooth public
distribution, not a property of the key. The gate's true content — eis(βX) =
ω·eis(X) with zero re-reduction when the lift is inside the inscribed ellipse —
is a statement about the public x alone (consistent with
`RESULT_linchpin_s_gate_v2.md` and the flap-vs-carry distinction in
`RESULT_eps_to_d_constraint_v2.md`: the public flap ε is not the scalar-side
carry).

## 3. Layer C — the information claims

**C1 (mod 3): identity in unknowns.** With the label (j, s) public
(χ₃ of x gives j = 2e mod 3 — extraction verified 240/240; y vs p/2 gives s)
and d₀ the canonical orbit representative, the corrected bridge is
`d ≡ (−1)^s 2^j d₀ − c·n (mod 3)` with `c = ⌊(−1)^s d₀ λ^j / n⌋` — an identity
(trivially true given d₀, c), containing two unknowns: d₀ mod 3 and c mod 3.
Knowing d₀ ⟺ knowing d (the label is public), so the identity reduces the
unknown to itself. For P140 it literally reads `d = n − d₀`.

**C2 (mod 2): false.** "y LSB = d mod 2" agrees on **49.65%** of N = 8000
uniform keys in [2¹³⁴, 2¹³⁵) (χ² = 0.39 on 1 dof — a coin flip). Explicit
counterexamples in the script output (e.g. d = 36163…48811 odd, y even). The
law is negation-consistent (p, n odd flip both sides), which is exactly why
their single mock sample could not refute it and why their "verification" of it
is worthless.

**C3 (their verification): tautology.** Replicated exactly: their mock key has
j = 0, s = 0, hence d₀ = d and c = 0; the printed "congruence check" is
`d % 3 == d % 3`, and the c·n = 0 term hid error (1) above.

**Empirical independence (the powered version of T2c(b)):** N = 8000 uniform in
the puzzle keyspace:

| table | χ² | dof | p |
|---|---|---|---|
| cubic character e(x) × d mod 3 | 2.57 | 4 | 0.37 |
| y LSB × d mod 2 (their law) | 0.39 | 1 | 0.47 |
| y vs p/2 × d mod 2 | 1.07 | 1 | 0.70 |
| core-gate membership × d mod 3 | 1.57 | 2 | 0.54 |
| composite label (j, s, y LSB) × d mod 6 | 47.46 | 55 | 0.25 |

All consistent with independence. This upgrades the under-powered T2c(b) null
of `RESULT_t2c_j_range_dmod3_v1.md` (V_detect ≈ 0.2 there; here the specific
y-LSB law is excluded by ~3 orders of magnitude in the statistic, and joint
effects of a few percent per cell are below the floor).

## 4. What is real in the batch, and what it is worth

- **Orbit labels (j, s) are genuine public invariants** (this was already the
  repo's position: POSITIVE_FINDINGS_MASTER Part XVI.C — they are the μ₃/±1
  orbit position, capped by log₂|Aut(E,[O])| = log₂ 6). They are worth
  **zero key bits**: only d itself satisfies [d]G = P (the other five orbit
  scalars generate the distinct conjugate pubkeys (β^k x, ±y)); each of the
  six determines the others by public multiplication λ^{±k} mod n, so any one
  is equivalent knowledge — while the label is a function of P alone,
  statistically independent of d mod 3/6 (§3 tables), with no exact public
  anchor (every congruence factors through the unknown d₀). *(Erratum
  2026-08-16, same session, pre-commit: this bullet originally justified
  zero bits by "all six orbit scalars are valid private keys for the same
  pubkey" — false as stated; corrected here.)*
- The classical √6 automorphism speedup applies to full-range Pollard rho, not
  to interval (kangaroo) search: the orbit scalars λ^j d mod n lie far outside
  [2¹³⁴, 2¹³⁵), destroying tame/wild window overlap. No GLV work-reduction is
  available to the puzzles — including the batch's own: even granting their
  false premise, dividing the *interval* by 6 divides kangaroo *work* by √6 =
  2.45 (2⁶⁷ → 2⁶⁵·⁷), not by 6 (their own "59% runtime cut" contradicts their
  "2⁶⁴·⁴" line).
- **Strategy C (Semaev S₃/S₄ + Babai BDD, "1 μs")**: no system exists — S₃ with
  two known x's constrains the third only under a key relation d₁₂₀ ± d₁₃₀ ±
  d₁₃₅ ≡ 0 (mod n) that has no reason to hold and doesn't; x(P₁₂₀ + P₁₃₀) is
  public and constrains nothing; Babai/GLV decomposes a *known* scalar (see
  `ANALYSIS_public_gate_glv_carry_circularity_v1.md` §4). Circular hand-off.
- **Farey/Egyptian/Dirichlet apparatus**: CFs of u_frac are the generic
  continued fraction of a uniform random rational (the highlighted large
  partial quotients — 92, 162, 8562266856 — are ordinary Gauss–Kuzmin noise);
  "Dirichlet island centers d_q = 2^(b−1)(1 ± 1/q)" have no basis in puzzle key
  generation (keys are uniform b-bit integers). Decorative.

## 5. Relation to the standing record

- `OPEN_d2_congruence_law_v1.md` (CLOSED NULL): same congruence law; this batch
  adds nothing — and its printed form carries the two erratas of §1.
- `ANALYSIS_public_gate_glv_carry_circularity_v1.md`: confirmed; λ ≡ 2 (mod 3)
  re-verified numerically here.
- `RESULT_t2c_j_range_dmod3_v1.md` correction banner (public-readout route
  "OPEN and under-tested"): now tested at power on the actual keyspace — scoped
  NULL (§3 table).
- `RESULT_linchpin_s_gate_v2.md`: Pr[s < 3/16] now exact (π√3/8); percentile
  quantification of P135/P140 added.
- `ARSENAL_d_shadow_and_range_tools_v1.md`: unchanged — the only non-circular
  thread remains the known-bit-range carry route, still quantitatively weak.

## 6. What is NOT closed

Absence of *any* cheap public function correlating with d mod 3/6 is a
heuristic (empirical null + the structural argument that all exact relations
factor through the unknown d₀), not a theorem — it is DLP-adjacent and cannot
be proven by sampling. Scope of this closure: the six named artifacts, their
specific mechanisms, and generic per-cell deviations of a few percent at
N = 8000.

## 7. Reproducibility

`python3 btc_puzzle_investigation/audit_d2_bridge_reduction_v1.py [N]`
(default N = 8000; seed 20260816; pure stdlib; ~2 min). Signal path integer/
Fraction-exact; floats only in display and the χ² statistic. SHA-256:
`0782d9b9cfdafc63b090c18768ee84f2a588dfc5e349e4878a194ecb15dfd60b`
(supersedes `de9063…92dbf`; change is the §4 erratum prose only — the
signal path is untouched).

## 8. Addendum (same-day, post-challenge re-read of the full batch)

The challenge "did you read the material properly?" surfaced two things.

**(a) Read gap, now closed.** The batch extends beyond the seven artifacts
named in the header. Additionally read 2026-08-16: `d2-lang-torsor-twist-bridge-v1.md`
(the source derivation, Aug 13), `d2-lang-torsor-puzzle-verification.md` (Aug 13),
`semaev-tautology-trap-verification.md` (Aug 13). Not read: `eisenstein-core-gate-verification.md`,
`eisenstein-core-gate-p135.md`, `l1-lemma-rhombus-verification.md`, `isotypic-trace-carry-reproduction.md`,
`joint-semaev-*` — their subject matter (the ε=0 core-gate mechanics and the
rhombus/inradius geometry) is exactly what §2 above verifies independently and
exactly, and what `RESULT_linchpin_s_gate_v2.md` / `RESULT_eps_to_d_constraint_v2.md`
already tested with controls. `verify_d2_residues.py` and the `/workspace/scratch/*.py`
files cited by the docs were never delivered to ~/Downloads — only their
printed logs exist.

**(b) The new files strengthen the NULL — the stream's own source concedes the
circularity.** Findings:

1. `d2-lang-torsor-puzzle-verification.md` §4 ("The 'Oracle Gap' & Tautology
   Audit") states verbatim that extracting d mod 3 from a single public point
   is blocked by an "unresolved circular dependency (Tautology Trap)": j needs
   the representative's coordinates, the congruence needs the carry c, and
   "both the orbit representative d₀ and the carry c are functions of the
   secret scalar d itself." This is precisely §3-C1 of this audit. The Aug-16
   batch re-asserts standalone extraction anyway; its only new element is
   "ε = 0 coerced by the Core Gate", i.e. the coordinate-side/scalar-side
   equivocation (the flap-vs-carry distinction the repo already falsified at
   tested scope in `RESULT_eps_to_d_constraint_v2.md`). No document in the
   stream derives c from ε.
2. The stream contradicts itself across versions. `twist-bridge-v1` states
   λ ≡ −1 (mod 3) — **correct** (λ ≡ 2, confirmed numerically here) — and
   writes the law with the (−1)^j fold; `puzzle-verification` §3 writes the
   fully correct form d ≡ (−1)^s (−1)^j d₀ − c (mod 3) (λ-fold and n ≡ 1 both
   right); the Aug-16 `d2-bridge-exact-residues.md` then drops the λ-fold and
   implicitly asserts n ≡ 2 — wrong on both counts (§1 above). The algebra
   degrades toward the conclusion. Also: β₁/β₂ *labels* for the same hex
   constants are inverted between the Aug-13 and Aug-16 documents.
3. The "BDD Oracle Escape (Case 2)" MI spike of 5.5732 bits
   (`semaev-tautology-trap-verification.md` §3) is circular by the document's
   own parenthetical: x([d₁+d₂]G) with d₂ known is "structurally identical to
   the target's public coordinate x₁" — one recovers [d₁]G = [d₁+d₂]G − [d₂]G
   from it. MI(x_shared; d₁) = H(x_shared) because the map is injective; the
   "information gain" equals the entropy of the public key, i.e. zero new
   bits. The Babai/CVP step that would convert this into key recovery has no
   lattice construction anywhere in the stream (a BDD target would require a
   small-coefficient linear relation among independent puzzle keys; none
   exists). Consistent with `ANALYSIS_public_gate_glv_carry_circularity_v1.md` §4.
4. New arithmetic verified exactly (this session): the P135 ± P140 sum and
   difference points and their cubic characters
   (x⁺ = 0xef305c91…, idx 1 under their convention; x⁻ = 0x5b330e4e…, idx 0)
   — all correct. Same class as everything else in the batch: public
   functions of public points, computable by anyone, zero bits about
   d₁₃₅ ± d₁₄₀ (mod n).

**(c) Erratum in this audit, corrected above (§4).** The original §4 bullet
justified zero bits via "all six orbit scalars are valid private keys for the
same pubkey" — false ([d']G = P forces d' = d on prime-order ⟨G⟩; the other
five generate distinct conjugate pubkeys). The zero-bit conclusion is
unchanged; its correct grounds are the independence tables (§3), the absence
of any exact public anchor, and — corroboration, not proof — the source
stream's own tautology concession (b1).

**Standing verdict (unchanged, now with the stream's own testimony):
net key information extracted 0 bits; net keyspace/work reduction none.**

## 9. Addendum 2: the "Dirichlet island" apparatus, closed (2026-08-16, same session)

The claim appears in three documents with three **inconsistent** "merge boundaries"
(√lo = 2^67 in farey-p135, 2^67.5 in farey-p140, 2^127.5 in d2-bridge) and the center
formula d_q = 2^(b−1) ± ⌊2^(b−1)/q⌋, asserting the keyspace "shatters into these
isolated Dirichlet singletons," prunable 5/6 by the mod-6 residue.

**(a) Internal contradiction (proved).** The in-range centers are
{2^(b−1) + ⌊2^(b−1)/q⌋}; the distinct values of ⌊N/q⌋ number exactly
2⌊√N⌋ − 1 + [N ≥ ⌊√N⌋(⌊√N⌋+1)] (Dirichlet hyperbola; formula verified exactly on
N ≤ 4096). For b = 135: N = 2^134 is a perfect square, so the islands number
2·2^67 − 1 ≈ 2.95·10^20 against a keyspace of 2^134 — **coverage 1.4·10^−20**.
A set covering 2^−66 of the keyspace cannot be what "the keyspace shatters into."
(The −-branch centers lie below the interval entirely.)

**(b) Real-data test (82 independently verified solved keys).**
- Island hits: **0 of 72 keys with b ≥ 11** — the stream's own claimed domain
  ("above the merge boundary"), expected hits < 0.01 under uniformity.
- 6 hits occur at b ≤ 10 (puzzles 1, 2, 4, 5, 7, 10) — where the island set covers
  2^((3−b)/2) = 9%–100% of the tiny intervals (trivial density artifacts, and
  outside the theory's own claimed regime).
- Offsets (d − 2^(b−1))/2^(b−1): mean 0.5015 (uniform 0.5, sd 0.0319) — **keys are
  uniform in their intervals**; this independently discharges the uniform-generation
  assumption previously carried on project lore (RESEARCH.md item 10 caveat).
- mod-6 residues: [11, 14, 12, 16, 20, 9], χ² = 5.66 on 5 dof (p ≈ 0.34) — no
  class-level residue structure for any island/pruning premise to attach to.

**(c) What is true in the neighborhood.** The floor-quotient set {⌊N/q⌋} is a real
object (exact count above); the CF convergents of u_frac(x) are genuinely "isolated"
best-approximation points (each is the unique best approximation in its denominator
range); visible lattice points have density 6/π². All are properties of public
coordinates or of N — no bridge to d exists (indexical→operational wall, §8b).
The "shattering into singletons" language dresses the one true triviality:
conditioning on the public key isolates d indexically — the same wall every
construction in this stream dies on.
