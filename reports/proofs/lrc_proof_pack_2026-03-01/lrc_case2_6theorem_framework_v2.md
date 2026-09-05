# Case 2 Proof Framework: 6-Theorem Structure
**Session 4, 2026-03-01**

---

## Shared Setup and Notation

Fix n ≥ 3 prime. Let E = (e_1,...,e_{n-1}) be a gcd-1 speed tuple with |E|=n-1 and at least
one e_i ≡ 0 (mod n) (Case 2 hypothesis). Set L = lcm(E), N = nL.

**Partition**: E = E_div ∪ E_non where E_div = {e∈E : n|e}, E_non = {e∈E : n∤e}.
Note |E_div| ≥ 1 and |E_non| = n-2 (since |E|=n-1).

**Fiber decomposition**: Every k ∈ Z_N can be written as k = aL + b with a ∈ Z_n, b ∈ {0,...,L-1}.
The safe condition for runner e at k is: L ≤ (e·k mod N) ≤ (n-1)L.

**Key quantities**:
- `B_div(E,L)` = set of fibers b ∈ {0,...,L-1} where every divisible runner e_d ∈ E_div is safe.
  For a single divisor speed n: B_div = {b : n·b/L ∈ [1,n-1]} = {b : b ∈ [L/n, (n-1)L/n]}.
- `t_e(b)` = floor(e·b/L)  for e ∈ E_non (the "floor quotient" for runner e at fiber b)
- `bad_a(e,b)` = {(-t_e)·inv(e) mod n, (n-1-t_e)·inv(e) mod n}  [2 elements when e·b mod L ≠ 0;
  else 1 element {(-t_e)·inv(e) mod n}]
- `union_bad(b)` = ∪_{e∈E_non} bad_a(e,b) ⊆ Z_n
- `A_b` = Z_n \ union_bad(b)  (safe a-values at fiber b)
- `B_safe(E,L)` = {b ∈ B_div : A_b ≠ ∅}  (fibers with ≥1 safe point)
- `C_bad(E,L)` = |B_div| − |B_safe|  (count of bad fibers)

**Goal**: Prove |B_safe(E,L)| ≥ n−1 = φ(n) for ALL gcd-1 Case-2 tuples.

---

## Theorem 1: Encoding Invariance  [T1 — PROVED]

**Statement**: The quantities B_div(E,L), C_bad(E,L), B_safe(E,L) depend only on the multiset
{e_1,...,e_{n-1}} and L. They are invariant under permutation of E. The bad-a formula
`bad_a(e,b) = {(-t_e)·inv(e), (n-1-t_e)·inv(e)} mod n` depends on e and b only through t_e(b)
and inv(e) mod n — both exact, no fitting.

**Key instance (PL.1)**: For a one-parameter family F(M) = (E_fixed, M) with L = L_0·M:
- Free runner e=M: t_M(b) = floor(M·b/(L_0·M)) = floor(b/L_0). **M-independent.** [PROVED analytically]
- Fixed runners e∈E_fixed: t_e(b) = floor(e·b/(L_0·M)). Depends on M, but takes finitely many
  values mod n for b ∈ B_div (b/M bounded).

**Proof**: Immediate from the definition of floor and L = L_0·M. QED for PL.1.

---

## Theorem 2: Feasible-Signature Compression  [T1 partly; T2 for count bound]

**Statement**: Define the joint signature τ(b) = (t_e(b))_{e∈E_non} ∈ Π_{e∈E_non}{0,...,e-1}.
The set of realized signatures Σ(E,L) = {τ(b): b ∈ B_div} satisfies:

**(a)** The map τ ↦ union_bad(τ) is exact: b ↦ union_bad(b) factors through τ(b). [T1]

**(b)** For each e: t_e(b) = floor(e·b/L), so as b increases, t_e is non-decreasing and piecewise
constant. The joint signature is geometrically coupled: for b ∈ B_div, the realized signatures
are exactly those (t_e) satisfying t_e·L/e ≤ b < (t_e+1)·L/e for all e simultaneously. [T1]

**(c)** Empirical compression: |Σ| << Π_e e. [T2: exact formula open]
  - n=7, E_non = {1,2,3,4,5}: |Σ| = 10 << 120 (12× compression)
  - n=11, E_non = {1,2,3,4,6,6,8,9,M}: many classes, period-121 structure empirically (but not exact law)

**Bottom signature τ_bot = (0,...,0)**: Always realized (b near L/n lies in lower band).
- union_bad(τ_bot) = {0} ∪ {(n-1)·inv(e) mod n : e ∈ E_non} (T1: exact formula)

**Top signature τ_top = (e-1,...,e-1)**: Realized for b near (n-1)L/n.
- union_bad(τ_top) = {0} ∪ {inv(e) mod n : e ∈ E_non} (T1: exact formula, complementary to bottom)

---

## Theorem 3: Structural Obstruction  [T1 for n prime; T2 for composite n]

**Statement**: A fiber b ∈ B_div is bad (A_b = ∅) iff union_bad(b) = Z_n. The following are
sufficient conditions for A_b ≠ ∅ (safe fiber):

**(a) Degree bound** [T1 for n prime]:
  If |E_non| ≤ floor((n-1)/2), then |union_bad(b)| ≤ 2|E_non| ≤ n-1 < n for ALL b.
  Proof: each runner contributes ≤ 2 elements; total ≤ 2·floor((n-1)/2) ≤ n-1. QED.
  → C_bad = 0, B_safe = B_div ≥ n-1. [CLOSED for Case (i)]

**(b) Bottom band** [T1 for n prime]:
  If t_e(b) = 0 for all e ∈ E_non, then:
  union_bad(b) = {0} ∪ {(n-1)·inv(e) : e ∈ E_non} ⊆ Z_n.
  Since {(n-1)·inv(e)} ⊆ Z_n\{0} and |E_non| = n-2:
  |union_bad(b)| ≤ 1 + (n-2) = n-1 < n. Hence A_b ≠ ∅. [PROVED]

**(c) Top band** [T1 for n prime]:
  If t_e(b) = e-1 for all e ∈ E_non, then:
  union_bad(b) = {0} ∪ {inv(e) : e ∈ E_non} ⊆ Z_n.
  Same size bound: |union_bad(b)| ≤ n-1 < n. Hence A_b ≠ ∅. [PROVED]

**(d) Missing-element counting** [T1 — key tool for Theorem 4]:
  If union_bad(E_non \ {M}, t=0) has m elements missing from Z_n and |bad_a(M,b)| ≤ 2,
  and m ≥ 3, then coverage < n regardless of M. [PROVED — exact CRT count]

---

## Theorem 4: Uniform Deficit Bound  [OPEN in general; PROVED for F1246689]

**Goal**: For any gcd-1 Case-2 LRC tuple E with |E|=n-1, n prime:
  C_bad(E,L) ≤ B_div(E,L) − (n−1).

Equivalently: B_safe(E,L) ≥ n−1 = φ(n).

### Sub-theorem 4.F (F1246689): PROVED via Quasi-Lower-Band Argument

**Family**: E(M) = (1,2,3,4,6,6,8,9,M,11), gcd(M,792)=1, n=11, L=792M.
- E_div = {11}; E_non = {1,2,3,4,6,6,8,9,M} (M is the free runner, coprime to 11)
- B_div = [72M, 720M] ∩ Z (exact, from e_d=11 safe interval [L/11, 10L/11])
- B_div count = 648M + 1

**Key computation (exact CRT)**:

For fixed runners E_fixed = {1,2,3,4,6,8,9} (7 distinct speeds; 6 appears twice):

In the quasi-lower band (t_e(b) = 0 for all e ∈ E_fixed):

| e | inv(e) mod 11 | (n-1)·inv(e) mod 11 = bad_a^1 |
|--:|--:|--:|
| 1 | 1 | 10 |
| 2 | 6 | 5 |
| 3 | 4 | 7 |
| 4 | 3 | 8 |
| 6 | 2 | 9 |
| 8 | 7 | 4 |
| 9 | 5 | 6 |

bad_a(e, b) for t_e=0: {0, (n-1)·inv(e)} = {0, value in table above}.

union_bad(E_fixed, t=0) = {0} ∪ {10, 5, 7, 8, 9, 4, 6} = {0, 4, 5, 6, 7, 8, 9, 10}.
(e=6 repeated: contributes {0,9} twice; union unchanged.)

**Missing elements**: Z_11 \ {0,4,5,6,7,8,9,10} = **{1, 2, 3}**. Count = 3.

Free runner M contributes |bad_a(M,b)| ≤ 2 additional elements.

Since 3 > 2: union_bad(b) = union_bad(E_fixed, t=0) ∪ bad_a(M,b)
  has at most 8 + 2 = 10 < 11 elements. So A_b ≠ ∅ for ALL such fibers.

**Quasi-lower band in B_div**:
The condition t_e(b) = 0 for all e ∈ E_fixed requires b < 792M/max(E_fixed) = 792M/9 = 88M.
Combined with B_div = [72M, 720M]:
  Quasi-lower band = {b ∈ Z : 72M ≤ b ≤ 88M − 1}.
  Count = 16M.

For all M ≥ 1: 16M ≥ 16 ≥ 10 = n−1. **Every fiber in this band is safe.**

(Note: t_M(b) = floor(b/792) can be arbitrary in this band; the proof doesn't require t_M=0.)

**Conclusion**: B_safe(F1246689, M) ≥ 16M ≥ 10 = φ(11) for all gcd(M,792)=1.
No fitted slopes used. This is an exact CRT argument. ✓

**Certificate upgrade**: F1246689 moves from T4 (data-fit) to **T1 (proved)**.

---

### Status of Theorem 4 for Other Cases

**Case (i): |E_non| ≤ floor((n-1)/2)** → C_bad = 0. PROVED [T1 for n prime; T2 for composite].

**Canonical (L=n)**: B_safe = n-1 exactly. PROVED [T1].

**2nd smallest (L=2n)**: B_safe = 2(n-2) ≥ n-1. PROVED [T1].

**General large-L with one repeated fixed speed**: The quasi-lower-band argument applies whenever
|union_bad(E_fixed, t=0)| ≤ n-3, i.e., the distinct fixed speeds create ≤ n-3 non-zero elements
in Z_n. This requires k_distinct ≤ n-4 distinct fixed speeds. [T1 when condition holds]

**General large-L with all distinct fixed speeds** (k_distinct = n-3): Missing = 2 elements.
Free runner M can potentially cover both → argument fails. OPEN. [T3 empirically]

**Routes for the remaining open case**:
- **Route D.1 (Density limit)**: Show lim_{L→∞} C_bad/B_div < 1 via the structure of realized
  signatures. In the continuum limit (b/L → β), each signature is a step function of β; the
  measure of β-values with full coverage can be bounded.
- **Route D.2 (Multi-band)**: Even if the quasi-lower band has missing ≤ 2, the top band
  (t_e=e-1 for all fixed e) gives missing = n-1 elements from {-inv(e): e∈E_fixed} ⊆ Z_n\{0}
  — also safe. Combined lower+top safe fiber count may exceed n-1.
- **Route D.3 (CRT period structure)**: For M-parameterized families, the exact C_bad(M)
  for large M is determined by the residue class of inv(M) mod n. At most (n-1) values of
  inv(M) can make each quasi-lower-band fiber bad → most inv(M) residues give safe fibers.

---

## Theorem 5: Main Case-2 Closure  [conditional]

**Statement**: For all n prime and all gcd-1 Case-2 LRC tuples E with |E|=n-1:
  B_safe(E,L) ≥ n−1 = φ(n).

**Proof** (conditioned on Theorem 4):
By Theorem 3(a), if |E_non| ≤ floor((n-1)/2): C_bad=0, B_safe=B_div ≥ n-1. [T1]
For canonical and 2nd-smallest: proved directly. [T1]
For F1246689: Sub-theorem 4.F. [T1]
General large-L with all-distinct fixed speeds: Theorem 4 open. [T3]

**Corollary**: x_0(E) ≥ |B_safe| ≥ φ(n). QED (conditional).

---

## Theorem 6: Full LRC Rational Theorem  [conditional on T5]

**Statement**: For all n ≥ 3 and all gcd-1 speed tuples E = (e_1,...,e_{n-1}):
  x_0(E) ≥ φ(n).

**Proof**:
- Case 1 (∀e: n∤e): Witnesses {jL: gcd(j,n)=1} are all safe. [T1, proved session 1]
- Case 2 (∃e: n|e): Theorem 5. [T1 for sub-cases above; T3 in general]
- Irrational branch: Weyl equidistribution. [T1, proved session 2]

---

## Proof Status Summary

| Theorem | Component | Status |
|---|---|---|
| T1: Encoding Invariance | PL.1 (t_M M-independent) | **PROVED** |
| T2: Signature Compression | Exact map b↦union_bad(τ(b)) | **PROVED** |
| T2: Signature Compression | Compression count bound | T2 (empirical) |
| T3: Structural Obstruction | Degree bound Case(i) | **PROVED** (n prime) |
| T3: Structural Obstruction | Bottom/top band safety | **PROVED** |
| T3: Structural Obstruction | Missing-element tool | **PROVED** |
| T4: Deficit Bound — Canonical | L=n | **PROVED** |
| T4: Deficit Bound — 2nd smallest | L=2n | **PROVED** |
| T4: Deficit Bound — F1246689 | Quasi-lower-band (exact CRT) | **PROVED (NEW)** |
| T4: Deficit Bound — General | All-distinct fixed speeds | **OPEN** |
| T5: Case-2 Closure | Full generality | Conditional on T4 |
| T6: Full Theorem | Rational branch | Conditional on T5 |

---

## Key New Proof: F1246689 Quasi-Lower-Band (No Fitted Slopes)

This is the first exact analytic proof for a "hard" Case-2 family at n=11.

**Mechanism**: The speed-6 repetition in E(M) = (1,2,3,4,**6,6**,8,9,M,11) is crucial:
- 7 distinct fixed speeds cover 7+1=8 elements of Z_11 (with multiplicity from speed-6 repetition
  not adding a new element)
- Missing = {1,2,3}: 3 elements that fixed runners cannot cover when t_e=0
- Free runner M covers at most 2 elements → coverage always ≤ 10 < 11
- Quasi-lower band count: 16M ≥ 16 >> n-1=10

This argument uses ONLY:
1. Exact modular inverses mod 11 (CRT computation)
2. The exact fiber count in [72M, 88M-1] (elementary counting)
3. The bad-a formula (proved from LRC definitions)

**No polynomial fitting, no period-121 model, no slope assumptions.**

---

## Remaining Single Gap

**Open problem**: Prove Theorem 4 for Case-2 families E where E_fixed has n-3 distinct
speeds (each appearing once) — the "all-distinct" regime where the quasi-lower-band
missing count drops to 2, allowing potential full coverage by the free runner M.

**Empirical status**: Zero violations in n=3..7 exhaustive + n=8..12 random (158,626 tuples).
The density C_bad/B_div ≤ 3.75% for F1246689-type families empirically.

**Promising route**: Route D.1 (density limit). In the continuum limit, the bad-fiber
density is determined by the measure of β ∈ [L/n, (n-1)L/n] (normalized) where the
continuum signature gives full coverage. For most β, the signature gives incomplete coverage
(some element of Z_n has zero bad-a preimage). Proving this for the continuum measure would
close the gap.

---

## Addendum A: TM Mechanism Block (Large-L Case-2)

This addendum isolates the mechanism-first route for the remaining large-L Case-2 gap.

### Lemma TM1 (bad fiber iff exact 2-point cover)

Assume a fiber `b` satisfies:
- `|R_fix(b)| = 2`, where `R_fix(b) = Z_n \\ U_fix(b)`
- `|U_M(b)| = 2` (equivalently `s_M(b) != 0`)

Then:

`b` is bad iff `U_M(b) = R_fix(b)`.

So in this regime, badness is exactly a 2-point matching event.

### Lemma TM2 (free-pair rotation law on frozen-fixed band)

Let `I` be a contiguous band where all fixed floors are constant:
`forall e in E_fixed, t_e(b)=tau_e` on `I`.

Then `R_fix(b)` is constant on `I`; write `R_fix={u,v}`.
For prime `n`, with `alpha=M^{-1} mod n` and `t=t_M(b)`,

`U_M(b) = { -t alpha, -(t+1) alpha }`.

As `t -> t+1`, the free bad pair translates by `-alpha` in `Z_n`.

### Lemma TM3 (single-class counting cap)

Under TM2:
- If `gap(R_fix) != +-alpha (mod n)`, then no fiber in `I` can be bad.
- If `gap(R_fix) = +-alpha (mod n)`, badness can occur only when
  `t_M(b)` is in at most one residue class mod `n`.

Hence bad fibers in `I` have density at most `1/n` up to boundary/exception terms.

### Corollary TM-F1246689 (specialized exact form)

For `E(M)=(1,2,3,4,6,6,8,9,M,11)`, `n=11`, `L=792M`,
`I_M=[72M,88M-1] subset B_div` has `|I_M|=16M` and fixed floors `t_e=0` for
all fixed speeds on the whole band.

Exact fixed union:

`union_bad(E_fixed,t=0) = {0,4,5,6,7,8,9,10}`,

missing set `{1,2,3}` has size 3.
Free runner contributes at most 2 bad residues.
Therefore full coverage is impossible on every fiber in `I_M`, so every fiber in
`I_M` is safe.

Thus:

`B_safe >= |I_M| = 16M >= 10 = n-1 = phi(11)`.

So F1246689 is an exact T1 proof instance (no fitted slopes).
