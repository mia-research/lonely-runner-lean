# The Arithmetic of secp256k1 — a pure-structure study

**Version 4 · 2026-07-11 (finalized).** Consolidates v1–v3 and the integrity
audit into a single canonical statement, with every claim graded by evidence.
The clean split of **confirmed positives (graded)** vs **scoped negatives (each
bound to its probe/parameters/scale)** lives in `RESULTS_LEDGER_v1.md`; this
document is the narrative, that one is the record.
The curve is `E : y² = x³ + 7` over `𝔽_p`, `p = 2²⁵⁶ − 2³² − 977`, studied for
its own arithmetic (no keys/puzzle). v1–v3 stay frozen; this version supersedes
them for reference.

**Evidence grades.** **[exact]** = decided by exact integer/Fraction arithmetic
or an exact rational identity (re-run this session). **[LMFDB]** = matched
against the L-functions/Modular-Forms Database. **[math]** = follows from an
argument herein. **[relayed]** = a recorded prior-session computation, not re-run.
**[conjecture]** = a plausible but unproven pattern, flagged as such.

**Notation.** `n = #E(𝔽_p)` (prime); `t = p+1−n = 432420386565659656852420866390673177327`;
`ω = e^{2πi/3}`, `ℤ[ω]`, `μ₆ = ℤ[ω]^* = {±1,±ω,±ω²}`; `K = ℚ(√−3)`;
`N(x+yω)=x²−xy+y²`, `Tr(x+yω)=2x−y`; `π_p = a+bω`,
`a=367917413016453100223835821029139468249`,
`b=303414439467246543595250775667605759171`, `N(π_p)=p`, `2a−b=t` **[exact]**.

---

## Part I — The exact results (Ledger A: solid)

None of Part I depends on any spectral/statistical/Gram computation; each item is
exact or LMFDB-checked. Scripts: `verify_v1.py` (30/30), `thread_A_reciprocity_v2.py`,
`census_ss_v1.py`, `thread_C_supercong_v2.py`, `thread_E_zeros_v1/v3.py`,
`test_claims_v1.py`.

### 1. CM base and the one organizing ideal

`End(E) = ℤ[ω]` (j = 0, disc −3, h = 1), from the visible automorphism
`φ(x,y)=(βx,y)`, `φ²+φ+1=0` **[math; φ(G)=[λ]G exact]**. The classical norm form
holds in primary shape: `4p = t² + 27M²`, `M = 101138146489082181198416925222535253057`
**[exact]**. One ideal organizes the first ledger:
`(π_n) = (π_p − 1)` is the GLV lattice, the amicable prime, the unique prime-order
twist, and the shared-M partner — `N(π_p)=p`, `N(π_p−1)=n` **[exact]**.

### 2. Formal group logarithm

`L(T) = Σ_{k≥0} 7^k C(3k,k)/(6k+1) T^{6k+1} = T + 3T⁷ + (735/13)T¹³ + ⋯`
**[exact to T⁴⁹]**. μ₆-sparse (nonzero exponents ≡ 1 mod 6, forced by Aut(E)).
Exact hypergeometric form `L(T) = T·₃F₂(1/6,1/3,2/3;1/2,7/6;27·7·T⁶/4)` **[exact
term-ratio]**. Family: `Σ b^k C(3k,k)/(6k+1) T^{6k+1}` for all b **[exact, b=1..8]**.
- **Integrality:** `[2],[3],[5](T) ∈ ℤ[[T]]` to T³⁷ — all primes at once **[exact]**.
- **ASD/Honda bridge:** at split `ℓ=6k+1`, `7^k C(3k,k) ≡ a_ℓ (mod ℓ)` (735≡7
  mod 13, 28812≡8 mod 19), and the three-term `b_{ℓ²} − a_ℓ b_ℓ + ℓ ≡ 0 (mod ℓ²)`
  holds for **all 147 split ℓ < 2000** **[exact]**. The mod-ℓ³ upgrade locus is
  **exactly {a_ℓ = ±1}** = {37, 61, 127, 397, 547} **[exact on ℓ<2000]**; the
  scalar correction `δ_ℓ = (b_ℓ−a_ℓ)/ℓ` is non-elementary (not Fermat-quotient,
  not harmonic — Gauss-sum content) **[exact negative]**.
- **Radius:** `T_c = (4/27b)^{1/6}` = the T-chart ramification at `x³ = 2b`; the
  boundary `₃F₂(1)` is an incomplete beta; the critical point is non-torsion
  (doubling sends x ↦ −x/2) **[exact]**.

### 3. The Hecke character — DERIVED

`L(E/ℚ,s) = L(ψ,s)`, ψ a Grössencharacter of K with ∞-type (1,0),
`ψ((α)) = χ(α)·α`. The finite part is a **single sextic symbol on primary π**:

```
χ(π) = −(4k/π)₆⁻¹ ,   k = 7 ⇒  χ(π) = −(28/π)₆⁻¹
```

**[exact — derived, not fit]** (`thread_A_reciprocity_v2.py`): the classical
Jacobi-sum Grössencharacter (Ireland–Rosen ch. 18 / Weil 1949), reconstructed
independently. `a_p(k) = −Σ_x λ(x³+k)` reduces via `#{x:x³=t}=1+ρ+ρ²` to
`a_p(k) = −Tr(χ̄₆(k)·A)`, `A = Σ λ(1+s)ρ(s)` a Jacobi sum, `N(A)=p`; sextic
reciprocity gives the canonical `a_p(k) = Tr(−(4k/π)₆⁻¹·π)` — **1442/1442** over
all six twists + k=7, split primes < 3000. The `4 = 2²` is the 2-supplement (the
`(2²)` conductor part). Conductor `𝔣 = (2²)(√−3)²(7)`, `N(𝔣)=7056`,
`N_E = 3·7056 = 21168` **[math+relayed]**. χ is class-constant mod 28 on primaries
(432 classes = |Cl_𝔣|, 0 violations < 5·10⁵) **[relayed]**; predicts the 256-bit
trace `t` and the amicable alignment **[exact]**. **v1's "not a single rational
sextic symbol" is withdrawn** — round 18 tried `(28/π)₆`, never the negated
inverse.

### 4. The amicable pair — a 13/50 event, exactly the Silverman–Stange constant

`#E(𝔽_p)=n` and `#E(𝔽_n)=p` **[exact, point-order both directions + Hasse
uniqueness]**; mechanism `π_n = π_p − 1`, shared-M form `4n=(t−2)²+27M²` **[exact]**.

- **Not automatic.** "Amicability automatic when n prime" is the j≠0 S–S theorem
  misapplied; for our j=0 curve **12 of 22** split ℓ<1500 with `#E₇` prime fail to
  close (43→31→21, 97→79→67, 211→199→189) **[exact]**.
- **Closure = 13/50**, a residue-class function of the primary Frobenius mod 84:
  of 432 classes, 100 allowed (`432·⅔·½·25/36`), **26 close** **[exact]**; empirical
  0.2666 over ℓ<5·10⁵ (1 SE from 0.26, 9 SE from 1/6) **[relayed]**.
- **= Silverman–Stange Conjecture 40.** `ρ_k = ½(1/3+R(k))`; for k=7 (case d,
  `R=14/75`) this is 13/50; verified as **exact rationals across all 12 residue
  classes mod 36** (`census_ss_v1.py`) **[exact]**. Per-b `ρ_b = {½,13/50,18/101,1/10}`
  order-predict the amicable-pair abundance (b2>b7>b3>b5), matching direct
  enumeration **[exact]**. So 13/50 is *their* published value evaluated for the
  k≡7 class they didn't print — reconstruction + explicit symbol + 256-bit
  instance, not a new theorem.

### 5. GLV = the CM ideal

`φ = [λ]`, `β³≡1 (mod p)`, `λ³≡1 (mod n)`; the GLV lattice `{(u,v):u+vλ≡0 (mod n)}`
has reduced basis `{π_n, ω²π_n}`, det = n; base field `{π_p, ω·π_p}` **[exact]**.
The "magic constants" are the Frobenius coordinates — one ideal `(π_n)=(π_p−1)`.

### 6. Zeros and BSD — computed and LMFDB-confirmed

`L(ψ,s)` built from exact CM Hecke eigenvalues (`thread_E`):
- `Λ(s)=W·Λ(2−s)` to 30 dps; `L(1)=Ω=3.041417228428` **[exact closed form
  `Γ(1/3)Γ(1/6)/(2√π·7^{1/6})`]**, matching **LMFDB 3.0414172284278810424268528156
  to 28 digits**.
- **BSD closes cleanly:** `L(1)/Ω = 1`, and since `y²=x³+7` is globally minimal
  and BSD-rank-0 is a theorem (CM, Rubin/Kolyvagin), every Tamagawa `c_ℓ = 1` and
  `Ш = 1`; all bad fibres Kodaira Type II **[math + numeric]**. (The pasted-table
  "Ω≈6.0828" = `2Ω` = `∫|dx/y|`, the wrong differential.)
- **Zeros:** verified-complete list to height 22 (`thread_E_zeros_v3.py`, bisection
  + completeness assert; unfolded mean spacing 0.991); first zero
  `γ₁ = 0.8173126364` matches **LMFDB 0.8173126364220043 to 10 digits**. On the
  complete list, level repulsion is present (GUE beats Poisson, `P(gap<0.5)=0.056`)
  — a small (36-spacing), low-height, non-asymptotic sample, stated as suggestive.

### 7. External claims-table adjudication (`CLAIMS_ADJUDICATION_v1.md`)

| Claim | Verdict |
|---|---|
| Frobenius coords (a,b) | **✓ exact** |
| "amicability automatic when n prime" | **✗ half wrong** — theorem `π_n=π_p−1` yes; "automatic" is j≠0 misapplied; closure = 13/50 |
| formal-group p-adic integrality | **✓ strengthened** — `[2],[3],[5](T)∈ℤ[[T]]` to T³⁷ |
| unit root α ≡ t (mod p), Hensel to p² | **✓ exact** |
| sextic distribution uniform | **✓ exactly** — 72/432 per unit, χ²=3.26 (df 5) |
| A(ψ) ≈ 536.19 | **✓** = N/(4π²) |
| Ω ≈ 6.0828 | **✗ normalization** — that's 2Ω; Néron/BSD period is 3.0414 (LMFDB-confirmed) |
| \|χ(𝔭)\|² = N𝔭 | **✓ but that's ψ**; the finite χ has \|χ\|=1 |

---

## Part II — The spectral extension (honestly scoped)

Two ledgers, kept separate. The curve's L(ψ,s) is a maximally explicit CM object
(§6), and much of the "spectral" excitement in the associated RH-programme reduces,
on inspection, to the CM discriminant character χ₋₃ — but the tools here are
confound-prone and the strong meta-claims are **not** established.

- **What is solid:** the explicit-formula / Riemann–von Mangoldt counting law
  (verified on the zeros); the local Hilbert–Pólya realization per prime
  (Sato–Tate phases `e^{±iθ_p}`), with the proven global interpolation obstruction
  (arXiv:2605.17645); the derived χ names the **finite** ray-class μ₆ sector
  (Pontryagin-dual to the archimedean angle — a v1-adelic conflation corrected in
  `adelic_recasting_v2.md`).
- **The one robust spectral finding — the "dilution" is the χ₋₃ conductor shadow.**
  For the `f_q(ℓ)=cos(2π a_ℓ/q)` construction, the elevated `λ_max/Tr` is a single
  rank-1 mode aligning with χ₋₃ at 0.997; it comes from `a_ℓ=0` identically on
  inert primes; restricting to split primes kills it (0.575→0.120). This mechanism
  is envelope-independent and stands. *Caveat:* the feature map was inferred (Q=50
  numeric off ~25% from the reported table) — mechanism solid, exact reproduction
  approximate.
- **[conjecture] "the spectral/Gram axis is exhausted (only χ₋₃ shows)."**
  Downgraded from a claim (`INTEGRITY_AUDIT_v1.md`). It rests on Gram tests that
  proved confound-prone (the `1/√p` envelope and sample-set choices flipped the
  Finding-3 verdict twice). *Scoped negative:* the clean same-sample,
  envelope-preserving, matched-random-character null (8 moduli, 500 samples)
  **detected no sextic common mode** (real top below null, z=−1.5) — a fact about
  that test, not a proof that none exists (see `RESULTS_LEDGER_v1.md` B4).
- **The Moment-Pumping / twist question (`thread_moment_twist.py`).** The RH
  programme's "moment decays not grows" verdict used generic `|χ|=1` twists. The
  CM curve twist (`a_p`, Sato–Tate amplitude + inert support) is a *constant factor*
  more concentrated, but **delocalized at the same asymptotic rate** (slope −0.327
  vs −0.33) *for the tested parameters* (γ=14.13, σ=0.5, X≤32000) — no growth
  observed in this range/construction (ledger B6). (A first `p^{σ−1}`-envelope run
  falsely showed concentration; that envelope did not reproduce the drafts' −0.36
  baseline and was corrected. Near-miss.)
- **The φ(n)-RH programme (Ledger B) does not establish RH,** on two load-bearing
  gaps, each scoped: the Moment-Pumping forcing needs growth but the projected
  moment *delocalizes* on the tested forcing class (E1); and `Ĥ=πA²` on `[1,∞)` has
  deficiency indices `(1,1)≠(0,0)` (re-derived, implementation-independent, E2).
  The study never leans on it.

---

## Part III — Ledger, manifest, threads

### What holds, by grade
- **[exact / LMFDB — solid]:** everything in Part I (formal group + ASD, derived χ,
  amicable 13/50 = S–S Conj 40, GLV, zeros, BSD, the claims table).
- **[robust mechanism]:** the χ₋₃ conductor shadow behind the "dilution."
- **[conjecture / downgraded]:** "spectral axis exhausted / sextic invisible";
  the μ₆=μ₂×μ₃ role split.
- **[open]:** thread α (formal group → Katz p-adic L; `{a_ℓ=±1}` = p-adic special
  locus; δ_ℓ = Gross–Koblitz candidate); thread β (amicable dynamical system,
  exact 3-cycle density); thread γ (make the χ₋₃-only 2nd-moment statement a
  theorem, and where μ₃ lives = Sym²). See `ULTRATHINK_THREADS_v1.md`.

### Verification manifest
`verify_v1.py` (30/30); `thread_A_reciprocity_v2.py` (character derivation,
1442/1442); `census_ss_v1.py` + `test_ss_conjecture40_v1.py` (13/50 = Conj 40, 12
classes); `thread_C_supercong_v2.py` (ASD 147/147, {a_ℓ=±1}); `thread_E_zeros_v3.py`
(verified-complete zeros, GUE); `test_claims_v1.py` (claims table). Integrity +
spectral audits: `INTEGRITY_AUDIT_v1.md`, `SPECTRAL_AUDIT_v1.md`,
`SPECTRAL_REALIZATION_v1.md`, `DILUTION_CHECK_v1.md`, `BASE_AUDIT_v1.md`,
`adelic_recasting_v2.md`.

### Standing method rule (from the audit)
Any spectral/Gram common-mode test requires **same sample set, envelope preserved,
matched random-character null** (not the iid Marchenko–Pastur edge, not an
independent-column shuffle) — *and reproduce the target's baseline first* — before
any rank/common-mode claim. Reproduce a source's phenomenon before dismissing it.

## References
Silverman–Stange (arXiv:0912.1831, Conj 40+27); B. Smith (1409.4526); GLV (2001);
Ireland–Rosen ch. 18 / Weil 1949; supercongruences (1210.4489, 1303.6706);
CM-√−3 L(1) (1003.5289); Lee–Sheen (2606.25067), Pajaziti–Sadek (2301.00711);
local Hilbert–Pólya (2605.17645); Cohen 1949; LMFDB curve 21168.ce2 / `y²=x³+7`.
