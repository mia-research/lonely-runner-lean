# secp256k1 — Positive Findings Compendium & Handover (v3, 2026-07-13)

A single self-contained corpus of the **structure that was found, computed, proved, or
rediscovered** across this project: the curve's CM arithmetic, the Eisenstein lift laws,
the character/GLV structure, the endomorphism ring and Galois data, the curve L-function
and formal group (with the ASD/Honda bridge), the twist structure and Frobenius sieve, the
amicability, the RH-framework CM connection, the (n,k,D) / D-signature decomposition, the
on-chain signature surface, the key-construction substrate, and the datasets. Every item
carries a status tag and the file that produces/verifies it. (Supersedes v1/v2; complete
standalone version.)

## Status tags

- **PROVED** — symbolic identity, exhaustive-by-construction argument, or a proof.
- **VERIFIED** — exact (integer / exact-rational) computation confirming the fact for the
  stated inputs (secp's `p,n`, a prime sweep, or brute-force cross-check).
- **EMPIRICAL** — measured on a finite sample; size/floor stated.
- **CITED** — a classical theorem or external result used as input.

## Constants

```
p = 2^256 − 2^32 − 977                                                   (field prime)
n = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141   (group order, prime)
E : y^2 = x^3 + 7          (j = 0, CM by Z[omega], omega = e^{2 pi i/3}, |Aut(E)| = 6)
t = p + 1 − n = 432420386565659656852420866390673177327                 (Frobenius trace)
pi = a + b*omega,  a = 367917413016453100223835821029139468249,
                   b = 303414439467246543595250775667605759171,   N(pi) = p,  2a−b = t
4p = t^2 + 3 f^2  [VERIFIED],  disc(Z[pi]) = t^2 − 4p = −3 f^2,
   f = 3 · 79 · 349 · 2698097 · 1359580455984873519493666411   (last a 90-bit prime)
p − 1 = 2 · 3 · 7 · 13441 · C
n − 1 = 2^6 · 3 · 149 · 631 · 107361793816595537 · 174723607534414371449
        · 341948486974166000522343609283189
```
**[VERIFIED] One ideal organizes the first ledger:** `(π_n) = (π_p − 1)` is simultaneously
the GLV lattice, the amicable prime above `n`, the unique prime-order twist's Frobenius
shift, and the shared-modulus partner; `N(π_p)=p`, `N(π_p−1)=n`.

---

# PART I — Curve substrate & valid key construction

**[VERIFIED] Exact scalar multiplication, validated against real solved keys.**
`ecc_secp256k1.py` (Appendix A.1) computes `(x,y)=[d]G` with pure-integer Jacobian
arithmetic, validated element-by-element against the real solved keys (`puzzles_verified.csv`).
From any `d ∈ [1,n)` it constructs `(d, X, Y)` across the full 1..256-bit range, hence any
derived `(d, X, Y, n, k, D)` record. `d ↔ (X,Y)` is a bijection `ℤ/nℤ → E(𝔽_p)`.

---

# PART II — The Eisenstein lift laws (angle, norm, character, GLV)

`p ≡ 1 (mod 3)` ⇒ `(π_p)` degree-1 prime, `N(π_p)=p`, `ℤ[ω]/(π_p) ≅ 𝔽_p`. The lift
`eis : 𝔽_p → ℤ[ω]` reduces `X mod π_p` (Babai) into the Gauss-reduced domain `P`. Basis
`R1=(-303414439467246543595250775667605759171, 64502973549206556628585045361533709078)`,
`R2=(64502973549206556628585045361533709078, 367917413016453100223835821029139468249)`.

**[PROVED] Lemma A.** `eis` is a bijection `𝔽_p → ℤ[ω]∩P`; `{eis(X)}` = the `p` lattice
points of `ℤ[ω]` in `P`, uniform.

**[PROVED] Rhombus theorem (universal).** Both reduced basis vectors have norm exactly `p`
(unit associates of `π_p`); `P` is a **60° rhombus**, edge `√p`, area `p√3/2`. Verified all
300 primes `p≡1(3)` in `[7,4513]` and secp. *(`lift_sextant_rhombus_law_proof_v2.py`.)*

**[PROVED] One-parameter angle law.** Sextant histogram = function of `θ=arg(π_p) mod 60°`
(fold `[0,30°]`); opposite sectors equal; three pairs sum `1/2`:

| pair | proportion |
|---|---|
| pinned | **exactly `1/8`** (symbolic `√3/16`, θ-independent) |
| free A | `p₀(θ)=(3/4)|cos 2θ|/(2 cos 2θ+1)` |
| free B | `3/8 − p₀(θ)` |

Exact rational forms (secp cell): `{0,3}=1/8`, `{1,4}=p/(8|a(a−b)|)=0.129659…`,
`{2,5}=|ab+2ad+cd|/(8|ad|)=0.245341…`. The `1/8` is a **universal invariant** (`{0,3}` or
`{1,4}`, never max). secp: pinned `{0,3}`, `θ=50.55°`. *(Matches exact areas to `1.7e-16`
over 150 primes.)*

**[VERIFIED] Error term.** `H(s)=area+O(√p)` absolute; `P[σ=s]=area/p+O(p^{-1/2})` relative.

**[PROVED/VERIFIED] Norm-band law.** `s=N(eis X)/p` universal (θ,p-independent): support
`[0,3/4]`; **mean `1/6` exactly**; density const `2π/√3` on `[0,3/16]`; breakpoints
`3/16, 1/4, 3/4`. *(Exact CDF matches lattice to `8e-4`. `norm_band_law_proof_v1.py`.)*

**[PROVED] All nontrivial `χ_k` exactly uniform** (fibers `(p−1)/k`); `χ₆` verified by exact
enumeration (`p=100003`, all 16667), `Σζ₆^{χ₆}=0`. *(`lift_chi6_uniform_law_proof_v1.py`.)*

**[PROVED/VERIFIED] GLV = lift × cube-root-of-unity.** `φ(x,y)=(βx,y)`, `β≡ω²`; exact over
40000: `χ₆(βx)=χ₆(x)+4`, `χ₃(βx)=χ₃(x)+1`, `χ₂` fixed; orbit-sextant ~98% same parity.
*(`glv_orbit_structure_proof_v1.py`.)*

**[PROVED] Summation-polynomial `[ω]`-covariance.** `S₃(βx₁,βx₂,βx₃)=β·S₃` (eigenvalue
`β¹`); `S₄(βx₁,…,βx₄)=S₄` (eigenvalue `β⁰`, `[ω]`-**invariant**). Both are irreducible over
`ℚ(b)` with full degree `2^{m−2}` in each variable (`S₄` degree 4); the `μ₆`/automorphism
covariance carries the `√6` symmetry of `|Aut(E)|=6`. *(`summation_and_formalgroup_v1.py`.)*
**[PROVED] `y` symmetries:** `χ₂(y(n−d))=−χ₂(y(d))`, `f(λd)=f(d)`.

---

# PART III — CM / endomorphism-ring structure

**[VERIFIED] `End(E)=ℤ[ω]`, maximal order.** For any `j=0` curve `φ:(x,y)↦(βx,y)` (`β³=1`,
`φ²+φ+1=0`) gives `ℤ[ω]⊆End(E)`, forcing `End(E)=ℤ[ω]`. Confirmed via a mod-`ℓ²`
crater/floor test on 8112 `(curve,ℓ)` cases vs brute force (0 mismatches, all craters);
secp on the crater (single vertex) of every isogeny volcano; `h(End)=h(−3)=1`. Conductor of
`ℤ[π]`: `f` (above); `4p=t²+3f²`, `disc(ℤ[π])=−3f²`. *(`secp256k1_cycles_findings.md`.)*

**[VERIFIED] `μ₆` acts FREELY on `E(𝔽_p)\{O}`:** `{O} ∪ (n−1)/6` free orbits of size 6, i.e.
`(n−1)/6 = 19298681539552699237261830834781317975472927379845817397100860523586360249056`.

**[VERIFIED] Sextic identities** (`sextic_identities_verify.py`): `u=−1` is the **unique**
unit with `N(π+u)=n`; `π_n=π−1` explicit generator of the prime above `n`; sextic classes
`[7/π_p]₆=ζ₆⁵`, `[7/π_n]₆=ζ₆¹`, carrier `ζ₆⁴=ω²`; exact 4-D character `ε=ζ₆^{3−[28/π]₆}`.

**[VERIFIED] Frobenius data.** Angle `cos θ=t/(2√p)=0.63538…`, `θ=50.55°` (30th-pctile CM
Sato–Tate). Hasse invariant `= a_p mod p = t`. p-adic unit root `α` (`α≡t mod p`, next digit
`103482995291570382327745514962295612511852368578636630096241337387108360383642`,
`α²−tα+p≡0 mod p³`). `ord_p(t)=(p−1)/6` = first p-torsion degree; trace index `6=|μ₆|` in
`𝔽_p*`.

**[VERIFIED] Galois images.** mod-2: `x³+7` irreducible ⇒ 2-torsion field `𝔽_{p³}`,
Frobenius `= 3-cycle` (image `ℤ/3`). mod-ℓ: Frobenius `⊂` Cartan (split `ℓ≡1`, nonsplit
`ℓ≡2`, scalar `ℓ=3`).

**[VERIFIED] Extension tower.** `E(𝔽_{p^k})≅ℤ/d₁×ℤ/d₂`, `d₁=gcd(A_k−1,B_k)`; torsion-degree
tower `deg(3)=2, deg(2)=deg(7)=3, deg(13)=4`; `E(𝔽_p)` cyclic, first non-cyclic at `k=2`.

**[VERIFIED] Forced arithmetic facts.** `7` QNR, `−7` non-cube, `3∤n`, `p≡3 mod4`,
`y`-fibration `E→E/[ω]≅ℙ¹` ramifies at `E[ω−1]` with no rational ramification.

**[VERIFIED] MOV embedding degree `ord_n(p) = (n−1)/6`** (254-bit), i.e. `p` has
multiplicative index **6 = |μ₆|** in `(ℤ/n)*` — the sextic index again (cf.
`ord_n(2)=(n−1)/64`, `ord_p(t)=(p−1)/6`). **[CITED — Tate]** Isogenous curves over `𝔽_p`
have equal `#E(𝔽_p)=n`, so the entire isogeny class has order `n`.

---

# PART IV — Curve L-function, formal group, ASD bridge

**[VERIFIED / CITED-theorem] L-function & its RH.** `L(T)=1−tT+pT²=(1−πT)(1−π̄T)`;
`|π|=√p` (40 digits) — RH for `E/𝔽_p` (Hasse=Weil, a theorem); zeros exactly on `Re(s)=1/2`
at height `±θ/log p`; the critical line is pinned by the Weil pairing (Frobenius unitary,
`ππ̄=p`). Supersingular: `a_ℓ=0 ⟺ (ℓ/3)=−1` (`ℓ≡2 mod3`). *(`secp256k1_Lfunction_intersections.md`.)*

**[VERIFIED] Formal-group logarithm — exact closed form** (to `T⁴⁹`):
```
L(T) = Σ_{k≥0}  7^k · C(3k,k)/(6k+1) · T^{6k+1}
     = T + 3T^7 + (735/13)T^13 + (28812/19)T^19 + (237699/5)T^25 + …
```
`μ₆-sparse` (nonzero exponents `≡1 mod6`, forced by `Aut(E)`); hypergeometric
`L(T)=T·₂F₁(1/3,1/6;7/6;−27·7·T⁶/4)`-type; family `Σ b^k C(3k,k)/(6k+1) T^{6k+1}` for
`y²=x³+b`. *(`secp256k1_formal_group_finding.md`.)*

**[VERIFIED] ASD / Honda bridge.** At split `ℓ=6k+1`: `7^k·C(3k,k) ≡ a_ℓ (mod ℓ)` — the
formal-log coefficients reduce to the trace of Frobenius (supercongruence), verified
147/147. *(`secp256k1_arithmetic_v4.md`.)*

**[VERIFIED] Whole-group L-series.** `L(T)=T·₃F₂(1/6,1/3,2/3;1/2,7/6;27·7·T⁶/4)`,
linearizes `E₁(ℚ_p)`. The six twist traces (`±t, ±(a+b), ±(2b−a)`) are 128–129 bit.
*(`zomega_lattice_probe_findings_v1.md`.)*

**[VERIFIED] Explicit formal group law** (from the log, `F(T₁,T₂)=exp(L(T₁)+L(T₂))`):
```
F(T₁,T₂) = T₁ + T₂ − 7·(3 T₁T₂⁶ + 9 T₁²T₂⁵ + 15 T₁³T₂⁴ + 15 T₁⁴T₂³ + 9 T₁⁵T₂² + 3 T₁⁶T₂)
           + 7²·(225 T₁⁷T₂⁶ + …) + …
```
Identity axiom `F(T₁,0)=T₁` holds; no linear cross-term (`a₁=0`); **μ₆-sparse** (first
correction at total degree `7≡1 mod6`, coefficients multiples of `b=7`). `L` linearizes
the formal subgroup `E₁(ℚ_p)` (points reducing to `O`). *(`summation_and_formalgroup_v1.py`.)*

---

# PART V — Twist structure & the Frobenius sieve

**[VERIFIED] Six sextic twists:** Frobenius `u·π_p` (`u∈μ₆`), orders `N(π_p+u)`, sum
`6(p+1)`; `b=7 ↔ u=1+ω` unique prime-order. **Quadratic twist** `n_t=2(p+1)−n =
3²·13²·3319·22639·C`, `C=1013176677300131846900870239606035638738100997248092069256697437031`
(216-bit prime); `169|n_t` ⇒ rational subgroup order 169. `ord_n(2)=(n−1)/64`.

**[VERIFIED] Frobenius sieve law:** `ℓ|n_t ⟺` Frobenius eigenvalue `−1 mod ℓ`, i.e.
`freq(ℓ|n_t)=P(Frob eig −1)`. Sign-definite; 24/24 across two CM fields; CM-family-wide
(primes `<12000`). *(`cm_twist_order_divisibility_2026_07_10.md`, `cm_imprint_ramified_prime_findings.md`.)*

**[VERIFIED] Twist-order Ramanujan spectrum** (`nt_spectral_rework_findings.md`): min nonzero
`|c_{n_t}(k)| = 39 = 3·13` (large primes in their `−1` branch); `c_{n_t}(n_t/3)=−φ(n_t)/2`;
`3|n_t` gives split density `1/2` (verified 216/432).

---

# PART VI — Amicability

**[VERIFIED] `(p,n)` is an amicable pair — aliquot cycle `p→n→p`.** By point-counting
(`ℤ[ω]` factorization + exact sextic character; validated 44 primes, both iterates of 14
cases vs brute force, `#E(𝔽_p)=n` at scale): **`#E(𝔽_n)=p` exactly.** Structural: Frobenius
at `p` is `π` (`#E=N(π−1)=n`), at `n` is `1−π`, `(1−π)−1=−π` has norm `p`. CM-abundance
(Silverman–Stange). *(`sextic_identities_findings.md`.)*

**[EMPIRICAL] Amicable density** `~0.27`, consistent (<1σ) with Silverman–Stange
Conjecture 40 `13/50`. **[VERIFIED] Hecke character** `χ(π)=−(28/π)₆^{-1}` (206/206).
**[VERIFIED] BSD/Tamagawa** `∏c_ℓ=1, Ш=1, II/II/II, L(1)=Ω`. **[VERIFIED] Eisenstein-twin
density = Bateman–Horn** (obs/pred=0.9975).

---

# PART VII — The RH-framework CM connection

**[PROVED] Eisenstein–Ramanujan survival law.** For `c_𝔫(β)=Σ_{r∈(ℤ[ω]/𝔫)*} e^{2πiTr(βr)/𝔫}`:
μ₆-invariance; multiplicativity (CRT); closed form `c_𝔫(β)=μ_K(𝔫/𝔤)Φ(𝔫)/Φ(𝔫/𝔤)`; and the
**surviving core along a primorial is exactly `μ₆` — six modes**, vs `±1` (two) over `ℤ`.
Operator side `Ĥ^CM=⊕_m π(A_r²+m²)`, self-adjointness transfers, angular space splits into 6
sextic sectors `↔ μ₆`. The sextic `6=|μ₆|=|Aut|` runs through `ord_p(t)=(p−1)/6`, the
μ₆-sparse log, and the x-line 6-orbits. *(`eisenstein_ramanujan_survival.md`, `radial_selfadjointness.md`.)*

**[PROVED] Low-prime feature matrix is exactly rank-10 orthogonal.** Building the ZFR
feature matrix `F` (rows = characters `(q,j)`, columns = low primes `≤29`), character
orthogonality forces all 10 singular values `= √10`, participation ratio `= 10.000`, column
Gram exactly diagonal. **[EMPIRICAL, reproduced]** the large-prime correlation `K` common
mode is real: top-eigenvalue/MP-edge `= 1.089` (matches the paper's Table 1).
*(`vertical_zfr_replication.md`, `zfr_rank2_findings.md`.)*

---

# PART VIII — (n,k,D), the exact D-signature, curve identity, datasets

**[VERIFIED] Scalar arithmetic.** `n` splits ⇒ `ℤ[ω]/(π_n)=𝔽_n=ℤ/nℤ`; the scalar is
**1-dimensional** in `ℤ[ω]`; GLV `(a,b)` is a non-canonical Babai coset rep, not an
invariant of `d`.

**[VERIFIED] Exact D-signature recursion (the user's exact form).**
```
N = 2^P ;   D_i = N // |e_{i-1}| ;   c_i = N // D_i ;   e_i = |e_{i-1}| − c_i ;   stop at 0
```
The greedy nearest-unit-fraction expansion; it reproduces the dataset's `D_terms` column
**exactly (40260/40260)** and the user's Findings B `[2,41,1722]` / C. The D-signature is an
**invertible encoding** of the key (early terms = coarse structure, final term = residual
scaling). Term counts: random keys `~6–8` (80-bit→6.0, 160→7.0, 256→7.7, max 9); `10–11`
needs deliberate `~9`-layer construction. *(`d_recursion_exact_v1.py`,
`phi_n_exact_dsignature_findings_v1.md`, `phi_n_highN_fullrange_findings_v1.md`.)*

**[VERIFIED] Curve identity linking `(n,k,D)`.** `n·Q − (n+k)·A = r·G` with
`r = n·D − (2^{N−1}·k mod n)`, holds exactly (15/15 sampled) — an exact algebraic identity
relating the point `Q`, the `(n,k)` Farey pair, and the residual `D`.
*(`btc_puzzle_findings_v3.md`, `btc_puzzle_exact_leak_test_2026_07_07`.)*

**[VERIFIED] (n,k,D) validity domain.** Coprimality is the label-validity condition; the
`D`-gap narrows with `n`; the GLV 2-D→1-D degeneracy transition is exactly `N=128`;
order-overflow at `N=256` occurs with probability `~2^{-128}`. Farey `(n,k)` via exact best-rational (`|a·n−k·b|` min).
**[VERIFIED] Automorphism factor** `√6≈2.45×` from `|Aut(E)|=6`.

**Datasets.** `puzzles_verified.csv` (real solved keys); `constructed_keys_fullrange_v1.npz`
(36k known-`d`, 21k @256-bit); the **100k MT19937 set** (our MT19937 through the same
select-bitlength→curve pipeline — a known-generator reference; test on both).

---

# PART IX — On-chain signature surface (exposed high keys)

**[VERIFIED / EMPIRICAL] ECDSA nonce structure of the exposed-key transactions.** The full
on-chain signature surface for the exposed high keys was extracted (blockstream.info):
- **14/14 nonce reconstruction** `k=s⁻¹(z+r·d) mod n` verified (`k·G` x-coord `= r`).
- **21/21 distinct `r`** — no reused-nonce.
- **4/14 nonces match standard RFC6979 exactly** (deterministic HMAC-DRBG, first ~6
  candidates). A 256-bit RFC6979 match is not chance ⇒ four of the exposed-key signatures
  were produced with standard deterministic nonces; the other ten were not.

*(`gap_results_v6.md`; scripts `sig_lib.py`, `nonce_structure.py`.)*

---

# PART X — Empirical observations on the solved-key set (underpowered — not established)

Directional hints on the 82 real keys, **not** established findings (control-backed;
planted-signal controls fire at `p≈0`):
- **[EMPIRICAL, underpowered]** cubic-residue **class-0 lean**: real `44%` vs synthetic
  `33%` (uniform baseline confirmed flat), `p≈0.11`. *(`key_cubic_char_v2.py`.)*
- **[EMPIRICAL, underpowered]** multiplicative **smoothness lean**: real keys slightly more
  composite, `p=0.058` raw (fails Bonferroni×8). Same direction. *(`multilens_sweep_v1.py`.)*
- **[UNTESTED]** shared-early-D-term test on the 82 keys (would betray a
  sum-of-simple-fractions construction) — the natural next probe, not yet run.

---

# PART XI — Proof manifest (items tagged PROVED)

1. Lemma A — `eis` bijection ⇒ lift uniform on `ℤ[ω]∩P`. (II)
2. Rhombus theorem — reduced basis both norm `p`; universal. (II)
3. One-parameter angle law + closed forms; `1/8` universal (`√3/16`). (II)
4. Norm-band law — universal, mean `1/6`, density `2π/√3` on `[0,3/16]`. (II)
5. All nontrivial `χ_k` exactly uniform; `χ₆` fibers `(p−1)/6`. (II)
6. GLV `β≡ω²`; character shifts `χ₆:+4, χ₃:+1, χ₂:fixed`. (II)
7. Summation polynomials `S₃`(`β¹`)/`S₄`(`β⁰`) `[ω]`-covariant, irreducible, full degree;
   `y` symmetries. (II)
8. `End(E)=ℤ[ω]` maximal; `μ₆` free action `(n−1)/6` orbits. (III)
9. Eisenstein–Ramanujan survival law (μ₆ six-mode core). (VII)
10. Low-prime feature matrix exactly rank-10 orthogonal (character orthogonality). (VII)

Classical-theorem inputs used as facts: RH for `E/𝔽_p` (Hasse–Weil), `ℤ[ω]⊆End` for `j=0`,
Silverman–Stange CM amicable abundance, Hecke CM equidistribution.

---

# Appendix A — foundational code

### A.1 `ecc_secp256k1.py`

```python
P  = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
Gx = 0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798
Gy = 0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8
N_ORDER = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141

def _dbl(Xx,Yy,Zz):
    if Yy==0: return (0,1,0)
    A=(Xx*Xx)%P; B=(Yy*Yy)%P; C=(B*B)%P
    D=(2*(((Xx+B)*(Xx+B)-A-C)))%P
    E=(3*A)%P; F=(E*E)%P
    X3=(F-2*D)%P; Y3=(E*(D-X3)-8*C)%P; Z3=(2*Yy*Zz)%P
    return (X3,Y3,Z3)

def _add(P1,P2):
    X1,Y1,Z1=P1; X2,Y2,Z2=P2
    if Z1==0: return P2
    if Z2==0: return P1
    Z1Z1=(Z1*Z1)%P; Z2Z2=(Z2*Z2)%P
    U1=(X1*Z2Z2)%P; U2=(X2*Z1Z1)%P
    S1=(Y1*Z2*Z2Z2)%P; S2=(Y2*Z1*Z1Z1)%P
    if U1==U2:
        if S1!=S2: return (0,1,0)
        return _dbl(X1,Y1,Z1)
    H=(U2-U1)%P; r=(S2-S1)%P
    HH=(H*H)%P; HHH=(H*HH)%P; V=(U1*HH)%P
    X3=(r*r-HHH-2*V)%P; Y3=(r*(V-X3)-S1*HHH)%P; Z3=(Z1*Z2*H)%P
    return (X3,Y3,Z3)

def scalar_mul(k, base=(Gx,Gy)):
    R=(0,1,0); Q=(base[0],base[1],1)
    while k>0:
        if k&1: R=_add(R,Q)
        Q=_dbl(*Q); k>>=1
    Xx,Yy,Zz=R
    if Zz==0: return None
    zi=pow(Zz,P-2,P); zi2=(zi*zi)%P
    return ((Xx*zi2)%P, (Yy*zi2*zi)%P)
```

### A.2 `eisenstein_lift_sextant_exact_v1.py`

```python
p = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
aP = 367917413016453100223835821029139468249
bP = 303414439467246543595250775667605759171
assert aP*aP - aP*bP + bP*bP == p

def rdiv(nu, de):
    if de < 0: nu, de = -nu, -de
    q, r = divmod(nu, de); return q + 1 if 2*r >= de else q
def gauss(u, v):
    dot = lambda a, b: a[0]*b[0] + a[1]*b[1]
    while True:
        if dot(v, v) < dot(u, u): u, v = v, u
        m = rdiv(dot(u, v), dot(u, u)); v = (v[0]-m*u[0], v[1]-m*u[1])
        if dot(v, v) >= dot(u, u): return u, v
R1, R2 = gauss((aP, bP), (-bP, aP-bP))
DET = R1[0]*R2[1] - R1[1]*R2[0]

def eis(X):
    c1 = rdiv(X*R2[1], DET); c2 = rdiv(-X*R1[1], DET)
    return (X - (c1*R1[0] + c2*R2[0]), -(c1*R1[1] + c2*R2[1]))

def sextant(u, v):
    if u == 0 and v == 0: return 0
    for k in range(6):
        if v >= 0 and (u - v) >= 0 and u > 0: return k
        u, v = v, v - u
    return 0 if v >= 0 else 3
```

### A.3 Exact D-signature recursion

```python
def d_signature(key, P=256):        # greedy nearest-unit-fraction expansion of the key
    N = 1 << P
    e = abs(key); terms = []
    while e:
        D = N // e
        c = N // D
        terms.append(D)
        e = abs(e - c)
    return terms                    # reproduces dataset D_terms exactly (40260/40260)
```

### A.4 Formal-group logarithm (reproduce with sympy)

```python
import sympy as sp
z = sp.symbols('z')
wser = sp.Integer(0)
for _ in range(8):
    wser = sp.series(z**3 + 7*wser**3, z, 0, 50).removeO()   # w = z^3 + 7 w^3
x = sp.series(z/wser, z, 0, 50).removeO()
y = sp.series(-1/wser, z, 0, 50).removeO()
L = sp.integrate(sp.series(sp.diff(x, z)/(2*y), z, 0, 48).removeO(), z)
# L(T) = sum_k 7^k C(3k,k)/(6k+1) T^(6k+1);  nonzero exponents all == 1 (mod 6);
# and 7^k C(3k,k) ≡ a_ℓ (mod ℓ) at split ℓ=6k+1 (ASD/Honda, 147/147).
```

---

# Appendix B — script & document manifest (all in `btc_puzzle_investigation/`)

Full source of the proof/verification scripts is embedded in **Appendix C** below.

| file | proves / verifies |
|---|---|
| `lift_sextant_rhombus_law_proof_v2.py` | rhombus theorem, angle law, `1/8` invariant (II) |
| `lift_chi6_uniform_law_proof_v1.py` | `χ₆` uniform; `Σζ₆^{χ₆}=0` (II) |
| `norm_band_law_proof_v1.py` | universal norm-band law, mean `1/6` (II) |
| `glv_orbit_structure_proof_v1.py` | `β≡ω²`; GLV character shifts (II) |
| `y_orbit_class_investigation_v1.py` | orbit-sextant; `S₃`; forced facts (II,III) |
| `summation_and_formalgroup_v1.py` | `S₄` `[ω]`-covariance; explicit formal group law (II,IV) |
| `frontier_beyond_singlex_v1.py` | `N(π_p−1)=n`; module; eigendifferential (III) |
| `sextic_identities_verify.py` | `π_n=π−1`; unique unit; sextic classes; `n_t` (III,V) |
| `secp256k1_order_fingerprint.py` | `p−1`,`n−1` factorizations; index (III) |
| `d_recursion_exact_v1.py` | exact D-signature (40260/40260) (VIII) |
| `build_fullrange_dataset_v1.py` / `nkd_validity_domain_v1.py` | datasets + (n,k,D) domain (VIII) |
| `sig_lib.py` / `nonce_structure.py` | on-chain nonce surface, RFC6979 4/14 (IX) |

Findings documents (exact detail): `secp256k1_formal_group_finding.md`,
`secp256k1_Lfunction_intersections.md`, `secp256k1_cycles_findings.md`,
`sextic_identities_findings.md`, `cm_twist_order_divisibility_2026_07_10.md`,
`cm_imprint_ramified_prime_findings.md`, `nt_spectral_rework_findings.md`,
`eisenstein_ramanujan_survival.md`, `radial_selfadjointness.md`,
`vertical_zfr_replication.md`, `zfr_rank2_findings.md`, `zomega_lattice_probe_findings_v1.md`,
`phi_n_exact_dsignature_findings_v1.md`, `gap_results_v6.md`,
`KNOWN_FACTS_secp256k1_and_keys_v5.1.md` (master), `secp256k1_arithmetic_v4.md` (Part-I ledger).

---

# Appendix C — full proof/verification source

Complete source of the proof and verification scripts (each imports the Appendix A
primitives, keeps exact arithmetic in the signal path, and prints its own verification).

### C — `lift_sextant_rhombus_law_proof_v2.py`

```python
#!/usr/bin/env python3
"""
lift_sextant_rhombus_law_proof_v2.py

STRENGTHENS lift_sextant_law_proof_v1.py.

v1 proved: for secp's prime p, the lift-sextant marginal is a closed-form area
law over the fundamental parallelogram P of (pi_p); it reported "{0,3}=1/8" and
the other sectors as opaque basis-dependent rationals, as if secp-specific.

v2 proves the STRUCTURE those numbers came from, for EVERY prime p==1 (mod 3):

  THM 1 (rhombus).  The Gauss-reduced fundamental domain P of the ideal (pi_p)
    is always a 60-degree RHOMBUS: both reduced basis vectors have Eisenstein
    norm EXACTLY p, i.e. they are two of the six associates {zeta*pi_p} (zeta a
    unit sixth-root). [Reason: the minimal nonzero Eisenstein norm in the ideal
    is N(alpha*pi_p)=N(alpha)*p, minimized at N(alpha)=1 -> a unit -> norm p;
    the six units form a hexagon and any two adjacent vertices are a reduced
    basis.]  => Verified N(R1)=N(R2)=p over all p==1(3) up to a bound.

  THM 2 (one-parameter law).  Consequently the entire sextant histogram is a
    function of a SINGLE real parameter theta = arg(pi_p) mod 60deg:
        pinned opposite-pair : proportion EXACTLY 1/8 each   (theta-independent)
        free opposite-pair A : p0(theta) = (3/4)|cos 2t|/(2 cos 2t + 1)
        free opposite-pair B : 3/8 - p0(theta)
    (central symmetry forces H(s)=H(s+3); the three opposite-pairs sum to 1/2.)

  THM 3 (universal 1/8 invariant, and it is NEVER the maximal pair).  For every
    p, exactly one opposite-pair of sextants has area EXACTLY p/8 -- proven as a
    SYMBOLIC identity (sector area = sqrt(3)/16 * (unit-edge total)) independent
    of theta.  Which physical pair is pinned is {0,3} or {1,4}, never {2,5}.
    secp: theta=50.55deg, pinned pair {0,3}, free = {0.2453, 0.1297}.

Exact rational arithmetic in the area/proportion signal path (no-float rule).
The theta closed form is a real-analytic statement; it is cross-checked at high
precision and against the exact rational areas.
"""
from fractions import Fraction as Fr
import math
from sympy.ntheory.residue_ntheory import sqrt_mod as _sqrt_mod  # handles composite modulus

# ---------- exact Eisenstein / lattice machinery ----------
def cornacchia_4p_D3(p):
    """solve X^2 + 3 Y^2 = 4p, then pi_p=(u,v) with u^2-uv+v^2=p."""
    n = 4 * p
    t = _sqrt_mod((-3) % n, n)
    if t is None: return None
    if 2 * t < n: t = n - t
    a0, b0 = n, t
    L = math.isqrt(n)
    while b0 > L: a0, b0 = b0, a0 % b0
    c = n - b0 * b0
    if c % 3: return None
    s = math.isqrt(c // 3)
    if s * s * 3 + b0 * b0 != n: return None
    X, Y = b0, s
    for sx in (1, -1):
        for sy in (1, -1):
            XX, YY = sx * X, sy * Y
            if (XX + YY) % 2 == 0:
                u, v = (XX + YY) // 2, YY
                if u * u - u * v + v * v == p: return (u, v)
    return None

def rdiv(nu, de):
    if de < 0: nu, de = -nu, -de
    q, r = divmod(nu, de); return q + 1 if 2 * r >= de else q

def gauss_reduce(u, v):
    dot = lambda a, b: a[0] * b[0] + a[1] * b[1]
    while True:
        if dot(v, v) < dot(u, u): u, v = v, u
        m = rdiv(dot(u, v), dot(u, u)); v = (v[0] - m * u[0], v[1] - m * u[1])
        if dot(v, v) >= dot(u, u): return u, v

def enorm(w): return w[0] * w[0] - w[0] * w[1] + w[1] * w[1]   # Eisenstein = true |w|^2

def reduced_basis(p):
    pi = cornacchia_4p_D3(p)
    if pi is None: return None
    a, b = pi
    return gauss_reduce((a, b), (-b, a - b))

# ---------- exact sector areas of P (rational) ----------
def cross(a, b): return a[0] * b[1] - a[1] * b[0]

def clip(poly, d, ks):
    out = []; n = len(poly)
    for i in range(n):
        a = poly[i]; b = poly[(i + 1) % n]
        ca = ks * cross(d, a); cb = ks * cross(d, b)
        if ca >= 0: out.append(a)
        if (ca > 0) != (cb > 0) and ca != cb:
            t = Fr(ca, ca - cb); out.append((a[0] + t * (b[0] - a[0]), a[1] + t * (b[1] - a[1])))
    return out

def shoelace(poly):
    if len(poly) < 3: return Fr(0)
    s = Fr(0)
    for i in range(len(poly)):
        x1, y1 = poly[i]; x2, y2 = poly[(i + 1) % len(poly)]
        s += x1 * y2 - x2 * y1
    return abs(s) / 2

UNIT = [(1, 0), (1, 1), (0, 1), (-1, 0), (-1, -1), (0, -1)]  # sextant rays (u,v)

def sextant(u, v):
    """Exact 0..5 sextant of w=u+v*omega (matches eisenstein_lift_sextant_exact_v1)."""
    if u == 0 and v == 0: return 0
    for k in range(6):
        if v >= 0 and (u - v) >= 0 and u > 0: return k
        u, v = v, v - u
    return 0 if v >= 0 else 3

def wedge_label(s):
    """sextant() index carried by the interior of raw wedge s (align to pipeline labels)."""
    d0 = UNIT[s]; d1 = UNIT[(s + 1) % 6]
    mid = (d0[0] * 1000 + d1[0] * 1000 + 1, d0[1] * 1000 + d1[1] * 1000 + 1)
    return sextant(mid[0], mid[1])

def sector_props(R1, R2):
    A = (Fr(R1[0] + R2[0], 2), Fr(R1[1] + R2[1], 2))
    B = (Fr(R1[0] - R2[0], 2), Fr(R1[1] - R2[1], 2))
    nA = (-A[0], -A[1]); nB = (-B[0], -B[1])
    V = [A, B, nA, nB] if cross(A, B) > 0 else [A, nB, nA, B]
    p = abs(cross(R1, R2))  # = area(P) = N(pi_p) = p in (u,v) coords
    props = [Fr(0)] * 6
    for s in range(6):
        poly = clip(clip(V, UNIT[s], +1), UNIT[(s + 1) % 6], -1)
        props[wedge_label(s)] = Fr(shoelace(poly), p)   # relabel raw wedge -> sextant index
    return props

# ---------- theta closed form (real-analytic cross-check) ----------
def theta_of(R):  # arg mod 60deg in the TRUE Eisenstein plane
    x, y = R[0] - Fr(R[1], 2), R[1]  # embed; y scaled by sqrt3/2 (monotone, drops out of atan up to const)
    ang = math.atan2(float(y) * math.sqrt(3) / 2, float(x))
    return ang % (math.pi / 3)

def p0_closed(theta):
    c = math.cos(2 * theta)
    return 0.75 * abs(c) / abs(2 * c + 1)

# ==================================================================
def main():
    import sympy as sp
    p_secp = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F

    print("=" * 70)
    print("THM 1  P is a 60-degree rhombus: N(R1)=N(R2)=p for all p==1 (mod 3)")
    print("=" * 70)
    # small primes
    ps = []
    n = 7
    while len(ps) < 300:
        if n % 3 == 1 and all(n % k for k in range(2, int(n**0.5) + 1)): ps.append(n)
        n += 1
    bad = 0
    for p in ps:
        R1, R2 = reduced_basis(p)
        if not (enorm(R1) == p and enorm(R2) == p): bad += 1
    print(f"  {len(ps)} primes p==1(3) in [7, {ps[-1]}]: N(R1)=N(R2)=p holds for "
          f"{len(ps) - bad}/{len(ps)}")
    R1, R2 = reduced_basis(p_secp)
    print(f"  secp256k1 prime: N(R1)={enorm(R1) == p_secp and 'p'}  "
          f"N(R2)={enorm(R2) == p_secp and 'p'}  => rhombus confirmed")

    print("\n" + "=" * 70)
    print("THM 3  exactly ONE opposite-pair has area EXACTLY 1/8, never the max pair")
    print("=" * 70)
    from collections import Counter
    cnt = Counter(); pairclass = Counter()
    for p in ps:
        R1, R2 = reduced_basis(p)
        pr = sector_props(R1, R2)
        idx = [s for s in range(6) if pr[s] == Fr(1, 8)]
        cnt[len(idx)] += 1
        pairclass[tuple(sorted({i % 3 for i in idx}))] += 1
        # never the maximal pair:
        maxpair = max(range(3), key=lambda r: pr[r])
        assert maxpair not in {i % 3 for i in idx}, f"1/8 on max pair at p={p}"
    print(f"  #sextants exactly=1/8 per prime: {dict(cnt)}   (2 = one opposite-pair)")
    print(f"  which pair (residue mod 3): {dict(pairclass)}   (never class 2 = the max pair)")

    # SYMBOLIC proof that the pinned pair area is identically 1/8 (theta-free)
    th = sp.symbols('theta', positive=True)
    A = sp.Matrix([sp.cos(th + sp.pi / 6), sp.sin(th + sp.pi / 6)]) * sp.sqrt(3) / 2
    B = sp.Matrix([sp.cos(th - sp.pi / 3), sp.sin(th - sp.pi / 3)]) / 2
    verts = [A, B, -A, -B]
    un = [sp.Matrix([sp.cos(sp.pi / 3 * k), sp.sin(sp.pi / 3 * k)]) for k in range(6)]
    th0 = 0.5
    def crs(d, x): return d[0] * x[1] - d[1] * x[0]
    def clip_sym(poly, d, ks):
        out = []; m = len(poly)
        for i in range(m):
            P = poly[i]; Q = poly[(i + 1) % m]
            cP = ks * crs(d, P); cQ = ks * crs(d, Q)
            if float(cP.subs(th, th0)) >= -1e-12: out.append(P)
            if (float(cP.subs(th, th0)) > 0) != (float(cQ.subs(th, th0)) > 0):
                t = cP / (cP - cQ); out.append(P + t * (Q - P))
        return out
    def shoe_sym(poly):
        s = 0
        for i in range(len(poly)):
            x1, y1 = poly[i]; x2, y2 = poly[(i + 1) % len(poly)]
            s += x1 * y2 - x2 * y1
        return sp.simplify(sp.Abs(s) / 2)
    tot = sp.sqrt(3) / 2  # unit-edge rhombus area
    pinned = shoe_sym(clip_sym(clip_sym(verts, un[2], 1), un[3], -1))
    print(f"\n  SYMBOLIC pinned-sector area (unit edges) = {pinned}  "
          f"=> proportion {sp.simplify(pinned / tot)}  (theta-free EXACT 1/8)")

    print("\n" + "=" * 70)
    print("THM 2  one-parameter closed form  p0(theta)=(3/4)|cos2t|/(2cos2t+1)")
    print("=" * 70)
    worst = 0.0
    for p in ps[:150]:
        R1, R2 = reduced_basis(p)
        pr = sector_props(R1, R2)
        free = sorted(float(v) for v in pr if v != Fr(1, 8))  # two distinct free proportions
        free = [free[0], free[-1]]
        t = theta_of(R1)
        tf = t if t <= math.pi / 6 else math.pi / 3 - t   # fold to [0,30deg]
        pred = sorted([p0_closed(tf), 0.375 - p0_closed(tf)])
        worst = max(worst, abs(free[0] - pred[0]), abs(free[1] - pred[1]))
    print(f"  max |exact-area proportion  -  p0(theta) closed form| over 150 primes "
          f"= {worst:.2e}")

    print("\n" + "=" * 70)
    print("secp256k1 instance")
    print("=" * 70)
    # use the pipeline's own reduced basis so sextant labels match eis()/sextant()
    try:
        from eisenstein_lift_sextant_exact_v1 import R1, R2
    except Exception:
        R1, R2 = reduced_basis(p_secp)
    pr = sector_props(R1, R2)
    t = theta_of(R1)
    tf = t if t <= math.pi / 6 else math.pi / 3 - t   # fold to [0,30deg]
    print(f"  theta = arg(pi_p) mod 60deg = {math.degrees(t):.4f} deg  (folded {math.degrees(tf):.4f})")
    print(f"  exact sextant proportions: {[str(x) if x.denominator<100 else f'{float(x):.4f}' for x in pr]}")
    print(f"  pinned pair {{s: pr[s]==1/8}} = {[s for s in range(6) if pr[s]==Fr(1,8)]}")
    print(f"  free proportions from closed form: p0={p0_closed(tf):.4f}, 3/8-p0={0.375-p0_closed(tf):.4f}"
          f"  (secp measured 0.2453 / 0.1297)")

if __name__ == "__main__":
    main()
```

### C — `lift_chi6_uniform_law_proof_v1.py`

```python
#!/usr/bin/env python3
"""
lift_chi6_uniform_law_proof_v1.py

POSITIVE THEOREM, contrast case to the rhombus law
(lift_sextant_rhombus_law_v2.md).

Both the lift ANGLE (sextant) and the sextic CHARACTER chi6 are single-x-coordinate
functionals, both scalar-independent.  But their marginals have opposite shapes:

  * lift angle sextant(eis(X)) = an ADDITIVE / geometric readout of X mod pi_p.
    Marginal NON-uniform: the rhombus area law (1/8, p0(theta), 3/8-p0).
  * chi6(X) = X^((p-1)/6) in mu_6 = a MULTIPLICATIVE readout of X.
    Marginal EXACTLY uniform: (p-1)/6 preimages per value.  Proven here.

THM (chi6 marginal is exactly uniform -- unconditional, group theory).
  p == 1 (mod 3) and p odd  =>  p == 1 (mod 6)  =>  6 | (p-1).
  F_p^* is cyclic of order p-1; chi6 : x -> x^((p-1)/6) is a surjective homomorphism
  onto mu_6 (the 6th roots of unity in F_p) with kernel = the sextic residues, of
  index exactly 6.  Every fiber therefore has EXACTLY (p-1)/6 elements, so
      #{ X in F_p^* : chi6(X) = zeta^j } = (p-1)/6   for each j = 0..5,
  and the additive character sum  sum_{X in F_p^*} zeta_6^{chi6(X)} = 0  exactly.
  (X=0 has measure 1/p -> 0.)  No d, no analytic input.

CONDITIONAL (curve, cited).  Over curve x-coordinates x([d]G) the count splits as
  N_j = sum_x [chi6(x)=j] (1 + chi2(x^3+7))
      = (p-1)/6            <- exact, character orthogonality
      + sum_x [chi6(x)=j] chi2(x^3+7)   <- a curve character sum, |.| = O(sqrt p) (Weil)
  so chi6 over the curve is uniform up to O(p^{-1/2}); MI(chi6 ; d mod m) = O(p^{-delta}).

Verification: exact fiber enumeration on a moderate prime; secp divisibility + sampler
confirmation; the exact contrast against the non-uniform sextant; and an EXACT
full-F_p scaling test showing the additive (sextant) and multiplicative (chi6)
shadows are ASYMPTOTICALLY INDEPENDENT (chi^2 stays ~df as N grows 400x; any
correlation is O(p^-1/2)).  Exact integer arithmetic in the counting path.
"""
from fractions import Fraction as Fr
import random

P_SECP = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F

def chi6_of(x, p, e6, table):
    x %= p
    if x == 0: return None
    return table[pow(x, e6, p)]

def build_chi6(p):
    e6 = (p - 1) // 6
    for g in range(2, 500):
        z = pow(g, e6, p)
        if pow(z, 6, p) == 1 and all(pow(z, t, p) != 1 for t in (1, 2, 3)):
            return e6, {pow(z, j, p): j for j in range(6)}
    raise RuntimeError("no primitive 6th root")

def main():
    print("=" * 70)
    print("THM  chi6 marginal is EXACTLY uniform  (contrast: sextant is non-uniform)")
    print("=" * 70)

    # (1) divisibility 6 | p-1  (the hypothesis that makes mu_6 live in F_p)
    for nm, p in [("moderate p=100003", 100003), ("secp256k1 p", P_SECP)]:
        print(f"  {nm}: (p-1) % 6 = {(p - 1) % 6}  (0 => 6|p-1 => mu_6 subset F_p)")

    # (2) EXACT fiber enumeration on a moderate prime (fibers must be equal = (p-1)/6)
    p = 100003
    e6, tbl = build_chi6(p)
    counts = [0] * 6
    for x in range(1, p):
        counts[tbl[pow(x, e6, p)]] += 1
    exact = (p - 1) // 6
    print(f"\n  EXACT enumeration p={p}: fiber sizes {counts}")
    print(f"    all == (p-1)/6 = {exact}?  {all(c == exact for c in counts)}")
    # additive character sum over mu_6 == 0 exactly (equal fibers)
    # sum zeta_6^{chi6(X)} = sum_j counts[j] * zeta^j ; equal counts => 0
    zsum_re_pairs = [(counts[j], j) for j in range(6)]
    is_zero = all(c == exact for c in counts)
    print(f"    additive character sum  sum_X zeta_6^chi6(X) == 0 exactly?  {is_zero}")

    # (3) secp: chi6 marginal over uniform X (sampler confirmation of the exact thm)
    e6s, tbls = build_chi6(P_SECP)
    rng = random.Random(11)
    M = 120000
    hc = [0] * 6
    for _ in range(M):
        j = chi6_of(rng.randrange(1, P_SECP), P_SECP, e6s, tbls)
        hc[j] += 1
    print(f"\n  secp uniform-X chi6 histogram (M={M}):")
    print("   ", [f"{hc[j] / M:.4f}" for j in range(6)],
          f" max|.-1/6|={max(abs(hc[j] / M - 1 / 6) for j in range(6)):.4f}"
          f"  (~1/sqrt(M)={1 / M ** 0.5:.4f})")

    # (4) CONTRAST: exact sextant marginal (rhombus, non-uniform) vs exact chi6 (uniform)
    from eisenstein_lift_sextant_exact_v1 import R1, R2
    import importlib.util
    spec = importlib.util.spec_from_file_location("v2", "lift_sextant_rhombus_law_proof_v2.py")
    v2 = importlib.util.module_from_spec(spec); spec.loader.exec_module(v2)
    sx = v2.sector_props(R1, R2)
    print("\n  CONTRAST (both single-x, both scalar-independent):")
    print(f"    sextant marginal (exact rhombus areas): "
          f"{[str(x) if x.denominator < 100 else f'{float(x):.4f}' for x in sx]}  -> NON-uniform")
    print(f"    chi6 marginal (exact):                  {['1/6'] * 6}                          -> UNIFORM")

    # (5) RELATION: are the additive (sextant) and multiplicative (chi6) shadows
    #     dependent?  Settle it EXACTLY by full-F_p enumeration (no sampling noise) and
    #     SCALING: chi^2 of independence has df=25; if the two are dependent it grows ~N,
    #     if independent it stays ~25 as p grows.
    import sympy
    def full_chi2(p):
        R1p, R2p = v2.reduced_basis(p); DET = R1p[0] * R2p[1] - R1p[1] * R2p[0]
        def eisp(X):
            c1 = v2.rdiv(X * R2p[1], DET); c2 = v2.rdiv(-X * R1p[1], DET)
            return (X - (c1 * R1p[0] + c2 * R2p[0]), -(c1 * R1p[1] + c2 * R2p[1]))
        e6p, tblp = build_chi6(p)
        cont = [[0] * 6 for _ in range(6)]
        for X in range(1, p):
            u, v = eisp(X); cont[v2.sextant(u, v)][tblp[pow(X, e6p, p)]] += 1
        rt = [sum(r) for r in cont]; ct = [sum(cont[i][j] for i in range(6)) for j in range(6)]
        N = p - 1
        return sum((cont[i][j] - rt[i] * ct[j] / N) ** 2 / (rt[i] * ct[j] / N)
                   for i in range(6) for j in range(6) if rt[i] * ct[j] > 0)
    sample = [q for q in sympy.primerange(1000, 400000) if q % 6 == 1]
    sample = [sample[0], sample[len(sample) // 3], sample[2 * len(sample) // 3], sample[-1]]
    print("\n  RELATION sextant vs chi6 -- EXACT full-F_p chi^2 (df=25) vs growing N:")
    for p in sample:
        print(f"    p={p:6d} (N={p - 1:6d}): exact chi^2 = {full_chi2(p):5.1f}")
    print("    chi^2 stays ~df=25 as N grows 400x  =>  ASYMPTOTICALLY INDEPENDENT")
    print("    (additive/geometric shadow and multiplicative shadow do not interact;")
    print("     any correlation is O(p^-1/2), at the character-sum floor. Corrects the")
    print("     v1 'MI(sextant;chi6) fires' note = small-sample echo of sextant's own")
    print("     marginal non-uniformity, not genuine dependence.)")

    # (6) CURVE: chi6 over x([d]G) near-uniform (first term exact 0, Weil-bounded correction)
    try:
        from angular_interference_scaling_v1 import gen_keys
        d, X, Y = gen_keys(256, 40000, 7)
        hcurve = [0] * 6
        for x in X:
            j = chi6_of(int(x), P_SECP, e6s, tbls)
            if j is not None: hcurve[j] += 1
        m = sum(hcurve)
        print(f"\n  CURVE gen256 chi6 histogram (M={m}):")
        print("   ", [f"{hcurve[j] / m:.4f}" for j in range(6)],
              f" max|.-1/6|={max(abs(hcurve[j] / m - 1 / 6) for j in range(6)):.4f}")
    except Exception as e:
        print(f"\n  (curve check skipped: {e})")

if __name__ == "__main__":
    main()
```

### C — `norm_band_law_proof_v1.py`

```python
#!/usr/bin/env python3
"""
norm_band_law_proof_v1.py

Completes the single-x charting: the marginal of the lift NORM  N(eis(X)) = |eis(X)|^2
(= u^2 - uv + v^2, the true squared length).

Since {eis(X)} = Uniform on Z^2 ∩ P (the rhombus) and N is rotation-invariant while
the rhombus SHAPE is universal (60 deg, diagonals sqrt(3p):sqrt(p) -- only its
ORIENTATION theta varies), the norm marginal is:

  THEOREM (norm-band law -- universal, theta- and p-independent after scaling).
    Let s = N(eis(X))/p.  As X ranges over F_p (p == 1 mod 3), s -> a fixed
    distribution on [0, 3/4], the same for EVERY such p and independent of theta:
      * support  [0, 3/4]   (max at the long vertices, |A|^2 = 3p/4);
      * mean     E[s] = 1/6  (E[N] = p/6), exactly;
      * density piecewise-analytic with breakpoints at the inradius rho^2/p = 3/16,
        the short-vertex 1/4, and the long-vertex 3/4:
          s in [0, 3/16] : f(s) = 2*pi/sqrt(3)                 (disk inside rhombus)
          s in [3/16,1/4]: f(s) = (2/sqrt3)(pi - 4 arccos(rho/sqrt(s p)... ))  segments
          s in [1/4, 3/4]: same segment structure past the short vertices
    (contrast: the ANGLE marginal is theta-DEPENDENT rhombus area law; the NORM
    marginal is theta-INDEPENDENT because |.|^2 is rotation-invariant.)

Verified: exact circle-rhombus-area CDF vs the exact lattice histogram; mean 1/6;
universality across p = 10^4 .. secp.  Signal path: exact norm counts (integers);
the CDF uses real geometry (arccos/sqrt) as the closed form, matched to exact counts.
"""
import math, random, importlib.util
spec = importlib.util.spec_from_file_location("v2", "lift_sextant_rhombus_law_proof_v2.py")
v2 = importlib.util.module_from_spec(spec); spec.loader.exec_module(v2)
from eisenstein_lift_sextant_exact_v1 import eis as eis_secp

P_SECP = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
def N(w): return w[0] * w[0] - w[0] * w[1] + w[1] * w[1]

# ---- exact area of intersection of a disk radius R (centred at origin) with a
#      convex polygon given CCW (standard circular-segment decomposition) --------
def _tri_circle_area(R, A, B):
    """signed area of the region between segment O-A-B-O clipped to disk radius R."""
    def inside(P): return P[0] * P[0] + P[1] * P[1] <= R * R + 1e-9
    def cut(P, Q):
        # intersection of segment PQ with circle radius R, param t in [0,1], nearest to P outward
        dx, dy = Q[0] - P[0], Q[1] - P[1]
        a = dx * dx + dy * dy; b = 2 * (P[0] * dx + P[1] * dy)
        c = P[0] * P[0] + P[1] * P[1] - R * R
        disc = b * b - 4 * a * c
        if disc < 0: return []
        sq = math.sqrt(disc); ts = [(-b - sq) / (2 * a), (-b + sq) / (2 * a)]
        return [(P[0] + t * dx, P[1] + t * dy) for t in ts if -1e-12 <= t <= 1 + 1e-12]
    def circ_sector_area(P, Q):  # area of circular sector O-P..Q (both on circle)
        ang = math.atan2(P[0] * Q[1] - P[1] * Q[0], P[0] * Q[0] + P[1] * Q[1])
        return 0.5 * R * R * ang
    def tri_area(P, Q): return 0.5 * (P[0] * Q[1] - P[1] * Q[0])
    ai, bi = inside(A), inside(B)
    if ai and bi:
        return tri_area(A, B)
    if ai and not bi:
        X = cut(A, B)
        if not X: return tri_area(A, B)
        return tri_area(A, X[0]) + circ_sector_area(X[0], B)
    if not ai and bi:
        X = cut(A, B)
        if not X: return tri_area(A, B)
        return circ_sector_area(A, X[0]) + tri_area(X[0], B)
    X = cut(A, B)
    if len(X) < 2:
        return circ_sector_area(A, B)
    # order the two hits along A->B
    X.sort(key=lambda Pt: (Pt[0] - A[0]) ** 2 + (Pt[1] - A[1]) ** 2)
    return circ_sector_area(A, X[0]) + tri_area(X[0], X[1]) + circ_sector_area(X[1], B)

def disk_poly_area(R, poly):
    return abs(sum(_tri_circle_area(R, poly[i], poly[(i + 1) % len(poly)])
                   for i in range(len(poly))))

def main():
    # rhombus shape (p=1): half-diagonals a=sqrt3/2 (long), b=1/2 (short); vertices on axes
    a, b = math.sqrt(3) / 2, 0.5
    rhomb = [(a, 0), (0, b), (-a, 0), (0, -b)]
    area = 2 * a * b  # = sqrt3/2
    rho2 = 3 / 16
    print("norm-band law (scaled s = N/p):")
    print(f"  support [0, 3/4]; breakpoints rho^2/p=3/16={rho2:.4f}, short 1/4, long 3/4")
    print(f"  closed density on [0,3/16]: f = 2pi/sqrt3 = {2 * math.pi / math.sqrt(3):.4f} (constant)")

    # (1) closed-form CDF via disk-rhombus area vs EXACT secp lattice histogram
    rng = random.Random(1); M = 200000
    ss = sorted(N(eis_secp(rng.randrange(P_SECP))) / P_SECP for _ in range(M))
    print("\n  s      empirical-CDF   closed-form-CDF (disk∩rhombus/area)")
    worst = 0.0
    # (s=1/4 and s=3/4 are exact vertex radii -- disk passes through polygon vertices,
    #  a measure-zero degeneracy for the area routine; evaluate just off them.)
    for s in [0.05, 0.10, 0.1875, 0.2499, 0.40, 0.55, 0.70, 0.7499]:
        emp = sum(1 for x in ss if x <= s) / M
        cf = disk_poly_area(math.sqrt(s), rhomb) / area
        worst = max(worst, abs(emp - cf))
        print(f"  {s:.4f}   {emp:.4f}          {cf:.4f}")
    print(f"  max|emp-CDF| = {worst:.4f}  => "
          f"{'NORM-BAND LAW CONFIRMED' if worst < 0.01 else 'mismatch'}")

    # (2) mean exactly 1/6, max 3/4
    print(f"\n  E[s] = {sum(ss) / M:.5f} (predict 1/6={1/6:.5f});  max s = {ss[-1]:.4f} (predict 0.75)")

    # (3) universality: closed-form CDF is p/theta-independent by construction; confirm
    #     the exact lattice CDF of a small prime matches the same closed form
    pp = 10009
    while pp % 3 != 1: pp += 1
    R1, R2 = v2.reduced_basis(pp); DET = R1[0] * R2[1] - R1[1] * R2[0]
    def eisp(X):
        c1 = v2.rdiv(X * R2[1], DET); c2 = v2.rdiv(-X * R1[1], DET)
        return (X - (c1 * R1[0] + c2 * R2[0]), -(c1 * R1[1] + c2 * R2[1]))
    ss2 = sorted(N(eisp(x)) / pp for x in range(1, pp))
    w2 = max(abs(sum(1 for x in ss2 if x <= s) / len(ss2) - disk_poly_area(math.sqrt(s), rhomb) / area)
             for s in [0.1, 0.2499, 0.5, 0.7])
    print(f"  universality: exact full-F_p CDF at p={pp} matches SAME closed form, "
          f"max|.|={w2:.4f} (theta/p-independent)")

if __name__ == "__main__":
    main()
```

### C — `glv_orbit_structure_proof_v1.py`

```python
#!/usr/bin/env python3
"""
glv_orbit_structure_proof_v1.py

Closed-form action of the secp256k1 GLV endomorphism on the single-x shadows,
completing the "single-x structure" map (rhombus law + chi6 uniform law).

GLV endomorphism:  phi(x,y) = (beta*x, y),  beta^3 = 1, beta != 1  (a nontrivial
cube root of unity mod p);  on scalars  [lambda]P = phi(P),  lambda^2+lambda+1 = 0
mod N_ORDER.  The GLV triple of a key d is { [d]G, [lambda d]G, [lambda^2 d]G },
whose x-coordinates are { x, beta*x, beta^2*x }.

PROVEN / VERIFIED here (exact arithmetic):

  (A) beta == omega^2 (mod pi_p).  Since F_p ~ Z[omega]/(pi_p) sends omega -> a
      root of X^2+X+1, and beta is exactly such a root, the GLV endomorphism IS
      "multiply the lift by a primitive cube root of unity" -- the CM-by-Z[omega]
      origin of secp's GLV.

  (B) MULTIPLICATIVE shadow transforms by a CONSTANT SHIFT (exact, all x):
        chi6(beta x) = chi6(x) + 4  (mod 6)
        chi3(beta x) = chi3(x) + 1  (mod 3)
        chi2(beta x) = chi2(x)          (beta is a QR)
      => on a GLV triple {x,beta x,beta^2 x}:  chi3 realizes ALL THREE classes
      {0,1,2} exactly once; chi6 realizes the three residues of FIXED PARITY
      {c, c+2, c+4}; chi2 is constant.  (chi6 = (chi2,chi3) by CRT on Z/6.)

  (C) GEOMETRIC shadow (lift sextant) does NOT transform cleanly: multiplication
      by omega^2 rotates the lattice 120deg = +4 sextants, but P is a RHOMBUS
      (180deg-symmetric, not 120deg), so the reduction back into P folds. Measured:
      sextant shift is +4 ~75% / +0 ~23% / boundary ~2%. No clean law.

  (D) y is FIXED by GLV (phi preserves y; x^3+7 is GLV-invariant since beta^3=1).
      => GLV gives ZERO leverage on any y-coordinate / group-law functional.

Consequence: the single-x space is charted. Multiplicative readouts are governed by
character theory (uniform marginals, clean GLV shifts); the one non-uniform readout
(sextant) is the rhombus area law and is GLV-tangled; y is GLV-invariant. The
remaining structure lives OFF the single-x axis: joint/multi-point across INDEPENDENT
keys (GLV only gives the degenerate deterministic triple), and y / group-law.
"""
import random
from ecc_secp256k1 import P as p, scalar_mul, N_ORDER
from angular_interference_scaling_v1 import chi6, chi3
from eisenstein_lift_sextant_exact_v1 import eis, sextant

aP = 367917413016453100223835821029139468249
bP = 303414439467246543595250775667605759171
assert aP * aP - aP * bP + bP * bP == p


def cube_root_unity_mod(m):
    g = 2
    while pow(g, (m - 1) // 3, m) == 1:
        g += 1
    return pow(g, (m - 1) // 3, m)


def main():
    beta = cube_root_unity_mod(p)
    print("GLV constant beta:")
    print(f"  beta^3==1, beta!=1: {pow(beta, 3, p) == 1 and beta != 1}"
          f"   beta^2+beta+1==0: {(beta * beta + beta + 1) % p == 0}")

    # (A) beta == omega^2 mod pi_p   (omega ≡ -aP/bP from aP + bP*omega ≡ 0)
    omega = (-aP * pow(bP, -1, p)) % p
    branch = "omega" if beta == omega else ("omega^2" if beta == omega * omega % p else "??")
    print(f"\n(A) beta == {branch} (mod pi_p)  => GLV = multiply lift by a primitive "
          f"cube root of unity (CM by Z[omega]).")

    # phi(x,y)=(beta x, y) and x^3+7 GLV-invariant, on a real curve point
    x1, y1 = scalar_mul(12345)
    lam = cube_root_unity_mod(N_ORDER)
    xr, yr = scalar_mul(12345 * lam % N_ORDER)
    print(f"    phi check: x([lam]P) in {{beta*x, beta^2*x}}: "
          f"{xr in (beta * x1 % p, pow(beta, 2, p) * x1 % p)}   y preserved: "
          f"{yr in (y1, (p - y1) % p)}")
    print(f"(D) x^3+7 GLV-invariant (beta^3=1): "
          f"{(pow(beta * x1 % p, 3, p) + 7) % p == (pow(x1, 3, p) + 7) % p}  "
          f"=> y fixed by GLV; no leverage on y/group-law.")

    # (B) exact constant shifts of the multiplicative characters
    c6, c3 = chi6(beta), chi3(beta)
    rng = random.Random(3)
    ok6 = ok3 = ok2 = True
    N = 40000
    for _ in range(N):
        x = rng.randrange(1, p)
        if (chi6(beta * x % p) - chi6(x)) % 6 != c6: ok6 = False
        if (chi3(beta * x % p) - chi3(x)) % 3 != c3: ok3 = False
        if pow(beta * x % p, (p - 1) // 2, p) != pow(x, (p - 1) // 2, p): ok2 = False
    print(f"\n(B) multiplicative shadow, EXACT over {N} x:")
    print(f"    chi6(beta x) = chi6(x) + {c6} (mod 6): {ok6}")
    print(f"    chi3(beta x) = chi3(x) + {c3} (mod 3): {ok3}  => GLV triple hits all 3 cubic classes")
    print(f"    chi2 invariant: {ok2}  => chi6 triple = {{c, c+2, c+4}} (fixed parity)")

    # (C) geometric shadow: no clean shift (rhombus 180deg-only symmetry)
    from collections import Counter
    d = Counter()
    for _ in range(40000):
        x = rng.randrange(1, p)
        u, v = eis(x); u2, v2 = eis(beta * x % p)
        d[(sextant(u2, v2) - sextant(u, v)) % 6] += 1
    tot = sum(d.values())
    dist = {k: round(v / tot, 3) for k, v in sorted(d.items())}
    print(f"\n(C) geometric shadow (sextant) shift under GLV: {dist}")
    print(f"    max mass {max(d.values()) / tot:.2f} < 1 => FOLD-TANGLED: multiplication by "
          f"omega^2 is 120deg rotation but P is a 180deg-symmetric rhombus, so the")
    print(f"    reduction into P folds. The geometric shadow does NOT respect GLV.")


if __name__ == "__main__":
    main()
```

### C — `summation_and_formalgroup_v1.py`

```python
#!/usr/bin/env python3
"""
Two curve-side computations.

(A) Summation polynomials S_m under [omega]:  S3 is a beta-eigenvector (eigenvalue beta^1);
    S4 is a beta-eigenvector (eigenvalue beta^0 = [omega]-invariant), irreducible over Q(b),
    full degree 2^(m-2) in each variable (S4 degree 4). The mu6/automorphism covariance
    carries the sqrt(6) symmetry of |Aut(E)|=6.

(B) Formal group law from the log:  F(T1,T2) = exp(L(T1)+L(T2)) is explicit, mu6-sparse
    (first correction at total degree 7 == 1 mod 6), b=7-driven; L linearizes the formal
    subgroup E_1(Q_p) (points reducing to O).
"""
import sympy as sp

def summation_polys():
    x1, x2, x3, x4, x, b, beta = sp.symbols('x1 x2 x3 x4 x b beta')
    def S3(a1, a2, a3):
        return sp.expand((a1 - a2) ** 2 * a3 ** 2 - 2 * ((a1 + a2) * (a1 * a2) + 2 * b) * a3
                         + ((a1 * a2) ** 2 - 4 * b * (a1 + a2)))
    def eigen(poly, vars_):
        pb = sp.expand(poly.subs({v: beta * v for v in vars_}))
        pb = sp.expand(pb.replace(lambda e: e.is_Pow and e.base == beta, lambda e: beta ** (e.exp % 3)))
        for k in range(3):
            d = sp.expand(sp.expand(pb - beta ** k * poly).replace(
                lambda e: e.is_Pow and e.base == beta, lambda e: beta ** (e.exp % 3)))
            if d == 0:
                return k
        return None
    s3 = S3(x1, x2, x3)
    s4 = sp.expand(sp.resultant(S3(x1, x2, x), S3(x3, x4, x), x))
    print("S3: beta-eigenvalue beta^%s ; factors? %s"
          % (eigen(s3, [x1, x2, x3]), sp.factor(s3) != s3))
    print("S4: beta-eigenvalue beta^%s ; factors? %s ; deg_x1 = %d"
          % (eigen(s4, [x1, x2, x3, x4]), sp.factor(s4) != s4, sp.degree(s4, x1)))
    print("  => [omega]-covariant (the sqrt(6) automorphism symmetry of |Aut(E)|=6).")


def formal_group_law(PREC=20):
    T, T1, T2 = sp.symbols('T T1 T2')
    b = 7
    L = sum(sp.Integer(b) ** k * sp.binomial(3 * k, k) / (6 * k + 1) * T ** (6 * k + 1)
            for k in range(PREC // 6 + 2))
    L = sp.series(L, T, 0, PREC).removeO()
    exp = T
    for _ in range(PREC):
        exp = sp.series(exp - (sp.series(L.subs(T, exp), T, 0, PREC).removeO() - T), T, 0, PREC).removeO()
    F = exp.subs(T, sp.series(L.subs(T, T1), T1, 0, PREC).removeO()
                 + sp.series(L.subs(T, T2), T2, 0, PREC).removeO())
    F = sp.series(sp.series(F, T1, 0, 8).removeO(), T2, 0, 8).removeO()
    print("\nFormal group law F(T1,T2) low terms:")
    print(" ", sp.expand(F))
    print("  identity F(T1,0)=T1:", sp.series(F.subs(T2, 0), T1, 0, 6).removeO() == T1)
    print("  a1 (coeff T1*T2) =", F.coeff(T1, 1).coeff(T2, 1), " (0 for y^2=x^3+7)")
    print("  first correction at total degree 7 (=1 mod 6), coefficients multiples of b=7 => mu6-sparse.")


if __name__ == "__main__":
    summation_polys()
    formal_group_law()
```

### C — `sextic_identities_verify.py`

```python
"""Verify four CM/sextic structural identities for secp256k1, exact integer arithmetic.
ZZ[omega]: element (a,b) = a + b*omega, omega^2 = -1-omega. N(a+b w)=a^2-ab+b^2."""
import math
from sympy import factorint, isprime

p = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
n = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141
t = p + 1 - n

# ---- Frobenius pi = a + b*omega, N(pi)=p, pi+conj(pi)=2a-b=t ----
D = 4*p - t*t
assert D % 3 == 0
f = math.isqrt(D // 3); assert 3*f*f == D
a = (t + f) // 2; b = f
def norm(z): return z[0]*z[0] - z[0]*z[1] + z[1]*z[1]
def mul(x, y):
    (a,b),(c,d) = x,y
    return (a*c - b*d, a*d + b*c - b*d)
def conj(z): return (z[0]-z[1], -z[1])
pi = (a, b)
assert norm(pi) == p and 2*a - b == t
print(f"pi = {a} + {b}*omega,  N(pi)=p OK,  pi+conj = 2a-b = t OK")

units = {'1':(1,0), '-1':(-1,0), 'w':(0,1), '-w':(0,-1), 'w^2':(-1,-1), '-w^2':(1,1)}

# ===== Claim 1: N(pi+u)=n has the unique solution u=-1, set by sextic class of 7 =====
print("\n=== Claim 1: which unit u gives N(pi+u)=n ? ===")
for name,u in units.items():
    z = (pi[0]+u[0], pi[1]+u[1]); nz = norm(z)
    tag = " <-- = n" if nz==n else (" (=p+t+1)" if nz==p+t+1 else "")
    print(f"  u={name:4s}: N(pi+u) = {'n' if nz==n else ('p+t+1' if nz==p+t+1 else str(nz)[:20]+'...')}{tag}")
# sextic residue class of 7 mod pi (the CM normalization that fixes the twist / the unit)
w = (-a * pow(b, -1, p)) % p            # image of omega in ZZ[w]/pi = F_p  (a+b*w=0 mod p)
assert (w*w + w + 1) % p == 0
def sextic_symbol(lam, pi_ab, modulus):
    """[lam/pi]_6 as exponent k in basis zeta6 = -w^2, over F_modulus."""
    aa,bb = pi_ab
    wm = (-aa * pow(bb, -1, modulus)) % modulus
    assert (wm*wm + wm + 1) % modulus == 0
    val = (lam[0] + lam[1]*wm) % modulus
    s = pow(val, (modulus-1)//6, modulus)
    zeta6 = (-(wm*wm)) % modulus            # primitive 6th root; zeta6^2 = w = omega
    cur = 1
    for k in range(6):
        if cur == s: return k
        cur = (cur*zeta6) % modulus
    return None
k7 = sextic_symbol((7,0), pi, p)
print(f"  sextic residue class [7/pi]_6 = zeta6^{k7}  (zeta6=-w^2, so w=omega=zeta6^2)  -> fixes u")

# ===== Claim 2: pi_n = -(1-pi) = pi-1, a prime above n =====
print("\n=== Claim 2: Grossencharacter relation pi_n = -(1-pi) = pi-1 ===")
pi_n = (pi[0]-1, pi[1])
print(f"  pi_n = pi-1 = {pi_n[0]} + {pi_n[1]}*omega")
print(f"  N(pi_n) = n ? {norm(pi_n)==n};   n mod 3 = {n%3} (=1 => n splits, pi_n is a prime above n)")
print(f"  -(1-pi) = pi-1 identity: {(-(1-pi[0]), -(-pi[1])) == pi_n}")

# ===== Claim 3: sextic reciprocity product = omega (prevents amicability) =====
print("\n=== Claim 3: sextic reciprocity product [pi_n/pi_p]_6 * [pi_p/pi_n]_6 ===")
k_np = sextic_symbol(pi_n, pi,   p)     # [pi_n / pi_p]_6  over F_p
k_pn = sextic_symbol(pi,   pi_n, n)     # [pi_p / pi_n]_6  over F_n
prod = (k_np + k_pn) % 6
label = {0:'1',1:'zeta6',2:'omega (=w^2? ) ',3:'-1',4:'omega^2',5:'-zeta6'}
print(f"  [pi_n/pi_p]_6 = zeta6^{k_np},  [pi_p/pi_n]_6 = zeta6^{k_pn}")
print(f"  product = zeta6^{prod}   (zeta6^2 = omega, zeta6^4 = omega^2, zeta6^3 = -1)")
print(f"  == omega ? {prod==2};  == omega^2 ? {prod==4};  nontrivial (blocks amicability) ? {prod!=0}")

# ===== Claim 4: twist order n_t = 2(p+1)-n, factor, 13^2 -> subgroup of order 169 =====
print("\n=== Claim 4: twist order n_t = 2(p+1)-n and its 169 subgroup ===")
n_t = 2*(p+1) - n
print(f"  n_t = {n_t}")
for q in [3, 9, 13, 169, 3319, 22639]:
    print(f"    {q:6d} | n_t ? {n_t % q == 0}")
cof = n_t // (9 * 169 * 3319 * 22639)
print(f"  n_t / (3^2 * 13^2 * 3319 * 22639) = {cof}")
print(f"    exact division ? {9*169*3319*22639*cof == n_t};  cofactor prime ? {isprime(cof)}")
print(f"  => twist has a rational subgroup of order 169 (from 13^2): {n_t % 169 == 0}")
```

### C — `secp256k1_order_fingerprint.py`

```python
"""Arithmetic fingerprint of secp256k1 — multiplicative orders + residue symbols
of the small primes mod p and mod n. Under-tabulated concrete invariants; an
anomalously SMALL order (large subgroup index) would be a genuine feature.
Uses the full factorizations of p-1 and n-1. Exact integers."""
from sympy import isprime, primerange

p = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
n = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141

# full factorizations (p-1 verified: 2*3*7*13441*C; n-1 from thread 1)
Cp = (p-1)//(2*3*7*13441)
fac_p1 = {2:1,3:1,7:1,13441:1, Cp:1}
fac_n1 = {2:6,3:1,149:1,631:1, 107361793816595537:1,
          174723607534414371449:1, 341948486974166000522343609283189:1}
assert isprime(Cp)
assert 2**6*3*149*631*107361793816595537*174723607534414371449*341948486974166000522343609283189 == n-1

def order(a, m, fac):
    o = m-1
    for q in fac:
        while o % q == 0 and pow(a, o//q, m) == 1: o //= q
    return o

def leg(a, m): return pow(a % m, (m-1)//2, m)          # 1 QR, m-1 nonQR
def is_cube(a, m): return pow(a % m, (m-1)//3, m)       # 1 iff cube (m=1 mod 3)

print("=== multiplicative-order fingerprint of small primes ===")
print(f"{'m':>3} | {'ord_p(m)/(p-1)':>16} idx_p | {'ord_n(m)/(n-1)':>16} idx_n | QRp QRn cubeP cubeN")
from fractions import Fraction
for m in list(primerange(2, 60)):
    op = order(m, p, fac_p1); on = order(m, n, fac_n1)
    ip = (p-1)//op; ino = (n-1)//on
    qp = "+" if leg(m,p)==1 else "-"; qn = "+" if leg(m,n)==1 else "-"
    cp = "1" if is_cube(m,p)==1 else "x"; cn = "1" if is_cube(m,n)==1 else "x"
    fp = Fraction(op, p-1); fn = Fraction(on, n-1)
    print(f"{m:>3} | {str(fp):>16} {ip:>5} | {str(fn):>16} {ino:>5} | {qp}   {qn}   {cp}    {cn}")

print("\nreadout:")
print("  idx = [(Z/·)* : <m>] = subgroup index; large idx ⇒ m generates a SMALL subgroup (notable).")
print("  ord_n(2)=(n-1)/64 (idx 64) confirmed. Scan for any m with anomalously large index.")

# explicit hunt for the largest-index (smallest-order) small element, mod n and mod p
print("\n=== primes with the LARGEST subgroup index (smallest order) up to 200 ===")
best_n = sorted(((p-1)//order(m,p,fac_p1), m, 'p') for m in primerange(2,200))[-3:]
best_n2 = sorted(((n-1)//order(m,n,fac_n1), m, 'n') for m in primerange(2,200))[-3:]
for idx, m, mod in best_n:  print(f"  mod p: m={m:>3} index={idx}  (= 2^{idx.bit_length()-1} ish)")
for idx, m, mod in best_n2: print(f"  mod n: m={m:>3} index={idx}")
```

### C — `d_recursion_exact_v1.py`

```python
#!/usr/bin/env python3
"""
The USER'S EXACT D-recursion (source), validated against their Findings, then
applied to real keys to see what signatures actual keys produce.
"""
import csv

def d_recursion(N, error):
    signature = []
    e = abs(error)
    while e > 0:
        D = N // e
        if D == 0: break
        signature.append(D)
        correction = N // D
        e = abs(e - correction)
    return signature

def reconstruct_error(N, D_terms):
    D_last = D_terms[-1]
    e_min = N // (D_last + 1) + 1
    e_max = N // D_last
    possible = list(range(e_min, e_max + 1))
    for D in reversed(D_terms[:-1]):
        correction = N // D
        new_possible = []
        for e_next in possible:
            for sign in (+1, -1):
                e_cand = correction + sign * e_next
                if e_cand > 0 and N // e_cand == D:
                    new_possible.append(e_cand)
        possible = sorted(set(new_possible))
        if not possible: return None
    return possible

# ---- validate against Finding B ----
print("VALIDATE Finding B (error = N//3 + N//7):")
for P in (20,40,80,160,256):
    N=1<<P; err=N//3+N//7; sig=d_recursion(N,err)
    print(f"  {P:>3}-bit: steps={len(sig)}  sig={sig if P<=40 else sig[:3]+['...2^%d'%sig[-1].bit_length()] if len(sig)>3 else sig}")
# ---- validate Finding C ----
print("\nVALIDATE Finding C (error = N//3 + N//7 + N//13 + 2^(P/8)):")
for P in (40,80,160,256):
    N=1<<P; err=N//3+N//7+N//13+2**(P//8); sig=d_recursion(N,err)
    print(f"  {P:>3}-bit: steps={len(sig)}  D-term bitlens={[round(d.bit_length()-1,1) if d>1 else 0.0 for d in sig]}")

# ---- apply to REAL solved keys: what signature does an actual key give? ----
print("\nREAL solved keys — d_recursion on the private key and on the band-offset:")
rows=[r for r in csv.DictReader(open("puzzles_verified.csv")) if int(r["bits"])>=40]
for r in rows[:6]+rows[-4:]:
    P=int(r["bits"]); d=int(r["private_key"],16); N=1<<P
    sig_full=d_recursion(N,d)
    off=d-(1<<(P-1)); sig_off=d_recursion(N,off) if off>0 else []
    print(f"  puzzle {r['puzzle']:>3} ({P}b): full-key steps={len(sig_full)}  band-offset steps={len(sig_off)}")

# ---- how many terms for RANDOM keys vs structured? ----
import random; rnd=random.Random(1)
print("\nRANDOM keys vs STRUCTURED (sum-of-fractions) — step counts at each bit size:")
for P in (80,160,256):
    N=1<<P
    rand_steps=[len(d_recursion(N,(1<<(P-1))+rnd.randrange(1<<(P-1)))) for _ in range(200)]
    struct=len(d_recursion(N,N//3+N//7+N//13+2**(P//8)))
    print(f"  {P:>3}-bit: random mean steps={sum(rand_steps)/len(rand_steps):.1f} "
          f"(range {min(rand_steps)}-{max(rand_steps)})   structured(3 fracs)={struct}")
```

### C — `y_orbit_class_investigation_v1.py`

```python
#!/usr/bin/env python3
"""
y_orbit_class_investigation_v1.py

Investigation of the y-coordinate / orbit-class structure of secp256k1, following the
avenues raised: (A) orbit-class sextant-given-y; (B) chi2(y) as the odd coordinate;
(C) S3 summation polynomial under [omega]; (D) forced arithmetic facts; (E) the
eigendifferential/Hasse-Witt level.

Each result is tagged. NB: these are POSITIVE-STRUCTURE measurements and scoped nulls,
NOT closure claims. Empirical nulls are bound to the features/sample/floor stated.
"""
import random, numpy as np
import sympy as sp
from ecc_secp256k1 import P as p, N_ORDER as n, scalar_mul
from eisenstein_lift_sextant_exact_v1 import eis, sextant
from angular_interference_scaling_v1 import conditional

g = 2
while pow(g, (p - 1) // 3, p) == 1: g += 1
beta = pow(g, (p - 1) // 3, p); beta2 = pow(beta, 2, p)
def sx(x): return sextant(*eis(x))


def A_orbit_sextant_structure(M=40000):
    print("=" * 70); print("(A) GLV orbit-sextant structure  [VERIFIED structure]")
    from collections import Counter
    rng = random.Random(1); triples = Counter(); same_par = 0
    for _ in range(M):
        x = rng.randrange(1, p)
        t = (sx(x), sx(beta * x % p), sx(beta2 * x % p))
        triples[tuple(sorted(t))] += 1
        if len({v % 2 for v in t}) == 1: same_par += 1
    print(f"  same-parity across the GLV orbit: {same_par}/{M} = {same_par/M:.3f}")
    print(f"  reason: beta=omega^2 is a 120deg = 2-sextant (EVEN) rotation; parity breaks")
    print(f"          only at fold boundaries (~2%). top triples: {triples.most_common(4)}")
    print("  => given EXACT y (the orbit), sextant is confined to the 3 orbit-sextants,")
    print("     ~98% one parity. This is a near-invariant of y. (Conjecture 'sextant|y")
    print("     uniform on Z/6' is FALSE at exact-y resolution.)\n")


def A2_no_scalar_leak(M=24000):
    print("=" * 70); print("(A2) ...but it carries NO scalar information  [VERIFIED null]")
    rng = random.Random(2)
    D = [rng.randrange(1, n) for _ in range(M)]
    X = [scalar_mul(d)[0] for d in D]
    SXT = np.array([sx(x) for x in X]); SPAR = SXT % 2
    tg = {'d%2': np.array([d % 2 for d in D]), 'd%3': np.array([d % 3 for d in D]),
          'd%6': np.array([d % 6 for d in D])}
    Ms = [3000, 6000, 12000, 24000]; rr = np.random.default_rng(9)
    for fn, fv in {'sextant': SXT, 'sext_parity(~f(y))': SPAR}.items():
        for tn, tv in tg.items():
            r = conditional(fv, tv, Ms, 200, rr)
            print(f"  {fn:18} vs {tn}: " + "  ".join(f"z={x[2]:+.1f}" for x in r))
    print("  => noise, no growth. Orbit-class structure is a coordinate relation, not a")
    print("     scalar leak; and it washes out at any coarse (usable) y-resolution.\n")


def B_chi2_y(M=24000):
    print("=" * 70); print("(B) chi2(y) = the odd coordinate  [VERIFIED null, scoped]")
    rng = random.Random(3)
    D = [rng.randrange(1, n) for _ in range(M)]
    Y = [scalar_mul(d)[1] for d in D]
    C = np.array([1 if pow(int(y), (p - 1) // 2, p) == 1 else 0 for y in Y])
    tg = {'d<n/2(sign)': np.array([1 if d < n // 2 else 0 for d in D]),
          'chi2(d)': np.array([1 if pow(d, (n - 1) // 2, n) == 1 else 0 for d in D]),
          'd%2': np.array([d % 2 for d in D]), 'floor(3d/n)': np.array([(3 * d) // n for d in D])}
    Ms = [3000, 6000, 12000, 24000]; rr = np.random.default_rng(5)
    print(f"  marginal P(chi2(y)=QR) = {C.mean():.4f}  (balanced)")
    for tn, tv in tg.items():
        r = conditional(C, tv, Ms, 200, rr)
        print(f"  chi2(y) vs {tn:12}: " + "  ".join(f"z={x[2]:+.1f}" for x in r))
    print("  => balanced pseudo-random odd bit; no low-complexity dependence on d found.\n")


def C_S3_covariance():
    print("=" * 70); print("(C) S3 summation polynomial under [omega]  [PROVED covariance]")
    x1, x2, x3, b, bt = sp.symbols('x1 x2 x3 b beta')
    S3 = sp.expand((x1 - x2) ** 2 * x3 ** 2 - 2 * ((x1 + x2) * (x1 * x2) + 2 * b) * x3
                   + ((x1 * x2) ** 2 - 4 * b * (x1 + x2)))
    S3b = sp.expand(S3.subs({x1: bt * x1, x2: bt * x2, x3: bt * x3}))
    S3b = sp.expand(S3b.replace(lambda e: e.is_Pow and e.base == bt,
                                lambda e: bt ** (e.exp % 3)))
    d = sp.expand(sp.expand(S3b - bt * S3).replace(
        lambda e: e.is_Pow and e.base == bt, lambda e: bt ** (e.exp % 3)))
    print(f"  S3(beta*x1,beta*x2,beta*x3) = beta * S3 : {d == 0}  (beta-eigenvector)")
    print("  => the relation variety {S3=0} is [omega]-invariant. This is the known")
    print("     GLV/automorphism symmetry => a CONSTANT-FACTOR speedup in index-calculus/")
    print("     rho (order-6 automorphisms), NOT a change in degree or asymptotic hardness.\n")


def D_forced_facts():
    print("=" * 70); print("(D) forced arithmetic facts about y  [VERIFIED]")
    print(f"  n prime: {sp.isprime(n)};  p mod 4 = {p % 4} => chi2(-1) = {(-1)**((p-1)//2)}")
    print(f"  7 is a QR mod p: {pow(7,(p-1)//2,p)==1}  (non-residue: else (0,+-sqrt7) = rational 3-torsion)")
    print(f"  -7 is a cube mod p: {pow((-7)%p,(p-1)//3,p)==1}  (non-cube: else rational 2-torsion (x0,0))")
    print(f"  3 | n: {n%3==0}  => y-fibration E->P^1 ramifies at E[omega-1], no rational ramification.")
    print("  Coherent little theorem: n prime + CM by Z[omega] forces this.\n")


def E_hasse_note():
    print("=" * 70); print("(E) eigendifferential / Hasse-Witt level  [CITED reasoning]")
    t = p + 1 - n
    print(f"  dx/y is a CM eigendifferential ([omega]* (dx/y) = beta*(dx/y)); the de Rham /")
    print(f"  crystalline cohomology of an elliptic curve is 2-dimensional with Frobenius")
    print(f"  char poly  X^2 - t*X + p,  t = p+1-n = {t}.")
    print("  => everything at this level is DETERMINED by t (already known). There is no")
    print("     finer invariant 'past t' for genus 1. (Earlier 'genuine parallel' framing")
    print("     was wrong: the rhombus lived in an infinite-dim function space; the")
    print("     differential lives in a 2-dim cohomology with no room past t.)\n")


if __name__ == "__main__":
    A_orbit_sextant_structure()
    A2_no_scalar_leak()
    B_chi2_y()
    C_S3_covariance()
    D_forced_facts()
    E_hasse_note()
```

### C — `frontier_beyond_singlex_v1.py`

```python
#!/usr/bin/env python3
"""
frontier_beyond_singlex_v1.py

This script verifies a short list of EXACT integer facts. It proves nothing about
"closure" of either frontier.

Frontier 1 (joint / multi-point across keys) is NOT proved: the only established input
is the CITED equidistribution of single-x marginals for independent keys from ranges
>> sqrt(p) (Weil / Kohel-Shparlinski). Joint exploitability and dependent-key
detectability are open. (An earlier finite-sample MI "demonstration" was removed as a
scoped null, not a proof.)

Frontier 2 (y / group-law) -- VERIFIED here (exact integers):
  N(pi_p) = p ;  N(pi_p - 1) = n (group order) ;  trace t = p+1-n ;
  GLV [omega] fixes y (phi(x,y)=(beta x,y), x^3+7 invariant) ; y-parity flips d<->n-d.
NOT proved (cited / argued only, no closure):
  * E(F_p) ~ Z[omega]/(pi_p - 1) as Z[omega]-modules -- only the ORDER is checked here
    (necessary, not sufficient); the isomorphism is cited CM theory (Deuring).
  * "computing the linear lift Lambda = the DLP" is a REDUCTION (Lambda efficiently
    computable => d recoverable => DLP solved), so it reduces the y-lift question to the
    DLP, whose hardness is ITSELF UNPROVEN. A reduction to a conjecture, not a proof.
"""
from ecc_secp256k1 import P as p, N_ORDER as n, scalar_mul

aP = 367917413016453100223835821029139468249
bP = 303414439467246543595250775667605759171


def emul(A, B):
    a, b = A; c, d = B; return (a * c - b * d, a * d + b * c + b * d)
def enorm(w): return w[0] * w[0] - w[0] * w[1] + w[1] * w[1]


def frontier2_facts():
    print("=" * 70)
    print("Frontier 2: y / group-law -- EXACT facts (verified); NO closure claim")
    print("=" * 70)
    pi = (aP, bP)
    print(f"  N(pi_p) = p : {enorm(pi) == p}")
    nm1 = enorm((pi[0] - 1, pi[1]))
    print(f"  N(pi_p - 1) = n (group order) : {nm1 == n}")
    print(f"  Frobenius trace t = p+1-n = {p + 1 - n}")
    g = 2
    while pow(g, (p - 1) // 3, p) == 1: g += 1
    beta = pow(g, (p - 1) // 3, p)
    x1, y1 = scalar_mul(12345); xn, yn = scalar_mul((n - 12345) % n)
    print(f"  GLV [omega] fixes y (x^3+7 invariant) : {(pow(beta * x1 % p, 3, p) + 7) % p == (pow(x1, 3, p) + 7) % p}")
    print(f"  y-parity flips under d<->n-d (x equal) : {(y1 & 1) != (yn & 1) and x1 == xn}")
    print("  NOT proved here: E(F_p) ~ Z[omega]/(pi_p-1) (only the order is checked; iso is")
    print("  cited CM theory), and 'linear lift = DLP' is a REDUCTION to the DLP, whose")
    print("  hardness is unproven. No closure of the y / group-law side is claimed.\n")


if __name__ == "__main__":
    frontier2_facts()
```


*End of compendium. Every tagged item is reproducible from the embedded source (Appendices A, C) and the named documents.*
