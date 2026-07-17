# secp256k1 — Positive Findings Compendium & Handover (v1, 2026-07-13)

A self-contained corpus of the **structure that was found and established** in this
project: the curve's CM arithmetic, the Eisenstein lift and its exact laws, the
character/GLV structure, the twist and atlas facts, the (n,k,D) decomposition and its
valid-construction domain, the key-construction substrate, and the datasets. Every item
carries an explicit status tag and the file that produces/verifies it. Code that
generates the evidence is embedded in the Appendices.

## How to read this / status tags

- **PROVED** — established by symbolic identity, exhaustive-by-construction argument, or
  a proof; holds for all inputs in its stated range.
- **VERIFIED** — exact (integer / exact-rational) computation confirming the stated fact
  for the stated inputs (e.g. secp's `p,n`, or a finite prime sweep).
- **EMPIRICAL** — measured over a finite sample with the stated size/floor.
- **CITED** — a classical theorem or external result used as input.

Constants used throughout:
```
p = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F   (field prime)
n = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141   (group order, prime)
curve: y^2 = x^3 + 7   (j = 0, CM by Z[omega], omega = e^{2 pi i/3})
t = p + 1 - n = 432420386565659656852420866390673177327                 (Frobenius trace)
p - 1 = 2 * 3 * 7 * 13441 * C
n - 1 = 2^6 * 3 * 149 * 631 * 107361793816595537 * 174723607534414371449
        * 341948486974166000522343609283189
```

---

## §1. Curve substrate & valid key construction

**[VERIFIED] Exact scalar multiplication, validated against real solved keys.**
`ecc_secp256k1.py` (Appendix A.1) computes `(x,y) = [d]G` with pure-integer Jacobian
arithmetic and is validated element-by-element against the real solved puzzle keys
(`puzzles_verified.csv`). This is the substrate: from any chosen scalar `d ∈ [1,n)` it
constructs the valid keypair `(d, X, Y)` across the full 1..256-bit range, and hence any
derived record `(d, X, Y, n, k, D)`.

**[VERIFIED] `d ↔ (X,Y)` is a bijection** `ℤ/nℤ → E(𝔽_p)` (G a generator). *(Files:
`ecc_secp256k1.py`; noted across `btc_puzzle_*` topic files.)*

---

## §2. The Eisenstein CM lift and the angle (sextant) law

Since `p ≡ 1 (mod 3)`, `(π_p)` is a degree-1 prime ideal of `ℤ[ω]` with `N(π_p)=p` and
`ℤ[ω]/(π_p) ≅ 𝔽_p`. The lift `eis : 𝔽_p → ℤ[ω]` sends `X` to the representative of
`X mod π_p` in the Gauss-reduced fundamental domain `P` (Babai rounding).

`π_p = aP + bP·ω`, `aP = 367917413016453100223835821029139468249`,
`bP = 303414439467246543595250775667605759171`.
Reduced basis: `R1 = (-303414439467246543595250775667605759171, 64502973549206556628585045361533709078)`,
`R2 = (64502973549206556628585045361533709078, 367917413016453100223835821029139468249)`.

**[PROVED] Lemma A (bijection).** `eis` is a bijection `𝔽_p → ℤ[ω]∩P`; the multiset
`{eis(X):X∈𝔽_p}` is exactly the `p` lattice points of `ℤ[ω]` in `P`, each once.

**[PROVED] Rhombus theorem (universal, all `p≡1 mod 3`).** Both Gauss-reduced basis
vectors have Eisenstein norm exactly `p` (`N(R1)=N(R2)=p`), i.e. both are unit associates
`ζ·π_p`. Hence `P` is a **60° rhombus** with true edge length `√p` and area `p·√3/2`.
*(Verified for all 300 primes `p≡1(3)` in `[7,4513]` and for secp. File:
`lift_sextant_rhombus_law_proof_v2.py`, THM 1.)*

**[PROVED] One-parameter angle law.** The sextant (60° sector) histogram of `eis(X)` is a
function of the single parameter `θ = arg(π_p) mod 60°` (fold to `[0°,30°]`). With
opposite sectors equal (central symmetry) and the three opposite-pairs summing to `1/2`:

| opposite-pair | proportion |
|---|---|
| pinned pair | **exactly `1/8`** (θ-independent; symbolic area `√3/16`) |
| free pair A | `p₀(θ) = (3/4)·|cos 2θ| / (2 cos 2θ + 1)` |
| free pair B | `3/8 − p₀(θ)` |

*(Symbolic identity + matches exact rational areas to `1.7e-16` over 150 primes. File:
`lift_sextant_rhombus_law_proof_v2.py`, THM 2–3.)*

**[PROVED] Exact rational sector proportions in the basis** (secp's cell, `R1=(a,b)`,
`R2=(c,d)`):
- pinned `{0,3}` = `1/8`
- `{1,4}` = `p / (8·|a(a−b)|)` = `0.129659…`
- `{2,5}` = `|ab + 2ad + cd| / (8·|ad|)` = `0.245341…`
- sum = `1/2` ✓. *(Derived symbolically; `lift_sextant_law_clarifications_v1.md`.)*

**[PROVED] `1/8` is a universal invariant.** For every `p≡1(3)`, exactly one opposite-pair
has area exactly `p/8`; it is the `{0,3}` or `{1,4}` class, never the maximal `{2,5}`.
secp: pinned `{0,3}`, `θ = 50.55° ≡ 9.45°`. *(300/300 primes; symbolic. File as above.)*

**[VERIFIED] Marginal error term.** `H(s) = area(P∩sector_s) + O(√p)` absolute;
`P[σ=s] = area/p + O(p^{-1/2})` relative (empirically `|H(s)−area|/√p ≈ 0.5–0.6`,
perimeter `≈ 4√p`). *(File: `lift_sextant_law_clarifications_v1.md`.)*

---

## §3. The lift-norm band law

The norm `N(eis(X)) = |eis(X)|² = u²−uv+v²` (true squared length).

**[PROVED/VERIFIED] Universal norm law.** With `s = N(eis(X))/p`, the distribution is the
**same for every `p≡1(3)` and independent of `θ`** (rotation-invariance + universal
rhombus shape):
- support `[0, 3/4]`;
- **mean `E[s] = 1/6` exactly** (`E[N] = p/6`);
- density piecewise-analytic; **constant `2π/√3 ≈ 3.628` on `[0, 3/16]`**; breakpoints at
  inradius `3/16`, short vertex `1/4`, long vertex `3/4`.

*(Exact circle∩rhombus CDF matches the exact lattice to `8e-4`; identical at
`p=10009…secp`. File: `norm_band_law_proof_v1.py`.)*

---

## §4. Multiplicative character & GLV structure

**[PROVED] All nontrivial multiplicative characters are exactly uniform.** For any
`k | (p−1)`, `χ_k(X) = X^{(p−1)/k}` has each fiber of size exactly `(p−1)/k` (character
orthogonality). In particular `χ₆` is exactly uniform (fibers `(p−1)/6`), verified by
exact enumeration at `p=100003` (all six = 16667) and `Σ_X ζ₆^{χ₆(X)} = 0` exactly.
*(File: `lift_chi6_uniform_law_proof_v1.py`.)*

**[PROVED/VERIFIED] GLV = multiplication of the lift by a cube root of unity.** The GLV
endomorphism `φ(x,y) = (βx, y)` has `β ≡ ω² (mod π_p)` (`β = -aP·bP^{-1} mod p`, squared).
On the multiplicative characters (exact over 40000 samples):
- `χ₆(βx) = χ₆(x) + 4 (mod 6)`
- `χ₃(βx) = χ₃(x) + 1 (mod 3)`  → a GLV triple `{x,βx,β²x}` hits **all three** cubic classes
- `χ₂(βx) = χ₂(x)` (β is a QR)

*(File: `glv_orbit_structure_proof_v1.py`.)*

**[VERIFIED] GLV orbit-sextant structure.** The three `x`-values sharing a `y` are the GLV
orbit `{x,βx,β²x}`; their sextants are **~98% the same parity** (97.2%/40k), ~75% exactly
`{0,2,4}` or `{1,3,5}` — because `β=ω²` is a 120°=2-sextant (even) rotation. *(File:
`y_orbit_class_investigation_v1.py`.)*

**[VERIFIED] Hecke character (closed form).** `χ(π) = −(28/π)₆^{-1}` — a single sextic
symbol, confirmed on 206/206 primes; `χ(π_p)=1` two independent ways. *(File/topic:
`secp256k1_hecke_character_explicit_2026_07_11`.)*

---

## §5. Group-law / summation-polynomial covariance

**[PROVED] `S₃` is a `β`-eigenvector under `[ω]`.** The 3rd Semaev summation polynomial
for `y²=x³+7`,
`S₃ = (x₁−x₂)²x₃² − 2((x₁+x₂)x₁x₂+14)x₃ + (x₁²x₂² − 28(x₁+x₂))`,
satisfies `S₃(βx₁,βx₂,βx₃) = β·S₃(x₁,x₂,x₃)` exactly (sympy). The relation variety
`{S₃=0}` is `[ω]`-invariant. *(File: `frontier_beyond_singlex_v1.py` / `y_orbit_class_investigation_v1.py`.)*

---

## §6. Module & Frobenius structure

**[VERIFIED] `E(𝔽_p)` as a `ℤ[ω]`-module.** `N(π_p−1) = n` exactly; the Frobenius is `π_p`
(trace `t = p+1−n`); `E(𝔽_p) ≅ ℤ[ω]/(π_p−1)` (order match verified; module iso is CITED CM
theory). `dx/y` is a CM eigendifferential: `[ω]*(dx/y) = β·(dx/y)`. *(File:
`frontier_beyond_singlex_v1.py`.)*

**[VERIFIED] `y`-coordinate symmetries.**
- `χ₂(y(n−d)) = −χ₂(y(d))` — `[PROVED]` (`p≡3 mod4 ⇒ χ₂(−1)=−1`, `[−1](x,y)=(x,−y)`).
- `χ₂(y([λd]G)) = χ₂(y([d]G))`, i.e. `f(λd)=f(d)` — `[PROVED]` (`[λ]=φ` fixes `y`).
So `f=χ₂(y)` transforms by the `μ₆` sign character (odd/`−1`, invariant/`λ`).
*(Files: `y_orbit_class_investigation_v1.py`, `chi2y_harmonic_v1.py`.)*

---

## §7. Forced arithmetic facts (n prime + CM by ℤ[ω])

**[VERIFIED] A coherent little theorem.** `n` prime and CM by `ℤ[ω]` force:
- `7` is a **quadratic non-residue** mod `p` (else `(0,±√7)` would be rational 3-torsion);
- `−7` is a **non-cube** mod `p` (else `(x₀,0)` rational 2-torsion);
- `3 ∤ n`; `p ≡ 3 (mod 4)`;
- the `y`-fibration `E → E/[ω] ≅ ℙ¹` ramifies at `E[ω−1]` with no rational ramification.

*(File: `y_orbit_class_investigation_v1.py`.)*

**[VERIFIED] Class-number-1 factorization.** The Epstein zeta of the `ℤ[ω]` norm form
factors: `ζ_{ℤ[ω]}(s) = ζ(s)·L(s,χ₋₃)` (numerically confirmed). *(File:
`y_additive_multiplicative_dissection_v1.md`.)*

---

## §8. Twist & curve atlas facts

*(Topic files: `secp256k1_atlas_findings_2026_07_10`, `secp256k1_arithmetic_v4.md`,
`cm_twist_order_divisibility_2026_07_10`, `secp256k1_bsd_tamagawa_resolved_2026_07_11`,
`secp256k1_eisenstein_twin_density_2026_07_12`.)*

- **[VERIFIED]** `b = 7` is the unique prime-order sextic twist family constant.
- **[VERIFIED]** GLV basis = the CM ideal `{π_n, ω²π_n}`.
- **[VERIFIED]** `(p,n)` amicable: `#E₇(𝔽_n) = p`.
- **[VERIFIED]** twist order `n_t = 3²·13²·3319·22639·C` (C a large prime cofactor).
- **[VERIFIED]** CM twist-order divisibility law: `ℓ | n_t ⟺` Frobenius eigenvalue `−1`
  (24/24 sign-reversal cases).
- **[VERIFIED]** `ord_n(2) = (n−1)/64` (index 64).
- **[VERIFIED]** Eisenstein-twin density = Bateman–Horn (obs/pred = 0.9975, `𝔖 = 1.672`).
- **[VERIFIED]** BSD/Tamagawa for `y²=x³+7 /ℚ`: `∏c_ℓ = 1`, `Ш = 1`, Kodaira `II/II/II`,
  `L(1) = Ω` via an independent L-series.

---

## §9. The (n,k,D) decomposition & construction domain

*(Topic files: `btc_puzzle_fullrange_dataset_nkd_domain_2026_07_13`,
`btc_puzzle_nk_decomposition`, `btc_puzzle_zomega_scalar_is_Fn_2026_07_12`.)*

- **[VERIFIED]** `ℤ[ω]/(π_n) = 𝔽_n = ℤ/nℤ` (n splits, `n≡1 mod 3`) — the scalar sits in
  `𝔽_n`; GLV `(a,b)` is a non-canonical representation.
- **[VERIFIED] (n,k,D) validity domain map:** coprimality is the **only** label
  obstruction; the `D`-gap narrows with `n`; the GLV 2-D→1-D degeneracy transition is
  exactly `N = 128`; order-overflow at `N=256` is `~2^{-128}`.
  *(Files: `build_fullrange_dataset_v1.py`, `nkd_validity_domain_v1.py`.)*
- **[VERIFIED]** Farey-coordinate structure of `(n,k)` (exact best-rational via
  `|a·n − k·b|` minimization; no floating point).

---

## §10. Datasets (valid constructed keys)

- **`puzzles_verified.csv`** — the real solved puzzle keys (validation ground truth).
- **`constructed_keys_fullrange_v1.npz`** — 36k known-`d` records, 21k at 256-bit (GLV 2-D),
  full bit range; replaces the 160-capped set. *(Builder: `build_fullrange_dataset_v1.py`.)*
- **100k MT19937 set** — our own MT19937 output through the same select-bitlength→curve
  pipeline: a full-power **known-generator** reference set (run every test on this AND the
  real set). *(Helper: `gen_keys` in `angular_interference_scaling_v1.py`.)*

---

## §11. Proof manifest (items tagged PROVED)

1. Lemma A — `eis` bijection ⇒ lift multiset = `ℤ[ω]∩P` uniform. (§2)
2. Rhombus theorem — reduced basis both norm `p`; `P` a 60° rhombus; universal. (§2)
3. One-parameter angle law + closed-form sector proportions. (§2)
4. `1/8` universal invariant (symbolic `√3/16`), never the maximal pair. (§2)
5. Norm-band law — universal, mean `1/6`, constant density `2π/√3` on `[0,3/16]`. (§3)
6. All nontrivial `χ_k` marginals exactly uniform; `χ₆` fibers `(p−1)/6`. (§4)
7. GLV `β≡ω²`; character shifts `χ₆:+4, χ₃:+1, χ₂:fixed`. (§4)
8. `S₃` `β`-eigenvector under `[ω]`. (§5)
9. `y` symmetries: `χ₂(y(n−d))=−χ₂(y(d))`, `f(λd)=f(d)`. (§6)
10. Forced arithmetic: `7` QNR, `−7` non-cube, ramification at `E[ω−1]`. (§7)

---

## Appendix A — foundational code

### A.1 `ecc_secp256k1.py` (exact scalar multiplication + validation)

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
    """affine (x,y) = k·base, exact."""
    R=(0,1,0); Q=(base[0],base[1],1)
    while k>0:
        if k&1: R=_add(R,Q)
        Q=_dbl(*Q); k>>=1
    Xx,Yy,Zz=R
    if Zz==0: return None
    zi=pow(Zz,P-2,P); zi2=(zi*zi)%P
    return ((Xx*zi2)%P, (Yy*zi2*zi)%P)
```

### A.2 `eisenstein_lift_sextant_exact_v1.py` (exact lift + sextant)

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
    """Exact 0..5 sextant of w=u+v*omega via integer omega-rotation."""
    if u == 0 and v == 0: return 0
    for k in range(6):
        if v >= 0 and (u - v) >= 0 and u > 0: return k
        u, v = v, v - u
    return 0 if v >= 0 else 3

def lift_sextant(X):
    u, v = eis(X); return sextant(u, v)
```

---

## Appendix B — proof-script manifest

All in `btc_puzzle_investigation/`. Each is self-contained (imports A.1/A.2), exact
arithmetic in the signal path, and prints its own verification.

| file | proves / verifies |
|---|---|
| `lift_sextant_rhombus_law_proof_v2.py` | rhombus theorem, one-parameter angle law, `1/8` invariant (§2) |
| `lift_sextant_law_clarifications_v1.md` | exact rational sector forms; error term (§2) |
| `lift_chi6_uniform_law_proof_v1.py` | `χ₆` exactly uniform; character-sum `=0` (§4) |
| `norm_band_law_proof_v1.py` | universal norm-band law, mean `1/6` (§3) |
| `glv_orbit_structure_proof_v1.py` | `β≡ω²`; GLV character shifts; `y` fixed (§4) |
| `y_orbit_class_investigation_v1.py` | orbit-sextant parity; `S₃` covariance; forced facts (§5,§7) |
| `frontier_beyond_singlex_v1.py` | `N(π_p−1)=n`; module structure; eigendifferential (§6) |
| `chi2y_harmonic_v1.py` | `y` symmetries; multiplicative-basis structure (§6) |
| `y_multiplicative_rigidity_v1.py` | residue-frame / rigidity Gram construction (§9-adjacent) |
| `build_fullrange_dataset_v1.py` | constructs the 36k full-range known-`d` dataset (§10) |
| `nkd_validity_domain_v1.py` | (n,k,D) validity domain map (§9) |
| `secp256k1_order_fingerprint.py` | `p−1`, `n−1` factorizations; index structure (§8) |

### B.1 Rhombus + angle-law verification core (`lift_sextant_rhombus_law_proof_v2.py`)

```python
def enorm(w): return w[0]*w[0] - w[0]*w[1] + w[1]*w[1]   # Eisenstein = true |w|^2
# THM 1: both reduced basis vectors have norm exactly p  => P is a 60-deg rhombus
#   verified for all 300 primes p==1(mod 3) in [7,4513] and for secp.
# THM 3 (symbolic, sympy): the pinned wedge area is identically sqrt(3)/16 = (sqrt3/2)/8
#   => one opposite-pair is EXACTLY 1/8, theta-independent.
# THM 2: free-pair proportion  p0(theta) = (3/4)|cos 2t|/(2 cos 2t + 1),
#   theta = arg(pi_p) mod 60deg (fold [0,30]); matches exact rational areas to 1.7e-16.
```

### B.2 `χ₆` uniformity core (`lift_chi6_uniform_law_proof_v1.py`)

```python
# p == 1 (mod 3) and p odd  => 6 | (p-1).  chi6 : F_p^* -> mu_6 surjective homomorphism,
# kernel index 6  => each fiber EXACTLY (p-1)/6.  Verified by exact enumeration at
# p=100003: fibers all = 16667; additive character sum sum_X zeta_6^{chi6(X)} = 0 exactly.
```

### B.3 GLV structure core (`glv_orbit_structure_proof_v1.py`)

```python
g = 2
while pow(g, (p-1)//3, p) == 1: g += 1
beta = pow(g, (p-1)//3, p)                  # nontrivial cube root of unity mod p
# beta == omega^2 (mod pi_p):  omega = -aP * bP^{-1} mod p ;  beta == omega^2 mod p.
# EXACT over 40000 x:  chi6(beta x)=chi6(x)+4,  chi3(beta x)=chi3(x)+1,  chi2 invariant.
# phi(x,y)=(beta x, y) fixes y;  x^3+7 is GLV-invariant (beta^3=1).
```

### B.4 Norm-band core (`norm_band_law_proof_v1.py`)

```python
def N(w): return w[0]*w[0] - w[0]*w[1] + w[1]*w[1]
# s = N(eis(X))/p  is universal (theta- and p-independent):
#   support [0,3/4];  E[s] = 1/6 exactly;  density const 2*pi/sqrt(3) on [0,3/16];
#   breakpoints 3/16 (inradius), 1/4 (short vertex), 3/4 (long vertex).
# Exact circle-∩-rhombus CDF matches the exact secp lattice histogram to 8e-4.
```

### B.5 Forced arithmetic + `S₃` covariance (`y_orbit_class_investigation_v1.py`)

```python
# n prime + CM by Z[omega]  =>  chi2(7) = -1 (QNR),  (-7)^((p-1)/3) != 1 (non-cube),
#   3 ∤ n,  p ≡ 3 (mod 4),  y-fibration ramifies at E[omega-1].
# S3 summation polynomial for y^2=x^3+7 is a beta-eigenvector:
#   S3(beta x1, beta x2, beta x3) = beta * S3(x1,x2,x3)   (verified symbolically).
# GLV orbit-sextant triples: ~98% same parity; ~75% exactly {0,2,4} or {1,3,5}.
```

---

*End of compendium. All items above are reproducible by running the named scripts in
`btc_puzzle_investigation/`; each prints its own exact verification.*
