# secp256k1 — Positive Findings Compendium & Handover (v2, 2026-07-13)

A single self-contained corpus of the **structure that was found, computed, proved, or
rediscovered** across this project: the curve's CM arithmetic, the Eisenstein lift and its
exact laws, the character/GLV structure, the endomorphism ring and Galois data, the curve
L-function and formal group, the twist structure and Frobenius sieve, the amicability, the
RH-framework CM connection, the (n,k,D) decomposition, the key-construction substrate, and
the datasets. Every item carries a status tag and the file that produces/verifies it. Code
that generates the evidence is embedded in the Appendices. (Supersedes v1; this is the
complete standalone version.)

## Status tags

- **PROVED** — symbolic identity, exhaustive-by-construction argument, or a proof; holds
  for all inputs in its stated range.
- **VERIFIED** — exact (integer / exact-rational) computation confirming the fact for the
  stated inputs (secp's `p,n`, a finite prime sweep, or brute-force cross-check).
- **EMPIRICAL** — measured on a finite sample; size/floor stated.
- **CITED** — a classical theorem or external result used as input.

## Constants

```
p = 2^256 − 2^32 − 977
  = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F   (field prime)
n = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141   (group order, prime)
curve  E : y^2 = x^3 + 7        (j = 0, CM by Z[omega], omega = e^{2 pi i/3}, |Aut(E)| = 6)
t = p + 1 − n = 432420386565659656852420866390673177327                 (Frobenius trace)
Frobenius pi = a + b*omega,  a = 367917413016453100223835821029139468249,
                              b = 303414439467246543595250775667605759171,   N(pi) = p
p − 1 = 2 · 3 · 7 · 13441 · C
n − 1 = 2^6 · 3 · 149 · 631 · 107361793816595537 · 174723607534414371449
        · 341948486974166000522343609283189
```

---

# PART I — Curve substrate & valid key construction

**[VERIFIED] Exact scalar multiplication, validated against real solved keys.**
`ecc_secp256k1.py` (Appendix A.1) computes `(x,y) = [d]G` with pure-integer Jacobian
arithmetic, validated element-by-element against the real solved puzzle keys
(`puzzles_verified.csv`). From any chosen `d ∈ [1,n)` it constructs the valid keypair
`(d, X, Y)` across the full 1..256-bit range, hence any derived `(d, X, Y, n, k, D)` record.

**[VERIFIED] `d ↔ (X,Y)` is a bijection** `ℤ/nℤ → E(𝔽_p)` (`G` a generator).

---

# PART II — The Eisenstein lift laws (angle, norm, character, GLV)

Since `p ≡ 1 (mod 3)`, `(π_p)` is a degree-1 prime ideal of `ℤ[ω]`, `N(π_p)=p`,
`ℤ[ω]/(π_p) ≅ 𝔽_p`. The lift `eis : 𝔽_p → ℤ[ω]` sends `X` to `X mod π_p` reduced (Babai)
into the Gauss-reduced fundamental domain `P`. Reduced basis:
`R1 = (-303414439467246543595250775667605759171, 64502973549206556628585045361533709078)`,
`R2 = (64502973549206556628585045361533709078, 367917413016453100223835821029139468249)`.

**[PROVED] Lemma A (bijection).** `eis` is a bijection `𝔽_p → ℤ[ω]∩P`; the multiset
`{eis(X)}` is exactly the `p` lattice points of `ℤ[ω]` in `P`, each once.

**[PROVED] Rhombus theorem (universal, all `p≡1 mod 3`).** Both reduced basis vectors have
Eisenstein norm exactly `p` (`N(R1)=N(R2)=p`) — both unit associates `ζ·π_p`. Hence `P` is
a **60° rhombus**, true edge `√p`, area `p·√3/2`. *(Verified all 300 primes `p≡1(3)` in
`[7,4513]` and secp; `lift_sextant_rhombus_law_proof_v2.py`.)*

**[PROVED] One-parameter angle law.** The sextant histogram of `eis(X)` is a function of
`θ = arg(π_p) mod 60°` (fold `[0°,30°]`); opposite sectors equal; three pairs sum `1/2`:

| opposite-pair | proportion |
|---|---|
| pinned | **exactly `1/8`** (θ-independent; symbolic area `√3/16`) |
| free A | `p₀(θ) = (3/4)·|cos 2θ| / (2 cos 2θ + 1)` |
| free B | `3/8 − p₀(θ)` |

**Exact rational sector proportions in the basis** (secp cell, `R1=(a,b)`, `R2=(c,d)`):
`{0,3}=1/8`; `{1,4}=p/(8|a(a−b)|)=0.129659…`; `{2,5}=|ab+2ad+cd|/(8|ad|)=0.245341…`; sum
`1/2`. **The `1/8` is a universal invariant** (one opposite-pair for every `p`, the `{0,3}`
or `{1,4}` class, never the max `{2,5}`). secp: pinned `{0,3}`, `θ=50.55°≡9.45°`.
*(Symbolic; matches exact rational areas to `1.7e-16` over 150 primes.
`lift_sextant_rhombus_law_proof_v2.py`, `lift_sextant_law_clarifications_v1.md`.)*

**[VERIFIED] Marginal error term.** `H(s)=area(P∩sector_s)+O(√p)` absolute;
`P[σ=s]=area/p+O(p^{-1/2})` relative (`|H(s)−area|/√p ≈ 0.5–0.6`, perimeter `≈4√p`).

**[PROVED/VERIFIED] Norm-band law.** `s = N(eis(X))/p = |eis(X)|²/p`, universal (θ- and
p-independent): support `[0,3/4]`; **mean `E[s]=1/6` exactly** (`E[N]=p/6`); density
piecewise-analytic, **constant `2π/√3 ≈ 3.628` on `[0,3/16]`**; breakpoints inradius `3/16`,
short vertex `1/4`, long vertex `3/4`. *(Exact circle∩rhombus CDF matches the lattice to
`8e-4`; identical `p=10009…secp`. `norm_band_law_proof_v1.py`.)*

**[PROVED] All nontrivial multiplicative characters exactly uniform.** For `k|(p−1)`,
`χ_k(X)=X^{(p−1)/k}` has each fiber of size exactly `(p−1)/k` (orthogonality). `χ₆` fibers
`(p−1)/6`, verified by exact enumeration at `p=100003` (all = 16667); `Σ_X ζ₆^{χ₆(X)}=0`
exactly. *(`lift_chi6_uniform_law_proof_v1.py`.)*

**[PROVED/VERIFIED] GLV = multiplication of the lift by a cube root of unity.**
`φ(x,y)=(βx,y)`, `β≡ω² (mod π_p)`. Exact over 40000 samples:
`χ₆(βx)=χ₆(x)+4`, `χ₃(βx)=χ₃(x)+1` (a GLV triple `{x,βx,β²x}` hits all three cubic
classes), `χ₂(βx)=χ₂(x)`. GLV orbit-sextant triples ~98% same parity (β=ω²=2-sextant even
rotation). *(`glv_orbit_structure_proof_v1.py`, `y_orbit_class_investigation_v1.py`.)*

**[PROVED] `S₃` `[ω]`-covariance.** The 3rd Semaev polynomial for `y²=x³+7`,
`S₃=(x₁−x₂)²x₃²−2((x₁+x₂)x₁x₂+14)x₃+(x₁²x₂²−28(x₁+x₂))`, satisfies
`S₃(βx₁,βx₂,βx₃)=β·S₃` exactly (β-eigenvector); `{S₃=0}` is `[ω]`-invariant.
*(`frontier_beyond_singlex_v1.py`.)*

**[PROVED] `y`-coordinate symmetries.** `χ₂(y(n−d))=−χ₂(y(d))` (`p≡3 mod4`); and
`χ₂(y([λd]G))=χ₂(y([d]G))` (`[λ]=φ` fixes `y`). So `f=χ₂(y)` transforms by the `μ₆` sign
character. *(`chi2y_harmonic_v1.py`.)*

---

# PART III — CM / endomorphism-ring structure

**[VERIFIED] `End(E) = ℤ[ω]`, the maximal order.** For any `j=0` curve `φ:(x,y)↦(βx,y)`
(`β³=1`) is a visible endomorphism with `φ²+φ+1=0`, so `ℤ[ω] ⊆ End(E)`, and
`End(E)⊆O_K` forces `End(E)=ℤ[ω]`. Confirmed via a mod-`ℓ²` crater/floor test validated on
8112 `(curve,ℓ)` cases vs brute force (0 mismatches): **every case is a crater, zero
floors** — secp sits on the crater (single vertex) of every isogeny volcano. Class number
`h(End(E))=h(−3)=1`. Conductor of the Frobenius order `ℤ[π]`:
`f = 3·79·349·2698097·1359580455984873519493666411` (last 90-bit prime),
`disc(ℤ[π])=t²−4p=−3f²`. *(`secp256k1_cycles_findings.md`.)*

**[VERIFIED] `μ₆` acts FREELY on `E(𝔽_p)\{O}`.** `[ω]` fixes only `E[ω−1]` (`3∤n`); negation
fixes 2-torsion (`2∤n`). So `E(𝔽_p) = {O} ∪ (n−1)/6` free orbits of size 6, exactly
`(n−1)/6 = 19298681539552699237261830834781317975472927379845817397100860523586360249056`
orbits. *(`secp256k1_cycles_findings.md`.)*

**[VERIFIED] Sextic structural identities** (`sextic_identities_verify.py`):
- **`π_n = π − 1`** is the explicit generator of the prime above `n`: over the 6 units,
  `u=−1` is the **unique** unit with `N(π+u)=n`; `N(π−1)=p−t+1=n`, `n≡1(3)` splits.
  `π_n = 367917413016453100223835821029139468248 + 303414439467246543595250775667605759171·ω`.
- Sextic classes of the curve constant: `[7/π_p]₆ = ζ₆⁵`, `[7/π_n]₆ = ζ₆¹`; the amicability
  carrier `[7/π_p]₆/[7/π_n]₆ = ζ₆⁴ = ω²` (a nontrivial cube root).
- Exact 4-D sextic character `ε = ζ₆^{3−[28/π]₆}` (validated on 44 primes + 256-bit scale).

**[VERIFIED] Frobenius data.**
- **Angle** `cos θ = t/(2√p) = 0.63538465…`, `θ = 50.55°` (30th percentile of the CM
  ordinary Sato–Tate / Hecke angle law — typical, not extreme).
- **Hasse invariant** `= a_p mod p = t` (coeff of `x^{p−1}` in `(x³+7)^{(p−1)/2}`; verified
  on small `j=0` curves).
- **p-adic unit root** `α` (`αβ̄=p`): Hensel-lifts from `α≡t (mod p)`; next digit
  `(α mod p²)/p = 103482995291570382327745514962295612511852368578636630096241337387108360383642`;
  `α²−tα+p≡0 (mod p³)` verified.
- **`ord_p(t) = (p−1)/6`** = first `p`-torsion degree; the trace has multiplicative index
  `6 = |μ₆|` in `𝔽_p*` (parallels `ord_n(2)=(n−1)/64`).

**[VERIFIED] Galois images.**
- **mod-2:** `x³+7` is irreducible over `𝔽_p` (`−7` a non-cube) ⇒ 2-torsion field `𝔽_{p³}`,
  Frobenius acts on `E[2]` as a **3-cycle** (image `ℤ/3`); no rational 2-torsion.
- **mod-ℓ:** Frobenius `⊂` Cartan for all `ℓ` — split-Cartan (`ℓ≡1 mod3`), nonsplit
  (`ℓ≡2`), scalar (`ℓ=3`). CM structure.

**[VERIFIED] Extension tower.** `E(𝔽_{p^k}) ≅ ℤ/d₁×ℤ/d₂`, `d₁(k)=gcd(A_k−1,B_k)` with
`π^k=A_k+B_kω`. Torsion-degree tower: full `E[ℓ]` enters `E(𝔽_{p^k})` iff `deg(ℓ)|k`, with
`deg(3)=2, deg(2)=deg(7)=3, deg(13)=4`. `E(𝔽_p)` cyclic (order `n` prime); first non-cyclic
at `k=2` (`d₁=3`). *(`secp256k1_cycles_findings.md`.)*

**[VERIFIED] Forced arithmetic facts (`n` prime + CM by `ℤ[ω]`).** `7` is a QNR mod `p`;
`−7` a non-cube; `3∤n`; `p≡3 (mod 4)`; the `y`-fibration `E→E/[ω]≅ℙ¹` ramifies at `E[ω−1]`
with no rational ramification. *(`y_orbit_class_investigation_v1.py`.)*

---

# PART IV — The curve L-function & formal group

**[VERIFIED / CITED-theorem] Curve L-function and its RH.** `L(T)=1−tT+pT²=(1−πT)(1−π̄T)`;
`|π|=√p` verified to 40 digits — the **Riemann Hypothesis for `E/𝔽_p` (Hasse=Weil), a
theorem**. In the `s`-plane (`T=p^{-s}`) the zeros lie **exactly on `Re(s)=1/2`**, at height
`±θ/log p`. The "self-adjointness" pinning the critical line is the **Weil pairing** making
Frobenius unitary (`ππ̄=p` = the functional equation). Supersingular characterization:
`a_ℓ=0 ⟺ χ₋₃(ℓ)=(ℓ/3)=−1` (`ℓ≡2 mod3`). *(`secp256k1_Lfunction_intersections.md`.)*

**[VERIFIED] Formal-group logarithm — exact closed form.** For `E:y²=x³+7` in `T=−x/y`:
```
L(T) = Σ_{k≥0}  7^k · C(3k,k) / (6k+1) · T^{6k+1}
     = T + 3T^7 + (735/13)T^13 + (28812/19)T^19 + (237699/5)T^25 + (50471421/31)T^31 + …
```
Verified exactly against the series of `∫dx/2y` to `k=6` (`T³⁷`); every nonzero exponent
`≡ 1 (mod 6)` up to `T⁴³`. **`μ₆-sparsity`** = negation (odd exponents) × cube-root CM
(`≡1 mod3`). Hypergeometric CM signature `L(T)=T·₂F₁(1/3,1/6;7/6;−27·7·T⁶/4)`-type; family
fact `L(T)=Σ b^k C(3k,k)/(6k+1) T^{6k+1}` for `y²=x³+b` (secp = `b=7`).
*(`secp256k1_formal_group_finding.md`.)*

**[VERIFIED] Whole-group L-series hypergeometric form.**
`L(T) = T·₃F₂(1/6,1/3,2/3; 1/2,7/6; 27·7·T⁶/4)` — linearizes `E₁(ℚ_p)` (the formal
subgroup). The curve is **not anomalous** (no twist trace `±1`; base trace 129-bit,
smallest twist 128-bit), so the Smart/Satoh–Araki linearization applies only to `E₁`.
*(`zomega_lattice_probe_findings_v1.md`.)*

---

# PART V — Twist structure & the Frobenius sieve

**[VERIFIED] The six sextic twists.** Each twist has Frobenius `u·π_p`, `u∈μ₆`; orders
`= N(π_p+u)`, summing to `6(p+1)`. `b=7 ↔ u=1+ω` is the unique prime-order twist.
*(`KNOWN_FACTS_secp256k1_and_keys_v5.1.md`, atlas.)*

**[VERIFIED] Quadratic twist order.** `n_t = 2(p+1)−n = 3²·13²·3319·22639·C`,
`C = 1013176677300131846900870239606035638738100997248092069256697437031` (216-bit,
**prime**). `169 | n_t` ⇒ the twist has a **rational subgroup of order 169** (the `13²` is
the CM-structural / embedding-tower factor). `ord_n(2)=(n−1)/64`.
*(`sextic_identities_findings.md`, atlas.)*

**[VERIFIED] Frobenius sieve — twist-order divisibility law.** `freq(ℓ|n_t) = P(Frobenius
has eigenvalue −1 mod ℓ)`; concretely `ℓ|n_t ⟺` the Frobenius eigenvalue is `−1` mod `ℓ`.
A sign-definite dependence law, verified 24/24 across two CM fields and generalizing across
CM discriminants (primes `<12000`). *(`cm_twist_order_divisibility_2026_07_10.md`,
`cm_imprint_ramified_prime_findings.md`.)*

---

# PART VI — Amicability

**[VERIFIED] `(p,n)` is an amicable pair — a length-2 aliquot cycle `p→n→p`.** By direct
point-counting (`q↦#E(𝔽_q)` via `ℤ[ω]` factorization + the exact sextic character, validated
on 44 small primes, both iterates of 14 amicable/anomalous cases vs brute force, and at
256-bit scale `#E(𝔽_p)=n`): **`#E(𝔽_n)=p` exactly.** Structural reason: Frobenius at `p` is
`π` (`#E(𝔽_p)=N(π−1)=n`), Frobenius at `n` is `1−π`, and `(1−π)−1=−π` has norm `p`. This is
CM-abundance (Silverman–Stange: `≫X/(log X)²` for CM curves) — secp exemplifies it, not an
exception. *(`sextic_identities_findings.md`.)*

**[EMPIRICAL] Amicable-pair density.** The 2-cycle closure rate `~0.27` is consistent
(<1σ) with the Silverman–Stange Conjecture 40 value `13/50 = 0.26`; the exact `26/100`
census is unaudited. *(`secp256k1_amicable_13_50_confirmed_2026_07_11` (memory).)*

**[VERIFIED] Hecke character.** `χ(π) = −(28/π)₆^{-1}` — a single sextic symbol, confirmed
206/206 primes; `χ(π_p)=1` two independent ways. *(`secp256k1_hecke_character_explicit_2026_07_11`.)*

**[VERIFIED] BSD / Tamagawa** for `y²=x³+7 /ℚ`: `∏c_ℓ=1`, `Ш=1`, Kodaira `II/II/II`,
`L(1)=Ω`. **[VERIFIED] Eisenstein-twin density = Bateman–Horn** (obs/pred = 0.9975,
`𝔖=1.672`). *(`secp256k1_bsd_tamagawa_resolved_2026_07_11`, `secp256k1_eisenstein_twin_density_2026_07_12`.)*

---

# PART VII — The RH-framework CM connection

**[PROVED] Eisenstein–Ramanujan survival law (CM analogue of the φ(n)-framework's core
lemma).** For the generalized Ramanujan sum `c_𝔫(β)=Σ_{r∈(ℤ[ω]/𝔫)*} e^{2πi Tr(βr)/𝔫}`:
1. **μ₆-invariance:** `c_𝔫(uβ)=c_𝔫(β)` for every unit `u∈μ₆` (units permute `(ℤ[ω]/𝔫)*`).
2. **Multiplicative:** `c_{𝔫₁𝔫₂}=c_{𝔫₁}c_{𝔫₂}` for coprime ideals (CRT).
3. **Closed form:** `c_𝔫(β)=μ_K(𝔫/𝔤)·Φ(𝔫)/Φ(𝔫/𝔤)`, `𝔤=gcd(𝔫,(β))`; prime-ideal values
   `N𝔭−1` if `𝔭|(β)`, else `−1`.
4. **Survival:** along a primorial ideal, a mode `β` stays bounded iff `β` is a unit ⇒ the
   infinite-lifetime modes are exactly **`μ₆` — six modes**, vs the **two** (`±1`) over `ℤ`.

**Operator side.** `ℚ(√−3)` has one complex place ⇒ its multiplicative object is `ℂ*` and
`Ĥ^CM = π(A_r² + A_θ²)`; in the `m`-basis `Ĥ^CM = ⊕_m π(A_r²+m²)`, self-adjointness transfers
from the rational operator, and the angular space splits into **6 sextic sectors
(`m mod 6`) ↔ the 6 units `μ₆`** — the operator image of the survival law. The sextic core
`6 = |μ₆| = |Aut(secp)|` is the same symmetry running through `ord_p(t)=(p−1)/6`, the
`μ₆`-sparse formal logarithm, and the `x`-line 6-orbits. *(`eisenstein_ramanujan_survival.md`,
`radial_selfadjointness.md`, `adelic_recasting_v2.md`.)*

---

# PART VIII — The (n,k,D) decomposition, domain & datasets

**[VERIFIED] Scalar arithmetic.** `n` splits (`n≡1 mod3`) ⇒ `ℤ[ω]/(π_n) = 𝔽_n = ℤ/nℤ`; the
scalar is **1-dimensional** in `ℤ[ω]` (a 2-D coordinate would exist only if `n` were inert).
The GLV pair `(a,b)` is a non-canonical Babai coset rep, not an invariant of `d`.
*(`btc_puzzle_zomega_scalar_is_Fn_2026_07_12`, `zomega_lattice_probe_findings_v1.md`.)*

**[VERIFIED] (n,k,D) validity domain map.** Coprimality is the only label obstruction; the
`D`-gap narrows with `n`; the GLV 2-D→1-D degeneracy transition is exactly `N=128`;
order-overflow at `N=256` is `~2^{-128}`. Farey `(n,k)` via exact best-rational
(`|a·n−k·b|` minimization; no floating point). *(`build_fullrange_dataset_v1.py`,
`nkd_validity_domain_v1.py`, `btc_puzzle_fullrange_dataset_nkd_domain_2026_07_13`.)*

**[VERIFIED] Curve automorphism speedup ceiling.** `√6 ≈ 2.45×` (`μ₃ √3` + negation `√2`) —
a theorem about `|Aut(E)|=6`. *(`zomega_lattice_probe_findings_v1.md`.)*

**Datasets.** `puzzles_verified.csv` (real solved keys, validation ground truth);
`constructed_keys_fullrange_v1.npz` (36k known-`d`, 21k at 256-bit, full range;
`build_fullrange_dataset_v1.py`); the **100k MT19937 set** (our MT19937 through the same
select-bitlength→curve pipeline — a full-power known-generator reference; run tests on both).

---

# PART IX — Empirical observations on the solved-key set (underpowered — not established)

These are measured directional hints on the 82 real solved keys, **not** established
findings; flagged so the silo can extend them if more puzzles are solved. Both are
control-backed (planted-signal controls fire at `p≈0`) but do **not** reach significance.

- **[EMPIRICAL, underpowered]** cubic-residue **class-0 lean**: real `44%` vs synthetic
  `33%` uniform baseline, `p≈0.11` (82 keys); baseline confirmed flat (not an interval
  artifact). *(`zomega_lattice_probe_findings_v1.md`, `key_cubic_char_v2.py`.)*
- **[EMPIRICAL, underpowered]** multiplicative **smoothness lean**: real keys slightly more
  composite than uniform, `p=0.058` raw (does not survive Bonferroni×8). Same direction as
  the cubic lean. *(`multilens_sweep_v1.py`.)*

---

# PART X — Proof manifest (items tagged PROVED)

1. Lemma A — `eis` bijection ⇒ lift multiset `= ℤ[ω]∩P` uniform. (II)
2. Rhombus theorem — reduced basis both norm `p`; `P` a 60° rhombus; universal. (II)
3. One-parameter angle law + closed-form sector proportions; `1/8` universal (`√3/16`). (II)
4. Norm-band law — universal, mean `1/6`, density const `2π/√3` on `[0,3/16]`. (II)
5. All nontrivial `χ_k` marginals exactly uniform; `χ₆` fibers `(p−1)/6`. (II)
6. GLV `β≡ω²`; character shifts `χ₆:+4, χ₃:+1, χ₂:fixed`. (II)
7. `S₃` `β`-eigenvector under `[ω]`. (II)
8. `y` symmetries `χ₂(y(n−d))=−χ₂(y(d))`, `f(λd)=f(d)`. (II)
9. `End(E)=ℤ[ω]` maximal; `μ₆` acts freely (`(n−1)/6` orbits). (III)
10. Eisenstein–Ramanujan survival law (μ₆-invariance, multiplicativity, closed form,
    unit-survival). (VII)

Plus classical-theorem inputs used as verified facts: RH for `E/𝔽_p` (Hasse–Weil),
`ℤ[ω] ⊆ End` for `j=0`, Silverman–Stange CM amicable abundance.

---

# Appendix A — foundational code

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
    if u == 0 and v == 0: return 0
    for k in range(6):
        if v >= 0 and (u - v) >= 0 and u > 0: return k
        u, v = v, v - u
    return 0 if v >= 0 else 3
```

### A.3 Formal-group logarithm (reproduce with sympy)

```python
import sympy as sp
z = sp.symbols('z'); w = sp.symbols('w')
# curve in (z=T=-x/y, w=-1/y):  w = z^3 + 7 w^3  ->  x=z/w, y=-1/w
wser = sp.Integer(0)
for _ in range(8):                       # fixed-point iterate for w(z)
    wser = sp.series(z**3 + 7*wser**3, z, 0, 46).removeO()
x = sp.series(z/wser, z, 0, 46).removeO()
y = sp.series(-1/wser, z, 0, 46).removeO()
L = sp.integrate(sp.series(sp.diff(x, z)/(2*y), z, 0, 44).removeO(), z)
# L(T) = sum_k 7^k * C(3k,k)/(6k+1) * T^(6k+1);  nonzero exponents all == 1 (mod 6).
```

---

# Appendix B — script & document manifest

All in `btc_puzzle_investigation/`. Proof scripts import A.1/A.2, use exact arithmetic in
the signal path, and print their own verification.

| file | proves / verifies |
|---|---|
| `lift_sextant_rhombus_law_proof_v2.py` | rhombus theorem, angle law, `1/8` invariant (II) |
| `lift_sextant_law_clarifications_v1.md` | exact rational sector forms; error term (II) |
| `lift_chi6_uniform_law_proof_v1.py` | `χ₆` exactly uniform; character-sum `=0` (II) |
| `norm_band_law_proof_v1.py` | universal norm-band law, mean `1/6` (II) |
| `glv_orbit_structure_proof_v1.py` | `β≡ω²`; GLV character shifts; `y` fixed (II) |
| `y_orbit_class_investigation_v1.py` | orbit-sextant parity; `S₃` covariance; forced facts (II,III) |
| `frontier_beyond_singlex_v1.py` | `N(π_p−1)=n`; module structure; eigendifferential (III) |
| `chi2y_harmonic_v1.py` | `y` symmetries; multiplicative-basis structure (II) |
| `sextic_identities_verify.py` | `π_n=π−1`, unique unit, sextic classes, `n_t` factorization (III,V) |
| `secp256k1_order_fingerprint.py` | `p−1`, `n−1` factorizations; index structure (III) |
| `build_fullrange_dataset_v1.py` | constructs the 36k full-range known-`d` dataset (VIII) |
| `nkd_validity_domain_v1.py` | (n,k,D) validity domain map (VIII) |

Findings documents with the exact detail (curve/CM side):
`secp256k1_formal_group_finding.md` (IV) · `secp256k1_Lfunction_intersections.md` (IV) ·
`secp256k1_cycles_findings.md` (III) · `sextic_identities_findings.md` (III,V,VI) ·
`cm_twist_order_divisibility_2026_07_10.md` + `cm_imprint_ramified_prime_findings.md` (V) ·
`eisenstein_ramanujan_survival.md` + `radial_selfadjointness.md` + `adelic_recasting_v2.md`
(VII) · `zomega_lattice_probe_findings_v1.md` (IV,VIII) · `KNOWN_FACTS_secp256k1_and_keys_v5.1.md`
(master) · `secp256k1_pure_arithmetic_study` / `secp256k1_arithmetic_v4.md` (Part-I consolidation).

*End of compendium. Every tagged item above is reproducible from the named script/document;
each proof script prints its own exact verification when run.*
