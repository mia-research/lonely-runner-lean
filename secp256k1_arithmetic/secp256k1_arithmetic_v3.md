# The Arithmetic of secp256k1 — a pure-structure study

**Version 3 · 2026-07-11.** Changes from v2 (same day; scripts
`test_claims_v1.py`, `rho_b_investigate_v1.py`): (i) §4 — **BSD closes
cleanly**, no Tamagawa tension: from-scratch `L(1)=Ω=3.0414…` (exact `a_n` to
n≤4000) gives `L(1)/Ω=1`, and since `y²=x³+7` is globally minimal with BSD a
theorem (CM, rank 0), every `c_ℓ=1` and `Ш` is trivial — the v2 thread-D worry
was a mis-read of Kodaira types (all Type II). (ii) §4 — the single symbol
generalizes to `u_b(π)=−(4b/π)₆⁻¹`, and the per-b closure constants
`ρ_b = {½, 13/50, 18/101, 1/10}` for `b=2,7,3,5` **predict the amicable-pair
abundance ordering, verified 4/4** against direct enumeration. (iii) An
external results table was adjudicated (`CLAIMS_ADJUDICATION_v1.md`); two rows
corrected: "amicability automatic when n prime" (false for j=0 — 12/22
counterexamples) and "Ω≈6.0828" (= 2Ω, the `dx/y` period, not the Néron
period). (iv) §4 — **thread B settled**: our ρ_k **is** Silverman–Stange
Conjecture 40 (+27), verified as exact rationals across all 12 residue classes
mod 36 (`census_ss_v1.py`); `13/50` for k=7 is *their* conjectural value, not a
new result — novelty demoted to reconstruction + explicit character + 256-bit
instance. (v) §2 — **thread C**: three-term ASD holds for all 147 split ℓ<2000;
mod-ℓ³ upgrade locus = exactly `{a_ℓ ∈ ±1}`; scalar δ_ℓ has no elementary form
(`thread_C_supercong_v2.py`). (vi) §6 — **thread E**: the zeros of `L(ψ,s)` are
computed from CM eigenvalues, γ₁=0.8173126364 matches LMFDB to 10 digits,
functional equation to 30 digits — §6 upgraded to "verified instance"
(`thread_E_zeros_v1.py`). (vii) §3 — **thread A**: `χ(π)=−(28/π)₆⁻¹` is now
*derived* from the Jacobi-sum Grössencharacter + sextic reciprocity, verified
1442/1442 (`thread_A_reciprocity_v2.py`), not just a fit. (viii) §6 — the
**spectral-realization boundary** is mapped precisely (`SPECTRAL_REALIZATION_v1.md`):
explicit formula (theorem, verified) / Connes ψ-sector (χ names it, selection not
construction) / global operator (open); local HP a theorem with a proven global
obstruction. *v2 changes retained below.* Prior v2 note: §3 single symbol
`χ(π)=−(28/π)₆⁻¹`, §2 three-term ASD + radius `T_c⁶=4/(27b)`.

A standalone mathematical study of the curve
`E : y² = x³ + 7` over `𝔽_p`, `p = 2²⁵⁶ − 2³² − 977`, with no reference to keys,
puzzles, or attack surfaces. It consolidates the five exact results of the
2026-07 arithmetic investigation, places each against the published record, and
states why this particular curve occupies a distinguished point in the landscape
of CM elliptic curves.

**Verification.** Every claim tagged **[✓ v1]** was re-verified from scratch on
2026-07-11 by `verify_v1.py` in this directory (30/30 checks, exact
integer/Fraction arithmetic wherever a claim is decided). Claims tagged
**[relayed]** rest on recorded prior-session computations (scripts named in
§9) that were not re-run today. Claims tagged **[math]** follow from arguments
given in the text. Nothing here is asserted from memory alone.

**Notation.** `p = 2²⁵⁶ − 2³² − 977`; `n = #E(𝔽_p)` (prime);
`t = p + 1 − n = 432420386565659656852420866390673177327`;
`ω = e^{2πi/3}`, `ℤ[ω]` the Eisenstein integers, `μ₆ = ℤ[ω]^* = {±1, ±ω, ±ω²}`;
`K = ℚ(√−3)`; `N(x + yω) = x² − xy + y²`; `Tr(x + yω) = 2x − y`.
Frobenius `π_p = a + bω` with
`a = 367917413016453100223835821029139468249`,
`b = 303414439467246543595250775667605759171`,
`N(π_p) = p`, `2a − b = t` **[✓ v1]**.

---

## 1. The global object

secp256k1 is the reduction mod p of the Mordell curve `y² = x³ + 7 / ℚ`:
rank 0, trivial torsion, conductor `N_E = 21168 = 2⁴·3³·7²`, bad primes
`{2, 3, 7}`, additive reduction at 7 [relayed: `secp256k1_global_mordell.py`;
LMFDB tabulates the curve at conductor 21168].

Its endomorphism ring is decided by a visible automorphism: `φ(x,y) = (βx, y)`
with `β³ = 1` satisfies `φ² + φ + 1 = 0`, so `ℤ[ω] ⊆ End(E)`; since `ℤ[ω]` is
the maximal order of `K`, `End(E) = ℤ[ω]` — CM by the full ring of Eisenstein
integers, discriminant −3, class number 1, `j = 0` **[math; φ(G) = [λ]G
✓ v1]**. Two consequences used throughout:

- `Aut(E) = μ₆`, the largest automorphism group an elliptic curve in
  characteristic ≠ 2,3 can have. μ₆ acts freely on `E(𝔽_p) \ {O}`, giving
  `(n−1)/6` orbits of size 6 [math].
- `h(−3) = 1` puts the curve on a single-vertex isogeny volcano at every
  prime: there is no isogeny structure beyond the CM itself [relayed].

The classical CM norm form holds in the strong (primary) shape:

```
4p = t² + 27M²,   M = 101138146489082181198416925222535253057   [✓ v1]
```

The factor 27 (rather than the generic 3) records that the primary
representative of `π_p` is itself the arithmetically normalized Frobenius —
see §3.

---

## 2. The formal group logarithm

The formal group of `E` in the standard parameter `T = −x/y` has logarithm

```
L(T) = Σ_{k≥0}  7^k · C(3k,k)/(6k+1) · T^(6k+1)
     = T + 3T⁷ + (735/13)T¹³ + (28812/19)T¹⁹ + (237699/5)T²⁵ + ⋯
```

**[✓ v1]** — recomputed today by exact power-series expansion of `∫ dx/2y`
through `T⁴⁹` (k ≤ 8), from the Weierstrass recursion `w = z³ + 7w³` alone.
(An earlier draft note quoting `56/13` for the `T¹³` coefficient is wrong;
`7²·C(6,2)/13 = 735/13` is the verified value.)

Three exact structural facts:

1. **μ₆-sparsity.** Every nonzero exponent is `≡ 1 (mod 6)` **[✓ v1]**. This
   is forced by the full automorphism group acting on the invariant
   differential: negation `[−1]` kills even exponents; the CM automorphism
   `[ω]` kills exponents `≢ 1 (mod 3)`. A generic curve's formal log is merely
   odd; a `j = 0` curve's is supported on `1 mod 6`. The formal log is exactly
   as sparse as `Aut(E)` allows.

2. **Hypergeometric closed form.** The exact term-ratio identity

   ```
   a_{k+1}/a_k = (27b/4) · (k+1/6)(k+1/3)(k+2/3) / ((k+1/2)(k+7/6)(k+1))
   ```

   holds in ℚ for all k **[✓ v1]**, i.e.

   ```
   L(T) = T · ₃F₂( 1/6, 1/3, 2/3 ; 1/2, 7/6 ; 27·7·T⁶/4 ).
   ```

   (This corrects the looser "₂F₁-type" phrasing in the 2026-07-09 finding
   note: the ratio has an irreducible cubic numerator, so the series is a
   genuine ₃F₂.)

3. **Family fact.** For every `y² = x³ + b`,
   `L(T) = Σ b^k C(3k,k)/(6k+1) T^(6k+1)` — verified for `b = 1..8`
   **[✓ v1]**. secp256k1 is the `b = 7` member; the curve constant enters
   only as the geometric weight `b^k`.

**The bridge to the L-function (Atkin–Swinnerton-Dyer/Honda congruence,
explicit instance).** At a split prime `ℓ = 6k + 1`, the coefficient of `T^ℓ`
is `c_ℓ = 7^k C(3k,k)/ℓ` — the unique denominators divisible by ℓ occur
exactly at these indices — and the congruence `ℓ·c_ℓ ≡ a_ℓ (mod ℓ)` holds:

```
7^k · C(3k,k) ≡ a_ℓ (mod ℓ = 6k+1)      e.g.  735 ≡ 7 (mod 13),  28812 ≡ 8 (mod 19)
```

verified for every split prime `ℓ < 200` **[✓ v1]**. The numerators of the
formal-group logarithm reduce, prime by prime, to the Hecke eigenvalues of §3.
At `ℓ = p` itself this is the statement that the Hasse invariant is
`7^{(p−1)/6}·C((p−1)/2, (p−1)/6) ≡ t (mod p)` [math + relayed small-scale
check]. The congruence family is classical (Honda; cf. the supercongruence
literature, arXiv:1210.4489); the explicit `7^k C(3k,k)` instance for this
curve is the study's own tabulation.

Two refinements **[✓ v2]** (writing `b_m = 7^{(m−1)/6}·C((m−1)/2,(m−1)/6)`):

- **Three-term ASD:** `b_{ℓ²} − a_ℓ·b_ℓ + ℓ ≡ 0 (mod ℓ²)` at all ten split
  primes tested (13…97), with sporadic mod-ℓ³ upgrades at ℓ = 37, 61. The
  naive extension `b_m ≡ a_m (mod m)` holds for m ≡ 1 (mod 6) **except**
  exactly when m has two coprime norm components (91, 169, 325 = 5²·13, …) —
  the congruence is prime-power local, as Honda's theorem dictates.
- The mod-ℓ² correction `δ_ℓ = (b_ℓ − a_ℓ)/ℓ·a_ℓ^{−1} (mod ℓ)` is **not** a
  fixed rational combination of the Fermat quotients q_ℓ(2), q_ℓ(3), q_ℓ(7)
  (exhaustive small-coefficient search); its closed form is open (thread C).

**Radius and boundary [✓ v2].** The series' radius of convergence is exactly
`T_c = (4/27b)^{1/6}` — the hypergeometric argument `27b·T⁶/4` reaching 1 —
and geometrically T_c is the T-chart ramification point `x³ = 2b`,
`P* = ((2b)^{1/3}, √(3b))`. The boundary value is an incomplete beta:
`₃F₂(1/6,1/3,2/3;1/2,7/6;1) = (27/4)^{1/6}/6 · B(1/3; 1/6,1/3) = 1.18796…`,
and `L(T_c)/Ω = 0.205428…` is not a small rational — `P*` is **not** torsion
(doubling sends `x ↦ −x/2` there, exactly), consistent with rank 0.

---

## 3. The Hecke character, reconstructed from point counts

`L(E/ℚ, s) = L(ψ, s)` for a Grössencharacter ψ of `K = ℚ(√−3)` with ∞-type
`(1,0)`: `ψ((α)) = χ(α)·α` on ideals prime to the conductor, where χ is a
finite character. The investigation computed ψ **from point counts alone**
(no tables), and the pieces cross-check:

- **Conductor** `𝔣 = (2²)·(√−3)²·(7)`, `N_{K/ℚ}(𝔣) = 84² = 7056`;
  conductor–discriminant: `N_E = |d_K|·N(𝔣) = 3·7056 = 21168` — matching the
  curve conductor exactly [relayed: `hecke.py` rounds 18/27; the earlier
  candidate `𝔣` of norm 441 fails this identity and is refuted].
- **Finite part** χ is a **primitive order-6 ray-class character** of the ray
  class group `Cl_𝔣` (order 432), ramified at 2, 3, 7 — and it **is a single
  rational sextic symbol on primary generators**:

  ```
  χ(π) = −(28/π)₆^{−1}     (π primary),   so   ψ(𝔭) = −(28/π)₆^{−1}·π
  ```

  **[✓ v3 — derived]**, and it is a *derivation*, not a fit
  (`thread_A_reciprocity_v2.py`): the classical Jacobi-sum Grössencharacter
  (Ireland–Rosen ch. 18 / Weil 1949), reconstructed independently and verified
  link-by-link on split primes < 3000. With `λ = χ₆³` (quadratic), `ρ = χ₆²`
  (cubic), the point count `a_p(k) = −Σ_x λ(x³+k)` reduces via
  `#{x:x³=t}=1+ρ+ρ²` to `a_p(k) = −Tr(χ̄₆(k)·A)`, `A = Σ_s λ(1+s)ρ(s)` a Jacobi
  sum with `N(A) = p` (1442/1442 identity; `N(A)=p` 206/206); sextic reciprocity
  puts it in the canonical, primitive-root-free form
  `a_p(k) = Tr(−(4k/π)₆⁻¹·π)` — all six twists + k=7, **1442/1442**. The
  `4 = 2²` is the 2-supplement (the `(2²)` conductor part); `k` the curve
  constant; `28 = 4·7`. Independently, the formula was first *found* as the
  unique survivor of an exhaustive symbol search (147 primes<2000, revalidated
  to 5000; class-constant mod 28, 432 classes = |Cl_𝔣|, 0 violations
  <5·10⁵) — the two agree. **This withdraws v1's "not a single rational
  sextic symbol"** — the recorded round-18 test tried `(28/π)₆` but not its
  negated inverse. The local decomposition
  `χ(π) = χ₄(π mod 4)·(π/π₇)₆⁵·(π/π̄₇)₆⁵` (verified on 329 primes [relayed:
  round 20]) is the same character with the 7-part flipped by sextic
  reciprocity; χ₄ is the reciprocity supplement, not an independent 2-adic
  degree of freedom. (Derivation from reciprocity + reconciliation with the
  Ireland–Rosen/Weil Jacobi-sum formula: thread A, `THREADS_v1.md`.)
- **Calibration capstone.** χ learned from primes `< 3000` predicts the
  256-bit Frobenius exactly: `χ(π_p) = 1`, so `ψ(𝔭_p) = π_p`, trace `t`,
  `#E(𝔽_p) = n` [relayed: round 18]. Two independent shadows of
  `χ(π_p) = 1` were re-verified today: the primary norm form `4p = t² + 27M²`
  and the point count `#E(𝔽_p) = n` **[✓ v1]**.
- **Theta identity.** `f = Σ_{𝔞 ⊆ ℤ[ω]} ψ(𝔞) q^{N(𝔞)}` reproduces the
  point-count newform coefficient-by-coefficient for `n ≤ 120`
  (`f = q + 7q¹³ + 8q¹⁹ − 5q²⁵ + ⋯`) [relayed: round 26]; the spot values
  `a₁₃ = 7`, `a₁₉ = 8` were re-counted today **[✓ v1]**.
- **Trace laws** (all good `ℓ < 200`, re-verified today **[✓ v1]**):
  `a_ℓ = 0 ⟺ ℓ ≡ 2 (mod 3)` (supersingular at inert primes), and at split ℓ
  the ℤ[ω] norm form `4ℓ = a_ℓ² + 3g²`. (The stronger `27m²` shape is
  special to primes where the unit is ±1, as at p; asserting it for all split
  ℓ is false and was caught by today's battery.)
- **Root number and L(1).** `W(E) = +1`, self-verified from point-count data
  via theta parity, and `L(E,1) = Ω` with

  ```
  Ω = Γ(1/3)Γ(1/6) / (2√π · 7^{1/6}) = 3.0414172284…
  ```

  [relayed: round 19; the closed form was re-verified against direct
  numerical integration of `∫ dx/√(x³+7)` to 10 digits today **[✓ v1]**].
  One recorded caveat stands: a "π ≡ −1 ⇒ all local root numbers +1"
  shortcut argument is a non-sequitur (3 is bad with nontrivial local root
  number); `W = +1` is correct but is fixed by the bad fibers and ∞.
- **BSD closes cleanly [✓ v3].** Recomputed from scratch (exact `a_n` to
  `n ≤ 4000`, approximate functional equation): `L(E,1) = 3.041417228428`,
  giving `L(1)/Ω = 1.000000000`. Since `y² = x³ + 7` is a **global minimal
  model** (`Δ = −2⁴·3³·7²`, every `v_ℓ(Δ) < 12`), `dx/2y` is the Néron
  differential and Ω = 3.0414 **is** the BSD real period. BSD for analytic
  rank 0 is a theorem here (CM, Rubin/Kolyvagin), so

  ```
  L(1)/Ω = (∏_ℓ c_ℓ · #Ш) / #E(ℚ)_tors² = 1  ⇒  every c_ℓ = 1,  #Ш = 1
  ```

  (torsion trivial). All Tamagawa numbers are 1 and Ш is trivial; the bad
  fibres at 2, 3, 7 are all Kodaira **Type II** (`c = 1`). A separate note is
  that the *analytic conductor* is `A(ψ) = N/(2π)² = 21168/(4π²) = 536.19`.
  Caution on normalization: `∫_{E(ℝ)} |dx/y| = 2Ω = 6.0828` is a real
  quantity but is **not** the BSD period; only `Ω = 3.0414` satisfies
  `L(1) = Ω`.

**Where `ζ(s)L(s, χ₋₃)` actually enters.** `L(ψ, s)` is a *primitive* degree-2
L-function; it does **not** factor as `ζ(s)L(s, χ₋₃)` — that product is the
Dedekind zeta `ζ_K(s)`, the weight-0 object of the same field. The precise
connections are: (i) the same splitting law `χ₋₃` governs both — it decides
which Euler factors of `ζ_K` split and which coefficients of `L(ψ,s)` vanish
(`a_ℓ = 0` exactly at inert ℓ); (ii) classically, the symmetric square
factors as `L(Sym²E, s) = L(ψ², s)·L(χ₋₃, s−1)` [math, standard CM
factorization]; (iii) on the Selberg-class axis, a measured check: the
vertical-variance constant of `L(ψ)` matches ζ (`n_L ≈ 0.99` vs `1.00`),
while the *reducible* `ζ_K` gives 2 — primitivity, not degree, is the
invariant [relayed: `lfunc_sigma_profile.py`].

---

## 4. The amicable pair (p, n)

`#E(𝔽_p) = n` **and** `#E(𝔽_n) = p` — the same equation `y² = x³ + 7` read
over either prime — re-verified today in both directions by random-point
order tests, decisive by Hasse uniqueness (each candidate is the only
multiple of the prime in its Hasse interval) **[✓ v1]**. In
Silverman–Stange's terminology (arXiv:0912.1831), `(p, n)` is an amicable
pair: a 2-cycle of the map `q ↦ #E(𝔽_q)`.

The algebraic mechanism is one subtraction in ℤ[ω]:

```
π_n = π_p − 1,     N(π_p) = p,   N(π_p − 1) = n      [✓ v1]
```

(the Frobenius at n is `1 − π_p`, and `(1 − π_p) − 1 = −π_p` has norm p).
At the level of the classical norm form this is the **shared-M identity**

```
4p = t² + 27M²,   4n = (t−2)² + 27M²,   same M      [✓ v1]
```

— p and n differ only by `t → t − 2`.

**The six-neighbor picture.** The six sextic twists of E over 𝔽_p biject with
the six units: twist orders are exactly `N(π_p + u)`, `u ∈ μ₆`, summing to
`6(p+1)`; among the six, **exactly one is prime — `u = −1`, order n**
**[✓ v1]**. So three statements are one: *unique prime-order twist = unique
prime unit-neighbor of the Frobenius = unique amicable twist*, all carried by
the ideal `(π_p − 1)`.

**The Frobenius quadratic.** `Q(c) = N(π_p − c) = c² − tc + p` packages the
family: `Q(0) = p`, `Q(1) = n`, `Q(−1) = n_t` (the quadratic-twist order).
`disc(Q) = t² − 4p = −27M²`, so for good ℓ (`ℓ ∤ M`) the number of roots of Q
mod ℓ is `1 + χ₋₃(ℓ)`: **inert primes divide no value of Q** — the same CM
dichotomy of §3, now as a sieve statement. Q is accordingly prime-rich
(Hardy–Littlewood constant ≈ 2.277, the `x²+x+1` constant) [relayed: round
24]; over `c ∈ [−200, 200]` the longest run of consecutive prime values is
exactly `{Q(0), Q(1)} = {p, n}` [relayed: round 22].

**The closure probability is 13/50, exactly [✓ v2].** Amicability is the
alignment `ψ(𝔮) = 1 − ψ(𝔭)` for `𝔮 = (ψ(𝔭) − 1)` — one Hecke-unit condition.
With the single-symbol formula of §3, this alignment is a **residue-class
function of the primary Frobenius mod 84** (verified: zero violations over
~20,000 split primes < 5·10⁵). Exact census of the 432 primary classes: 100
satisfy "π and π−1 both coprime to 84" (= 432·(2/3)·(1/2)·(25/36), the local
factors at 2, 3, 7), and **26 of those 100 close the 2-cycle**:

```
P( #E₇(𝔽_q) = ℓ  |  q = #E₇(𝔽_ℓ) prime )  =  26/100  =  13/50
```

— not the naive `1/|μ₆| = 1/6 ≈ 0.167`; the conductor biases the alignment
by +56%. Empirical check: 461/1729 = 0.2666 over ℓ < 5·10⁵ (0.6 SE from
0.26). The class computation is unconditional; reading the fraction as the
asymptotic probability assumes standard Chebotarev/Hecke equidistribution of
primary Frobenii along twin-norm primes. This sets up an exact
Silverman–Stange-type density conjecture for the j = 0 family
(thread B, `THREADS_v1.md`).

**"Automatic amicability" is false for j = 0 [✓ v3].** For CM curves with
`j ≠ 0` (unit group {±1}), `q = #E(𝔽_ℓ)` prime *forces* `#E(𝔽_q) = ℓ`
(Silverman–Stange). This does **not** transfer to our `j = 0` curve: a brute
counterexample hunt found that of 22 split ℓ < 1500 with `#E₇(𝔽_ℓ)` prime,
only 10 close and **12 fail** — e.g. `ℓ=43 → 31 → 21 ≠ 43`, `97 → 79 → 67`,
`211 → 199 → 189`. The six-unit μ₆ is exactly why: closure needs the alignment
above, which holds 13/50 of the time, not always. Any statement that treats
`(p, n)` amicability as an automatic consequence of `n` prime is importing the
{±1} theorem into the μ₆ setting.

**The constant is a per-b invariant [✓ v3].** The single symbol generalizes to
`u_b(π) = −(4b/π)₆⁻¹` (0 mismatches vs point counts, `b = 2,3,5,7`, all split
ℓ < 3000). Its mod-84 closure census gives exact per-b constants and — the
falsifiable test — they **order the amicable-pair abundance correctly, 4/4**:

```
b:        2       7       3        5
ρ_b:     1/2    13/50   18/101   1/10     (class census, exact)
#pairs:   34      21      15       11      (direct enumeration to X = 20000)
```

(`b = 1` is degenerate: `(−1,0)` is 2-torsion, all orders even, no amicable
pairs.) The magnitudes are not proportional — the full density carries a
b-dependent Hardy–Littlewood twin-norm constant `C_HL(b)` — but ρ_b fixes the
ordering.

**This is exactly Silverman–Stange Conjecture 40 [✓ v3].** Reading their j = 0
section (arXiv:0912.1831) settles the provenance: our ρ_b **is their published
conjectural value**, not a new one. Their **Conjecture 40** gives
`N_k^[1](X)/N_k(X) → 1/3 + R(k)` with `R(k)` a table in `k mod 36`, and
**Conjecture 27** gives amicable pairs `Q_k ~ ¼ N_k^[1]`. Since each pair
contributes two members, `ρ_k = 2Q_k/N_k = (1/2)(1/3 + R(k))`; for k = 7
(case (d), split, `R(7) = 2·7/(3·5²) = 14/75`) this is **exactly 13/50**, and
their own intro formula `1/6 + 1/(3(k−3))` for k ≡ 1,19 is the same ρ_k. We
verified the identity **as exact rationals** via a mod-12k class census
(`census_ss_v1.py`) for all twelve residue classes mod 36
(`k = 5,7,11,13,17,19,23,29,31,37`) — zero discrepancy — and by direct
enumeration within sampling error. So `ρ_7 = 13/50` for secp256k1 is an
evaluation of S–S's conjecture for the k ≡ 7 class they left untabulated; the
study's contribution here is the independent reconstruction (validating Conj 40
across all classes), the explicit single-symbol character `χ = −(4k/π)₆⁻¹` that
drives it, and the specific 256-bit instance — **not** a new theorem.

**Rarity at 256 bits.** For the `y² = x³ + b` CM family the measured amicable
density is `A(X) ≈ 0.10·X/(log X)²` (tracked at X = 10k…60k) [relayed: round
38], consistent with the Silverman–Stange CM-enhanced heuristic. At
`X = 2²⁵⁶` this makes the *lower member of an amicable pair* roughly a
1-in-1800 event among primes [math from the relayed constant; heuristic
extrapolation, flagged as such]. Deployed-curve context: the amicability of
secp256k1 was not a design criterion anywhere in the documented parameter
rationale; it is a consequence of `n = N(π_p − 1)` being prime, which *was*
the design criterion (prime order).

Two literature notes: Silverman–Stange's framework (2009) established that CM
curves have abundant amicable pairs and proved their structure theorems for
`j ≠ 0`; our curve is `j = 0`, where their unit group is μ₆ rather than
{±1}, and the specific 256-bit instance was not found in the literature
search. A recorded external claim that a sextic-symbol obstruction *blocks*
this pair is refuted by the direct point count (the symbol used was not the
true Hecke character; §3).

---

## 5. GLV = the CM ideal

The GLV endomorphism of secp256k1 is `φ(x,y) = (βx, y) = [λ]` with
`β³ ≡ 1 (mod p)`, `λ³ ≡ 1 (mod n)`, `φ(G) = [λ]G` — all re-verified today
**[✓ v1]**. The GLV scalar-decomposition lattice

```
L = {(u, v) ∈ ℤ² : u + vλ ≡ 0 (mod n)}
```

has reduced basis **{π_n, ω²·π_n}** under the coordinate map
`x + yω ↦ (x, y)`, with `det = n` exactly — both recorded basis vectors lie
in L, the determinant is +n, and `v1 = ω²·v2` in ℤ[ω] **[✓ v1]**. The
recorded `π_n` representative is the associate `−ω²(π_p − 1)` **[✓ v1]**.

So the "magic constants" of fast secp256k1 arithmetic are the coordinates of
the Frobenius: the lattice *is* the ideal `(π_n) = (π_p − 1)` — the same
object that carries the amicable pair (§4), the shared-M norm form, and the
unique prime-order twist. On the base field, the analogous lattice
`{(u,v) : u + vβ ≡ 0 (mod p)}` is the ideal `(π_p)` with basis
`{π_p, ω·π_p}`, and the two cube-root choices of β select the two conjugate
primes above p — libsecp256k1's published β corresponds to `π̄_p` [relayed:
rounds 13/7]. Scalar multiplication by ℤ[ω] commutes with Frobenius; the GLV
trick is that commutativity made computational.

Literature: the observation that the GLV short basis comes "from elementary
facts about quadratic rings" is B. Smith's (arXiv:1409.4526); the explicit
identification for secp256k1's published `(β, λ)` — including which conjugate
each implementation uses and the tie to `(π_n)` — is this study's tabulation.

---

## 6. The Eisenstein–Ramanujan survival law

The ℤ[ω] analogue of the classical Ramanujan-sum survival phenomenon (over ℚ:
`c_q(k)/φ(q)` decays for every k except the units `k = ±1`). Define, for an
ideal 𝔫 and `β ∈ ℤ[ω]`,

```
c_𝔫(β) = Σ_{r ∈ (ℤ[ω]/𝔫)^*} e^{2πi·Tr(βr)/𝔫},    Φ(𝔫) = |(ℤ[ω]/𝔫)^*|.
```

**Theorem** (assembled from Cohen's 1949 generalized Ramanujan-sum theory;
statement and verification 2026-07-10, spot re-verification today):

1. `c_𝔫(β)` depends only on the ideal `(β)`; in particular it is
   μ₆-invariant [math: units permute `(ℤ[ω]/𝔫)^*`].
2. Multiplicative in 𝔫 for coprime moduli [math: CRT].
3. Closed form `c_𝔫(β) = μ_K(𝔫/𝔤)·Φ(𝔫)/Φ(𝔫/𝔤)`, `𝔤 = gcd(𝔫, (β))`.
4. **Survival:** `|c_𝔫(β)| = 1` for all 𝔫 in a prime-ideal primorial tower
   **iff β is a unit**. Over ℤ the surviving modes are the **two** units ±1;
   over ℤ[ω] they are the **six** units μ₆.

Re-verified today: all six units hold `|c| = 1` at moduli `m = 2, 10, 70`,
and a non-unit dies on schedule with the closed-form value
(`c_(10)(2) = −3 = μ_K((5))·Φ((10))/Φ((5))`) **[✓ v1]**. The ramified prime 3
requires the ideal primorial (`𝔭₃` once), not the rational one [relayed
technical note].

**Operator side** [relayed: `q4_principal_survival.py` + adelic note]. The CM
field's one archimedean place is complex, `ℂ^* = ℝ_{>0} × S¹`, so the natural
operator is `Ĥ = π(A_r² + A_θ²)`; the compact angular factor has deficiency
indices (0,0) and splits the space into **six sextic sectors `m mod 6` ↔
μ₆**, the operator-theoretic image of the survival law; the `m = 0` sector
recovers the rational (ℚ, ±1) framework. **Scope, stated plainly:** this is a
consistency/model result about a free lattice spectrum — the μ₆ structure is
a selector of self-adjoint completions, not a construction of Riemann or
Hecke zeros; the global spectral realization remains open (Connes program),
and a May-2026 paper (arXiv:2605.17645) proves the corresponding
local-to-global obstruction for elliptic-curve L-functions. The rational
framework this extends is the investigator's own φ(n)-residue construction;
the number-field Ramanujan-sum ingredients are classical.

**The zeros are real and computed [✓ v3].** The L-function `L(ψ,s)` whose
survival law this section models is not abstract: built from the exact CM
Hecke eigenvalues (`thread_E_zeros_v1.py`, mpmath), it satisfies
`Λ(s) = W·Λ(2−s)` to 30 digits, gives `L(1) = Ω` (matching LMFDB to 28
digits), and its first ten zeros on `Re(s)=1` are located to `|L| ~ 10⁻²⁸` —
the first, `γ₁ = 0.8173126364`, agrees with LMFDB's `0.8173126364220043` to
ten digits, and the zero spacing matches the conductor-21168 density to <1%.
So §6 is a **verified instance**: the zeros exist, sit on the critical line,
and are reproduced from ideal counts alone. What stays open is only the
*spectral realization* of those zeros (the μ₆ operator model is a consistency
result, not a construction of them) — the honest maximal statement.

**The spectral boundary, mapped precisely** (`SPECTRAL_REALIZATION_v1.md`). Three
tiers: (I) the **Weil explicit formula / Riemann–von Mangoldt counting law** is a
theorem and is verified on the computed zeros; (II) the **Connes trace-formula ⟺
RH** framework on the idele class space `𝔸_K^*/K^*` gives the zeros a spectral
*interpretation* in the ψ-isotypic sector — and the derived χ = −(28/π)₆⁻¹ names
that sector (the six ray-class characters ↔ the six `S¹` sectors of the complex
place `ℂ^* = ℝ_{>0}×S¹` of `K`, exactly the §6 model), but this is *selection*,
not construction, and the positivity that would give RH is open; (III) an actual
global self-adjoint operator is **open** (the Hilbert–Pólya conjecture proper).
The **local** realization is a theorem prime-by-prime (Sato–Tate phases
`e^{±iθ_p}`, `cos θ_p = a_p/2√p`), with a **proven global interpolation
obstruction** (arXiv:2605.17645) — the clean CM instance of the exact
local/global boundary. Nothing here constructs the operator; the value is the
sharp map of where the wall is.

---

## 7. Why this curve is special — the landscape

**One symmetry organizes everything: μ₆.** The curve has the largest possible
automorphism group, and each of the five results is a different face of it:

| Face | Manifestation |
|---|---|
| Formal group (§2) | log supported on exponents `≡ 1 mod 6`; ₃F₂ closed form |
| Twists (§4) | six sextic twists ↔ six units; orders `N(π_p + u)` |
| Point set | μ₆ acts freely: `(n−1)/6` hexagonal orbits |
| p-torsion tower | `ord_p(t) = (p−1)/6` [relayed] |
| Survival law (§6) | six infinite-lifetime modes; six operator sectors |
| Hecke character (§3) | χ has order 6; ψ takes values `u·π`, `u ∈ μ₆` |

**One ideal organizes the rest: `(π_p − 1)`.** GLV lattice = amicable pair =
shared-M norm form = unique prime-order twist = the prime above n. What looks
like four coincidences is one element of ℤ[ω] and its norm.

**Why the parameters land here [math + relayed].** Given the two design
demands *prime order* (cofactor 1) and *an efficient endomorphism* (GLV),
`j = 0` is forced, not chosen: the only other efficient-CM option, `j = 1728`,
always carries the rational 2-torsion point `(0,0)`, so its twists all have
even order and can never be prime. Within `j = 0` over this field, exactly
one of the six twist classes has prime order, and `b = 7` is its smallest
representative (`b = 1…6` are composite-order — re-verified today
**[✓ v1]**). So "the standard j = 0 curve" is well-earned: secp256k1 is the
minimal instantiation of the unique prime-order sextic twist class over the
first suitable pseudo-Mersenne field — and it is essentially alone among
mainstream deployed curves in having small-discriminant CM at all (P-256,
Curve25519, Brainpool are non-CM), which is why this entire atlas has no
deployed-curve peer to compare against.

**Where it sits in the theory.** As a CM curve over ℚ with `h(−3) = 1`,
everything about E is "as explicit as elliptic curves get": its L-function is
a Hecke theta series computable from ideal counts (§3), its formal group is
hypergeometric with integral structure tied to eigenvalues by ASD congruences
(§2), its isogeny geometry is a single point, and its reductions generate
structured prime families (`Q(c)`, §4). The 2026 literature is actively
working the same seam: divisibility biases of reduction orders
(Lee–Sheen, arXiv:2606.25067 — whose CM imprint the investigation
reconstructed independently), and local Hilbert–Pólya realizations for
EC L-functions (arXiv:2605.17645 — matching the §6 boundary exactly). The
curve most people treat as a black-box cryptographic primitive is, read
mathematically, a maximally explicit worked example of CM theory at 256 bits.

---

## 8. Novelty calibration

Following the project's literature appendix (KNOWN_FACTS v5.1 App. A):
independent convergence is a method validation, not a demotion; "not found in
search" is method-scoped, never "provably novel."

| Result | Theory status | This study's part |
|---|---|---|
| Formal log closed form (§2) | Known-in-principle (Honda/Hazewinkel; CM ⇒ hypergeometric; supercongruences arXiv:1210.4489) | The explicit `Σ 7^k C(3k,k)/(6k+1) T^(6k+1)` and exact ₃F₂ form; the three-term ASD (147/147 split ℓ<2000) with mod-ℓ³ locus `{a_ℓ=±1}`; δ_ℓ shown non-elementary |
| Hecke ψ reconstruction (§3) | Classical (Deuring/Weil); curve tabulated in LMFDB (21168); CM-√−3 L(1) in arXiv:1003.5289 | End-to-end recomputation from point counts (conductor, ray-class order 432, local χ formula, W, L(1) = Ω) — a calibration of explicit CM theory on the largest deployed instance |
| Amicable pair (p, n) (§4) | **Fully covered** — Silverman–Stange 0912.1831 Conj 40 gives the exact j = 0 closure constant `1/3 + R(k)` per `k mod 36`; our ρ_7 = 13/50 **is their value** | Independent reconstruction validating Conj 40 across all 12 classes; explicit single-symbol `χ = −(4k/π)₆⁻¹`; the 256-bit `π_n = π_p − 1` instance. Not a new theorem. |
| GLV = CM ideal (§5) | Known to specialists (GLV 2001; B. Smith 1409.4526) | Explicit identification of the published β, λ constants with `(π_n)`, `(π_p)`, incl. conjugate bookkeeping |
| Survival law (§6) | Ingredients classical (Cohen 1949 generalized Ramanujan sums) | The μ₆ synthesis with the φ(n)-framework and the six-sector operator transfer; scope-bounded (model, not zeros). Zeros themselves now computed + LMFDB-confirmed (γ₁ to 10 digits) |

---

## 9. Verification manifest

**This session (2026-07-11): `verify_v1.py`, 30/30 checks.** Exact
integer/Fraction arithmetic decides every claim; floats appear only in the
Ramanujan-sum root-of-unity sums (checked against the exact closed form at
1e-6) and the period integral (1e-7 target; agreed to 10 digits).

- A1–A4: formal log to T⁴⁹, μ₆-sparsity, family b = 1..8, exact ₃F₂ ratio.
- B1–B3: shared-M norm forms at p and n; t.
- C1–C4: `N(π_p) = p`, `N(π_p−1) = n`, trace, associate bookkeeping.
- D1–D3: six twist orders `N(π_p+u)`, sum `6(p+1)`, unique prime = n.
- E1: orders of `y² = x³ + b`, b = 1..7, by two-point annihilator tests.
- F1–F2: amicable pair, both directions, with Hasse-uniqueness argument.
- G1–G6: λ, β cube roots; GLV basis in the lattice; det = +n; `v1 = ω²v2`;
  `φ(G) = [λ]G`.
- H1–H4: trace laws for good ℓ < 200; theta spot values; ASD congruence.
- I1–I2: survival of all six units at m = 2, 10, 70; death of β = 2 with
  closed-form value.
- J1: `Ω = Γ(1/3)Γ(1/6)/(2√π·7^{1/6})` vs direct integration.

**This session, second pass: `thread_probes_v1.py`, `thread_probes_v2.py`.**
P1: single-symbol search (train 147 / test 182 split primes; capstone at p;
alignment at n). P2: three-term ASD mod ℓ²/ℓ³; all-m failure pattern;
Fermat-quotient non-fit. P3: (67,79) worked example; closure scans at 2·10⁵
and 5·10⁵. v2 census: class-function verification mod 84/28 and the exact
26/100 closure count. P4: radius identity and boundary value.

**This session, third pass: `test_claims_v1.py`, `rho_b_investigate_v1.py`.**
Adjudication of an external results table (`CLAIMS_ADJUDICATION_v1.md`):
T1 Frobenius coords; T2 automatic-amicability counterexample hunt (12/22 fail);
T3 formal-group integrality via `[2],[3],[5](T) ∈ ℤ[[T]]` to T³⁷ (all primes at
once); T4 unit root α ≡ t (mod p) Hensel-lifted to p²; T5 exact unit
equidistribution (72/432 per unit, χ²=3.26 df 5); T6 `A(ψ)=N/4π²=536.19`;
T7 from-scratch `L(1)=Ω`, `L(1)/Ω=1` (BSD resolution); T8 `|ψ(𝔭)|²=N𝔭`.
ρ_b census: `u_b=−(4b/π)₆⁻¹` validated; per-b constants `{½,13/50,18/101,1/10}`
order-match amicable-pair enumeration to X=20000 (4/4).

**This session, fourth pass (settle B, then C, E): `test_ss_conjecture40_v1.py`,
`census_ss_v1.py`, `thread_C_supercong_v2.py`, `thread_E_zeros_v1.py`.**
B: our ρ_k = (1/2)(1/3+R(k)) = Silverman–Stange Conj 40 (+27), exact-rational
match for all 12 classes mod 36 (mod-12k census; direct enumeration within SE).
C: three-term ASD 147/147 split ℓ<2000; mod-ℓ³ locus = {a_ℓ∈±1} exactly;
δ_ℓ not Fermat-quotient/harmonic. E: L(ψ,s) from CM eigenvalues — Λ=WΛ(2−s) to
30 dps, L(1)=Ω (LMFDB 28 digits), first 10 zeros on Re(s)=1, γ₁ matches LMFDB
to 10 digits, spacing matches conductor density <1%. Source read this session:
Silverman–Stange arXiv:0912.1831 (Conj 40 R(k) table, Conj 27); LMFDB
21168.ce2 (L(1), γ₁).

**Relayed (recorded prior sessions, not re-run today):** χ local formula
(329 primes) and ray-class order 432 (`hecke*.py`, `thread2_rayclass.py`);
theta match to n ≤ 120 (`thread1_theta.py`); root-number parity computation
(`closers.py`); Selberg n_L measurements (`lfunc_sigma_profile.py`);
Hardy–Littlewood constant and Q(c) prime scan (`frob_quadratic.py`,
`vein_hl.py`); amicable density A(X) (`amicable_scale.py`); operator-side
six-sector computation (`q4_principal_survival.py`); global Mordell data
(`secp256k1_global_mordell.py`). All live in `../btc_puzzle_investigation/`.

**Corrections this document makes to prior notes:** `T¹³` coefficient is
`735/13`, not `56/13`; the hypergeometric form is a ₃F₂, not a ₂F₁; the
split-prime norm form is `4ℓ = a_ℓ² + 3g²` in general (27m² is the primary
special case); `L(ψ,s) ≠ ζ(s)L(s,χ₋₃)` — the latter is `ζ_K(s)`, and the
correct contact points are the shared splitting law and the Sym²
factorization; the v1 "χ is not a single sextic symbol" is withdrawn
(§3, v2); the v2 thread-D BSD/Tamagawa "tension" was a mis-read of Kodaira
types — BSD closes with `∏c_ℓ = #Ш = 1` (§4, v3).

## References

- Silverman, Stange — *Amicable pairs and aliquot cycles for elliptic
  curves*, arXiv:0912.1831.
- B. Smith — *The Q-curve construction for endomorphism-accelerated elliptic
  curves*, arXiv:1409.4526.
- Gallant, Lambert, Vanstone — *Faster point multiplication on elliptic
  curves with efficient endomorphisms*, CRYPTO 2001.
- *Supercongruences and Complex Multiplication* — arXiv:1210.4489; *Formal
  Groups and Invariant Differentials* — arXiv:1303.6706.
- *A note on L(1) of Hecke L-series … CM by √−3* — arXiv:1003.5289.
- Lee, Sheen — *Divisibility Biases in the Orders of Elliptic Curve
  Reductions*, arXiv:2606.25067; Pajaziti, Sadek — arXiv:2301.00711.
- *A Local Hilbert–Pólya Realisation for Elliptic Curve L-Functions* —
  arXiv:2605.17645.
- E. Cohen — generalized Ramanujan sums over number fields (1949).
- LMFDB, elliptic curve of conductor 21168 (`y² = x³ + 7`); SEC 2 (Certicom).
