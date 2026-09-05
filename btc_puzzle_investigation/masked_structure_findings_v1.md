# Masked-Structure Investigation — Findings v1

**Date:** 2026-07-16
**Harness:** `masked_structure_harness_v1.py` (exact signal path: int/Fraction only;
float appears only as a *ranked* display statistic against a matched null)
**Datasets:** full field enumeration (p = 103, 1009, 10009, 100003), random secp
curve points (pool 9000), generator orbit {x([i]G)} (40000), the 82 solved keys as a SET.
**Stance:** curve-arithmetic only (no PRNG/generation side). Nulls below are scoped to
the exact readout inspected and are invitations, not verdicts.

---

## 0. Headline

The session's driving question was *"could additive structure be masked from
multiplicative readouts?"* The tests aimed at that question came back null and
well-controlled. **But the geometry test (D) opened a new exact law** that
subsumes four previously-separate VERIFIED constants and adds three new ones.

**The Cap Law (new, exhaustively verified):** the μ₃-orbit correction label ε is
*exactly* a **linear half-space indicator on the long diagonal** of the lift rhombus —
not a norm threshold. Everything in the Int.1 frame-operator panel and the norm-band
panel follows from it by exact integration.

---

## 1. THE CAP LAW  [VERIFIED exhaustively — 0/111,018 mismatches]

Let `z = eis_p(x)` be the exact Eisenstein lift into the reduced 60°-rhombus
fundamental domain `P` (an L¹ diamond, origin-centred), with

- half-diagonals `a` (long), `b` (short), `a/b = √3`  (60° rhombus)
- `b² = p/4`, `a² = 3p/4`  (forced; see §2)
- area `2ab = √3·p/2` = the fundamental-domain area of an index-p sublattice of ℤ[ω] ✓
- `D` = long-diagonal vector, `D̂` its unit vector, `a = |D|/2`

**Claim (region identity):**

```
    ε(x) ≠ 0   (flap)   ⟺   |⟨ eis_p(x), D̂ ⟩|  >  a/2
```

i.e. the flap is exactly the **two caps of the diamond beyond ±a/2 along the long
diagonal**, and the core is the central band.

**Verification** — exhaustive, exact integer arithmetic (`2·|2⟨z,D⟩| > N(D)`):

| p | flap count | flap frac | mismatches |
|---|---|---|---|
| 1009 | 252/1008 | 0.2500 | **0 / 1,008** |
| 10009 | 2496/10008 | 0.2494 | **0 / 10,008** |
| 100003 | 24990/100002 | 0.2499 | **0 / 100,002** |

Zero mismatches over 111,018 points. Cap area fraction `(1 − 1/2)² = 1/4`, matching the
PROVED `3/4 : 1/8 : 1/8` ε-law.

**Status:** VERIFIED (exhaustive at three primes), **not yet PROVED** from the CM /
2-point lift law. Named gap → §6.

---

## 2. WHAT THE CAP LAW DERIVES

For a uniform L¹ diamond, `E[x²] = a²/6`, `E[y²] = b²/6`. The cap integrals
(`x` = long-diagonal coordinate, caps at `|x| > a/2`, half-width `b(1−x/a)`):

```
  ∫cap x² dA = 11a³b/96      ∫cap y² dA = ab³/96      area(cap) = ab/4
  ⇒  E_flap[x²] = 11a²/24    E_flap[y²] = b²/24
```

Everything below follows by exact integration. **Bold = new this session.**

| Quantity | Cap-Law value | Measured (p=100003, exact) | Prior status |
|---|---|---|---|
| `C_core` λmax/λmin | `a²/(3b²) = 1` (isotropic) | λmax/Tr = **0.50000 exactly** | Int.1 VERIFIED → **DERIVED** |
| `C_all`  λmax/λmin | `a²/b² = 3` ⇒ λmax/Tr = 3/4 | 0.74992 | Int.1 VERIFIED → **DERIVED** |
| **`C_flap` λmax/λmin** | **`11a²/b² = 33` exactly** | 33.0141 | **NEW** |
| **`C_flap` λmax/Tr** | **33/34 = 0.970588** | 0.97060 | **NEW** |
| **`C_flap` principal axis** | **the LONG diagonal** | \|cos\| = 1.000000 exact, ⊥short = 0 | **NEW** |
| `E[N]/p` | `2b²/3p = 1/6` | 0.16665 | VERIFIED → **DERIVED** |
| **`E[N\|core]/p`** | **5/48 = 0.104167** | 0.10418 | **NEW** |
| **`E[N\|flap]/p`** | **17/48 = 0.354167** | 0.35416 | **NEW** |
| norm-band edges | `3b²/4 : b²` = **3/16, 1/4** | matches verified band | VERIFIED → **DERIVED** |
| flap centroid | 0 (central symmetry) | **(0,0) exactly** | **NEW** |

Consistency: `(3/4)(5/48) + (1/4)(17/48) = 1/6` ✓ — the core/flap norm split reproduces
the known mean exactly.

`λmax/Tr(core) = 0.50000` holds **exactly** at every p (μ₃'s 120° symmetry forces exact
isotropy); the other constants converge as `O(p^{-1/2})` discretisation: aniso_flap =
32.53 (p=1009) → 33.05 (10009) → 33.014 (100003) → 33.03 (secp, sampled 200k) → **33**.

### 2.1 Why the norm band exists (resolves a standing puzzle)

The band is a **projection artifact of reading a linear cut with a quadratic gauge.**
On the cap boundary `x = a/2` the diamond's half-width is `b/2`, so along that line

```
  N = x² + y²  ranges from  a²/4 = 3b²/4   (at y=0)
                      to    a²/4 + b²/4 = b²  (at y = ±b/2)
```

With `b² = p/4`: `N/p ∈ [3/16, 1/4]`. Hence **exactly**

- `N/p < 3/16` ⇒ core (the inscribed radius of the cut) — guaranteed
- `N/p > 1/4`  ⇒ flap (the circumscribed radius) — guaranteed
- `3/16 < N/p < 1/4` ⇒ **mixed** — where the circle crosses the straight boundary

The threshold **ratio** `(3/16)/(1/4) = 3/4 = (3b²/4)/b²` is what pins `b² = p/4`, which
in turn forces `E[N]/p = 2b²/3p = 1/6` ✓. So the two band edges, their ratio, and the
norm mean are one fact, not three.

**Correction to a claim in circulation:** ε is *not* "a norm threshold in disguise"
(and *not* an iff — the band is genuinely mixed, as our earlier VERIFIED result said).
ε is a **linear** threshold in disguise. The norm is a proxy that agrees outside the band
and cannot resolve inside it.

### 2.2 Two circulating findings are one fact

The "ε = norm threshold" and "C_flap ≈ 33:1 along the long diagonal" observations are
**the same geometric statement** seen twice: the flap is the high-|x| cap pair, so it is
(i) the high-norm region and (ii) mass concentrated at the two long-diagonal tips.
The `33:1` is real and is now exact (= `11a²/b²`), though "almost rank-1" overstates it —
33:1 is strongly anisotropic, and the second eigenvalue is a definite `b²/24`, not noise.
Because F proves the flap is closed under `z → −z` (centroid `(0,0)` exactly), this is
**genuine** anisotropy, not an uncentred-mass artifact.

---

## 3. THE OTHER PANELS

### F — Isotypic census + exact anchor  [PROVED + VERIFIED]

Over any `x → −x`-closed lift set, `z³` is odd ⇒ `Σ z³ = 0` **exactly**. Confirmed on
the full field, the core, and the flap at p=100003 — all three give exactly `(0,0)`.
So `E[z³]` is a pure **symmetry-breaking** detector: only the QR-restriction of curve
x-coordinates (`x³+7` a square) can make it nonzero. Census of low μ₆ observables:
mass (read), `N(z)` (read: norm band / ε), 6-sextant `χ₆` (read: covariant),
**`z³` = the μ₃-invariant cubic** → the one unread component ⇒ test A.
Also: `ε == 2` never fires (the CM law is exhaustive on the field).

### A — μ₃-invariant cubic moment `E[z³]`  [null, scoped, well-controlled]

Matched null = random curve-point subsets of the same N; verdict = rank percentile
(the statistic is heavy-tailed, so a mean/sd z-score is not trustworthy here).

| set | N | rank-pct | verdict |
|---|---|---|---|
| **[ctrl] random-82** | 82 | 0.427 | null ✓ *(control calibrated)* |
| generator orbit | 82 | 0.095 | null |
| generator orbit (full) | 40000 | 0.375 | null |
| **82 solved keys SET** | 82 | 0.333 | null |

Scope: the cubic moment **of the set** does not separate the 82 from random curve points
at N=82. It does not speak to any other cubic statistic (per-point conditionals, joint
moments, or the difference-set — see §6).

### G — the closure-blind corner: `χ_k(x([d]G))` vs `d mod k`  [null, scoped]

Motivation: the closure theorem's bound carries `‖F‖_A`, and a nontrivial multiplicative
character has `‖χ‖_A ≈ √p` (Gauss sums), which exactly cancels the `O(p^{-1/2})` gain.
So this corner is *not* covered by our proved panel — the one place a multiplicative
readout could see additive scalar structure.

All rows null under the **scaling** verdict (`Ic ~ 1/M`, `slope ≈ −1.2…−1.8` = noise;
a signal would plateau with `z` growing `~√M`). Detector-fires control (`selfMI`) fires
in every row.

| set | k=2 | k=3 | k=6 |
|---|---|---|---|
| orbit (N=40000) | slope −1.79 | −1.29 | −1.56 |
| random-d 64b (N=40000) | −1.21 | −1.79 | −1.49 |

82 keys single-shot (N=82, underpowered): perm p = 0.516 / **0.049** / 0.607. The k=3
value is one of three tests at N=82; the *same* test at N=40000 is null with slope −1.79,
so the powered version bounds the underpowered one. Not treated as a signal.

**Methodology catch (important):** the first pass reported `orbit χ₂, z = +5.95 ⇒ SIGNAL`.
Scaling audit: `z` = 4.9 → 2.3 → −0.4 → −0.2 → −0.4 as M = 2k → 32k, with `Ic ~ 1/M`.
**Pure noise.** The random-curve control *also* threw a spurious `z = +3.58` at one M.
Single-M z-scores fluctuate; only the scaling trend is admissible. The harness classifier
was rewritten accordingly (`slope(Ic)` + `z`-vs-`√M` trend, never a single-M z).

---

## 4. χ₂ DOUBLING TRANSPORT  [PROVED + VERIFIED 0/3000]

Found while auditing the G fluctuation. For `y² = x³ + 7`:

```
  x(2P) = (3x²)²/(2y)² − 2x = (9x⁴ − 8x(x³+7)) / (4(x³+7)) = x(x³ − 56) / (4(x³+7))
```

Since `x³+7 = y²` is a square and `χ₂(4) = 1`, the denominator's character is 1:

```
  χ₂( x(2P) )  =  χ₂( x · (x³ − 56) )        — exactly, and y-FREE
```

Verified 0/3000 mismatches on random 64-bit `d` (both the rational identity and the
character identity). The χ₂ readout is therefore **not a black box under doubling** — it
has an exact algebraic transport law that needs no `y`. Forward-only as stated (evaluating
the second factor needs the full `x`), so no reduction follows directly; recorded as an
exact transport fact of the kind §7 collects.

---

## 5. WHAT THE MASKING IDEA LOOKS LIKE AFTER THIS

Formalised: masking = `Cov(F(x([d]G)), φ(d)) ≈ 0`. Our closure theorem gives

```
  |Cov(F(x([d]G)), φ(d))|  ≤  (max|T|/n)·‖F‖_A·‖φ‖_A  =  O(p^{-1/2})·‖F‖_A·‖φ‖_A
```

Two consequences worth keeping:

1. **The mask is the default, and it strengthens with construction structure.** An
   algebraically-built `d` (sum-of-fractions, etc.) has *sparse* Fourier support ⇒ small
   `‖φ‖_A` ⇒ *more* invisible. So "additive construction hides from multiplicative
   readouts" is not a conspiracy — it is what the theorem predicts, and simple
   constructions are the easiest to mask. [PROVED, given Kohel–Shparlinski]
2. **The theorem names its own blind spot, and it is small and precise:** the bound is
   vacuous exactly when `‖F‖_A ≳ √p`, i.e. for multiplicative-character readouts. G tested
   that corner at `k ∈ {2,3,6}` against `d mod k` and found it null with proper scaling —
   which *narrows* the blind spot rather than closing it (see §6).

On the four circulating candidates: **C1** (μ₆-equivariant construction) is subsumed by
closure. **C2** (formal group linearises) was already probed — the linearisation
`L(T([d]P)) = d·L(T(P))` is real but lives on `E₁(ℚ_p)`; on reduced points `T_d` is a unit
so `v_p ≡ 0`, and the entry map is the DLP. **C3** (amicable washout) — amicable is a
*Frobenius* fixed point `(1−π)−1 = −π`, not a spectral one; curve-side residue → §6 (E).
**C4** (φ-residue averaging annihilates high-frequency modes) is **correct and is exactly
the closure/large-sieve mechanism** — a restatement of the theorem we hold, not a new
avenue. Its live piece is the *bilinear* analogue (closure covers single sums only).

---

## 6. OPEN — ranked

1. **Prove the Cap Law** (§1). Show `ε(x) ≠ 0 ⟺ |⟨z, D̂⟩| > a/2` from the CM / 2-point
   lift law. This is the highest-value item: it is exhaustively verified at 3 primes and
   0/111,018, it is a clean well-posed statement, and it would convert Int.1's `1/2`, `3/4`,
   the norm band `3/16, 1/4`, and `E[N]/p = 1/6` from four VERIFIED empirics into
   **corollaries of one proved identity** — with `33`, `33/34`, `5/48`, `17/48` as new
   proved constants. The ε label being a *linear functional threshold* is also the most
   tractable description of ε we have ever had.
2. **B — bilinear / joint-SET on the difference set** `{x([dᵢ−dⱼ]G)}`. Closure's own named
   complement (it bounds single sums only). Curve-side: the point relations
   `Pᵢ ⊖ Pⱼ = [dᵢ−dⱼ]G`. Test the cubic-moment / ε-profile of the difference set against a
   matched random-82-subset null; control row must fire.
3. **E — cross-domain bilinear moment over the amicable bridge.** Joint lift
   `(z_p = eis_p(x([d]G)), z_n = eis_n(d))`; cross-moments `E[z_p·z̄_n]`, `E[z_p²·z̄_n]`.
   Disjoint construction ⇒ tautology-guard clean. Asks whether the exact `C_n ⊆ C_p`
   overlap and the 4-cell slippage leave a coupling the coarse grid missed.
4. **G′ — widen the closure-blind corner.** G tested `χ_k` vs `d mod k` for k ∈ {2,3,6}.
   The corner is `‖F‖_A ≳ √p` *in general*: other high-Wiener-norm readouts, and other
   additive targets (`e_n(ad)` for varying `a`, low-degree additive features of `d`),
   remain untested. A Weil/Bourgain character-sum bound here would close the corner
   positively.
5. **Exact continuum vs lattice.** The Cap Law constants are continuum limits with
   `O(p^{-1/2})` discretisation. The exact finite-p lattice corrections are unexamined.

---

## 7. SCRIPTS

| file | contents |
|---|---|
| `masked_structure_harness_v1.py` | F / A / D / G. Exact ring (`emul`/`ecube`/`enorm`), exact `χ_k` via `make_chik`, `orbit_x`, `load_82` (private_key is **hex**), rank-based matched nulls, scaling-trend classifier |

Reused: `int1_frame_operator_v1.py` (`build`/`build_secp`), `ecc_secp256k1.py`,
`angular_interference_scaling_v1.py` (`conditional`/`mi_bits`/`gen_keys`/`loglog_slope`),
`lift_sextant_rhombus_law_proof_v2.py` (`reduced_basis`).

**Bugs caught and fixed this session** (all would have produced false verdicts):
- `load_82` parsed `private_key` as decimal → silently loaded **10 of 82** keys. It is hex.
- `dir_rational_of_vec` had a factor-2 error in the denominator.
- `tan(2φ)` identifies a **perpendicular pair**, not an axis — a rhombus has perpendicular
  diagonals, so it "matched" both. Which diagonal requires the eigenvector (→ long, |cos|=1).
- A single-M z-score was mis-flagging noise as SIGNAL (§3, G).
- The `A` bootstrap needed with-replacement sampling (pool < orbit size) and a rank
  verdict, not mean/sd.

**No-float compliance:** every signal-path quantity is `int`/`Fraction`. Floats appear only
in ranked/display statistics (`# noqa` annotated). The circulating scripts that motivated
these tests violate this fatally (float-complex `ε` compared at `1e-10` on a 256-bit prime,
`s = N(...)/p` true division, `np.linalg.eigh` on float outer products) — a double's 52-bit
mantissa destroys exactly the low bits at issue, so verdicts from them are uninformative in
either direction.
