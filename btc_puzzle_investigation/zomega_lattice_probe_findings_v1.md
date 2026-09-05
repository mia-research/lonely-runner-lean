# Z[ω]/GLV + p-adic curve probes — findings v1 (2026-07-12)

Probes of the user's four search-reduction ideas. Exact integers only
(`zomega_lattice_probe_v1.py`, passes the no-float signal-path rule except for
p-value ratios in reporting). Every test carries a **firing control**. Outcomes
are scoped to the test, per the research-stance rule — none is an avenue-death claim.

## Idea 2 & 4 — GLV / ℤ[ω] representation of the key set (`zomega_lattice_probe_v1.py`)
Object: ⟨G⟩ ≅ ℤ[ω]/(π_n), π_n = π_p−1, N(π_n)=n; a scalar "in ℤ[ω]" is its
balanced GLV pair (a,b), a+bλ ≡ d (mod n), via exact 2-D Gauss reduction + Babai.

| Test | What it detects | Control | Result |
|---|---|---|---|
| **T1 GLV-short** | generator emits GLV-short / lattice-aligned scalars | planted GLV-short → p=0.000 ✓ | **null** — obs sum(maxbits)=3712, null P(≤)=0.80. (Only #130 has a genuinely 2-D rep among solved keys ⇒ well-powered for that one; control validates the machinery.) |
| **T2 LCG mod n** | keys satisfy d_{i+2}−d_{i+1} ≡ a(d_{i+1}−d_i) (mod n), consistent a (LCG modulus aligned with n) | planted LCG mod n → 1 multiplier ✓ | **null** — 68 consecutive triples, **68 distinct** multipliers, max multiplicity 1 |
| **T3 CM-conjugacy** | d_j ≡ λ^e·d_i (mod n) (key set closed under φ) | recognizes λ·d ✓ | **null** — no hits |
| **T4 sextic leak** | sextic class of X([d]G) carries d mod 6 | cls=d mod6 → p≈0 ✓ | **null** — assoc stat 254, permutation p=0.75 |

Scope: T2/T4 use all 82 keys (well-powered); T1/T3 well-powered for the tested
relation. The ℤ[ω] joint-set test is **data-limited** for the short-vector angle:
only #130 exceeds 2^128, so the balanced rep is trivial ((d,0)) for the rest.
A well-powered short-vector test needs solved keys in the 2^128–2^160 band
(i.e. more of #129–160 solved) or the creator's own high-index draws.

## Idea 1 — p-adic formal-group lift (anomalous-twist check)
Smart/Satoh–Araki/Semaev give an O(1) DLP via the formal-group log **iff the curve
is anomalous** (#E(𝔽_p)=p, trace ±1) — exactly when L(T) linearizes the *whole*
group, not just the formal subgroup E_1(ℚ_p).

Checked base curve + all six sextic twists (traces = ±{t, a+b, 2b−a}):
- base trace t is **129-bit**; smallest twist trace (2b−a) is **128-bit**;
  **none is ±1** ⇒ **no anomalous twist**. Twist orders factor as recorded in the
  atlas (e.g. −t order = 3²·13²·3319·22639·C).
- Consequence: the exact `L(T)=T·₃F₂(1/6,1/3,2/3;1/2,7/6;27·7·T⁶/4)` linearizes
  E_1(ℚ_p) (points reducing to O). A puzzle point [d]G is a *general* point of
  E(𝔽_p); using L(T) needs a lift into E_1's additive coordinate consistent with
  G, and that lift is obstructed precisely by non-anomalousness (trace ≠ ±1).
  So this rules out the **specific** Smart shortcut — NOT a proof the DLP is hard
  (that remains a computational assumption).

## Idea 3 — φ(n) survival / small-prime-support spectral attack
Speculative programme item. Partially probed already: the ℤ[ω] prime-support test
(χ₋₃(d), split-vs-inert divisor counts, v₃) came back null vs the 100k matched
null (`reset_thread_C_eisenstein_v1.py`; only lean = inert primes 2,5 = decimal,
not CM). The "map key-space onto mode space so smallness = a feature" step is
**underdefined** — needs an explicit map from d to the survival-law mode space
before it is testable. Open, not run.

## ℤ[ω]-coverage audit (user: "has all testing taken ℤ[ω] into account?")
The answer turns on ONE structural fact, not a script survey:

**n is prime and SPLITS in ℤ[ω] (`n ≡ 1 mod 3`), so ℤ[ω]/(π_n) ≅ F_n ≅ ℤ/nℤ.**
The scalar is therefore **1-dimensional** — the 2-D structure would exist only if n
were INERT (`n ≡ 2 mod 3`, residue field F_{n²}). Consequences:
- **Scalar/key:** "d in ℤ[ω]" = "d in ℤ/nℤ". No hidden 2-D coordinate to miss.
  The GLV pair (a,b) is a non-canonical Babai coset rep, not an invariant of d.
  ⇒ the ℤ/nℤ tests (d mod 3, d mod 6, GLV-conjugacy, cubic/sextic char) ARE the
  ℤ[ω] scalar tests — not the wrong coordinate.
- **Curve/points:** genuine ℤ[ω] (φ=β on x, μ₆ point-orbit, π_p, amicable, L(ψ)).
  Covered by sextic χ₆(X), CM-conjugacy, Eisenstein prime-support, the atlas/L study.
- **Generation/PRNG:** ℤ[ω] not a generator coordinate; the only ℤ[ω]-selection
  channel is a multiplicative-class bias → tested next.

**Multiplicative character of the KEY mod n** (`key_cubic_char_v2.py`; v1 had two
flaws, both fixed here). SCOPE CORRECTION: this is a **low-prior completeness
channel**, not a novel high-value register — χ₃(d) mod n can only carry creator
info via an LCG-*mod-n* generator (already tested null, T2) or deliberate selection
(implausible: needs a 256-bit modexp). Result, now against the 100k synthetic pool
as the null:
- synthetic 100k baseline is **uniform** (cubic [0.334,0.336,0.330]) ⇒ null clean,
  no short-interval artifact.
- real-82 cubic [36,21,25] = frac [0.439,0.256,0.305]; **real vs 100k bit-matched
  null P=0.107**. sextic [20,11,8,16,14,13], P=0.294. control (planted cubic-residue
  reals) fires P=0.00000.
- Read: a real-vs-synthetic **cubic-residue (class-0) lean** (44% vs 33%) that is
  **NOT** a synthetic/interval artifact (baseline flat) but is **underpowered**
  (p≈0.11, 82 keys) — consistent with noise; would need MORE SOLVED KEYS to resolve.
  **v1 ERROR RETRACTED:** v1 attributed this to a "decimal/human artifact" by
  analogy to the base-10 finding — unjustified (different object; base-10 was about
  prime factors of the decomposition denominator, not χ₃ of d mod n). No such
  attribution is warranted; it is simply an underpowered non-result on a low-prior
  channel.
- **Why 82 not 100k:** the 100k are OUR randint (uniform baseline confirms) ⇒ they
  are the NULL, not creator signal. The creator's fingerprint is irreducibly the 82
  solved keys; only solving more puzzles adds signal here.

**Not ℤ[ω] gaps:** Farey (n,k) tests are in ℚ (different structure); the GLV
short-vector test is *data*-limited (only #130 > 2^128), a power gap.

## Multi-lens selection sweep (guard vs false-null from lens/representation bias)
`multilens_sweep_v1.py`. Concern: a real selection signal can be invisible in the
wrong representation. Modular residues in EVERY base already covered by the
all-moduli joint test (`reset_method2`, null). This sweeps the **non-modular**
lenses, pre-registered, real-82 vs 100k bit-matched null, Bonferroni×8:

| lens | feature | obs | p(2-sided) | Bonf×8 |
|---|---|---|---|---|
| binary | Hamming frac | 0.492 | 0.38 | 1.0 |
| binary | longest run | 5.05 | 0.16 | 1.0 |
| binary | top/bottom bal | 0.61 | 0.36 | 1.0 |
| binary | v₂ (trailing 0-bits) | 1.13 | 0.32 | 1.0 |
| decimal | leading digit (Benford) | — | 0.32 | 1.0 |
| decimal | trailing digit | — | 0.49 | 1.0 |
| decimal | trailing dec zeros | 0.12 | 0.76 | 1.0 |
| multiplicative | small-prime-factor count (≤10³) | 2.39 | **0.058** | 0.46 |

Control (planted low-Hamming keys) fires P=0.00000. **Nothing survives Bonferroni.**
The one flicker = **multiplicative smoothness** (M1): real keys slightly MORE
composite than uniform, p=0.058 raw — same direction as the cubic-residue lean
(p=0.11) and the base-10 ω hint (didn't survive fixed decomposition). If any creator
selection exists it is a mild "smoother/more-composite d" preference; NOT significant
at 82 keys. Genuinely-uncovered lenses: full multiplicative factorization of d
(intractable for 160-bit), compression/Kolmogorov (weak). Watch M1 if more keys solve.

## Net
The curve-side endomorphism speedup **√6 ≈ 2.45×** (μ₃ √3 + negation √2) is the
ceiling *from |Aut(E)|=6* — a theorem about the automorphism group, not a proof
of DLP hardness. Ideas 2 & 4 are control-backed nulls on the raw solved keys;
idea 1's specific shortcut needs anomalousness the curve lacks; idea 3 needs a
concrete map to become testable. The DLP is not proven impossible — none of these
is a wall, each is a scoped negative on a specific instrument.
