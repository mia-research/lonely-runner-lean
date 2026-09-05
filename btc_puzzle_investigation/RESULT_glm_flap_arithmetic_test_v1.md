# Is the flap ε an arithmetic object? — testing GLM's thesis, then following the conservation

Date: 2026-07-18. Object: canonical `int1_frame_operator_v1.build(p) → (eis, eps)`.
Exact integer arithmetic (no float in signal path). Pre-registration by `experiment-designer`
(spec honored verbatim); χ² ranked against a matched permutation null (the one float use the
folder rule permits); verdict = integer exceedance count, decided OUT-OF-SAMPLE.
Scripts: `glm_flap_harness.py` (Part A), `glm_flap_partB.py` (Part B), `scratchpad/inv_group.py`.

GLM's chain was: (A) `N(eis x) = least residue of x² mod p`; (B) `ε=0 ⟺ N(eis x) < 3p/16`;
(C) thesis: ε is an ARITHMETIC object — it carries a multiplicative character of x.

## Part A — the load-bearing identity is FALSE (exact, deterministic)
`N(eis x) ≡ x² (mod p)` holds at only chance rate (0.003 at p=1e5, 0.001 at p=1e6).
What holds for **100%** of x is `N(eis x) ≡ x·y′ (mod p)`, where `y′ = eis(x) mod π̄_p` is the
OTHER CRT embedding — essentially independent of x. So the lift norm is **not** a function of
the quadratic residue x². GLM's mechanism (flap = threshold on the size of x²) is dead at the
identity level. [SCOPE: exhaustive x, p∈{100003,100057,1000003}. PROVED by exact arithmetic.]

## Part B — pre-registered character test
STATISTIC Pearson χ² (obs exact Fraction; null = fixed-margin permutation, B=10000, verdict =
integer exceedances). FEATURES χ2, χ3, χ6, size6=6·(x² mod p)//p. POSITIVE CONTROLS norm-band
nb, sextant, GLM-threshold 1[16N<3p]. PLANTED power calibration. IN-SAMPLE p1=100003 (≡3 mod4),
OUT-OF-SAMPLE p2=100057 (≡1 mod4). Exhaustive x∈[1,p).

| feature | p1=100003 (χ², exc/1e4, V) | p2=100057 (χ², exc/1e4, V) | reading |
|---|---|---|---|
| **χ2** (load-bearing) | 0.00, 10000, 0.0000 | **0.12, 7371, 0.0011** | NULL both; on p2 μ6 does NOT force it, still null |
| **size6** (GLM's "size of x²") | 4.87, 4266, 0.0049 | 4.86, 4360, 0.0049 | NULL both |
| χ3 (entangled) | 0.00, 10000, 0.0000 | 0.00, 10000, 0.0000 | EXACTLY 0 both |
| χ6 (entangled) | 0.00, 10000, 0.0000 | 0.12, 9995, 0.0008 | exact on p1; near-0 on p2 (χ6 not faithful on μ6 when p≡1 mod4) |
| PC norm-band nb | 84047, **0/2000**, 0.648 | 84051, **0/2000**, 0.648 | FIRES (apparatus alive) |
| PC threshold thr | 70901, **0/2000**, 0.842 | 70767, **0/2000**, 0.841 | FIRES |
| PC sextant | 33307, **0/2000**, 0.408 | 26093, **0/2000**, 0.361 | FIRES |

PLANTED calibration (p1): a χ2-shaped fake character correlated with ε on fraction f fires at
f=0.05 (V=0.044) and f=0.02 (V=0.019), not at f=0.01 (V=0.009). **Smallest detectable V ≈ 0.015–0.02.**
Every character sits at V ≤ 0.005 — the zeros are exact/near-exact, not weak signal below threshold.

**Pre-registered verdict = SCOPED NULL, characterized.** GLM's thesis (C) is not supported: over
exhaustive x on p∈{100003,100057}, ε shows no association with χ2/χ3/χ6/size-of-x² above V≈0.02,
while the norm-band/threshold/sextant geometry is detected at V=0.36–0.84. NOT "ε is not arithmetic"
— a bounded magnitude with the geometric locus of ε's information named. (χ3/χ6 did NOT fire with
V≈1, so the construction-entanglement the pre-reg flagged did not manufacture a false hit — the
opposite: they are exactly orthogonal.)

## Following the conservation — the enforcing symmetry (not a closure)
The exact zeros are not luck. Three probes:

1. **ε is exactly μ6-invariant.** ε(βx)=ε(β²x)=ε(−x)=ε(x) for ALL x (exhaustive, all primes).
   A character nontrivial on μ6 then has **exactly equal counts within each ε-class** (verified:
   χ3 counts per class 25004/25004/25004 core, 8330/8330/8330 flap) ⇒ χ²=0 exactly.
2. **μ6 is SHARP.** The full multiplicative invariance group G={g: ε(gx)=ε(x) ∀x} is **exactly μ6**
   (|G|=6 on both primes, zero excess). Per the drill protocol, no second object hides in excess
   invariance — μ6 is the precise symmetry.
3. **The symmetry decomposes, and the CM half is constitutive.** μ6 = ⟨β⟩·⟨−1⟩:
   - **⟨β⟩ (μ3) = the GLV/CM endomorphism.** ε(x)=0 ⟺ `eis(βx) = ω²·eis(x)` EXACTLY; the flap is
     precisely the equivariance defect `c = eis(βx) − ω²·eis(x)`, which lands in {0,±R1,±R2} for
     every x (never "else"; core:flap = ¾:¼). This forces χ3,χ6 ⊥ ε. It exists only because j=0
     (no CM ⇒ no β ⇒ no Eisenstein lift ⇒ no flap): CM is not correlated with the orthogonality,
     it constitutes it.
   - **⟨−1⟩ = lift parity** `eis(−x) = −eis(x)` (symmetric fundamental domain). Forces χ2 ⊥ ε only
     when χ2(−1)=−1, i.e. p≡3 mod4 — generic to any centrally-symmetric lattice, not CM.

**Deeper symmetry (the payoff).** The flap sits entirely in the *trivial (μ6-invariant) isotypic
component* of functions of x. CM (j=0) upgrades it from "⊥ odd characters" (what a generic
symmetric lattice gives) to "⊥ the entire μ6 character group ⟨χ2,χ3,χ6⟩". Its information content
is genuinely geometric — norm-band (V=0.65) and sextant (V=0.36–0.41) — not any multiplicative
character. This SHARPENS the recorded "ε ⊥ χ6, geometric Babai class function" and the masked-
structure bigrading `ε=(0,0)`, and explains its p-mod-4 dependence.

## Next probe (door left open, per mantra)
The d-dependence / leak lives in the μ6-**anti**-invariant readouts: the master records `xy` as
odd-in-d + μ3-weight-1 (a nontrivial isotype), and the (x,y) aligned leak ≈0.93. ε being
trivial-isotype is orthogonal to those *by representation theory of μ6*. Concrete probe: decompose
the coordinate/readout functions into μ6-isotypes and check the leak lives in the nontrivial
isotypes while ε lives in the trivial one — tying the flap-null to the leak-structure through the
same μ6. Separately, a CM-by-Z[i] curve (j=1728, Aut=μ4) predicts a flap ⊥ χ4,χ2 but NOT χ3
(untested — would need a Gaussian-integer lift). Neither closes anything; both name where structure
lives next.
