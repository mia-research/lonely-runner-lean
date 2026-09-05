# PREREG — Cubic difference-set energy `E3` (v1)

**Status:** FROZEN before apply. Gate: `experiment-designer` (isolated). Date: 2026-07-26.
Applied result: [RESULT_diffset_cubic_v1.md]. Complement of the antisymmetric [PREREG_diffset_sdiff_v1.md].

---

## Object
```
E3 = a² + b² + c² − ab − bc − ca          (exact integer; = |a + bω + cω²|², ω = e^{2πi/3})
(a,b,c) = counts of cubic classes {χ₃=1, β, β²} over the C(82,2)=3321 UNORDERED pairwise
          x-coordinate differences of the 82 solved-puzzle pubkeys, over F_P (secp256k1).
class of z≠0 : r = pow(z,(P−1)//3,P) ∈ {1, β, β²};  β = BETA, β² = BETA² mod P.
```
Source real x: `solved_puzzles_xy.csv` col `X`. E3 is symmetric in (a,b,c) ⇒ invariant to the
ω↔ω² labeling (100k random checks).

## Orientation (the point of this probe)
`χ₃(−1) = pow(P−1,(P−1)//3,P) = 1` at secp (P ≡ 1 mod 6) ⇒ `χ₃(x_j−x_k)=χ₃(x_k−x_j)` ⇒ E3 is
**orientation-EVEN**. S_diff (χ₂, P≡3 mod4) is orientation-ODD. **Orthogonal channels:** E3 measures
exactly the symmetric difference-set subspace S_diff is identically blind to.

## Forced structure (decidable, before data)
- Beyond `a+b+c=3321`: **E3 ≡ 0 (mod 3) is FORCED** for every 82-point set (`E3 = 3321² − 3(ab+bc+ca)`,
  3321 = 3·1107; specific to n=82). Apply-time asserts this — a non-multiple-of-3 = path bug, not signal.
- Control class means (1106.8, 1107.3, 1106.9) ≈ 1107 each; `Var(a) ≈ 727 ≈` independent-multinomial
  738 ⇒ **no curve-structure class bias**; classes behave as independent-uniform ternary.

## Matched control (null)
10,000 resamples of size 82 from `constructed_keys_1to160_100k.csv`, one key per matching real
bit-length. Null is **Exponential(mean ≈ 3321)** — the √-floor (`mean/3321 = 0.986`), verified vs
analytic `−μ·ln(1−p)` at every quantile. mean 3274.4, sd 3222.6, median 2268, range [0, 25524].
**Do NOT z-score (σ ≈ mean); empirical order statistics only.**

## Planted control — FIRES both arms
Concentration plant ε (reassign ε·3321 pairs to one class): reject 0.048 → 0.936 over ε∈[0,0.05].
Over-uniformity plant δ: reject-low 0.025 → 0.833 over δ∈[0,0.013]. ε=0/δ=0 calibrate to α on
out-of-sample fresh draws.

## Power
50% / 80% at one class rising 1/3 → ≈0.353 / ≈0.363 (ε₅₀≈0.030, ε₈₀≈0.044); over-uniformity
δ₅₀≈0.0073, δ₈₀≈0.012.

## Falsification (FROZEN, integer order statistics, two-sided)
```
reject-HIGH (concentration)     iff  E3 > 11997     ( = A[9750], upper tail 0.0249 )
reject-LOW  (over-uniformity)   iff  E3 <    84     ( = A[249],  lower tail 0.0236 )
else FAIL-TO-REJECT
```
seed 20260727, N=10000, achieved two-sided α = 0.0485. Apply rank-p:
`min((#{A≥E3}+1)/(N+1), (#{A≤E3}+1)/(N+1))·2`.

## Scope
82 solved puzzles, bit-lengths {1–70,75–130}; control = 100k constructed set; secp P; cubic
character; N=10000, seed 20260727. No number generalizes past this scope.

## Subspace caveat (load-bearing)
E3 is a function ONLY of the marginal counts (a,b,c). Provably blind to: (i) orientation-odd signal
(S_diff's channel), (ii) joint/triangle structure among overlapping pairs that keeps marginals
uniform, (iii) bit-length-band-localized concentration (pooled → diluted). A fail-to-reject bounds
only the pooled orientation-symmetric magnitude channel; it does not close the cubic channel.

## Artifacts (this directory)
`diffset_cubic_apply_v1.py`, `diffset_cubic_audit_v1.py`, `diffset_cubic_frozen_null_E3_v1.npy`
(10000 int, all ≡0 mod3), `diffset_cubic_frozen_null_abc_v1.npy`, `diffset_cubic_frozen_meta_v1.json`.
