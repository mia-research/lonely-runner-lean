# BLINDED PROTOCOL — joint feature → residue dependence test

You are implementing a **blinded statistical analysis**. You will compute a uniform dependence
matrix between a fixed set of point-features and a fixed family of scalar-residue targets, and
report a flat table. **No target is privileged.** You are not told which (if any) target is a
live hypothesis, and you must not attempt to find out.

## BINDING RULES (read first)

1. **Do NOT read any markdown / analysis document in this workspace** — no `PREREG_*`,
   `RESULT_*`, `*LEDGER*`, `RESEARCH.md`, `ANALYSIS_*`, `*.md` except this file. Those contain
   context that would invalidate the blinding. If you need a definition, it is in this file or
   in the explicitly-allowed code files below.
2. **Allowed files (valence-free code/data only):** this protocol, `ecc_secp256k1.py`,
   `int1_frame_operator_v1.py`, `lift_sextant_rhombus_law_proof_v2.py`,
   `glv_fundamental_domain_law_v1.py`, `puzzles_verified.csv`.
3. **Compute the identical pipeline for every target.** Make NO target-specific choice.
4. **Commit before you see.** Write the full statistic+null code, print its SHA-256 to stdout,
   and only then run it on the real data. Record the SHA in the result file.

## 1. The curve and the point

secp256k1: `y² = x³ + 7` over `F_p`. Constants (from `ecc_secp256k1.py`):
```
P  = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
N  = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141
Gx = 0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798
Gy = 0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8
```
`Q_d = dG` via `ecc_secp256k1.scalar_mul(d)`. `Q_d = (x_d, y_d)`.

GLV constants (for the orbit quotient): compute dynamically — `find_glv` below — do NOT read
them from any other file.

## 2. The six features (exact; functions of the point only)

`find_glv` and `chi3_index` (verbatim from the canonical sources):
```python
def find_glv(p):
    e = (p - 1) // 3
    g = 2
    while pow(g, e, p) == 1:
        g += 1
    wp = pow(g, e, p)                      # primitive cube root of 1 mod p
    # lambda: smallest c>=2 with c^3==1 mod N, c!=1, s.t. x([c]G) == wp*x(G) (mod p) convention
    # for the orbit quotient we only need wp (cubic root) and lambda (order-3 unit mod n):
    n = N
    lam = 2
    while not (pow(lam, 3, n) == 1 and lam != 1):
        lam += 1
    return wp, lam

def chi3_index(x, p, wp):                  # F1, domain {0,1,2}
    v = pow(x % p, (p - 1) // 3, p)
    return 0 if v == 1 else (1 if v == wp else 2)
```
For the secp regime, build the lift machinery once:
```python
import int1_frame_operator_v1 as frm
secp = frm.build_secp()                    # provides secp.eis(x), secp.eps(x), secp.beta, ...
import lift_sextant_rhombus_law_proof_v2 as L
def enorm(w): return w[0]*w[0] - w[0]*w[1] + w[1]*w[1]
def sextant_uv(u, v): return L.sextant(u, v)         # the canonical 0..5 classifier
```
Then the six features of `Q_d = (x_d, y_d)`:
```python
def features(x_d, y_d, p, wp, secp):
    e = secp.eis(x_d)
    F1 = chi3_index(x_d, p, wp)                       # χ₃-index,        {0,1,2}
    F2 = secp.eps(x_d)                                # flap ε,          {0,1,2}
    E = enorm(e)
    F3 = 0 if 16*E < 3*p else (1 if 16*E < 6*p else 2)   # s-band3,     {0,1,2}
    sxt = sextant_uv(*e)
    F4 = sxt % 3                                      # sextant mod 3,  {0,1,2}
    F5 = 0 if sxt in (0,2,4) else 1                   # sextant parity, {0,1}
    F6 = 0 if pow(y_d, (p-1)//2, p) == 1 else 1       # χ₂(y) Legendre, {0,1}
    return (F1, F2, F3, F4, F5, F6)
```
**For the model-curve regime** (`E: y²=x³+7` over small `F_p`), use `frm.build(p)` instead of
`build_secp()`; everything else is identical.

## 3. The target family (BLINDED — all peers, none privileged)

For each `d` in scope compute `T_m(d) = d mod m` for `m ∈ {3, 4, 5, 7}`, plus
`T_DECOY(d) = π(d mod 3)` where `π` is a fixed uniform random permutation of `{0,1,2}` drawn
from `random.Random(20260813)`. So the family is `{T_3, T_4, T_5, T_7, T_DECOY}` — five
targets, treated identically.

## 4. Scope (two key-sets)

- **(M) model curves:** for each `p` in scan `{547, 907}` then confirm `{1303, 1669, 2089}`,
  build `E/F_p`, enumerate `d = 1..n-1`, keep one rep per `⟨±λ⟩`-orbit via `orbit_reps(n, lam)`
  below. (This is the powered regime — large N.)
- **(S) secp solved keys:** the `d` column of `puzzles_verified.csv` (small N; the real regime).

`orbit_reps` (full ⟨±λ⟩ orbit, verbatim):
```python
def orbit_reps(m, lam):
    seen, reps = set(), []
    for d in range(1, m):
        orb = []
        for k in range(3):
            lk = pow(lam, k, m)
            orb += [(lk*d) % m, (-lk*d) % m]
        d0 = min(x for x in orb if x != 0)
        if d0 not in seen:
            seen.add(d0); reps.append(d0)
    return reps
```
For (S) there is no orbit quotient (the keys are the given d's).

## 5. Statistic (frozen; identical for every target)

For a target `T` and the feature 6-tuple `F`:
- **Primary:** `MI(F ; T)` in bits. Estimate via plugin with **Miller–Madow bias correction**
  on the full `|F| × |T|` contingency (|F| fixed = product of feature domains). Report in bits.
- **Decomposition:** `MI(F_k ; T)` for each single feature `k=1..6`.
- **Null (symmetry-matched permutation):** holding the features fixed, permute the `T`-labels
  **within F1 (χ₃-index) stratum** (preserves the orbit-position marginal; destroys only the
  residual coupling). `R = 20000` resamples, `random.Random(777333)`. `p = (ge+1)/(R+1)`,
  `z = (MI_obs − μ_null)/σ_null`.
- **Omnibus:** `χ²` statistic on the `F × T` contingency with its own within-F1-stratum
  permutation `p` (report `χ²`, dof, perm-p; never rely on the asymptotic p alone).

## 6. Controls (all must fire; if any fails, stop and report no result)

- **C1 FIRING:** construct a synthetic target `T_plant` that equals `F2` (flap ε) on a random
  30% subset of rows (seed `random.Random(31415)`) and is otherwise a random residue. Run the
  full pipeline on `T_plant` — it MUST yield `z ≥ 5` and `p < 0.01`. (The builder cannot tell
  `T_plant` from a real target.)
- **C2 DECOY:** `T_DECOY` MUST come back `|z| < 2` in every key-set. If it fires, the pipeline
  has a bug — stop.
- **C3 φ-forced sanity:** verify, on every model curve, that `F2, F3, F5` are constant on each
  full `⟨±λ⟩`-orbit (exact integer check). Any violation ⇒ bug, stop.
- **C4 OOS:** scan curves `{547,907}` are discovery; `{1303,1669,2089}` are confirmation.
  Report both. (S) is an independent holdout.

## 7. Multiplicity

Holm–Bonferroni over the family `{5 targets × 2 key-sets}` = 10 primary tests, family-wise
α = 0.05. Report each target's raw and Holm-adjusted p.

## 8. What to produce

Write `RESULT_t2c_joint_readout_dmod3_BLINDED_v1.md` containing:
1. The SHA-256 of the frozen statistic+null code (committed before any real-data run).
2. A **flat matrix**: rows = the 5 targets `{T_3,T_4,T_5,T_7,T_DECOY}`, columns per key-set =
   `{MI_obs, μ_null, σ_null, z, raw_p, Holm_p}` for the joint `MI(F;T)`, plus the 6
   single-feature `MI(F_k;T)` rows beneath each.
3. C1–C4 verdicts (each PASS/FAIL with the numbers).
4. A one-line neutral summary **per target** ("dependence detected / not detected at Holm
   0.05"), with no target singled out as primary.

Do NOT write a "conclusion about ECDLP" or name a "live hypothesis." You do not have that
information. Report the flat matrix and stop.
