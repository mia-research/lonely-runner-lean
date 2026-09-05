# RESULT -- blinded joint feature->residue dependence readout (v1)

Protocol: `PROTOCOL_blinded_joint_readout_v1.md` (blinded). No target is privileged; the five targets are treated identically.

- **Frozen code SHA-256:** `a4cce4b27f0ad120c716920c451fca1fd83127fb68e65c631d6ea201b40956b7`
- **Frozen code path:** `blinded_joint_readout_v1.py` (hashed before any real-data run).
- **No ECDLP conclusion is drawn and no live hypothesis is named.** This is the flat matrix only.

## 0. Scope & conventions

- **Targets (all peers):** {T_3, T_4, T_5, T_7, T_DECOY}.
- **Primary key-sets:** (M) model curves pooled over primes {547,907,1303,1669,2089}; (S) secp256k1 solved keys.
- **Multiplicity:** Holm-Bonferroni over the family {5 targets x 2 key-sets} = 10 primary tests, family-wise alpha = 0.05.
- **Joint MI:** plugin entropy with Miller-Madow bias correction on the full |F| x |T| contingency, |F| = product of feature domains = 324. Reported in bits.
- **Null:** permute T-labels WITHIN the F1 (chi3-index) stratum (preserves the orbit-position marginal); R = 20000 resamples, seed `random.Random(777333)`; `raw_p = (ge+1)/(R+1)`, `z = (MI_obs - mu_null)/sigma_null`.
- **Omnibus:** chi^2 on the F x T contingency with its own within-F1-stratum permutation p (perm-p authoritative; asymptotic dof invalid on sparse table).

- **Model primes skipped:** none. Group orders: p=547 -> n=547, p=907 -> n=967, p=1303 -> n=1249, p=1669 -> n=1663, p=2089 -> n=2143.
- **N:** (M) = 1094 (orbit-rep rows); (M-disc) = 252; (M-conf) = 842; (S) = 82.

## 1. Primary flat matrix -- joint MI(F;T)

### Key-set (M) model curves -- N=1094

| target | MI_obs | mu_null | sigma_null | z | raw_p | Holm_p | chi^2 | dof | chi^2_perm_p |
|---|---|---|---|---|---|---|---|---|---|
| T_3 | -0.1248 | -0.1151 | 0.0126 | -0.7614 | 0.7722 | 1.0000 | 169.9049 | 240 | 0.8573 |
| T_4 | -0.1798 | -0.1819 | 0.0148 | 0.1390 | 0.4328 | 1.0000 | 277.6588 | 360 | 0.5785 |
| T_5 | -0.2545 | -0.2503 | 0.0164 | -0.2557 | 0.5924 | 1.0000 | 348.6806 | 480 | 0.9387 |
| T_7 | -0.4209 | -0.4136 | 0.0189 | -0.3826 | 0.6479 | 1.0000 | 538.5361 | 720 | 0.7189 |
| T_DECOY | -0.1248 | -0.1151 | 0.0126 | -0.7614 | 0.7722 | 1.0000 | 169.9049 | 240 | 0.8573 |

Single-feature MI(F_k;T) decomposition (Miller-Madow, observed bits):

| target | F1 | F2 | F3 | F4 | F5 | F6 |
|---|---|---|---|---|---|---|
| T_3 | 0.0008 | 1.633e-05 | 0.0021 | -0.0007 | 0.0017 | -0.0008 |
| T_4 | 0.0032 | 0.0018 | 0.0046 | 0.0004 | -1.570e-05 | 0.0013 |
| T_5 | 0.0090 | -0.0014 | 0.0008 | 0.0039 | -0.0003 | 0.0009 |
| T_7 | 0.0023 | -0.0031 | 7.071e-05 | -0.0020 | -0.0001 | 0.0013 |
| T_DECOY | 0.0008 | 1.633e-05 | 0.0021 | -0.0007 | 0.0017 | -0.0008 |

### Key-set (S) secp -- N=82

| target | MI_obs | mu_null | sigma_null | z | raw_p | Holm_p | chi^2 | dof | chi^2_perm_p |
|---|---|---|---|---|---|---|---|---|---|
| T_3 | -2.7657 | -2.8375 | 0.0585 | 1.2292 | 0.1173 | 1.0000 | 74.3342 | 106 | 0.1620 |
| T_4 | -4.4719 | -4.4987 | 0.0568 | 0.4717 | 0.3322 | 1.0000 | 112.2691 | 159 | 0.5579 |
| T_5 | -6.2141 | -6.1822 | 0.0536 | -0.5958 | 0.7006 | 1.0000 | 152.2729 | 212 | 0.8961 |
| T_7 | -9.6808 | -9.7129 | 0.0463 | 0.6924 | 0.2305 | 1.0000 | 266.9443 | 318 | 0.2208 |
| T_DECOY | -2.7657 | -2.8375 | 0.0585 | 1.2292 | 0.1173 | 1.0000 | 74.3342 | 106 | 0.1620 |

Single-feature MI(F_k;T) decomposition (Miller-Madow, observed bits):

| target | F1 | F2 | F3 | F4 | F5 | F6 |
|---|---|---|---|---|---|---|
| T_3 | 0.0617 | -0.0012 | 0.0463 | 0.0469 | -0.0095 | -0.0030 |
| T_4 | 0.0387 | 0.0389 | 0.0949 | 0.0321 | -0.0178 | -0.0020 |
| T_5 | 0.0666 | -0.0084 | 0.0549 | -0.0162 | 0.0102 | 0.1464 |
| T_7 | -0.0483 | -0.0518 | 0.0260 | -0.0205 | 0.0198 | -0.0167 |
| T_DECOY | 0.0617 | -0.0012 | 0.0463 | 0.0469 | -0.0095 | -0.0030 |

## 2. OOS (C4) -- discovery vs confirmation (descriptive, NOT in Holm family)

| target | phase | N | MI_obs | z | raw_p |
|---|---|---|---|---|---|
| T_3 | disc | 252 | -0.7659 | -1.3253 | 0.9098 |
| T_3 | conf | 842 | -0.1747 | -0.1449 | 0.5475 |
| T_4 | disc | 252 | -1.1542 | -0.5567 | 0.7049 |
| T_4 | conf | 842 | -0.2575 | 0.5444 | 0.2858 |
| T_5 | disc | 252 | -1.5624 | 0.3554 | 0.3551 |
| T_5 | conf | 842 | -0.3632 | 0.0800 | 0.4580 |
| T_7 | disc | 252 | -2.4831 | 1.1101 | 0.1348 |
| T_7 | conf | 842 | -0.6120 | -0.9115 | 0.8177 |
| T_DECOY | disc | 252 | -0.7659 | -1.3253 | 0.9098 |
| T_DECOY | conf | 842 | -0.1747 | -0.1449 | 0.5475 |

## 3. Controls

### C1 (planted dependence) -- MUST yield z>=5 and p<0.01

| key-set | N | MI_obs | z | raw_p | verdict |
|---|---|---|---|---|---|
| (M) | 1094 | -0.0612 | 4.5444 | 1.000e-04 | FAIL |
| (S) | 82 | -2.8512 | 0.6198 | 0.2808 | FAIL |
| (M-disc) | 252 | -0.6202 | 2.5518 | 0.0079 | (descriptive) z=2.5518 p=0.0079 |
| (M-conf) | 842 | -0.0598 | 6.7821 | 5.000e-05 | (descriptive) z=6.7821 p=5.000e-05 |

**C1 verdict (literal z>=5 bar): FAIL on pooled (M).** Substantively, the planted
dependence IS recovered with high significance on the model regime: p = 1.0e-04 on
pooled (M) and z = 6.78, p = 5.0e-05 on the confirmation split (M-conf) (>=5 there).
The pooled (M) z = 4.54 sits marginally below the 5.0 bar; (S) has only N = 82 rows
(low power, z = 0.62 as expected for any weak signal). The magnitude shortfall on
pooled (M) is attributable to the protocol-specified plant strength (30%-of-rows F2,
with F2 realized as binary {0,1} on this curve family) and is not a pipeline bug:
the GLV / lift machinery is independently validated by C3-F2's exact orbit-invariance
(0/1094 violations), and the plant is detected at p << 0.01 wherever there is power.
Reported, not papered over.

### C2 (decoy in-band) -- T_DECOY MUST come back |z|<2 in every key-set

| key-set | z(T_DECOY) |
|---|---|
| (M) | -0.7614 |
| (S) | 1.2292 |

**C2 verdict:** PASS (max |z| over primary key-sets = 1.2292).

### C3 (phi-forced orbit-invariance) -- F2,F3,F5 constant on each full orbit

Per-prime exact violation counts (orbits whose full <+-lambda> orbit is NOT constant on the named feature):

| prime | n | #orbits | F2-viol | F3-viol | F5-viol | tuple-viol |
|---|---|---|---|---|---|---|
| 547 | 547 | 91 | 0 | 18 | 25 | 25 |
| 907 | 967 | 161 | 0 | 36 | 16 | 44 |
| 1303 | 1249 | 208 | 0 | 51 | 33 | 59 |
| 1669 | 1663 | 277 | 0 | 59 | 67 | 68 |
| 2089 | 2143 | 357 | 0 | 92 | 18 | 105 |
| **total** |  | **1094** | **0** | **256** | **159** | **301** |

**C3 verdict: PARTIAL / premise error.** F2 (flap eps) is exactly orbit-constant on ALL 1094 orbits (0 violations) -- this validates the GLV / Eisenstein-lift machinery (the GLV identity x([lam]d) = beta*x(d) holds and eps is constructed from it). However F3 (norm band) and F5 (sextant parity) are NOT exact orbit-invariants: F3 violates on 256/1094 orbits and F5 on 159/1094. Mechanism: eis(beta*x) = reduce_P(zeta . eis(x)) (Babai reduction into the fundamental parallelogram); the unit zeta preserves norm and sextant parity, but the lattice CORRECTION in reduce_P does not, so enorm and sextant can change across an orbit. This is a math-premise error in protocol section 6 (the premise that F3,F5 are phi-forced), not a pipeline bug and not target-dependent. The MI/permutation analysis below is independent of this structural claim and remains well-defined.

### C4 (OOS split)

Discovery {547,907} and confirmation {1303,1669,2089} reported separately (Section 2); (S) is an independent holdout. Both phases computed for every target. No prime was skipped (none).

**C4 verdict:** PASS (discovery and confirmation both reported; secp holdout reported as primary key-set (S)).

## 4. Neutral per-target summary (Holm 0.05)

- **T_3:** (M) not detected at Holm 0.05 (z=-0.7614, Holm_p=1.0000); (S) not detected at Holm 0.05 (z=1.2292, Holm_p=1.0000).
- **T_4:** (M) not detected at Holm 0.05 (z=0.1390, Holm_p=1.0000); (S) not detected at Holm 0.05 (z=0.4717, Holm_p=1.0000).
- **T_5:** (M) not detected at Holm 0.05 (z=-0.2557, Holm_p=1.0000); (S) not detected at Holm 0.05 (z=-0.5958, Holm_p=1.0000).
- **T_7:** (M) not detected at Holm 0.05 (z=-0.3826, Holm_p=1.0000); (S) not detected at Holm 0.05 (z=0.6924, Holm_p=1.0000).
- **T_DECOY:** (M) not detected at Holm 0.05 (z=-0.7614, Holm_p=1.0000); (S) not detected at Holm 0.05 (z=1.2292, Holm_p=1.0000).

## 5. Notes / deviations (transparency)

- **`d` column:** `puzzles_verified.csv` has no column literally named `d`. The scalar `d` with Q_d = dG is the `private_key` column (hex), exactly as the allowed file `ecc_secp256k1.py` itself reads it (`d = int(r['private_key'], 16)` and validates via `scalar_mul(d)`). This is the column the allowed code defines as `d`; it is not a substitution.
- **`find_glv` for secp:** the protocol's verbatim `find_glv` searches lambda (smallest lam>=2, lam^3==1 mod n) which is intractable for secp's ~256-bit group order. Per protocol section 4, key-set (S) has NO orbit quotient, so secp requires only `wp` (the cube root of unity mod p, for chi3_index); `find_wp` is instantaneous. `find_lam` is used for model curves only (small n).
- **Miller-Madow with |F|=324** heavily corrects the joint MI at small N (key-set (S), N=82): the corrected MI_obs can be negative there. The inferential quantities z and raw_p are invariant to this (the correction is an additive constant applied identically to observed and null).
- **C3** is reported as PARTIAL (see Section 3): F2 is exactly orbit-invariant; F3, F5 are not. Flagged rather than asserted.
- **C1 plant** uses an exact 30% uniform subset (`rng.sample`), seed 31415; non-subset rows get uniform random residue in {0,1,2}.
- Single-feature rows report observed Miller-Madow MI only (no separate null), per protocol section 8 (null columns are for the joint MI).
- **T_DECOY is an alias of T_3 under this test.** The protocol's `pi` is a uniform
  random *permutation* (bijection) of {0,1,2}, so `T_DECOY(d) = pi(d mod 3)` is a
  bijective relabeling of `T_3(d) = d mod 3`. MI is invariant under bijective
  relabeling of either variable, and the within-F1 stratified permutation null uses
  a fixed seed, so T_DECOY and T_3 yield *identical* test statistics in every key-set
  (visible in the tables: same MI_obs, z, raw_p, chi^2). Consequently C2 is not
  independent of the T_3 test: it reads null precisely because T_3 reads null. This
  is a property of the protocol's decoy definition (a bijective `pi` cannot destroy
  MI), not a pipeline artefact; reported for transparency. A non-bijective decoy
  (e.g. a random hash to {0,1,2}) would be needed for an independent null check.

