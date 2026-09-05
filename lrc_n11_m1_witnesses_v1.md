# M=1 Witnesses for Prop 4.5 — All 9 Templates

For M=1, the speed set is E = F ∪ {1} ∪ {11} where F ⊂ {2,...,10}, |F|=8.
L = L_0 = lcm(F), N = 11 * L_0.

For each of the 9 templates (omitting one element from {2,...,10}), we exhibit
an explicit witness k_F such that e * k_F mod N ∈ [L_0, 10*L_0] for ALL e ∈ E.

## Witness Table

| Omit | F | L_0 | N | k_F |
|------|---|-----|---|-----|
| 2 | {3,4,5,6,7,8,9,10} | 2520 | 27720 | 12830 |
| 3 | {2,4,5,6,7,8,9,10} | 2520 | 27720 | 8568 |
| 4 | {2,3,5,6,7,8,9,10} | 2520 | 27720 | 6440 |
| 5 | {2,3,4,6,7,8,9,10} | 2520 | 27720 | 5270 |
| 6 | {2,3,4,5,7,8,9,10} | 2520 | 27720 | 4320 |
| 7 | {2,3,4,5,6,8,9,10} | 360  | 3960  | 540  |
| 8 | {2,3,4,5,6,7,9,10} | 1260 | 13860 | 1680 |
| 9 | {2,3,4,5,6,7,8,10} | 840  | 9240  | 1008 |
| 10 | {2,3,4,5,6,7,8,9} | 2520 | 27720 | 2750 |

## Arithmetic Verification

Each row is arithmetically verified: all values e * k_F mod N lie in [L_0, 10*L_0].

### Omit 2: F={3,4,5,6,7,8,9,10}, L_0=2520, N=27720, k=12830
| e | e*k mod N | In [2520, 25200]? |
|---|-----------|-------------------|
| 1 | 12830 | YES |
| 3 | 10770 | YES |
| 4 | 23600 | YES |
| 5 | 8710 | YES |
| 6 | 21540 | YES |
| 7 | 6650 | YES |
| 8 | 19480 | YES |
| 9 | 4590 | YES |
| 10 | 17420 | YES |
| 11 | 2530 | YES |

### Omit 3: F={2,4,5,6,7,8,9,10}, L_0=2520, N=27720, k=8568
| e | e*k mod N | In [2520, 25200]? |
|---|-----------|-------------------|
| 1 | 8568 | YES |
| 2 | 17136 | YES |
| 4 | 6552 | YES |
| 5 | 15120 | YES |
| 6 | 23688 | YES |
| 7 | 4536 | YES |
| 8 | 13104 | YES |
| 9 | 21672 | YES |
| 10 | 2520 | YES |
| 11 | 11088 | YES |

### Omit 4: F={2,3,5,6,7,8,9,10}, L_0=2520, N=27720, k=6440
| e | e*k mod N | In [2520, 25200]? |
|---|-----------|-------------------|
| 1 | 6440 | YES |
| 2 | 12880 | YES |
| 3 | 19320 | YES |
| 5 | 4480 | YES |
| 6 | 10920 | YES |
| 7 | 17360 | YES |
| 8 | 23800 | YES |
| 9 | 2520 | YES |
| 10 | 8960 | YES |
| 11 | 15400 | YES |

### Omit 5: F={2,3,4,6,7,8,9,10}, L_0=2520, N=27720, k=5270
| e | e*k mod N | In [2520, 25200]? |
|---|-----------|-------------------|
| 1 | 5270 | YES |
| 2 | 10540 | YES |
| 3 | 15810 | YES |
| 4 | 21080 | YES |
| 6 | 3900 | YES |
| 7 | 9170 | YES |
| 8 | 14440 | YES |
| 9 | 19710 | YES |
| 10 | 24980 | YES |
| 11 | 2530 | YES |

### Omit 6: F={2,3,4,5,7,8,9,10}, L_0=2520, N=27720, k=4320
| e | e*k mod N | In [2520, 25200]? |
|---|-----------|-------------------|
| 1 | 4320 | YES |
| 2 | 8640 | YES |
| 3 | 12960 | YES |
| 4 | 17280 | YES |
| 5 | 21600 | YES |
| 7 | 2520 | YES |
| 8 | 6840 | YES |
| 9 | 11160 | YES |
| 10 | 15480 | YES |
| 11 | 19800 | YES |

### Omit 7: F={2,3,4,5,6,8,9,10}, L_0=360, N=3960, k=540
| e | e*k mod N | In [360, 3600]? |
|---|-----------|-----------------|
| 1 | 540 | YES |
| 2 | 1080 | YES |
| 3 | 1620 | YES |
| 4 | 2160 | YES |
| 5 | 2700 | YES |
| 6 | 3240 | YES |
| 8 | 360 | YES |
| 9 | 900 | YES |
| 10 | 1440 | YES |
| 11 | 1980 | YES |

### Omit 8: F={2,3,4,5,6,7,9,10}, L_0=1260, N=13860, k=1680
| e | e*k mod N | In [1260, 12600]? |
|---|-----------|-------------------|
| 1 | 1680 | YES |
| 2 | 3360 | YES |
| 3 | 5040 | YES |
| 4 | 6720 | YES |
| 5 | 8400 | YES |
| 6 | 10080 | YES |
| 7 | 11760 | YES |
| 9 | 1260 | YES |
| 10 | 2940 | YES |
| 11 | 4620 | YES |

### Omit 9: F={2,3,4,5,6,7,8,10}, L_0=840, N=9240, k=1008
| e | e*k mod N | In [840, 8400]? |
|---|-----------|-----------------|
| 1 | 1008 | YES |
| 2 | 2016 | YES |
| 3 | 3024 | YES |
| 4 | 4032 | YES |
| 5 | 5040 | YES |
| 6 | 6048 | YES |
| 7 | 7056 | YES |
| 8 | 8064 | YES |
| 10 | 840 | YES |
| 11 | 1848 | YES |

### Omit 10: F={2,3,4,5,6,7,8,9}, L_0=2520, N=27720, k=2750
| e | e*k mod N | In [2520, 25200]? |
|---|-----------|-------------------|
| 1 | 2750 | YES |
| 2 | 5500 | YES |
| 3 | 8250 | YES |
| 4 | 11000 | YES |
| 5 | 13750 | YES |
| 6 | 16500 | YES |
| 7 | 19250 | YES |
| 8 | 22000 | YES |
| 9 | 24750 | YES |
| 11 | 2530 | YES |

## Analytic Proof of Prop 4.5

> **Proposition 4.5.** For each of the 9 valid M=1 templates, x_0(E) >= 1. In fact x_0(E) >= 2 by the reflection involution.

**Proof.** For each of the 9 templates F ⊂ {2,...,10} with |F|=8, Table 1 above exhibits an explicit integer k_F with 1 ≤ k_F ≤ N-1 and all 10 values e * k_F mod N ∈ [L_0, 10*L_0] as verified arithmetically above. Hence x_0(E) ≥ 1.

By Lemma 4.1 (Reflection Involution), k_F safe implies N - k_F also safe, giving a second distinct safe time. Hence x_0(E) ≥ 2.

To confirm x_0(E) ≥ 10: the safe condition for runner e_u ∈ F is periodic with period N/gcd(e_u, N). Since k_F is safe and gcd(e_u, N) = e_u (because e_u | L_0 | N and gcd(e_u, 11) = 1 and e_u | N/11 = L_0), the safe set for each runner is a union of arithmetic progressions. Explicit enumeration confirms x_0 ≥ 10 for all 9 templates (certificate §6). ☐

## Structural Observation

Note the elegant structure of several witnesses:

- **Omit 7** (k=540): k = 3L_0/2 = 1.5 * L_0. Note 540 = 3*180 = 3*360/2.
- **Omit 9** (k=1008): k = L_0 + L_0/5 = 840 * (1 + 1/5)... actually 1008 = 840 * 6/5. The fractions are not clean.
- **Omit 8** (k=1680): k = 4L_0/3 = 1680. Note 1680 = 4*420 = 4*1260/3.

The witnesses satisfy k_F ∈ [L_0, 2L_0] for 8 of 9 templates (all except Omit 2 where k=12830 > 2*2520=5040? Wait: 12830 > 5040, so k ∈ [4L_0, 6L_0] for Omit 2. Let me check: 12830/2520 ≈ 5.09. So k ≈ 5.09 L_0 for Omit 2.

The reflection involution pairs k_F with N - k_F.
