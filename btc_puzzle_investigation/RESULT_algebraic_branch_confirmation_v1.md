# RESULT: the algebraic-layer law is branch-dependent

**Date:** 2026-08-01
**Script:** `algebraic_branch_confirmation_v1.sage` (committed; reuses `build_L`, `Q_norm`).
**Grade:** `[VERIFIED — exact, 5 primes, branch-distinct stable laws]`.
**Register:** purist. Item 4 of the 2026-08-01 handoff (`untested_threads`).

---

## 0. What was open

`RESULT_algebraic_number_layer_v1.md` §2, §4 verified the eigenvalue-$\mathbb{Q}$-minpoly law

> minpoly degree $=4(n-1)/3$, multiplicity exactly 3,

only in the $\chi_2(-1)=-1$ branch ($p=43,67,127$, all $p\equiv3\pmod4$), and explicitly flagged: *"a $\chi_2(-1)=+1$-branch confirmation would need a larger $+1$-branch prime (p=13 is too small, the artifact above)."* This closes that item — and the answer is that **the law is branch-dependent**, not uniform.

## 1. The finding

Running the identical construction (build $L_a$, take $N_{\mathbb{Q}(\zeta_n)/\mathbb{Q}}$, factor over $\mathbb{Q}$) at two non-degenerate $\chi_2(-1)=+1$ primes ($p=61,n=61$ and $p=97,n=79$; both $\gg$ the $n=7$ degeneracy) gives:

| branch | primes | minpoly degree | multiplicity |
|---|---|---|---|
| $\chi_2(-1)=-1$ ($p\equiv3\pmod4$) | 43, 67, 127 | $4(n-1)/3$ | **3** |
| $\chi_2(-1)=+1$ ($p\equiv1\pmod4$) | 61, 97 | $4(n-1)/6$ | **6** |

Exact checks:

| $p$ | $n$ | branch | deg $P$ (norm) | Q-factorization $\{$deg:mult$\}$ |
|---|---|---|---|---|
| 43 | 31 | $-1$ | 120 | $\{40:3\}$ |
| 67 | 79 | $-1$ | 312 | $\{104:3\}$ |
| 127 | 127 | $-1$ | 504 | $\{168:3\}$ |
| **61** | **61** | **$+1$** | **240** | **$\{40:6\}$** |
| **97** | **79** | **$+1$** | **312** | **$\{52:6\}$** |

Both $+1$-branch primes: $4(n-1)/6$ exactly ($4\cdot60/6=40$, $4\cdot78/6=52$), multiplicity exactly 6.

## 2. Structural reading

The $+1$ branch has **twice the multiplicity and half the minpoly degree** of the $-1$ branch. The total degree $4(n-1)$ is preserved (it is just the norm degree), so the eigenvalue set decomposes into **6 equal $\mathbb{Q}$-Galois orbits in the $+1$ branch vs 3 in the $-1$ branch** — a finer orbit decomposition.

The natural reading: when $\chi_2(-1)=+1$ (i.e. $-1$ is a square mod $p$), the involution $d\mapsto -d$ on the frequency/scalar group lifts to an additional symmetry of the eigenvalue configuration, halving the $\mathbb{Q}$-orbit size and doubling the orbit count. This is the arithmetic counterpart of the closure-sign distinction the Route-A control measured (`RESULT_powersum_ladder_routeA_control_v1.md`: $V_2=V_1^2\pm2p$, $V_3=-2V_1^3\mp6pV_1$ with the sign $=\chi_2(-1)$) — the branch already controls the $e_3$ closure sign; it now also controls the $\mathbb{Q}$-Galois orbit count.

**Honest scope:** this is the measured branch law at 5 primes (3 $-1$, 2 $+1$), exact at each. It is not a proof of the branch dependence over all $p\equiv7\pmod{12}$ vs $p\equiv1\pmod{12}$; the multiplicity/degree regularity is the robust signature, as in the $-1$-branch case.

## 3. Consequence for the mechanism picture

- The $\mu_3$ signature (multiplicity a multiple of 3) survives in **both** branches: mult 3 in $-1$, mult 6 in $+1$. The threefold structure is branch-independent; the *extra* factor of 2 in the $+1$ branch is the new fact.
- This does not affect the degree-10 Galois-group identification of `RESULT_algebraic_galois_degree10_v1.md` (that lives at $p=43$, $-1$ branch, where the degree-$(n-1)/3=10$ object is in range). The $+1$ branch would have degree-$(n-1)/6$ objects — at $p=61$ that is degree 10 again, a candidate for a **second-prime cross-check of the degree-10 group in the $+1$ branch** (open; not run here).
- For secp256k1 itself ($p\equiv3\pmod4$, $-1$ branch), the operative law remains the $-1$-branch one ($4(n-1)/3$, mult 3).

## 4. Files

- `algebraic_branch_confirmation_v1.sage` — `branch_law(p)` for either branch; reproduces the table.
- Extends `RESULT_algebraic_number_layer_v1.md` §2/§4 (the $-1$-branch law) to the $+1$ branch.
