# RESULT — D2 twist-rigidity certificate: the four-step framework executed first-hand, exactly (8 primes, both mod-12 arms, every cell)

**Date 2026-08-21. Grade: `[VERIFIED — exact, decidable artifact]`** for every structural check below
(exact `Z[ζ_n]` arithmetic in the whole signal path; float only in the final degree-4 root readout,
with an error-bar argument for the one non-exact claim). No secrets, no leakage or ECDLP claim —
a deterministic certificate of the documented object. Script `d2_twist_rigidity_certificate_v1.py`
(+ `.log`); sweep extension `d2_nonabelian_sweep_v2.sage` (+ `.log`). Companion to
`ANALYSIS_n1_cap_anew_channel_kronecker_route_v2/v3.md`, `RESULT_anew_twisted_eigenvalues_nonabelian_v1.md`,
P32/P25/P23/M4.

## The framework, executed

**(1) Base objects (exact).** $V_1(a) = \sum_d h_1[d]\,\zeta_n^{ad} \in \mathbb{Z}[\zeta_n]$ with
$h_1[d] = \chi_2(y_{[d]G})$ — implemented independently (own group walk, own cyclotomic arithmetic,
$\mathbb{Z}[T]/\Phi_n$ with exact reduction) and **cross-checked against the repo's
`audit_n1_vsign_v2_core.hist_k1`** (generator-permutation reconciled) at all 8 primes; numeric-DFT
cross-embedding dev $\le 5\times10^{-13}$. Twisted poly from the record's coefficient laws:
$e_1 = -V_1$, $e_2 = e_1^2 - \chi_2(-1)p$ **[P32]**, $e_3 = \chi_2(-1)p\,e_1$, $e_4 = p^2$.

**P32 at cells, first-hand:** at p=43 and p=67 the $e_2$ law was validated against the
$F_{p^2}$ trace sum (`core.hist_k2`): $V_2(a) = V_1(a)^2 - 2\chi_2(-1)p$ **exactly, 31/31 and 79/79
cells** — the $F_{p^2}$ histogram equals the algebraic prediction coefficient-for-coefficient.

**(2) Un-twisted baseline.** At $a=0$: $V_1(0) = \sum_P \chi_2(y_P) = 0$ exactly on all six
$p \equiv 3 \bmod 4$ primes (L1), and $L^*(0) = T^4 + pT^2 + p^2$ factors as
$\prod (T - \sqrt p\,\zeta_6^{k})$, $k \in \{1,2,4,5\}$ — the **rigid control state
$\sqrt p \cdot \mu_6$, orders $[6,3,6,3]$** (P27's secp structure), verified to $10^{-12}$.
On the $p \equiv 1 \bmod 4$ arm (349, 61): $V_1(0) \ne 0$ (36, 12) as expected (L1's cancellation is
$\chi_2(-1) = -1$-specific), purity $|\alpha| = \sqrt p$ still holds, and the baseline eigenvalues are
**not** roots of unity — consistent with P23's supersingularity being a $p \equiv 3 \bmod 4$ statement.

**(3)+(4) Twisted state, every cell $a \ne 0$, total enumeration** (30–312 cells/prime; 1030 cells):

| check | result (8 primes: 43, 67, 79, 127, 163, 211, 349, 61) |
|---|---|
| purity $\|\alpha_i\| = \sqrt p$ | max dev $2.9\times10^{-14}$ (float floor) |
| **$\zeta_3$ multiset law** | **0 failures at every prime**, max residual $5.5\times10^{-14}$ (exact) |
| closure pattern | $p \equiv 3$: $\{\alpha, \rho\alpha, -\bar\alpha, -\bar\rho\bar\alpha\}$ (trace imag); $p \equiv 1$: $\{\alpha, \rho\alpha, \bar\alpha, \bar\rho\bar\alpha\}$ (trace real), $\rho \in \{\zeta_3, \bar\zeta_3\}$ |
| M4 parity ($V_1(a)$ imag / real by $p \bmod 4$) | **exact** (coefficient-vector identity) at all cells |
| ω-descent $V_1(\lambda a) = V_1(a)$ | **exact** at all cells, both arms |
| **absolute rigidity survival** ($\alpha/\sqrt p \in \mu_m$, $m \le 66$) | **none, anywhere**: min $\|u^m - 1\| = 2.1\times10^{-6}$ (p=163), 5+ orders above the $\le 7\times10^{-12}$ float error bar — an exact hit would read at machine zero |
| $\max_a \|V_1(a)\|/\sqrt p$ | 1.56–1.93 (record's 1.932 @ p=547; the $\sqrt3$ sub-Weil target stays OPEN — not a bound) |

**The certificate's one-line answer to the D2 framing:** the twist **destroys the absolute rigidity at
every cell** ($\alpha/\sqrt p$ is never a root of unity) while **preserving exactly** purity, the
$\chi_2(-1)$-parity closure, and the $\zeta_3$ relative law — first-hand, on both mod-12 arms. This is
the v2 §2 rigidity budget, now total-enumeration and consolidated in one decidable artifact.

## Two new precision points beyond the record

1. **The closure pattern is parity-dependent.** The record said "its $\alpha \mapsto \bar\alpha$
analogue ($p \equiv 1 \bmod 4$)" without a multiset statement. First-hand: the closure involution is
$-\bar\alpha$ at $p \equiv 3 \bmod 4$ and $\bar\alpha$ at $p \equiv 1 \bmod 4$ — i.e. **the same
$\chi_2(-1)$ that sets $V(a)$'s Re/Im (M4) and the k=3 channel's component (parity lemma) also sets the
eigenvalue closure sign.** Three objects, one $\chi_2(-1)$ — direct first-hand fuel for the M24∩M4
unification probe.
2. **Descriptive caveat (not a contradiction):** pooled free-angle $\overline{|\cos\theta|} = 0.524$
(p≡3 arm; 0.610 all primes) vs Sato–Tate $4/(3\pi) = 0.424$ and uniform $2/\pi = 0.637$. The record's
"0.408 vs 0.424" equidistribution evidence is statistic/sample-dependent and does not replicate under
this pooling — the *exact* non-survival sweep above is the unambiguous form of "angles are free";
which limiting law they follow is **not settled by either measurement** (descriptive both ways).

## Non-abelianity sweep extension (`d2_nonabelian_sweep_v2.sage`)

Extends `RESULT_anew_twisted_eigenvalues_nonabelian_v1.md` (p=43, 67 generic + p=13 exception) with the
same machinery (`[2,2]` factorization over $\mathbb{Q}(\zeta_{12n})$ → discriminant Galois-test
$\sigma(D)/D \in K^2$, plants $D=5$ / $D=\zeta+2$ validated in **every** field tested):

| p | n | φ(12n) | verdict |
|---|---|---|---|
| 79 | 67 | 264 | **NON-ABELIAN** (both quads, σ₃₃₇) |
| 127 | 127 | 504 | **NON-ABELIAN** (both quads, σ₁₂₇₃) — anomalous order |
| 163 | 139 | 552 | **NON-ABELIAN** (both quads, σ₆₉₇) |
| **61** | 61 | 240 | **NON-ABELIAN** (both quads, σ₆₇₃) — **first p≡1 mod 12 arm + anomalous** |

With p=43, 67 from the record: **six generic primes, both mod-12 arms, both anomalous and non-anomalous
orders — every one NON-ABELIAN, every plant firing.** p=211 (φ=792) crashed on a PARI 1GB stack overflow
during plant validation (resource limit, not a result); relaunched with an 8GB stack together with p=349
(φ=1248) and the a=2 spread check — results append to `.log`. Grade of the confirmed rows:
`[VERIFIED — exact, plant-validated per field]`; a uniform-in-p proof remains open (as in the record).

## Scope / what this does not close

- `[VERIFIED — exact]` at 8 primes $\le 349$, all cells — not a uniform-in-$p$ proof (secp banner governs).
- **Still open, unchanged:** the L-mono mechanism (the $\mu_3$ in the monodromy forcing the $\zeta_3$
  uniformly — the *reason* the relative law survives), the a-family monodromy (N10-adjacent), the
  uniform non-abelianity proof, and any transfer/leakage content (none claimed here — D2's bridge
  question stays where `ANALYSIS_anew_bridge_n_visibility_v2` left it: the transfer map is the bottleneck).

## §Sweep FINAL (2026-08-27): nine generic primes, all NON-ABELIAN — the sweep is COMPLETE

Batch 2 landed: **p=349 NON-ABELIAN** (both quads at σ₉₄₉; 91.7 h on the degree-1248 field, plants
fired) and the **a-spread check at p=61 (a=2) NON-ABELIAN** (σ₆₇₃). Final tally: **43, 67, 79, 127,
163, 211, 349, 61@a=1, 61@a=2 — nine generic confirmations across both mod-12 arms, both order
classes, and two values of a; zero exceptions (p=13 remains the lone small-case exception); every
field's plants fired.** The generic non-abelianity of the a≠0 twisted eigenvalues is established as
the universal behavior at every tested generic prime. Uniform-in-p proof remains open (unchanged).
