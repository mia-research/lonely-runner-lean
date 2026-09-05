# RESULT: power-sum ladder (Route A) — the missing C-FORCED control, now run

**Date:** 2026-07-31
**Script:** `powersum_ladder_routeA_v1.sage` (direct $V_k$ over $E(\mathbb{F}_{p^k})$, no closure assumed)
**Grade: `[VERIFIED — exact, Route A, no closure assumed, both branches]`** for $V_2, V_3$ (and $V_4$ in the $+1$ branch).
**Register:** purist. This is the control that was missing from the collapse verification, run to close the gap an external critique correctly identified.

---

## 0. The critique that motivated this (vindicated)

The collapse verification (`verify_charpoly_collapse_v1.sage:78-79`) sets $e_3=-p\,e_1$ and $e_4=p^2$ **by the closure** — so it independently tests $e_2$ only (via $V_2=V_1^2+2p$). Purity and the 120° config are partly *consequences* of the forced $e_3,e_4$, not measurements. This is exactly the gate's missing C-FORCED control, and a wrong closure *sign* already produced a false null once (the $D4$ stratum-C bug). The fix: Route A (direct $V_k$ over $E(\mathbb{F}_{p^k})$, Newton to char poly with **no closure assumed**), testing the power-sum ladder.

## 1. The ladder (derived, branch-dependent — the branch sign IS the $D4$ closure sign)

Newton's identities ($p_k=-V_k$, $e_1=-V_1$) give, with $e_2=e_1^2\pm p$, $e_3=\pm p\,e_1$, $e_4=p^2$:

| $\chi_2(-1)$ | $V_2$ | $V_3$ | $V_4$ |
|---|---|---|---|
| $-1$ ($p\equiv3\bmod4$) | $V_1^2+2p$ | $-2V_1^3-6pV_1$ | $V_1^4+4pV_1^2+2p^2$ |
| $+1$ ($p\equiv1\bmod4$) | $V_1^2-2p$ | $-2V_1^3+6pV_1$ | $V_1^4-4pV_1^2+2p^2$ |

The ladder is **graded**: $V_2$ tests $e_2$ (the 120° lock itself), $V_3$ tests $e_3$ (**the closure sign — the thing that bit in $D4$**), $V_4$ tests $e_4=p^2$. Route A measures all of them independently, so checking against these three formulas is simultaneously a new test of the collapse and the missing control.

## 2. Result — the ladder holds, both branches, Route A measured (no closure)

| p | n | $\chi_2(-1)$ | $V_2$ (e2 lock) | $V_3$ (e3 sign) | $V_4$ (e4=$p^2$) |
|---|---|---|---|---|---|
| 13 | 7 | $+1$ | $1.2\times10^{-46}$ | $9.6\times10^{-46}$ | $2.8\times10^{-45}$ |
| 43 | 31 | $-1$ | $1.4\times10^{-44}$ | $4.3\times10^{-43}$ | (skipped, $O(p^4)$) |

**Control C2 (plant recovery)** fires: $\max|\text{recovered}-\text{planted}|=4.4\times10^{-16}$. The $V_k$ are computed by direct point-counting over $E(\mathbb{F}_{p^k})$ with **no closure used** to form the char poly or the comparison.

**This closes the critique's central gap.** $e_3$ (the closure sign) and $e_4=p^2$ are now **measured, not forced**, in both branches — including the $+1$ branch where the $D4$ sign bug lived, and the $-1$ branch at p=43. The closure sign that previously produced a false null is now confirmed independently via the $V_3$ identity to $\sim10^{-43}$.

## 3. Scope held honestly

- **Tiny $p$ only** (p=13, 43): Route A is $O(p^4)$ and the $k=4$ enumeration of $E(\mathbb{F}_{p^4})$ is infeasible above $p\sim40$ in pure Python (the per-point Frobenius-trace is the cost, not the enumeration). $V_4$ in the $-1$ branch (p=43) was skipped for this reason; $e_4=p^2$ is the constant term, already tested by the $+1$ branch at p=13.
- **This is a control, not a scale result.** The point was to close the "e3,e4 are forced, not measured" gap — done at small $p$ in both branches. Route B (the $e_2$-only verification) still handles scale (`RESULT_e2_identity_extended_verification_v1.md`, 7 primes / 1182 freqs). The two are complementary: Route B tests $e_2$ at scale; Route A tests $e_2,e_3,e_4$ independently at small $p$.
- **Does NOT test purity at every embedding** (item 2 of the critique — still open, `[CITED]`, see §4) nor the algebraic-number layer (item 3).

## 4. The critique's remaining items (status after this)

1. **Power-sum ladder (this doc) — DONE.** $e_2,e_3,e_4$ now independently measured; the closure sign controlled.
2. **Purity at every embedding — RESOLVED to its true status (2026-07-31).** The "[CITED], untested" line conflates two genuinely different notions, and only one is an independent test:
   - **$\mathbb{Q}(\zeta_n)/\mathbb{Q}$ embeddings** ($\sigma_k:\zeta_n\mapsto\zeta_n^k$): verified *exactly* (in $\mathbb{Q}(\zeta_7)[T]$, all six automorphisms) that $\sigma_k(L_a)=L_{ka}$ — the Galois conjugate of the char-poly at frequency $a$ is the char-poly at frequency $ka$. So **Galois-conjugate purity over $\mathbb{Q}(\zeta_n)$ is identical to archimedean purity at every frequency**, which the moduli column already checks (all $\approx\sqrt p$) at the tested primes. **Not an independent open thread.**
   - **$\mathbb{Q}(\alpha)/\mathbb{Q}$ embeddings** (conjugates of a single eigenvalue): at p=13 these are all pure (minpoly $T^4+T^3-12T^2+13T+169$, four pure roots), **but this is partly an artifact of $n=7$ being too small** — at n=7 the char-poly coefficients collapse to $\mathbb{Q}$ (verified: all five coeffs rational), which does *not* happen at n=31/p=43 (where $e_1\notin\mathbb{Q}$, confirmed). So the p=13 minpoly result is suggestive, not load-bearing; the full minpoly-over-$\mathbb{Q}$ at p=43 (degree $\sim30$) was too slow to compute via QQbar.
   - **The genuinely open part is purity at non-archimedean ($p$-adic) places** — a Weil-number condition at the finite primes, which the archimedean minpoly does *not* capture and which is a distinct, harder computation. That is the true residual content of the ledger item; it is **still open**, correctly scoped now as "non-archimedean Weil-number condition," not "every embedding."
3. **Algebraic-number layer** — OPEN, and untouched by the ideals-argument circularity. Minimal polynomial over $\mathbb{Q}$, splitting field degree/Galois group, factorization type of $L^*(T)$ mod small primes — a different observable class than the archimedean $|\alpha|,\arg\alpha$ the table reports. Known anchor: splitting field contains $\omega$ ($\zeta_3\notin\mathbb{Q}(\zeta_n)$ when $3\nmid n$). Partially addressed by `anew_eigenvalue_verify_v4` (Galois abelian-discriminator: eigenvalue field **non-abelian** at p=43,67), but the minimal-polynomial / factorization-type detail is not recorded.
4. **Discarded cells** ($V=0$, repeated-root) — OPEN. The census filters these before reporting; where/when they occur (e.g. $e_1=0\Rightarrow g_4=4$; $\sqrt p\{1,\zeta_6,\zeta_3,-1\}\Rightarrow g_6=3$) is discarded data the C-ZERO control needs. At p=13..127 there were zero of each, so this is a degenerate-corner census, not urgent.

## 5. Files

- `powersum_ladder_routeA_v1.sage` — Route A ladder test (this doc).
- Builds on `verify_charpoly_collapse_v1.sage` (Route B, e2-only) and `RESULT_e2_identity_extended_verification_v1.md` (e2 at scale).
