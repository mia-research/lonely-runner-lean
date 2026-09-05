# RESULT — L-mono brick 2: the tensor-structure shadow (T2 at factor level) holds EXACTLY at 7/7 fresh cells

**Date 2026-08-27. Grade: `[VERIFIED — exact, factor-level, 7 cells]`** Script:
`lmono_brick2_tensor_shadow_v1.sage` (+ `.log`). Executes brick 2 of
`PLAN_lmono_monodromy_campaign_v1.md` §7.2 (the campaign's first completed brick).

## The tested identity

At cell $a$, factor the twisted char-poly over $K = \mathbb{Q}(\zeta_{12n})$ (where the record's
$[2,2]$ factorization lives): $L^*(a) = g_1 g_2$, $g_i = T^2 - s_iT + u_i$ monic. The
**tensor-structure shadow** of the campaign's centralizer conjecture is the exact rescaling relation

$$g_2 \;=\; T^2 - \rho\, s_1 T + \rho^2 u_1, \qquad \rho \in \{\zeta_3, \bar\zeta_3\},$$

i.e. $\mathrm{roots}(g_2) = \rho\cdot\mathrm{roots}(g_1)$ — equivalently the **cross-plane trace
identity** $\mathrm{Tr}(\pi_a|W') = \rho\,\mathrm{Tr}(\pi_a|W)$ (T2) at the factor level. This is
strictly stronger than the numeric multiset certificate (`RESULT_d2_twist_rigidity_certificate_v1`)
and independent of it (exact ring arithmetic in $K$, $\zeta_3 = \zeta_{12n}^{4n}$).

## Result

| cell | n | field deg $\varphi(12n)$ | verdict | time |
|---|---|---|---|---|
| (79, a=1) | 67 | 264 | **EXACT** | 24 s |
| (79, a=2) | 67 | 264 | **EXACT** | 18 s |
| (127, a=1) | 127 | 504 | **EXACT** | 286 s |
| (163, a=1) | 139 | 552 | **EXACT** | 418 s |
| (61, a=1) | 61 | 240 (≡1 mod 12 arm) | **EXACT** | 16 s |
| (61, a=2) | 61 | 240 (≡1 mod 12 arm) | **EXACT** | 12 s |
| (211, a=1) | 199 | 792 | **EXACT** | 1357 s |

**7/7 cells EXACT** — both mod-12 arms, both $a$-values, through the largest field yet factored for
this object. Together with the record: the 22-prime numeric certificates (per-cell $g{=}2$), the P32
coefficient shadow (uniform in the $e_2$ identity), and the D2 certificate (the full multiset law at
8 primes × all cells), **T2 now stands verified in its sharpest finite form at every tested cell,
with zero exceptions of any kind.**

## What this does for the campaign

The centralizer conjecture (PLAN §4: $H^1_c \cong W \oplus (W \otimes \psi)$, $\psi$ the order-3
Kummer character of the twist parameter) predicts precisely this rescaling as the shadow of
$W' \cong W \otimes \psi$. Brick 2 is its **strongest confirmation to date**: the shadow is exact,
not approximate, and holds uniformly across the structural classes (arms, $a$-values, anomalous and
non-anomalous orders). The open step to the theorem is unchanged — the sheaf-level isomorphism (route
B) or the GKR rigidity argument (route A) — but the object they must produce is now pinned by exact
finite evidence at every scale tested.

**Next campaign bricks (per PLAN §7):** (1) the GKR input computation — the $\det$-twisted moment
invariants of the candidate group's rank-4 representation, compared against the FFT-measurable
statistics; (3) the $a{=}0$ unification against the S-visibility sweep (grinding; the rare-blindness
finding already narrows it).
