# RESULT — L-mono brick 1 (GKR inputs): the alternative-moment table verified (U(1), N(T) excluded on the correct statistic); the ρ-branch is GLOBALLY CONSTANT per prime — the tensor glue is prime-rigid

**Date 2026-08-31. Grade: `[VERIFIED — exact factor-level, 3 primes all cells; moment table exact]`.**
Scripts: `lmono_brick1_branch_v2.sage` (+ `.log`, `lmono_brick1_branch.json`; v1 superseded — see the
discipline note), plus the numerical moment check (in-line, logged below). Companion:
`RESULT_lmono_brick2_tensor_shadow_v1.md` (brick 2: the rescaling exact at 7 cells),
`PLAN_lmono_monodromy_campaign_v1.md`.

## 1. The Goursat-alternative moment table (brick 1, part A)

The GKR discrimination on the effective-trace statistic $t = \mathrm{Tr}/(2\sqrt p)$ — normalized
Haar moments, verified numerically (2×10⁶ samples per group):

| group | $m_2$ | $m_4$ | $m_6$ | $m_8$ | $m_{10}$ |
|---|---|---|---|---|---|
| $SU(2)$ | 0.25003 | 0.12489 | 0.07791 | 0.05441 | 0.04070 |
| $U(1)$ (torus) | 0.49972 | 0.37489 | 0.31257 | 0.27362 | 0.24635 |
| $N(T)$ (torus normalizer) | 0.24958 | **0.18736** | 0.15627 | 0.13684 | 0.12324 |
| **measured (at-scale, 49,833 cells)** | 0.24916 | 0.12467 | 0.07811 | 0.05487 | 0.04134 |
| $\mathrm{Catalan}_k/4^k$ | 0.25000 | 0.12500 | 0.07812 | 0.05469 | 0.04102 |

**Only $SU(2)$ matches.** The torus is excluded at $m_2$ (arcsine $1/2$ vs measured $1/4$) — sharper
than the record's earlier $m_4 = 3/8$ argument, and on the *correct* statistic (the effective-angle
trace of the rank-4 object, which the tensor structure reduces to a single angle); the torus
**normalizer** — the one alternative sharing $m_2 = 1/4$ — is excluded at $m_4$ ($3/16$ vs $1/8$).
Together with the at-scale continuity (finite monodromy excluded), the 1-point GKR evidence for
"$G^0_{\rm geom}$ acts as $SU(2)$" is now clean and self-consistent.

> **[RETRACTED 2026-09-01 — see `RESULT_rho_branch_convention_v1.md`.]** The global constancy
> established below is **forced**, not measured: `u₁u₂ = e₄ = p²` is cell-independent, so
> `{u₁,u₂} = {εpζ₃, εpζ₃²}` at every cell, and `canon()` sorts on the constant coefficient first and
> never reads past it. The branch VALUE is `ε = leg = χ₂(−1)` composed with an n-inert lex tiebreak,
> i.e. **branch = 1 ⟺ p ≡ 3 mod 4** — confirmed out-of-sample at p=163. Furthermore half of
> `Gal(Q(ζ₁₂ₙ)/Q(ζ_n))` swaps the two factors, so **no `Q(ζ_n)`-rational labeling of the planes
> exists** and the §3 follow-up ("connect ρ_p to the `Q(√p,ζ₃)` embedding sign") is **VOID**.
> §1 (the moment table) is untouched and stands. §3's "the finite evidence is now maximal" is false:
> brick 2 has since been reduced to the identity `V₂ = V₁² − 2·leg·p` and verified at 312 cells.

## 2. The ρ-branch: GLOBALLY CONSTANT per prime (brick 1, part B — the new observable)

Brick 2 established roots$(g_2) = \rho\cdot$roots$(g_1)$ exactly per cell. The branch $\rho(a) \in
\{\zeta_3, \bar\zeta_3\}$ is then a per-cell function — **never measured before**. With the canonical
factor ordering (lexicographic on power-basis coefficient vectors) and the descent
$L^*(a) = L^*(\lambda a)$ verified exact at every prime tested:

| p | n | cells | branch distribution | mixed μ₃-orbits (must be 0) |
|---|---|---|---|---|
| 43 | 31 | 30 | **{1: 30} — constant** | 0 |
| 61 | 61 | 60 | **{2: 60} — constant** | 0 |
| 79 | 67 | 66 | **{1: 66} — constant** | 0 |

**The branch is not a function of the cell at all — it is a prime-level invariant.** The two
$\zeta_3$-conjugate planes carry a **global canonical labeling** over $\mathbb{Q}(\zeta_{12n})$:
T2 sharpens to

> **there is a global $\rho_p \in \{\zeta_3, \bar\zeta_3\}$ with
> $\mathrm{roots}(g_2^{(a)}) = \rho_p\cdot\mathrm{roots}(g_1^{(a)})$ at EVERY cell $a$** —

a stronger rigidity than the per-cell statement: the tensor glue is *prime-rigid*. (The values
1/2/1 at 43/61/79 suggest a possible $p \bmod 4$ dependence — 61 is the lone $p \equiv 1 \bmod 4$;
p=163, grinding, tests this: predicted branch 1 if the mod-4 law holds.)

**No multiplicative-character law (and a structural reason):** $\chi_3^{(n)}, \chi_3^{(p)}$ and
$\chi_2^{(p)}$ all cycle on μ₃-orbits ($\chi(\lambda) \ne 1$) — they are *structurally barred* from
equaling an orbit-constant branch; $\chi_2^{(n)}$ is orbit-constant at these primes and agrees at
exact chance (5/10, 10/20, 11/22). The earlier v1 "perfect anti-correlation" was an artifact of a
broken character labeling (reference element outside the order-3 subgroup) — retracted; the
corrected analysis above is what stands.

## 3. What this gives the campaign

- The GKR 1-point input is complete and consistent (SU(2)-only).
- The arithmetic side of the tensor conjecture is now **maximally rigid at finite level**: exact
  rescaling (brick 2) + global branch (brick 1B) + descent exactness (re-verified per prime here) +
  the ω-descent. What remains for the theorem is the sheaf-level statement (route B) or the GKR
  argument proper (route A) — the finite shadow cannot get sharper.
- A named new prime-level invariant: $\rho_p$ (the global branch) — worth connecting to the
  automatic-$\sqrt p$ witness $r = 1{+}p$ and the S-visibility embedding signs
  (`NOTE_anew_subgroup_structure_map_v1.md`) when the sweep data completes; a candidate law is
  $\rho_p = $ the $\mathbb{Q}(\sqrt p, \zeta_3)$-embedding sign class of $p$.

## Discipline note

Two analysis-layer bugs were caught and corrected in-session (the v1 orbit-consistency pairing and
the character labeling); v1's correlation tallies are retracted. The branch data itself (canonical
ordering, verified on a hand-checked orbit) was never wrong — only its interpretation moved, from
"character-correlated" to "globally constant," which is the stronger fact.
