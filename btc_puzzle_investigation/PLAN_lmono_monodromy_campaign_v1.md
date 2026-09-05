# PLAN — the L-mono campaign: proving the $\zeta_3$ relative rigidity is forced by the monodromy structure (formulation, not yet proof)

**Date 2026-08-22.** The theoretical capstone track, scoped per the user blueprint (ω-descent
constraint / SU(2) component / centralizer target). No grade moves — this is a formulation document
with the banked inputs cited and the precise gap isolated. Companion computations this session:
`RESULT_d2_twist_rigidity_certificate_v1.md` (the ω-descent exact on both arms; the parity-dependent
closure), `NOTE_anew_subgroup_structure_map_v1.md` (the $\zeta_3$-eigenplane algebra).

## 1. The precise target theorem (one line, three equivalent forms)

For every cell $a \in (\mathbb{Z}/n)^*$ and every $p \equiv 7 \bmod 12$ (⊇ secp):

**(T1)** the eigenvalue multiset is $\{\alpha,\ \zeta_3\alpha,\ -\bar\alpha,\ -\bar\zeta_3\bar\alpha\}$ —
the spectrum is a single $\omega$-orbit plus its negative-conjugate;

**(T2)** over $K = \mathbb{Q}(\zeta_{12n})$, the $[2,2]$ factorization $L^*(a) = g_1 g_2$ satisfies
$\mathrm{roots}(g_2) = \zeta_3 \cdot \mathrm{roots}(g_1)$ — **the cross-plane trace identity**
$\mathrm{Tr}(\pi_a | W') = \zeta_3\,\mathrm{Tr}(\pi_a | W)$ for the two rank-2 pieces;

**(T3)** the Frobenius conjugacy classes $[\pi_a]$ all lie in the $\zeta_3$-**saturated** locus of the
arithmetic monodromy group (§4).

*Consistency anchor:* at $a = 0$ the same shape holds with $\alpha = \sqrt p\,\zeta_6^2$ (the
supersingular baseline $\sqrt p\,\mu_6$, orders $[6,3,6,3]$ — verified exactly in the D2
certificate). **Banked:** T2 per-cell at 22 primes (`RESULT_n1_120deg_exact_v1`), the coefficient
shadow of T2 uniformly via P32 (`RESULT_26_PROVED_weil_restriction`, the $e_2$ identity), purity
numerically to 160-bit (N31 holds the citation debt).

## 2. Banked inputs (what the proof may consume, with grades)

| input | statement | grade / file |
|---|---|---|
| ω-descent | $V(\lambda a) = V(a)$ exactly; $L^*(a)$ over the index-3 subfield; **exact on both mod-12 arms** | `[VERIFIED]` + D2 certificate (2026-08-21) |
| non-abelianity | $a \ne 0$ eigenvalues generate non-abelian non-Galois fields — **the $\zeta_3$ is not eigenvalue-arithmetic; it is internal to the $GL$-structure** | `[VERIFIED — 7 generic primes, both arms]` `RESULT_anew_twisted_eigenvalues_nonabelian` + sweep |
| $G^0_{\rm geom}$ acts as $SU(2)$ in the trace | semicircle marginal, 49,833 cells, 8 moments to 4–5 sig figs; finite monodromy excluded (continuity); torus excluded ($m_4 = 1/8 \ne 3/8$) | `[VERIFIED — at scale]` `RESULT_monodromy_sato_tane_at_scale_v1` |
| 2-point statistics | spacing/number-variance/tail/small-ball vs the semicircle null at 17+15 primes: **NULL — the cross-cell spectrum is iid Sato–Tate, not GUE-rigid** | `RESULT_semicircle_null_and_verification_v1` |
| rank-4 caveat | the Katz trichotomy is rank-2; a rank-4 semicircle trace is *consistent with* $H^1 \cong W \otimes R$ (tensor-decomposition candidate) but not forced by the 1-point marginal alone | §3 of the at-scale RESULT |
| $E[u^4]$ / M34 | consistent with full $SU(2)$, excludes the 3/8-torus/CM reduction (12/12 OOS) | `[EMPIRICAL — scoped]` |
| the $\zeta_3$-plane algebra at $a=0$ | $f = (T^2 \mp \sqrt p T + p)$, the $\zeta_3$-eigenpairing $=$ the conjugation pairing; $r = 1+p$ the automatic $\sqrt p$ witness mod $\ell | M$ | `NOTE_anew_subgroup_structure_map_v1` |

## 3. The ω-descent constraint, formalized

The automorphism $\omega: (x,y) \mapsto (\beta x, y)$ ($\beta^3 = 1$, $p \equiv 1 \bmod 3$) satisfies
$\omega^*(L_{\chi_2(y)} \otimes L_{\chi_a}) = L_{\chi_2(y)} \otimes L_{\chi_{a\lambda}}$ — it
**intertwines the fibers of the twist family along the orbit $\{a, \lambda a, \lambda^2 a\}$**, not
within a fiber (the §3 retraction of `CORRECTION_deflation_overreach` stands: no within-cell
$\mu_3$-equivariance at $a \ne 0$). Consequence for the monodromy: the arithmetic monodromy
representation of the orbit-quotient family is well-defined with the descent acting trivially on
invariants — **the proof may quotient by the orbit, but the forcing must be group-theoretic within the
fiber.** This is why v3 §2's verdict ("necessary context, not the lever") is correct and final.

## 4. The centralizer target (the heart of the campaign)

**Conjecture (the structural home of $\zeta_3$):** the twist family's sheaf cohomology carries a
tensor structure
$$H^1_c(E, L_{\chi_2(y)} \otimes L_{\chi_a}) \;\cong\; W_a \oplus (W_a \otimes \psi),$$
where $\psi$ is the **order-3 Kummer character of the twist parameter**, $W_a$ a rank-2 piece with
$G^0_{\rm geom}|_{W} = \mathrm{SL}_2$, and the arithmetic monodromy lands in
$$G_{\rm ar} \subseteq \big(\mathrm{SL}_2(W) \text{ acting diagonally}\big) \cdot \langle \text{Kummer-}\mu_3 \text{ on } W \otimes \psi \rangle \cdot \{\pm 1\}\text{-twists}.$$
On such a group, **every** element's spectrum is automatically $\omega$-saturated (the second plane's
eigenvalues are $\zeta_3^j \times$ the first's by construction) — T3 ⟹ T1/T2 for all $a$ at once.
This explains simultaneously: the per-cell 120° law, its survival at $a=0$ (where $\psi$ degenerates
to the CM structure), the iid cross-cell statistics (independent Frobenius draws from the group), and
— at $a = 0$ — the $S$-visibility embedding-sign texture (the same $\zeta_3$/Kummer character, now
seen in the $\mathbb{Q}(\sqrt p, \zeta_3)$ splitting).

## 5. Proof routes, in priority order

**(A) Katz rigidity / GOURSAT–KOLCHIN–RIBET (primary).** The family is Kummer/hypergeometric-type
(the D2 prereg's formalization, `PREREG_D2_lang_hypergeometric_relin_v1`, is the notational anchor).
GKR: if the collection of $\det$-twisted 4th-moment statistics of the rank-4 sheaf matches those of
the candidate group, the geometric monodromy **is** that group (up to finite center). Inputs in hand:
semicircle (1-point), $m_4 = 1/8$, 2-point iid. **Owed first:** the explicit GKR input list for the
candidate $G$ (the $\det \otimes$-masked moment invariants of $\mathrm{SL}_2 \cdot \mu_3 \cdot \{\pm\}$
in the rank-4 representation) — a finite, nameable computation.
**(B) The sheaf-isomorphism route.** Establish $W' \cong W \otimes \psi$ as an isomorphism of
sheaves (not just numeric $[2,2]$ factorization). A constructive path: the $\omega$-intertwining +
Kummer structure of the Lang torsor should produce it; the per-cell certificates (22 primes) are its
traces.
**(C) Monodromy-at-scale completion.** Pin the finite center / component group via the named
2-point discriminators (already NULL for GUE-type rigidity — the residual discrimination is
center-vs-center×finite).
(C) supports (A); it does not alone prove T1.

## 6. Falsifiers (what would kill the conjecture)

- any cell violating T2 beyond purity noise (none in 22 primes; P32 makes the coefficient level
  uniform);
- a 4th-moment signature of the torus/CM class ($m_4 = 3/8$) — excluded;
- GUE-type cross-cell rigidity (would contradict the diagonal-$SL_2$/Kummer picture) — excluded (NULL);
- failure of the tensor-structure numeric shadow: the $[2,2]$ factors NOT related by the $\zeta_3$
  rescaling at any new cell.

## 7. Session plan (the campaign, brick-sized)

1. **GKR-input computation** (deterministic): the moment invariants of the candidate $G$'s rank-4
   representation; compare against the FFT-measurable cell statistics (the at-scale route extends).
2. **Tensor-structure shadow test**: verify $g_2(T) = \zeta_3^{2\deg}\!-$rescaled $g_1$ exactly at
   fresh cells (extend the 22-prime certificate; cheap via the D2 certificate machinery).
3. **The $a=0$ unification**: close the $S$-visibility character (the sweep grinding now) and check
   it against the Kummer-$\psi$ prediction — if they agree, §4 gets its first independent
   confirmation.
4. Only then: the GKR argument written as a proof, with the Katz citations passing
   `citation-verifier` (the project rule).

**Interplay with Brick E (both-ends attack):** Brick E bounds the *return leg* (the transfer map's
degree); L-mono proves the *spectral geometry* (why the cover's rigidity survives the twist). If
Brick E returns "high $D$" and L-mono closes, the supersingular-cover attack surface is completely
mapped: rigid within cells, decoupled across cells, and non-homomorphically scrambled on return.
