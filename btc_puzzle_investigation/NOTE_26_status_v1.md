# NOTE — #26 proof attack: status (one rigorous obstruction, one flagged gap; proof not closed)

**Date:** 2026-08-01
**Target:** uniform #26 — prove $e_2(a)=e_1(a)^2+p$ for all $a\in(\mathbb{Z}/n)^\times$, all $p\equiv7\bmod12$. Equivalently $V_2=V_1^2+2p$.
**Register:** investigation/collaboration (lens-open in §4; the math is purist). **Honest status: NOT proved.** Two real findings below narrow the search; one flags a gap in the freshest reduction doc.
**Scripts:** `reduce26_p1_explicit_probe_v1.sage`, `reduce26_antisymmetry_probe_v1.sage`, `reduce26_crosscheck_v1.sage`, `reduce26_signreversing_search_v1.sage`.

---

## 0. What is solid going in

- **The identity holds, exactly, at every measured cell.** $V_2(a)-V_1(a)^2 = -2\varepsilon p$ verified exactly by the circular-convolution residual at 22 primes / 3585 cells (A1, `RESULT_120deg_conjoined_certificate_v1.md`); the convolution $f[d]=h_2[d]-(h_1*h_1)[d]$ is $0$ for all $d\ne0$. At p=43 this session re-verified: `const_off_zero=True`, $V_2-V_1^2=86=2p$.
- **The reduction to a pair-space identity** (`RESULT_26_reduction_to_character_sum_v1.md`, S1–S3) is the sharpest attack surface in the corpus: #26 $\Leftrightarrow$ "for every $R\ne O$, $\Sigma_{\text{rational pairs}}\chi_2(y_Qy_{Q'}) = \Sigma_{\text{conjugate pairs}}\chi_2(y_Py_{\phi P})$," equivalently (the doc's claim) $\Leftrightarrow \sum_{t\in\mathbb{P}^1(\mathbb{F}_p)}\chi_2(g(t)F(t))=0$.

## 1. Finding (rigorous, negative): the $E[2]$-translation antisymmetry is impossible

The reduction doc's §5 lead: an involution $\sigma$ of $\mathbb{P}^1$ with $\chi_2(g(\sigma t)F(\sigma t))=-\chi_2(g(t)F(t))$ would pair terms and force the sum to $0$; "natural candidates are the $E[2]$-translations $\tau_T$." The doc flags "note these are not $\mathbb{F}_p$-rational when $n$ is odd" but offers them as the lead.

**The flag is fatal, rigorously.** $\tau_T(P)=P+T$ commutes with $\iota(P)=R-P$ iff $2T=O$ (so $\tau_T$ descends to an automorphism $\sigma_T$ of $E/\iota$). The descent is $\mathbb{F}_p$-rational on the quotient iff $\sigma_T$ commutes with Frobenius there:

$$\sigma_T\text{ is }\mathbb{F}_p\text{-rational on }E/\iota \iff \mathrm{Frob}(T)=T \iff T\in E[2](\mathbb{F}_p).$$

(Proof: $\mathrm{Frob}(\sigma_T\{P,\iota P\})=\{\mathrm{Frob}P+\mathrm{Frob}T,\iota(\mathrm{Frob}P+\mathrm{Frob}T)\}$ must equal $\sigma_T(\mathrm{Frob}\{P,\iota P\})=\{\mathrm{Frob}P+T,\iota\mathrm{Frob}P+T\}$; equality forces $\mathrm{Frob}T=T$.) But **$E[2](\mathbb{F}_p)=\{O\}$ whenever $n=\#E(\mathbb{F}_p)$ is odd** (no rational 2-torsion). Hence no nontrivial $E[2]$-translation descends to an $\mathbb{F}_p$-rational involution of $\mathbb{P}^1$, and none can pair $\mathbb{F}_p$-points to force the vanishing.

**The named lead is killed.** The mechanism — whatever it is — is not an $\mathbb{F}_p$-rational pointwise antisymmetry from $E[2]$.

## 2. Correction (the "+1" was my enumeration, not a gap in the doc)

An earlier draft of this note flagged a "reproducibility gap": my direct computation gave $\Sigma_{\text{rat}}-\Sigma_{\text{conj}}=+1$ for every $R$, not $0$ as the doc's pair-space identity claims. **That flag was wrong — it was a diagonal-handling difference in my enumeration, not a gap.** Resolved on re-derivation:

- The convolution $(h_1*h_1)[e]$ runs over pairs with $Q+Q'=R$, $Q,Q'\ne O$ (since $h_1[0]=0$). The diagonal $Q=Q'=P_0$ (the unique $2P_0=R$) contributes $\chi_2(y_{P_0})^2=+1$. So RHS $= +1 + 2\,\Sigma_{\text{rat,distinct}}$.
- The $h_2[e]$ side (over $\mathbb{F}_{p^2}$): each conjugate pair $\{P,\phi P\}$ contributes $2\,\chi_2(y_P y_{\phi P})$, and the rational $P_0$ (where $P=\phi P$) contributes once, $\chi_2^{(2)}(y_{P_0})=\chi_2(y_{P_0}^2)=+1$. So LHS $= +1 + 2\,\Sigma_{\text{conj}}$.
- Equating: $+1+2\Sigma_{\text{conj}} = +1+2\Sigma_{\text{rat,distinct}}$, i.e. **$\Sigma_{\text{conj}} = \Sigma_{\text{rat,distinct}}$** — exactly the doc's identity. My enumeration had *included* $P_0$ in "$\Sigma_{\text{rat}}$," giving $\Sigma_{\text{rat}}-\Sigma_{\text{conj}}=+1$; subtracting the diagonal recovers $0$. **The pair-space reduction is sound.** The earlier "Finding 2 / flagged gap" is withdrawn.

(The $\sum_t\chi_2(gF)$ values that varied with $R$ reflected the same diagonal issue plus the not-yet-correct quotient coordinate; they are not evidence against the pair-space identity, which is what actually carries #26.)

## 3. The sharp remaining target

With the pair-space identity confirmed sound, the open question is purely:

> **Why does $\displaystyle\sum_{\substack{\text{conjugate pairs}\\P+\phi P=R}}\chi_2(y_P y_{\phi P}) \;=\; \sum_{\substack{\text{rational distinct pairs}\\Q+Q'=R}}\chi_2(y_Q y_{Q'})$ hold for every $R\ne O$?**

Both sides sum $\chi_2(y_1 y_2)$ over Galois-stable unordered pairs $\{P_1,P_2\}$ with $P_1+P_2=R$, split by Frobenius type (inert conjugate pair vs split rational pair). The equality says **the two Frobenius types contribute equally.** Finding 1 (§1) rules out the explanation "a pointwise antisymmetry pairs the two sides." The mechanism — whatever forces the two Frobenius-stratum sums to agree — is the content of #26, and it is not yet identified.

## 4. Probe rounds 2–3: three more mechanisms ruled out

After correcting the "$+1$" (§2), three further probes each ruled out a candidate mechanism:

- **(R2) Multiset agreement — ruled out.** The multisets $\{\chi_2(y_1y_2)\}$ on the split and inert strata do **not** agree (sizes 14 vs 28 at p=43; sign distributions differ, e.g. R=[3]G: rational $+4/-10$, conjugate $+11/-17$ — not a $2\times$ scaling). So there is no sign-preserving bijection between the strata. The *sums* agree exactly for every $R$.
- **(R2) Simple character / fixed-magnitude Gauss sum — ruled out.** $S(e):=\Sigma_{\text{rat,distinct}}(e)=\Sigma_{\text{conj}}(e)$ has $\widehat{S}(a)=V_1(a)^2/2$ (up to the rational constant from the diagonal) — i.e. $S$ is essentially $\mathrm{IDFT}(V_1^2)$, the autocorrelation of $h_1$ (tautologically #26). $V_1(a)=-e_1(a)$ is **not** a fixed-magnitude Gauss sum: $|V_1(a)|^2$ takes several distinct values ($12.2, 104.0, 3.5, 26.2, 9.0$ at p=43) repeating across $a$ — this is just the eigenvalue angle $\theta_a$ varying (Sato–Tate), $|V_1|^2 = 2p(1-\cos 2\psi)$. No simple-character shortcut.
- **(R3) Coset-character of $E'(\mathbb{F}_p)$ — ruled out.** Structural lead confirmed: $\mathrm{Tr}:E(\mathbb{F}_{p^2})\to E(\mathbb{F}_p)$ is a group hom, $\ker(\mathrm{Tr})=\{P:\phi P=-P\}\cong E'(\mathbb{F}_p)$ (the quadratic twist; verified $\#\ker\mathrm{Tr}=57=\#E'$ at p=43), and the inert fibre $\mathrm{Tr}^{-1}(R)$ is a **coset of $\ker(\mathrm{Tr})$**. So $\Sigma_{\text{conj}}(R)$ is a character sum over a coset of the twist group. But $\chi_2(N(y_P))$ is **not** a group homomorphism on $\ker(\mathrm{Tr})$ (tested $K\mapsto\chi_2(N(y_{P_0+K}))$ multiplicative; fails) — so it is not a multiplicative character of the coset, and the coset-sum is not a clean Gauss sum over $E'$. The imbalance in the coset sign-count ($+28/-28$ for $R=[1]G$, $+22/-34$ for $R=[3]G$) equals $2\Sigma_{\text{conj}}=2\Sigma_{\text{rat}}$, but *why* it equals the rational-stratum sum is still open.

## 5. Round 4: the function-field setup flaw diagnosed (root cause)

The function-field approach ($g(t), F(t)$ explicit) repeatedly failed across four attempts. **Root cause found:** the coordinate $s_1 = x + \iota(x)$ I used as "the $\iota$-invariant quotient coordinate" is **not** a generator of the fixed field $L^{\langle\iota\rangle}$. It IS $\iota$-invariant (verified: $s_1(\iota P)=x(\iota P)+x(R-\iota P)=x(R-P)+x(P)=s_1(P)$), but it is **many-to-one on $\iota$-orbits**: 884 orbits over $E(\mathbb{F}_{p^2})$ collapse to only 30 distinct $s_1$-values. So $s_1 = h(t)$ for a high-degree $h$, with $t$ the true quotient coordinate, and $s_1 \mapsto F$ is genuinely multi-valued (20 of 22 sampled $s_1$-values give two $F$'s).

**This explains the earlier "flagged gap" (round 1, since withdrawn) and every function-field failure:** $\sum_t\chi_2(gF)$ computed via $s_1$ was meaningless, because $s_1$ did not range bijectively over $\mathbb{P}^1$. The pair-space identity (rounds 2–3, which do not use $s_1$) remains sound. The reduction doc's step "parametrise by $P_1$; then $E/\iota \cong \mathbb{P}^1$" is correct *in principle*, but the doc never specified the coordinate, and $s_1$ was the wrong guess. The correct $t$ is a degree-1-on-orbits generator of $L^{\langle\iota\rangle}$ — a standard but nontrivial function-field computation that Sage's subfield machinery can do but that fought me across attempts.

## 6. Honest framing from the Fourier analysis

A separate, decisive observation: $V_2 = V_1^2 + 2p$ **is** the eigenvalue lock, by Newton's identities ($p_2 = e_1^2 - 2e_2$, and $V_k = -p_k$, so $V_2 - V_1^2 = -2e_2 + (\text{e}_1\text{-terms})$; the identity holds iff $e_2 = e_1^2 + p$, which *is* the 120° lock). Therefore elementary pair-space / Fourier / coset manipulation **cannot independently prove #26** — every such route reduces back to the eigenvalue lock. The mechanism is the $\zeta_3$ in the monodromy of the Kummer sheaf $L_{\chi_2(y)}\otimes L_{\chi_a}$, a **cohomological** statement (the surviving corpus L-mono route). The explicit $g(t), F(t)$ on the *correct* quotient could still reveal a factorization (a cohomological decomposition in disguise), but the sign-pattern variation seen across rounds 1–3 suggests it will not be elementary.

## 7. Where this leaves #26 (final status, this session)

- **Not proved.** Five elementary mechanisms now ruled out: (i) pointwise antisymmetry / $E[2]$-translation (§1); (ii) simple character / fixed-magnitude Gauss sum (R2); (iii) multiset bijection (R2); (iv) coset-character of $E'(\mathbb{F}_p)$ (R3); (v) the $s_1$-coordinate $\mathbb{P}^1$ setup (R4, the flaw that explained the earlier false "gap"). Plus the corpus routes already blocked (Stickelberger-on-eigenvalues, etc.).
- **The elementary attack is exhausted.** The identity is exact and verified at scale ($V_2-V_1^2=2p$, A1); "not proved" is the honest state, not a hint of falsehood.
- **The remaining route is genuinely sheaf-cohomological:** (a) compute the correct quotient coordinate $t$ and test a revealing factorization of $gF$ (worth doing once the function-field API cooperates — the flaw is now understood, not mysterious); or (b) directly identify the $\zeta_3$ in the monodromy of $L_{\chi_2(y)}\otimes L_{\chi_a}$ (the L-mono route, research-grade). Both are beyond single-session elementary probing.
- **Counter-prior discipline, reaffirmed:** five rounds, each rigorously characterized. "Mechanism not found" is a failed search, **not** evidence the identity is false. #26 remains the load-bearing open fact, its attack surface materially narrowed, the false "gap" retracted, and the genuine obstacle (cohomological mechanism + correct quotient coordinate) cleanly identified.

## 8. Files / reproducibility

- `reduce26_crosscheck_v1.sage` — re-verifies $V_2-V_1^2=2p$ (HOLDS) and tabulates the pair sums + $\sum_t\chi_2(gF)$ per $R$ (the §2 table).
- `reduce26_signreversing_search_v1.sage` — brute-force search over $\mathbb{F}_p$-rational Möbius involutions for a sign-reversing one (NONE found).
- `reduce26_multiset_probe_v1.sage`, `reduce26_S_of_e_probe_v1.sage`, `reduce26_kerTr_probe_v1.sage` — rounds 2–3 probes (multiset, $S(e)$/DFT, $\ker\mathrm{Tr}$ coset).
- `reduce26_quotient_field_v1.sage`, `reduce26_F_of_s1_v{1,2}.sage` — round 4 function-field attempts (the $s_1$-coordinate flaw, §5; kept for provenance).
- All p=43, $E:y^2=x^3+7$; reproducible by `sage <script>.sage`.

## 9. What I did NOT do (honest scope)

- Did not build the correct explicit quotient coordinate $g(t), F(t)\in\mathbb{F}_p(t)$. The flaw is now understood ($s_1$ is degree-many on orbits, not a generator; §5), but finding the true generator via Sage's function-field subfield machinery is the remaining technical step — not completed.
- Did not prove #26. Five elementary mechanisms ruled out; the genuine route is cohomological (the $\zeta_3$ in the sheaf monodromy, §6–7).
- Did not search the literature (the doc says run the cheap check first; the cheap checks are now done and negative for the elementary mechanisms).
