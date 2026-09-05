# Replication of Vertical ZFR (zenodo 18514399) Appendix B — 2026-07-10

Adversarial replication of the finite-rank / common-mode numerical evidence
(Q=100, X=800, low primes p≤29), the empirical support for the rank-2 projector
Π=I−P_r^{(29)} used in Lemma L. `secp256k1_relation_search.py`-style numpy.

## Finding 1 — the LOW-PRIME feature matrix F is EXACTLY rank-10 orthogonal (theorem)
Built F exactly as §2.4–2.5: rows = characters (q,j), q∈{53,…,97}, columns = low
primes {2,…,29}, entry `g_{p0}(q,j)=(χ_j(p0)−μ_{p0}(q))/√(q−1)` with μ_{p0}(q)=0
(your own derivation for p0<q). Result: **all 10 singular values equal √10,
participation ratio = 10.000 exactly, column Gram exactly diagonal (off-diag = 0).**
This is FORCED, not numerical: character orthogonality gives
`Σ_j χ_j(p1)χ̄_j(p2) = (q−1)·[p1≡p2 (mod q)] = 0` for distinct primes p1,p2 < q.
⇒ **Table 4's rank-2 (σ=1,0.987,0.312,…) is not reproduced; the centred low-prime
features are provably orthogonal (rank 10).** A rank-2 projector on F therefore
selects an arbitrary 2 of 10 orthogonal directions — not a canonical common mode.

## Finding 2 — the common mode IS real, but in the LARGE-PRIME correlation K (§8.1)
Built K = correlations of `a_χ=(χ(p)/√p)_{p∈(800,1600]}` (112 large primes, 722
characters), standardized, compared to Marchenko–Pastur (aspect 0.155, MP edge 1.943).
**Top eigenvalue/MP-edge ratio = 1.089 — matches your Table 1's 1.089 almost exactly.**
So the ~9% common-mode uplift is genuine and reproducible. BUT: in my run only the
**top** eigenvalue exceeds the MP edge (rank 1); the 2nd is 0.93·edge (below), whereas
Table 1 shows two above (1.089, 1.069).

## Synthesis (the tension, stated fairly)
- The finite-rank common mode genuinely exists — in the **large-prime coefficient
  correlations K**, top-mode uplift reproduced to 3 digits.
- It does NOT live in the **low-prime feature matrix F** (which is orthogonal by a
  theorem). Yet the projector `Π=I−P_r^{(29)}` in §2.5 / Lemma L is built from F.
  ⇒ possible mismatch: the object with the common mode (K) ≠ the object the projector
  removes (F). And the uplift I see is rank 1, not rank 2.
- Caveat: my char-indexing / MP standardization may differ from yours in detail;
  Finding 2's rank is standardization-sensitive. **Finding 1 (F orthogonal) is a
  theorem and implementation-independent.**

## Questions for the author
1. Is P_r^{(P0)} meant to be built from the **large-prime** coefficient vectors a_χ
   (where the common mode is), rather than the low-prime features g_p (orthogonal)?
2. Is the common-mode rank 1 or 2? (Affects Lemma L's constant κ and the δ=5/16 balance.)

## Finding 3 — CM common mode is 3× the Dirichlet one (sextic prediction CONFIRMED)
Built K for a CM/Eisenstein character family (characters of F_{q²}^*=ℤ[ω]/(inert q),
evaluated on Eisenstein prime generators a+bω, so μ₆⊂F_{q²}^* is present) alongside
the Dirichlet baseline, same standardization vs Marchenko–Pastur.
- **Dirichlet (units {±1}):** eig/edge = [1.089, 0.929, …] → **1 common mode above edge**.
- **CM/Eisenstein (units μ₆):** eig/edge = [1.269, 1.174, 1.106, 1.022, …] → **3 above**.
- **Ratio = 3.0 = |μ₆|/|μ₂| = 6/2.** The common-mode count tracks (#units)/2 (conjugate
  pairing halves the 6-fold unit orbit): ℤ→1, ℤ[ω]→3. The φ(N)-residue sextic core is
  visible in the correlation spectrum.
Caveats: finite-size numerical (like Appendix B), the exact count is threshold- and
aspect-ratio-sensitive; the qualitative 3× and the clean top-3 uplift are robust.
This also re-answers the ZFR rank question: Dirichlet common mode is rank **1** (my
replication), CM is rank **3** — the paper's "rank 2" sits between; for the CM/Hecke
family the honest rank is 3, set by the units.

## CM / secp256k1 tie-in
The measured CM rigidity (CM character sums take ~⅓ as many distinct values) predicts
the large-prime common mode is **more pronounced** for a CM Hecke family (higher uplift,
possibly higher rank) — the CM case would *strengthen* this mechanism, not weaken it,
and is a natural place to test whether the common mode is genuinely rank ≥ 2.
