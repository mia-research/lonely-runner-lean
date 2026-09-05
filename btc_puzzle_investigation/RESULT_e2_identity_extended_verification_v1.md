# RESULT: extended verification of `e₂ = e₁² + p` (the char-poly collapse) + mechanism re-examination

**Date:** 2026-07-31
**Script:** `verify_e2_identity_extended_v1.sage` (float-free integer convolution route)
**Grade: `[VERIFIED — exact integer arithmetic, 7 primes / 1182 frequencies, 0 counterexamples]`** for the identity; **`[NEGATIVE — refutes a specific proposed mechanism]`** for the commutative-commutation hypothesis.
**Register:** purist. This is a findings + mechanism-re-examination document; it does not move the cap grade (that needs a proof, not a sweep, and "no finite sweep can" prove uniformity).

---

## 0. What was checked and why

The char-poly collapse (`ANALYSIS_n1_charpoly_collapse_v1.md`) reduces the cap chain to a single open link: the identity $e_2(a)=e_1(a)^2+p$ for all $a$, all $p\equiv 7\bmod 12$ — equivalent to $V_2(a)=V_1(a)^2+2p$, equivalent to the 120° law. The record verified this at **3 primes** (43, 67, 127) by brute $E(\mathbb{F}_{p^2})$ enumeration (`verify_V2_identity_v1.sage`), which is the $O(p^2)$ wall. This document (a) extends that verification with a float-free route, (b) checks a falsifiable prediction of the proposed mechanism, and (c) records an honest correction about the mechanism.

**Honest correction on the record first.** The record's headline "[VERIFIED-exact] at 8-10 primes" for the $V_2$ identity is, in `verify_V2_identity_v1.sage`, actually **3 primes** — the same $O(p^2)$ wall that limits this work. (The 120° law *itself* is verified at 22 primes via the fast `g=deg gcd` route in `freeze_n1_120deg_v1.py` / `RESULT_n1_120deg_exact_v1.json`, all cells `g=2`, in seconds — that part is solid and unaffected.) Flagging this so the "8-10 primes" figure is not relied upon for the $V_2$ identity specifically.

---

## 1. The float-free integer convolution route

**Identity.** $V_2(a)-V_1(a)^2=2p$ for all $a\neq0$ is equivalent (by inverse DFT) to the circular-convolution sequence
$$f[d]\;:=\;h_2[d]-(h_1\ast h_1)[d]$$
satisfying **both** (i) $f[d]=c$ constant for all $d\neq0$, **and** (ii) $f[0]-c=2p$.
(Because $\sum_{d\neq0}\zeta^{ad}=-1$ for $a\neq0$, so $V_2(a)-V_1(a)^2=\sum_d f[d]\zeta^{ad}=f[0]-c$.)
This is an **exact integer check** — no complex field, no precision.

**Normalization subtlety (worth recording).** There are two valid conventions for trace-zero points $P\in E(\mathbb{F}_{p^2})$ (those with $P+P^p=O$) at $k=2$:
- *count into bin 0* (record's convention, `Tp=E1(T[0],T[1])` with trace-zero → `E1(0)`, dlog 0): gives $\sum h_2=2p$, target $f[0]-c=2p$.
- *skip* (`if T.is_zero(): continue`): gives $\sum h_2=n-1$, target $f[0]-c=n-1$.
Both give $c=0$ for $d\neq0$ and hence the **same** identity for all $a\neq0$. This is *not* a discrepancy, but if undocumented it makes a future re-derivation look like a contradiction (it did exactly this during this session — a first implementation appeared to refute the record before the normalization was understood). Recorded here to prevent repetition.

---

## 2. Result — no counterexample

Validated against the record's 160-bit DFT route at p=43,67,127 (agreement to $10^{-45}$ once normalizations match), then swept:

| p | n | frequencies (a≠0) | result |
|---|---|---|---|
| 43 | 31 | 30 | OK |
| 67 | 79 | 78 | OK |
| 79 | 67 | 66 | OK |
| 127 | 127 | 126 | OK |
| 163 | 139 | 138 | OK |
| 211 | 199 | 198 | OK |
| 547 | 547 | 546 | OK |

**7 primes, 1182 (a,p) frequencies, 0 counterexamples.** At every frequency $f[d]=0$ for $d\neq0$ and $f[0]-c=2p$ exactly. The identity $e_2=e_1^2+p$ holds exactly across this range. (The $n$-prime condition on $\#E(\mathbb{F}_p)$ is restrictive — only 7 such primes below 600 in the class $p\equiv7\bmod12$ — which is the same reason the record's 22-prime sweep stops at 547.)

**What this is NOT.** A sweep, not a proof; "no finite sweep can" prove uniformity. The counterexample-hunt came back empty, which is consistent with the separation thesis but does not establish it. Pushing to larger $p$ is bottlenecked by the $O(p^2)$ $E(\mathbb{F}_{p^2})$ enumeration (the record hits the same wall); the small-cofactor auxiliary-curve method (direction B) would extend the range but offers diminishing returns over 7 clean primes.

**Low-order characters (direction-B validity check).** Separately verified that the identity holds for characters $a$ of **low order** (2, 3, 6) at p=43,67,127,547 — errors $\sim10^{-41}$–$10^{-45}$. So the collapse does **not** depend on $a$ having full order; an order-$h$ character lives in the same rank-4 cohomology and satisfies the same collapse. This validates the premise of the small-cofactor extension method (it samples the same law), though $V_2$ for low-order $a$ is *not* polylog-evaluable (the trace-fibers still cost $O(p^2)$) — so the cheap-range-gain claimed for direction B applies to $V_1$ and the `g=deg gcd` route, not to the $V_2$ identity sweep.

---

## 3. Falsifiable prediction of the proposed mechanism — and its refutation

The leading candidate mechanism (parallel-session proposal; recorded in `STRUCTURAL_IMPLICATIONS_2026-07-30_v1.md` §4) was: the $\zeta_3$ in the 120° configuration comes from an endomorphism $T\in\operatorname{End}^0(A_{new})$ that commutes with Frobenius up to a $\zeta_3$ factor over $\mathbb{F}_{p^3}$, i.e. $T\cdot\mathrm{Frob}=\zeta_3\cdot\mathrm{Frob}\cdot T$. Two checks:

**(a) The perfect-square-over-$\mathbb{F}_{p^3}$ prediction — HOLDS, but is not independent evidence.** Cubing the eigenvalues kills $\zeta_3$ ($\zeta_3^3=1$), so the 120° configuration predicts the $A_{new}$ L-polynomial over $\mathbb{F}_{p^3}$ is a perfect square. Verified: for the **untwisted** $a=0$ fibre the four eigenvalues cube to $\{+\alpha^3,+\alpha^3,-\alpha^3,-\alpha^3\}$ (a doubled *real* pair) at p=43,67,127; and for the **full twisted family** (every nonzero $a$) at p=43,67,127 — **234 frequencies, 0 failures.** ⚠ But this is a *consequence* of the 120° configuration (built via the collapse identities), so it is a self-consistency check, **not** independent support for the mechanism.

**(b) The abelian-discriminator — REFUTES the commutative version of the hypothesis.** `anew_eigenvalue_verify_v4.sage` factors the per-$a$ twisted L-polynomial over $\mathbb{Q}(\zeta_{12n})$ and runs the Galois test "$\sigma(D)/D\in(K^\*)^2$ for all $\sigma$" (necessary for the eigenvalue extension to be Galois/abelian over $\mathbb{Q}$), validated against abelian/non-abelian plants:
- **p=13**: both quadratic factors pass — eigenvalue extension *could be abelian*.
- **p=43, p=67**: both quadratic factors **FAIL** (at a specific $\sigma$) — the eigenvalue extension is **non-abelian, not even Galois over $\mathbb{Q}$.**

This is the record's B2.2 finding, now confirmed by direct factorization. **Consequence for the mechanism:** a *commutative* CM endomorphism ring ($\mathbb{Z}[\omega]$, $\mathbb{Q}(\zeta_{12})$) acting on Frobenius would force the eigenvalues into an abelian extension. The non-abelianity at p=43,67 **refutes the commutative-commutation hypothesis** $T\cdot\mathrm{Frob}=\zeta_3\cdot\mathrm{Frob}\cdot T$ for $T$ in a commutative endomorphism ring. (p=13 is the known exception where things are small enough to be abelian; it is not the generic case.)

---

## 4. Honest status of the mechanism question

- **The phenomenon is robust:** 120° law (22 primes, `g=deg gcd`), $e_2=e_1^2+p$ (7 primes / 1182 freqs, exact), perfect-square over $\mathbb{F}_{p^3}$ (234 freqs). All consistent, no counterexample.
- **The proposed *commutative* explanation is refuted** by the non-abelianity at p=43,67. The tensor decomposition $H^1\cong W\oplus(W\otimes\xi)$ remains a *candidate* but, if it holds, the $\xi$-twist does **not** come from a commutative CM endomorphism — it would have to come from a genuinely non-commutative action (e.g. the monodromy group, conjecturally $\mathrm{SL}_2$-on-the-tensor-structure, not a scalar endomorphism).
- **The separation thesis (inertness) is unaffected** by this mechanism question: the thesis rests on the *phenomenon* (uniform rigidity → cap → separation), and a proof of uniform #26 would establish inertness regardless of which mechanism enforces the rigidity. The mechanism is "why is it rigid"; the thesis is "what does the rigidity imply." Refuting one "why" candidate does not touch the "what."

**Net move on the mechanism:** the parallel-session proposal "the $\zeta_3$ lives in $\operatorname{End}^0(A_{new})$ over $\mathbb{F}_{p^3}$ and commutes with Frobenius up to $\zeta_3$" is **downgraded from leading-candidate to refuted (commutative form).** The live mechanism target is the *geometric monodromy* (frontier #28), not a scalar endomorphism. This sharpens, not weakens, the programme: it rules out the easy explanation and points at the structural one.

---

## 5. Files

- `verify_e2_identity_extended_v1.sage` — the float-free convolution verification (this doc).
- `verify_V2_identity_v1.sage` — the record's brute DFT check (3 primes; the "8-10" figure corrected here).
- `freeze_n1_120deg_v1.py` / `RESULT_n1_120deg_exact_v1.json` — the 22-prime 120° law via fast `g=deg gcd` (unaffected, solid).
- `anew_eigenvalue_verify_v4.sage` — the abelian-discriminator (refutes commutative-commutation at p=43,67).
- `ANALYSIS_n1_charpoly_collapse_v1.md` — the collapse derivation (derivation general; verification now 7 primes).
