# Theorem 8.2c — Non-Unit Runner Gap: Full Analytic Closure
**Date:** 2026-03-12
**Status:** GAP CLOSED

---

## 1. The Question

At fibre $b_m = mL/e_u$ (the Theorem 8.2c targeted event), can any **retained non-unit runner** $e' \in E_{\rm fix}$ with $g = \gcd(e', n) > 1$ cover the departing residue $r_{\rm dep} = -(m-1)e_u^{-1} \bmod n$?

The audit identified that Lemma 8.2a (and hence the proof of Theorem 8.2c) was stated only for unit runners $e'$, leaving non-unit runners unaddressed.

---

## 2. Re-Derivation from First Principles (No Assumption on $\gcd(e', n)$)

Let $e' \in \{1,\ldots,n-1\}$ be **any** runner, unit or non-unit. Set $t_{e'} = \lfloor e'm/e_u \rfloor$ and $s = e'm \bmod e_u \in \{0, \ldots, e_u-1\}$, so $t_{e'} = (e'm - s)/e_u$.

**Coverage via $-t_{e'}$:** $r_{\rm dep} \in \mathrm{Sol}(e', -t_{e'}, n)$ iff

$$e' \cdot r_{\rm dep} \equiv -t_{e'} \pmod{n}.$$

Substitute $r_{\rm dep} = -(m-1)e_u^{-1}$:

$$-e'(m-1)e_u^{-1} \equiv -t_{e'} \pmod{n}$$
$$e'(m-1)e_u^{-1} \equiv t_{e'} \pmod{n}$$

Multiply both sides by $e_u$ (invertible mod $n$ since $\gcd(e_u,n)=1$):

$$e'(m-1) \equiv e_u \cdot t_{e'} \pmod{n}$$
$$e'(m-1) \equiv e_u \cdot \frac{e'm - s}{e_u} \pmod{n}$$
$$e'(m-1) \equiv e'm - s \pmod{n}$$
$$-e' \equiv -s \pmod{n}$$
$$s \equiv e' \pmod{n}.$$

Since both $s \in \{0,\ldots,e_u-1\} \subset \{0,\ldots,n-1\}$ and $e' \in \{1,\ldots,n-1\}$, congruence mod $n$ forces **exact equality**:

$$\boxed{s = e'.}$$

This is **Cond 1** of Lemma 8.2a. **The derivation used no property of $\gcd(e',n)$. It holds for all $e'$.**

**Coverage via $-(t_{e'}+1)$:** $r_{\rm dep} \in \mathrm{Sol}(e', -(t_{e'}+1), n)$ iff $e' r_{\rm dep} \equiv -(t_{e'}+1) \pmod{n}$. By the same steps:

$$e'(m-1) \equiv e_u(t_{e'}+1) \pmod{n}$$
$$-e' \equiv -s + e_u \pmod{n}$$
$$s \equiv e' + e_u \pmod{n}.$$

Since $s < e_u$ and $e' + e_u \geq e_u$: this has solutions only when $e' + e_u \geq n$, giving $s = e' + e_u - n$. This is **Cond 2** of Lemma 8.2a. **Again, $\gcd(e',n)$ plays no role.**

---

## 3. What This Means

> **Lemma 8.2a (Extended).** *At the $m$-th z=0 event of unit $e_u$, **any** runner $e' \in \{1,\ldots,n-1\}$ covers $r_{\rm dep} = -(m-1)e_u^{-1}$ if and only if:*
> - *(Cond 1)* $e'm \bmod e_u = e'$ (requires $e' < e_u$), or
> - *(Cond 2)* $e'm \bmod e_u = e' + e_u - n$ (requires $e' + e_u \geq n$).

The "unit runner" qualifier in the original Lemma 8.2a statement is an **unnecessary restriction**. The algebraic derivation is valid for all $e' \in \{1,\ldots,n-1\}$.

---

## 4. Theorem 8.2c is Now Complete for All Runners

The existing proof of Theorem 8.2c already establishes:

**No Cond 1 coverer exists for any $e'$:**
Cond 1 requires $e'(m-1) \equiv 0 \pmod{e_u}$ (from $s = e'$, combined with $s = e'm - e_u\lfloor e'm/e_u\rfloor$... actually from Cond 1: $e'm \bmod e_u = e'$, i.e., $e'(m-1) \equiv 0 \pmod{e_u}$). Since $\gcd(m-1, e_u) = 1$ (established in the Theorem 8.2c proof), this forces $e_u \mid e'$. But Cond 1 also requires $e' < e_u$, so $e' = 0$, which is impossible for $e' \in \{1,\ldots,n-1\}$. **Hence Cond 1 is impossible for every runner $e'$, unit or non-unit.**

**The unique Cond 2 runner is $d \notin E_{\rm fix}$:**
Cond 2 gives $e' \equiv d \pmod{e_u}$ with $e' \in [n-e_u, n-1] = [u, n-1]$, an interval of exactly $e_u$ consecutive integers. Since $d \in [u, n-1]$ (as $d = au \geq u$ for $a \geq 1$) and both $d - e_u < u$ and $d + e_u > n-1$ (both verified in the original proof), the unique solution is $e' = d$. Since $d \notin E_{\rm fix}$, **no retained runner — unit or non-unit — satisfies Cond 2.**

**Conclusion:** No retained runner covers $r_{\rm dep}$ at $b_m$, for any runner type. The Tier 1 claim of Theorem 8.2c is complete.

---

## 5. What Changes in the Proof Document

**Lemma 8.2a:** Remove the qualifier "unit runner $e'$." The statement and proof hold for all $e' \in \{1,\ldots,n-1\}$.

**Theorem 8.2c:** No structural change needed. The phrase "the departing residue is uncovered by all retained runners" is now justified by the extended Lemma 8.2a, which covers all runner types.

**This is not a new branch.** It is a recognition that the existing algebraic mechanism already covers non-unit runners — the original statement was just stated more narrowly than necessary.

---

## 6. Why the Gap Appeared (and What It Tells Us)

The Cond 1/Cond 2 conditions are usually introduced in the context of unit runners because unit bad sets are 2-element sets $\{-te^{-1}, -(t+1)e^{-1}\}$, which makes it natural to ask "which 2 residues does $e'$ cover?" For non-unit $e'$, the bad set is a coset of size $g > 1$, so the question becomes "does the coset contain $r_{\rm dep}$?" — which looks different but resolves to the same congruence condition.

The deeper reason both cases give the same Cond 1/Cond 2: the coverage condition $e'r_{\rm dep} \equiv -t$ is a **modular equation in $r_{\rm dep}$**, and the structure of the bad set (2 elements vs. coset) only affects how many values of $r_{\rm dep}$ are covered, not the algebraic form of the condition **for the specific $r_{\rm dep}$ we're testing**. Since we're asking about one specific $r_{\rm dep}$, the coset size is irrelevant.

---

## 7. Cross-Check on n=15, d=10

Settings: $n=15$, $d=10$, $u=2$, $e_u=13$, $m=6$, $r_{\rm dep}=10$, $s$-values:

| Runner $e'$ | $s = e'm \bmod 13$ | Cond 1 ($s=e'$?) | Cond 2 ($s=e'+13-15=e'-2$?) | Covers $r_{\rm dep}$? |
|---|---|---|---|---|
| 3 (non-unit) | $18 \bmod 13 = 5$ | $5=3$? No | $5=1$? No | No ✓ |
| 5 (non-unit) | $30 \bmod 13 = 4$ | $4=5$? No | $4=3$? No | No ✓ |
| 6 (non-unit) | $36 \bmod 13 = 10$ | $10=6$? No | $10=4$? No | No ✓ |
| 9 (non-unit) | $54 \bmod 13 = 2$ | $2=9$? No | $2=7$? No | No ✓ |
| 10 (dropped, $d$) | $60 \bmod 13 = 8$ | $8=10$? No | $8=8$? **YES** | Would cover — but $d \notin E_{\rm fix}$ ✓ |

The table confirms: the unique Cond 2 runner is $d=10$ itself (the dropped runner), and every other runner fails both conditions. Fully consistent with the extended Lemma 8.2a.
