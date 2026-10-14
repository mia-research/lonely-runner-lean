# Theorems 5.2-SR and 5.2-SR2 — Proofs to verify

## Setup (from v11.8 §5.2)

Let $(n, G, A, p)$ satisfy the hypotheses of Theorem 5.2 with $k_G + k_A = n - 1$ (LRC-shape). Here:
- $n \ge 3$ integer
- $G = \{v_1, ..., v_{k_G}\}$ and $A = \{u_1, ..., u_{k_A}\}$ are sets of distinct positive integers
- $p$ is prime (or positive integer) with $\gcd(p, L_G) = 1$, where $L_G := \mathrm{lcm}(G)$
- Joint witness condition: $t^* \in \mathbb{R}$ satisfies $\|v t^*\| \ge 1/n$ for all $v \in G$ AND $\|u\{p t^*\}\| \ge 1/n$ for all $u \in A$, where $\|x\| := \min(x \bmod 1, 1 - (x \bmod 1))$ is distance-to-nearest-integer

Lemma 2.1 (Fundamental Identity, already in v11.8): For any positive integer $u$ and real $t$, $\|u \{p t\}\| = \|u p t\|$. (Because $u \{pt\} = u(pt - \lfloor pt \rfloor) = upt - u\lfloor pt \rfloor$, and $u \lfloor pt \rfloor \in \mathbb{Z}$.)

Define $W := G \cup pA = G \cup \{p u_1, ..., p u_{k_A}\}$. By Lemma 2.1, the joint witness condition is equivalent to $\|w t^*\| \ge 1/n$ for all $w \in W$. Note $|W| = n - 1$ (distinctness: $\gcd(p, L_G) = 1$ implies $p \nmid v_i$ for $v_i \in G$, so $v_i \ne p u_j$).

---

## Theorem 5.2-SR (Slot-Residue Closure) — claimed UNCONDITIONAL

**Statement.** *Suppose $n \nmid w$ for every $w \in W$. Then for every $s \in \{1, ..., n-1\}$ with $\gcd(s, n) = 1$, the rational $t^* := s/n$ is a joint witness.*

**Proof.** Fix any $s \in \{1, ..., n-1\}$ with $\gcd(s, n) = 1$, so $s$ is a unit in $\mathbb{Z}/n\mathbb{Z}$. By the FI reduction, it suffices to show $\|w t^*\| \ge 1/n$ for all $w \in W$.

For $w \in W$: since $s$ is a unit mod $n$, the map $x \mapsto sx$ is a bijection of $\mathbb{Z}/n\mathbb{Z}$. Hence
$$ws \equiv 0 \pmod{n} \iff w \equiv 0 \pmod{n} \iff n \mid w.$$
By hypothesis $n \nmid w$, so $ws \bmod n \in \{1, 2, ..., n-1\}$. Therefore
$$\|w t^*\| = \|w s / n\| = \frac{\min(ws \bmod n,\ n - (ws \bmod n))}{n} \ge \frac{1}{n}.$$
$\square$

**Remark.** SR generalizes the previously-proved Theorem 5.2-PCL (Coprime Witness, $\gcd(p, n) = 1$ + $n \nmid v$ + $n \nmid u$, witness $t^* = 1/n$) in two ways: it allows $\gcd(p, n) > 1$ (only needs $n \nmid pu$ for $u \in A$), and it produces $\varphi(n)$ candidate witnesses (one per $s$ coprime to $n$). Empirically on the 53 L_residual cases at $n \in \{4,5,6\}$, SR closes 19/53 (35.8%), strictly improving on PCL's 16/53 (30.2%).

---

## Theorem 5.2-SR2 (Lifted Slot-Residue) — n²-lattice extension

**Setup.** When SR's hypothesis fails (some $w \in W$ with $n \mid w$), decompose
- $W_1 := \{w \in W : n \nmid w\}$
- $W_2 := \{w/n : w \in W, \ n \mid w\}$ (positive-integer multiset).

**Statement.** *Suppose $n \nmid w'$ for every $w' \in W_2$ (equivalently, $n^2 \nmid w$ for every $w \in W$ with $n \mid w$). Suppose further that there exist $c \in \{1, ..., n-1\}$ and $k \in \{0, 1, ..., n-1\}$ such that:*
- *(a) $w'c \not\equiv 0 \pmod{n}$ for every $w' \in W_2$;*
- *(b) $\|w(nk + c)/n^2\| \ge 1/n$ for every $w \in W_1$.*

*Then $t^* := (nk + c)/n^2$ is a joint witness.*

**Proof.** By FI it suffices to verify $\|w t^*\| \ge 1/n$ for all $w \in W$.

Case 1: $w \in W_1$, i.e., $n \nmid w$. By (b), $\|w t^*\| = \|w(nk+c)/n^2\| \ge 1/n$. ✓

Case 2: $w \in W$ with $n \mid w$. Write $w = n w'$ with $w' \in W_2$. Then
$$w t^* = n w' (nk + c) / n^2 = w'(nk+c)/n = w' k + w' c / n.$$
Since $w' k \in \mathbb{Z}$, $\|w t^*\| = \|w' c / n\|$. By (a), $w' c \bmod n \in \{1, ..., n-1\}$, so
$$\|w t^*\| = \frac{\min(w' c \bmod n,\ n - (w' c \bmod n))}{n} \ge \frac{1}{n}.$$
$\square$

**Note on (a).** Condition (a) is itself an SR-style condition on $W_2$ (treating $W_2$ as effective speeds mod $n$). By the same argument as Theorem 5.2-SR: a $c \in \{1, ..., n-1\}$ with $\gcd(c, n) = 1$ satisfies (a) iff $n \nmid w'$ for all $w' \in W_2$, which is the standing hypothesis.

**Note on (b).** For each $w \in W_1$, the bad $k$-set at offset $c$ has size at most $2 \gcd(w, n)$ by an explicit modular reduction (Generalized Phase Constraint Lemma, already proved this session for $\gcd(w, n) = 1$, count $= 2$; extends with $\le 2g$ for $\gcd(w, n) = g$). The condition (b) holds iff $\bigcup_{w \in W_1} \mathrm{bad}_k(w, c) \ne \{0, 1, ..., n-1\}$.

**Empirical status.** Across all 34 L_residual SR-failure cases at $n \in \{4, 5, 6\}$ (computer-verified), (a) and (b) both hold; combined coverage SR + SR2 closes 53/53 cases. Analytical proof that (b) holds whenever (a) holds + LRC-shape is the remaining open question.

---

## Specific questions for verification

1. **SR proof rigor**: Does the SR proof have any unstated hypothesis or logical gap?
2. **SR generalization scope**: Is the claim that SR strictly generalizes PCL correct?
3. **SR2 proof rigor**: Are Cases 1, 2 of the SR2 proof logically correct? Is the algebraic step $w t^* = w' k + w' c / n$ valid?
4. **SR2 conditions (a), (b)**: Are these the right conditions, or is there a hidden hypothesis I'm missing?
5. **Lift to higher $n^h$ lattice**: Is there a natural induction: if some $w \in W$ has $n^2 \mid w$, can we lift again to $n^3$ lattice and beyond? Or does the structure break?

Provide a VERDICT (ACCEPT / ACCEPT-WITH-MINORS / REJECT) on the SR proof and the SR2 architecture (excluding the unproven condition (b)), and CONFIDENCE level.
