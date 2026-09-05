# Adversarial review request

You are a **hostile** referee reviewing a candidate proof of the **Lonely Runner Conjecture (LRC)** for publication. Find every flaw, gap, circularity, and undefended claim. If there are no genuine issues, say so — but do not invent problems, and do not grant the benefit of the doubt.

## LRC statement

For $n \ge 3$ and distinct positive integers $v_1,\dots,v_{n-1}$, there exists $t \ge 0$ such that $\|t v_i\| \ge 1/n$ for all $i$ (where $\|\cdot\|$ denotes distance to nearest integer).

## Reduction (stated, not proved)

After irrationality reduction (Thm 3.1 via Weyl) and integer scaling with $\gcd = 1$, set $L := \operatorname{lcm}(e_1,\dots,e_{n-1})$, $N := nL$. Then LRC $\iff$ $x_0(E) \ge 1$ where
$$x_0(E) := \#\{k \in \{1,\dots,N-1\} : (e_i k \bmod N) \in [L, (n-1)L] \text{ for all } i\}.$$
Partition $E = E_{\mathrm{non}} \sqcup E_{\mathrm{div}}$. $R_{\mathrm{non}}$ = residues mod $n$ of $E_{\mathrm{non}}$. $B_{\mathrm{div}} := [L/n, (n-1)L/n] \cap \mathbb{Z}$.

## Proof structure (your target)

The proof assembles 6 branches:
- Case 1: $E_{\mathrm{div}} = \emptyset$ → Thm 4.1 gives $x_0 \ge \varphi(n)$ via witnesses $k_j = jL$, $\gcd(j,n)=1$.
- Prime $n$, $|E_{\mathrm{div}}|=1$ → Lemma 5.2 (absent-unit covering) via base-fibre + sliding-window chain (Prop 6.1).
- Prime $n$, $|E_{\mathrm{div}}|\ge 2$ → Thm 8.2 (regular $k$) or Thm 8.3 (extreme $k$), both via transparency (Lemma 8.1) and Lemma 5.2.
- Composite $n$, $|E_{\mathrm{div}}|=1$, unit absent → Prop 10.1 via late-window Lemma 10.2 (residue $s_d = d^{-1}-1$ uncovered on $J = [(n-2)L/(n-1), (n-1)L/n]$).
- Composite $n$, non-units absent → Lemma 9.4 + Thm 9.2c (floor-reset CG1/CG2 analysis).
- Composite $n$, $|E_{\mathrm{div}}|\ge 2$ → Thm 11.1 via Lemma 10.2 + Lemma 11.A + Thm 9.2c.

## Proof body

[Full text of lrc_proof_v11_1.md follows. Identify the weakest 3 claims. For each, name the lemma/theorem, state the specific flaw, and estimate severity (low/med/high). If all pass, output "NO-ISSUES".]

---

PROOF_BODY_MARKER_BEGIN

