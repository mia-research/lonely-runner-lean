# Adversarial review — §§7, 8, 11, 12 of lrc_proof_v11_1.md

You are a hostile referee. Find every flaw. Do not grant benefit of the doubt; do not invent problems.

## Setup (brief)

LRC Tier-1 claim: $x_0(E) \ge 1$ for all $n \ge 3$, distinct positive speeds with $\gcd = 1$. $L = \operatorname{lcm}(E)$, $N = nL$. Partition $E = E_{\mathrm{non}} \sqcup E_{\mathrm{div}}$ (divisible = multiples of $n$).

## Target sections

### §7 Prime $n$, one divisible runner

**Theorem 7.1.** *Prime $n$, $|E_{\mathrm{div}}|=1$, $|E_{\mathrm{non}}|=n-2$. Then $x_0(E) \ge 1$.*

Proof: $|R_{\mathrm{non}}| \le n-2 < n-1$, so some $d \in \{1,\ldots,n-1\}$ absent. Prime $n \Rightarrow$ every nonzero residue is a unit; $d$ is a unit. Apply Lemma 5.2. $\square$

### §8 Prime $n$, multiple divisible runners

**Lemma 8.1.** *Prime $n$, $e = kn \in E_{\mathrm{div}}$, $k \in \{1,\ldots,n-2\}$. Then $\mathrm{bad}(kn, \lfloor knb/L\rfloor, n) = \emptyset$ for $b \in [L/n, L/(n-1))$.*

Proof: $\gcd(kn, n) = n$, so Sol $= \mathbb{Z}/n\mathbb{Z}$ iff $n \mid j$, else empty. At $b$ in the interval, floor $= k$. Since $k \in \{1,\ldots,n-2\}$, neither $-k$ nor $-(k+1)$ is a multiple of $n$; bad $= \emptyset$.

**Theorem 8.2 (regular $k$).** *Prime $n$, $|E_{\mathrm{div}}| \ge 2$, every $k$ with $kn \in E_{\mathrm{div}}$ has $k \in \{1,\ldots,n-2\}$. Then $x_0(E) \ge 1$.*

Proof: on $I = [L/n, L/(n-1))$, every divisible transparent by Lemma 8.1. Only $|E_{\mathrm{non}}| \le n-3$ non-divisibles contribute, each a 2-residue bad set, total $\le 2(n-3) = 2n-6 < 2n$. Some residue uncovered on $I$.

**Theorem 8.3 (extreme $k$).** *Prime $n$, $|E_{\mathrm{div}}| \ge 2$, some $e_d = kn$ has $k \equiv 0$ or $k \equiv -1 \pmod n$. Then $x_0(E) \ge 1$.*

Proof: bad $\ne \emptyset$ only at floors $t$ with $n \mid t$ or $n \mid t+1$; sparse. On transparent fibres of $e_d$: if $|E_{\mathrm{div}}| \ge 3$, apply Thm 8.2 to reduced tuple. If $|E_{\mathrm{div}}| = 2$, the other divisible $e_d'$ is regular ($k' \in \{1,\ldots,n-2\}$) else both extreme and $L$ bounded by $n(n-1) \le 2n$ (only for $n \le 3$, vacuous). Reduced tuple has $\le n-3$ non-divisibles, unit $d$ absent, Lemma 5.2.

### §11.2 Composite, $|E_{\mathrm{div}}| \ge 2$

**Theorem 11.1.** *Composite $n \ge 4$, $|E_{\mathrm{div}}| \ge 2$. Then $x_0 \ge 1$.*

Case A (unit absent): use late-window Lemma 10.2 to get residue-safe $b \in J$ with $[b]_n \equiv s_d$, plus divisible-safety via counting argument.

Case B (both absent non-units): Lemma 9.4 (Unit-Complete) + Theorem 9.2c produces $m$ with uncovered $r_{\mathrm{dep}}$; chamber to the right of $b_m$ has width $\ge L/((n-1)e_u) \ge 1$, contains integer $b$ with $[b]_n \equiv r_{\mathrm{dep}}$ (possibly translating by $n$); divisible-safety via same counting as Case A.

### §12 Assembly

**Theorem A.** For $n \ge 3$, $\gcd = 1$ tuple $E$ of distinct positive integers: $x_0(E) \ge 1$.

Proof dispatch:
- All speeds rational (Thm 3.1) → integer.
- $E_{\mathrm{div}} = \emptyset$ → Thm 4.1, $x_0 \ge \varphi(n) \ge 1$.
- $L \in \{n, 2n\}$ → Prop 5.1.
- $L > 2n$, prime $n$, $|E_{\mathrm{div}}|=1$ → Thm 7.1.
- $L > 2n$, prime $n$, $|E_{\mathrm{div}}| \ge 2$, all regular → Thm 8.2.
- $L > 2n$, prime $n$, $|E_{\mathrm{div}}| \ge 2$, extreme → Thm 8.3.
- $L > 2n$, composite $n$, $|E_{\mathrm{div}}|=1$, unit absent → Prop 10.1.
- $L > 2n$, composite $n$, $|E_{\mathrm{div}}|=1$, non-unit absent, at least one other absent class is unit → Prop 10.1 to that unit.
- $L > 2n$, composite $n$, $|E_{\mathrm{div}}|=1$, both absent classes non-unit → Lemma 9.4 + Thm 9.2c (via Thm 9.3).
- $L > 2n$, composite $n$, $|E_{\mathrm{div}}| \ge 2$ → Thm 11.1.

## Adversarial questions

1. **Thm 7.1 coverage hypothesis.** The premise is "$|E_{\mathrm{non}}| = n - 2$". What if $|E_{\mathrm{non}}| < n - 2$, i.e., $|E_{\mathrm{div}}| \ge 2$? Then §8 applies; is there a case where $|E_{\mathrm{non}}| = n - 2$ exactly is the binding constraint? Also: Lemma 5.2 is only for prime $n$; Thm 7.1 verifies prime explicitly. Fine.

2. **Lemma 8.1 interval check.** The floor $= k$ claim says: at $b \in [L/n, L/(n-1))$, $\lfloor knb/L\rfloor = k$. Verify: $knb/L \ge k \cdot n/n = k$ and $< k \cdot n/(n-1)$. Is $kn/(n-1) < k+1$? Equivalent to $kn < (k+1)(n-1) = kn + n - k - 1$, i.e., $0 < n - k - 1$, i.e., $k < n - 1$, i.e., $k \le n - 2$. ✓ Fine, but is $[L/n, L/(n-1))$ always nonempty as an **integer** set? Width $= L/(n(n-1))$; nonempty integer set requires $L \ge n(n-1)$, which requires $|E_{\mathrm{div}}| \ge 2$. Yes.

3. **Thm 8.2 pigeonhole.** Total bad incidence $\le 2(n-3) = 2n-6$. $n$ residues; average multiplicity $\le 2 - 6/n$. Thus some residue has multiplicity $\le \lfloor 2 - 6/n\rfloor \le 1$. Actually the argument needs $< 2n$ total so at least one residue has multiplicity $0$, not just $\le 1$. Verify: if all residues had multiplicity $\ge 1$, need $\ge n$. Indeed $2n-6 < n$ requires $n < 6$. So the argument works for $n \ge 7$? **Flag: the argument claims "some residue uncovered" from $\le 2n-6 < 2n$, but this only rules out the "all mult $\ge 2$" case, not the "all mult $\ge 1$" case.** For some residue to be *uncovered* (mult 0), we need total $< n$, i.e., $2n - 6 < n \iff n < 6$. **This looks like a potential gap.** Double-check: is the pigeonhole argument actually producing uncovered, or just thin?

4. **Thm 8.3 "$L$ bounded by $n(n-1) \le 2n$" claim.** When are both divisibles extreme? That would need $k_1 \equiv 0$ and $k_2 \equiv 0$ or $k_1 \equiv 0, k_2 \equiv -1$, etc. Extreme $k \equiv 0 \pmod n$ means speed $= kn$ with $n \mid k$, i.e., $n^2 \mid $ speed. Is this possible alongside $\operatorname{lcm}(E) = L$? The claim "both extreme ⇒ $L \le 2n$ ⇒ Prop 5.1" requires scrutiny. Verify concrete small-$n$ cases.

5. **Thm 11.1 Case B chamber.** The chamber "to the right of $b_m$" has width $\ge L/((n-1)e_u)$; for $e_u$ possibly as large as $n-2$, this is $\ge L/((n-1)(n-2))$. For the chamber to contain an integer with given residue mod $n$, the width must be $\ge n$. That requires $L \ge n(n-1)(n-2)$, which is $\approx n^3$. Is this ensured? The "possibly after translating by $n$" parenthetical admits a potential issue. Verify.

6. **Thm 11.1 Case A divisible-safety counting.** Uses "fraction $\le 2(n-2)/n$ of $J_{s_d}$ unsafe"; for $n \ge 4$, $2(n-2)/n = 2 - 4/n$; for $n = 4$ this is $1.0$ (100%)! So the counting argument **fails for $n = 4$**. For $n = 5$, $6/5 = 1.2 > 1$ — also fails. Only for $n \ge 6$ is this $< 2$. And for the count to be useful we need $< 1$: $2(n-2)/n < 1 \iff n < 4$, never. So the fraction argument is "$\le 2$" not "$\le 1$"; the proof says "excludes a fraction $\le 2(n-2)/n + o(1) < 2$, so at least $|J_{s_d}| - 2(n-2)/n \cdot |J_{s_d}|$ fibres remain", which is **negative for $n \le 4$**. **Potential major gap for small $n$.**

7. **§12 dispatch completeness.** For $L > 2n$, composite $n$, $|E_{\mathrm{div}}|=1$, non-unit $d_1$ absent, the other absent class $d_2$ could be: (a) another non-unit, or (b) a unit. Is the case "only one non-unit absent and no other class absent" possible? Each tuple has $n-1-|E_{\mathrm{div}}|$ non-divisibles. With $|E_{\mathrm{div}}|=1$, $|E_{\mathrm{non}}| = n - 2$, so $|R_{\mathrm{non}}| \le n-2$, hence **at least one** class absent. Could be exactly one. If $|R_{\mathrm{non}}| = n - 2$ and the single absent class is non-unit: Thm 9.2c applies directly via Thm 9.3 ("Unit-Complete"). Fine.

Output format:
```
VERDICT: ACCEPT | ACCEPT-WITH-MINORS | REJECT
SCORE (0–100):
TOP-3 ISSUES: (lemma, flaw, severity high|med|low, can-be-patched? yes|no)
```
