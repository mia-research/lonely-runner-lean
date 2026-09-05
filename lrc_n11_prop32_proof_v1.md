# Prop 3.2 — Proof Draft (Step 1a, Claude-authored)

## Source

Specialized from `lrc_proof_v7_8_preprint.md` §8 (Theorems 8.2 and 8.3),
specialized to n = 11.

---

## Proposition 3.2

**Proposition 3.2.** If $|E_{\rm div}| \ge 2$, then $x_0(E) \ge 10$.

---

## Proof

Write each $e \in E_{\rm div}$ as $e = 11k$ for a positive integer $k$.
Call $k$ **regular** if $\gcd(k, 11) = 1$ (equivalently $11 \nmid k$) and
**extreme** if $11 \mid k$ (so $e$ is divisible by $121$).

### Regular case: all multipliers are regular

Assume every $e = 11k \in E_{\rm div}$ satisfies $\gcd(k, 11) = 1$.

Consider the ten times $t_j = jL$ for $j = 1, \ldots, 10$.

For any $e_u \in E_{\rm non}$ (so $\gcd(e_u, 11) = 1$):
$$e_u \cdot t_j \bmod 11L = L \cdot (e_u j \bmod 11).$$
Since $\gcd(e_u, 11) = 1$ and $j \in \{1, \ldots, 10\}$, the residue
$e_u j \bmod 11 \in \{1, \ldots, 10\}$, so $e_u t_j \bmod 11L \in [L, 10L]$. ✓

For any $e = 11k \in E_{\rm div}$ with $k$ regular:
$$e \cdot t_j \bmod 11L = L \cdot (kj \bmod 11).$$
Since $\gcd(k, 11) = 1$ and $j \in \{1, \ldots, 10\}$, the residue
$kj \bmod 11 \in \{1, \ldots, 10\}$, so $e t_j \bmod 11L \in [L, 10L]$. ✓

Hence all ten $t_j$ are safe, giving $x_0(E) \ge 10 = \varphi(11)$. $\square$

**Remark**: This case covers all configurations where $E_{\rm div} \subseteq \{11, 22, 33, 44, 55, 66, 77, 88, 99, 110, 154, \ldots\}$ — i.e., no divisible speed is divisible by $121$.

---

### Extreme case: at least one multiplier is extreme

Assume some $e_0 = 11k_0 \in E_{\rm div}$ with $11 \mid k_0$ (so $121 \mid e_0$).

**Step 1: Bad-set structure of an extreme runner.**

For $e_0 = 11k_0$ with $\gcd(e_0, 11) = 11$, we have $e_0 r \equiv 0 \pmod{11}$
for all $r$. Hence the solution set $\mathrm{Sol}(e_0, j, 11) = \mathbb{Z}_{11}$
if $11 \mid j$, and $= \emptyset$ otherwise. The bad set at floor value $t$ is:
$$\mathrm{bad}(e_0, t, 11) =
\begin{cases}
\mathbb{Z}_{11} & \text{if } 11 \mid t \text{ or } 11 \mid (t+1), \\
\emptyset & \text{otherwise.}
\end{cases}$$
So $e_0$ is either *fully opaque* (covers all residues) or *completely transparent*
at each fibre; it is transparent at the majority of fibres.

**Step 2: Non-exceptional fibre count for $n = 11$.**

On the interval $B_{\rm div} = [L/11, 10L/11]$, the floor value
$t = \lfloor e_0 b / L \rfloor$ ranges over integers from
$\lfloor k_0 \rfloor = k_0$ to $\lfloor 10 k_0 \rfloor = 10k_0$.
(Here we use $e_0 = 11k_0$, so $e_0 b / L = 11k_0 b / L$ and at
$b = L/11$: $t = k_0$; at $b = 10L/11$: $t = 10k_0$.)

The number of floor values in $\{k_0, \ldots, 10k_0\}$ satisfying
$t \equiv 0$ or $t \equiv -1 \pmod{11}$ is at most $2 \cdot \lceil 9k_0/11 \rceil \le 2(k_0 + 1)$.

Each floor value corresponds to at most $\lceil L/e_0 \rceil$ fibres.
The total count of fibres where $e_0$ is non-transparent (opaque) is therefore
at most $2(k_0+1) \cdot \lceil L/e_0 \rceil = 2(k_0+1) \cdot \lceil L/(11k_0) \rceil$.

A cleaner bound: the opaque fibres number at most $2(n-1) = 20$ per **period**
of length $L/k_0$ within $B_{\rm div}$. For $k_0 \ge 11$ (which holds since
$11 \mid k_0$ and $k_0 \ge 1$ implies $k_0 \ge 11$), we have
$|B_{\rm div}| \ge 9L/11 \ge 9 \cdot 121/11 = 99$, and the number of non-exceptional
fibres is at least
$$|B_{\rm div}| - 2(n-1) \cdot |E_{\rm div}|_{\rm ext}
\ge 99 - 20 \cdot |E_{\rm div}|_{\rm ext},$$
where $|E_{\rm div}|_{\rm ext}$ counts extreme runners.

If $|E_{\rm div}|_{\rm ext} \le 4$, this gives $\ge 99 - 80 = 19 > n-1 = 10$.
For larger $|E_{\rm div}|_{\rm ext}$, the presence of more extreme runners forces
$L$ to grow (since distinct extreme speeds require $L \ge \mathrm{lcm}(e_i)$),
making $|B_{\rm div}|$ correspondingly larger. Concretely:
- $|E_{\rm div}|_{\rm ext} = m$ distinct extreme speeds $\ge 121$ have
  $\mathrm{lcm} \ge 121m$, so $L \ge 121m$ and $|B_{\rm div}| \ge 99m$;
- Non-exceptional fibres $\ge 99m - 20m = 79m \ge 10$ for $m \ge 1$.

Thus in all sub-cases, the non-exceptional fibre count is $\ge 10 = n-1$.

**Step 3: Counting bridge on non-exceptional fibres.**

On each non-exceptional fibre $b$, all extreme divisible runners are transparent
(bad set $= \emptyset$) and all regular divisible runners are transparent by
Lemma 8.1 of the companion analysis (since $\gcd(k, 11) = 1$ for regular runners).
Thus all divisible runners contribute no coverage, and the safe/unsafe condition
at fibre $b$ is determined solely by $E_{\rm non}$.

With $|E_{\rm non}| \le 8 = n - 3$ non-divisible runners, the total
non-exceptional fibre count $\ge 79$ and the prime lower-band counting
bridge for $n = 11$ prime with at most $n - 3$ non-divisible runners
yields $x_0(E) \ge \varphi(11) = 10$.

(The counting bridge step: at each non-exceptional fibre $b$, the coverage
of $\mathbb{Z}_{11}$ by $|E_{\rm non}| \le 8$ runners — each covering exactly
2 residues — leaves at least $11 - 2 \cdot |E_{\rm non}|$ residues uncovered
in expectation. However, for prime $p = 11$ and at most $p - 3$ runners,
the exact count via Fourier analysis on $\mathbb{Z}_p$ gives the precise
bound $x_0 \ge n - 1$; see Proposition 10.5 of the companion $n{=}\text{all}$
analysis for the full argument, which specializes to $x_0 \ge 10$ at $n = 11$.) $\square$

---

## Auditor Checkpoint

**Decision**: **Modifying — partial only.**

The REGULAR CASE proof is complete and self-contained. ✅

The EXTREME CASE proof gives the correct structure (bad-set dichotomy, non-exceptional
fibre count ≥ 10) but the counting bridge step (Step 3) is not fully self-contained
— it defers to Prop 10.5 of the companion.

**Options for v3 integration**:
1. Include as-is with the companion citation (honest, concise).
2. Add a self-contained Appendix A proving the counting bridge for n=11 specifically.
3. Restructure: prove the extreme case computationally via the existing 45-template certificate (since all extreme-case configurations are covered by the computational certificate in §6).

**Recommended approach for v3**: Option 3. The computational certificate in §6 covers ALL 45 templates across all M values including extreme configurations. Cite it for the extreme case and note that the analytic argument above gives the structure. This keeps the paper short and honest.

**DeepSeek verification needed**: Have DeepSeek `--task verify` check the non-exceptional fibre count calculation (Step 2) specifically: is "79m ≥ 10 for m ≥ 1" correct? And is the lcm bound "lcm ≥ 121m" for m distinct extreme speeds correct?
