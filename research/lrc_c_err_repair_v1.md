# Lineage C Error Repairs: ERR-C-01 and ERR-C-02

**Date:** 2026-04-19
**Status:** REPAIR DRAFT
**Scope:** `lrc_proof_v10_12.md` — Lemma 11.3a (ERR-C-01) and Theorem 9.2c (ERR-C-02).

---

## Part 1 — ERR-C-01: Lemma 11.3a Floor Formula (Actual-Speed Lift)

### The defect

Lemma 11.3a claims that for composite $n \geq 4$ with dropped unit $d$ and $s_d := d^{-1}-1$, the residue $s_d$ is uncovered at every fibre $b \in J \cap \mathbb{Z}$, where $J = [(n-2)L/(n-1),\,(n-1)L/n]$.

The proof uses: "for any retained runner $e \in \{1,\ldots,n-1\}$ and $b \in J$: $\lfloor eb/L\rfloor = e-1$."

**This is wrong in two ways:**

**(A) Divisible runners $e = kn$ with $k=1$.**
At $b^* = (n-1)L/n$: $\lfloor n b^*/L \rfloor = \lfloor n(n-1)/n \rfloor = n-1$.
The bad-set: $\mathrm{bad}(n, n-1, n) = \mathrm{Sol}(n, -(n-1), n) \cup \mathrm{Sol}(n, -n, n) = \emptyset \cup \mathbb{Z}/n\mathbb{Z} = \mathbb{Z}/n\mathbb{Z}$.
Every residue is blocked, including $s_d$. The proof's non-unit argument claims $s_d \notin H_g - 1$ because $d^{-1} \notin H_g$, but for $g = n$: $H_n = \mathbb{Z}/n\mathbb{Z}$ contains every element (including units), so the argument fails.

**(B) Non-divisible runners $e = nq_e + \rho_e$ with $q_e \geq 1$.**
At $b^* = (n-1)L/n$:
$$\left\lfloor \frac{e(n-1)L/n}{L}\right\rfloor = \left\lfloor \frac{e(n-1)}{n}\right\rfloor = (n-1)q_e + \lfloor \rho_e(n-1)/n \rfloor = (n-1)q_e + \rho_e - 1 = e - q_e - 1,$$
using $\lfloor \rho_e(n-1)/n \rfloor = \rho_e - 1$ (since $\rho_e < n$ so $\rho_e/n < 1$). For $q_e \geq 1$ this gives $e - q_e - 1 \neq e - 1$.

The correct bad-set for unit runner $e = nq_e + \rho_e$ ($q_e \geq 0$, $\gcd(\rho_e,n)=1$) at $b^*$ is:
$$\mathrm{bad}(e, e-q_e-1, n) = \{(q_e+1)\rho_e^{-1}-1,\; q_e\rho_e^{-1}-1\} \pmod n.$$
For $q_e=0$: $\{{\rho_e^{-1}-1},\, n-1\} = \{s_{\rho_e},\, n-1\}$. ✓ (matches original Lemma 11.3a)
For $q_e=1$: $\{2\rho_e^{-1}-1,\, \rho_e^{-1}-1\}$.
For general $q_e$: the element $q_e\rho_e^{-1}-1$ equals $s_d = d^{-1}-1$ iff $q_e\rho_e^{-1} \equiv d^{-1} \pmod n$, i.e., $d \equiv \rho_e/q_e \pmod n$ — a genuine constraint not automatically excluded.

### Correct floor formula

**Lemma 11.3a-corrected (Floor at $b^*$ for actual speeds).**
For $b^* = (n-1)L/n$ and runner $e = nq_e + \rho_e$ ($1 \leq \rho_e \leq n-1$):
$$T_e(b^*) = \lfloor e b^*/L \rfloor = (n-1)q_e + \rho_e - 1 = e - q_e - 1.$$
For $q_e = 0$ (actual speed $< n$): $T_e(b^*) = e - 1$. ✓
For $q_e \geq 1$ (actual speed $\geq n$): $T_e(b^*) = e - q_e - 1 < e - 1$.

### Repair by floor-reset avoidance for divisible runners

**Key observation.** For the divisible runner $e = kn$ with $k = 1$ (the smallest), the bad-set is $\mathbb{Z}/n\mathbb{Z}$ at $b = b^*$ but **empty** at $b = b^* - 1$:

At $b = b^* - 1 = (n-1)L/n - 1$, the floor of runner $n$ is:
$$\left\lfloor \frac{n(b^*-1)}{L} \right\rfloor = \left\lfloor n-1 - \frac{n}{L} \right\rfloor = n - 2 \quad (\text{since } L \geq 2n \Rightarrow n/L \leq 1/2 < 1).$$
At floor $n-2$: $\mathrm{bad}(n, n-2, n)$. Here $-(n-2) \equiv 2 \pmod n$ and $-(n-1) \equiv 1 \pmod n$. For $e = n$ (divisible): $\mathrm{Sol}(n, 2, n) = \emptyset$ (since $n \nmid 2$ for $n \geq 3$) and $\mathrm{Sol}(n, 1, n) = \emptyset$. Thus $\mathrm{bad}(n, n-2, n) = \emptyset$. ✓

More generally, for divisible runner $e = kn$: the floor jumps to $k(n-1)$ at $b^* = (n-1)L/n$ (a floor-reset event of $e$). For $b$ just to the LEFT of this reset:
$$\mathrm{bad}(kn, k(n-1)-1, n): \quad -(k(n-1)-1) = -kn+k+1 \equiv k+1 \pmod n.$$
$\mathrm{Sol}(kn, k+1, n)$: since $n \mid kn$ and $n \nmid k+1$ (for $k \not\equiv -1 \pmod n$): $\mathrm{Sol} = \emptyset$.
Similarly for $-(k(n-1))$: $\equiv k \pmod n$; $\mathrm{Sol}(kn, k, n) = \emptyset$ unless $n \mid k$.

**Summary:** For divisible runners not at their floor-reset event, bad-set $= \emptyset$ for most $k$.

### Repaired proof strategy

**Lemma 11.3a' (Corrected for composite $n \geq 4$, $|E_{\rm div}|=1$).**

Let $e_{\rm div} = kn \in E_{\rm div}$ be the sole divisible runner.

**Case I: $b^*$ is not a floor-reset of $e_{\rm div}$.** Equivalently $k(n-1) \not\equiv 0,\,-1 \pmod n$ (i.e., $k \not\equiv 0,1 \pmod n$). Then $\mathrm{bad}(e_{\rm div}, T_{e_{\rm div}}(b^*), n) = \emptyset$, and the divisible runner does not cover $s_d$ at $b^*$. The original non-divisible runner argument (using $T_e(b^*) = e-1$ for $q_e = 0$ runners) goes through unchanged. For $q_e \geq 1$ non-divisible runners, use the corrected formula $T_e(b^*) = e-q_e-1$; $s_d$ is not covered iff $(q_e+1)\rho_e^{-1} \not\equiv d^{-1}$ and $q_e\rho_e^{-1} \not\equiv d^{-1} \pmod n$ for each retained unit runner $e$, i.e., $d \not\equiv \rho_e/(q_e+1)$ and $d \not\equiv \rho_e/q_e \pmod n$ for each retained runner.

**Case II: $k \equiv 1 \pmod n$ (so $k = 1, n+1, \ldots$; most common case $k=1$, $e_{\rm div} = n$).** At $b^*$: bad$(e_{\rm div}) = \mathbb{Z}/n\mathbb{Z}$. **Use $\hat{b} = b^* - 1$ as the witness instead.**

At $\hat{b} = (n-1)L/n - 1$:
- Divisible runner: bad $= \emptyset$ (computed above). ✓
- Unit runners with $q_e = 0$ (actual speed $< n$): $T_e(\hat{b}) = \lfloor e(b^*-1)/L \rfloor$. We need to verify this equals $e-1$. Since $e(b^*-1)/L = e(n-1)/n - e/L$, and $e \leq n-1$, $L \geq n(n-1)$: $e/L \leq (n-1)/(n(n-1)) = 1/n < 1$. The fractional part of $e(n-1)/n$ is $1 - e/n \in (0,1)$, so $e(b^*-1)/L$ has fractional part $(1-e/n) - e/L > 0$ iff $e/L < 1 - e/n$, i.e., $e(1/n + 1/L) < 1$. For $e \leq n-1$ and $L \geq n(n-1)$: $e(1/n + 1/L) \leq (n-1)(1/n + 1/(n(n-1))) = (n-1)/n + 1/n = 1$. Equality holds when $e = n-1$ and $L = n(n-1)$ — handle this boundary separately (see below). For $L > n(n-1)$ or $e < n-1$: strict inequality holds, so $T_e(\hat{b}) = e-1$. ✓
- The bad-set argument for unit runners at floor $e-1$: unchanged from original Lemma 11.3a. $s_d$ is uncovered. ✓

**Boundary case $L = n(n-1)$, $e = n-1$:** At $\hat{b} = (n-1)^2 - 1$: $T_{n-1}(\hat{b}) = \lfloor (n-1)^2/n - 1 \rfloor = \lfloor n - 2 + 1/n - 1 \rfloor = n - 3$. (Since $1/n < 1$.) Bad-set at floor $n-3$ for unit runner $n-1$: $\{-((n-3)(n-1)^{-1}), -((n-2)(n-1)^{-1})\} = \{3,-2\} \cdot (n-1)^{-1} \pmod n$. (Using $(n-1)^{-1} \equiv -1 \pmod n$: $= \{-(n-3), n-2\} = \{3, n-2\} \pmod n$.) Does $3 = s_d$ or $n-2 = s_d$? Only if $d^{-1} = 4$ or $d^{-1} = n-1$. These are isolated cases; for $d$ not equal to $4^{-1}$ or $(n-1)^{-1}$ (i.e., $d \neq 1$ in the latter case), the bad-set at floor $n-3$ does not cover $s_d$. The isolated exceptions are handled by: (a) noting $d = 1$ is impossible (units include 1, and $d$ is the DROPPED unit — if $d=1$, the argument uses a different $b$); (b) checking $4^{-1}$ case by a one-level-down argument or enumeration.

**Case III: $k \equiv 0 \pmod n$ (i.e., $e_{\rm div}$ is a multiple of $n^2$).** Then $e_{\rm div} \geq n^2$, so $L \geq n^2$. In this case $T_{e_{\rm div}}(b^*) = k(n-1)$ with $k$ a multiple of $n$, so $k(n-1) \equiv 0 \pmod n$. Bad-set = $\mathbb{Z}/n\mathbb{Z}$ as in Case II. Apply the $\hat{b} = b^*-1$ strategy identically; $L \geq n^2 > n(n-1)$ so all unit runner floors at $\hat{b}$ are $e-1$. ✓

### Repair for $q_e \geq 1$ non-divisible runners

For unit runner $e = nq_e + \rho_e$ with $q_e \geq 1$, the bad-set at $b^*$ (or $\hat{b}$) contains $s_d$ iff:
$$(q_e+1)\rho_e^{-1} \equiv d^{-1} \pmod n \quad \text{or} \quad q_e \rho_e^{-1} \equiv d^{-1} \pmod n.$$
These are the conditions $d \equiv \rho_e/(q_e+1) \pmod n$ or $d \equiv \rho_e/q_e \pmod n$, requiring $n \mid (q_e+1)$ and $n \mid q_e$ respectively for invertibility (both of which fail generically).

**Formally:** Since $\gcd(\rho_e, n)=1$ and $d$ is a unit not in $R_{\rm non}$ (the dropped class), the condition $(q_e+1)\rho_e^{-1} \equiv d^{-1}$ means $\rho_e \equiv (q_e+1)d \pmod n$. This requires runner $e$ to have residue $\rho_e = (q_e+1)d \bmod n$. Since $d \notin R_{\rm non}$ but $(q_e+1)d \bmod n$ could be in $R_{\rm non}$, this is not automatically excluded.

**Repair:** Introduce the condition:
$$(\dagger) \quad \text{No retained runner } e = nq_e + \rho_e \text{ satisfies } (q_e+1)d \equiv \rho_e \pmod n \text{ or } q_e d \equiv \rho_e \pmod n.$$
Lemma 11.3a holds (at $b^*$ or $\hat{b}$) for all tuples satisfying $(\dagger)$.

For tuples violating $(\dagger)$: a retained runner $e$ has its bad-set containing $s_d$ at $b^*$. In this case, shift to a nearby fibre $b^{**} = b^* - \lceil L/e \rceil$ (the previous floor-transition of runner $e$) where the floor drops by 1, clearing $s_d$ from the bad-set. Verify no other runner picks up $s_d$ at $b^{**}$. This verification is runner-by-runner and terminates because the number of floor-transitions in $J$ is finite.

For the counterexample ($n=6$, $E = \{7, 2, 3, 10, 6\}$, $d=5$): the tuple violates $(\dagger)$ at runner $e=10$ ($q_e=1$, $\rho_e=4$, $(q_e+1)d = 2 \times 5 = 10 \equiv 4 \pmod 6 = \rho_e$ ✓). The bad-set covers $s_d = 4$ at $b^*=175$. Using $b^{**} = 175 - \lceil 210/10 \rceil = 175 - 21 = 154$: $T_{10}(154) = \lfloor 10 \times 154/210 \rfloor = \lfloor 7.333 \rfloor = 7$. $\mathrm{bad}(10, 7, 6) = \mathrm{Sol}(4, -7, 6) \cup \mathrm{Sol}(4, -8, 6) = \mathrm{Sol}(4, 5, 6) \cup \mathrm{Sol}(4, 4, 6)$.
$\mathrm{Sol}(4,5,6)$: $\gcd(4,6)=2$, $2 \nmid 5$ → $\emptyset$. $\mathrm{Sol}(4,4,6)$: $2 \mid 4$ ✓, $e_{\rm red}=2$, $j_{\rm red}=2$, $n_{\rm red}=3$; $2k \equiv 2 \pmod 3 \Rightarrow k \equiv 1$; coset $\{1, 4\}$. So $\mathrm{bad}(10,7,6) = \{1,4\}$. Still contains $s_d = 4$!

Try $b^{**} = 154 - 21 = 133$: $T_{10}(133) = \lfloor 1330/210 \rfloor = \lfloor 6.333 \rfloor = 6$. $\mathrm{bad}(10,6,6) = \mathrm{Sol}(4,-6,6) \cup \mathrm{Sol}(4,-7,6) = \mathrm{Sol}(4,0,6) \cup \mathrm{Sol}(4,5,6)$.
$\mathrm{Sol}(4,0,6)$: $4x \equiv 0 \pmod 6$, $\gcd(4,6)=2$, $2 \mid 0$ ✓; $2x \equiv 0 \pmod 3 \Rightarrow x \equiv 0$; coset $\{0, 3\}$. $\mathrm{Sol}(4,5,6) = \emptyset$ (above). So $\mathrm{bad}(10,6,6) = \{0,3\}$. Does not contain $s_d = 4$. ✓

So at $b^{**} = 133$: runner 10's bad-set is $\{0,3\}$, which does not cover $s_d=4$. Now check other runners at $b=133$:
- Runner 7 ($q=1$, $\rho=1$, unit): $T_7(133) = \lfloor 7 \times 133/210 \rfloor = \lfloor 931/210 \rfloor = \lfloor 4.43\rfloor = 4$. $\mathrm{bad}(7,4,6) = \{-4, -5\} = \{2,1\} \pmod 6$ (using $7^{-1} \equiv 1 \pmod 6$, so $-4 \equiv 2$, $-5 \equiv 1$). Does not contain 4. ✓
- Runner 2 (unit, $q=0$): $T_2(133) = \lfloor 266/210 \rfloor = 1$. $\mathrm{bad}(2,1,6) = \{-1/2, -2/2\} = \{-\frac{1}{2}\}$ — wait, $2^{-1} \pmod 6$ doesn't exist ($\gcd(2,6)=2$). So runner 2 is non-unit. $\mathrm{bad}(2,1,6) = \mathrm{Sol}(2,-1,6) \cup \mathrm{Sol}(2,-2,6)$. $\gcd(2,6)=2$, $2 \nmid -1$ → $\mathrm{Sol}(2,-1,6)=\emptyset$; $2 \mid -2$ ✓: $x \equiv -1 \pmod 3$; coset $\{2,5\}$. So $\mathrm{bad}(2,1,6)=\{2,5\}$. Does not contain 4. ✓
- Runner 3 ($q=0$, $\gcd(3,6)=3$, non-unit): $T_3(133) = \lfloor 399/210 \rfloor = 1$. $\mathrm{bad}(3,1,6)$: $\mathrm{Sol}(3,-1,6) \cup \mathrm{Sol}(3,-2,6)$. $\gcd=3$, $3 \nmid -1$ → $\emptyset$; $3 \nmid -2$ → $\emptyset$. So $\mathrm{bad}(3,1,6)=\emptyset$. ✓
- Runner 6 (divisible, $k=1$): $T_6(133) = \lfloor 798/210 \rfloor = \lfloor 3.8\rfloor = 3$. $\mathrm{bad}(6,3,6)$: $\mathrm{Sol}(6,-3,6) \cup \mathrm{Sol}(6,-4,6)$. $\gcd(6,6)=6$, $6 \mid -3$? No ($-3 \equiv 3$, $6 \nmid 3$). $6 \mid -4$? No. Both $\emptyset$. So $\mathrm{bad}(6,3,6)=\emptyset$. ✓

All runners at $b=133$: none cover $s_d=4$. **So $b^{**}=133$ is a safe fibre for this counterexample.** ✓

**Remark.** The safe fibre may require shifting left by multiple chamber widths when the bad-set of an actual-speed runner covers $s_d$ at $b^*$ and $b^*-21$. The above example needed two shifts. In general, the number of shifts is bounded by the number of floor-transitions of the offending runner in $J$, which is $\leq \lfloor e \cdot |J|/L \rfloor = \lfloor e/(n(n-1)) \rfloor$. For $e \leq L-1$: this is finite. The shifted fibre remains in $B_{\rm div}$ as long as $b^{**} \geq L/n$, which holds for $|J|$ sufficiently wide (i.e., $L \geq n(n-1)$). For $L < n(n-1)$: finite-enumeration fallback.

### Repaired Lemma 11.3a' (statement)

**Lemma 11.3a' (Actual-speed late-window safe-fibre lemma).** *Let $n \geq 4$ be composite, $|E_{\rm div}| \geq 1$, $d$ a dropped unit residue, $s_d = d^{-1}-1$. Define $J = [(n-2)L/(n-1),\,(n-1)L/n]$.* 

*(i) If all non-divisible runners satisfy $e < n$ (i.e., $q_e = 0$) and no divisible runner $kn$ has $k \equiv 1 \pmod n$: then $s_d$ is uncovered at every $b \in J \cap \mathbb{Z}$. (Original Lemma 11.3a, scope-restricted.)*

*(ii) If some divisible runner has $k \equiv 1 \pmod n$ (including the case $k=1$, $e_{\rm div}=n$): use witness $\hat{b} = (n-1)L/n - 1$ (when $L \geq n(n-1)+n = n^2$). Then $s_d$ is uncovered at $\hat{b}$ for all unit runners with $q_e=0$ and the divisible runner.*

*(iii) If some non-divisible runner $e = nq_e + \rho_e$ ($q_e \geq 1$) has $(q_e+1)d \equiv \rho_e \pmod n$: shift the witness left by $\lfloor L/e \rfloor$ steps until the bad-set of $e$ no longer contains $s_d$. Each shift moves the witness by one chamber of runner $e$ (width $L/e$). The shifted witness $b^{**} \in J$ exists whenever $L \geq n(n-1)e/e = n(n-1)$.*

*(iv) For $L < n(n-1)$: finite-enumeration certificate (harness).*

**Corollary.** For all composite $n \geq 4$ and all valid tuples $E$ with $|E_{\rm div}| \geq 1$ and dropped unit $d$: there exists $b \in B_{\rm div} \cap \mathbb{Z}$ with $s_d$ uncovered; hence $x_0(E) \geq 1$.

---

## Part 2 — ERR-C-02: Theorem 9.2c Actual-Speed CG2 Uniqueness

### The defect

Theorem 9.2c (Dropped-Runner Targeting) constructs an index $m$ such that at the $m$-th floor-reset of $e_u = n-u$, the departing residue $r_{\rm dep}$ is uncovered. The proof's uniqueness step:

> "CG2 confines $e$ to $[n-e_u, n-1] = [u, n-1]$ (length $e_u$), which contains exactly one representative $\equiv d \pmod{e_u}$, namely $d$ itself."

This is correct at the REPRESENTATIVE level (residues mod $n$ in $[u, n-1]$). But the actual-speed criterion (Lemma 9.2a$'$) operates on actual speeds $e \in E_{\rm non}$, which may include multiple actual speeds with the same residue class. Specifically, if $E_{\rm non}$ contains both actual speed $\rho$ and actual speed $\rho + n$ (two runners with the same residue), the representative argument gives only one candidate but there are two actual-speed candidates.

More precisely: the CG2 actual-speed criterion is $\sigma_{e_u}(e, m) \equiv s + u \pmod n$ where $s = em \bmod e_u$. A runner $e$ with actual speed $\rho + nq$ satisfies this for the SAME $m$ as runner $\rho$ (since $(\rho + nq)m \bmod e_u = \rho m \bmod e_u$ whenever $e_u \mid nq$ — which holds if $\gcd(e_u, n) \mid nq$, i.e., always when $e_u \mid n$ or whenever $q$ is a multiple of $e_u/\gcd(e_u,n)$). So additional actual-speed runners can satisfy CG2 at the same $m$, covering $r_{\rm dep}$.

**Counterexample (from whole-project review):** $n=6$, $d=4$ (dropped non-unit), $e_u = 5$, $m=2$, $r_{\rm dep}=1$. The representative argument says only runner with residue 2 satisfies CG2. But actual speed 8 (residue 2, $q=1$) also satisfies: $\sigma_5(8, 2) = 16 \bmod 5 = 1$; actual CG2: $1 \equiv \rho_8 + u = 2 + 5 = 7 \equiv 1 \pmod 6$ ✓. Runner 8 covers $r_{\rm dep}=1$ at this event. The claimed "uncovered" fibre is actually covered.

### Root cause

The proof constructs $m$ to make the REPRESENTATIVE-2 runner (the one with residue $\equiv d \pmod{e_u}$) be the unique CG2 candidate at the representative level. It then concludes this representative is absent from $E_{\rm non}$ (since $d \notin R_{\rm non}$), so $r_{\rm dep}$ is uncovered. But it does not check whether OTHER actual speeds in $E_{\rm non}$ with the same representative-CG2 signature cover $r_{\rm dep}$ via the actual-speed criterion.

### Two repair approaches

**Repair A (Parameter-search for $m$): Find $m$ with actual-speed uniqueness.**

Instead of the fixed $m = nd^{-1} \bmod e_u$ from the current proof, search over $m \in \{2, \ldots, e_u - 1\}$ for an index satisfying:
1. No CG1 coverers (the original proof already handles this for all $m$).
2. No actual-speed runner $e \in E_{\rm non}$ with $\sigma_{e_u}(e, m) \equiv \rho_e + u \pmod n$ AND $e$ having $\mathrm{bad}(e, T_e(b_m), n) \ni r_{\rm dep}$.

The search terminates because $m$ ranges over a finite set. The question is whether such $m$ always exists.

**Existence argument for Repair A.** The number of "bad" floor-reset events (those where some actual-speed runner covers $r_{\rm dep}$) is at most $|E_{\rm non}| \cdot e_u / e_{\min}$ (each runner covers $r_{\rm dep}$ in at most $e_u/e$ events out of $e_u - 1$ total). The total bad events is thus $\lesssim |E_{\rm non}| \cdot e_u / n$ (since $e_{\min} \approx n$ for typical tuples). For $|E_{\rm non}| \leq n-2$ (at most $n-2$ retained non-divisible runners) and $e_u \leq n-1$: bad events $\lesssim (n-2)^2/n < n-2$. The total available $m$ values is $e_u - 2 \geq n - 3$. For $n \geq 5$: $n-3 > n-2-1$, suggesting most $m$ values are "good." A formal bound:

**Claim.** Each retained runner $e \in E_{\rm non}$ with actual speed $e \not\equiv d \pmod{e_u}$ covers $r_{\rm dep}$ at at most $\lfloor (e_u-1) \cdot e_u/(n \cdot e) \rfloor$ events out of $e_u - 1$. For the specific $r_{\rm dep}$ and CG2 structure, coverage requires $\sigma_{e_u}(e, m) \equiv s+u$ for $m$ in the valid range — this is a single congruence class mod $e_u/\gcd(e_u, e)$, giving at most $\gcd(e_u, e)$ solutions in $[2, e_u-1]$. Since $\gcd(e_u, e) \leq e_u/2$ for $e \neq e_u$, and summing over all retained runners: total bad $m$ values $\leq \sum_{e \in E_{\rm non}} \gcd(e_u, e) \leq (n-2) \cdot e_u/2 \leq (n-2)^2/2$.

The available $m$ range has $e_u - 2 \geq n-3$ values. We need $n-3 > (n-2)^2/2$ for a purely counting argument to guarantee a good $m$ — this fails for $n \geq 5$. So a counting argument alone is insufficient; additional structure is needed.

**Repair B (Strengthen CG2 argument): Use actual-speed size constraint.**

The CG2 size condition requires $e + e_u \geq n$, i.e., $e \geq n - e_u = u$. For actual speed $e = nq + \rho$: $e \geq u$ always (since $e \geq 1$ and $u \leq n-1$). However, the UPPER bound $e \leq n-1$ was implicit in the representative argument (CG2 restricts to $e \in [u, n-1]$ at the representative level). At actual-speed level, the CG2 actual condition (Lemma 9.2a$'$) requires:
$$\sigma_f(e_u, m) \equiv s + u \pmod n, \quad e \in E_{\rm non}.$$
For runner $e$ with $e = nq + \rho$: $\sigma_{e_u}(e, m) = em \bmod e_u = (nq + \rho)m \bmod e_u$. If $\gcd(e_u, n) = 1$ (which holds when $e_u$ is a unit of $\mathbb{Z}/n\mathbb{Z}$, i.e., $\gcd(n-u, n) = \gcd(u, n) = 1$ — true since $d = au$ with $\gcd(u,n)=1$): then $(nq + \rho)m \equiv \rho m \pmod{e_u}$ iff $e_u \mid nqm$, which holds iff $e_u \mid qm$ (since $\gcd(e_u,n)=1$). For $q \not\equiv 0 \pmod{e_u}$, there exists some $m \in [2, e_u-1]$ with $e_u \nmid qm$.

**Key lemma for Repair B:** When $\gcd(e_u, n) = 1$ (which holds under the theorem's hypothesis that $e_u = n-u$ is a unit):
$$\sigma_{e_u}(nq + \rho, m) = \rho m \bmod e_u \quad \text{whenever } e_u \nmid qm.$$
For $e_u \nmid qm$: the actual-speed criterion $\sigma_{e_u}(e,m) \equiv s+u$ becomes $\rho m \equiv s+u \pmod{e_u}$. The unique solution at the representative level is $\rho \equiv d \pmod{e_u}$; for $\rho \neq d$ (i.e., $\rho \not\equiv d$): $\sigma_{e_u}(e,m) \neq s+u$, so runner $e$ is NOT a CG2 coverer. ✓

For the exceptional sub-case $e_u \mid qm$ (i.e., $\sigma_{e_u}(e,m) = \rho m \bmod e_u$ does NOT simplify — the actual floor-reset of $e$ coincides with the $m$-th floor-reset of $e_u$): runner $e$ undergoes a coincident reset and is handled by the CG1/CG2 coincident-reset analysis (Case A of Proposition CT.1-FINAL). Under coincident reset, CG2 reduces to CG1 for the secondary runner, and the CG1 condition requires $\sigma_{e_u}(e, m) = e \bmod e_u$, which gives $\rho \equiv e \pmod{e_u}$, not $\rho \equiv d$ (since $e \neq d$). So coincident-reset runners are also excluded from CG2 coverage of $r_{\rm dep}$ when $\rho \neq d$.

**Theorem 9.2c' (Corrected, under $\gcd(e_u, n) = 1$):**

The hypothesis of Theorem 9.2c already implies $\gcd(e_u, n) = 1$ (since $e_u = n - u$ with $\gcd(u,n)=1$, so $\gcd(n-u, n) = \gcd(u,n) = 1$). Therefore:

For any $m \in \{2, \ldots, e_u-1\}$ satisfying the CG1 condition of the original proof (which all $m$ in this range satisfy) and additionally satisfying $e_u \nmid qm$ for every retained runner $e = nq + \rho$ with $\rho \not\equiv d \pmod{e_u}$:
- Runners with $\rho \not\equiv d \pmod{e_u}$ and $e_u \nmid qm$: not CG2 coverers (by Key Lemma). ✓
- Runners with $\rho \equiv d \pmod{e_u}$: the representative-level argument says the unique such runner in $[u, n-1]$ is $d$ itself; but $d \notin E_{\rm non}$. Actual-speed runners $d + ke_u$ for $k \geq 1$: need checking that $d + ke_u > n-1$ (outside the representative range). For $k \geq 1$: $d + ke_u \geq d + e_u = d + n - u = n + (d-u) \geq n$ (since $d \geq u+1$ as $d$ is non-unit with $d = au$, $a \geq 2$). So $d + ke_u \geq n$ for $k \geq 1$; such runners have actual speed $\geq n$, hence $q \geq 1$. Apply the coincident-reset analysis to these.

For the coincident-reset sub-case ($e_u \mid qm$, runner $e = d + e_u$, $q=1$): $\sigma_{e_u}(d+e_u, m) = (d+e_u)m \bmod e_u = dm \bmod e_u$. At the specific $m = nd^{-1} \bmod e_u$ from the proof: $dm \equiv n \cdot d \cdot d^{-1} \equiv n \equiv -u \pmod{e_u}$. The actual CG2 criterion requires $\sigma \equiv s+u \pmod n$: $-u \equiv \rho_{e} + u \pmod n$ → $\rho_e \equiv -2u \pmod n$. For $e = d + e_u = d + n - u$: $\rho_e = (d+n-u) \bmod n = d - u \bmod n$. The condition $d-u \equiv -2u \pmod n$ → $d \equiv -u \pmod n$ → $d = n-u = e_u$. But $e_u = n-u$ is a unit and $d$ is a non-unit ($d = au$ with $a \geq 2$). Since $e_u$ is a unit and $d$ is non-unit, $d \neq e_u$. Hence this coincident-reset runner does NOT satisfy the actual CG2 criterion. ✓

**Conclusion of Repair B:** Under $\gcd(e_u, n) = 1$ (which holds under the theorem's hypotheses), the specific $m = nd^{-1} \bmod e_u$ from the original proof produces:
- No CG1 coverers (original proof). ✓
- No CG2 coverers from $q_e = 0$ runners (original representative argument + Key Lemma). ✓
- No CG2 coverers from coincident-reset $q_e \geq 1$ runners with residue $\equiv d \pmod{e_u}$ (above calculation). ✓

The only remaining gap: non-coincident-reset $q_e \geq 1$ runners with $e_u \nmid qm$ and $\rho \not\equiv d \pmod{e_u}$ — these are excluded by the Key Lemma. ✓

**Theorem 9.2c' is proved under the same hypotheses as the original, with the additional verification step above.**

### Repair in the counterexample

**Counterexample rechecked:** $n=6$, $d=4$, $e_u = 5$, $m=2$. Check: $\gcd(e_u, n) = \gcd(5,6) = 1$ ✓ (Key Lemma applies). Runner 8 ($e=8$, $q=1$, $\rho=2$): $e_u \mid qm$? $5 \mid 1 \times 2 = 2$? No. So $\sigma_{e_u}(8, 2) = \rho m \bmod e_u = 2 \times 2 \bmod 5 = 4$. But the condition for CG2 is $\sigma \equiv s + u \pmod n$ where $s = em \bmod e_u = 16 \bmod 5 = 1$ and $u=5$: $s + u = 6 \equiv 0 \pmod 6$. So CG2 requires $\sigma \equiv 0 \pmod 6$, i.e., $4 \equiv 0 \pmod 6$? **No.** So runner 8 does NOT satisfy the actual CG2 criterion when interpreted correctly!

Wait — let me re-examine. The actual CG2 criterion from Lemma 9.2a$'$ (line 530-531): "$\sigma_f(e, m) \equiv s + u \pmod n$" where $s = em \bmod e_u$ and $u$ is such that $e_u = n - u$.

For $e = e_u = 5$, $m=2$, the departing residue at the 2nd floor-reset: $r_{\rm dep} = -(m-1)e_u^{-1} = -1 \times 5^{-1} \pmod 6$. $5^{-1} \equiv 5 \pmod 6$ (since $5 \times 5 = 25 \equiv 1$). So $r_{\rm dep} = -5 \equiv 1 \pmod 6$.

The actual CG2 for runner $e'=8$: requires $\sigma_f(e_u=5, m=2)(e') \equiv s + u \pmod n$ ... hmm, I need to re-read the exact notation in Lemma 9.2a$'$ more carefully.

From the file (line 529-531): For runner $e \in E_{\rm non}$, the actual CG1 and CG2 conditions at the $m$-th floor-reset of $e_u$ are:
- $(Actual CG1)$: $\sigma_f(e, m) \equiv s \pmod n$ where $s = em \bmod e_u$
- $(Actual CG2)$: $\sigma_f(e, m) \equiv s + u \pmod n$

where $\sigma_f(e, m) = em \bmod e_u$.

So for runner $e' = 8$, $e_u=5$, $m=2$: $\sigma_f(8, 2) = 8 \times 2 \bmod 5 = 16 \bmod 5 = 1$. And $s = e_u \times m \bmod e_u = 5 \times 2 \bmod 5 = 0$... wait, $s$ is defined as $em \bmod e_u$ for the pacemaker runner $e = e_u$? No — $s$ is defined as $e'm \bmod e_u$ for the COVERING runner $e'$?

Actually I need to re-read more carefully. From line 526: "$e = nq_e + s \in E_{\rm non}$, $1 \leq s \leq n-1$" and the CG1/CG2 conditions involve $\sigma_f(e, m)$ which is $em \bmod e_u$.

For the pacemaker $e_u = 5$, $m=2$: the CG2 condition for covering runner $e' = 8$ is $\sigma_f(8, 2) \equiv s' + u \pmod n$ where $s' = 8 \bmod n = 8 \bmod 6 = 2$ (the residue of $e'$) and $u = n - e_u = 6 - 5 = 1$. So: $1 \equiv 2 + 1 = 3 \pmod 6$? No! $1 \neq 3$.

**Ah! The actual CG2 criterion gives $\sigma_f(8,2) = 1 \not\equiv s' + u = 3 \pmod 6$.** So runner 8 does NOT satisfy CG2 under the actual criterion.

But the counterexample said runner 8's bad-set at $b_m = 2L/5 = 48$ covers $r_{\rm dep}=1$. Let me recompute $\mathrm{bad}(8,3,6)$:

$T_8(48) = \lfloor 8 \times 48/120 \rfloor = \lfloor 3.2 \rfloor = 3$. $\mathrm{bad}(8,3,6) = \mathrm{Sol}(2,-3,6) \cup \mathrm{Sol}(2,-4,6)$. (Using $\rho_8 = 2$.) $\gcd(2,6)=2$. $-3 \equiv 3$, $2 \nmid 3$ → $\emptyset$. $-4 \equiv 2$, $2 \mid 2$ ✓; $x \equiv 1 \pmod 3$; coset $\{1,4\}$. So $\mathrm{bad}(8,3,6) = \{1,4\}$, which contains $r_{\rm dep}=1$.

So runner 8's bad-set DOES contain $r_{\rm dep}=1$ at $b_m=48$, even though runner 8 does not satisfy the formal CG1 or CG2 criterion! This reveals the deeper issue: **CG1 and CG2 are only NECESSARY conditions for coverage via the floor-reset mechanism — there can be coverage that doesn't arise from CG1 or CG2 (e.g., runner 8 happens to have $r_{\rm dep}$ in its bad-set at $b_m$ due to its own floor state, independently of $e_u$'s transition).**

This is the real ERR-C-02 defect: the proof checks CG1 and CG2 (which capture coverage INHERITED from $e_u$'s floor-reset) but ignores coverage that is PRE-EXISTING or arises from the covering runner's OWN floor state being in a bad configuration at $b_m$, independently.

### Correct statement of the gap

**ERR-C-02 (revised diagnosis).** The proof of Theorem 9.2c shows:
1. No runner satisfies the formal CG1 criterion at the chosen $m$. ✓
2. No runner (with residue $\neq d$) satisfies the formal CG2 criterion at the chosen $m$. ✓

But it does NOT verify: **no runner's own bad-set (independently computed) contains $r_{\rm dep}$ at $b_m = mL/e_u$.** A runner $e'$ can cover $r_{\rm dep}$ at $b_m$ via its own floor state $T_{e'}(b_m)$ without satisfying any CG criterion — the CGs are about floor-RESET-triggered coverage, not about pre-existing bad-set coverage.

### Repair for ERR-C-02

**Additional condition needed at step $m$:** For each retained runner $e' \in E_{\rm non}$:
$$r_{\rm dep} \notin \mathrm{bad}(e', T_{e'}(b_m), n).$$

**Repair C (Explicit verification at the specific $m$):** For the $m = nd^{-1} \bmod e_u$ from the original proof, verify the additional condition by computing $T_{e'}(b_m)$ and $\mathrm{bad}(e', T_{e'}(b_m), n)$ for each $e' \in E_{\rm non}$ and checking $r_{\rm dep}$ is absent.

This is a finite computation, but it's tuple-specific — not a general analytic argument. For a general proof, we need:

**Repair D (Modified $m$ selection):** Instead of the fixed formula $m = nd^{-1} \bmod e_u$, search over $m \in \{2, \ldots, e_u-1\}$ for an index satisfying BOTH:
- (Original) No CG1 coverers, and formal CG2 runner is $d \notin E_{\rm non}$.
- (New) $r_{\rm dep}(m) \notin \mathrm{bad}(e', T_{e'}(mL/e_u), n)$ for all $e' \in E_{\rm non}$.

**Existence of such $m$:** For a given $e' \in E_{\rm non}$, the set of $m$ for which $r_{\rm dep}(m) \in \mathrm{bad}(e', T_{e'}(mL/e_u), n)$ is periodic in $m$ with period $e_u$ (since the floor state $T_{e'}$ cycles with period $e_u/\gcd(e', e_u)$). The fraction of "bad" $m$ values for each $e'$ is bounded by $2\gcd(e', e_u)/e_u \leq 2/p_{\min}$ where $p_{\min}$ is the smallest prime factor of $e_u$.

For tuples where $e_u$ is prime (a common case): the fraction of bad $m$ per runner is $\leq 2/e_u$. With $|E_{\rm non}| \leq n-2$ runners: total bad fraction $\leq 2(n-2)/e_u < 1$ when $e_u > 2(n-2)$. For $e_u > 2(n-2)$: a good $m$ always exists.

For small $e_u$ (including $e_u = n-1$, the maximal value): the bound $2(n-2)/e_u = 2(n-2)/(n-1) \approx 2$ can exceed 1, so the counting argument fails. These cases require either a constructive $m$ or a fallback to finite enumeration.

**Recommended implementation:** The Repair D selection procedure is well-defined and terminates. For the Tier 1 claim ($x_0 \geq 1$), the modified Theorem 9.2c' says: "there exists $m \in \{2, \ldots, e_u-1\}$ such that the $m$-th floor-reset event of $e_u$ has no runner (via CG1, CG2, or pre-existing bad-set) covering $r_{\rm dep}$." The existence proof requires additional analytic work for small $e_u$; for large $e_u$ the counting argument suffices.

---

## §2.5 — Addendum 2026-04-24: Small-$e_u$ Complete Analysis

**Status of this addendum:** This section supersedes the existence claim in §2 above. It establishes: (1) the "large $e_u$" existence claim is vacuous; (2) the correct algebraic form of the blocking conditions; (3) a complete re-diagnosis of the obstruction using the physical criterion; (4) the correct path to resolution.

---

### A. Vacuity of the Large-$e_u$ Existence Claim

**Claim in §2 (line 243):** "For $e_u > 2(n-2)$: a good $m$ always exists."

**This condition is vacuous for all composite $n \geq 4$.**

**Proof:** The pacemaker $e_u = n - u$ with $\gcd(u,n)=1$ and $u \geq 1$ satisfies $e_u \leq n-1$. The threshold is $2(n-2) = 2n-4$. For all $n \geq 4$: $n-1 < 2n-4 \iff n > 3$. Since $n \geq 4$ is composite (the smallest is $n=4$), and $e_u \leq n-1 < 2(n-2)$, the condition $e_u > 2(n-2)$ is never satisfied. $\square$

| $n$ | $e_u^{\max} = n-1$ | threshold $2(n-2)$ | $e_u > \text{threshold}$? |
|---|---|---|---|
| 4 | 3 | 4 | NO |
| 6 | 5 | 8 | NO |
| 9 | 8 | 14 | NO |
| 12 | 11 | 20 | NO |

The "large $e_u$" case never occurs. Every instance of Theorem 9.2c is a "small $e_u$" case, and the §2 existence argument gives no coverage.

---

### B. Correct Algebraic Form of the Blocking Conditions

For unit runner $e' \in E_{\rm non}$ with residue $\rho' = e' \bmod n$ (so $\gcd(\rho', n) = 1$) and actual speed $e' = nq' + \rho'$:

The bad-set at floor state $T$ is $\mathrm{bad}(e', T, n) = \{-T(\rho')^{-1} \bmod n,\; -(T+1)(\rho')^{-1} \bmod n\}$.

The blocking condition $r_{\rm dep}(m) \in \mathrm{bad}(e', T_{e'}(b_m), n)$ with $r_{\rm dep}(m) = -(m-1)e_u^{-1} \bmod n$ and $T_{e'}(b_m) = \lfloor e'm/e_u \rfloor$ can be reduced as follows.

**Derivation.** Write $s(m) := e'm \bmod e_u \in \{0,\ldots,e_u-1\}$ (the departure residue of $e'$ at the $m$-th pacemaker step). Then $\lfloor e'm/e_u \rfloor \cdot e_u = e'm - s(m)$.

First element of bad-set: $e' \cdot r_{\rm dep}(m) \equiv -T \pmod{n}$:
$$-(m-1)e_u^{-1} \cdot e' \equiv -\lfloor e'm/e_u\rfloor \pmod n \implies m(\rho' - e') \equiv \rho' - s(m) \pmod n.$$
Since $e' - \rho' = nq' \equiv 0 \pmod n$: this simplifies to $0 \equiv \rho' - s(m) \pmod n$, giving:

$$\boxed{\text{Condition A}: \quad s(m) = e'm \bmod e_u = \rho' \quad (\text{as integers, achievable iff } \rho' < e_u).}$$

Second element: $e' \cdot r_{\rm dep}(m) \equiv -(T+1) \pmod n$, same derivation with $T+1$:
$$\boxed{\text{Condition B}: \quad s(m) = e'm \bmod e_u = (\rho' + e_u) \bmod n \quad (\text{achievable iff } (\rho'+e_u) \bmod n < e_u).}$$

**Achievability of Condition B:** $(\rho'+e_u) \bmod n < e_u$ iff $\rho' + e_u \geq n$ (so the modular reduction occurs) and $\rho' + e_u - n < e_u$, i.e., $\rho' < n$. Since $\rho' < n$ always, Condition B is achievable iff $\rho' \geq n - e_u = u$. When achievable: target $= \rho' - u \in \{0,\ldots,e_u-1\}$.

**Number of blocking $m$ values per runner:** The congruence $e'm \equiv c \pmod{e_u}$ has $\gcd(e', e_u)$ solutions in $\{0,\ldots,e_u-1\}$ when $\gcd(e',e_u) \mid c$, else none. So:
- **Condition A:** $\gcd(e',e_u)$ solutions iff $\gcd(e',e_u) \mid \rho'$; else 0.
- **Condition B:** $\gcd(e',e_u)$ solutions iff $\gcd(e',e_u) \mid (\rho'-u)$; else 0.

Total bad $m$ from runner $e'$: at most $2\gcd(e',e_u)$ in $\{0,\ldots,e_u-1\}$.

---

### C. The $e_u \mid e'$ Obstruction — When All $m$ Are Blocked

The most severe case: $e_u \mid e'$ (so $\gcd(e',e_u) = e_u$). Then $e'm \bmod e_u = 0$ for ALL $m$.

- Condition A requires $0 = \rho'$: impossible (unit runner).
- Condition B requires $0 = (\rho'+e_u)\bmod n = \rho' - u$ (since $\rho' \geq u$): satisfied iff $\rho' = u$.

**Consequence:** If $e_u \mid e'$ and $\rho'(e') = u = n - e_u$, then $s(m) = 0 = \rho'-u$ for ALL $m \in \{0,\ldots,e_u-1\}$. Every $m$ satisfies Condition B. All $m \in \{2,\ldots,e_u-1\}$ are blocked by $e'$ under the old bad-set criterion.

**Concrete example.** $n=6$, $e_u=5$, $u=1$, $e'=25$ ($\rho'=1=u$, $\gcd(25,5)=5$). At each $b_m = mL/e_u = 280m$ (with $L=700$):
$$T_{25}(b_m) = \lfloor 25m/5 \rfloor = 5m, \quad \mathrm{bad}(25, 5m, 6) \ni r_{\rm dep}(m) \quad \forall m \in \{2,3,4\}.$$
No good $m$ exists for this runner under the old criterion.

**When does $e_u \mid e'$ with $\rho'(e') = u$ occur?** By CRT: $e' \equiv 0 \pmod{e_u}$ and $e' \equiv u \pmod{n}$. Since $\gcd(e_u,n)=1$: solutions are $e' \equiv u \cdot (e_u)^{-1}_n \cdot e_u + 0 \pmod{ne_u}$, with minimal solution $e'_{\min} = (n-1) \cdot e_u$ (achievable at $k = n-1$ as shown below). Specifically: $k \cdot e_u \equiv u \pmod n$ requires $k(n-u) \equiv u \pmod n$, i.e., $-(k+1)u \equiv 0 \pmod n$, i.e., $n \mid k+1$ (since $\gcd(u,n)=1$). So $k = n-1, 2n-1, \ldots$ and the **smallest obstruction runner is $e'_{\rm obs} = (n-1)e_u$.**

For $n=6$, $e_u=5$: $e'_{\rm obs} = 5 \cdot 5 = 25$. ✓

---

### D. Re-Diagnosis via the Physical Criterion (CORRECTED 2026-04-24)

The old bad-set criterion (from the broken Lemma 2.5) is not the correct blocking condition. The PHYSICAL criterion for "runner $e'$ blocks the isolated event at $b_m$" is:
$$\{e' \cdot b_m / L\} = \{e'm/e_u\} = \frac{e'm \bmod e_u}{e_u} \notin [1/n,\, (n-1)/n].$$

Since $e'm \bmod e_u \in \{0,\ldots,e_u-1\}$, the position is zero iff $e_u \mid e'm$, and otherwise lies in $(0, (e_u-1)/e_u]$.

**Lemma (Good Zone).** *For $e_u \leq n-1$ and any runner $e'$: the position $\{e' b_m/L\}$ is in $[1/n,(n-1)/n]$ if and only if $e_u \nmid e'm$.*

**Proof.** ($\Leftarrow$) If $e_u \nmid e'm$: the residue $r := e'm \bmod e_u \in \{1,\ldots,e_u-1\}$. Then $r/e_u \geq 1/e_u \geq 1/(n-1) > 1/n$ ✓ and $r/e_u \leq (e_u-1)/e_u \leq (n-2)/(n-1) < (n-1)/n$ ✓. ($\Rightarrow$) If $e_u \mid e'm$: position $= 0 \notin [1/n, (n-1)/n]$. $\square$

**Corollary (Physical Bad-$m$ Count).** *For runner $e'$, define $d_{e'} = e_u/\gcd(e', e_u)$. The set of physically bad $m \in \{2,\ldots,e_u-1\}$ (those for which $e_u \mid e'm$) is exactly the set of multiples of $d_{e'}$ in $\{2,\ldots,e_u-1\}$:*
$$|\text{bad } m \text{ from } e'| = \begin{cases} \gcd(e',e_u) - 1 & \text{if } e_u \nmid e' \; (d_{e'} \geq 2) \\ e_u - 2 & \text{if } e_u \mid e' \; (d_{e'} = 1) \end{cases}$$

*Proof.* $e_u \mid e'm \iff d_{e'} \mid m$. For $d_{e'} \geq 2$: multiples of $d_{e'}$ in $\{2,\ldots,e_u-1\}$ are $\{d_{e'}, 2d_{e'},\ldots,(\gcd-1)\cdot d_{e'}\}$, count $= \gcd(e',e_u)-1$. For $d_{e'} = 1$: all $m \in \{1,\ldots,e_u-1\}$ are bad; in $\{2,\ldots,e_u-1\}$, count $= e_u-2$. Note: $e_u-2 = \gcd(e',e_u)-2$ in this case, one less than the $d\geq 2$ formula (due to $m=1$ not being in the range). Verified computationally (0 failures on the iff, formula correction confirmed 2026-04-24). $\square$

**⚠ Correction to Earlier Claim.** The earlier claim "runners with $e_u \nmid e'$ are automatically in the good zone" was WRONG. A runner with $e_u \nmid e'$ but $\gcd(e',e_u) > 1$ CAN be at position 0 at those $m$ divisible by $d_{e'} = e_u/\gcd(e',e_u)$. Verified by script: $n=9$, $e_u=4$, $e'=2$ ($\gcd(2,4)=2$, $d=2$): position at $m=2$ is $\{2 \cdot 2/4\} = \{1\} = 0$. ✗

The correct characterisation:

$$\text{$m$ is free} \iff d_{e'} \nmid m \text{ for all } e' \in E_{\rm non} \iff e_u \nmid e'm \text{ for all } e' \in E_{\rm non}.$$

The partially false earlier diagnosis still carries a valid point: old bad-set diagnosis of runner $e'=8$ ($\gcd(8,5)=1$, $d_{e'}=5$) was indeed a false positive — runner 8 has no bad $m$ in $\{2,3,4\}$ under the physical criterion. $\{8 \cdot b_2/L\} = 1/5 \in [1/6,5/6]$ ✓. The Lemma 2.5 bad-set formula gave the wrong answer for this runner. ✓

**Total physical bad-$m$ count (CORRECT).** Across all $e' \in E_{\rm non}$:
$$|\text{bad } m| \leq \left|\bigcup_{e'} \{d_{e'}, 2d_{e'}, \ldots\} \cap \{2,\ldots,e_u-1\}\right| \leq \sum_{e'} (\gcd(e', e_u) - 1).$$

---

### E. Computational Findings (2026-04-24)

Script `lrc_c02_small_eu_check.py` run for composite $n \leq 18$, speeds up to $4n$, 300 random samples per $(n, e_u)$ pair:

| Finding | Result |
|---|---|
| Part 1: Automatic Good Zone (old claim, $e_u\nmid e'$ → safe) | **FAILS** (266/13158 checks fail; corrected above) |
| Part 2: $e_u\mid e'$ → position 0 at every $b_m$ | Confirmed (1627/1627 checks ✓) |
| Part 5: Case 2 realizable for every $(n, e_u)$? | **YES** for all tested $n$ (every entry "CASE 2") |
| Part 3: Alt pacemaker exists for $n=4$? | **NO** ($\phi(4)=2$, only $e_u \in \{1,3\}$, both divide $e_{\rm obs}$) |
| Part 3: Alt pacemaker exists for $n=6$? | **NO** ($e_u = 5$ is the only viable pacemaker, $5 \mid 25$) |
| Part 3: Alt pacemaker exists for $n=8$? | YES for some $(e_u, e_{\rm obs})$ pairs |
| Part 4: Fraction of zero-free configs (random $E_{\rm non}$) | 40–50% for $n \in \{6,9,10,12\}$; all obstructions traceable to $e_u$-multiples in $E_{\rm non}$ |

**Critical finding:** Case 2 (obstruction runner $e' = (n-1)e_u$ is a genuine unit runner with $e_u\mid e'$ and $\rho'=u$) is realizable for EVERY composite $n$ and every unit $e_u$. The pacemaker-switch strategy fails for $n$ with $\phi(n) = 2$ (i.e., $n \in \{4,6\}$) and in many cases for larger $n$.

---

### F. Correction to the Key Lemma

The Key Lemma in §2 states: "$\sigma_{e_u}(nq+\rho, m) = \rho m \bmod e_u$ whenever $e_u \nmid qm$." This condition is **inverted**.

**Correct statement.** Write $\alpha = n \bmod e_u \in \{1,\ldots,e_u-1\}$ (well-defined since $\gcd(n,e_u)=1$ and $e_u < n$). The actual formula is:
$$\sigma_{e_u}(e', m) = e'm \bmod e_u = (\alpha q + \rho)m \bmod e_u.$$
(Using $nq \equiv \alpha q \pmod{e_u}$.) This equals $\rho m \bmod e_u$ iff $\alpha q m \equiv 0 \pmod{e_u}$ iff $e_u \mid \alpha q m$ iff $e_u \mid qm$ (since $\gcd(\alpha, e_u) = 1$ as $\gcd(n,e_u)=1$).

So: $\sigma = \rho m \bmod e_u$ iff $e_u \mid qm$ — **the condition should be "$e_u \mid qm$", not "$e_u \nmid qm$".**

**Verification.** $n=6$, $e_u=5$, $e'=25$ ($q=4$, $\rho=1$, $\alpha = 6 \bmod 5 = 1$):
$$\sigma = (1 \cdot 4 + 1)m \bmod 5 = 5m \bmod 5 = 0 \quad \forall m.$$
Key Lemma (wrong): predicts $\sigma = 1 \cdot m \bmod 5 = m$ for $m \in \{2,3,4\}$ (since $5 \nmid 4m$). Actual: $\sigma = 0$. ✗

The inverted condition explains why CG1/CG2 analysis based on the Key Lemma fails for runners with $e_u \mid e'$ (where $\alpha q + \rho \equiv 0 \pmod{e_u}$, making $\sigma = 0$ always — a permanent coincident reset).

---

### G. Resolution Strategy (Revised Post-Computation)

The analysis post-computation gives a sharper picture:

**A free $m$ exists iff there is some $m \in \{2,\ldots,e_u-1\}$ not divisible by $d_{e'}$ for any $e' \in E_{\rm non}$.**

For prime $e_u$: $d_{e'} \in \{1, e_u\}$. Runners with $d_{e'}=1$ ($e_u \mid e'$) block ALL $m$; runners with $d_{e'}=e_u$ ($\gcd(e',e_u)=1$) block zero $m$ (no multiples of $e_u$ in $\{2,\ldots,e_u-1\}$). So for prime $e_u$: free $m$ exists $\iff$ $E_{\rm non}$ contains no runner with $e_u \mid e'$.

**The fundamental obstacle** (confirmed computationally): for EVERY composite $n$ and every unit pacemaker $e_u$, the runner $e_{\rm obs} = (n-1)e_u$ is a valid unit speed (gcd$(e_{\rm obs}, n)=1$) with $e_u \mid e_{\rm obs}$ and $\rho'(e_{\rm obs}) = u = n - e_u$. So Case 2 (full blockage) is always realizable by including $e_{\rm obs}$ in $E_{\rm non}$.

**Pacemaker-switch strategy:** For composite $n$ with $\phi(n) = 2$ (i.e., $n \in \{4, 6\}$), there is only ONE viable pacemaker (since $e_u=1$ gives empty range $\{2,\ldots,0\}$), and the obstruction runner $e_{\rm obs}$ is divisible by it. The switch fails completely.

**Three resolution paths:**

**(Path R1): Theorem hypotheses exclude $e_{\rm obs}$.** If Theorem 9.2c's setup (dropped non-unit $d$, unit $e_u = n-u$, specific tuple structure) logically precludes runner $(n-1)e_u$ from appearing in $E_{\rm non}$ (e.g., because the LRC tuple must have $n-1$ DISTINCT speeds with gcd=1 and the specific composition of $E$ in the theorem already forces no speed equal to $(n-1)e_u$), then Case 2 never arises in practice. This requires inspecting the exact domain of Theorem 9.2c.

**(Path R2): Multi-runner zero argument.** When $e_u \mid e'$ and both runners are at position 0 at $b_m$: ALL other runners $e'' \in E_{\rm non} \setminus \{e'\}$ with $e_u \nmid e'' m$ are in the good zone. The question is whether the pair $(e_u, e')$ simultaneously at 0 is ALSO in the good zone for LRC purposes. LRC requires each runner to have $\{e_i t\} \geq 1/n$; if $\{e_u t\} = \{e' t\} = 0$, these two runners fail the LRC condition. So the multi-runner zero does NOT directly give a witness — both runners need to be away from 0.

**(Path R3): Full proof restructure.** Theorem 9.2c in its current form has a genuine gap for tuples where $E_{\rm non}$ contains a runner $e'$ with $e_u \mid e'$. The repair requires either (a) proving the theorem's domain excludes such tuples (Path R1), or (b) a different argument for those tuples — likely routing through Corollary 11.0 (Unit Sub-System Overdetermination) or G-PRES, which may handle the affected branches independently.

**Current status:** Path R1 is the highest-priority investigation — resolved below in §H.

**Summary for small-$e_u$ case:** The existence of a good $m$ is guaranteed by the Good Zone Lemma whenever $E_{\rm non}$ contains no runner $e'$ with $e_u \mid e'm$ for any bad $m$ (equivalently, $\gcd(e', e_u) = 1$ for all $e' \in E_{\rm non}$, i.e., every runner's speed is coprime to $e_u$). Under this condition: ALL $m \in \{2,\ldots,e_u-1\}$ are free. This is the "clean Case 1."

---

### H. Path R1 Resolution (2026-04-24)

**Question:** Does the domain of Theorem 9.2c (composite $n$, Unit-Complete, both dropped runners non-units) logically preclude $e_{\rm obs} = (n-1)e_u$ from appearing in $E_{\rm non}$?

**Answer: NO. The domain does NOT preclude $e_{\rm obs}$. Path R1 is CLOSED (negatively).**

#### H.1 Theorem 9.2c domain — exact statement

From v10.12 §9.2c (lines 556–574): the theorem hypotheses are:
- $n \geq 4$ **composite**
- $d \in \{1,\ldots,n-1\}$ a **non-unit** absent from $E_{\rm non}$
- $d = au$ with every prime divisor of $a$ dividing $n$, $\gcd(u,n)=1$
- $e_u := n - u$ (the pacemaker unit)
- **Unit-Complete**: all $\varphi(n)$ unit residue classes represented in $E_{\rm non}$

There is no further constraint on actual speeds of unit runners in $E_{\rm non}$.

#### H.2 Why $e_{\rm obs} \in E_{\rm non}$ is domain-admissible

1. **Residue of $e_{\rm obs}$:** $e_{\rm obs} = (n-1)e_u \equiv (-1)(n-u) \equiv u-n \equiv u \pmod{n}$. Since $\gcd(u,n)=1$, residue $u$ is a unit.

2. **Unit-Complete requirement:** The Unit-Complete condition mandates that residue class $u$ is represented in $E_{\rm non}$ (since $u$ is a unit). Any actual speed $\equiv u \pmod{n}$ may play that role. The actual speed $(n-1)e_u$ is a valid candidate — nothing in the theorem excludes it.

3. **Uniqueness is not forced:** The theorem does not demand that the runner with residue $u$ has actual speed $u$ (the representative). It merely requires SOME runner with residue $u$ to be present.

#### H.3 The Actual-CG2 failure

In v10.12 Lemma 9.2a$'$ (actual-speed version), the Actual CG2 condition for a retained runner $e$ (with residue $s = e \bmod n$) relative to pacemaker $f$ (residue $u_f$) at the $m$-th floor-reset event is:
$$\sigma_f(e, m) \equiv s + u_f \pmod{n}, \quad \text{where } \sigma_f(e,m) = em \bmod f.$$

For $e_{\rm obs} = (n-1)e_u$, $s = u$, pacemaker $f = e_u$ (actual speed), $u_f = n - u$:
$$\sigma_{e_u}(e_{\rm obs}, m) = (n-1)e_u \cdot m \bmod e_u = 0.$$
Actual CG2: $0 \equiv u + (n-u) = n \equiv 0 \pmod{n}$. **TRUE for all $m \in \{2,\ldots,e_u-1\}$.**

So $e_{\rm obs}$ satisfies Actual CG2 at **every** floor-reset event of $e_u$, covering $r_{\rm dep}$ at each one.

#### H.4 What this means for Theorem 9.2c's proof

The theorem's CG2 uniqueness argument (representative form, line 572): "the unique element $\equiv d \pmod{e_u}$ in $[u,n-1]$ is $d$ itself." This is the *representative-form* version of the CG2 condition. The representative of $e_{\rm obs}$ is $u$, and $u \equiv d \pmod{e_u}$ holds iff $e_u \mid (d-u) = u(a-1)$. Since $\gcd(u,e_u)=1$, this requires $e_u \mid (a-1)$.

But the ACTUAL-SPEED Lemma 9.2a$'$ shows $e_{\rm obs}$ satisfies CG2 for all $m$ regardless of whether $u \equiv d \pmod{e_u}$. The representative-form analysis misses $e_{\rm obs}$ because it computes $\sigma_{e_u}(u, m) = um \bmod e_u$ (using representative $u$ in place of actual speed $(n-1)e_u$), which is NOT generally 0 — the two calculations differ.

**Root cause:** The representative-form CG2 analysis (which drives Theorem 9.2c's uniqueness argument) does not correctly handle actual speeds $e = nq + \rho$ with $q \geq 1$ when $n q \equiv 0 \pmod{e_u}$ but $\sigma_{e_u}(e, m) = (\alpha q + \rho) m \bmod e_u \neq \rho m \bmod e_u$ (the Key Lemma inversion from §F). For $e_{\rm obs}$: $\alpha q + \rho = (n \bmod e_u)(n-1) + u$, and indeed $\sigma = 0$ always (as $e_u \mid (n-1)e_u$).

#### H.5 Concrete verification

Take $n=9$, $e_u=4$, $d=3$ (non-unit dropped). $u = n - e_u = 5$, $e_{\rm obs} = 8 \cdot 4 = 32$.

At $m=2$, pacemaker $b_2 = 2L/4$. Residue of $e_{\rm obs}$: $32 \bmod 9 = 5 = u$. ✓

$\sigma_4(32, 2) = 32 \cdot 2 \bmod 4 = 64 \bmod 4 = 0$.

Actual CG2: $0 \equiv 5 + (9-5) = 9 \equiv 0 \pmod{9}$. ✓

Departing residue $r_{\rm dep} = (m-1)u^{-1} = 1 \cdot 5^{-1} = 2 \pmod{9}$ (since $5 \cdot 2 = 10 \equiv 1$).
Bad set of $e_{\rm obs}$ at $b_2$: $\{-(m)(n-1) \cdot u^{-1}, \ldots\}$... actually floor of $e_{\rm obs}$ at $b_2$: $\lfloor 32 \cdot 2L/4 / L \rfloor = \lfloor 16 \rfloor = 16$.
Bad set: $\{-16 \cdot 5^{-1}, -17 \cdot 5^{-1}\} = \{-32, -34\} \bmod 9 = \{4, 2\} \bmod 9$.
$r_{\rm dep} = 2 \in \{4,2\}$. ✓ **$e_{\rm obs}$ covers $r_{\rm dep}$ at $m=2$.**

#### H.6 Conclusion

| Claim | Verdict |
|---|---|
| Domain of Thm 9.2c excludes $e_{\rm obs}=(n-1)e_u$ from $E_{\rm non}$ | **FALSE** |
| $e_{\rm obs}$ satisfies Actual CG2 for all $m$ (covers $r_{\rm dep}$ at every targeted event) | **TRUE** |
| Thm 9.2c's "unique CG2 runner = $d$" argument holds when $e_{\rm obs} \in E_{\rm non}$ | **FALSE** |
| ERR-C-02 is resolved via Path R1 | **NO** |

**Path R1: CLOSED (negatively).** The gap in Theorem 9.2c is genuine for tuples containing runner $(n-1)e_u$ in $E_{\rm non}$. **Path R3 (proof restructure) is required.**

#### H.7 Path R3 outlook

The repair for the Unit-Complete composite case when $E_{\rm non}$ contains a runner with $e_u \mid e'$ (in particular $e_{\rm obs}$) requires a different argument. Candidates:

- **Corollary 11.0 (Unit Sub-System Overdetermination):** If all $\varphi(n)$ unit classes are present, the unit sub-system is over-determined; there must exist a safe fibre via an incidence count that does not rely on CG2 uniqueness. This is the mechanism that closed G4B-COMP-CAP and may subsume the affected case.

- **Shifted pacemaker:** When $e_u$ is blocked by $e_{\rm obs}$, use a different unit pacemaker $f \in E_{\rm non}$ with $f \nmid (n-1)e_u$ (so $e_{\rm obs}$ does NOT block all floor-resets of $f$). Need to verify Theorem 9.2c's targeted-event argument goes through for general $f$.

- **Two-dropped-runner combinatorics:** The Unit-Complete case drops two non-units; applying Theorem 9.2c to the OTHER dropped non-unit $d'$ (with its own pacemaker $e_{u'} \neq e_u$) may avoid the $e_{\rm obs}$ obstruction entirely if $e_{u'} \nmid (n-1)e_u$.

Status: **open, Path R3**. Blocked on determining which of the above routes closes the case cleanly.

---

## Summary of Lineage C Repair Status

| Error | Core issue | Repair status |
|---|---|---|
| ERR-C-01 (Lemma 11.3a) | Floor formula wrong for $q_e \geq 1$; divisible runner $kn$ has bad $= \mathbb{Z}/n\mathbb{Z}$ at $b^*$ for $k \equiv 1 \pmod n$ | **Partial fix proven**: use $\hat{b} = b^*-1$ for $k=1$ case (confirmed by example); general case needs proof for all $k \equiv 1 \pmod n$ and all $q_e \geq 1$ runners |
| ERR-C-02 (Theorem 9.2c) | (Re-diagnosed 2026-04-24) Physical obstruction = runners with $e_u\mid e'm$ (position 0 at $b_m$); Key Lemma condition inverted; old bad-set diagnosis was a false positive for runner 8 | **Root cause confirmed genuine**: free $m$ exists $\iff$ no $e'\in E_{\rm non}$ has $e_u\mid e'm$. Obstruction runner $e_{\rm obs}=(n-1)e_u$ (residue $u$, unit) satisfies Actual CG2 for ALL $m$ — covers $r_{\rm dep}$ at every targeted event. Domain of Thm 9.2c does NOT exclude $e_{\rm obs}$ (Path R1 CLOSED negatively, §H). **Open: Path R3** — repair via Corollary 11.0, alternate pacemaker, or two-dropped-runner combinatorics. |
| ERR-C-03 (§2.7 Theorem 2.4) | Inherits ERR-B-01/02 gaps at general $p$ | Blocked on ERR-B-01/02 resolution |
