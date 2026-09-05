# §2.4 Rebuild — Chamber-Indexed Safety Framework (Lineage A)

**Status:** Draft v1, 2026-04-19  
**Purpose:** Replaces Lemma 2.5 iff-identity in v11.x (ERR-A-01). Provides the correct structural characterization of safe fibres and re-establishes the downstream §§6/8/10/11 machinery on a sound basis.  
**Relationship to v10.12:** Adopts the actual-speed, chamber-indexed language of v10.12 §§5.3/9.2a'. Merges that architecture into the v11.x narrative structure.

---

## 1. The Problem with Lemma 2.5 (v11.x)

Lemma 2.5 in `lrc_proof_v11_2.md` (lines 140–148) asserts:

> *For $e \in E_{\rm non}$ and $b \in B_{\rm div}$: $(eb \bmod nL) \in [L,(n-1)L]$ iff $[b]_n \notin \mathrm{bad}(e, \lfloor eb/L\rfloor, n)$.*

The proof claims (line 148): "the condition fails iff $\rho_e \cdot [b]_n \equiv -t$ or $-(t+1) \pmod n$."

**Why this is false.** The key identity used is that $[b]_n = b \bmod n$ controls the safety condition. In reality:

$$eb \bmod nL \in [L,(n-1)L] \iff \lfloor eb/L \rfloor \bmod n \in \{1,\ldots,n-2\}.$$

This is a function of $T_e(b) := \lfloor eb/L \rfloor \bmod n$ **alone** — it does not depend on $[b]_n = b \bmod n$ separately. The quantity $[b]_n$ appears in the bad-set definition, but the bad-set condition $[b]_n \notin \mathrm{bad}(e,t,n)$ is NOT equivalent to the safety criterion $T_e(b) \in \{1,\ldots,n-2\}$.

**Explicit failure.** Let $n=5$, $E=(3,5)$, $L=15$, $b=6$:
- $T_3(6) = \lfloor 18/15 \rfloor = 1 \in \{1,2,3\}$ → **SAFE**.
- $[b]_5 = 1$; $\mathrm{bad}(3,1,5) = \{-2,-4\} = \{3,1\}$. Since $1 \in \{3,1\}$, Lemma 2.5 predicts **UNSAFE**. ✗

And $b=4$:
- $T_3(4) = \lfloor 12/15 \rfloor = 0 \notin \{1,2,3\}$ → **UNSAFE**.
- $[b]_5 = 4$; $\mathrm{bad}(3,0,5) = \{0,3\}$. Since $4 \notin \{0,3\}$, Lemma 2.5 predicts **SAFE**. ✗

The error propagates to every downstream result that uses the bad-set framework to characterize per-fibre safety.

---

## 2. Correct Framework — Chamber-Indexed Safety

### 2.1 Definitions

Fix a Case-2 tuple $E = E_{\rm div} \cup E_{\rm non}$ with $L = \mathrm{lcm}(E)$, $N = nL$, and $B_{\rm div} = [L/n, (n-1)L/n] \cap \mathbb{Z}$.

**Floor state.** For $e \in E_{\rm non}$ and $b \geq 0$, define
$$T_e(b) := \left\lfloor \frac{eb}{L} \right\rfloor.$$

**Safety at a fibre.** Fibre $b \in B_{\rm div}$ is **safe for runner $e$** iff $T_e(b) \bmod n \in \{1,\ldots,n-2\}$.  
Fibre $b$ is **globally safe** iff it is safe for every $e \in E_{\rm non}$.

**Chamber.** For $e \in E_{\rm non}$ and integer $t \geq 0$, the *$t$-chamber of $e$* is the real interval
$$C_e(t) := \left[\frac{tL}{e},\, \frac{(t+1)L}{e}\right).$$
On $C_e(t)$, the floor state $T_e(b) = t$ is constant. A chamber is **good** for $e$ iff $t \bmod n \in \{1,\ldots,n-2\}$, and **bad** otherwise.

**Remark.** The integer fibres $B_{\rm div}$ partition into chamber segments $B_{\rm div} \cap C_e(t)$ for varying $t$. At most two consecutive values of $t$ satisfy $t \bmod n \in \{0, n-1\}$ (the unsafe values); the rest are good chambers. The chamber boundaries $tL/e$ are rational with denominator $e$.

### 2.2 Correct Safety Lemma

**Lemma 2.5' (Chamber Safety, proved).** *For $e \in E_{\rm non}$ with $e = nq_e + \rho_e$ ($1 \leq \rho_e \leq n-1$) and $b \in B_{\rm div}$:*
$$b \text{ is safe for } e \quad\iff\quad T_e(b) \bmod n \in \{1,\ldots,n-2\}.$$
*Equivalently, $b$ lies in a good chamber $C_e(t)$ for some $t$ with $t \bmod n \in \{1,\ldots,n-2\}$.*

**Proof.** By definition, $b$ is safe for $e$ iff
$$eb \bmod nL \in [L,(n-1)L].$$
Write $eb = T_e(b) \cdot L + r$ with $0 \leq r < L$ (Euclidean division). Then $eb \bmod nL = T_e(b) \cdot L + r$ if $T_e(b) < n$, and in general $eb \bmod nL \equiv T_e(b) \bmod n \cdot L + r \pmod{nL}$ with $r \in [0,L)$. The condition $eb \bmod nL \in [L,(n-1)L]$ holds iff $T_e(b) \bmod n \in \{1,\ldots,n-2\}$ (since $r$ only contributes fractionally within the $L$-wide strip). $\square$

**Corollary 2.5'a.** The bad-set $\mathrm{bad}(e,t,n)$ is a useful bookkeeping device for which *residue classes are obstructed at floor $t$*, but **it does not characterize safety at a specific fibre** $b$ via $[b]_n$. Correct usage: 

> "Runner $e$ at floor $t$ obstructs residue class $r$ (meaning: any fibre with $T_e(b)=t$ is unsafe for $e$ if additionally $r$ is needed elsewhere)" — this is a residue-level bookkeeping tool, NOT an iff about $b$.

**Corollary 2.5'b (Base fibre).** At $b_0 = L/n$, one has $T_e(b_0) = \lfloor e/n \rfloor = q_e$ exactly. For a unit runner ($\gcd(\rho_e,n)=1$):
$$\mathrm{bad}(e,q_e,n) = \{-q_e \rho_e^{-1},\; -(q_e+1)\rho_e^{-1}\} \pmod n.$$
This describes which residue classes $r$ runner $e$ blocks **at floor $q_e$** — useful for identifying uncovered residues, but the coverage of residue $r_d$ by runner $e$ at $b_0$ is determined by whether $r_d \in \mathrm{bad}(e,q_e,n)$, NOT by $[b_0]_n \in \mathrm{bad}(e,q_e,n)$.

---

## 3. What the Bad-Set IS Good For

The bad-set $\mathrm{bad}(e,t,n)$ remains the correct tool for the following residue-level argument (which is what v10.12 §§2.2–2.4 actually does):

**Goal (restated correctly).** We want to show: there exist $b \in B_{\rm div}$ and at least one runner $e$ such that $b$ is globally safe (all runners simultaneously in good chambers).

**Residue coverage argument.** Define the coverage multiplicity at floor configuration $(t_e)_{e \in E_{\rm non}}$:
$$C_r(t_1,\ldots,t_k) := \#\{e \in E_{\rm non} : r \in \mathrm{bad}(e,t_e,n)\}.$$
A global configuration $(t_e)$ is "blocking" iff $\bigcup_e \mathrm{bad}(e,t_e,n) = \mathbb{Z}/n\mathbb{Z}$. We want to show no globally consistent blocking configuration can be realised simultaneously for every $b \in B_{\rm div}$.

**The correct argument structure (two steps):**

*Step 1 (Static — missing unit class).* If some unit residue class $d$ is absent from $R_{\rm non} := \{\rho_e : e \in E_{\rm non}, \gcd(e,n)=1\}$, then at the base fibre $b_0 = L/n$, the residue $r_d = -d^{-1} \bmod n$ is uncovered:
- Every unit runner $e$ has $q_e \geq 0$; at $b_0$ its bad set is $\{-q_e\rho_e^{-1}, -(q_e+1)\rho_e^{-1}\}$.
- For $q_e = 0$: bad set is $\{0, -\rho_e^{-1}\}$. Since $d \notin R_{\rm non}$, no runner has $\rho_e = d$, so $r_d = -d^{-1}$ is not in any bad set at floor 0.
- For $q_e \geq 1$: requires a separate check (Lemma 5.1a of v10.12: runner $e$ covers $r_d$ iff $\rho_e \equiv q_e d$ or $(q_e+1)d \pmod n$). This step is handled by the sliding-window chain (§6) which shows the uncovering propagates.

*Step 2 (Dynamic — unit-complete).* If every unit residue class is present, the floor-reset mechanism (§9) shows a departing residue cannot be fully absorbed. This step is unaffected by the Lemma 2.5 error: it operates on the floor state $T_e(b)$ directly, using the actual-speed bad-set at the floor-reset point.

---

## 4. Rebuilding the Downstream Connection

### 4.1 Sliding-Window (§6) — What Survives

The §6 sliding-window proof (Proposition 6.1, Coverage-Transfer Lemma 6.0) argues: as $b$ moves through $B_{\rm div}$, the union $\bigcup_e \mathrm{bad}(e,T_e(b),n)$ can only change at chamber-boundary ("floor-reset") points $b = tL/e$ for some $e,t$. Between resets, all bad sets are constant.

This is **entirely correct** and does not depend on Lemma 2.5. The fix: replace every invocation of "fibre $b$ is safe iff $[b]_n \notin \bigcup_e \mathrm{bad}(e,T_e(b),n)$" with the correct statement "fibre $b$ is safe iff every runner is in a good chamber, i.e., $T_e(b) \bmod n \in \{1,\ldots,n-2\}$ for all $e$."

The sliding-window argument then becomes: the set of globally safe fibres $b$ is the intersection $\bigcap_e \mathcal{G}_e$ where $\mathcal{G}_e = \bigcup_{t \bmod n \in \{1,\ldots,n-2\}} (C_e(t) \cap B_{\rm div})$. Each $\mathcal{G}_e$ is a union of $\lfloor (n-2)/n \cdot |B_{\rm div}|/\text{chamber-length}\rfloor$ intervals. The coverage-transfer identity (Lemma 6.0) governs how $\mathcal{G}_e$ changes as $b$ enters a new chamber.

**Key fix for Lemma 6.0:** Lemma 6.0 as stated uses the bad-set to track which residues are "in play." The correct statement: at each floor-reset event $b = mL/e_u$ for a unit runner $e_u$, the chamber changes from $C_{e_u}(m-1)$ to $C_{e_u}(m)$. The bad set of $e_u$ changes from $\{-(m-1)\rho_{e_u}^{-1}, -m\rho_{e_u}^{-1}\}$ to $\{-m\rho_{e_u}^{-1}, -(m+1)\rho_{e_u}^{-1}\}$. The "departing" residue is $-(m-1)\rho_{e_u}^{-1}$ and the "arriving" residue is $-(m+1)\rho_{e_u}^{-1}$. This is a local description of the residue-level coverage change and remains valid. The sliding-window argument tracks whether the departing residue is covered by another runner — this is exactly the CG1/CG2 mechanism.

### 4.2 Theorem 8.2 (§8) — L-Bound Fix

The L-bound "L < n(n-1) equivalently L ∈ {n, 2n}" (ERR-A-03) is a separate error. Fix: replace with the correct classification of small-L cases:
- $L = n$: only possible for $n \in \{3,4\}$ (as in v10.12 Proposition 5.1).
- $L = 2n$: handled by Proposition 5.1, Case B.
- $L \in \{3n, \ldots, (n-2)n\}$: these small-L cases were omitted; they require either a dedicated subcase or an appeal to the harness (explicit finite check). For prime $n$, these are exactly the cases where $L = kn$ with $k \in \{3,\ldots,n-2\}$, equivalently where $E_{\rm div} \subseteq \{n\}$ and $E_{\rm non}$ has $\mathrm{lcm} = kn$ for small $k$.

**Fix strategy for §8:** Add a "small-L bridge" proposition that handles $L < n(n-1)$ as a finite enumeration (n ≤ 30 by harness, analytically for larger n using the dropped-unit argument with $q_e = 0$).

### 4.3 Lemma 10.2 (§10) — Floor-Formula Fix

The correct formula (ERR-A-02 fix): for $e = nq_e + \rho_e$ on the late window $J = [(n-2)L/(n-1), (n-1)L/n]$:
$$T_e(b) = \left\lfloor \frac{eb}{L} \right\rfloor = n q_e + (\rho_e - 1) + \left\lfloor \frac{\rho_e \cdot b - L}{L} \right\rfloor.$$
On $J$: $b \approx (n-1)L/n$, so $\rho_e b/L \approx \rho_e(n-1)/n \in [1 - 1/n, n-1-1/n]$ for $\rho_e \in \{1,\ldots,n-1\}$. The floor $\lfloor \rho_e b/L \rfloor$ therefore equals $\lfloor \rho_e(n-1)/n \rfloor$ which ranges from 0 (for $\rho_e=1$) to $n-2$ (for $\rho_e=n-1$). The full formula:
$$T_e(b) \bmod n \equiv \rho_e - 1 - q_e \pmod n \quad \text{on } J, \text{ for } q_e \geq 0.$$
The paper's formula $\rho_e - 1$ is correct only for $q_e = 0$ ($e < n$). For $q_e \geq 1$ (speeds exceeding $n$), the corrected value $\rho_e - 1 - q_e \bmod n$ must be used throughout.

**Impact on §10.** The residue $s_d = d^{-1} - 1 \bmod n$ that the lemma claims is uncovered on $J$ must be checked against the corrected formula. For $q_e = 0$ runners, the argument stands. For $q_e \geq 1$ runners, the bad set at floor $\rho_e - 1 - q_e$ is $\{-((\rho_e-1-q_e)\rho_e^{-1}),-((\rho_e-q_e)\rho_e^{-1})\}$ — different from the paper's $\{d^{-1}-1, d^{-1}\}$. The conclusion "$s_d$ is uncovered on $J$" must be re-verified for each $q_e \geq 1$ runner.

---

## 5. Summary — Minimal Repair Checklist

| Item | Error | Fix | Effort |
|---|---|---|---|
| Lemma 2.5 | iff via $[b]_n$ — FALSE | Replace with Lemma 2.5' (chamber safety, §2.2 above) | Replace 1 lemma, ~10 lines |
| Usage of bad-set to characterize fibre safety | Incorrect invocation throughout §§5.1b, 6, 8, 10, 11 | Change to "runner $e$ at floor $T_e(b)$ obstructs residue $r$"; remove iff claim | ~5 proof passes |
| Lemma 6.0 statement | OK structurally; fix invocation context | Clarify bad-set tracks residue obstruction, not fibre safety | Minor restatement |
| Theorem 8.2 L-bound | "L ∈ {n,2n}" misses $\{3n,\ldots,(n-2)n\}$ | Add small-L bridge proposition | 1 new proposition |
| Lemma 10.2 floor formula | $\rho_e - 1$ misses $-q_e$ | Replace formula; re-check $s_d$ conclusion for $q_e \geq 1$ runners | Per-case arithmetic |
| Theorem 11.1 Case A | Same L-bound error | Same fix as Theorem 8.2 | Shared with above |
| §12.2 certificate claim | "no certificate" vs harness invocations | Either make small-L analytic or disclose harness use | Documentation |

**Critical path.** Lemma 2.5' → sliding-window re-statement (§6) → L-bound bridge (§8) → Lemma 10.2 corrected formula (§10) → Theorem 11.1 Case A (§11). These are sequential. The §9 floor-reset machinery (Theorem 9.2c, CG1/CG2) is independent and survives.

---

## 6. Candidate New Lemma 2.5' — Final Statement

**Lemma 2.5' (Chamber-Safe Characterization).** *Let $E$ be a Case-2 tuple with $L = \mathrm{lcm}(E)$, $n \geq 3$, and $B_{\rm div} = [L/n,(n-1)L/n] \cap \mathbb{Z}$. For $e \in E_{\rm non}$ and $b \in B_{\rm div}$, define the floor state $T_e(b) = \lfloor eb/L \rfloor$. Then:*

1. *$b$ is safe for runner $e$ if and only if $T_e(b) \bmod n \in \{1,\ldots,n-2\}$.*
2. *$T_e(b)$ is constant on each chamber $C_e(t) = [tL/e,(t+1)L/e)$ and changes by $\pm 1$ only at chamber boundaries $b = tL/e$.*
3. *For unit $e$ ($\gcd(e,n)=1$): the blocked residues at floor $T$ are $\mathrm{bad}(e,T,n) = \{-T\rho_e^{-1}, -(T+1)\rho_e^{-1}\} \pmod n$ (a 2-element set, independent of $b$ within the chamber).*
4. *For non-unit $e$ with $g = \gcd(e,n) > 1$: $\mathrm{bad}(e,T,n)$ is a coset of $H_g = (n/g)\mathbb{Z}/n\mathbb{Z}$ when $g \mid T$, and $\emptyset$ otherwise.*

*The criterion "$[b]_n \notin \mathrm{bad}(e,T_e(b),n)$" is NOT equivalent to "$b$ is safe for $e$" in general; it is a residue-level bookkeeping statement about which residue classes are blocked at floor $T_e(b)$, applicable only in the context of coverage multiplicity arguments (§2.4) and not as a fibre-by-fibre safety test.*

**Proof.** Points 1–4 are direct from the Euclidean division $eb = T_e(b) \cdot L + r$, $0 \leq r < L$, and the definition of $\mathrm{Sol}(e,j,n)$ for unit and non-unit $e$. The final disclaimer follows from the counterexamples at $n=5$, $b=6$ (safe, predicted unsafe) and $b=4$ (unsafe, predicted safe). $\square$
