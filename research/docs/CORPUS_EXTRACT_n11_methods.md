# Corpus extract — the two n=11 methods

**Date:** 2026-09-07
**Type:** reference index. Extraction only — no quality assessment, no defect hunt.
**Rule applied:** every claim below is a verbatim quote with `file:line`, obtained by
opening the file at that line. Ellipses are marked `…`. Where two lines of the same file
disagree, both are quoted and neither is adjudicated.

---

## A. The two methods

There are **exactly two** distinct methods in the corpus surveyed. They share two
ingredients verbatim (the Complementary Pairs Theorem and the Coupling Principle) and
diverge completely after that point: the divergence is in what is done with the unclaimed
slot `I₉`, in what is held fixed, and in the scope of the resulting statement.

| | Method 1 | Method 2 |
|---|---|---|
| Name used in the files | "Route 3 architecture" / "Algebraic Lemma" | no internal name; the paper's own structure words are "the algebraic core", "gap obstruction lemmas", "the static core", "shift-invariant closure" |
| Files | `lrc_n11_algebraic_lemma_v1.md` + `lrc_n11_incompatibility_v1.md` | `eleven_lonely_runners_v33.md` (and the same architecture in `lrc_n11_ap_paper_v30.md`) |
| Scope of its own conclusion | one sign class (`++------`) | all speed vectors; `2^8 = 256` sign classes |
| Closing device | an exact rational incompatibility on `a₂` after locking `a₉`, `a₆` at resonance | an exhaustive filler table (PSM / Chain A / Chain B / infeasible) applied per sign class, then shift-invariance |
| Output | an explicit rational witness time `t* = 69/275` (Case C) plus `GF > 0` | `GF(I_k) > 0` for some slot; no single explicit witness time |

### Method 1 — Complementary Pairs + Coupling + Baton-Pass Certificate + Runner-2 Incompatibility

**Carried by:** `lrc_n11_algebraic_lemma_v1.md` (§0–§9), with its Main Claim 5.1 proved in
`lrc_n11_incompatibility_v1.md`.

**Main theorem statements, verbatim:**

`lrc_n11_algebraic_lemma_v1.md:213`
> **Theorem 6.1 (GF > 0 for ++------class — Main Result).** *For any CB configuration in the ++------ sign class with $|\delta_j| \leq C$ for some absolute constant $C$, the good fraction $\mathrm{GF}(W_0) > 0$. Equivalently, there exists an explicit rational $t^* \in W_0$ where all runners are simultaneously lonely.*

`lrc_n11_incompatibility_v1.md:169-171`
> **Theorem 4.1 (Runner 2 Incompatibility — Main Claim 5.1).** *For any CB configuration in the ++------ sign class with $a_9 = 25/3$ and $a_6 = 40/7$:*
> $$\mathrm{GF}(I_4) + \mathrm{GF}(I_9) > 0.$$
> *Equivalently, there is no assignment of runner speeds simultaneously closing both I₄ and I₉.*

The triple named in the task appears as:

- Complementary Pairs — `lrc_n11_algebraic_lemma_v1.md:27-29`
  > **Theorem 1.1 (Complementary Pairs).** *In the AP limit ($a_j = j$ for all $j$), each runner $j \in \{2,\ldots,9\}$ lies at position $j t_m \bmod 1 \in \{1/11, 10/11\}$ at exactly two witnesses:*
  > $$m_j^- = j^{-1} \bmod 11 \quad (position = 1/11) \qquad \text{and} \qquad m_j^+ = 10j^{-1} \bmod 11 \quad (position = 10/11).$$
- Coupling Principle — `lrc_n11_algebraic_lemma_v1.md:59`
  > **Lemma 2.2 (Coupling Principle).** *When $a_j$ changes, ALL bad intervals $B_{j,k}$ scale uniformly (all endpoints $\propto 1/a_j$). There is no way to shift $B_{j,k_1}$ without simultaneously shifting $B_{j,k_2}$ for $k_2 \neq k_1$.*
- Baton-Pass Certificate — `lrc_n11_algebraic_lemma_v1.md:158-159`
  > **Theorem 4.1 (Baton-Pass Certificate, Case C).** *Suppose $a_9 = 25/3$ and $a_6 = 40/7$ (slot $I_1$ fully closed). Define the rational time:*
  > $$t^* = \frac{69}{275}.$$

**Mechanism, in the files' own vocabulary.** Fix the *resonance* speeds `a₉ = 25/3`,
`a₆ = 40/7` that close the two edges of slot `I₁` (`Corollary 2.3`, `:63-65`). By the
Coupling Principle the whole *chain* of each of those two runners is then pinned, and the
files tabulate exactly which slots each chain *visits* and *skips* (`Prop 3.1`, `:97-108`;
`Prop 3.2`, `:112-122`), producing *forced gaps* `G₆` of width `161/2200` (`Lemma 3.3`)
and `G₃` of width `1/40` (`Lemma 3.4`). The residual burden falls on runner 2, which by
Complementary Pairs owns `I₄` and `I₅`. Closing `I₄` pushes `a₂` up; bridging the left gap
`J₉` of the unclaimed `I₉` pushes `a₂` down; the two rational bounds cross. The excluded
alternative absorbers (runners 3, 5, 7) are each knocked out by the *baton-pass* good
window at `t* = 69/275` in `I₂` or by an `I₇` reach failure. Where the incompatibility does
not apply (`a₉ < 25/3` or `a₆ > 40/7`), an explicit `I₁` edge gap is used instead
(`Corollary 5.1`, `lrc_n11_incompatibility_v1.md:192-196`).

### Method 2 — Window / pacemaker-slot method (gap obstruction + universal blocking + shift invariance)

**Carried by:** `eleven_lonely_runners_v33.md`; the same architecture, section for section,
in `lrc_n11_ap_paper_v30.md`.

**Main theorem statement, verbatim:** `eleven_lonely_runners_v33.md:41-43`
> **Theorem 1.1 (Main Theorem).** *For any ten distinct positive real speeds
> $e_1<\cdots<e_{10}$, there exists $t>0$ such that*
> $$\|e_i t\|\ge \frac{1}{11}\qquad(i=1,\ldots,10).$$

Its load-bearing internal theorem is `eleven_lonely_runners_v33.md:548-553`
> **Theorem 5.5 (Universal Blocking).** *Let $[g_L,109/110]\subset I_9$ be any nonempty right gap with $g_L\in[100/110,109/110)$. … No assignment of runners $3,\ldots,8$ can cover this gap while keeping $\mathrm{GF}(I_s)=0$ for every other slot.*

and its closure statement `eleven_lonely_runners_v33.md:761-762`
> **Theorem 7.3 (Shift-invariant static core).** *Let $C_m\subset W_{\mathrm{ref}}$ be any complete pacemaker cycle. Then some slot $I_k^{(m)}$ has positive good fraction.*

**Mechanism, in the paper's own vocabulary.** Normalise `a_i = 10e_i/e_10`, `a₁₀ = 10`, and
abandon the AP witness family for the *isolation window* `W_ref = [1/(11a₁), 10/(11a₁)]`,
sliced into *pacemaker cycles* `C_m` each carrying nine *pacemaker slots* `I₁…I₉`
(`:147-170`). Assume a *completely blocking* configuration, i.e. `GF(I_s) = 0` for all
nine slots (`:176-177`). *Sign-range containment* (Lemma 5.1) confines every runner to
`a_j ∈ (j-1, j+1)`, leaving `2^8 = 256` *sign classes*. Complementary Pairs leaves `I₉`
unclaimed, so some runner must absorb it *off schedule*; the Coupling Principle makes that
move non-local. The three *gap obstruction lemmas* name the slot that opens in each case:
*Primary Slot Miss* (negative sign — the interval overshoots its own primary slot), *Chain
A* (runner 3, `σ₃=+1`, forces `a₈ ≥ 8a₃/3` then misses `I₈` by `1/50`), and *Chain B*
(runner 4, `σ₄=+1`, forces `a₇ ≥ 7a₄/4 > 7` against `a₇ ≤ 560/87 < 7`, an outright
incompatibility). *Universal Blocking* exhausts the filler table; the *static core*
(Section 6) splits on `σ₂` and, for `σ₂=+1`, decomposes the parameter space into seven
`α`/`β` regions in `a₉`. *Shift invariance* (Section 7) then propagates the single-cycle
result to every cycle, and `Corollary 7.4` extracts the witness.

### Relationship between the two, stated plainly

The `Complementary Pairs` theorem and the `Coupling Principle` are common to both; the
statements are near-identical — Complementary Pairs at
`lrc_n11_algebraic_lemma_v1.md:27-44` vs `eleven_lonely_runners_v33.md:287-309`, and the
Coupling Principle at `lrc_n11_algebraic_lemma_v1.md:59` vs
`eleven_lonely_runners_v33.md:277-281`. What differs is
everything downstream. Method 1 pins two speeds at resonance and derives a *numerical*
contradiction on `a₂` valid in one sign class; Method 2 leaves all eight free speeds inside
their sign-range boxes and derives a *structural* contradiction valid in all 256. Method 1
produces a named rational witness time; Method 2 produces only positivity of the good
fraction. The papers do not cite the algebraic-lemma files, and the algebraic-lemma files
cite "the AP paper" (`lrc_n11_algebraic_lemma_v1.md:12`: *"we work in the classical EFN
framework (§7 of the AP paper v8)"*), i.e. an earlier lineage than v30/v33.

### `lrc_n11_ap_paper_v30.md` vs `eleven_lonely_runners_v33.md` — confirmed different files, same method

The project record's note that these are different papers is **confirmed as to title and
framing, not as to method**. They carry the same argument.

- Titles differ. `lrc_n11_ap_paper_v30.md:1` — `# The Lonely Runner Conjecture for n = 11`;
  `eleven_lonely_runners_v33.md:1` — `# Eleven Lonely Runners: Complementary Pairs and the Coupling Principle`.
- Dates/status differ. `lrc_n11_ap_paper_v30.md:4-5` — *"**Date:** 2026-03-30 / v30"*,
  *"**Status:** Submission draft — blocker cleanup and proof-derivation pass"*;
  `eleven_lonely_runners_v33.md:4` — *"2026-04-06 · v33"*.
- Section 7 is renamed. v30 `:642` `## 7. Phase-Uniform Closure in $W_{\rm ref}$`,
  `:646` *"Lemma 7.1 (bad-interval width is phase independent)"*; v33 `:720`
  `# 7. Shift-Invariant Closure in $W_{\mathrm{ref}}$ (All Cycles)`, `:732` *"Lemma 7.1."*
  with the same content. v30 `:656` proves it in one sentence — *"No step depends on a
  specific absolute phase."*; v33 `:744-752` expands it to a paragraph naming `k_m = k_0+m`.
- Section 5 is renamed: v30 `:226` `## 5. The Analytical Engines`; v33 `:361`
  `# 5. Gap Obstruction Lemmas`.
- v33 adds an exhaustiveness paragraph the v30 seven-region lemma does not have.
  `eleven_lonely_runners_v33.md:681-684` — *"*Exhaustiveness.* The seven regions partition
  the interval $(a_9^{\min},a_9^{\max})=(8,10)$ … exhaustively and disjointly"*. Grep for
  `exhaustiv` in v30 returns only `:780`, the three-case statement.
- v33 adds the ownership-scoping remarks. `eleven_lonely_runners_v33.md:91-94` and
  `:337-347` (`Remark 4.3`) have no counterpart in v30 §4.2 (`:193-222`).
- v33 adds `Remark 2.1 (Terminology guide)` (`:195-205`) and `Appendix C` as a separate
  numbered appendix; v30 folds the irrational case into `## 8. The Irrational Case and the
  Full Proof` (`:699`).
- The mathematics that carries the proof is shared verbatim, constants included: both give
  `Complementary Pairs` with the same four-pair table (v30 `:201-210`, v33 `:292-300`),
  the same `Runner-2 Elimination Lemma` with `114/1417 > 0` (v30 `:520-536`, v33 `:604-616`),
  the same `Negative-Branch Gap Lemma` minimum `538/54395` and the same four-row
  `(σ₃,σ₄)` table (v30 `:538-568`, v33 `:618-642`), the same `Universal Blocking` filler
  table (v30 `:1197-1201`, v33 `:561-569`), the same `Corollary 7.4` with `79/11 > 1`
  (v30 `:670-695`, v33 `:771-781`), the same `Example 3.1` with witness `t = 4/17` and
  minimum `13/119` (v30 `:140-175`, v33 `:229-258`), and the same Appendix B campaign table
  — `1.1×10⁹` configurations, `0` failures, `34` exact checks (v30 `:1273-1288`,
  v33 `:1087-1120`).

---

## B. The free parameter

### Method 1 — the free parameter is `a₂`; `a₉` and `a₆` are pinned at resonance

Held fixed — `lrc_n11_incompatibility_v1.md:12`
> Fix $a_9 = 25/3$ and $a_6 = 40/7$ (I₁-closing conditions, Corollary 2.3 of the algebraic lemma).

and `lrc_n11_algebraic_lemma_v1.md:74`
> Fix $a_9 = 25/3$ and $a_6 = 40/7$ (the conditions that close $I_1$'s edges). By the Coupling Principle (Lemma 2.2), the chains for runners 9 and 6 are now fixed, and we can compute exactly where they land in each subsequent slot.

What varies, and the two constraints it must straddle —
`lrc_n11_incompatibility_v1.md:65-67`
> ### Lemma 3.1 (I₄ forces $a_2 \geq 20/9$)
>
> *Suppose I₄ is closed (GF(I₄) = 0). Then $a_2 \geq 20/9$.*

`lrc_n11_incompatibility_v1.md:119-121`
> ### Lemma 3.2 (I₉ forces $a_2 \leq 575/261$)
>
> *Suppose I₉ is closed (GF(I₉) = 0). Then $a_2 \leq 575/261$.*

`lrc_n11_incompatibility_v1.md:184`
> Since no value of $a_2$ can satisfy both $a_2 \geq 20/9$ and $a_2 \leq 575/261$, we cannot have GF(I₄) = GF(I₉) = 0. Therefore GF(I₄) + GF(I₉) > 0. $\square$

`lrc_n11_incompatibility_v1.md:59` (the motion of `a₂`, explicitly)
> For $a_2 = 2$: $B_{2,1} = [21/22, 23/22] \approx [0.955, 1.045]$. As $a_2$ increases, $B_{2,1}$ shifts left. …

A secondary free parameter, `a₃`, governs the Case C₁ / Case D split —
`lrc_n11_algebraic_lemma_v1.md:172-175`
> The window is positive iff:
> $$\frac{10}{11 a_3} > \frac{69}{275} \iff a_3 < \frac{10 \times 275}{11 \times 69} = \frac{2750}{759} \approx 3.623.$$
>
> This is **Case C₁**: both $I_1$ is closed AND $a_3 < 2750/759$.

and `a₉`, `a₆` themselves are the Case A/B/C parameter before being pinned —
`lrc_n11_algebraic_lemma_v1.md:67-68`
> *When $a_9 < 25/3$: left edge gap $= 12/110 - 10/(11a_9) > 0$ …*
> *When $a_6 > 40/7$: right edge gap $= 12/(11a_6) - 21/110 > 0$ …*

### Method 2 — the free parameter is `a₉` (region decomposition) with `a₂` squeezed between two bounds; `a₁₀` fixed by normalisation, each `a_j` boxed by its sign

Held fixed — `eleven_lonely_runners_v33.md:149-150`
> Fix $n=11$ throughout. For a speed vector $e_1<\cdots<e_{10}$, normalise by setting
> $$a_i := \frac{10e_i}{e_{10}},\qquad a_{10}=10.$$

Boxed — `eleven_lonely_runners_v33.md:371-372`
> **Lemma 5.1 (Sign-range containment).** *In every completely blocking configuration,*
> $$a_j \in (j-1,\,j+1)\qquad(j=2,\ldots,9).$$

`eleven_lonely_runners_v33.md:400-401`
> **Consequence.** Every completely blocking configuration belongs to exactly one of the
> $2^8=256$ sign classes determined by $(\sigma_2,\ldots,\sigma_9)$.

What varies and drives the argument — `eleven_lonely_runners_v33.md:646-647`
> We now assume $\sigma_2=+1$. The pair $(2,9)$ carries the sharpest tension: closing $I_4$
> drives $a_2$ upward, while bridging $I_9$ drives $a_2$ downward.

`eleven_lonely_runners_v33.md:649-654` (the lower bound is a function of `a₉`)
> **Lemma 6.3 (The $I_4$ lower bound on $a_2$).** *Closing $I_4$ requires*
> $$a_2 \ge L(a_9) :=
>   \begin{cases}
>     20/9, & a_9 < 86/9,\\[2pt]
>     2a_9/9, & a_9 \ge 86/9.
>   \end{cases}$$

`eleven_lonely_runners_v33.md:694-697` (the upper bound is a function of `a₉`)
> $$\frac{23}{11a_2}\ge \frac{87}{11a_9} \implies a_2\le\frac{23a_9}{87}\quad
>   (B_{9,7}\text{ regime}).$$
> Similarly, $a_2\le 23a_9/98$ in the $B_{9,8}$ regime and for $\sigma_9=+1$.

`eleven_lonely_runners_v33.md:668-669` (the seven regions are intervals in `a₉`)
> **Lemma 6.4 (The $I_9$ decomposition).** *Under $\sigma_2=+1$, the parameter space splits
> into seven regions:*

A third varying quantity is the residual gap's left endpoint `g_L` —
`eleven_lonely_runners_v33.md:548-549`
> **Theorem 5.5 (Universal Blocking).** *Let $[g_L,109/110]\subset I_9$ be any nonempty
> right gap with $g_L\in[100/110,109/110)$.*

**Note on the contrast.** In Method 1 the incompatibility on `a₂` is between two *constants*
(`20/9` and `575/261`). In Method 2 the same tension is between two *functions of `a₉`*
(`L(a₉)` and `23a₉/87` or `23a₉/98`), which is why Method 2 must decompose the `a₉` range
into `α` regions (bounds incompatible) and `β` regions (bounds compatible, residual gap
survives and Universal Blocking takes over).

---

## C. Where primality enters

`11` is prime, and the corpus uses that fact in exactly one place in each method: the
derivation of the witness labels `m_j^± ≡ ±j⁻¹ (mod 11)` and the pairing `j ↔ 11-j`.
Neither file uses the words "primitive root" or "cyclic group": grep for `primitive root`
and `cyclic` over `eleven_lonely_runners_v33.md` and `lrc_n11_ap_paper_v30.md` returns
nothing. The unit-group structure is used implicitly, through the existence of `j⁻¹` for
every `j ∈ {2,…,10}`.

### USES PRIMALITY

1. `eleven_lonely_runners_v33.md:84-89` — **USES PRIMALITY** (explicitly; existence of `j⁻¹` and the `j ↔ 11-j` involution)
   > The prime modulus $11$ imposes a rigid algebraic structure. At the AP limit $a_j=j$, each
   > runner $j\in\{2,\ldots,9\}$ has two witness labels $m_j^{\pm}\equiv\pm j^{-1}\pmod{11}$.
   > Because $11$ is prime, runners $j$ and $11-j$ share the same two labels: they form a
   > *complementary pair*. The four pairs — $(2,9)$, $(3,8)$, $(4,7)$, $(5,6)$ — together
   > own eight primary slots $I_1,\ldots,I_8$, two per pair. Slot $I_9$ is left unclaimed:
   > no pair's label corresponds to it.

2. `eleven_lonely_runners_v33.md:287-290` — **USES PRIMALITY** (the inverse must exist for every `j` in `2..9`)
   > At the AP limit $a_j=j$, the first lower-boundary and upper-boundary witnesses are
   > $$m_j^- \equiv j^{-1}\pmod{11},\qquad m_j^+ \equiv 10j^{-1}\pmod{11}.$$
   > Since $(11-j)^{-1}\equiv -j^{-1}\pmod{11}$, the runners $j$ and $11-j$ share the same
   > two witness labels.

3. `eleven_lonely_runners_v33.md:304-305` — **USES PRIMALITY** (the eight inverses exist and are a permutation of `2..9`)
   > *Proof.* Compute inverses modulo $11$:
   > $$2^{-1}=6,\ 3^{-1}=4,\ 4^{-1}=3,\ 5^{-1}=9,\ 6^{-1}=2,\ 7^{-1}=8,\ 8^{-1}=7,\ 9^{-1}=5.$$

4. `eleven_lonely_runners_v33.md:325-327` — **USES PRIMALITY** (named as the source of the symmetry)
   > Each pair owns two non-adjacent slots (one in the first half, one in the second). The
   > prime structure ensures symmetry: slot $I_s$ and slot $I_{9-s}$ are always owned by the
   > same pair. Slot $I_9$ is not covered by any pair's AP-limit witness labels.

5. `eleven_lonely_runners_v33.md:349-351` — **USES PRIMALITY** (the file's own statement of the primality dependence's generality)
   > > **Remark 4.4.** The complementary-pair structure generalises to other odd primes; the
   > > extension to general $n$ and the question of algorithmic automation are addressed in a
   > > subsequent paper.

6. `eleven_lonely_runners_v33.md:16-20` and `:60-63` and `:269` and `:811-812` — **USES PRIMALITY** (the abstract, the introduction, the case-reduction handoff, and the final assembly all name the prime modulus as the source of the structure)
   > `:16-18` The commensurable case rests on two structural facts: the prime modulus $11$ forces the runners $2,\ldots,9$ into four **complementary pairs**, …
   > `:269` This is where the structure of the prime modulus $11$ becomes decisive.
   > `:811-812` The algebraic structure of the prime modulus $11$ (Complementary Pairs, Section 4) forces the unclaimed slot $I_9$, …

7. `lrc_n11_ap_paper_v30.md:197-199` and `:212-214` — **USES PRIMALITY** (same two steps, v30 wording)
   > `:197` m_j^- \equiv j^{-1}\pmod{11},\qquad m_j^+\equiv 10j^{-1}\pmod{11}.
   > `:199` Since $(11-j)^{-1}\equiv -j^{-1}\pmod{11}$, the runners $j$ and $11-j$ share the same two witness labels.

8. `lrc_n11_algebraic_lemma_v1.md:27-29` — **USES PRIMALITY** (Method 1's version of the same step)
   > **Theorem 1.1 (Complementary Pairs).** *In the AP limit ($a_j = j$ for all $j$), each runner $j \in \{2,\ldots,9\}$ lies at position $j t_m \bmod 1 \in \{1/11, 10/11\}$ at exactly two witnesses:*
   > $$m_j^- = j^{-1} \bmod 11 \quad (position = 1/11) \qquad \text{and} \qquad m_j^+ = 10j^{-1} \bmod 11 \quad (position = 10/11).$$

9. `lrc_n11_algebraic_lemma_v1.md:42` — **USES PRIMALITY** (the complementarity identity `m_j^+ + m_j^- = 11j⁻¹ ≡ 0`, and the inverse-of-`11-j` step)
   > **Proof.** From Lemma 4.2' of the AP paper: runner $j$ has $r_j(m) \equiv jm \pmod{11} = 1$ (lower boundary) iff $m \equiv j^{-1} \pmod{11}$, … $m_j^+ + m_j^- = 10j^{-1} + j^{-1} = 11j^{-1} \equiv 0 \pmod{11}$, so $m_j^+ + m_j^- = 11$ … Since $j \leftrightarrow 11-j$ maps $j^{-1} \leftrightarrow (11-j)^{-1} \equiv -j^{-1} \equiv 11-j^{-1}$, runners $j$ and $11-j$ own the same pair of slots …

10. `lrc_n11_algebraic_lemma_v1.md:44-46` — **USES PRIMALITY** (uses `10⁻¹` to show `I₉` is unclaimed; this is the step that creates the object the whole proof turns on)
    > **Corollary 1.2 (Slot $I_9$ is unclaimed).** *No runner $j \in \{2,\ldots,9\}$ has $m_j^- = 10$ or $m_j^+ = 10$ …*
    >
    > **Proof.** $m_j^- = 10 \Rightarrow j^{-1} \equiv 10 \pmod{11} \Rightarrow j \equiv 10^{-1} \equiv 10 \pmod{11}$, so $j = 10$. …

### does not use primality

Every remaining step is interval arithmetic in `ℚ`. `11` appears throughout as the modulus
of the loneliness threshold `1/11` and in the denominators `110`, `275`, `440`, but no step
below invokes invertibility, a primitive root, or the group `(ℤ/11)ˣ`.

- `eleven_lonely_runners_v33.md:153-157` bad-interval formula — **does not**.
- `eleven_lonely_runners_v33.md:277-283` `Lemma 4.1 (Coupling Principle)`, proved *"Immediate from the endpoint formula."* — **does not**.
- `eleven_lonely_runners_v33.md:371-398` `Lemma 5.1 (Sign-range containment)` — **does not** (speed-range and endpoint comparisons only).
- `eleven_lonely_runners_v33.md:414-460` `Lemma 5.2 (PSM)` — **does not**.
- `eleven_lonely_runners_v33.md:470-511` `Lemma 5.3 (Chain A)` — **does not**. (`:487` invokes *"Lemma 5.1 and Theorem 4.2"* to name runner 8 as the unique candidate; the primality content is inherited from Theorem 4.2, and the step itself is a reach computation.)
- `eleven_lonely_runners_v33.md:520-538` `Lemma 5.4 (Chain B)` — **does not**.
- `eleven_lonely_runners_v33.md:548-589` `Theorem 5.5 (Universal Blocking)` — **does not**; its infeasibility criterion is `:578-581`, `109(11k+10)>100(11k+12) \iff 9\cdot 11k > 110 \iff k > 110/99`.
- `eleven_lonely_runners_v33.md:604-616` `Lemma 6.1`, `:618-642` `Lemma 6.2`, `:649-666` `Lemma 6.3`, `:668-706` `Lemma 6.4`, `:708-716` `Theorem 6.5` — **do not**.
- `eleven_lonely_runners_v33.md:732-752` `Lemma 7.1`, `Lemma 7.2`; `:761-769` `Theorem 7.3`; `:771-781` `Corollary 7.4` — **do not**.
- `eleven_lonely_runners_v33.md:213-218` bounded-ratio case — **does not**.
- `eleven_lonely_runners_v33.md:1139-1208` Appendix C, Kronecker reduction — **does not**.
- `lrc_n11_algebraic_lemma_v1.md:52-61` `Lemma 2.1`, `Lemma 2.2`; `:63-68` `Corollary 2.3`; `:76-152` `Prop 3.1`, `Prop 3.2`, `Lemma 3.3`, `Lemma 3.4`; `:158-182` `Theorem 4.1` — **do not**.
- `lrc_n11_incompatibility_v1.md:65-117` `Lemma 3.1`; `:119-161` `Lemma 3.2`; `:169-184` `Theorem 4.1`; `:190-196` `Corollary 5.1` — **do not**. Method 1's entire closing argument is rational arithmetic; the only primality-dependent input is the pair table it inherits from `Theorem 1.1`.

**Summary.** Primality is load-bearing at exactly one junction in each method — the
Complementary Pairs theorem and its corollary that `I₉` is unclaimed. Everything after that
junction is `ℚ`-arithmetic that would run unchanged for any modulus that produced the same
pair table.

---

## D. PROVED vs OPEN

### `eleven_lonely_runners_v33.md` — no grade tags, no open mathematical items marked

The file carries no status or grade line. It marks no step open, pending, conditional or
unverified. The only outstanding items it names are editorial and computational:

- `:332-333` — *"[TikZ figure to be added in .tex version: color each pair's slots distinctly; $I_9$ in grey labelled "unclaimed"; arrows from pair labels to their slots.]"*
- `:1212` — *"*End of v33. Next: TikZ figure for Figure 1 to be added in .tex conversion.*"*
- `:1080-1083` — *"The computations described here are *not* part of the proof; the theorem is established analytically in Sections 1–8. They provide independent, large-scale corroboration that the proof's structural mechanisms behave as the analysis predicts, with no exceptional regimes detected in either campaign."*
- `:1119-1120` — *"With zero failures across $1.1\times 10^9$ event-complete trials, the 99.9% confidence upper bound on the true failure rate is $6.9\times10^{-9}$."*
- `:1123` records the archive DOI as *"This paper is archived at https://doi.org/10.5281/zenodo.19341800."* (Recorded here as quoted; not adjudicated against the memory record, which assigns v33 to `10.5281/zenodo.19464700`.)
- Two scoping statements that qualify the strength of the ownership notion rather than mark
  an item open: `:61-63` — *"("Ownership" here refers to the AP-limit primary-slot pattern and the perturbative burden of repair, not absolute exclusivity for all perturbed configurations.)"*; and `:92-94` — *"It does *not* mean the pair covers the slot under all perturbed configurations; that is exactly what the gap obstruction lemmas in Section 5 resolve."*
- One measure-zero exclusion: `:187-188` — *"We exclude the measure-zero hyperplanes $a_j=j$; boundary cases can be handled by a limiting argument or direct boundary check and do not affect the contradiction analysis."*

### `lrc_n11_ap_paper_v30.md` — one status line, one measure-zero exclusion

- `:5` — *"**Status:** Submission draft — blocker cleanup and proof-derivation pass"*
- `:110` — *"We exclude the measure-zero hyperplanes $a_j=j$; every completely blocking configuration lies in one of the open sign classes."*
- `:1269` — *"The computations described here are *not* part of the proof; the theorem is established analytically in Sections 1–8. …"*

### `lrc_n11_incompatibility_v1.md` — graded PROVED, scope stated

- `:4` — *"**Status:** PROVED"*
- `:5` — *"**Scope:** n=11 AP framework, classical EFN, sign class ++------. Depends on `lrc_n11_algebraic_lemma_v1.md` §0–§3 (Setup, Complementary Pairs, Chain Structure, Forced Gaps)."*
- `:6` — *"**Result:** Closing slots I₄ and I₉ simultaneously is algebraically impossible; hence GF(I₄) + GF(I₉) > 0 for every CB configuration in the ++------ class with $a_9 = 25/3$, $a_6 = 40/7$."*

No item inside this file is marked open.

### `lrc_n11_algebraic_lemma_v1.md` — graded PROVED in the header, with nine internally marked open or pending items

Status lines:
- `:5` — *"**Status:** PROVED (2026-03-23). Steps 1–4 proved; Main Claim 5.1 proved in `lrc_n11_incompatibility_v1.md` via exact Runner 2 Incompatibility (I₄ forces $a_2 \geq 20/9$; I₉ forces $a_2 \leq 575/261$; gap $= 5/261 > 0$)."*
- `:207` — *"**Status: Main Claim 5.1 PROVED.** See `lrc_n11_incompatibility_v1.md` for the complete proof including exclusivity arguments for runners 3, 5, and 7."*
- `:278` (the §8 status table row for the same claim) — *"| Overdetermination Main Claim (§5) | Main Claim 5.1, this file | **Open** (explicit incompatibility pending) |"*

Those three lines disagree about the grade of Main Claim 5.1. Both readings are quoted; no
adjudication is offered here.

Items the file marks open, pending or unverified, individually:

1. `:164` — *"2. *$\{a_6 \cdot t^*\} = \{(40/7)(69/275)\} = \{360/385\}$... [needs exact computation]*"*
2. `:180-182` — *"- Runners 4,5,7,8: their bad intervals in $I_2$ must be checked. This is the remaining verification step."* / *"*[Open: complete the Case C₁ all-runner verification.]*"*
3. `:221` — *"- *[Status: stated; explicit lower bound pending computation of other runners' coverage of $I_1$'s left edge.]*"*
4. `:228` — *"- *[Open: verify all other runners are isolated in $(69/275, 10/(11a_3))$.]*"*
5. `:230` — *"Left gap in $I_3 = [34/110, 10/(11a_3)]$ of width $10/(11a_3) - 34/110 > 0$ (since $a_3 < 10 \cdot 110/(11 \cdot 34) \approx 2.94$... need to check upper bound on $a_3$)."*
6. `:233` — *"…GF > 0 on the entire compact CB set by the Overdetermination argument. $\square$ *(Pending step 1,3,4 completion.)*"*
7. `:261` — *"*[The I₉ resonance analysis requires the closing conditions table. The key result from `lrc_n11_closing_conditions_v1.md` §3 is that only runner 2 with $\delta_2 \in (0.1, 0.22]$ can be a single-runner cover of $I_9$; if this fails, $I_9$ has GF > 0.]*"*
8. `:277` — *"| Baton-pass certificate $t^* = 69/275$ (§4) | Theorem 4.1, this file | **Proved** (runner 9 verified; other runners pending) |"*
9. `:279` — *"| GF > 0 for ++------ class (§6) | Theorem 6.1, this file | **Architecture complete; pending §5** |"*

Its own §9 list of open steps (`:283-293`), verbatim headings:
- `:285` — *"1. **Case A/B explicit lower bound**: Compute GF(I₁) lower bound when $a_9 < 25/3$ or $a_6 > 40/7$, showing that no combination of the other 7 runners can cover the edge gap."*
- `:287` — *"2. **Case C₁ all-runner verification**: At $t \in (69/275, 10/(11a_3))$ in Case C₁, verify that all runners 2, 4, 5, 7, 8 are simultaneously isolated."*
- `:289` — *"3. **Overdetermination incompatibility (Main Claim 5.1)**: Write the explicit blocking conditions for $I_4, I_5, I_9$ on runners 2 and 9, and show the two constraints on runner 2 are incompatible rational equations."*
- `:291` — *"4. **Extension to all 247 sign classes**: The complementary pairs structure (Theorem 1.1) applies to all sign classes. The forced-gap computation (§3) changes by sign class (different resonance speeds), but the counting overdetermination (§5) should hold in all cases. Generalise."*
- `:293` — *"5. **Quantitative lower bound**: Express GF ≥ $c \cdot \min_j \rho_{j,m_{\rm crit}}$ where $\rho_{j,m}$ is the minimum distance from $a_j$ to the nearest resonance speed. From the empirical floor GF ≥ 0.12%, $c \approx 0.001$ for this class."*

The file also contains two in-line self-corrections left in place, which mark the
surrounding computation as reworked rather than open: `:93` — *"— wait, this isn't
skipping. Let me re-examine."* and `:141` — *"…let me recompute."*

### `docs/n11/AUDIT_COUNTING_CLAIMS_v2.md` — its own findings and its own scope limit

- `:11-15` (headline) — *"**None of the nine reaches either live document.** Three sit in dead working files, three died before `v30`, and three belong to the general-`n` programme that is on hold. Most importantly, the central one — the "9 slots, 8 runners" pigeonhole — was **replaced in `v33` by a correct algebraic fact**, which I verified."*
- `:31` — *"**Verified exactly.** With labels `m_j^± ≡ ±j⁻¹ (mod 11)`:"* and `:42` — *"…label 10 gives `I₉` (unclaimed), and label 1 is not a slot. The claim holds."*
- `:44-46` — *"`v33` also scopes the notion explicitly … so it does not overclaim."*
- The one item it leaves open, `:70` — *"D7 | `lrc_proof_allN_v11_8.md` (Conj. 5.2-H), `lrc_v11_9_theorem_5_2_sr_draft_v2.md` (Conj. 5.2-SR-H) | "The union of blocked sets is not everything." Empirically verified (34/34), **analytically open**, and the manuscript's abstract already declares the Main Theorem conditional. This is the real open item — and see below."*
- `:71` — *"D8 | `lrc_proof_v10_9.md:368` | CT.1 Case B marked open; *"depth ≤ 1 empirically"*. Superseded lineage (v10 → v11_8)."*
- `:88-89` — *"1. **Nothing blocks v30 or v33 from this family.** No correction is owed to the preprint on these grounds."*
- `:95` — *"5. D7 stays open and is now the shared target with n=8."*
- Its scope limit, `:99-102` — *"Nine specific claims, read at source. This is **not** a general audit of the n=11 lineage: it says nothing about `v33`'s own §5 gap obstruction lemmas, its seven-region exhaustiveness argument, or the separate issues that keep the preprint from submission. Those were not examined here."*

---

## E. The witness set

Both methods start from the same ten AP witness times and the same nine slots. The two
counts are distinct and both matter.

### The AP witness family — 10 elements, one per runner

`eleven_lonely_runners_v33.md:151-152`
> The classical AP witnesses are
> $$t_m = \frac{m}{11},\qquad m=1,\ldots,10.$$

`lrc_n11_algebraic_lemma_v1.md:19` (the same family, as the definition of complete blocking)
> - **Complete-blocking (CB):** For every AP witness $t_m = m/11$ ($m = 1,\ldots,10$), at least one runner $i$ satisfies $\{a_i t_m\} \notin [1/11, 10/11]$.

**Count: 10.** One witness per moving runner `e₁,…,e₁₀`; `n = 11` runners including the
stationary one. Both papers record that this family is not enough on its own —
`eleven_lonely_runners_v33.md:227` — *"The AP witnesses $\{m/11\}$ do not suffice once $a_1<1$."*
with the explicit counterexample at `:229-232` (blocked at all ten, witness `t = 4/17`).

### The slot family — 9 elements, one per witness label `m = 2,…,10`

`eleven_lonely_runners_v33.md:159-160`
> The **pacemaker slots** in cycle-relative coordinates are
> $$I_s = \left[\frac{11s+1}{110},\,\frac{11s+10}{110}\right],\qquad s=1,\ldots,9.$$

`eleven_lonely_runners_v33.md:161-163` (the same slots in absolute coordinates, per cycle)
> The $m$th **pacemaker cycle** is $C_m=\bigl[m/10,\,(m+1)/10\bigr]$, and in absolute
> coordinates the slots inside that cycle are
> $$I_s^{(m)} = \left[\frac{11m+11s+1}{110},\,\frac{11m+11s+10}{110}\right].$$

`lrc_n11_algebraic_lemma_v1.md:20` (Method 1's indexing, by witness label)
> - **Runner-10 slots:** $I_{m-1} = [(11m-10)/110,\ (11m-1)/110]$ for $m = 2,\ldots,10$ — the 9 sub-windows of $W_0$ near each AP witness $t_m$.

The two indexings agree: substituting `s = m-1` into `lrc_n11_algebraic_lemma_v1.md:20`
gives `[(11s+1)/110, (11s+10)/110]`, the `v33` formula.

**Count: 9**, against **8** free runners `2,…,9`. That mismatch is the object the whole
argument turns on. `eleven_lonely_runners_v33.md:292-302`
> **Theorem 4.2 (Complementary Pairs).** *The free runners $2,\ldots,9$ split into four
> complementary pairs, with primary-slot correspondence:*
>
> | Pair | Assigned slots |
> |---|---|
> | $(2,9)$ | $I_4$, $I_5$ |
> | $(3,8)$ | $I_3$, $I_6$ |
> | $(4,7)$ | $I_2$, $I_7$ |
> | $(5,6)$ | $I_1$, $I_8$ |
>
> *Slot $I_9$ is unclaimed.*

Four pairs × two slots = eight owned slots `I₁…I₈`; the ninth, `I₉ = [100/110, 109/110]`,
has no owner. `lrc_n11_algebraic_lemma_v1.md:40` states it as *"Slot $I_9 = [10/11,\ 109/110]$ is unclaimed — no runner pair has it as a primary slot."*

The audit records the arithmetic behind the count independently —
`docs/n11/AUDIT_COUNTING_CLAIMS_v2.md:40-42`
> Union `= {2,…,9}`; unowned `= {1,10}`. With the slot indexing `I_s ↔ m = s+1`
> (from `lrc_n11_closing_conditions_v1.md`), owned labels give exactly `I₁…I₈`,
> label 10 gives `I₉` (unclaimed), and label 1 is not a slot. The claim holds.

### The search window containing the slots

`eleven_lonely_runners_v33.md:168-170`
> In the large-ratio case $a_1<1$, and we work in the window
> $$W_{\mathrm{ref}} = \left[\frac{1}{11a_1},\,\frac{10}{11a_1}\right].$$
> Runner 1 is isolated throughout $W_{\mathrm{ref}}$ by construction.

`lrc_n11_algebraic_lemma_v1.md:17` gives Method 1's identical window under a different name:
*"**Window $W_0$:** $[1/(11a_1),\ 10/(11a_1)]$ — runner 1's isolation window."*

### Method 1's single explicit witness time

`lrc_n11_algebraic_lemma_v1.md:158-159` (quoted in full in §A above) names
`t* = 69/275`, verified against runner 9 at `:166`
> **Proof of point 1.** $(25/3)(69/275) = 25 \times 69 / (3 \times 275) = 1725/825 = 23/11$. Since $\lfloor 23/11 \rfloor = 2$, $\{23/11\} = 23/11 - 2 = 1/11$. ✓

with the good window it opens at `:170-173`, positive iff `a₃ < 2750/759`. Method 2 names
no analogous single time in the large-ratio case; its only explicit witness is the
bounded-ratio one, `eleven_lonely_runners_v33.md:48` — `t^*=\frac{10}{11e_{10}}`.

---

## Coverage — files and line ranges read

Every quote above was taken from a line inside one of these ranges, opened directly.

| File | Line ranges read |
|---|---|
| `eleven_lonely_runners_v33.md` (1212 lines) | 1–146, 147–272, 273–402, 403–600, 601–825, 1078–1212; plus grep hits across the whole file for `^#`, `prime\|pmod{11}\|inverse\|cyclic\|primitive root\|j^{-1}`, `open\|pending\|conditional\|unverified\|TODO\|status\|grade`, `exhaustiv`. Not read line-by-line: 826–1077 (References, Appendix A.1–A.11 boundary ledgers). |
| `lrc_n11_incompatibility_v1.md` (217 lines) | 1–110, 111–217 — complete. |
| `docs/n11/AUDIT_COUNTING_CLAIMS_v2.md` (102 lines) | 1–102 — complete. |
| `lrc_n11_ap_paper_v30.md` (1292 lines) | 1–60, 136–182, 181–230, 516–575, 642–700, 1267–1292; plus grep hits across the whole file for `^#`, primality patterns, `open\|pending\|Status\|empirical`, `exhaustiv`. Not read line-by-line: 61–135, 231–515, 576–641, 701–1266. |
| `lrc_n11_algebraic_lemma_v1.md` (294 lines) | 1–72, 72–156, 156–294 — complete. (Read although not on the assigned list: it carries Method 1 and is named in the task background.) |

**Not consulted:** `memory/MEMORY.md`, `memory/lrc_proof_status.md`, the Lean tree, and
every other n=11 working file (`lrc_n11_closing_conditions_v1.md`,
`lrc_n11_structural_mechanism_v1.md`, `lrc_n11_baton_pass_v1.md`, the `v3`–`v18` paper
lineage). Where those files are named above, the naming is quoted from the four files read,
not verified against the files themselves.
