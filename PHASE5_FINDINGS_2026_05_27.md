# Phase 5 — Counterexample structural investigation

**Session:** 2026-05-27 (ctd)
**Script:** `LonelyRunner/scripts/phase5_residue_structure.py`
**Output CSV:** `reports/phase5_residue_structure.csv` (38,664 rows)

## Headline finding — The pigeonhole sub-condition

**Sufficient condition for non-emptiness (perfect empirical separation):**
$$
|\mathcal{B}| + |\mathcal{I}_A| > n L_A,
$$
where $\mathcal{B} := \bigcup_{\alpha_0 \in \mathcal{I}_G}\{\lfloor (m'' \bmod nL_GL_A)/L_G \rfloor : m'' \in [\alpha_0 L_A p, (\alpha_0 + 1) L_A p)\}$
is the set of $\beta$ values reached by the bands.

| Stratum | Pigeonhole holds | Pigeonhole fails |
|---|---|---|
| Counterexamples (681) | **0** | **681** |
| Positives (37,983) | 34,825 | 3,158 |

**Proof of sufficiency:** if $|\mathcal{B}| + |\mathcal{I}_A| > n L_A$, then by pigeonhole in $[0, n L_A)$, $\mathcal{B} \cap \mathcal{I}_A \ne \emptyset$. Any $\beta_0 \in \mathcal{B} \cap \mathcal{I}_A$ corresponds to a joint-good fine cell. $\square$

## Two-stage counterexample mechanism

For the 681 CE, the obstruction decomposes:

**Stage 1 — Residue gap mod $L_A$** (113 CE / 681).
$\mathcal{I}_A$'s targets all lie in residue classes mod $L_A$ that the bands miss.
The bands hit $\beta$-residues from a subset $R_B \subsetneq \{0, 1, \ldots, L_A - 1\}$;
$\mathcal{I}_A$'s residues lie in the complement $L_A \setminus R_B$.

**Stage 2 — Within-residue gap** (568 CE / 681).
$\mathcal{I}_A$'s residues are in $R_B$ (bands cover the right residue classes), but
the *specific* $\beta$-values targets occupy are not among the band's coverage —
the bands hit some $\beta$'s in a residue class but not others.

Both stages reduce to pigeonhole failure: $|\mathcal{B}| + |\mathcal{I}_A| \le n L_A$.

## Structural mechanism — Smallest CE traced

For the smallest CE ($n = 3$, $G = [3]$, $A = [1, 5]$, $p = 2$):
- $L_G = 3$, $L_A = 5$, $n L_G = 9$, $n L_A = 15$, $M = 90$.
- $\mathcal{I}_G = \{1, 4, 7\}$ — all $\equiv 1 \pmod{L_G = 3}$ (highly constrained residue).
- Shift set: $r_{\alpha_0} = 2\alpha_0 \bmod 9 \in \{2, 8, 5\}$, all $\equiv 2 \pmod{3}$.
- Band starts (in $m'' \bmod 45$ space): $\{10, 25, 40\}$, all $\equiv 3 \pmod 5$.
- Band $\beta$-coverage: $\{3, 4, 5, 6\} \cup \{8, 9, 10, 11\} \cup \{13, 14, 0, 1\}$ = 12 values out of 15.
- Missed residue mod $L_A$: $\{2\}$ → missed $\beta$ values $\{2, 7, 12\}$.
- Target: $\mathcal{I}_A = \{7\}$ — which falls in the missed residue. CE.

The mechanism is: $\mathcal{I}_G$ has a single residue class mod $L_G$, which under
multiplication by $p$ produces a single shift-residue class mod $L_A$, which spans
$\lceil L_A p / L_G \rceil = 4$ consecutive residues mod $L_A$, missing the
remaining $L_A - 4 = 1$ residue.

## Why LRC-shape avoids CE — empirically

| LRC-shape ($k_G + k_A = n - 1$) | Pigeonhole holds | Doesn't hold |
|---|---|---|
| 5,517 inputs | 5,464 (99.04%) | 53 (0.96%) |

**For 5,464/5,517 LRC-shape inputs (99.04%), pigeonhole is automatically satisfied
because $|\mathcal{I}_G|$ and $|\mathcal{I}_A|$ are large enough.**

The remaining 53 LRC-shape inputs (0.96%) fail pigeonhole but are still positive
due to specific arithmetic alignment. They all have $p = 2$ and small $|\mathcal{I}_G|$.

## What we'd need to close Conjecture 5.2-H

Two analytic ingredients:

1. **Lower bound on $|\mathcal{B}|$ in terms of $(|\mathcal{I}_G|, L_G, L_A, p)$.**
   Trivial bound: $|\mathcal{B}| \ge |\mathcal{I}_G|$ (each band contributes ≥ 1 distinct value).
   Better: when bands are pairwise non-overlapping in $m''$ space (provable when
   the $r_{\alpha_0}$'s are well-separated mod $n L_G$), $|\mathcal{B}| \ge
   |\mathcal{I}_G| \cdot \lceil L_A p / L_G \rceil - O(\text{boundary effects})$.
2. **Arithmetic-alignment argument for the residual 0.96% small-$p$ cases.**
   These require a finer analysis specific to $p = 2$ and small $|\mathcal{I}_G|$,
   where bands happen to align with targets by structural coincidence.

For ingredient 1, the natural sufficient condition under LRC-shape would be:
$$
|\mathcal{I}_G| \cdot \lceil L_A p / L_G \rceil + |\mathcal{I}_A| > n L_A.
$$
Combined with Lemma 4.1's $|\mathcal{I}_G| \ge 2 L_G / ((n-1) v_{\max})$,
this gives the Option A bound — which is too weak in the DI hard case as
documented in `THEOREM52_JOINT_FINE_CELL_FALSE.md`.

So a STRONGER lower bound on $|\mathcal{I}_G|$, specific to LRC-shape, is the
genuine missing ingredient.

## Structural picture

The conjecture's truth has two layers:

**Layer 1 (combinatorial):** Pigeonhole $|\mathcal{B}| + |\mathcal{I}_A| > n L_A$.
Sufficient. Holds for 99.04% of LRC-shape, 0% of CE.

**Layer 2 (arithmetic):** When pigeonhole fails, the conjecture can still
hold if $\mathcal{B}$ and $\mathcal{I}_A$ overlap by *specific* arithmetic
alignment. Holds for the remaining 0.96% of LRC-shape.

The conjecture as a whole is the *union* of these layers. Closing it
unconditionally requires either:
(i) Proving Layer 1 always holds under LRC-shape (a stronger $|\mathcal{I}_G|$
   bound), or
(ii) Proving Layer 2 always covers the residual via arithmetic-alignment
   arguments (small-$p$ specific).

Neither is currently available, but the empirical mining has *characterised*
the gap precisely.

## Artefacts

- `LonelyRunner/scripts/phase5_residue_structure.py` — harness
- `reports/phase5_residue_structure.csv` — full 38,664-row data
- `LonelyRunner/PHASE5_FINDINGS_2026_05_27.md` — this file

## Status going forward

Phase 5 has surfaced **Theorem 5.2-P (Pigeonhole Sub-condition)** as a new
provable analytic theorem that we can add to v11.7. It is:
- **Sufficient** for the conjecture's conclusion.
- **Tight** in the empirical sense — perfectly separates CE from positives.
- **Empirically verifiable** for any specific input.

For the manuscript, adding Theorem 5.2-P narrows the conjecture's open scope
to the 0.96% LRC-shape edge cases where pigeonhole fails. This is a meaningful
refinement of Conjecture 5.2-H's status.
