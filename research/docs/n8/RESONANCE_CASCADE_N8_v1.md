# The resonance cascade at n = 8 — the n=11 engine translated, and a cleaner forced gap

2026-09-08. Translates the actual mechanism of `lrc_n11_ap_paper_v30.md` §4–5 and
`lrc_n11_algebraic_lemma_v1.md` §§2–3. Scripts `experiments/n8/boundary_ledger_n8_v1.py`,
`resonance_chain_n8_v1.py`. Exact `Fraction`; the flagged `/` sites are `Fraction/Fraction`.

## 1. The right object is the slot BOUNDARIES

Complete blocking in `W_ref` means every pacemaker slot `I_s = [(8s+1)/56, (8s+7)/56]` is
fully covered by runners `2..6`. A slot is covered only if **both endpoints** are. So the
objects are the twelve boundaries and, for each, which runners can reach it — the
translation of Appendix A.1–A.8.

`B_{j,k}(a) ∋ b ⟺ (8k+7)/(8b) ≤ a ≤ (8k+9)/(8b)`, intersected with `a_j ∈ (j−1, j+1)`.

## 2. The ledger, and its validation  `[PROVED]`

| boundary | reachable by |
|---|---|
| **`I₁` left, `9/56`** | **runners 5, 6 only** |
| `I₁` right, `15/56` | 3, 4, 5 |
| `I₂` left, `17/56` | 2, 3, 4, 6 |
| every later boundary | all of 2..6 |

The extreme left boundary is the scarcest, exactly as at `n = 11`. **Validation:** run at
`n = 11` and `I₁`'s left edge `6/55` is reachable only by runners 8 and 9, at `a ≥ 25/3` —
`25/3` being precisely the left-edge resonance of `lrc_n11_algebraic_lemma_v1.md` Cor. 2.3.
The ledger reproduces the source's own constant.

**The n = 8 resonances.** `(n−1)/(na) = 9/56 ⟹ a = 49/9`; `(n+1)/(na) = 15/56 ⟹ a = 21/5`.

## 3. The forced gaps  `[PROVED — exact, whole chain]`

Fixing a resonance fixes the entire chain (Coupling Principle). In units of `1/56`:

**`a = 49/9`** — `B₀ = [9, 81/7]`, `B₁ = [135/7, 153/7]`, `B₂ = [207/7, 225/7]`,
`B₃ = [279/7, 297/7]`, `B₄ = [351/7, 369/7]`. Touches `I₁, I₂, I₃, I₅, I₆`.
The gap `[225/7, 279/7] = [32.142…, 39.857…]` **strictly contains `I₄ = [33,39]`**:
**zero coverage of `I₄`.**

**`a = 21/5`** — `B₀ = [35/3, 15]`, `B₁ = [25, 85/3]`, `B₂ = [115/3, 125/3]`,
`B₃ = [155/3, 55]`. Touches `I₁, I₃, I₄, I₅, I₆`.
The gap `[15, 25]` **strictly contains `I₂ = [17,23]`**: **zero coverage of `I₂`.**

## 4. A correction to the source's wording, and why n = 8 is cleaner

`lrc_n11_algebraic_lemma_v1.md` Prop. 3.1 states that runner 9 at `a₉ = 25/3` *"SKIPS `I₆`
entirely"*. It does not, quite: `B_{9,4}` ends at `168/275 = 336/550` while `I₆` begins at
`67/110 = 335/550`, so a **sliver of width `1/550`** at `I₆`'s left edge is covered.

**This is a loose summary sentence, not a defect.** That file's own Lemma 3.3 opens the
forced gap at `168/275`, i.e. it accounts for the sliver correctly, and this computation
reproduces `168/275` exactly. Recorded so the word "entirely" is not inherited.

**At `n = 8` there is no sliver.** Both resonance gaps strictly contain their slot, so the
forced gaps are total rather than partial. The `n = 8` cascade therefore starts from a
*stronger* premise than the `n = 11` one.

## 5. What this sets up

The chain is now: `I₁`'s left edge can only be closed by runner 5 or 6, and only at
`a = 49/9`; that runner then contributes **nothing** to `I₄`. Symmetrically `I₁`'s right edge
forces `a = 21/5` on runner 3, 4 or 5, contributing nothing to `I₂`. Both are inside the
relevant sign ranges (`49/9 ≈ 5.44 ∈ (4,6)` and `(5,7)`; `21/5 = 4.2 ∈ (3,5)` and `(4,6)`).

So a completely blocking configuration must close `I₁` at both edges, and each closure
removes a runner from a different later slot. The next step is the overdetermination count:
with five free runners, two of them pinned to resonances and blind to `I₄` and `I₂`
respectively, whether the remaining budget can still cover all six slots. That is the
`n = 8` analogue of the Runner-2 Incompatibility (`I₄` forces `a₂ ≥ 20/9`, `I₉` forces
`a₂ ≤ 575/261`, gap `5/261`).

## 6. Status

`[PROVED]` the ledger, the two resonances, both forced gaps, and the `n = 11` validation.
`[NOT CLAIMED]` that the large-ratio case is closed. `[CORRECTED]` Prop. 3.1's "entirely".
Nothing here touches Rosenfeld's ledger; `n = 8` is not proved.
