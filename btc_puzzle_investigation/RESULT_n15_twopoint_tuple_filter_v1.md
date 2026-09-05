# RESULT — the N15 two-point tuple filter: NO super-additive structure; the MI is ~90% shuffled-null baseline + a ~c/n excess that vanishes at secp

**Date 2026-08-22. Grade: `[VERIFIED — exact, total enumeration; matched null]`** Scripts:
`n15_twopoint_tuple_filter_v1.py`, `n15_twopoint_tuple_scaling_v2.py` (+ logs). The N15 non-sign
pivot's two-point level — the cheapest decisive brick after the sign world closed (sessions (c)/(d)).

## Object

Two-key setting, public $(P_1, P_2, P_{12}=P_1{+}P_2)$; the canonical tuple
$t(d) = (\text{eps-class}, \text{sextant}, \text{band}, y\text{-parity})$ of each point
(`int1_frame_operator.build` machinery). Question: is $MI(t_{12}; (t_1, t_2))$ super-additive
structure (a meet-in-the-middle filter beating the sum of single-point budgets), finite-size
artifact, or real signal? **Exact total enumeration** over all pairs (d₁+d₂ ≢ 0) at 9 primes,
n ∈ [31, 1753], plus a **shuffled-tuple null** (random relabeling of tuples over d — same cell-size
structure, destroyed d-assignment; 200/40/12 draws by size).

## Results

| p | n | MI | null mean | z | MI−null | (MI−null)·n |
|---|---|---|---|---|---|---|
| 43 | 31 | 1.4333 | 1.3448 | 2.0 | 0.089 | 2.8 |
| 79 | 67 | 1.0738 | 1.0076 | 3.4 | 0.066 | 4.4 |
| 163 | 139 | 0.5783 | 0.5853 | −1.0 | −0.007 | −1.0 |
| 211 | 199 | 0.2395 | 0.2245 | 3.4 | 0.015 | 3.0 |
| 547 | 547 | 0.1121 | 0.1040 | 8.2 | 0.008 | 4.4 |
| 823 | 829 | 0.0265 | 0.0224 | 13.1 | 0.004 | 3.3 |
| 1051 | 1093 | 0.0204 | 0.0192 | 5.4 | 0.001 | 1.1 |
| 1303 | 1249 | 0.0216 | 0.0205 | 5.3 | 0.001 | 1.2 |
| 1831 | 1753 | 0.0117 | 0.0106 | 12.0 | 0.001 | 1.8 |

**Readings:**
1. **~90% of the MI is the null baseline** — deterministic tuple functions on a finite cyclic group
   force this much apparent MI from the cell structure alone; the shuffle (which preserves all
   cell sizes and within-tuple features) reproduces it. The two-point tuple readout carries **no
   super-additive filter structure**.
2. **The excess above null decays like c/n (c ≈ 1–4)** — the same 1/n-scale forced-effects family
   as the sign world's anti-diagonal. At secp: ~$2^{-254}$. (The consistently positive z's mark a
   real but $O(1/n)$ correlation — flagged, vanishing.)
3. Cell structure factorizes: max cell ≈ 0.2–1% of pairs, no cell explosion; the honest filter
   value stays $O(1)$ bits (≈ 3·H(t) ≈ 12–13 bits against $\log_2 n^2$ of pair entropy — nothing at
   scale, exactly the (g) single-point conclusion lifted to two points).

## Consequence

**The N15 non-sign door is now closed at the two-point level** (signs: sessions (c)/(d); tuples:
here). What remains for the 1.585-bit trit alignment filter: ≥3-point structured readouts, weighted
multiset objects (the E3 class — powered-bounded on the real 82 by N30), and the Fourier $V(a)$
side. Each is a strictly heavier class than anything closed today.

## §3-point addendum (same day, `n15_threepoint_tuple_filter_v1.py`)

The same design one rung up — $MI_3(t(s); (t_1,t_2,t_3))$ over triples off all forced vanishing loci,
shuffled null:

| p | n | MI₃ | null mean | z | (MI−null)·n |
|---|---|---|---|---|---|
| 43 | 31 | 0.988 | 0.828 | 3.7 | 5.0 |
| 79 | 67 | 0.483 | 0.407 | 4.4 | 5.1 |
| 163 | 139 | 0.167 | 0.156 | 2.9 | 1.5 |
| 211 | 199 | 0.045 | 0.032 | 73 | 2.6 |

Identical shape: null baseline dominant, excess $\sim c/n$ ($c \approx 2$–$5$) → vanishes at secp.
**The tuple world is closed through 3 points, mirroring the sign-world closure exactly.** N15's
remaining classes are only the heavy ones: weighted multisets (E3-class, bounded), Fourier $V(a)$,
and ≥4-point structured readouts.
