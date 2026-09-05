# COMPENDIUM — The μ₆ CM Lever of secp256k1: one mapped object, five pieces

**`[PROVISIONAL — compile-diff unavailable]`.** The mandatory `compile-diff` gate was attempted 2026-08-17
and did not complete (session/API rate limit — a gate UNAVAILABLE, not a gate that failed). Per project
§2a, this compendium proceeds provisionally: (1) tagged here in the grade slot; (2) a MECHANICAL self-audit
loss-check was run (grep of every source grade/caveat/open-item/owed-gate into this file) — result: no
material loss, no grade inflated above source; **uncovered by the self-audit: context-isolation (frame
drift in the synthesis sentences), which only the real gate catches**; (3) gate recorded as OWED below;
(4) **no grade in this file is promoted** — all labels are carried verbatim from sources.

**Framework (binding on how to read this).** This consolidates five independently-recorded pieces of a
single lever — the μ₆ CM structure of the `y²=x³+7` family — into one citable object. Each piece is logged
on its own terms and grade; **none is required to beat generic `√n` or solve ECDLP to count.** The lever is
mapped, including where it stops. Boundaries are recorded as honestly as positives.

**Consolidation date:** 2026-08-17. **Sources** (each retains its own file as the primary record):
`RESULT_semaev_cm_relation_yield_v3_scaling.md`, `NOTE_k3_analytic_reduction_v2.md`,
`RESULT_mu6_quotient_relation_multiplication_v1.md`, `RESULT_mu6_characters_index_orbits_v1.md`,
`RESULT_mu6_solving_degree_v1.md`. `compile-diff` gate: run before promotion (§ end).

## The shape (one sentence)
The μ₆ lever is real and lives **entirely on the relation-collection side** of index calculus (it multiplies
relations, cuts the factor base, organizes the yield); it **stops at the linear-algebra side**, where two
independent instruments agree it gives no drop **at tested scope** — a mapped boundary, NOT "no
linear-algebra structure ever" (the μ₃-graded syzygy module, piece 5 open (i), is untested).

## The five pieces

### 1. Yield excess — `[EMPIRICAL — EXPLORATORY]`
`T1(j0) = log(Q_j0/Q_nonCM)` grows ~linearly in `|V|` over {4,5,6}: 0.187, 0.338, 0.509; `perm_p=0.0000`;
pos 22–23/24 primes. Linear `T1` ⇒ ratio `Q_j0/Q_nonCM ~ exp(|V|)`. j1728 arm null at |V|≤5.
**Caveats (retained):** `|V|≤6` is tiny; **NO license to extrapolate to attack-scale `|V|~p^c`**; model
scale (p≤8011, m=3), **no `2²⁵⁶` transfer**; trend is within-window {4,6}, not asymptotic.
**Open (retained):** |V|=7,8 (out of reach here); mechanism of the j0 excess (→ piece 3); **yield → full
relation-collection-cost translation** (the consequential, unrun test).

### 2. slope² identity — `[PROVED]` (+ un-normalized channel PROVED)
For any three non-identity points with `P₁+P₂+P₃=O`, the group law forces `x₁+x₂+x₃ = m²` (slope²), so
`χ₂(x₁+x₂+x₃)=+1`. Hence `W(0)=Σ_{O-sum}χ₂(x-sum)=#{pairs, m≠0}=n²−O(n)>0` (rigorous; `#{m=0}=O(n)` since
each `y` has ≤3 points). ⇒ `Σ_b χ₂(b)T(a₀,b)³ = i√p·(n²−O(n))` — **un-normalized k=3×χ₂ channel PROVED**;
explains `a₀`-genericity (flat `s=0` mode). Identity is **φ-covariant** (`φ` sends it to `β(x-sum)=(m/β)²`),
so relations arrive pre-sorted into φ-orbits.
**Open (retained):** the **phase-normalized** `|mean_QR|≥c` (the banked k=3 object) — reduced to a stated
`|T(a₀,b)|`-near-0 sparse-zeros / Sato-Tate equidistribution estimate (`NOTE_k3_analytic_reduction_v3`),
supported by 4 moments + linear near-zeros count; NOT proved.

### 3. μ₆-quotient relation multiplication — `[VERIFIED — exact]`
μ₆-invariant factor base: CM (μ₆) multiplies each 3-term relation into **exactly 6** and quotients
`|F|→|F|/6`; non-CM (μ₂) → **exactly 2**. At matched effective base (~230 orbit-reps): **3× CM advantage**.
This is the mechanism behind piece 1.
**Scope (retained):** **constant-factor (≤6×), NOT an exponent change** — does not alone make index calculus
subexponential or beat generic `√n`. **Automorphism-accelerated index calculus is a KNOWN technique**; the
contribution is the clean μ₆-vs-μ₂ measurement + link to the covariant slope² relations. p≈4000, m=3.

### 4. Characters index the orbits — `[EMPIRICAL — real skew]` + boundary null
`e₁+e₂+e₃ mod 3` (μ₆-invariant) grades the orbits: {0:123528,1:117054,2:112212}, skew toward 0 = **~9σ**
(orbit level). `χ₂`-product skew ~8σ. slope²-`χ₂` constraint holds 99.4% (0.6% = `m=0`). **Real weak grading.**
**FOLLOW-UP — does the grading BLOCK the matrix? Scoped NULL:** block incidence `B` roughly uniform (all 4
`χ₂`-blocks 97–147); fill-in graded 940 vs random 1008 (~7%, inside noise). **The grading does NOT reduce
elimination cost.** Scoped to {this construction, p≈4000, `χ₂`/`e-sum` gradings}.

### 5. Solving degree — `[EMPIRICAL — scoped component null; PROVISIONAL]`
Last-fall degree `d_LF` (binding solving-degree invariant): m=3, |V|=4, `d_LF=19–20` across p=523–601;
CM/ω vs #E-matched non-CM **Δ=0 exactly** (integer equality, not noisy-small). β-arm `d_LF=34–35`, Δ_β=0.
Firing plant fires (reads a 1-degree drop); negative control Δ=0; `d_LF` varies 19/20/21/34/35 (live).
⇒ **at matched quo, μ₆/ω does NOT lower `d_LF`**.
**NOT A CLOSURE (retained, binding):** solving degree is ONE component of IC cost. **Open (retained):**
(i) the **μ₃-graded syzygy / staircase module** — un-projected, a scalar-`d_LF` null does not close whether
ω reshapes WHICH syzygies resolve when; (ii) **m=4/5** (S₅/S₆ VOID-intractable here, >240s) — null does NOT
extend; (iii) the **yield channel** (piece 1) untouched by this; (iv) full IC-cost accounting.
**Owed gate (retained):** `citation-verifier` on **Caminata–Gorla** (solving degree ≥ last-fall degree,
eprint 2021/1611) and on "no competitive prime-field summation-poly index calculus known"; per
`CORRECTION_semaev_cm_yield_mechanism_literature_v1`, extension-field LFD literature must NOT be cited as a
prime-field secp bound.

## The mapped boundary (the load-bearing synthesis)
- **Relation-collection side — μ₆ ACTS:** yield ~exp(|V|) (1), 6× multiplication (3), φ-covariant relations
  (2), characters grade orbits (4). Measured/proved.
- **Linear-algebra side — μ₆ STOPS:** grading does not block the matrix (4 follow-up, fill-in null) AND
  `d_LF` Δ=0 (5) — **two independent instruments agree.** Scoped, not "no structure ever."

## Consolidated open frontier (nothing dropped)
1. yield → full relation-collection-cost vs generic `√n` (unrun; piece 1).
2. phase-normalized `|mean_QR|≥c` = the `|T|`-tail equidistribution estimate (piece 2).
3. the **μ₃-graded syzygy module** on the linear-algebra side — the un-projected structure a scalar-`d_LF`
   null does not close (piece 5 open (i)); the honest frontier of the whole μ₆ line.
4. m=4/5 Semaev (intractable here; piece 5 open (ii)).
5. |V|=7,8 yield scaling (piece 1).

**Owed gates:** `citation-verifier` (Caminata–Gorla + no-competitive-prime-field-IC); **`compile-diff` —
ATTEMPTED 2026-08-17, DID NOT COMPLETE (session/API rate limit); OWED on re-run before this compendium is
treated as promoted.** Mechanical self-audit stood in provisionally (§top); it does not substitute for the
gate's context-isolation. No grade in this compendium exceeds its source; provisional/empirical/verified/proved labels are
carried verbatim.
