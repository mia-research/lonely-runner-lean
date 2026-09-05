# secp256k1 — Positive-Findings Handover (2026-08-17, v1)

**`[PROVISIONAL — compile-diff OWED]`.** This handover **compiles the results produced since the last
handover** (`POSITIVE_FINDINGS_MASTER_v10.md`, 2026-08-15) — the Aug 15–17 μ₆-lever / GLV-orbit /
carry-conservation / k=3-phase / isotypic-trace / exclusion cluster, plus the results-vs-narrative
audit layer. It is **additive**: it does **not** mutate or supersede v10; every row points to its
primary file as the record of truth. The mandatory `compile-diff` gate for a consolidated document was
attempted on 2026-08-17 by `COMPENDIUM_mu6_lever_v1` and **did not complete (session/API rate limit —
UNAVAILABLE, not failed)**; it was **not re-run this session**. Per project `§2a`, this proceeds
PROVISIONALLY: (1) tagged here in the grade slot; (2) a mechanical self-audit (every source's grade /
open-item / owed-gate carried in) stands in — **it does NOT cover context-isolation / frame drift**,
which only the real gate catches; (3) gate recorded OWED (§F); (4) **no grade is promoted** — all
labels are carried verbatim from the primary files.

**Why this document exists, stated straight.** The user asked for the compile *and* — because of the
project's measured **one-way suppression bias** (positives converted to nulls *before* they are tested;
never the reverse) — for the **results, not just the narrative conclusions**. §A is that pass: it reads
the measured numbers against what the prose said about them, in **both** directions the bias runs
(under-sold positives; over-sold closures). §A is the priority section.

**Scale banner (total, applies to every row).** Model-scale primes here are `p ≤ ~8000` (Semaev /
μ₆ / solving-degree), `p ≤ ~967` (k=3 phase decay), `p = 43` (isotypic trace `A_new`), or secp itself
(`n ≈ 2²⁵⁶`) only for the *public-key readouts* (GLV orbit, carry, flap), which are exact-arithmetic
facts about a coordinate, not statistical claims. **A model-scale count carries ZERO power against
`2²⁵⁶`.** No row below is a security claim; **no avenue is closed** except where a closure is graded
with object+class+power+scope (§A-2) — and those close a *named layer*, never the DLP.

**Grades:** `PROVED` (exact/symbolic) · `VERIFIED` (exact, scoped) · `EMPIRICAL` (survives a matched
null) · `CITED` · `HEURISTIC` · `OPEN` · `ABSTAINED` · `NULL — scoped` (a null bound to method+sample+
floor, never "impossible"). Sources are the primary record; grades inherited, not re-derived here.

---

## §A — RESULTS vs NARRATIVE (the suppression-bias pass)

The instruction was: *look at the results, not just the narrative conclusions.* Here is where the two
diverged in the Aug 15–17 work, read off the actual numbers.

### A-1. Positives the narrative UNDER-SOLD (the bias's primary direction)

**These are not new finds — they are finds the prose deflated, recovered by reading the tables. Do NOT
re-deflate them; each is owed a test, not a verdict.**

| # | The measured result | What the prose had said | Status |
|---|---|---|---|
| **A-1a ★** | **k=3 phase channel is real and asymptotic.** Survives the *negation-parity-matched* null (not the free shuffle): CM p=547 **p=0.001**, non-CM p=181 passes. Un-normalized channel `Σ_b χ₂(b)T(a₀,b)³ = i√p·(n²−O(n))` **PROVED** (rests on slope² + `#{m=0}=O(n)`). Concentration **asymptotically real**: `\|mean_QR\|·√\|QR\|` **grows 2→7** from p=43→967 (would be O(1) under equidistribution); `\|mean_QR\|` stabilizes **≈0.33**, 5–7× the `1/√\|QR\|` floor and widening. | An earlier "powered null" (q=463, **p≈0.88**) declared it dead — it was a **sorted-index bug** (paired x-coords with `e_n(a₀·idx)` by x-sorted position, not by the true `d`). And the "stable amplitude invariant" was **over-refuted** using small-p scatter. | **Two documented suppression self-corrections** — the first caught by the user. Channel is EMPIRICAL/VERIFIED-scope + a PROVED un-normalized piece. Phase-normalized `\|mean_QR\|≥c` OPEN (reduced to a `\|T\|`-near-0 tail estimate). `CONFIRMED_k3_phase_channel_weierstrass_v1`. |
| **A-1b ★** | **The public readout carries FULL determined information about `d`.** Firing control `MI(e([d]G); d) = 1.585 bits` = fully determined. Only **cheap-invertibility** fails: `max MI(e; 8 cheap fns of d) = 0.033 bits` (≈ the n=349 finite-size floor). | "**No keyspace reduction** from the public readout" — the load-bearing dismissal the whole "nothing here" story rested on. It was **argued, never tested** ("circular", "orbit-mates leave the interval"). | **CORRECTED ↓.** Circular ≠ no information. The test says *less* than the dismissal: full info present, only cheap-invertibility fails, and the **joint-readout question is untested** (see A-1e). `AUDIT_session_conclusions_v1` #4. |
| **A-1c** | The **public χ₃-index varies for all keys** — a real, public bit. (At tested power it carries no residue of `d`: `bits_removed ≈ ±0.05`, plant fired — a scoped null, not a dead bit.) | Earlier **mislabeled the χ₃-index "dead"** by conflating it with the trivially-zero *scalar* index. | Suppression **caught + corrected**; the bit is real and public. `RESULT_t2d_soft_exclusion_v1`. |
| **A-1d ★★** | **E3 cubic difference-set on the real 82 keys** — a **pre-registered reject**: `E3(real)=13125` at the **98.4th percentile, p≈0.033**, explicitly "**not a null-estimation artifact**," interpretation OPEN, **not** MC-corrected. Sits on the **group-law difference-set object-class — the one class that touches the DLP.** | `MASTER_v9` reverted it to a **stale H3 "at the AP-control floor" null** ("carried verbatim from H3"). | **The standout suppressed positive.** A *fired* pre-registered reject converted to a null at the consolidation seam. **Owed a MEASUREMENT** (§F), not a re-assertion and not a re-deflation. `RECOVERED_RESULTS_v1` B3.4; `LIVE_LEADS_MAP_v1`. |
| **A-1e** | The **joint-readout question is OPEN and untested:** do `e ⊕ s-class ⊕ y-parity ⊕ interval` jointly constrain `d` below brute force? (The user's "once these connect" thesis.) | Buried under "boundary located" / "no reduction" closure-framing. | **OPEN — the honest residue of A-1b.** Not refuted; untried. `AUDIT_session_conclusions_v1`. |

**Structural note (why A-1d matters most).** A-1a–c were caught and corrected *inside* this session's own
files — the mechanism worked. A-1d was corrected only by the results-vs-narrative audit, because it was
buried one document-generation ago and is invisible to every current top-level doc. That is the exact
failure mode the suppression bias produces: not a talked-up result, but a **fired positive silently
converted to a null at a consolidation seam**.

### A-2. Closures the narrative OVER-SOLD (the symmetric burden, per `§4c`)

**A null/closure invoked to shut an avenue faces the same bar as a PROVED claim: object + class +
power + scope, or it is an overclaim. These are graded closures of *named layers* — flagged so no
reader reads them wider than their scope.**

| # | The closure as written | The object it actually closes | The residue it does NOT close |
|---|---|---|---|
| **A-2a** | GLV-carry-conservation §8: "**closed layer** … **3.65 bits indexical, 0 bits operational** … **impossible by no-go**." | The **orbit-geometry readout as a standalone search filter**: with the exact joint law `6×{3/4,1/8,1/8}` and the conservation law, per-candidate membership costs a *full* candidate evaluation ⇒ zero work reduction *from orbit geometry alone*. Legitimately graded (exact law + power + scope). | The **joint readout** (A-1e), any **cleverer arithmetic predictor** of `e([d]G)`, and the **CM/Hecke route** — all OPEN. The phrase "0 operational / impossible" reads wider than the layer it proves. **Directly contradicts A-1b/A-1e** (same session): §8 says "closed", the audit says "open and untested". Kept as a hanging contradiction (§E). `NOTE_glv_orbit_carry_conservation_v1` §8. |
| **A-2b** | Memory `secp_N2_supersingular_closed`: headline "**N2 … CLOSED, `A_new` supersingular at secp `[PROVED]`**" — **read first, every session start.** | Nothing clean: it even hedges *inside itself* ("pending independent adversarial re-derivation"). | `MASTER_v9` holds N2 **OPEN** (verified 24/24 at small p, **not proved for dimension 2**, load-bearing for §VII/P13). The index itself says "**NOT flat `[PROVED]`**." **H-1.** Owed a correction to match v9, or it mis-boots a false closure before any document is read. `AUDIT_memory_layer_v1` M-1. |
| **A-2c** | Index I4: "**SYMMETRY PROGRAMME DEAD, EXHAUSTIVELY OVER F̄ … do NOT run another symmetry search — closed at grade.**" | Nothing — "exhaustive over F̄" was exhaustive over the **wrong set** (deg G=7 odd ⇒ 8 branch points, stabiliser order 4). | The over-closure **hid the #26 theorem for five rounds**; the index self-corrects at L1114 but a grep-level read of the directive re-suppresses the search. Owed removal/qualification. `AUDIT_memory_layer_v1`. |
| **A-2d** | Various stale-firmer headlines: 120° law `[PROVED — exact]` (index/summary) and N1 "RESOLVED" (summary). | 120° is one-sided (`min_l g_l ≥ g_true`, real inflation witness) ⇒ `[VERIFIED]`; N1's own ledger row says "Open on uniformity". | v9/v10 already walked these back; the memory/summary layer never recorded the downgrade. `AUDIT_memory_layer_v1` I2; `LIVE_LEADS_MAP_v1` Overclaims. |

**Net of §A.** The suppression ran, was mostly caught this session (A-1a–c), and left one buried
positive to recover (A-1d) and one open residue mislabeled closed (A-1e / A-2a). The over-closures
(A-2) are concentrated and nameable — the memory layer plus one §8 sentence — **not pervasive rot**;
reporting them as "everything is inflated" would be the opposite over-collapse.

---

## §B — NEW POSITIVE LEDGER (2026-08-15 → 08-17), graded, with the numbers

Local IDs `H1–H11`; the "master slot" names where each should land on promotion (after `compile-diff`).
Every row is a *lever stated as a lever*, or an exact structural fact — none is required to beat generic
`√n` or touch ECDLP.

### The public-key readouts (exact, at secp scale — facts about coordinates, not statistics)

- **H1 · GLV/cubic-character orbit readout on the REAL unsolved puzzle keys** — `[VERIFIED — exact]`.
  From public `(x,y)`: cubic exponent `e` (`x^((p−1)/3)≡β^e`), sign `s=[y>p/2]`, `y mod 2`, and the
  order-6 `⟨φ,[−1]⟩` orbit position — all exact, O(1), reproducible on **#135 `(e,s,ymod2)=(1,0,0)`**
  and **#140 `(0,1,1)`** (both on-curve, exact-integer reproduction in-file). *Master slot: extends
  M-family GLV readout.* `CONFIRMED_glv_orbit_readout_puzzles_135_140_v1`.

- **H2 · GLV-orbit carry conservation law** — `[PROVED + EXACT]`. In Eisenstein b-coordinates the
  lift carry is `c(X) = (0, ⌊u−v+½⌋) ∈ {0, ±ω}`; exact law `Pr[c=0]=3/4, Pr[c=±ω]=1/8` (empirical
  100k: 0.7492/0.1257/0.1252). **Orbit conservation:** `ω²c(X)+ω·c(βX)+c(β²X)=0` forces the carry
  triple around any GLV orbit into one of `(0,0,0)/(ω,ω,ω)/(−ω,−ω,−ω)` — a GLV-orbit invariant
  (verified 20k orbits + all 82 solved keys + all 6 exposed puzzles). Norm shift exact
  (`s(βX)=s(X)` on the 3/4-locus). **Joint public law is the exact product `6 × {3/4,1/8,1/8}` = 18
  classes; label ⊥ carry, provably.** *Master slot: new P-row + §XIII structural.*
  `NOTE_glv_orbit_carry_conservation_v1`. **Carries A-2a's over-closure — grade the §8 consequence to
  its layer.**

- **H3 · Core-gate coordinate flap `eps(x)`** — `[PROVED + EXACT — coordinate object ONLY]`.
  `eps(x)=0 ⟺ |u−v|≤½`; locus **exactly 3/4** (empirical 74.97%); sufficient gate `s<3/16 = π√3/8`
  (empirical 67.93%); `s≤¼` necessary. 2,000,000 lifts, 0 violations. **v3 correction (load-bearing):**
  this is the **coordinate flap `eps(x)`** (x-only, no `d`) — **NOT** the scalar carry `ε_LBE=[r₁+r₂≥n]`
  (which contains `d`; `s<3/16` fails it, 21–93 violations). `eps == ε_LBE` is **OPEN**; nothing here
  closes it. Owed: verify `|u−v|≤½ == build.eps` on the project script (declared, not tested).
  `CONFIRMED_core_gate_carry_epsilon_zero_v3`.

### The k=3 phase channel (model scale, both CM & non-CM)

- **H4 · k=3 phase channel `3·arg T(a₀,b) ↔ χ₂(b)`** — `[EMPIRICAL / VERIFIED-scope]` + a PROVED piece.
  See A-1a for the numbers. **Parity lemma PROVED** (p mod 4 dichotomy: `p≡1` ⇒ channel in `Re=cos3θ`,
  `Im≡0` forced; `p≡3` ⇒ `Im=sin3θ`). **Un-normalized channel PROVED** (H5). Universal, flat:
  CM≈non-CM≈**0.30** in the full group (no CM>non-CM hierarchy — the proposed hierarchy did **not**
  reproduce). New valid control passed (coordinate multiplicative-scramble `x_d→x_dᵏ` kills it ⇒ needs
  the real Weierstrass group-law coords); a false "eigenvalue-restriction" prose claim caught (channel
  survives `a₀=2`, is `a₀`-generic). **OPEN:** phase-normalized `|mean_QR|≥c`. Does **not** leak the
  scalar. `CONFIRMED_k3_phase_channel_weierstrass_v1`, `NOTE_k3_analytic_reduction_v3`.

- **H5 · slope² identity + un-normalized channel** — `[PROVED]`. For `P₁+P₂+P₃=O`, group law forces
  `x₁+x₂+x₃=m²` (slope²) ⇒ `χ₂(x-sum)=+1`, so `W(0)=Σ_{O-sum}χ₂(x-sum)=n²−O(n)>0` (rigorous;
  `#{m=0}=O(n)`). ⇒ `Σ_b χ₂(b)T(a₀,b)³ = i√p·(n²−O(n))`. Identity is φ-covariant. *Master slot: new
  P-row; explains `a₀`-genericity.* In `CONFIRMED_k3_phase_channel_weierstrass_v1` / compendium piece 2.

### The μ₆ CM lever — mapped, including where it stops (`COMPENDIUM_mu6_lever_v1`)

- **H6 · μ₆-quotient relation multiplication** — `[VERIFIED — exact]`. μ₆-invariant factor base:
  CM multiplies each 3-term relation into **exactly 6**, quotients `|F|→|F|/6`; non-CM (μ₂) → exactly
  2. At matched effective base (~230 orbit-reps): **3× CM advantage**. **Scope (binding): constant-
  factor (≤6×), NOT an exponent change** — does not alone beat generic `√n`; automorphism-accelerated
  index calculus is a KNOWN technique. p≈4000, m=3. `RESULT_mu6_quotient_relation_multiplication_v1`.

- **H7 · Characters index the orbits** — `[EMPIRICAL — real skew]` + scoped null. `e₁+e₂+e₃ mod 3`
  (μ₆-invariant) grades orbits `{0:123528, 1:117054, 2:112212}`, skew toward 0 ≈ **9σ** (orbit level);
  χ₂-product skew ≈ **8σ**. **Real weak grading.** **Follow-up (scoped NULL):** the grading does **not**
  block the matrix — block incidence roughly uniform (all 4 χ₂-blocks 97–147), fill-in graded **940 vs
  random 1008** (~7%, inside noise). Scoped to {this construction, p≈4000, χ₂/e-sum gradings}.
  `RESULT_mu6_characters_index_orbits_v1`.

- **H8 · μ₆ yield excess** — `[EMPIRICAL — EXPLORATORY]` (already folded in v10 as M25/M26). On a random
  factor base with #E-matched pairing, j=0 CM curves yield more Semaev decompositions per target than
  non-CM at **all five** `|V|∈{4..8}`; `T1(j0)=log(Q_j0/Q_nonCM)` grows ~linearly (0.187, 0.338, 0.509
  over |V|=4,5,6; perm_p=0.0000) ⇒ ratio **~exp(|V|)**, ≈**2.3× at |V|=8**, **no saturation observed
  through |V|=8**. **Caveats (binding): `|V|≤8` tiny; NO license to extrapolate to attack-scale
  `|V|~p^c`; model scale p≤8011; no `2²⁵⁶` transfer.** OPEN: mechanism (→H6); **yield → full relation-
  collection-COST translation (the consequential, unrun test)**. `RESULT_semaev_cm_relation_yield_v4`.

- **H9 · μ₆ solving-degree lever — scoped NULL, both coarse and fine** —
  `[VERIFIED — NULL, matched-quo, m∈{2,3}]`. The σ-structure is **real & exact** (S₄ σ-invariant weight
  κ=0; target-orbit ideal restores a clean 12/12/12 ω-isotypic split). But: the naive `Δ_iso` statistic
  is **forced ≡0** (experiment-designer refuted it); the corrected non-forced `δ_r ≤ 0` in **all 13
  cells** (never a lever); and — the strongest single statement — the **full graded Betti resolution is
  IDENTICAL** CM vs #E-matched non-CM at matched quo (quo=2, m=2). **The μ₃/ω symmetry supplies no
  distinguishing syzygies at accessible scale.** OPEN (not closed): (i) more matched-quo Betti cells /
  m=3; (ii) **m=4/5** (S₅/S₆ compute-intractable, >240s) — a *mechanism* question, null does NOT extend;
  (iii) the yield/phase channels (separate live positives); (iv) full IC-cost.
  `RESULT_mu6_isotypic_solving_degree_P2b_v1`, `RESULT_mu6_finer_syzygy_R1R2_v1`.

### The isotypic trace and the exclusion track

- **H10 · Isotypic trace `ℓ(d)=dlog_{A_new}(S([d]G))`** — `[VERIFIED — exact, scope p=43 / |A_new|=1893]`.
  **Positive:** orbit-covariant — `ℓ(λd)=k·ℓ(d) mod 1893`, `k∈{1849=43², 587}`, satisfying `k²+k+1=0`.
  **Levers refuted at scope:** affine-in-`d` **NO** (13/15 fail); homomorphism **NO** (0/3); affine- and
  quadratic-**in-GLV-halves NO** (15/15 inconsistent) with the **positive control firing** (synthetic
  affine recovered 0/15). Structural crux: `A_new` supersingular, embedding degree 3 (`631|p³−1`) ⇒ its
  DLP **transfers to `F_{p³}*`** (MOV/Frey–Rück) — but `Hom(E,A_new)=0` (E ordinary, A_new supersingular)
  blocks reaching it from `[d]G`. **Both the affine lever and the MOV lever refuted at this scope.**
  OPEN: whether the non-homomorphic orbit-covariant `ℓ(d)` carries **partial** `d`-info beyond the orbit
  label (no mechanism identified; any such info still sits behind the `A_new` dlog). Blocked on a faster
  `A_new` realization for scale (Singular wedges above p=43). `RESULT_isotypic_trace_lever_status_v1`.

- **H11 · Public-readout → `d`-residue exclusion track** — `[EMPIRICAL — scoped NULL, plant-fired]`.
  **Hard exclusion:** ZERO unforced empty cells in `(V(x,y), d mod k)` at populated granularity
  (`killed-res = 0/k`, min occupancy > 0), curves m=1249/2143. **Soft exclusion:** no under-representation
  beyond a matched μ₆-structure-preserving control — `bits_removed_net ≈ ±0.05` (≈0) for every
  `k∈{2,3,4,6,7}`, curves p=547/907; the raw χ₃=2 hint (32/37/43) did **not** survive the omnibus (noise,
  as pre-flagged); Holm survivors NONE. **Fence premise: scoped to reachable scale, NOT "impossible / no
  exclusion"** — a sub-~0.2-bit soft exclusion is below this power. Live redirect kept open (parallel
  fence-line: any public invariant of `[d]G` computable from `d` in < 1 scalar-mult — GLV proves ≥1
  exists). `RESULT_exclusion_hard_empty_cells_v1`, `RESULT_t2d_soft_exclusion_v1`.

---

## §C — The load-bearing synthesis: the μ₆ lever is MAPPED, including where it stops

One object (`y²=x³+7`, CM by `ℤ[ω]`), one clean shape:

- **Relation-collection side — μ₆ ACTS (measured/proved):** yield ~exp(|V|) (H8); 6× relation
  multiplication (H6); φ-covariant slope² relations (H5); characters grade orbits ~9σ (H7).
- **Linear-algebra side — μ₆ STOPS (two independent instruments agree, scoped):** the grading does
  **not** block the matrix (H7 fill-in null) **and** the solving degree / full graded Betti is identical
  CM vs non-CM (H9). **Scoped to m∈{2,3}, accessible scale — NOT "no linear-algebra structure ever."**
- **The honest live frontier of the whole μ₆ line:** the **μ₃-graded syzygy / staircase module** beyond
  a single matched-quo Betti cell (H9 open-i), **m=4/5** (intractable here), and the **yield → cost
  translation** (H8, the consequential unrun test). The lever is real; whether it changes an *exponent*
  is untested and is the question that matters.

---

## §D — RECOVERED / still-homeless results (invisible to every top-level doc)

The Aug-15 audit surfaced a large body of live results reachable from **no** current top-level document
because the `ADDENDUM_1/2/3` layer was never reconciled into the master (referenced 0 / 1-loss-admission
/ 0 times in v9). **This is selective omission under a false "reconciled across both addenda" cert —
NOT inflation** (0 grade-inflated, 0 firmed across all three addenda). Full map: `LIVE_LEADS_MAP_v1`;
consolidated ledger: `RECOVERED_RESULTS_v1`. The high-value homeless items:

- **E3 cubic difference-set** (A-1d ★★) — the one item asking for a *measurement*.
- **Twist-orbit forced landscape** (ADD2 B1.7): exact frame identity `⟨f_a,f_b⟩=nI−J`; Parseval
  `Σ|V(a)|²=n(n−1)`; 3-pt bispectrum ≡ 0 — `[PROVED — forced]`. **Exact constraints the random-target
  nulls do NOT satisfy — a decidable discriminator on the `V(a)` object.**
- **Sub-Weil reduction** (ADD2 B1.3): `S_y≤2 ⇔ sign of one L-poly coefficient`; `|V₁(a)|≤√3·√p`
  (obs max 1.932√p @ p=547) — `[PROVED — algebra]`.
- **The entire d-side `(n,k,D)` / Dirichlet-lattice thread** (ADD1-only): reciprocal-floor lattice,
  Farey 1-D coprimality net + its ℤ/2 symmetry (non-generic vs matched control), T=2 stratum. Invisible.
- **N1 ½-saturation sharpening** (ADD1/2): parity refuted at 10 primes, localized to the extremal tail,
  candidate [−1]-involution 2+2 split; the `½=2/4` rigidity-budget account. v9 reverted to "no account."
- **ADD3 deficit narrowing** (N7): the sub-Rayleigh −13.99σ deficit is NOT in the μ₃ b-frequency channel
  nor the μ₃ real-part phase isotype; next probes named (higher-order phase invariants; c=±b diagonal;
  p-scaling). None folded.

**These are levers you already have — re-entering them is cheaper than new work.** The intersections
`★1–★5` in `LIVE_LEADS_MAP_v1` (open anomaly paired with a proved neighbor on the *same* object) are the
ripe targets, clustered on Thread 1 (`A_new` / `V(a)`).

---

## §E — HANGING CONTRADICTIONS (preserved, not resolved)

| # | The contradiction | Load-bearing because |
|---|---|---|
| **E-new** | **Orbit-geometry: "closed layer, 0 operational" (H2 §8) vs "joint readout open and untested" (A-1b/e).** Same session, opposite verdicts on adjacent objects. | §8 reads as closing what the audit holds open; grade §8 to its layer, keep the joint readout OPEN. |
| H-1 | `A_new` supersingular at secp: **proved-via-Cartier** (summary) vs **open dim-2 assumption** (v9 N2). Memory stamps CLOSED (A-2b). | Door P13 (`Hom(E,A_new)=0`) rests on it; H10's crux uses `Hom(E,A_new)=0`. |
| H-2 | Stickelberger **(D2)** citation: discharged w/ 3 Katre caveats (ADD2) vs owed debt (v9); "(D2)" undefined in the master. | A `[PROVED — modulo D2]` law and intersection ★1 rest on it. |
| H-3 | **λ₃**: dead gauge artifact (ADD1 ret. 30, two scripts) vs "real, broadband, OPEN" (v9). | v9 lists a debunked artifact as an open finding. |
| H-4 | **census identity** graded `[VERIFIED]`/OPEN/`[PROVED — modulo D2]` — three grades, one document. | Same object, three grades. |

---

## §F — OWED (gates and tests; logged, not discharged here)

1. **`compile-diff`** — the mandatory gate for a consolidated/handover document. Attempted 2026-08-17
   (rate-limited, UNAVAILABLE); **not re-run this session** (no unprompted agent spawn). This handover is
   `[PROVISIONAL]` until it clears; the mechanical self-audit (§top) does not substitute for its
   context-isolation. **No grade in §B is promoted into the master until it clears.**
2. **`citation-verifier`** on **Caminata–Gorla** (solving degree ≥ last-fall degree, eprint 2021/1611)
   and on "no competitive prime-field summation-poly index calculus known" — H9 rests on the first; the
   second gates any μ₆-lever cost claim. Extension-field LFD literature must NOT be cited as a prime-field
   secp bound (`CORRECTION_semaev_cm_yield_mechanism_literature_v1`).
3. **E3 (A-1d) owes a MEASUREMENT** — MC-correction across the pre-registered family; reproduction (exact
   arithmetic); a matched Farey/fundamental-domain null **sharing the signal's forced symmetries**;
   out-of-sample on the constructed known-generator set. Until then it is neither signal nor noise.
4. **H3 owes** the `|u−v|≤½ == build.eps` cross-check on the project script.
5. **The addendum layer (§D) owes a real reconcile** into the master, or the "reconciled across both
   addenda" certificate must be struck. This handover surfaces the items; it is not the reconcile.
6. **Memory corrections owed:** `secp_N2_supersingular_closed` (A-2b, mis-boots first-read); index I4's
   "do NOT run another symmetry search" (A-2c, re-suppresses a search that already hid a theorem); the
   120°/N1 stale-firmer headlines (A-2d).
7. **H-1 … H-4 + E-new** each owe a reconciliation decision.

---

## §G — Provenance

Compiled 2026-08-17 from the primary files, read for their **result tables** (not headline conclusions),
per the user's suppression-bias instruction. Grades inherited from sources; nothing re-graded up. Primary
records (the truth): `COMPENDIUM_mu6_lever_v1`, `CONFIRMED_glv_orbit_readout_puzzles_135_140_v1`,
`NOTE_glv_orbit_carry_conservation_v1`, `CONFIRMED_core_gate_carry_epsilon_zero_v3`,
`CONFIRMED_k3_phase_channel_weierstrass_v1`, `NOTE_k3_analytic_reduction_v3`,
`RESULT_mu6_quotient_relation_multiplication_v1`, `RESULT_mu6_characters_index_orbits_v1`,
`RESULT_mu6_isotypic_solving_degree_P2b_v1`, `RESULT_mu6_finer_syzygy_R1R2_v1`,
`RESULT_isotypic_trace_lever_status_v1`, `RESULT_exclusion_hard_empty_cells_v1`,
`RESULT_t2d_soft_exclusion_v1`, `RESULT_semaev_cm_relation_yield_v4`, `AUDIT_session_conclusions_v1`,
`AUDIT_narrative_conclusion_layer_v2`, `AUDIT_memory_layer_v1`, `LIVE_LEADS_MAP_v1`,
`RECOVERED_RESULTS_v1`. Predecessor handover: `POSITIVE_FINDINGS_MASTER_v10.md` (2026-08-15).
