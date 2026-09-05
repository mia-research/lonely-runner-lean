# DEVIATIONS — PREREG_cm_jointset_semaev_r5_v1.md

Freeze protocol: post-freeze changes disclosed here. The OBJECT, statistic, multiset stratum, matched
null, plants, exactness rule, and falsification table are UNCHANGED. One RATIONALE correction (D1),
found by the runner's KAT before any data was measured.

---

## D1 — [KAT] the coincident-x guard is CONSTRUCTION HYGIENE, not trivial-zero removal (odd r=5)

**Frozen (§2R/§8).** The prereg states the coincident-x guard removes tuples where "a repeated
x-coordinate forces `S₅=0` as a curve-INDEPENDENT trivial relation (`+P−P+…=O`)", by analogy to the
S4 (r=4) case the citation-verifier established.

**KAT finding (`cm_jointset_semaev_r5_v1.py --selftest`, before any tier run).** That rationale is
**FALSE for ODD r=5.** A single coincident pair (x₁=x₂) makes `S₅=0` at **4/198 ≈ 2%** — the SAME rate
as random distinct-x tuples (4/283 ≈ 1.4%), i.e. NOT forced. Reason: `S₅=0 ⇔ ∃ signs Σε_iP_i=O`; with
x₁=x₂ one has `P₂=±P₁`, so a `+P₁∓P₂=O` cancellation uses two of the five points, but the remaining
THREE (`±P₃±P₄±P₅`) must then independently sum to O — which is not forced. Five points cannot be tiled
into disjoint cancelling pairs (odd count), so — unlike the even r=4 case (x₁=x₂ ∧ x₃=x₄ ⇒
`+P₁−P₂+P₃−P₄=O` forced) — coincident-x does not force a trivial `S₅=0`.

**Correction (D1).** The guard is **KEPT**, with the corrected rationale: it is **construction hygiene**
for the Sylvester/resultant build. `S₅ = Res_X(S₄(x₁,x₂,x₃,X), S₃(x₄,x₅,X))`; when the S₃-pair coincides
(`x₄=x₅`), the quadratic's leading coefficient `(x₄−x₅)²=0` drops its degree and the 6×6 Sylvester
determinant no longer equals the true `S₅` (it picks up a spurious `lead(g)`-weighted factor). The guard
`len(set(x_i)) < 5 ⇒ skip` removes exactly those degenerate builds, keeping every summation-polynomial
degree honest. It remains applied IDENTICALLY to both arms (via `draw_sets` rejecting repeated scalars,
== distinct-x in-interval), so it is a matched removal of a construction artifact, curve-independent and
Δ-cancelling — not a label-dependent filter.

**Consequence for the result:** none on the verdict — the guard is still applied (so all measured `S₅`
values are from non-degenerate builds), and the KAT confirms `S₅` vanishes on 80/80 true 5-relations and
is generic-nonzero (4/283) otherwise. Only the *stated reason* for the guard changed. The
citation-verifier gate (§10) should note this odd-vs-even distinction when it reads the r=5 case.

Recorded 2026-08-25, at runner KAT, before any tier was measured.
