# NEXT SESSION PROMPT — L-mono GKR discriminating moments (+ Brick E owed items)

**Written 2026-08-23.** Read this first, then `PLAN_lmono_monodromy_campaign_v1.md`, then the two
artifacts from the 2026-08-23 session (§2 below). Follow `btc_puzzle_investigation/CLAUDE.md` (counter-prior,
no-float, burden-on-closure) and the root `CLAUDE.md` gate table.

## 0. Orientation (do NOT re-derive these)
- **Real date is 2026-08-23.** Two accounts write the same UNTRACKED corpus (repo pinned at f71f72a).
  Before starting ANY thread, `ls -t RESULT_* NOTE_* PREREG_*` and check the HANDOFF_LOG — the 2026-08-23
  session was burned twice by re-doing work already on disk.
- **Master is v14** (`POSITIVE_FINDINGS_MASTER_v14.md`), NOT v12. Frontier = the **A_new two-prong**
  (Prong 1 = A_new supersingular ∀ p≡3 mod4, `[PROVED — 3 routes]`, `RESULT_anew_..._cartier_route_v3`;
  Prong 2 = Brick E) **+ the L-mono monodromy campaign**. The E3/difference-set line is CLOSED and folded
  into v14 — do not reopen it (a prior session re-ran the E3 owed measurement + group-law E3; both were
  already in v14).
- **Two other-account Sage jobs may still be running** at 99% CPU: `anew_sorder_sweep_v1.sage.py` (the
  S-visibility ground truth, feeds L-mono §7.3 a=0 unification) and `d2_nonabelian_sweep_v2.sage.py`. Do
  NOT kill them. Check if they finished and produced results.

## 1. Completed 2026-08-23 (do NOT redo)
- **Brick E — DONE.** `RESULT_brick_e_cd_degree_v2.md`: `c⁺(d)` at the generic degree ceiling at all
  well-posed rungs p∈{43,127,547} (D_obs = |Q|−1), degree-STABLE across ≥2 POWERED rungs {127,547},
  control-ii FIRES → the low-degree cover-scramble channel is RETIRED WITH POWER. `[VERIFIED-scope]`, null
  arm. Plan-correcting finding (D5): the frozen ladder was ill-posed at 4/5 rungs (needs `q|p²+p+1`, `q≥n`;
  the prior p=163/211 runs were on ill-posed rungs). Tools now validated: `brick_e_rung_v2.sage`
  (Pohlig–Hellman + cyclic projection + control-iv `I2=Fq(-1).sqrt()`), `brick_e_analysis_v2.py`
  (Newton-divided-difference O(|Q|²) fitter — the v1 O(|Q|⁴) fitter was infeasible).
- **L-mono — first GKR-input piece.** `NOTE_lmono_gkr_input_1point_v1.md`: the measured 1-point marginal
  `t=Im(V₁)/(2√p)` is distributionally EXACTLY the SU(2) half-trace `cos θ` (4M-sample group-Haar MC,
  m₄=0.125 matches). A convention error (`t=−sin(θ+π/3)`) was caught by the decidable check and NOT written
  into a result — see §3's warning.

## 2. THE PRIMARY TASK — the GKR discriminating moments (L-mono §7.1 / PLAN §5A)
Prove (Route A, Katz/Goursat–Kolchin–Ribet) that the geometric monodromy of the twist sheaf
`{H¹_c(E, L_{χ₂(y)} ⊗ L_{χ_a})}_a` IS the candidate `G = SL₂ (diag on W) · μ₃ (Kummer on W⊗ψ) · {±1}` on
the rank-4 rep `H¹ ≅ W ⊕ (W⊗ψ)`. GKR: if the collection of det-twisted moment invariants of the rank-4
sheaf matches those of the candidate `G`, the geometric monodromy is `G` up to finite center — which
FORCES `α₂/α₁ = ζ₃` for all cells (T3 ⟹ T1/T2), the whole 120°-rigidity prize.

**Concrete sub-bricks, in order:**
1. **Symbolic rank-4 eigenvalue bookkeeping FROM the L-polynomial** (do this FIRST, symbolically, not
   informally — see §3). From `L*(a)=T⁴−e₁T³+e₂T²−e₃T+e₄` with the verified coefficient laws
   (`e₁=−V₁`, `e₂=e₁²−χ₂(−1)p` [P32], `e₃=χ₂(−1)p·e₁`, `e₄=p²`; `d2_twist_rigidity_certificate_v1.py`),
   derive the four eigenvalues as `{α, β, ψα, ψβ}` (ψ the order-3 Kummer char) and pin exactly how the
   measured `Im(V₁)/(2√p)` reduces to the W half-trace `cos θ` (the piece the MC settled numerically but
   that is owed symbolically).
2. **Candidate-group moment invariants on rank-4.** Compute (via clean group-Haar sampling — the validated
   `NOTE_lmono_gkr_input_1point` pattern, no L-poly conventions in the sampler) the `⟨det⊗⟩`-masked 4th
   (and higher) moment invariants of `SL₂·μ₃·{±}` in `W⊕(W⊗ψ)` — the discriminating invariants that
   SEPARATE this group from alternatives (the 1-point marginal alone does NOT: it is shared by
   SU(2)×{finite center} etc.).
3. **Match against the FFT-measurable cell statistics** (extend the sato_tane FFT route). Banked inputs to
   match: 1-point semicircle ✓, `m₄=1/8` ✓, 2-point iid ✓ (`RESULT_semicircle_null_and_verification`).
   The NEW content is the higher/det-twisted invariants.
4. **Only then** write the GKR argument as a proof, with the Katz citations passing `citation-verifier`.
   Falsifiers (PLAN §6): any cell with `g≠2`; `m₄=3/8` (torus — excluded); GUE-type 2-point (excluded).

**Alternative route B (sheaf-isomorphism):** establish `W' ≅ W⊗ψ` as sheaves (not just numeric [2,2]
factorization) via the ω-intertwining + Kummer structure of the Lang torsor. The 22-prime per-cell
certificates are its traces.

## 3. BINDING WARNING — eigenvalue/root conventions
`feedback_verify_root_system_against_defining_polynomial`: derive every eigenvalue/root claim FROM its
defining polynomial before stating it; do NOT reason informally about `ζ₃`/pairing/reality signs. The
2026-08-23 session made exactly this error (`t=−sin(θ+π/3)`), caught only by a decidable Monte Carlo. For
sub-brick 1, keep a DECIDABLE cross-check (a group-Haar MC or an exact `Z[ζ_n]` evaluation) beside every
symbolic claim; a symbolic relation is not "true" until a decidable check agrees.

## 4. Owed / secondary
- **Brick E control-iv (ρ-identity) at p=127/547** — the `F_{p²}` function-field instrument (~p² places over
  GF(p²)) did not complete in-budget; held 15/15 at p=43 and is scale-independent. Needs a cheaper `F_{p²}`
  instrument (sampled non-QR d, or a direct ρ-action) to re-confirm. Recorded OWED, not assumed.
- **Brick E extra rungs** (p=967 reps=151, p=1303 reps=208; qmax≥n) would extend degree-stability — cheap
  now (PH runner + Newton fitter). Not required (the ≥2-powered-rung condition is met).
- **compile-diff** before folding any of this into a master (v15) — mandatory gate, not yet triggered.
- **Date hygiene:** the E3 RESULT files carry internal dates 2026-08-18/19 but the group-law re-run was
  2026-08-23; cosmetic, low priority.
- **L-mono §7.3 (a=0 unification)** is blocked on the S-visibility sweep (`anew_sorder_sweep`) — check if it
  finished; `NOTE_anew_subgroup_structure_map_v1` has the ζ₃-eigenplane algebra and the open visibility law
  (the 2026-08-23 Brick E p=547 run resolved its "547?:613" conjecture — S SEES the 613-part, dropped 0).

## 5. Done-check for the primary task
A `[PROVED — reviewed]` (or `[VERIFIED-scope]` with a named gap) statement that the candidate `G`'s
discriminating moment invariants match the sheaf's, hence the geometric monodromy is `G` up to finite
center — with (a) the rank-4 eigenvalue derivation done symbolically + decidably cross-checked, (b) the
Katz/GKR citation passing `citation-verifier`, (c) every negative/closure carrying object+power+scope.

*Predecessors: `PLAN_lmono_monodromy_campaign_v1`, `NOTE_lmono_gkr_input_1point_v1`,
`RESULT_monodromy_sato_tane_at_scale_v1`, `RESULT_semicircle_null_and_verification_v1`,
`RESULT_n1_120deg_exact_v1`, `d2_twist_rigidity_certificate_v1.py`, `RESULT_anew_twisted_eigenvalues_nonabelian_v1`.*
