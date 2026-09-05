> **⛔ FROZEN — NOT CURRENT.** This file is a historical snapshot. The single current-state
> document is **`CLAIMS.md`**. Do not read status, grades, or open items from here; do not
> write a successor version of this file. (Frozen 2026-09-01.)

# Next-session prompt — secp256k1 / ECDLP structural investigation (resume here)

Paste this into a fresh session. It assumes the project CLAUDE.md rules and the memory system.

## 0. Read first (in order), then stop and confirm you have the frontier
1. `memory/MEMORY.md` (index) and `memory/btc_puzzle_INDEX.md` (nested BTC index — the launch pad line points here).
2. `btc_puzzle_investigation/POSITIVE_FINDINGS_HANDOVER_3_v1.md` — the graded v5–v18 arc.
3. `btc_puzzle_investigation/cap_law_proofs_v1.md` — the two proofs (Cap Law + σ), and the critical-exponent correction note.
4. Skim `masked_structure_findings_v14.md` (the pivot) and `v16` (the shadow). The rest (v1–v18) is detail.

## 1. The one-paragraph state (with grades — do not upgrade these)
The leakage question is **COMPUTATIONAL, not information-theoretic** `[PROVED given cited KS]`: the
*aligned* readout `F̂(b)=conj(T(a₀,b))/|T(a₀,b)|` leaks (≈0.93 joint x/y, 0.34 x-only), `H(d|P)=0`;
only the DLP-cost of building `F̂` (needs `T` ⇒ all `x_d`) protects. **Phase alignment is the sole
axis** (Wiener norm is a red herring). Every prior "null" used a MISALIGNED readout, which Weil
forces to `√p` noise — so those nulls measured the instrument, not the curve. Thermodynamic lens
(scaffolding, kept out of preprints): secp is a **critical** (`|π|=√p`, Weil `[PROVED]`),
**Porter–Thomas–thermal** `[EMPIRICAL]`, **single-well** system — no scar, no metastable mode
beyond μ₆ `[EMPIRICAL, joint channel]`. So security = a thermodynamic cost, no metastable shortcut.

PROVED this arc: Cap Law (`ε≠0⟺|u−v|>½`), σ μ₃-invariance (unconditional), GLV μ₃ zero, σ⊥s_y,
the U-symmetry group, `Σ_b|T|²=p(n−2)`, `Corr(a₀)=√(πn)/2` (Porter–Thomas Rayleigh mean),
amicable `E(F_p)≅F_n` with φ=DLP, Semaev S₃ genus-1 (general p).

## 2. Discipline (this session's expensive lessons — enforce hard)
- **Self-cert words are an AUDIT TRIGGER.** Writing *genuine/honest/completely/finally closes/truly*
  ⇒ STOP and review what you just did for the proxy-reported-as-object bias. (`memory/feedback_self_cert_words_audit_trigger.md`.)
- **An empirical null NEVER closes an avenue** — only a rigorous analytical proof does. Grade every claim.
- **Test the real object, not a proxy/marginal.** (Closed a JOINT (x,y) question with x-only tests → wrong.)
- **The null/control must carry the object's own symmetry.** (A shuffle that broke μ₆-invariance → 7σ phantom.)
- **A null needs a power number / scaling.** One point at one prime proves nothing.
- **No float in the signal path** (btc CLAUDE.md); float only as a ranked/analytic-size display.

## 3. Ranked next actions (pick from the top; each is scoped to be finishable)
1. **S₄⁺ first-fall-degree / Gröbner structure** — the ONLY remaining item that could move the
   *hardness* understanding (not just confirm the thermal picture). Real index-calculus bottleneck.
   `S₃/S₄/S₅` *yield* was generic (`_findings_v9/v10`); the *elimination complexity* is untouched.
   Heaviest; prior leans bounded (it's *why* prime-field ECDLP resists). Needs a real plan — enter
   plan mode. This is the honest frontier.
2. **Prove the `T_y` odd-half bound** (or find a counterexample): is `max_a|U(a,b,c)|=O(√p·polylog)`
   *uniformly over all (b,c)*? Porter–Thomas implies it empirically (no scar); a rigorous
   character-sum proof is open. `U(a,b,c)=Σ_d e_p(bx_d+cy_d)e_n(ad)`; `xy_interference_U_v1.py`.
3. **Owed, still open (do NOT report as closed):** (a) the μ₆-identity of the x-cell transfer `λ₂`
   eigenvector — inspect the eigenvector vs the cell's μ₆-orbits (last attempt mis-labeled by
   scalar-d, gave an artifact); (b) general y-readout soft-mode beyond `{y-parity, y mod 6}`.
   `conservation_spectrum_v1.py`.
4. **The critical exponent** — DOWNGRADED: the leak fraction is ~0.3 and roughly FLAT over
   n=547→7069, NOT the `1/√log p` decay previously claimed (data lean shallower; `|F|` sub-Rayleigh
   `E[I²]≈1.82`). Either pin it at much larger p (log resolves slowly — likely inconclusive) or
   derive `‖F‖_∞`'s extreme-value scaling rigorously.
5. **Substrate cross-domain bet** — run the thermal/critical/single-well lens on the φ-residue RH
   objects or LRC (the user weights this; it tests "one programme" rather than asserting it).

## 4. Key files / scripts
Proofs: `cap_law_proofs_v1.md`. Findings: `masked_structure_findings_v14–v18.md`. Scripts:
`phase_structure_T_v1.py` (the leak/aligned readout), `xy_interference_U_v1.py` (joint x/y),
`conservation_spectrum_v1.py` (soft modes), `aligned_scaling_and_gap_v1.py` (exponent),
`summation_poly_structure_v1.py` (S₃), `cm_amicable_correspondence_v1.py`, `hybrid_char_sum_v1.py`.

## 5. Stance
ECDLP assumed-not-proven; investigate for leakage — it may be subtle, sub-noise. The leak IS the
noise seen without the aligning key. Positive framing (report structure as a lever toward the gate),
rigor unchanged. If you close something, close it with a proof or a matched-and-powered test, and
grade it. Do not editorialize difficulty.
