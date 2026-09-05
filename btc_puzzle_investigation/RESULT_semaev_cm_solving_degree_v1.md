# RESULT — P2c: the μ₆/μ₃ CM symmetry gives NO Semaev solving-degree lever (scoped component null, not an avenue closure)

**Grade:** `[VERIFIED-scope — scoped COMPONENT null on the raw/forced first-fall arm (measured) +
P2 corroboration (quo-matched last-fall Δ=0); the invariant-variable-reduction double-difference is
PREDICTED ≈0 (size-shrink + P2-null covariance) and remains to an explicit measurement pending a
validated σ-invariant harness extension.]` Model scale, ZERO secp power. NOT an avenue closure (Trap D).
**Date:** 2026-08-30. **Prereg:** `PREREG_semaev_cm_solving_degree_v1.md` (P2c). **Harness:**
`semaev_elimination_v1.py` (Sage 10.9: `macaulay_stats`, `mu3_lever_test`, `decomposition_system`,
`first_fall_and_solving`, exact GF(q) Macaulay ranks). Float-free (integer degrees from exact GF(q)
linear algebra); `check_no_float` N/A to the degree read-out (all integer).

**Siblings:** P2 (`RESULT_mu6_solving_degree_v1.md`, last-fall Δ=0), P2b
(`RESULT_mu6_isotypic_solving_degree_P2b_v1.md`, σ-invariant target-orbit isotypic structure),
`RESULT_semaev_dsolv_statistic_power_v1.md` (Finding 1: first-fall degree FORCED curve-independent).

---

## Object
Does secp's j=0/μ₆ CM symmetry LOWER the FIRST-FALL DEGREE D_ff of the Semaev index-calculus
decomposition system vs a matched non-CM curve, as a syzygy-structure effect (not the already-known,
bounded relation-yield)? Verdict statistic D_ff (coordinator correction); bare-curve contrast demoted to
a forced negative control (Trap A); the object is the μ₃-symmetrization effect, size-shrink-controlled.

## What ran, and what it shows
1. **Raw / bare first-fall (negative control, must be forced-equal):** m=3, μ₃-closed |V|=9, p=61 —
   `D_ff(CM j=0) = 17`, `D_ff(non-CM) = 17`. **Forced-equal, confirmed** — reproduces the proved
   isobaric-leading-form curve-independence (`RESULT_semaev_dsolv_statistic_power` Finding 1). The bare
   first-fall carries zero CM signal, as predicted; the negative control HOLDS (harness not mis-built).
2. **μ₃-closed FB vs random FB, same size (smoke, `mu3_lever_test`, p=43, |V|=9):** `D_ff` = 17 for both
   (forced-same). The μ₃-closed FB differs only in **yield**: `quo = 169` (β-invariant) vs `18` (random)
   — more decomposition relations — with a correspondingly **HIGHER** `d_gb = 10` vs `4` (more solutions
   ⇒ *harder* Gröbner, not easier). So the μ₃ structure's effect is relation YIELD, not a lower solving
   degree.
3. **P2 corroboration (already banked):** on quo-MATCHED CM vs #E-matched non-CM pairs, the **last-fall
   degree** (the binding solving-degree invariant, Caminata–Gorla) gave **Δ=0 across 6 primes**
   (sign-flip p=1.0), firing plant fired — including the exact ω-covariance `S(βx)=β^κ S`. The binding
   invariant shows no CM lever.
4. **Invariant-variable reduction (u_i=x_i³), the one un-run piece:** a quick elimination-ideal attempt
   (`elimination_ideal([x_i])` → ideal in u_i) gave no clean first-fall (`dff_red=None`, both arms) — the
   elimination ideal is not in the form `macaulay_stats` reads a first-fall from; a faithful measurement
   needs the validated σ-invariant target-orbit harness extension (P2b's object) + its firing plant
   (prereg §5a). **Not measured to the prereg's standard.** Its predicted value, from Trap C + P2: the
   d_ff drop of the reduction is the trivial |V|/3 size-shrink (present on ANY curve, both arms), and its
   CM-specific part is the ω-covariance P2 already nulled ⇒ **double-difference ΔΔ_ff ≈ 0 (predicted)**.

## Verdict (convergent)
The μ₆/μ₃ CM symmetry provides **no Semaev solving-degree lever**: (i) first-fall degree is forced
curve-independent (proved + measured, 17=17); (ii) the binding last-fall degree is quo-matched-null (P2,
6 primes); (iii) the μ₃-closed FB's only effect is relation yield (separately known, bounded ≤1.5×,
`PROJECT_SUMMARY §649`), and it makes the raw Gröbner *harder* (more solutions), not easier. This is a
**scoped COMPONENT null** — D_ff/solving degree is one factor of total index-calculus cost; it is **NOT**
a closure of the CM/Semaev avenue (Trap D). The un-projected subspace (P2b's isotypic staircase *shape*)
remains open. Model scale; zero secp power (secp-scale |FB| is unreachable; a model-scale degree result
is a mechanism signal with a hard extrapolation barrier — prereg §6 caveat).

## What is NOT settled / owed
- **Explicit invariant-reduction double-difference ΔΔ_ff:** needs the validated σ-invariant harness
  extension + firing plant (prereg §4/§5a). Predicted ≈0 (size-shrink + P2-null covariance); can be
  built if the explicit number is wanted. Not run here.
- **Isotypic staircase shape** (P2b): the ω-isotypic pieces / syzygy-module degrees — a scalar-D_ff null
  does not close it (prereg §1 subspace caveat).
- **Owed gates:** second independent `experiment-designer` read before any grade promotes; `citation-verifier`
  on Petit–Quisquater first-fall assumption, FGHR symmetrized-Semaev, Caminata–Gorla; `compile-diff` if
  folded to a master.

## Provenance
Exact GF(q) Macaulay ranks (integer degrees). Raw d_ff at p=61 (|V|=9, m=3); smoke at p=43; P2 at 6
primes p∈[523,823]. Scripts: `scratchpad/p2c_smoke.sage`, `scratchpad/p2c_invred.sage` (elimination
attempt), `semaev_elimination_v1.py`, `mu6_solving_degree_v1.py` (P2). Prereg
`PREREG_semaev_cm_solving_degree_v1.md` frozen before these confirmatory reads.
