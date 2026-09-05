# Session plan — cheap exact wins: 120° cert (A), degree-10 cross-check (B), cross-j in series

**Mode:** investigation/collaboration. Counter-prior in force; lens open in notes, purist in artifacts. Log everything to `RESEARCH.md`. Close only with proof; tag lens claims as conjectures. No floats in the signal path.

## Recon summary (what's already done — do NOT redo)
- Pasted "live" threads #1–#4 are mostly at their V1-accessible ceiling: monodromy marginal SU(2) (49833 cells) and 2-point NULL (iid) done; `inv` closed (cal p=0.265); `pow7` OOS-failed (not promoted); shortscalar harness **confirmed missing** and gate-blocked.
- The genuinely-unrun residue is A/B/cross-j below (per `NEXT_SESSION_PROMPT_2026-08-01_v2.md`, which is sharper than the pasted prompt).
- Reusable infra (do not reimplement): `audit_n1_vsign_v2_core` (shared), `verify_120deg_symbolic_factorization_v1` (PART 1: proves `D(T)|L(T)` and `D(T)|L(ζ₃T)` symbolically over `Q(ζ_M)` ⇒ `g≥2`), `verify_120deg_exact_certificate_v2` (PART 2: exact per-cell residual `V₂−V₁²=−2εp`, branch-aware, handles `p≡1 mod 4`), `run_n1_120deg_v1` (census: `min_l g_l`, the `g≤2` upper bound), `algebraic_galois_degree10_v1.sage` (W-piece + 10T14 census, `analyse(p)` parameterized), `algebraic_branch_confirmation_v1.sage`, `jclass_120deg_discriminator_v1` (`--check` legal; `--arms` gated).

---

## A. 120° census-certificate repair — promote 2464 cells from `[VERIFIED]` to genuinely-exact

**The asymmetry (the bug).** Reduction only raises gcd degree, so `min_l g_l ≥ g_true`. A census reading `min_l g_l = 2` certifies `g ≤ 2`, **not** `g = 2`. Currently `run_n1_120deg_v1.py:127` mislabels this as `g=2`.

**The two halves of the certificate (both must be conjoined):**
- `g ≤ 2`: the existing census `min_l g_l == 2` per cell (`run_n1_120deg_v1.py:99`).
- `g ≥ 2`: PART 1 proves symbolically over `Z[e1,p,ζ₃][T] ⊆ Q(ζ_M)[T]` that `D(T)=T²+e₁T+εp` divides both `L(T)` and `L(ζ₃T)` ⇒ `deg gcd ≥ 2` unconditionally; PART 2 measures the exact integer residual `V₂(a)−V₁(a)² = −2εp` per cell (ε=χ₂(−1), branch-aware).

### A1 (lead, ships the grade promotion now)
Write **`verify_120deg_conjoined_certificate_v1.py`**. Per frozen prime (IN_P/S_P/C_P — same set both scripts already use), per surviving cell `a`:
1. call into `verify_120deg_exact_certificate_v2.check_identity(p,n,h1,h2)` → residual-holds ⇒ `g ≥ 2` at that prime (PART-1 symbolic proof already covers `g≥2` over `Q(ζ_M)`, so the per-cell residual is the empirical confirmation; the symbolic half needs no per-cell recomputation),
2. call into `run_n1_120deg_v1.g_and_flags(...)` → `min_l g_l == 2` ⇒ `g ≤ 2`,
3. conjoin: `residual_holds ∧ min_l g_l==2 ⇒ g == 2`, emit per-cell certificate.
- Output: `RESULT_120deg_conjoined_certificate_v1.json` + `.md`. Relabel the 2464 `g=2` cells `[VERIFIED] → [PROVED-exact (conjoined: D|L ∧ D|L(ζ₃T) ⇒ g≥2; min_l g_l=2 ⇒ g≤2)]`. The `g=0` cells stay `[PROVED-exact]` (already exact: a null cell certifies exactly). Carry the CORRECTION's interim minimum alongside every `g`: the per-cell spread `max_l g_l − min_l g_l`.
- Also fix the mislabel at `run_n1_120deg_v1.py:127` (`alllaw` docstring) and `:8-9` to say `min_l g_l ≥ g_true` (the CORRECTION's wording), so the script no longer carries the one-sided statement.
- **Verify** A1 is sound before trusting: plant the CORRECTION's witness (PLANT-B, true `g₃=0` from α=3+2i, β=2+3i, both norm 13) and confirm the conjoined certificate correctly reads it as **NOT certified `g=2`** (the `g≥2` residual half fails there). This is the self-test that the conjunction isn't vacuous. Order any F-EMPTY-style check first (v2 standing repair).

### A2 (follow-on if time — the CORRECTION's literal route, purer)
Build the `Z[ζ_M]` infrastructure the CORRECTION specifies, as an independent cross-check on the same cells:
- `reduce_cyclotomic(A, M)` reducing mod general `Φ_M` (rewrite of `reduce_phi_prime:198`, which only handles prime `n`), with `ζ_N = y^{M/N}`, `ζ₃ = y^{M/3}` pinned **jointly** (load-bearing when `gcd(N,3)>1`; here `M=lcm(n,3)=3n` since `n≡1 mod 3`).
- Compute `Res_T(L(T), L(ζ₃T))` and first subresultant `S₁` in `Z[ζ_M][T]`. `Res_T=0 ∧ S₁=0 ⇒ g≥2` over `Q(ζ_M)`. Conjoin with `min_l g_l` for `g≤2`.
- **Do NOT** reuse the retracted `Z[x]/(Φ_N(x),Φ_k(x))` ring (the zero ring — `Res(Φ_N,Φ_k)=1` in scope).
- A2 is a purer/direct gcd certificate and a cross-validation of A1; it is not required for the grade promotion (A1 already reaches genuinely-exact).

**Honest scope:** A1 promotes to `[PROVED-exact (conjoined)]` — this *is* genuinely exact (both halves exact; no probabilistic embedding argument in the `g≥2` half once PART-1's symbolic proof is conjoined). Neither A1 nor A2 proves **uniformity** over all `a` / all `p≡7 mod 12` — that's #26, item D, untouched.

---

## B. degree-10 W-piece second-witness cross-check at p=61 (+1 branch)

The 10T14 identification (`RESULT_algebraic_galois_degree10_v1`) is single-prime (p=43) because p=67/127 give degree 26/42 (out of range). Coincidence: at p=61 (+1 branch), `(n−1)/6 = 10` — the +1-branch minpoly feeds a degree-40 squarefree object into the same pipeline.

**Action:** call `algebraic_galois_degree10_v1.sage :: analyse(61, a=1, n_primes=400)`. `analyse(p)` is parameterized; only `__main__:260` hardcodes p=43.

**Read the gates as structural verdicts (not sanity checks), in order:**
1. `assert len(fac)==2` (`:72`): does the +1-branch degree-40 radical split into two conjugate factors over Q(ω)?
2. evenness `f1(-T)==f1` (`:80`): is the Q(ω)-factor even-in-T?
3. `reduce_T2` even-power assert (`:90`): does the T²-reduction yield a degree-10 irreducible?

If all pass → the 10T14 cycle-type census auto-runs (`transitive_match` gated on `deg==10`, `:185`). Read the group verdict.

**Interpretation (genuinely open — no prior prediction in the record):**
- +1-61 **also** 10T14 ⇒ degree-10 W-piece group is branch-independent; p=43 becomes a 2-prime witness (still Chebotarev-density ID, not certified iso). Strengthening.
- +1-61 a **different** transitive group, or a gate **asserts out** ⇒ the W-piece Galois group is itself branch-dependent (the extra d↦−d symmetry in the +1 branch is the mechanism). New finding; p=43 does not generalize.
- Either outcome is publishable; record as `RESULT_algebraic_galois_degree10_p61_v1.md` with the gates' outcomes explicit.

**Scope:** still Chebotarev-density identification at each prime (certified iso blocked on KASH/Magma — out of scope). Does not touch the geometric-monodromy SL₂ conjecture (different object).

---

## C. cross-j Aut-contrast — IN SERIES (relevance decision, then orthogonal measurement)

Not a fork. Compute the relationship first, then let the test run as orthogonal fact-finding regardless.

### C.1 Relevance decision (reason first — "compute the relationship before the test")
Write the reasoning into a short note (`NOTE_cross_j_relevance_v1.md`):
- v2 §B's cross-j contrast tests whether the ζ₃ lock requires `μ₃ ⊂ Aut(E)`. That necessary condition is **already refuted by existing data**: secp256k1 (j≠0, no μ₃ Aut) exhibits the lock at 22 primes / 2464 cells. So an Aut-routed mechanism is dead; the surviving mechanism is geometric monodromy on the a-family, which is **j-independent**, so changing j is an axis cross-j cannot discriminate *as a mechanism test*.
- Conclusion: retire cross-j **as a mechanism discriminator**; keep it **as a cheap orthogonal claim** (j-independence of the 120° lock) in C.2. This satisfies v2 §B's "retire rather than leave dangling" for the mechanism question.

### C.2 Orthogonal j-independence fact-check (cheap, `--check` only — pre-gate legal)
Run `jclass_120deg_discriminator_v1 --check` (NOT `--arms`, which is gate-blocked and refuses without `--i-have-the-gate`). With v2 §B's revival fixes applied as a read-only sanity layer (drop prime-order requirement in any filtering; MEASURE b₁ from #C(F_p) directly at p≡1 mod 4 rather than deriving; order F-EMPTY first if any firing logic is reused): test whether the 120° lock persists on j∈{0,1728,secp} curves. This is the orthogonal claim "the lock is j-independent," independent of the mechanism question C.1 closed.
- If pursued toward `--arms`, STOP and surface the gate decision to you explicitly — do **not** bypass the experiment-designer gate silently (standing order).

**Discipline (v2 standing repairs, apply to any C run):** C-NEG needs `n≥20` independent draws with uniformity-checked percentiles; check readout-parity × index-set-parity before every probe (product odd ⇒ identically zero); measure `pow` cost before sizing (was 14× underestimated); precompute the pool difference table once; never pipe a long run through `tail` (use `-u` + log file); OOS retest before naming anything.

---

## Execution order & todo tracking
1. **A1** (conjunction runner + relabel + PLANT-B self-test) — ships the grade promotion. Lead.
2. **B** (`analyse(61)`, gate-by-gate) — cheap single-prime Sage, independent of A.
3. **C.1** (relevance note) — pure reasoning, fast.
4. **A2** (Z[ζ_M] resultant, if time) — follow-on cross-check of A1.
5. **C.2** (j-independence `--check`) — if time and C.1 cleanly retires the mechanism framing.
Each item produces its own `RESULT_`/`NOTE_` artifact in purist register; lens stays in `RESEARCH.md`. Append a structured `RESEARCH.md` entry per item (hypothesis, what ran, result, grade, what closes it). Recon-before-building confirmed: no done test is reimplemented.

## What this does NOT close
- Uniform #26 (the proof, not a measurement) — the load-bearing open fact; untouched here.
- (D2) citation discharge (Ireland–Rosen Ch.14 / Berndt–Evans–Williams by hand) — separate prerequisite.
- The shortscalar 2^128 arm — gate-blocked + harness missing (confirmed); separate heavy lift needing a gate-stance decision.
- The geometric-monodromy SL₂ conjecture (full group incl. finite center) — different object from B's arithmetic group.

## Files created/modified
- **New:** `verify_120deg_conjoined_certificate_v1.py`, `RESULT_120deg_conjoined_certificate_v1.{md,json}`, `RESULT_algebraic_galois_degree10_p61_v1.md`, `NOTE_cross_j_relevance_v1.md`; (A2) `cyclotomic_ring_utils_v1.py`, `RESULT_120deg_resultant_certificate_v1.{md,json}`; (C.2) `RESULT_cross_j_independence_check_v1.md`.
- **Modified:** `run_n1_120deg_v1.py` (relabel `:8-9`, `:127`), `RESEARCH.md` (append per item).
- No deletion/overwrite of existing results; no git commits/pushes unless asked.