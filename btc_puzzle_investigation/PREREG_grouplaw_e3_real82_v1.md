# PREREG v1 (FROZEN) — group-law E3 on the real 82

**Date drafted 2026-08-18; FROZEN 2026-08-19 after `experiment-designer` sign-off (verdict PROCEED, all
five arms SOUND; two non-material disclosures folded in below — §0 note + §A5 note).** The named next
probe from `RESULT_e3_owed_measurement_v1.md` (Brick A) and
`RESULT_diffset_cubic_cmvanishing_v1.md` §Next-2 / `CORRECTION_e3_cmvanishing_interaction_reading_v1` §5.3:
the **group-law** difference-set cubic energy `E3_gl = |Σ χ₃(x(Pᵢ−Pⱼ))|²`-type on the real 82 pubkey
POINTS — the CM endomorphism's native operation (uses the y-coordinates via curve addition, unlike the
field-difference E3 which used x only). Reuses the validated harness `c2_grouplaw_diffset_curve_v1.py`
(`Curve.add`/`gl_diff_code`/`stats3`; frozen `PREREG_c2_grouplaw_diffset_v2.md` was band-random ARMS, a
different object). Integer-exact signal + decision path. No security/keyspace/extractability claim.

---

## 0. Object (fixed) + the prediction under test
`P_i=(X_i,Y_i)=[d_i]G` are the 82 solved pubkey POINTS (`solved_puzzles_xy.csv`, X and Y hex). For each
unordered pair `i<j`: point difference `P_i − P_j = P_i + (−P_j)` (curve addition; `−P_j=(X_j,−Y_j)`),
take its x-coord `x(P_i−P_j)` (symmetric: `x(P_j−P_i)=x(−(P_i−P_j))=x(P_i−P_j)`), cube class
`χ₃∈{0,1,2}` and QR bit → 6-cell `H[3q+c]`. Family via the SAME `stats3` (E2,E3,E6). `E3_gl = a²+b²+c²
−ab−bc−ca` on cube marginals `(a,b,c)`; `E3 = T²−3(ab+bc+ca) ≡ T² mod 3`, so `E3≡0 mod3` is forced iff
`T≡0 mod3` (bug-check; `T=#{non-∞ pairs}`, `=3321` for the real 82). **§0 note (gate disclosure):**
`P_i−P_j=O` iff `d_i≡d_j mod n` (the "−" case `d_i≡−d_j` gives the finite point `[d_i−d_j]G`, not ∞);
the 82 `d`'s are distinct mod `n`, so no ∞ arises and `T=3321` exactly. **Harness disclosure:** `code(x)`
would `KeyError` at `x=0`, but this is unreachable on secp — `7` is a QR-**non**residue mod `P`, so no
`E(F_P)` point has `x=0`, hence no group-law difference x-coord is `0`. This is curve-specific (guard
before reusing the harness on `p256`/`E′`, where `b` may be a QR).

**Prediction (to be tested, not assumed):** `_cmvanishing` §Next-2 predicts group-law E3 "fires harder"
than the field-difference E3 (which rejected at p=0.035, bounded family-wise) because the group law is
where the CM endomorphism acts. **Falsification:** if `E3_gl` does NOT reject vs the structural null, that
BOUNDS the CM-native difference channel too (a brick either way). No outcome is forecast in a decision cell.

## 0.5 Mission/brick compliance
Counter-prior: this SURFACES the named next probe and TESTS it — the field-difference reject is real and
set-specific; the group-law object is the higher-resolution same-set statistic Brick A's power ceiling
pointed to. Burden-on-closure: any non-reject branch (§4) emits object+observable+power+scope + a named
next probe, never a "door shut." Brick: standalone (script+frozen null+summary), reusable (the gl-diff
structural-null percentile + FWER + q_MT), direction-true (null/control/OOS/forced-structure-control/grade).

## 1. Structural null (generator-free; shares forced symmetries)
`N_null=10000` sets of 82 uniform random valid secp `E(F_P)` POINTS (`Curve.rand_point`: uniform x with
`x³+7` a QR, random y-sign), frozen seed **`20260818`**. Group-law diff E3 on each. **Shares:** the curve
group law, the j=0/μ₆ cubic bias, `C(82,2)` pairs, forced `E3≡0 mod3` (T≡0), the gl-diff readout's forced
symmetries. **Differs only in** the real `d`-multiset (the tested contrast). `N=10000` (not 20000): the EC
group law is ~3× the per-pair cost of the field difference; 10⁴ resolves the ~98th-pctile tail and FWER to
~1e-4. Extension to 2×10⁴ is owed only if the decision lands within noise of the boundary.

## 2. Arms (pre-committed; decisions fixed before data)

### A1 — reproduction + structural null. PRIMARY.
Compute `E3_gl(real)`; assert `T=3321`, `E3≡0 mod3` (else path bug, abort). Integer order-statistic
boundary `U_struct = null_E3_sorted[(975·N_null)//1000]`, `L_struct = [(25·N_null)//1000]`. **Decision:
REJECT-HIGH iff `E3_gl(real) > U_struct`.** Symmetric two-sided rank p (integer numerator over common
denom, `+1` both tails, inclusive ties) for display.
- **Pre-committed:** `> U_struct` ⇒ the real set's group-law cubic-difference structure deviates from
  pseudorandom curve points; carry to A2. `≤ U_struct` ⇒ **the CM-native channel does not reject** — bound
  E3_gl's magnitude (power A4, scope = gl-diff marginal cubic energy) + next probe (triples / band-localized
  group-law); compare directly to the field-difference reject (does the group law add or not?).

### A2 — family-wise MC-correction over {E2,E3,E6}.
Westfall–Young max-statistic (min-p) on the SAME structural null; integer p-numerators; symmetric `+1`;
`≥`/`≤` inclusive ties applied identically to real and each null draw (plug-in self-inclusion disclosed,
O(1/N)). `p_FWER(E3) = (#{i: minp_i ≤ p_E3_obs}+1)/(N+1)`; decision integer `(cnt+1)·20 ≤ (N+1)`. Report
Bonferroni ×7 (session family) as a disclosed bound.
- **Pre-committed:** `p_FWER ≤ 0.05` ⇒ survives look-elsewhere ⇒ characterize + compare to field-diff.
  `> 0.05` ⇒ family-wise non-significant bounded magnitude with power+scope (NOT a cubic closure; E3 is one
  marginal rank-1 projection) + next probe.

### A3 — OOS on band-matched known-MT points. `q_MT`, fully partitioned.
`M_oos=1000` band-matched 82-sets from `constructed_keys_1to160_100k.csv` (one constructed POINT (X,Y) per
real bit-length; take X,Y directly, no EC mul), frozen seed **`20260818`**. `q_MT = #{MT-set E3_gl ≥
E3_gl(real)}/M_oos`; secondary = median MT percentile vs structural null.
- **Pre-committed:** `q_MT ≤ 0.05` ⇒ set-specific (real high even among band-matched MT sets);
  `0.05 < q_MT ≤ 0.50` ⇒ partial (report the `(1−q_MT)` quantile bound + next probe);
  `q_MT > 0.50` ⇒ pipeline/bit-band (real typical of/below band-matched MT sets) + next probe.

### A4 — firing control (instrument power). MUST FIRE.
`E3_gl = f(cube marginals)`, so a β²-count-excess plant is exactly matched (same as Brick A A4, gate-ruled
SOUND). On a structural-null 82-set's gl-diff counts `(a,b,c)`: plant `(a−⌊Δ/2⌋, b−⌈Δ/2⌉, c+Δ)` (sum
fixed); sweep `Δ∈{0,25,50,75,100,150}`; power = P(reject-high vs `U_struct`) over 500 planted draws, seed
**`12345`**. **Gate:** monotone in Δ; Δ=0 FPR ≈ 0.025 (one-sided upper); power ≥0.9 by Δ=150. Else STOP.

### A5 — C-GLV forced-structure control. MANDATORY (object-identity; the μ₃-closed trap).
On a **φ-closed (GLV-closed) point set** `S∪[λ]S∪[λ²]S`, the gl-diff set is φ-closed and its cube-class
counts are ω-cyclic ⇒ **E3=E6=0 EXACT** (χ₃(β)=ω≠1), E2≠0 not forced (verified in stageA C-GLV, E2=1521).
**Assert:** (i) a constructed φ-closed 82-point set gives `E3_gl=E6_gl=0` exact and `E2_gl≠0` — proving the
statistic *can* be zeroed by cubic symmetry (so a nonzero E3_gl reads genuine cubic imbalance, not an
artifact); (ii) the real 82 and a structural-null draw give `E3_gl>0` (NOT forced). This is the analog of
the `E3/E6 forced-zero on μ₃-closed sets` pre-screen — it certifies the real set is NOT reading a forced
value. If (i) fails, the harness is wrong; if the real set were φ-closed, E3_gl would be uninformative
(it is not — the 82 `d`'s are arbitrary).

## 3. Power ceiling & scope (before data)
- N=82 fixed (cannot grow). Raw p cannot strengthen on this statistic.
- **What the group law adds:** `E3_gl` depends on the y-coordinates through curve addition (the CM-native
  operation), so it can carry joint (x,y) structure the x-only field-difference E3 cannot — that is the
  reason to run it. But it remains a **marginal rank-1 all-ones cubic projection** of the gl-diff set,
  blind to orientation-odd / joint-triple / band-localized subspaces of the group-law object.
- **Grades:** A1/A2 `[EMPIRICAL @ secp]` percentile + p_FWER with power+scope, or `[DISSOLVED-ON-TEST]`
  with power+scope. A3 `q_MT` bound. Explicit comparison to the field-difference E3 result (added value of
  the group law, quantified). No security implication; no grade elsewhere moves.

## 4. Falsification summary (every branch a brick)
1. A1 `≤U_struct` → CM-native gl-diff cubic channel does NOT reject → bound + next probe; the field-diff
   reject is then the stronger of the two (group law did not add on this projection).
2. A2 `p_FWER>0.05` → family-wise non-sig bounded magnitude + next probe.
3. A3 `q_MT>0.50` → pipeline/bit-band bound + next probe.
4. A1 REJECT + A2 sig + A3 `≤0.05` → set-specific CM-native cubic structure, family-wise significant,
   FIRES HARDER than field-diff (the prediction) → characterize (which pairs/bands) + curve-class (E′).
5. A4 under-powered → STOP (instrument brick owed). A5 (i) fails → harness bug, fix before any read.

## 5. Mortar checklist
- [ ] exact integer signal + decision path; `check_no_float.py` (decisions integer; floats display-only)
- [ ] generator-free structural null sharing the gl-diff forced symmetries
- [ ] A4 firing control monotone; Δ=0 FPR ≈ nominal
- [ ] A5 C-GLV: φ-closed ⇒ E3=E6=0 exact; real & null NOT forced
- [ ] A3 OOS (band-matched MT points) before naming any zero
- [ ] forced quantities (`T`, `E3≡0 mod3`) are bug-checks, not evidence
- [ ] every output graded with power+scope; explicit field-diff-vs-group-law comparison

## 6. Artifacts (to be produced)
`grouplaw_e3_real82_v1.py` (A1–A5, reuses `c2_grouplaw_diffset_curve_v1.py` Curve/stats3); frozen null
`gl_e3_struct_null_{E2,E3,E6}_v1.npy`; `grouplaw_e3_real82_v1.log`; `_summary.json`.

*Predecessors: `RESULT_e3_owed_measurement_v1` (Brick A), `RESULT_c2_grouplaw_diffset_stageA_v1`
(band-arms bound + C-GLV), `RESULT_diffset_cubic_cmvanishing_v1` (§Next-2 prediction),
`CORRECTION_e3_cmvanishing_interaction_reading_v1` (§5.3). Frontier #29.*
