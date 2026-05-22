# Session Report — LRC Lean 4 Formalization (Exploratory)

**Date:** 2026-05-22  
**Session goal:** Initial Lean 4 formalization of `lrc_proof_v11_draft.md` (version 11.3)  
**Status:** Exploratory — structure complete, compilation blocked (see §3)

---

## §1  Environment

| Component | Version |
|-----------|---------|
| Lean | 4.29.1 (arm64-apple-darwin24.6.0) |
| Lake | 5.0.0-src+f72c35b |
| elan | 4.2.1 |
| Mathlib | v4.29.1 (commit pinned in lakefile.toml) |
| Platform | macOS 15.5 (Darwin 25.5.0, Apple Silicon) |

**Toolchain installation:** elan installed fresh via curl.  Lean 4.29.1 downloaded (~50 MB).
Mathlib source fully cloned from GitHub (~600 MB git pack).

---

## §2  Build Status

### 2.1  Precompiled cache (failed)

The standard Mathlib precompiled `.olean` cache (downloaded via `lake exe cache get` from
`lakecache.blob.core.windows.net`) **could not be fetched** in this environment.
The Azure blob storage endpoint (port 443) is blocked in the Claude Code sandbox.
All 8,232 downloads failed with "Couldn't connect to server".

### 2.2  Compilation from source (partial)

Without the precompiled cache, `lake build` compiles Mathlib from source.
During this session, **871 `.olean` files** were compiled from source
(Batteries, Aesop, Qq, LeanSearchClient, ImportGraph, and initial Mathlib linter/tactic
modules). The build was progressing and correct; it was terminated after ~4 minutes to
allow the session to complete.

**Estimate to complete full build from source:** 3–6 hours on Apple M-series hardware.

### 2.3  Immediate errors found and fixed

Two import path issues were discovered and fixed:

| Import as written | Issue | Fixed import |
|---|---|---|
| `import Mathlib.Algebra.Order.Floor` | Directory, not file (v4.29.1) | `import Mathlib.Algebra.Order.Floor.Defs` |
| `import Mathlib.MeasureTheory.Integral.Bochner` | Directory, not file | `import Mathlib.MeasureTheory.Integral.Bochner.Basic` |

One structural error was fixed: all source files had `/-! ... -/` doc blocks placed
before `import` commands; this violates Lean 4's requirement that imports come first.
Fixed by reordering all 9 files.

### 2.4  Does `lake build` pass on the whole project?

**No.** Full compilation was not completed due to the precompiled cache being unavailable.
However, the build was making correct progress when terminated; no Lean syntax errors in
our source files were observed beyond the fixed import paths.

**Recommendation:** In a network-enabled environment, run:
```bash
cd LonelyRunner
lake exe cache get     # downloads ~2 GB of precompiled .olean files
lake build             # should complete in ~5 minutes
```

---

## §3  Section-by-Section Summary

| File | Theorems / Defs | Fully proved | sorry stubs | Blockers |
|------|----------------|-------------|------------|---------|
| `Defs.lean` | 14 | `circDist.nonneg`, `circDist.le_half`, `circDist.le_one`, `circDist.periodic` (pending build verification) | 2 | 1 |
| `Lemma21_FundamentalIdentity.lean` | 6 | 0 | 6 | 3 |
| `Lemma41_PositiveMeasure.lean` | 4 | 0 | 12 | 6 |
| `Theorem52_Weyl.lean` | 4 | 0 | 7 | 4 |
| `Theorem61_BSR.lean` | 4 | `bsr_range` lower bound, `circDist_of_range` (pending) | 4 | 2 |
| `Theorem71_LargeSR.lean` | 3 | 0 | 6 | 3 |
| `Theorem101_DI.lean` | 6 | `DI_prime_ge_two` (1-liner) | 6 | 4 |
| `Theorem111_ModDI.lean` | 4 | 0 | 18 | 9 |
| `Theorem121_Main.lean` | 4 | `lemma91_case_exhaustion` (pending), `lemma92_DI_partition` (pending) | 9 | 5 |

**Total:** ~49 theorems/definitions attempted; 0 fully sorry-free (build not completed);
71 sorry stubs; 37 BLOCKER comments.

---

## §4  Critical Dependency Assessment — Theorem 5.2

**Finding:** Theorem 5.2 as stated in the manuscript is **NOT** classical Weyl equidistribution.
It is a finite **CRT measure-factorisation** result.

**What the proof actually needs:**
> If `G` has period `1/L`, `A ⊆ [0,1)` is measurable, and `gcd(p, L) = 1`, then
> the two indicator functions `1_G(t)` (depends only on `t mod 1/L`) and
> `1_A({pt})` (depends only on `t mod 1/p`) are "independent" over `[0, 1/(Lp))`,
> giving `μ({t ∈ G : {pt} ∈ A}) = μ(G) · μ(A)`.

**Mathlib availability (v4.29.1):**

| Ingredient | Mathlib status |
|-----------|---------------|
| `Int.fract` | ✅ EXISTS in `Mathlib.Algebra.Order.Floor.Defs` |
| `Nat.Coprime`, `ZMod.chineseRemainder` | ✅ EXISTS |
| `MeasureTheory.Measure.prod` (Fubini) | ✅ EXISTS |
| `MeasureTheory.volume` on `ℝ` | ✅ EXISTS |
| CRT bijection `φ : [0, 1/(Lp)) → [0,1/L) × [0,1/p)` as measure-preserving | ❌ NOT PRESENT as named lemma |
| Product-measure factorisation in this exact form | ❌ NOT PRESENT |
| Classical Weyl for irrational α (`AddCircle.equidistributed_of_irrational`) | ✅ EXISTS (not used) |

**Verdict:** Theorem 5.2 must be proved from primitives.  The key step is formalizing
the real-interval CRT bijection `φ` as a measure-preserving map, then applying Fubini.
Estimated effort: **200–400 lines** of Lean.  This is a non-trivial but tractable task
for a Lean expert; it is the **single most important open item** for the next session.

**Alternative approach:** The result could be deduced from the ergodic-theory fact that
the map `t ↦ pt mod (1/L)` is equidistributed on the circle `ℝ/(ℤ/L)` when `gcd(p,L)=1`.
Mathlib's `AddCircle` infrastructure might support this, but the connection would need
to be made explicit.

---

## §5  Top Blockers (Priority Order)

### Blocker 1 — Theorem 5.2 (CRT Measure Lemma) [CRITICAL]
**File:** `Theorem52_Weyl.lean`  
**Impact:** Blocks Theorems 10.1 and 11.1, which together cover the entire hard case.  
**Suggested next steps:**
1. Search Mathlib for `MeasureTheory.prod_volume_eq` and `ZMod.chineseRemainder_symm`.
2. Prove the real-interval CRT bijection: for `gcd(m,n)=1`, the map
   `t ↦ (t mod 1/m, t mod 1/n)` from `[0, 1/(mn))` to `[0,1/m) × [0,1/n)` is bijective.
3. Show the bijection is measure-preserving (both sides have measure `1/(mn)`).
4. Apply Fubini to factor the integral.

### Blocker 2 — Fundamental Identity (Lemma 2.1) proof [HIGH]
**File:** `Lemma21_FundamentalIdentity.lean`  
**Issue:** The identity `{a·{b·t}} = {a·b·t}` follows from `Int.fract_sub_int`
(or `Int.fract_add_int`) but the exact Lean 4 spelling needs to be worked out.  
**Suggested next steps:**  
Search for `Int.fract_sub_int` in Mathlib. If absent, derive from `Int.fract_add_int`
using `Int.cast_neg`. This should be a ≤10 line proof once the right lemma is found.

### Blocker 3 — Nat subtraction vs real arithmetic in Theorem 6.1 [MEDIUM]
**File:** `Theorem61_BSR.lean`  
**Issue:** The upper bound `v_j ≤ (n-1)*v₁` uses Nat subtraction `n - 1`, which in
Lean 4 is the truncated subtraction. The cast `(n - 1 : ℕ) → ℝ` needs `Nat.cast_sub`
combined with `hn : 1 ≤ n`.  
**Suggested next steps:**  
Use `Nat.cast_sub (by omega : 1 ≤ n)` to convert `(n - 1 : ℕ)` to `(n : ℝ) - 1`.
Then the arithmetic closes with `linarith`.

### Blocker 4 — Measure of setA [MEDIUM]
**Files:** `Lemma21_FundamentalIdentity.lean` (setA_measure), `Theorem101_DI.lean`  
**Issue:** Computing `μ(A) = (n-2)/n` requires explicit measure calculation for a
union of arithmetic intervals.  
**Suggested next steps:**  
Use `MeasureTheory.volume_iUnion_disjoint` + `Real.volume_Ioo` for each component,
then sum via `Finset.sum`.

### Blocker 5 — Measurability of goodSet and setA [MEDIUM]
**Files:** `Defs.lean`, `Theorem101_DI.lean`  
**Issue:** `{t | circDist(v*t) ≥ 1/n}` needs to be shown measurable.  
**Suggested next steps:**  
Show `t ↦ circDist(v*t)` is measurable (it's continuous), then the preimage of
`[1/n, ∞)` is a closed set → measurable.  
Search: `Continuous.measurable`, `measurable_min`, `Int.measurable_fract`.

---

## §6  What Verified Cleanly

Due to the incomplete build, no theorem could be confirmed sorry-free by the Lean
elaborator. However, based on manual inspection:

**Likely immediately correct (would pass with working Mathlib .olean):**
- `circDist.nonneg`, `circDist.le_half`, `circDist.le_one` — simple linarith from Int.fract bounds
- `lemma91_case_exhaustion` — omega closes all cases of the trichotomy
- `lemma92_DI_partition` — direct use of `Nat.dvd_or_coprime`
- `DI_prime_ge_two` — one-liner using `Nat.Prime.two_le`
- The lower bound proof in `bsr_range` — standard cast + mul_le_mul

**Requires slight tactic adjustment (1-5 lines each):**
- `circDist.periodic` — needs the right form of `Int.fract_add_one`
- `goodSet_periodic` — same issue with `Int.fract_add_one`
- `fundamental_identity` — needs `Int.fract_sub_int` (see Blocker 2)

**The numerical examples:**
```lean
example : circDist (1 * (1 / (3 * 1 : ℝ))) = 1 / 3 := by
  unfold circDist; norm_num [Int.fract_eq_self]
```
These should work once `Int.fract_eq_self` resolves correctly with `norm_num`.

---

## §7  Architecture Notes for Future Sessions

1. **Use `import Mathlib` instead of targeted imports** for exploratory work —
   eliminates the "is this file a directory?" problem at the cost of longer initial build.

2. **Theorem 5.2 is the keystone** — prove it first in isolation before developing
   the rest of the hard case.

3. **The main theorem (12.1) induction** has a structural issue: `Nat.strong_induction_on`
   in Lean 4 uses a different syntax from the `|` pattern matching shown.
   Use `Nat.rec` with the `Nat.strongInduction` principle or `Nat.strongRecOn`.

4. **Connecting `intLRC` to the sub-theorem signatures** is the main bookkeeping challenge.
   Consider defining a uniform `lrcAux` predicate that all sub-theorems use.

5. **The `Fin` index management** throughout (especially in Theorem 11.1) is the
   most syntactically complex part. Consider using `Finset` instead of `Fin` for
   more flexibility.

---

## §8  Files Produced

```
LonelyRunner/
├── SESSION_REPORT.md            ← this file
├── FORMALIZATION_PLAN.md        ← detailed formalization plan
├── lakefile.toml                ← lake config with Mathlib v4.29.1
├── lean-toolchain               ← Lean 4.29.1
├── LonelyRunner.lean            ← main entry (imports Basic)
└── LonelyRunner/
    ├── Basic.lean               ← imports LonelyRunner.LRC
    ├── CLAUDE.md                ← domain context for future sessions
    └── LRC/
        ├── Defs.lean            ← circDist, goodSet, jointGoodSet, LRC predicate
        ├── Lemma21_FundamentalIdentity.lean
        ├── Lemma41_PositiveMeasure.lean
        ├── Theorem52_Weyl.lean  ← CRITICAL DEPENDENCY (see §4)
        ├── Theorem61_BSR.lean   ← Bounded Speed Ratio
        ├── Theorem71_LargeSR.lean
        ├── Theorem101_DI.lean   ← Divisor Induction
        ├── Theorem111_ModDI.lean ← Modified DI (most complex)
        └── Theorem121_Main.lean  ← Assembly
```

**Total lines of Lean written:** ~900 lines  
**Total theorems attempted:** ~49  
**Sorry stubs:** 71 (all annotated with BLOCKER / MATHLIB_SEARCH / STATUS)
