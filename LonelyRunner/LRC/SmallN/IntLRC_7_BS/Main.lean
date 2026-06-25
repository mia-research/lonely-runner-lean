import LonelyRunner.LRC.Defs
import LonelyRunner.LRC.SmallN.IntLRC_7_BS.Defs

/-!
# n = 7 (Barajas–Serra) — assembly + discrete→real bridge

Source: `sources_barajas_serra_2008.txt`.

This file is the **interface** between the real-valued `intLRC 7` goal and the
purely number-theoretic content of Barajas–Serra 2008.

## Strategy

Barajas–Serra prove the conjecture for `|D| = 6` *unconditionally* (six positive
integers with `gcd = 1`); the hard-case hypotheses `6·v₁ < V ≤ 6·v₅` carried by
`IntLRC_7.lean` are an artefact of the other manuscript's case split and are not
needed here. The proof produces a **rational** witness `t = λ/N` with
`N = 7^(m+1)` and a multiplier `λ` such that `|λ·d|_N ≥ N/7`, i.e.
`circDist(λ·d/N) ≥ 1/7`, for every `d ∈ D`.

- `bs_discrete_to_real` — the bridge: an integer modulus `N > 0` and multiplier
  `λ` with `circDist(λ·dᵢ/N) ≥ 1/7` yields the real witness `t = λ/N`. Trivial;
  removes all real analysis from the remaining work.
- `bs_discrete` — the discrete Barajas–Serra core (the whole paper). **The single
  remaining `sorry`.** Future work fills this from
  `PrimeFiltering` + `Reduction` + `Case_A4` + `Case_A5`.
- `barajas_serra_seven` — the entry point used by `IntLRC_7.lean`.
-/

open Set

namespace IntLRC7BS

/-- **Bridge (discrete → real).** Given a positive integer modulus `N` and an
integer multiplier `lam` such that every `lam · D i` lands at circle distance at
least `1/7` of `N` (`circDist (lam·D i / N) ≥ 1/7`), the rational time
`t = lam / N` witnesses loneliness for all runners. Pure algebra:
`(D i) · (lam/N) = (lam · D i)/N`. -/
theorem bs_discrete_to_real
    {k : ℕ} (D : Fin k → ℕ)
    (h : ∃ (N : ℕ) (lam : ℤ), 0 < N ∧
          ∀ i, (1 : ℝ) / 7 ≤ circDist ((lam * D i : ℝ) / N)) :
    ∃ t : ℝ, ∀ i, circDist ((D i : ℝ) * t) ≥ (1 : ℝ) / 7 := by
  obtain ⟨N, lam, _hN, hd⟩ := h
  refine ⟨(lam : ℝ) / N, fun i => ?_⟩
  have hrw : (D i : ℝ) * ((lam : ℝ) / N) = ((lam * D i : ℝ) / N) := by ring
  rw [hrw]
  exact hd i

/-- **Discrete Barajas–Serra core, residue-band form (n = 7).** For six positive,
distinct integers with `gcd = 1`, there is a level `m` and a multiplier `lam`
sending every residue `(lam · d)_N` into the central band `[7^m, 6·7^m]` (with
`N = 7^(m+1)`) — equivalently `|lam·d|_N ≥ N/7`.

This is the *purely arithmetic* heart of Barajas–Serra 2008 §2–§6: Prime
Filtering (Lemma 2) + Corollary 3 + the §4 reduction to `|A| ∈ {4,5}`,
`(A)₇ ⊂ {1,2,4}`, then the finite mod-7 analysis of §5 (`|A|=4`) and §6 (`|A|=5`).

The band is **inclusive** at both ends: filtered elements (`d ∈ D\D₇(m)`) land in
the open arcs `q ∈ {1,…,5}` ⊂ `[7^m, 6·7^m)`, while `D₇(m)` elements are only
guaranteed `|d|_N ≥ N/7`, which may sit on the boundary `6·7^m`. See the analysis
in `ROADMAP.md` (this is why the target is the residue band, not `q ∉ {0,6}`).

**This is the single remaining `sorry` for n = 7.** Everything above it
(`bs_discrete`, the bridge, `IntLRC_7`) is closed. In the paper `m = max ν₇(D)`. -/
theorem bs_discrete_q
    (D : Fin 6 → ℕ) (hpos : ∀ i, 0 < D i)
    (hinj : Function.Injective D) (hgcd : Finset.univ.gcd D = 1) :
    ∃ (m : ℕ) (lam : ℤ), ∀ i,
      (7 ^ m : ℤ) ≤ (lam * (D i : ℤ)) % (7 ^ (m + 1) : ℤ) ∧
      (lam * (D i : ℤ)) % (7 ^ (m + 1) : ℤ) ≤ 6 * 7 ^ m := by
  sorry

/-- **Discrete Barajas–Serra core (n = 7).** For six positive, distinct integers
with `gcd = 1`, there exist a positive integer modulus `N` (a power of `7`) and a
multiplier `lam` placing every `lam · D i` at circle distance ≥ 1/7. Derived from
the residue-band form `bs_discrete_q` via `circDist_ge_of_residue`. -/
theorem bs_discrete
    (D : Fin 6 → ℕ) (hpos : ∀ i, 0 < D i)
    (hinj : Function.Injective D) (hgcd : Finset.univ.gcd D = 1) :
    ∃ (N : ℕ) (lam : ℤ), 0 < N ∧
      ∀ i, (1 : ℝ) / 7 ≤ circDist ((lam * D i : ℝ) / N) := by
  obtain ⟨m, lam, hq⟩ := bs_discrete_q D hpos hinj hgcd
  refine ⟨7 ^ (m + 1), lam, by positivity, fun i => ?_⟩
  obtain ⟨hlo, hhi⟩ := hq i
  have hmain := circDist_ge_of_residue m (lam * (D i : ℤ)) hlo hhi
  have hcast : ((lam * (D i : ℤ) : ℤ) : ℝ) = (lam * D i : ℝ) := by push_cast; ring
  rw [hcast] at hmain
  exact hmain

/-- **Entry point.** Barajas–Serra 2008 for seven runners: the real-valued
`intLRC 7` conclusion for six positive integer speeds with `gcd = 1`. Used to
discharge the Hard-Case `sorry` in `IntLRC_7.lean`. -/
theorem barajas_serra_seven
    (speeds : Fin 6 → ℕ) (hmono : StrictMono speeds)
    (hpos : ∀ i, 0 < speeds i) (hgcd : Finset.univ.gcd speeds = 1) :
    ∃ t : ℝ, ∀ i, circDist ((speeds i : ℝ) * t) ≥ (1 : ℝ) / 7 :=
  bs_discrete_to_real speeds (bs_discrete speeds hpos hmono.injective hgcd)

end IntLRC7BS
