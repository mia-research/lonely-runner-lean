# PRE-REGISTRATION (DRAFT) — R3: lag-d autocorrelation of the orbit's χ₃-sequence

**Status: `[DRAFT — UNFROZEN — awaiting experiment-designer frame-gate]`.** Grade slot `[PENDING GATE]`.
Executes R3 of `PLAN_interval_charsum_realbranch_characterization_v1.md`. The histogram-level test
(`RESULT_interval_vs_random_characterize_v1.md`) showed the orbit's χ-**histogram** ≈ random; R3 tests
the finer, histogram-invisible property: **sequential (lag-d) correlation** along the orbit. A natural
on-ramp to C2 (the statistic is a group-law-difference quantity: χ₃(x(P)) vs χ₃(x(P+[d]G))).

## §0. Scope / counter-prior
Constructed scalars, secp's own p/G, no keys/pool. A(d)≈null is a **bound** (finer-structure absent to
this power), never a closure. A hit is **characterized**, never verdicted (anomaly-drill protocol).

## §1. Object and disjointness (FRAME)
`c(s) = χ₃(x([s]G))` over a consecutive orbit `s ∈ [s₀, s₀+L)`. For lag `d`, the lag-difference is
`Δ_d(s) = c(s) − c(s+d) mod 3` (i.e. `χ₃(x(P_s))·χ₃(x(P_s+[d]G))⁻¹`, P_s=[s]G). **Statistic**
`A(d) = |Σ_s ω^{Δ_d(s)}|²` = the E₃-form of the Δ_d histogram (exact integer, Appendix A).
- **Disjointness:** the feature is a lag-d correlation of a nonlinear character readout; the "structure"
  is whether the orbit sequence self-correlates. No shared component fires it by construction.
- **Forced value — the failure mode to check (this is where multiplicity bit before):** `A(0)=L²`
  trivially (Δ=0), so **d=0 excluded**. For `d≠0`, the complete-orbit sum
  `Σ_{all P} χ₃(x(P))χ₃(x(P+[d]G))⁻¹` is a Weil correlation `O(√p)` ⇒ generic incomplete `A(d) ~ L`, NOT
  forced large — **but the gate must confirm no lag `d` in the frozen set has a degenerate/forced A(d)**
  (e.g. a small-order [d]G; secp is prime-order so none but O, but verify). A forced-value CONTROL is in §3.

## §2. Statistic and decision
- Lags frozen: `d ∈ {1,2,3,4,5,6,7,8,12,16,24,32,64,128,256}` (15 lags; small + a few large).
- For each d: rank the orbit's `A(d)` against the **shuffle null** (§3) → exact rank p-value.
- **SCREEN (two-sided):** p ≤ 0.005 or ≥ 0.995 (a real lag structure could raise A(d) — clustering — or
  lower it — anti-correlation).
- **GATE = OOS:** a screened lag is a candidate only if it screens the **same tail on ≥5 fresh orbit
  locations `s₀`**. Per-lag p reported **uncorrected**; look-elsewhere across 15 lags handled by the
  same-tail-5/5-OOS requirement (a chance screen won't replicate), not by an FWER penalty.
  - **(gate note 1+2, frozen):** the 5 OOS `s₀` are **seed-derived at freeze, independent of which lags
    screen**, and give **pairwise non-overlapping windows**; each of the 5 must **independently** meet
    the `p≤0.005`/`≥0.995` threshold on the **SAME tail** (not merely same side of median). Per-lag
    same-tail 5/5 false-positive `≈0.005⁵≈3×10⁻¹²`; union over 15 lags `≈5×10⁻¹¹`.

## §3. Matched control (FRAME; Rule 3)
- **Primary null = code-shuffle:** randomly permute the orbit's code sequence `c(·)` (preserves the
  exact code marginal, destroys all sequential order) and recompute `A(d)`. `R_sh ≥ 2000` shuffles →
  the reference distribution of A(d) under "same marginal, no lag structure." This is like-to-like on
  the marginal and isolates *sequential* structure only.
- **Forced-value control (answers §1):** compute A(d) on a near-complete / very long orbit (or average
  over many s₀) for each frozen d; confirm A(d)~L (not forced large). **(gate note 3, frozen) Drop
  threshold:** drop lag d iff its forced-value A(d) exceeds the shuffle-99th on the near-complete orbit,
  and record why (dropping can only remove a lag, never manufacture a hit).
- **C-PLANT (power):** inject a lag-`d*` correlation (e.g. copy c(s)→c(s+d*) for a fraction f of s) and
  confirm A(d*) fires above the shuffle 99th; void at f=0.
- **FORBIDDEN:** ranking A(d) against an iid-code null with the pool-imbalance defect (use the shuffle
  of the ACTUAL orbit codes — same marginal — not a bootstrap).

## §4. Plant-fires (MECHANICAL) — constructibility + power curve at f∈{0,½f*,f*,2f*}.

## §5. Power / bound (Rule 5)
Generic `A(d) ~ L` (mixing). Detectable lag-correlation magnitude from the shuffle 99th: report per-lag
`the smallest injected f that fires` (C-PLANT), and state the bound as "lag-d correlation < that,
excluded; blind below." `L` and R_sh frozen; larger L lowers the floor (O(L)).

## §6. Scope (FRAME; Rule 4)
secp p/G, this orbit family, these 15 lags. A hit is a **secp short-range χ correlation** — a localized
fact, not "generic"; genericity would require the control-curve test (R2), out of scope here.

## §7. Falsification (FRAME)
- **A(d)~shuffle for all frozen d** (no 5/5-OOS screen) → **mixing confirmed at these lags/power** — a
  bound: the orbit has no lag-d χ₃ correlation ≥ the §5 floor. Strengthens the earned artifact verdict.
- **A(d) screens 5/5-OOS at some d** → **real short-range χ structure the histogram missed** →
  characterize (which d, magnitude, scaling); it is a group-law-difference correlation ⇒ it directly
  seeds C2. Do NOT dismiss; do NOT name a mechanism unverified.
- **Kill:** C-PLANT fails to fire; a "hit" reproduced by the forbidden iid-code null; fails OOS.

## §8. Exactness — pure int; A(d) integer quadratic form; shuffle ranks integer counts.

## §9. Pre-commitment / freeze
Frozen: the 15 lags; L (this run 10⁵); R_sh (≥2000 shuffles); the two-sided-99th + same-tail-5/5-OOS
rule; shuffle null (primary) + forced-value control + C-PLANT; seeds. SHA-256 on freeze.

## Appendix A — exact statistic
Per lag d: histogram `m_δ = #{s : Δ_d(s)=δ}`, δ∈{0,1,2}. `A(d) = m₀²+m₁²+m₂² − m₀m₁−m₁m₂−m₂m₀`
(`=|Σ ω^{Δ}|²`, integer). Shuffle null: permute c(·), recompute. Ranks are integer counts.
