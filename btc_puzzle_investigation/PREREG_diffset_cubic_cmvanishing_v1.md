# PREREG — CM-vanishing test for the E3 anomaly (v1)

**Status:** FROZEN before apply. Gate: `experiment-designer` (isolated). Date: 2026-07-28.
Motivated by the freed-lens CM×band prediction on `RESULT_diffset_cubic_v1.md` (E3=13125,
p≈0.033 on secp's real 82). **All of this document is fixed before any E′ data is touched.**

---

## Objective (binary falsifier of the freed-lens CM-driven prediction)

The freed thermodynamic lens predicts the E3 anomaly is **CM-driven**: the $j=0$
endomorphism $\phi:(x,y)\mapsto(\omega x,y)$ of secp256k1 biases the cubic-residue classes
of the $X$-coordinate image of a band-constrained $d$-set, and $E_3$ detects that bias. The
falsifier is a curve swap: **map the same 82 real private keys $d$ onto a non-CM curve $E'$
over the same prime and re-compute $E_3$.**

- **FAIL-TO-REJECT on $E'$** ⟹ anomaly does not survive the curve swap ⟹ **CM-driven**
  (lens confirmed; the E3 secp reading is a $j=0$ curve fingerprint, not a $d$-fingerprint;
  the freed-rule avenue on this surface is curve-structural, not key-structural).
- **REJECT-HIGH on $E'$** ⟹ anomaly survives the curve swap ⟹ **$d$-driven** — the 82 puzzle
  $d$'s carry cubic-residue structure independent of the curve. This points at the puzzle
  generator / PRNG fingerprint and escalates Frontier #29 (group-law joint difference-set
  objects) to priority 1.
- **REJECT-LOW on $E'$** ⟹ over-uniformity on $E'$ (CM was supplying the bias that moved $E_3$
  high on secp). Characterize, do not interpret as a closure.

Either outcome is a scoped empirical characterization. **No security verdict is made or
implied.** Per the standing banners: `secure` / `closure` / `proven hard` / `unbreakable` are
forbidden; this is an anomaly characterization, not a leak claim.

---

## Object (identical statistic to PREREG_diffset_cubic_v1, on $E'$)

```
E3 = a² + b² + c² − ab − bc − ca          (exact integer; = |a + bω + cω²|², ω = e^{2πi/3})
(a,b,c) = counts of cubic classes {χ₃=1, β, β²} over the C(82,2)=3321 UNORDERED pairwise
          x-coordinate differences of the 82 points [d_i]G' on E', over F_P (secp's prime P).
class of z≠0 : r = pow(z,(P−1)//3,P) ∈ {1, β, β²};  β = BETA, β² = BETA² mod P.   [SAME field]
```

**Critical: $\chi_3$ is the field character over secp's $\mathbb{F}_P$ in BOTH cells.** $P$
does not change between secp and $E'$; only the curve (hence the map $d\mapsto X$) changes.
This isolates the curve variable cleanly: same prime ⟹ same $\chi_3$ ⟹ same cubic classes
⟹ the only thing that moves is the geometry of $d\mapsto X$ (CM endomorphism present vs
absent). That is exactly the variable the lens prediction turns on.

E3 is symmetric in $(a,b,c)$ ⟹ invariant to the $\omega\leftrightarrow\omega^2$ labeling.

## Orientation (unchanged)

`χ₃(−1) = 1` at $P$ ($P \equiv 1 \pmod 6$) ⟹ `χ₃(x_j−x_k)=χ₃(x_k−x_j)` ⟹ E3 is
orientation-EVEN on $E'$ just as on secp. Same orthogonal-channel interpretation as the
secp E3: probes the symmetric difference-set subspace `S_diff` is identically blind to.

## Forced structure (decidable, before data; identical to secp E3)

- `a+b+c = C(82,2) = 3321` for every 82-point set.
- **`E3 ≡ 0 (mod 3)` is FORCED** for every 82-point set (`E3 = 3321² − 3(ab+bc+ca)`,
  3321 = 3·1107). Apply-time asserts this — a non-multiple-of-3 = path bug, not signal.

## The non-CM curve $E'$ (fixed before any E′ data)

- $E': y^2 = x^3 + x + 1$ over $\mathbb{F}_P$, $P$ = secp's prime.
- $j(E') = 1728\cdot 4/(4+27) = 6912/31 \notin\{0,1728\}$ ⟹ **non-CM**, no extra automorphisms.
- Nonsingularity: $4a^3+27b^2 = 4+27 = 31 \not\equiv 0 \pmod P$ (trivially, $P \gg 31$).
- Generator $G'$ and group order $N' = \#E'(\mathbb{F}_P)$ computed by Sage (`cmvanishing_curve_setup.sage`).

**Requirement (amended 2026-07-28 after first candidate set all rejected — see Amendment
Note below):** (i) $j(E')\notin\{0,1728\}$ (non-CM); (ii) $G'$ generates a known prime-order
subgroup of order $n'$; (iii) $n' > 2^{130}$ (so $[d]G'$ is distinct for all 82 puzzle
$d\in[1,2^{130})$). The original cofactor $h'\le 4$ AND $n'>2^{254}$ clause is **relaxed**
per the Amendment Note.

> **Amendment Note (2026-07-28, before any E′ X-data is computed).** The first four
> prereg'd candidates — $(a,b)\in\{(1,1),(2,3),(5,7),(9,11)\}$ — were tried via
> `cmvanishing_curve_setup.sage`; **all four have cofactor $h' \gg 4$ over secp's $P$**
> ($h' \sim 2^{65\text{–}100}$, prime subgroup $n'\sim 2^{125\text{–}181}$ bits). This is
> structural for generic non-CM curves over secp's $P$, not a bug: $\#E(\mathbb{F}_P)$ for
> a generic $E$ has a large smooth factor, and a small cofactor is the special case (secp
> itself was selected to have $h=1$; arbitrary $a,b$ will not). The original $h'\le 4$
> requirement was inherited from cryptographic convention (small cofactor is "clean" for
> key generation) and is **not load-bearing for a characterization test**. What is
> load-bearing is: (a) non-CM (the lens prediction), (b) $G'$ of known prime order $n'$,
> (c) $n' > 2^{130}$ (so all 82 puzzle $d$'s map to distinct subgroup points). The first
> candidate, $(a,b)=(1,1)$, satisfies all three (non-CM, $n'\approx 2^{180}$, prime), so it
> is used. The large cofactor $h'\approx 2^{75}$ does not invalidate the test: **both the
> real 82 and the matched null are computed identically as $[d]G'$ in the same subgroup**,
> so they sample the same $X'$-distribution; the CM-vs-non-CM structural difference lives
> in the curve equation, not in the subgroup choice. This amendment is recorded before any
> E′ X-coordinate is computed; no real-82 E′ value has been observed.
- **Record to `diffset_cubic_Eprime_meta_v1.json`:** $P$, $a'$, $b'$, $j(E')$, $N'$, $h'$,
  $n'$, $G'=(G'_x, G'_y)$, which fallback was used, SHA-256 of this prereg file.

## Real 82 on $E'$ (Step 2)

- Source: `solved_puzzles_xy.csv` column `private_key` (the 82 real $d$'s; verified 82/82
  reproduce on-chain secp $X,Y$).
- For each $d$: $X'_i = x([d]G')$ on $E'$. Save `solved_puzzles_xy_Eprime.csv` with the
  original columns plus `X_Eprime`, `Y_Eprime`.
- **No $E_3$ is computed on the real 82 in Step 2.** The decision (Step 5) happens only
  after the null is frozen.

## Matched control (null) — the load-bearing prep (Step 3)

- Pool: the **same** 100,023 $d$-values from `constructed_keys_1to160_100k.csv`
  (known-MT19937, same bit-lengths as real 82, same select-bitlen→random-in-band-$d$→curve
  pipeline). This isolates the curve variable: same $d$-distribution, different curve.
- Pre-compute $[d]G'$ for all 100,023 constructed $d$'s ONCE, cache X-coords to
  `constructed_keys_Eprime_100k.csv`. (~2–5 min EC ops; done once; inner loop is then pure
  field arithmetic, matching the existing secp workflow.)
- **Freeze the $E'$ null**: 10,000 resamples of 82 (one $X'$ per matching real bit-length),
  compute $E_3$ for each, build order statistics.
- **Freeze region $[L', U']$ at the upper/lower 0.025 tails** (two-sided $\alpha \approx 0.05$):
  `L' = A'[249]`, `U' = A'[9750]` of the sorted 10,000-sample null. Seed frozen at
  `20260728`. Save `diffset_cubic_Eprime_frozen_null_v1.npy` (10000 int, all $\equiv 0\bmod 3$)
  + `diffset_cubic_Eprime_frozen_meta_v1.json`.
- **The secp frozen region `[84, 11997]` is NOT reused.** $E'$ gets its own region from its
  own null. This is gate-discipline-critical: each cell of the 2×2 has its own null.

## Controls (Step 4) — must fire or the test is void

1. **Forced-structure:** `E3 ≡ 0 (mod 3)` AND `a+b+c == 3321` for the real $E'$ value.
   Asserted; a violation aborts the run (path bug).
2. **Planted-firing control on $E'$:** concentration plant $\varepsilon$ — reassign
   $\varepsilon\cdot 3321$ pairs to one cubic class — must reject-high at $\varepsilon=0.05$
   with empirical power $\ge 0.9$ against the $E'$ null. If the planted control does NOT fire
   on $E'$, the test is **void** (instrument failure, not a null result) — record and stop.
3. **Independent cross-check regen:** 2000 resamples (seed 4242) from the constructed pool
   via the fast gmpy2 path; confirm the frozen null's shape (mean, 2.5%/50%/97.5% quantiles)
   matches within sampling noise. This is the same cross-check the secp E3 apply ran.

## Power

Reported from the $E'$ null at apply time (the $E'$ null's variance is not assumed equal to
secp's). Expected: 50%/80% power at one class rising $1/3 \to \approx 0.353/\approx 0.363$
($\varepsilon_{50}\approx 0.030$, $\varepsilon_{80}\approx 0.044$), matching secp E3 — but
**measured, not assumed.**

## Falsification (FROZEN, integer order statistics on $E'$ null, two-sided)

```
reject-HIGH (concentration)     iff  E3' > U'     ( = A'[9750], upper tail 0.025 )
reject-LOW  (over-uniformity)   iff  E3' < L'     ( = A'[249],  lower tail 0.025 )
else FAIL-TO-REJECT
```
seed `20260728`, N=10000, achieved two-sided $\alpha \approx 0.05$. Apply rank-$p$:
`min((#{A'≥E3'}+1)/(N+1), (#{A'≤E3'}+1)/(N+1))·2`. Empirical order statistics only;
**no z-score** ($\sigma$ is of order the mean).

## Decision (Step 5)

Compute `E3(X'_real)` on the 82 $E'$-derived X-coords. Exact integer path (gmpy2 if
available). Assert forced-structure. Decision vs frozen $[L', U']$:

| result | reading | next |
|---|---|---|
| `E3' > U'` (REJECT-HIGH) | **$d$-driven** — the 82 $d$'s carry cubic structure independent of curve | escalate: investigate puzzle generator; Frontier #29 group-law $E_3$ as priority 1 |
| `L' ≤ E3' ≤ U'` (FAIL-TO-REJECT) | **CM-driven** — lens confirmed; E3 secp anomaly is a $j=0$ curve fingerprint | close the $d$-leakage reading of E3; pivot freed-lens to group-law objects on secp specifically |
| `E3' < L'` (REJECT-LOW) | over-uniformity on $E'$ (CM supplied the high-$E_3$ bias on secp) | characterize; possible anti-CM signature; do not interpret as closure |

## Scope (load-bearing)

- **SCALE BANNER.** Keys are real secp $d$'s (up to 130-bit), mapped to $E'$ over secp's
  $P$ (256-bit). No measurement at any other prime. Nothing here generalizes past this scope.
- **LANGUAGE RULES.** `secure` / `closure` / `proven hard` / `unbreakable` forbidden.
  Characterization, not a verdict.
- **ANOMALY-DRILL RULE.** Output = characterization of the E3 anomaly's CM-dependence,
  never a security verdict.
- **MULTIPLE COMPARISONS.** This is 1 statistic on $E'$, but sits alongside the secp E3
  ($p\approx 0.033$, 1 of ~7). Report both; do not claim independence. The pair
  {secp E3, $E'$ E3} is 2 tests; a Bonferroni-$\times 2$ on a $p'\approx 0.04$ would be
  $\approx 0.08$ (borderline), matching the secp-side caveat.
- **LENS TAGGING.** The CM-driven prediction is a **lens-generated conjecture**
  (freed-rule, INVESTIGATION mode). The test result is **empirical** either way. Tag the
  prediction and the verdict separately in `RESULT_diffset_cubic_cmvanishing_v1.md`.

## Subspace caveat (inherited from secp E3, still load-bearing)

E3 is a function ONLY of the marginal counts $(a,b,c)$. Provably blind to: (i) orientation-odd
signal, (ii) joint/triangle structure among overlapping pairs that keeps marginals uniform,
(iii) bit-length-band-localized concentration (pooled → diluted). A FAIL-TO-REJECT on $E'$
bounds only the pooled orientation-symmetric magnitude channel **on $E'$**; it does not close
the cubic channel on $E'$, and it does not close any channel on secp.

## What this does NOT do (honest)

- Does not prove anything about leakage either way — it is a scoped empirical
  characterization of one anomaly's curve-dependence.
- Does not reach the subpolynomial question directly; that is the band-width phase scan (a
  follow-up if this test is CM-driven, since then the structure lives on secp and the band
  scan is the next lever).
- Does not test the $p$-driven third cell (would need a third curve over a different prime);
  noted as follow-up only if both CM and $d$-driven come back null.

## Artifacts (this directory)

- `cmvanishing_curve_setup.sage` (Step 1)
- `diffset_cubic_Eprime_derive.py` (Step 2)
- `diffset_cubic_Eprime_null.py` (Step 3)
- `diffset_cubic_Eprime_apply.py` (Steps 4–5)
- `constructed_keys_Eprime_100k.csv`, `solved_puzzles_xy_Eprime.csv`,
  `diffset_cubic_Eprime_frozen_null_v1.npy`, `diffset_cubic_Eprime_frozen_meta_v1.json`,
  `diffset_cubic_Eprime_meta_v1.json`
- `RESULT_diffset_cubic_cmvanishing_v1.md` (after the run)
