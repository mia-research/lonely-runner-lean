# PREREG — Escape Coverage of Theorem 10.1 at n = 8 (v1)

Pre-registered 2026-09-07, BEFORE any data. Binding under CLAUDE.md §2 and the Anomaly-Drill
protocol; deviations must be disclosed in the run report. Manuscript = `lrc_proof_allN_v11_8.md`.

## 1. OBJECT

The set `H` of hard-case, Theorem-10.1-eligible integer speed tuples at n = 8:
`T = (v1 < ... < v6, V)`, positive, `gcd(v1..v6,V) = 1`, `V > v6`, `7*v1 < V <= 7*v6`
(hard case, line 1300), and `gcd(p, L_G) = 1` with `p` = largest prime factor of `V`,
`L_G = lcm(v1..v6)` (Lemma 9.2(a), line 1311). Measured per `T in H`: whether escape (ii)
(Lemma 5.2-D, line 1006) fires; whether escape (iii) (Theorem 5.2-P, line 632) fires.
Escapes (i) and (iv) are excluded by prior proof (vacuous in the hard case for n >= 4) and are
NOT re-measured. Tuples with `gcd(p, L_G) > 1` are Theorem 11.1 and OUT of scope; their count
is printed beside every coverage figure (§8), never suppressed.
Feature and target are the same object: this is a census, not a correlation test. No tautology
risk, and no inference beyond a census may be drawn from it.

## 2. STATISTIC (one, fixed now)

Primary `C = |{T in H : (ii) or (iii) fires}| / |H|`, per arm, always reported as the four-cell
table `[(ii) only | (iii) only | both | neither]`. Residual `R = 1 - C`. If the residual count
is <= 200 in an arm, every residual tuple is listed individually with
`(v1..v6, V, p, q, L_G, |I_G|, |B|, |I_A|)`. No max-over-cells statistic. No secondary
statistic may be promoted to primary. Characterisation (not verdict) is required: the residual
is described by its distribution over the §3 strata and by whether `q = V/p = 1`. A residual
concentrated in one stratum is a finding about that stratum, not a closure.

## 3. POPULATION, SAMPLING, ARMS

- **Arm E (exhaustive):** slow speeds `<= 12`. All `C(12,6) = 924` slow sets, all `V` in
  `(7*v1, 7*v6]` with `V > v6`, then the §1 filters. Report `|H_E|` and the count rejected by
  each filter separately (gcd != 1 | not hard case | `gcd(p,L_G) > 1`, i.e. Thm 11.1).
- **Arm S (sampled):** slow speeds `<= 30`. Lexicographic enumeration is BANNED as a sample.
  `random.Random(20260907)`, shuffled slow-set index space, cap 400 accepted tuples per `v6`,
  target 60,000. The candidate population size is counted (not estimated) and printed with
  every Arm-S number so the sample fraction is known.
- **Compute cap (declared, not silent):** Arm S excludes `L_G > 10**6` (cost of `I_G` is
  `8*L_G`); the excluded count and its `(v1, v6, p)` profile are reported as stratum `CAP`.
  Arm E is uncapped (`L_G <= 27720`).
- **Strata, fixed now:** `v1 = 1` vs `v1 >= 2`; `p in {2,3}` vs `p >= 5`; `q = 1` vs `q >= 2`.
  No data-dependent cut, no quantile bins.

## 4. PILOT AND POWER

Pilot BEFORE the main run: Arm E restricted to slow speeds `<= 9`, reporting the **marginal**
firing rate of (ii) and of (iii) separately plus the four-cell table.
Abort/re-scope rule (binding): if either marginal is `> 99%` or `< 1%`, the main run does not
proceed as specified. It is re-scoped to coverage conditional on the §3 strata and no others,
with the saturated escape reported as saturated-in-scope. A saturated escape is uninformative
in the same way in either direction and is recorded as such, not as a result.
Power: a census, not a hypothesis test. Arm E resolves a residual of size 1 exactly. Arm S at
`N = 60,000` resolves rate `5e-5` (expected count 3, `P(0 | 5e-5) = 0.05`); a rate below
`1.7e-5` is indistinguishable from zero and is written `< 1.7e-5, not zero`. **Arm S may never
report "no residual".**

## 5. CONTROLS

**Tight instances (printed, not judged).** For `{1,2,3,4,5,6,7}`, `{1,2,3,4,5,7,12}`,
`{1,4,5,6,7,11,13}` (each `M = 1/8` exactly) print `V, p, q, L_G`, whether the tuple is in the
hard case at all, whether `gcd(p,L_G) = 1`, and if in scope the (ii)/(iii) bits. An escape
FIRING on a tight instance is NOT a contradiction — the escapes certify `M >= 1/n`, not
`M > 1/n`. Pipeline FAILURE is exactly: (a) a printed hard-case/gcd classification
inconsistent with a direct integer recomputation of the same inequality; or (b) an escape
reported as firing whose own witness fails verification.

**Witness verification (object-level, mandatory).** When (ii) fires: `t* = Fraction(1, 8*v1)`,
assert `||v_j t*|| >= 1/8` in `Fraction` for all seven speeds. When (iii) fires: extract
`beta_0 in B ∩ I_A` and its `m''`, form midpoint `Fraction(2*m''+1, 2*M)`,
`M = 8*L_G*L_A*p`, assert `||v_j t|| >= 1/8` for all seven. Any failure halts the run. This
checks the escape's own witness, not a proxy.

**Planted controls (must fire, both directions).**
P1 (ON for (ii)): `v1 = 1`, all speeds `!= 0 mod 8` — (ii) must fire. P2 (OFF for (ii)): some
`v_j ≡ 0 mod 8*v1` — (ii) must not fire. P3 (ON for (iii)): threshold `n*L_A` replaced by `-1`
— must fire 100%. P4 (OFF for (iii)): threshold `10**18` — must fire 0%. P5: `|B|` via
cyclic-interval union must equal brute-force enumeration of every `m''` in every band, on 200
seeded small tuples. P6: with A-speeds `= {q}`, assert `L_A == q`, `|I_A| == 6*q`,
`n*L_A == 8*q` from the general Step-2 definition (line 859), not from the closed form.
If any planted control misbehaves, the null is uninformative and the run is VOID — no coverage
figure is reported.

## 6. EXACTNESS

Integer / `Fraction` only on the signal path. No `float`, no `math.floor`, no `/` on integers
(use `//`), no `numpy`. Breach detector, all three required: (a) `assert isinstance(x,(int,Fraction))`
at every escape boundary and witness check; (b) a builtin shadow that raises on `float(...)`;
(c) a grep of the harness for `float|math\.|numpy|\.[0-9]` attached to the run report. No
carve-out. A float found is a defect, not a rounding question.
Source fidelity: the implementations of Lemma 5.2-D and Theorem 5.2-P must each carry, as a
comment directly above the function, the verbatim manuscript statement with line numbers
(5.2-D 1006-1013; 5.2-P 632-646; `I_G` 816-857; `I_A` 859-863; `alpha`/`beta` 872-874).
Audit is against those quotes, never a paraphrase.

## 7. FALSIFICATION

Hypothesis: "(ii) and (iii) cover the Theorem-10.1 hard case at n = 8." Abandoned if Arm E
gives residual `>= 50%`, or if the Arm E residual is non-empty and shows no concentration in
any §3 stratum.

## 8. PRE-COMMITMENT (before the run)

| Outcome | Conclusion |
|---|---|
| Residual empty in Arm E and Arm S | "(ii) or (iii) covers every Theorem-10.1 hard-case tuple in SCOPE"; Arm S stated as `< 1.7e-5`, not zero. NOT a proof of LRC(8); 5.2-H stays open outside the scanned range; Thm 11.1 untouched. |
| Residual non-empty, `<= 200` in Arm E | List it individually; characterise by §3 strata and the `q = 1` flag. That set is where the general-n proof at n = 8 reduces, via Remark 5.2-G (line 1104), to LRC(8) itself. Next probe = that set, not a re-fit. |
| Residual `>= 50%` in Arm E | §7 hypothesis abandoned; escapes recorded as covering a minority stratum, that stratum characterised. |
| Pilot marginal saturates | Re-scope per §4; saturated escape reported uninformative-in-scope; no coverage headline from the aborted design. |
| Planted control misbehaves | Run VOID (§5). No number reported. |

Standing prohibitions: (a) a high coverage figure does NOT prove LRC(8) — coverage of a
sufficient condition is not a proof of the conclusion, and the content sits in the residual;
(b) abstaining on Theorem 11.1 (`gcd(p, L_G) > 1`) is NOT a closure of it, and every coverage
number carries the Theorem-11.1 out-of-scope fraction beside it.

## 9. SCOPE STRING (attaches to every number)

`n = 8; 7*v1 < V <= 7*v6; gcd(tuple) = 1; gcd(p, lcm(slow)) = 1 (Thm 10.1 only, Thm 11.1
excluded); Arm E slow <= 12 exhaustive | Arm S slow <= 30 seeded shuffle N = 60k, L_G <= 1e6;
escapes (ii) Lemma 5.2-D and (iii) Theorem 5.2-P only; (i) and (iv) proved vacuous.`
