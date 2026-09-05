# secp256k1 (n,k,D) — Farm-Out Research Plan v1

*Devised by Fable 5 for the 100k dataset (`constructed_keys_1to160_100k.csv`,
100,023 rows). Numerical work packages are farmed to Claude model tiers; Opus 4.8
coordinates the results. Written to a file per project convention — the plan is the
artifact, not chat.*

Source of ideas: `~/Downloads/secp256k1_nkd_investigation_ideas_consolidated.md`
(9 sections, ~110 distinct proposals). This plan **triages** them against what is
already established and turns the survivors into runnable, self-contained subagent
briefs in `farm/wp_briefs/`.

---

## 0. What "farm out to other models" means here

Per project rule §0, local LLM agents (Qwen/DeepSeek/Gemma/Codex; the
`delegate`/`gemini` skills) are **retired and forbidden**. "Other models" = Claude
tiers dispatched through the `Agent` tool's `model` override:

| tier | role | WPs |
|---|---|---|
| **Haiku** | deterministic / mechanical compute, tabulation | WP3, WP4, WP5 |
| **Sonnet** | ML + judgment on distributions, control calibration | WP1, WP2 |
| **Opus 4.8** | cross-result adjudication + the bounded verdict | WPZ |

Fable 5 (this session) devises the plan, builds+validates the shared harness,
dispatches the WPs, spot-checks each result file (subagent summary ≠ what it did),
then spawns the Opus coordinator.

## 1. Design rules baked into every WP (from memory / findings v2 §0)

1. **Positive control is mandatory.** A null with no firing control is discarded as
   underpowered, not reported. (`lib_control.plant_leak`.)
2. **Conditional negatives only.** Never "impossible / ruled out". Bind every null
   to its features + sample size + noise floor. (`lib_control.conditional_negative`.)
3. **Attack-valid vs structure-probe.** An *attack* may use `(X, Y, N)` only.
   Using `d,n,k,D` to "predict" `n` is circular — the F1 / `XY mod n²` trap.
   (`lib_data.assert_attack_valid`.) Structure probes (WP4/WP5) are diagnostics,
   never phrased as attacks.
4. **Right null for the question.** Selection-of-`d` hypotheses → matched-multiset
   null (`lib_control.matched_null`). Map-property hypotheses → baseline + planted
   control. Single-scale uniform only tests "universal math relation".
5. **Find, then confirm.** Work the construction for a mechanism first; held-out /
   CV is the *final filter*, grouped by bit-length (never train+test same N).
6. **The target is a HINT on n** (a posterior shift), not recovery of `d`. Knowing
   exact `(n,k)` pins ~16 top bits; `D` is still ~60% of the free bits.
7. **Exact integer/rational arithmetic** for all curve values (no float smoothing).

## 2. Triage of the ~110 source ideas

**Harness validated** (`farm/smoke_test.py`, ran clean): loader parses all 100,023
rows; the shared EC code reproduces the dataset `(X,Y)` from `d` 301/301; our
`decompose()` reproduces the dataset `(n,k)` 501/501; planted-leak control lifts
grouped-CV accuracy to ~2.3× the public-only null (which sits at the 1/256 floor).

| bucket | source ideas | disposition |
|---|---|---|
| **A. Already answered — pure `(X,Y,N)→n/k` map property is flat at high power** (20k MI≈0.0005) | 1.1, 1.2, 2.2, 2.6, 3.3, 5.1, 5.4, 5.5, 5.6, 5.2, Strategy C, 8.4, 8.7, 9.3, 9.9, 9.12, 9.13, 9.18, 9.21, 9.23, and the many χ²/residue/compression/FFT-of-X restatements | **Collapse into WP2** — one definitive 100k-power ceiling with a calibrated control, not 30 reruns. |
| **B. Circular as attacks** (need secret `n/k/d`) | `X mod n`, `XY mod n²` (F1, resolved=noise), 2.5, 9.2 (·mod n), most "mod n" tests | **Drop as attacks.** Kept only as labelled structure probes where novel (WP5). |
| **C. Trace-only / need bits-of-d** (unavailable in the real puzzle; reduce to a map property at the endpoint) | 3.1, 5.7, all of §8 seismic/crystal/fluid/DNA/TDA/quantum-walk/side-channel/music/linguistics/spin-glass/percolation/archaeology/game-theory, 4.2, 8.16 & 9.8 (Weil pairing ≡ 1, dead) | **Drop as attacks.** Their only attack-relevant residue is "does periodicity of k/n scar the final (X,Y)" = Bucket A = WP2. |
| **D. Worth farming on the 100k set** | 2.1 / Cycle-2 (n·Q near-miss), 2.3 (small-N exact / D=0 match), 9.5 (BSGS small-N), the marginal-n / n-class selection watch-items, GLV residue diagnostic | **WP1–WP5** below. |

Net: ~110 ideas → **5 numerical WPs + 1 coordination WP**, with the redundancy and
the circular/trace-only dead ends removed up front.

## 3. The work packages (full briefs in `farm/wp_briefs/`)

| WP | title | attack-valid? | farm | why it survived triage |
|---|---|---|---|---|
| **WP1** | n·Q near-miss distinguisher | **yes** | Sonnet | only source idea that exploits the defining identity *and* runs as an attack (tries all n′∈[1,256]); source doc's own #1 pick |
| **WP2** | public→n map-property ceiling at 100k | **yes** | Sonnet | the definitive high-power version of the whole Bucket-A pile; replaces ~30 redundant tests |
| **WP3** | small-N exact structural ledger (N≤35) | exact | Haiku | turns statistics into fact on low bands; is WP1's positive control |
| **WP4** | null n-distribution + selection-prior sharpening | probe | Haiku | 100k = a high-power *matched null* for the 82-real-key n-class watch-items |
| **WP5** | GLV / endomorphism residue probe | probe | Haiku | separates the one novel GLV diagnostic from the 5 redundant GLV restatements (minor) |
| **WPZ** | Opus 4.8 coordination → `btc_puzzle_findings_v3.md` | — | Opus 4.8 | adjudicate against the checklist; write the bounded verdict |

Dependencies: WP3 provides WP1's exact control (run WP3 first or in parallel and
let WP1 consume its output). WP4 needs `matched_null` (in `lib_control`). WPZ runs
last, after all `RESULTS/*.json` land.

## 4. Shared harness (built + validated this session)

```
farm/
  lib_data.py       curve constants, exact EC ops, (n,k,D) decompose,
                    100k loader, PUBLIC-only feature guard (assert_attack_valid)
  lib_control.py    plant_leak, matched_null, grouped_cv_score,
                    permutation_null, conditional_negative
  smoke_test.py     proves loader+EC+decompose+control (PASSED)
  wp_briefs/        WP1..WP5, WPZ — each a self-contained subagent prompt
  RESULTS/          one WP<n>.json per package; SCHEMA.md defines the contract
```
Env: Python 3.14, numpy/pandas/scipy/sklearn/ecdsa present; **no** gmpy2 / xgboost
/ lightgbm → use `HistGradientBoostingClassifier` and native big-ints. 10 cores /
24 GB → WPs may parallelize across bands and run in background.

## 5. Orchestration (dispatch sequence)

1. **Fable 5** (done): plan + harness + smoke test.
2. Dispatch in parallel (background `Agent` calls):
   - WP3 → Haiku, WP4 → Haiku  (fast, deterministic; WP3 feeds WP1)
   - WP1 → Sonnet, WP2 → Sonnet  (heavier)
   - WP5 → Haiku  (low priority; only if capacity)
3. As each returns, **Fable 5 spot-checks** the `RESULTS/*.json`: control fired?
   attack-valid guard respected? phrasing conditional? Re-run any that fail a check.
4. **WPZ** → Opus 4.8 reads all result files + briefs, adjudicates, writes
   `btc_puzzle_findings_v3.md` (versioned), returns a 6–10 line summary.
5. **Fable 5** relays Opus's verdict + the single recommended next action.

## 6. Success criteria

- Every reported null carries a fired control and conditional phrasing.
- No attack-claim rides on a secret-derived (circular) feature.
- WP2 states the 100k map-property ceiling with its detectable-strength floor.
- WP1 reports (a) small-N exact control fired, (b) a bounded large-N verdict, (c)
  the top-1%/10% ranking payoff = the actual "hint on n".
- v3 findings supersede v2 with the 100k-power results, no absolutes.

## 7. Explicitly out of scope for the 100k farm

- **Sub-second PRNG-seed recovery** (findings v2 §3.1) — the strongest open
  *generation-side* vector, but it runs against the 82 real keys + a seed brute,
  not the constructed 100k set. Flag for a separate track; WPZ names it as a
  next-action candidate.
- **Kangaroo compute** on exposed-pubkey puzzles — engineering/compute, not a
  dataset-numerical question.
- Anything requiring `d`'s bits or the double-and-add trace **as an attack** (the
  real puzzle exposes only address, or `(X,Y)` for multiples-of-5): Bucket C.
