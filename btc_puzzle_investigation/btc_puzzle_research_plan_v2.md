# secp256k1 (n,k,D) — Farm-Out Research Plan v2

*Supersedes v1. v1's central mistake: it **triaged ~110 ideas down to 5 by
dismissing whole buckets on priors** ("already answered flat", "circular", "needs
the trace"). That is the sharpen-and-narrow / know-the-answer-before-looking
failure the project methodology exists to prevent. v2 keeps the structure but
**tests everything** — nothing is dropped; priority ordering is allowed, dismissal
is not.*

## 0. The three corrections (why v1 was wrong)

- **"Already answered" (Bucket A) → run each family fresh.** We do not know the
  prior 20k runs used the right features/params/interpretation. Each representation
  (spectral, compression, k-mer, CF, autocorrelation, GF(2) rank, clustering,
  address-hash) is tested **individually** at 100k with its own control (**WP7**),
  in addition to the joint classifier (**WP2**). The 20k number is a hypothesis to
  re-verify, not a result to cite.
- **"Circular" (Bucket B) → the attack is a candidate sweep, and it's valid.**
  `X mod n` is only circular if you feed a model the value at the true `n`. The
  attack computes the statistic for **all** `n' ∈ [1,256]` and bets on the outlier
  — never touching the secret. Tested in **WP6** (rank/z of true-n among candidates,
  with a control that runs the same aggregation).
- **"Needs the trace" (Bucket C/§8) → two-stage, and much of it is public.** On the
  dataset we have `d`, so we can measure whether the exotic quantity carries ANY
  n-information with full access (necessary condition, earned empirically). Then
  recast the extractor onto public `(X,Y)` and test with a control (**WP8**).
  Even the "dead" pairing ideas get **numerically verified** (value + embedding
  degree), not asserted.

## 1. Design rules (unchanged from v1 — the good part)

Positive control mandatory; conditional negatives only; attack-valid uses `(X,Y,N)`
only while structure-probes are labelled and never phrased as attacks; matched-
multiset null for selection, baseline+planted control for map properties; find-
then-confirm with group-by-bits CV; the target is a **hint on n** (posterior shift),
not recovery of `d`; exact integer arithmetic. Enforced in `farm/lib_*.py`.

## 2. Full work-package roster (nothing dropped)

| WP | scope | attack-valid? | farm | status |
|---|---|---|---|---|
| **WP1** | n·Q near-miss identity distinguisher | yes | Sonnet | running |
| **WP2** | joint public→n classifier ceiling (ONE member of the Bucket-A battery, not its replacement) | yes | Sonnet | running |
| **WP3** | small-N exact structural ledger (N≤35) | exact | Haiku | running |
| **WP4** | null n-distribution → sharpens 82-real-key selection priors | probe | Haiku | running |
| **WP5** | GLV residue diagnostic | probe | Haiku | running |
| **WP6** | candidate-sweep distinguisher battery (**reformulated Bucket B** — all the "mod n"/Kronecker/gcd/order ideas as attacks) | yes | Sonnet | dispatched |
| **WP7** | per-family map battery (**Bucket A run individually**: spectral, compression, k-mer, CF, autocorr, GF(2) rank, clustering, coord-stats, address-hash) | yes | Sonnet | dispatched |
| **WP8** | exotic/§8 two-stage (**Bucket C**: trace necessary-condition probe → public recast → control; + pairing verified numerically) | probe→yes | Sonnet | dispatched |
| **WPZ** | Opus 4.8 coordination → `btc_puzzle_findings_v3.md` | — | Opus 4.8 | after all land |

## 3. Idea → WP coverage map (every source idea has a home)

- §0 background — harness (`farm/lib_data.py`), verified 301/301 EC + 501/501 decomp.
- §1 Inv 1 (lattice/HNP) → WP1; Inv 2 (GLV) → WP5+WP2; Inv 3 (D-term residue) → WP7/WP8.
- §2.1 consecutive-key check → WP3; 2.2–2.9 → WP6 (sweeps) + WP2/WP7.
- §3 cycles + Strategy A (anchored kangaroo) → WP1; B (mod-n sieve) → WP6; C (neural) → WP2/WP7.
- §4 Tier1 → WP2/WP7; Tier2 (2.1 n·Q, 2.2 D-term, 2.3 GLV) → WP1/WP5; Tier3 (sinc, LLL, hash) → WP7/WP8.
- §5.1–5.8 → WP7 (spectral/compression/CF/k-mer/autocorr) + WP8 (RMT/lattice).
- §6 cycles 1–5 → WP1 (n·Q), WP6 (residue cascade), WP7 (periodicity/bit-entropy), WP2/WP8 (ML/deep).
- §7 A/B/C (thermo/moiré/chaos) → WP8 stage-1 probes.
- §8.1–8.20 → WP8 (each with a stage-1 empirical verdict + public recast).
- §9.1–9.25 → WP5 (GLV/endomorphism), WP7 (compression/CF/rank/cluster/hash), WP8
  (pairing verified, TDA), WP4 (sampling/gap 9.14), WP1 (BSGS/neighbour 9.4/9.5/9.11/9.24).

If the coordinator (WPZ) finds any source idea with no test, that is a defect to
fix, not to explain away.

## 4. Orchestration

Fable 5: plan + harness (done) → dispatch WP1–WP8 (background, tiered) → spot-check
each `RESULTS/*.json` (control fired? attack-valid guard? conditional phrasing?
idea actually tested vs argued-away?) → re-run failures → spawn Opus WPZ →
relay the bounded verdict + one recommended next action. Out-of-100k-scope vector
(sub-second PRNG seed, findings v2 §3.1) flagged for a separate track by WPZ.

## 5. Success criteria (v2)

- Every source idea maps to an executed test with a fired control — **zero
  "dismissed" entries** in the v3 findings.
- Bucket B ideas reported in their **sweep (attack) form**, with ranking payoff.
- Bucket C ideas each carry a **stage-1 empirical** verdict (with matched null),
  not a theoretical one; pairing triviality is a measured number.
- Bucket A families reported **individually** with per-family floors, plus the joint.
- All nulls conditional; any ≥2σ survivor stated as a bounded posterior shift on n.
