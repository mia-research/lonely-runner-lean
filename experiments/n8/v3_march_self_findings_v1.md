# v3 march census, SELF-ANCHORED family (rho_7, m) — findings v1 (2026-11-21)

Census of the self-anchored survivor classes E887 opened (the reach-dominating word at B=40
starts (rho_7, lap 5), its anchor zone (39 u_7, 41 u_7) contains the window start x=1 exactly when
rho_7 ∈ (39,41)). Population: strips C_m = (8m−1, 8m+1) for m = 5..10, i.e. the family where the
ANCHOR READING IS THE STRIP READING ITSELF (u_6 = 1/rho_7 pinned by the strip, no rho_4 front).
Artifacts in `experiments/n8/`: instrument `v3_march_self_v1.py`, per-m JSONs
`v3_march_self_m<m>.out` (m = 5..10), first-pass copies `v3_march_self_m<m>_firstpass_contended.out`
(m = 5..7), validation `v3_march_self_m5_B40_validation.out`, this note. Exact `Fraction` throughout.

## 1. Instrument (variant of the validated v2 census; search loop verbatim)

`v3_march_self_v1.py` is a copy of `v3_march_census_v2.py` with the BASE ROWS changed; the search
loop (stack, extension rows, irredundancy, lap pruning, cover test, rejection recording) is v2
verbatim. Base rows per m: sorted (base_system(7, B)), rho_6 > 17 strict, rho_7 ≥ 25 (subsumed by
the strip for m ≥ 4, kept for region parity), and the STRIP itself —
u_6 ≤ 1/(8m−1) (non-strict, entry side) and u_6 > 1/(8m+1) (strict, exit side). NO rho_4 front rows
and NO v2 survivor-window rows (the v2 window is hinge-type-anchored on the rho_4 front; the
self-anchored window is the strip). B = 8m+1 exact ('auto'): the strip pins rho_7 < 8m+1 and the
weak order caps all readings below it, so B cuts nothing. Hinge = (6, m) (anchor zone, lap m).
`cover_words` counts hinge-words reaching a 7-covering exit; `cover_words_any` counts ALL such
words; `jmax_seen` is the largest lap generated anywhere (searched frontier).

One non-base-row change (logging fix, per `v3_march_census_findings_v1.md` §5): rows are appended
to `Sys.log` only when `add()` succeeds, so `irred` certificates are true least-product killing
cycles instead of v2's loop artifacts. Search observables are unaffected (§2).

## 2. Validation on m=5 (all checks passed)

(a) **Banked-word replay.** The B=40 best word banked in `v3_reach_v1_B40.out` (starts (6,5), ends
(6,25), depth 23, sup exit 67/13 = 201/39) was replayed zone-by-zone under the variant's base rows
at B=40 and at B=41: every step feasible (entry, progress, irred rows all add), every zone inside
the instrument's candidate window (jlo..jhi — so the census tree really generates this word), the
cover test fires on NO prefix, hinge (6,5) present, final sup exit exactly 67/13 ≤ 67/13. So the
banked word is a genuine path of the m=5 census tree with frontier x = 67/13 ≈ 5.154 < 7.

(b) **Logging-fix invariance.** Node-capped (3000-node) A/B run, v2-style logging (log before
verdict) vs v3 logging: status, nodes, hinge_words, cover_words, cover_words_any, jmax_seen and
all 200 death chains identical bit-for-bit; entry and progress certificates identical; only the
irred certificate products differ (as designed — v2's are loop artifacts). Search semantics
unchanged; the fix only cleans the recorded killing cycles.

(c) **B=40 census semantics.** The variant at m=5, B=40 reports cover_words = 0 and
cover_words_any = 0 (no false cover anywhere in the searched tree), consistent with the banked
`v3_reach_v1_B40` exhaustive scan (covers = 0, best sup exit 67/13 over the full 7.13M-node tree).
A deeper solo B=40 leg (`v3_march_self_m5_B40_validation.out`, 20670 nodes, 480 s wall) confirms:
cover 0/0, hinge_words 20669, jmax_seen 12.

## 3. Census table (per m)

Carve-capable thresholds: a 7-covering zone-6 exit needs lap j ≥ 7m−1 (non-strict, exit = 7) and
fires first at j = 7m (strict; e.g. m=5: (8·35+1)/39 = 281/39 > 7 while j=34 gives exactly 7,
killed by the strict flag). The strip reach value at lap j is (8j+1)/(8m−1) (single row
u_6 ≤ 1/(8m−1) sets the entry side).

| m | strip | run | status | nodes | hinge_words | deaths | cover_words | cover_any | jmax_seen | deepest banked/observed |
|---|---|---|---|---|---|---|---|---|---|---|
| 5 | (39,41) | solo (2226 s wall), B=41 | CAP | 184762 | 184761 | ≥200 (depth 8–15) | 0 | 0 | 17 | banked word: lap 25, exit 67/13 ≈ 5.15 |
| 6 | (47,49) | solo (1978 s wall), B=49 | CAP | 26363 | 26362 | ≥200 | 0 | 0 | 14 | — |
| 7 | (55,57) | solo 1416 s wall, B=57 | CAP | 205226 | 205225 | ≥200 (depth 9–16) | 0 | 0 | 18 | — |
| 8 | (63,65) | first pass 1800 s, 8-way contended | CAP | 17102 | 17101 | ≥200 | 0 | 0 | 16 | — |
| 9 | (71,73) | first pass 1800 s, 8-way contended | CAP | 17097 | 17096 | ≥200 | 0 | 0 | 17 | — |
| 10 | (79,81) | first pass 1800 s, 8-way contended | CAP | 16390 | 16389 | ≥200 | 0 | 0 | 20 | — |

Protocol note (honesty): the machine's scheduler was unreliable throughout this session — the
m = 8,9,10 first-pass runs executed 8-way parallel degraded to ~10 nodes/s (~17k nodes each); the
solo reruns ran at 13–146 nodes/s and OVERSHOT their wall deadlines (up to 2226 s wall for 1400 s
requested — system stalls; nodes are the meaningful budget). All runs are protocol-valid CAP runs
(5M node cap; per-run deadlines as listed) and the first-pass m=5,6,7 outputs are preserved
verbatim as `v3_march_self_m<m>_firstpass_contended.out`. The solo m=5,6,7 trees are 1.2×–10×
deeper than their first passes (185k/26k/205k vs 19k/18k/17k nodes; frontiers 17/14/18). One
structural consequence of determinism: the DFS prefix is deterministic, so the recorded
deaths[:200] samples are IDENTICAL between first-pass and solo runs (the solo value is the deeper
searched frontier jmax_seen and node coverage, not new death records) — hence the §5 shape counts
are stable statistics of the family, not run artifacts. cover_words = 0 everywhere; **no ALIVE
cover was found at any m** — nothing to verify against `chain_cover_v4.covered`, and per the
task's priority clause this is reported immediately: the self-anchored family did not open a
carve.

## 4. The population inversion: this family is hinge-DENSE — genuine march deaths

The anchored (rho_4,1)-family census died mostly VACUOUSLY: 20 of 23 members had hinge_words = 0
(the hinge is unreachable upstream of the march). The self-anchored family INVERTS this:

- **hinge_words ≈ nodes** at every m (99.99%): essentially every node of the tree contains the
  anchor zone (6, m).
- **Every maximal word STARTS at the hinge**: the first zone is (6, m) in 200/200 recorded deaths
  at each of m = 5..10. The anchor zone is the march's first zone — its entry (8m−1)u_6 ≤ 1 is the
  strip row itself, and the strip exit row u_6 > 1/(8m+1) makes the (6,m) zone the only way to
  cover x = 1 (any other first zone (y, j) with y < 6 forces u_y ≤ 1/(8j−1), and the weak order
  u_6 ≤ u_y then pins the strip from above… the recorded words all take (6,m) first).
- Deaths are therefore REAL march deaths: words extend to depth 8–17 (per-m modes 10–11) and die
  by rejection, not by unreachability of the hinge.

## 5. Killing-cycle comparison across m — the E891 invariance pattern HOLDS

Rejection skeletons (ordered (why, zone) counts over the 200 recorded deaths per m) are
near-identical across m = 5..10: the same six entry positions (zones 1..6) with zone-1 at EXACTLY
200 in every m (one per recorded death — every maximal word rejects a zone-1 candidate), the
mid-zone entry ranks mildly reshuffled (z4/z5/z6/z2 alternate at the top across m), then progress
rejections on zones 3, 4, 5/6. The same killing-cycle SHAPES recur at every m, with laps
translated:

- **Self-loops, zone 6**: entry self-loop of candidate lap j after (6, j−1), product
  (8j−7)/(8j−1) — observed at j = m+3 dominantly (m+4 second), e.g. 19/21 (j=8, m=5), 65/71 (j=9,
  m=6), 73/79 (j=10, m=7), 89/95 (j=12, m=8 AND m=9 — identical value because a self-loop product
  depends only on the candidate lap), 97/103 (j=13, m=9,10), 35/37 (=105/111, j=14, m=10). The
  89/95 value is the same fraction the anchored-family k15/k17 comparison met verbatim (there on
  zone 5, lap 12) — cross-family echo of the same lap-12 self-loop.
- **The (8m+1)/(8m+7) row**: the two-row zone-3 rejection 6⇝3 carries path-row coefficient exactly
  (8m+1)/(8m+7) at every m (41/47, 49/55, 57/63, 65/71, 73/79, 81/87), reduced to 19/21 (m=7) and
  27/29 (m=10) when m ≡ 1 (mod 3). Progress self-loops zone 6 carry
  (8(m+2)+1)/(8(m+3)+1) = 57/65, 65/73, 73/81, 81/89, 89/97, 97/105 across m = 5..10 — same form,
  laps +1 per step.
- **Three-row cycles REQUIRED and recurring in shape** (v2 findings §4d pattern): the top killers
  at every m are the 3-row cycles
  6⇝3⇝4⇝5 (entry rejections of zone-5 candidates), 5⇝6⇝3⇝4 (zone-4 candidates), and
  3⇝4⇝5⇝6 (progress, zone-3 candidates) — e.g. the 6⇝3⇝4⇝5 entry cycle kills 74/110/142/174/184/172
  recorded rejections at m = 5..10. Their middle rows collapse to the STRIP RATIO (8m+1)/(8m−1)
  (49/47 at m=6, 57/55 at m=7, 65/63 at m=8, 73/71 at m=9, 81/79 at m=10) — the strip plays the
  role the invariant 33/7 anchor played in the anchored family.
- **Lap-translation law**: low-zone candidate laps shift +1 per m-step, zone by zone — zone-5
  entry candidates peak at m+3 (129, 111, 127, 149, 159, 153), zone-3 rejections at m+2 (153, 159,
  162, 143, 142, 134), zone-2 at m+1, zone-1 at m+1/+2 (2 for m=5,6; 3 for m=7..10). Zone-6
  candidate laps concentrate at m+2..m+6 with tails to m+7 (m=5 solo) and m+8 (m=6 solo). The whole
  word architecture translates with m — forced by the strip's scale (u_6 ≈ 1/(8m) makes zone-6 lap
  j cover x ≈ j/m). The solo trees also surface cross-reading echoes: m=5 records a zone-5 entry
  self-loop 19/21 (lap 8) — the same fraction as zone-6's lap-8 self-loop, since a self-loop
  product depends only on the candidate lap.
- **Products drift but stay < 1** at every shifted instance (drift law: coefficients are ratios
  (8(m+k)+α)/(8(m+k')+β); the death argument carries over the family exactly as E891 found for the
  anchored orbit).

## 6. Structural verdict: same mechanism, different phase — and the march stalls early

**The death mechanism is the SAME as the anchored family's** — upstream rejection cycles kill
words before any 7-covering exit (cover_words = 0 at every m, every searched tree) — but its PHASE
is inverted: anchored words died before reaching the hinge (vacuous march death); self-anchored
words are born ON the hinge (first zone (6,m)) and die DURING the march. The family is genuinely
marching, and the march stalls immediately:

- Recorded maximal words die at frontier x = exit(last zone) ≈ (8m+17)/(8m−1) (the zone-6 lap-(m+2)
  exit — the SECOND strip crossing — is the modal death at every m: 65/47 ≈ 1.38 at m=6, 89/63 ≈
  1.41 at m=8, 105/79 ≈ 1.33 at m=10), worst recorded ≈ 2.1 (m=5). The searched frontier lap
  jmax_seen = 17, 14, 18, 16, 17, 20 (m = 5..10; the m=5 and m=7 solo trees pushed their first-pass
  frontiers 12 → 17 and 16 → 18) — the stall is structural: candidates need (8j−1)u_y ≤ x with
  x ≲ 2 in the searched words and every reading pinned near the strip, so generated laps stay
  ≈ 1.4m–2m (jmax/m between 1.4 and 2.0 across the family) even at 185–205k nodes — far below the
  carve's 7m.
- Deeper words EXIST in the tree: at m=5 the banked word (a census-tree path, §2a) climbs to
  x = 67/13 ≈ 5.154 via zone-6 laps up to 25 = 5m — 3× past the searched frontier — and STILL
  falls short of 7 by the reach margin 7 − 67/13 = 24/13 ≈ 1.85. The carve needs zone-6 lap ≥ 7m
  (exit > 7): ~2m more laps of climbing than the best known word, with every lap-step opposed by
  the §5 killing-cycle grammar (each zone-6 re-read at lap+1 demands a fresh entry row whose cycle
  against the strip rows + weak order closes < 1 — the observed modal deaths).
- So the census verdict is: **the self-anchored family is dead by the same mechanism at every
  m = 5..10 searched** — no cover_words at any scope — with the death now demonstrated on the
  words themselves (nonvacuous at every m), not a fortiori. The m=5/B=40 slice additionally carries
  the banked exhaustive reach scan (covers = 0 over the full 7.13M-node tree, reach 67/13 < 7).

## 7. Anomalies / open items

1. The m = 8,9,10 trees are first-pass contended (~17k nodes; §3 protocol note). A solo rerun
   would deepen the searched frontier (expected ~500k nodes each); the census verdict at those m
   currently rests on CAP-scope trees.
2. jmax_seen is a searched-frontier statistic (DFS order: the (6,·) branches are explored first and
   the budget is spent inside them), not the tree's true depth — the banked word proves lap 5m
   exists at m=5. A DONE-status run would make the no-cover statement exhaustive for its B.
3. The depth trend of recorded maximal words DECREASES with m (modes 10/10/10 at m=5/6/7 solo,
   then 11/10/10-11 at m=8/9/10; deaths concentrate at exit-x ≈ (8m+17)/(8m-1) → 1): the stall
   tightens as the strip thins. Whether some intermediate m (outside 5..10) maximizes the climb —
   i.e. whether the family's reach (8j+1)/(8m−1) at fixed climb depth j−m peaks near small m — is
   open.
4. The m=5 first-pass top shape ranking differs slightly (z4-entry cycle leads at m=5,6; z5-entry
   leads at m=7..10) — rank reshuffling inside the same shape grammar; the count order over 200
   recorded deaths is not a full-population statistic (deaths[:200] truncation on CAP).

## 8. Repro

```
python3 -I v3_march_self_v1.py <m> auto 5000000 1800 > v3_march_self_m<m>.out
# validation replays:  /tmp/validate_self_m5.py (banked-word replay, B=40 and auto)
#                      /tmp/logfix_invariance.py 3000 (node-capped logging A/B)
# comparison:          /tmp/self_cycle_compare.py 5 6 7 8 9 10
```
Exact Fractions only. First-pass contended runs preserved as
`v3_march_self_m<m>_firstpass_contended.out` (m=5,6,7). No pre-existing file was edited or removed;
new artifacts only: `v3_march_self_v1.py`, per-m `.out`, this note.
