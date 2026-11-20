# v3 march census findings v1 (2026-11-20)

Full base-member march death census for the n=8 V3 survivor types, exact `Fraction` throughout.
Artifacts live in `experiments/n8/`: per-member JSONs `v3_march_census_v2_y<y>k<k>.out` (23),
table `v3_march_census_table_v1.out`, instrument `v3_march_census_v2.py`, probe copies
`v3_march_census_v1_y4k13.out` / `v3_march_census_v1_y5k13.out`, validated v1 run `v3_march_census_v1_k15.out`.

## 1. Instrument correction (v1 → v2), recorded per protocol

**Error found:** in `v3_march_census_v1.py`, the extension loop `for y in range(1, 7):` rebinds the
function parameter `y` (the hinge reading index). The hinge test `has_hinge = (0, y, k) in chain`
executes before the loop only on the first stack iteration (where `chain` is empty); on every later
iteration `y == 6`. So for hinge index y = 6 the check was accidentally correct (the validated
(6,15,22) run is unaffected), but for y ∈ {4,5} v1 tested `(0, 6, k) in chain` — the **wrong hinge**:
`hinge_words`, `cover_words` and `deaths` were censuses of the zone-6-at-lap-k words, not of the
member's hinge words. The search tree itself (nodes, window rows, rejections) is identical.

Consequence: the /tmp probes (4,13,19) and (5,13,19) were v1 runs and are mislabeled (their
781 / 1885 "hinge words" and 445 / 1189 "deaths" are censuses of (0,6,13)-words). They are copied
verbatim to `v3_march_census_v1_y4k13.out` / `_y5k13.out` for provenance; the census below uses v2.
A v1 rerun of (4,13,19) reproduced `/tmp/mc_y4k13.json` exactly (nodes 10504, hinge_words 781,
deaths 445), confirming the provenance.

**Fix (`v3_march_census_v2.py`, one-line fix + header, nothing else changed):** capture the hinge
index in `hy` before the loop; test `(0, hy, k)`. Regression: v2 on (6,15,22) reproduces the
validated `v3_march_census_v1_k15.out` exactly — nodes 10489, hinge_words 26, cover_words 0,
death_count 13, deaths identical, killing_cycle_top identical.

## 2. Census result: cover_words = 0 for ALL 23 members; the march death holds

**All 23 members completed (status DONE).** Every member reports **cover_words = 0** — no word
containing the hinge reaches a 7-covering exit anywhere in the searched region. **No carve of W_0
on the V3 region** at the stated scopes. Scopes: y=6 members search the type's exact rho_7 range
[25, (8j+1)/7) (B = (8j+1)/7 auto, exact); y ∈ {4,5} members close the type only for **rho_7 ≤ 49**
(B = 49; the type pins rho_y's window but leaves rho_7 region-bounded). The four y=6 members
k = 21, 23, 25, 27 hit the 1800 s wall on the first pass (~26k nodes) purely from machine load;
reruns with the identical budget finished in 118–263 s each (nodes 28858–71569) — recorded honestly
here because the first-pass CAP numbers (e.g. 26k nodes at CAP) say nothing about the census.

## 3. The dominant death mode is upstream of the march: the hinge is unreachable

20 of the 23 members report **hinge_words = 0**: no irredundant word contains the hinge reading
(0, y, k) at all, so the census is empty and the march death holds vacuously (a fortiori). This is
a *stronger* death than the march death. Verified concretely for (4,13,19) by a per-node trace: the
hinge candidate (4,13) is never even generated in the 10504-node tree. The mechanism (from a
materialised (6,15) node of that tree): the word's own high-lap zone-5/6 readings pin those zones
far below the region rows (e.g. u_6 ≤ 15/721 u_0 vs the region cap 1/25), and the member's floor
row u_0 ≤ (8j+1)/7 · u_y then closes a short cycle against any attempt to place the hinge — e.g.
the killing cycle 4→6 (entry 121/103) → 6⇝0 (15/721) → 0→4 (floor 153/7), product
277695/519841 < 1. The survivor *type* survives the minimal row system (v3_passtype census); it
dies as soon as rows must be realised by a strict, irredundant word.

Consequently the march census is **nonvacuous only where hinge words exist**: (6,15,22) with 26
hinge words / 13 maximal deaths, (6,17,25) with 4 / 2, and (6,25,37) with 4 / 4. The population
along the orbit is NOT monotone: 26 → 4 → 0 → 0 → 0 → 4 → 0 across k = 15, 17, 19, 21, 23, 25, 27
(y=6) — k=25 revives — and every y ∈ {4,5} member is empty. Node counts for y=4 also collapse with
k (10504 → 600): the thin window prunes the tree to nothing.

## 4. Invariance test (the key deliverable)

Compared (6,15,22) ↔ (6,17,25) — the two members with deaths, consecutive in the orbit k → k+2
(j → j+3). Evidence: per-death corrected certificates (true death-node logs recaptured by an exact
DFS replay, `/tmp/truelogs_k{15,17}.json`; entry/progress certificates recomputed on them match the
recorded products exactly, 0 mismatches).

**(a) Word correspondence.** k15 death 7 and k17 death 1 are the *same word* except
(6,8) → (6,9) and (6,15) → (6,17): 18 of 20 readings verbatim, all zone ≤ 5 laps unchanged. The
translation acts by ROLE, not uniformly: hinge-zone readings tied to the hinge shift **+2**
(preserving the hinge entry exactly: (8k−1)·33/((8k−1)·7) = 33/7 for every k — the invariance
anchor), the low zone-6 reading shifts **+1** (its exit value ≈ 2.5 is approximately preserved),
zones ≤ 5 shift **0**.

**(b) Rejection tables correspond position-by-position.** Same 8 (why, zone) rejections in the same
order: (1,3,entry), (2,4,entry), (3,5,entry), (4,6,irred), (4,7,entry), (5,10,progress),
(5,12,entry), (6,·,entry).

**(c) Same (a,b) pairs recur — verbatim on zones ≤ 5, shifted +2 on zone 6.**

| cycle | k=15 | k=17 | recurrence |
|---|---|---|---|
| self-loop entry, zone 5, (a,b) = (11,12) | 89/95 | 89/95 | **verbatim** |
| self-loop progress, zone 5, (11,10) | 81/89 | 81/89 | **verbatim** |
| entry cycle, zone 1, path row 5→1 (3/13) | 267/299 | 267/299 | **verbatim** |
| entry rejection of zone-6 candidate (a,b) = (11,16) → (11,18) | 5785/5969 | 6497/6721 | shape identical; laps +2 (candidate), +1 (link lap 8→9); product drifts |
| self-loop entry, zone 4, (6,7) | 49/55 | — (not in k17's 2 deaths) | absent ≠ contradicted |
| self-loop entry, zone 6, (16,17) | 43/45 | — | absent ≠ contradicted (k17 counterpart would be (18,19) = 145/153) |

**(d) Cycles of length > 2 are REQUIRED, and they recur in shape.** The irred rejection of the
candidate (4,6) — the zone-4 reading just above the hinge's zone-4 successor position — is killed
after correction by multi-row cycles, and no 2-row cycle kills it at k15 (the least-product
relaxation would have found one). Corrected certificates (true minimal cycles; see §5):

- k15 deaths 2, 5, 7: 4→5→6→4 = (57/31)·(65/47)·(47/121) = **3705/3751** ≈ 0.9877 < 1 — a 3-row cycle.
- k15 deaths 4, 10: (57/31)·(17/55)·(111/25)·(47/121) = **5055273/5157625** — 4 rows.
- k15 death 0: (23/41)·(49/15)·(65/47)·(47/121) = **14651/14883** — 4 rows.
- k15 death 9: (57/31)·(17/55)·(17/23)·(5/3)·(1/7)·(177/7)·(47/121) = **45679629/46501147** — a 6-row
  cycle routing through the window rows (front 1/7, cover floor 177/7) themselves.
- k17 death 1: the SAME 4→5→6→4 shape with the zone-6 coefficients shifted:
  (57/31)·(73/47)·(47/137) = **4161/4247** ≈ 0.9798 < 1.
- k17 death 0 additionally admits a 2-row cycle (89/31)·(47/137) = **4183/4247** — via the
  (6,11)→(4,4) link that only k17's richer word contains; no k15 counterpart (k15's word has no
  (6,11), and every k15 4⇄6 2-cycle product exceeds 1 — the closest is (13/5)·(47/121) = 611/605 ≈
  1.0099, then (71/25)·(47/121) = 3337/3025 ≈ 1.1027 — none killing).

So: the long cycles recur across members **in shape** (same row kinds, same zones, zone ≤ 5 laps
verbatim, zone-6 laps shifted +1/+2); their products are *not* invariant constants — they drift —
but every shifted instance stays < 1, so the death argument carries over the orbit. Verdict: the
E885 translation-invariance prediction is confirmed at the level of argument structure, with the
refinement that the lap shift is role-dependent (see (a)), and products drift within < 1.

**(d') Orbit-distance effect, from (6,25,37).** The third nonvacuous member, k=25 (four orbit steps
from k=17), keeps the same rejection-position skeleton — (1,3), (2,4), (3,5), (4,·), (5,·) entry
rejections, (5,·) progress rejections, and hinge-zone self-loops — but its word architecture has
reorganised: all 4 maximal words END at the hinge, placed directly off the (3,4) exit (entry
199·(33/1393) = 33/7, the invariant anchor), with zone-6 climbed via laps {9, 14, 16, 17, 19}. The
hinge-zone self-loops are (a,b) = (24,25) = 193/201 (progress, below-hinge re-read) and (25,26) =
67/69 (entry, above-hinge candidate) — the pair positions relative to k differ from k15's (16,17)
because the hinge is terminal here. The (1,3) rejection product drifts off the verbatim value
(267/299 → 420291/488267). So verbatim recurrence is a property of *adjacent* orbit members; at
larger distance the skeleton and the < 1 killing persist while the tight identification degrades.

**(e) The mod-8 ±1 heuristic is unreliable in both directions.** False positive: 147/155 is a 2-row
cycle (5⇄4 = (57/31)·(49/95)) whose *raw* product 2793/2945 ≡ (1,1) mod 8 reduces by gcd 19 (≡ 3)
to (3,3). False negative: the genuine 3-row cycle 3705/3751 has 3705 = 57·65 ≡ (1,1) and
3751 = 31·121 ≡ (7,1) — both ±1 mod 8. The reliable criterion is the structural row count of the
corrected certificate path, not arithmetic on the reduced product.

## 5. Second instrument finding: irred certificates are contaminated (verdicts unaffected)

The `_add` logging wrapper logs rows *before* the feasibility verdict, and the failed `irred` row
stays in `t.log` when `least_prod_path(t, y, pv)` computes its certificate. The relaxation then
routes through that infeasible row and loops it (each traversal multiplies by a < 1 factor), so
every recorded irred product is a loop artifact — e.g. k15 death 0's recorded
361129635879854966104654493/383563458231675132606848099 against the true minimal cycle 14651/14883
(ratio ~7.4e-8). `entry`/`progress` certificates are computed on the pre-add state and are exact
(0 mismatches over all 102 entry/progress certificates recomputed on the true logs; 9 irred
certificates corrected, 111 total across the two members). **The verdicts (rejections, deaths, cover_words)
are unaffected** — failed-add states are always discarded, and the closure's infeasibility check
itself only composes feasible rows. The corrections above (§4d) are computed from the true
death-node logs excluding the failed row. A v3 instrument would store the certificate *before*
logging the failed row; counts would be identical, so no rerun was spent on it.

## 6. Anomalies / open items

1. The upstream-death mechanism (§3) is established empirically (per-node trace + killing cycles);
   a proof that the hinge is unreachable for ALL 20 empty members — presumably the floor-row cycle
   6⇝0→y with the member floor coefficient (8j+1)/7 — is not yet written down. The census data is
   the evidence base for it.
2. The non-monotone hinge-word population 26 → 4 → 0 → 0 → 0 → 4 → 0 along the y=6 orbit is
   unexplained beyond window drift; in particular why k=25 revives (its words reorganise so the
   hinge sits terminal at the 33/7 anchor) is a structural question the census raises but does not
   answer.
3. The invariance verdict rests on the adjacent pair k15 ↔ k17 (clean); k25 (four steps away)
   supports the skeleton-level claim but degrades verbatim recurrence (§4d'). A k=19 or k=23
   hinge-word revival would test the pattern further; none occurs in this base list.
4. One incidental cleanup: a first relaunch attempt mis-parsed arguments under zsh and briefly
   created four junk files `v3_march_census_v2_y6k* *[0-9].out` (names with spaces); these were
   deleted (no other file touched). No pre-existing file was edited or removed.

## 7. Repro

```
python3 -I v3_march_census_v2.py <y> <k> <j> <B|auto> 5000000 1800 > v3_march_census_v2_y<y>k<k>.out
# y=6: B auto = (8j+1)/7 exact; y in {4,5}: B = 49 (scope rho_7 <= 49)
python3 -I v3_march_census_v1.py ...   # v1 kept untouched; mislabels y in {4,5} (see §1)
```
Exact Fractions only; floats steer nothing here. The corrected certificates and true logs come from
`/tmp/mc_true_logs.py` (exact DFS replay) — rerunnable as
`python3 -I /tmp/mc_true_logs.py 6 15 22 auto 20000`.
