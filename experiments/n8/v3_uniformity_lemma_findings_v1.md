# v3 uniformity lemma, findings v1 (2026-11-21)

The killing-cycle shape inventory for both V3 survivor families, extracted from the existing
census artifacts, normalized to shapes, and verified per shape over all valid offset bases
(exact `Fraction` arithmetic; Sturm sequences and Cauchy bounds over `Fraction` polynomials).
Artifacts: `v3_uniformity_lemma_v1.py` (instrument), `v3_uniformity_lemma_v1.out` (full report,
960 lines). No existing file edited; no git. Runtime ~40 s.

## 0. One-line verdict

**The shape set is FINITE and SMALL, and every shape's product inequality is decided exactly:
the death argument of either family is a finite table of (skeleton, offset-pattern, killing-set)
entries.** Anchored: 54 skeletons, 58 shapes, all 58 verified at the realized base-period bases.
Self: 379 skeletons, 1107 shapes, of which 907 kill for EVERY integer $m \ge 5$ on every pattern
and the remaining 200 kill on exactly-computable proper subsets (all observed occurrences
covered; zero failures). The residue is named: it is the anchored family's k=25 member (its
words reorganize hinge-terminal, so its 9 killing shapes are shared with no other member), and
— on the self side — a 200-shape tail whose killing sets are m-scoped rather than uniform.

## 1. The instrument and its validation (the foundation; all [T] exact)

`v3_uniformity_lemma_v1.py` reconstructs, for every death node of both censuses, the exact row
system from the word grammar (rows $u_p \le c\,u_q$, strict iff flagged; for a word
$z_0..z_{n-1}$ with readings $r_i$, laps $l_i$):

- $z_0$: entry $r_0 \to 0$ weight $\frac{1}{8l_0-1}$; progress $0 \to r_0$ weight $8l_0+1$;
- $z_i$ ($i \ge 1$): entry $r_i \to r_{i-1}$ weight $\frac{8l_{i-1}+1}{8l_i-1}$; progress
  $r_{i-1} \to r_i$ weight $\frac{8l_i+1}{8l_{i-1}+1}$;
- $z_i$ ($i \ge 2$): irred $r_{i-2} \to r_i$ weight $\frac{8l_i-1}{8l_{i-2}+1}$ (and for
  $z_1$ the same row against the root "zone" at lap 0, weight $8l_1 - 1$);

plus base rows (weak order, B-caps), region rows, and the family window rows (anchored: apex
$\frac{33}{7(8k-1)}$ / cover floor $\frac{8j+1}{7}$ / cover entry $\frac{7}{8j-1}$ on the hinge
reading; self: the strip rows $\frac{1}{8m-1}$ and $8m+1$). It then REPLAYS the instruments'
candidate loop (a reimplementation of the `d0_points_only_k6_v2` M-closure) and recomputes
every killing cycle as (failed candidate edge) + (least-product path).

Validation, both families together:

- **Rejection multisets: 1219/1219 death nodes reproduced exactly** — for every death node the
  replayed (candidate, why) multiset EQUALS the recorded one. The row grammar and the closure
  are a complete, independent re-derivation of the censuses.
- **Certificate products: 13,741/13,741 exact** — every entry/progress product matches the
  recorded JSON value; every anchored irred product matches the corrected (de-contaminated)
  value, 9/9 against `v3_march_census_table_v1.out` (the v2 logging contamination of
  `v3_march_census_findings_v1.md` §5 is thereby re-derived and bounded: only irred rows were
  affected, exactly as diagnosed).

This matters beyond hygiene: a Lean transcription of the census can be GENERATED from the
reconstruction (deterministic, exact, grammar-checked) rather than transcribed from the JSONs.

## 2. Shapes (the normalization; the task's definition made exact)

A **killing cycle** is the closed walk (failed candidate edge + least-product path); each edge
is tagged (kind, lap tuple, weight, strict). A **skeleton** is (cyclic reading tuple, edge-kind
tuple). A **shape** is a maximal set of same-skeleton cycles whose lap slots agree slot-wise
under the mechanism-derived role rule — per slot: EQUAL (abs), or EQUAL-OFFSET-FROM-BASE
(tied), or FREE on a slot the search itself leaves window-determined: the candidate lap, the
death-frontier lap, and (anchored family only) any slot whose reading is 6, the window-pinned
reading (E891's role rule: the +1/+2 drifts). The shape count is an UPPER bound (greedy clique
cover, deterministic, may over-split). A shape's **offset pattern** $\tau$ = the tuple of
free-slot offsets (relative to the member's base $k$ or $m$) realized by an instance; the
product along a pattern is a rational function $P_\tau(b) = A_\tau(b)/B_\tau(b)$ of the base,
with $A_\tau, B_\tau$ products of linear 8-grid factors (and the constant window/region rows).

Inventory (Part B/C of the .out):

| family | killing cycles | skeletons | shapes | multi-base shapes | single-base |
|---|---|---|---|---|---|
| anchored (k = 15, 17, 25 nonvacuous) | 145 | 54 | 58 | 8 | 50 (37@k15, 4@k17, 9@k25) |
| self (m = 5..10) | 13,596 | 379 | 1107 | 540 | 567 |

Cycle lengths: anchored {1:29, 2:38, 3:45, 4:29, 5:1, 6:1, 7:2}; self {1:1817, 2:3589, 3:3550,
4:3884, 5:647, 6:109}. Cycles of length > 2 are REQUIRED (the findings' §4d verdict, now
exhaustive): 5,845 of 13,741 cycles have ≥ 3 edges, and the multi-row shapes are the dominant
killers, not the exception. Dominance: anchored top-15 shapes cover 50% of cycles, top-44 90%;
self top-17 cover 50%, top-296 90% — the dominant grammar is the 44 multi-base self shapes with
≥ 30 instances, covering 9,908/13,596 cycles (72.87%), led by

- `5→6→3→4` (cand_entry + 3 path entries), 856 instances;
- `4→5→6→3` (same kinds), 716;
- `6→5` and `3→6` (2-row), 454/440;
- the zone-6 self-loops `6→(closed)` and `5→(closed)`, 431/381;
- the 3-row strip-ratio cycles `4→6→3`, `3→5→6`, `6→4→5`, `3→4→5→6`, `6→3→4→5`, `5→3→4` —
  the E887/E891 "3-row cycles REQUIRED and recurring in shape" table, now with exact roles.

The self-family role structure is remarkably rigid: on every dominant shape the path-zone laps
are tied (offset 0 or +1 from m), the strip rows carry the base, and only the candidate and
death-frontier laps are free, with offset windows +1..+8. The anchored family's multi-base
grammar (8 shapes) is: the three verbatim absolute cycles (89/95 at laps (12,11); 267/299 at
(3,11,5,1); 81/89 at (10,11)) — low-zone cycles pinned by the region rows, base-independent —
plus five zone-6 shapes whose candidate laps are tied+1 and whose zone-6 laps are free
(the value-tied role), including the 3-row irred cycle `6→4→5` = (47/121-direction)
`cand_irred + z_entry + z_entry` with worst instance 3705/3751 at k15 and 4161/4247 at k17 —
exactly E891's corrected certificates, recovered by the normalization.

## 3. Per-shape verification (the product inequalities; all [T] exact)

The kill criterion is $P \le 1$ with a strict edge in the cycle (the `tropicalCycle_infeasible`
semantics); every cycle here carries the strict candidate edge, and $P < 1$ is the generic
case. For a shape with pattern $\tau$, write $D_\tau = B_\tau - A_\tau$. **Claim of this
section: for every integer base $b$ in the pattern's killing set $K_\tau = \{b \ge b_{\min} :
D_\tau(b) \ge 0\}$, the cycle kills.** $K_\tau$ is decided EXACTLY: by Cauchy's bound every
real root $r$ of $D_\tau$ obeys $|r| \le R := 1 + \max|a_i/\mathrm{lead}|$, so the finite range
$[b_{\min}, \lceil R\rceil + 1]$ is evaluated exactly and the tail sign is sign(lead);
Sturm sequences over `Fraction` cross-check on the real half-line. deg $D_\tau \le 3$ over all
observed shapes (0, 1, 2 or 3). A symbolic self-check reproduces every realized instance's
recorded product from the polynomials (13,741/13,741).

- **SELF, all integer $m \ge 5$: 907 of 1107 shapes PROVED-UNIFORM** ($D_\tau > 0$ on the whole
  half-line for every pattern — e.g. the re-read self-loops: pattern $(c, c-1)$ gives
  $P = \frac{8(m+c-1)+1}{8(m+c)-1} < 1$ identically in structure, deficit exactly
  $\frac{6}{8(m+c)-1}$-shaped; the 856x shape's ten patterns all ALL-STRICT, drift
  $\gamma \in \{1/8, 3/8, 1\}$).
- **SELF: 200 shapes PROVED-SCOPED**: some patterns kill only on a proper subset of
  $[5, \infty)$, and the subset is exactly computed. Two mechanisms, both pure lap arithmetic:
  (i) *initial segments* — the shape `3→6` (cand_entry + z_entry) with candidate offset
  $c_1$, frontier offset $c_2 = c_1 + 1$ has $D = 48c_1 - 32m - 16$, killing iff
  $3c_1 > 2m + 1$ (e.g. pattern (5,6): kills on $m \in [5,7]$ — and the recorded product
  EXACTLY 1 at m=7 is this pattern's endpoint: the tangency is the pattern's own boundary,
  not an artifact); (ii) *final segments* — small-candidate patterns of `2→6` (cand_entry +
  z_irred) kill only for large m (e.g. pattern (0,2): kills for $m \ge 10$; it occurs at
  m = 10 only). Every observed occurrence lies inside its pattern's killing set (200/200
  covered; zero violations).
- **ANCHORED, realized base-period bases {15, 17, 25}: 58/58 PROVED** (every realized instance
  $< 1$; worst across the family 2204441/2223375 ≈ 0.9915). The absolute-slot shapes are
  base-independent and pass Sturm on the whole real half-line (they are constants); the
  free-slot shapes are verified at the realized bases — the regime beyond the base period is
  vacuous (E892: k=48 admits no hinge word), so no shape instances exist there.

## 4. The uniformity lemma (the statement a Lean theorem consumes)

Purist register; the lens-free form of what the census shows. Inputs, table, conclusion:

```
-- DATA (transcribed, per family): the finite shape table S = {(S_skeleton, role pattern,
--   pattern set P_S, killing-set certificates)}.  Anchored |S| = 58, self |S| = 1107.
--   Each entry carries, per pattern τ ∈ P_S, the exact rational functions A_τ, B_τ and the
--   verified inequality D_τ(b) = B_τ(b) − A_τ(b) ≥ 0 on its killing set K_τ (a finite union
--   of integer intervals, Cauchy/Sturm-certified).

def ShapeEntry : Type := (skeleton × slot_roles × (τ : ℕ → ℤ) × (D : ℤ → ℚ) × K_τ)

theorem march_death_of_census (F : Family) (mem : Member F) (W : ZoneWord F mem)
    (hmax : MaximalWord W) (hcensus : MemberCensus F mem) :
    ∃ (cand : Candidate) (C : KillingCycle), RejectsAt W cand ∧
      LeastProductCycle W cand C ∧
      ∃ entry ∈ S F, ShapeOf C entry ∧ PatternOf C entry τ ∧ mem.base ∈ entry.K τ
```

consumed by the PROVED engine

```
theorem tropicalCycle_infeasible  -- Fresh/TropicalCycle.lean, PROVED, standard-three axioms:
--   a satisfied ratio system admits no closed walk with product < 1, or = 1 with a strict edge
```

which turns (shape instance + $D_\tau(\text{mem.base}) \ge 0$ + strict edges) into the
infeasibility of the candidate extension, i.e. the death of W.

**Status of each piece.**

- [L] PROVED: `tropicalCycle_infeasible` and its instances (the telescope; the strictness-flag
  logic) — the consumption engine. The ladder law E840 remains data-side [T] (1420/1420 pairs)
  and is not needed for the table entries (each entry's inequality is self-contained), but it
  is the right instrument for the UNIFORM-in-base forms: the observed $D_\tau$ are affine in
  the dominant cases, where "kills for all $m \ge 5$" reduces to one linear inequality.
- [T] DONE (this artifact): the shape tables with their $D_\tau$ polynomials and killing sets,
  exact; the full replay validation that the tables are the censuses' death arguments.
- [T] NAMED (transcription, mechanical): per member, the maximal words + rejections + shape
  ids, generated from the reconstruction into a MechDataBatch-style Lean file (the
  ComposedFamData precedent); per (entry, member) the concrete rational inequality. For fixed
  members these are ground-ℚ evaluations (`decide`/`linarith` scale; deg D ≤ 3).
- [T] NAMED (per-member exhaustiveness): the search-tree certificates (no other maximal words,
  no cover words) — the M4CertSound-shaped data layer (E889/E890's three named items), outside
  this artifact.
- [P→L] the half-line forms: for the 907 self shapes uniform on $[5,\infty)$ and the affine
  $D_\tau$, the uniform statement is one `linarith` step from the explicit coefficients; for
  deg ≥ 2 a polynomial-ordering certificate (Sturm data transcribed, or `nlinarith` on the
  explicit roots). Not yet written in Lean.

**Hypotheses the lemma rests on (named, not hidden).** (a) *Grammar stability*: the pattern
sets $P_S$ extracted at m = 5..10 are the family's grammar at further m — empirically the
skeleton union saturates along m (increments +57, +65, +24, +15, +12 over m = 6..10; 85 core
skeletons at every m; 54 clusters realized at every m), but the CAP runs are not DONE-status
trees. (b) *The vacuous regime*: the anchored orbit translations t ≥ 1 (k = 48 verified
vacuous, E892; t ≥ 2 unrun) die by the UPSTREAM-CYCLE lemma — the floor-row short cycle against
the region rows (e.g. 4→6→6⇝0→0→4, product 277695/519841 < 1) — which has NO rejection tables
in these artifacts (vacuous members record no deaths) and is NOT covered by the shape tables.
It is the last named instrument between the censuses and the V3 finite-type reduction
(E892's "next step", unchanged).

## 5. The residue (named precisely)

- **Anchored: the residue is the k=25 member.** 9 of its shapes are shared with no other
  member (`1→6→5→2`, `2→6→5`, `4→6→5`, `5→6`, `6→5→4`, `6→(cand_progress)`, `3→6→5→2`, plus
  singletons), and NO skeleton is common to all three nonvacuous members. Mechanism (consistent
  with `v3_march_census_findings_v1.md` §4d'): k25's maximal words reorganize HINGE-TERMINAL —
  all four end at the hinge, placed directly off the (3,4) exit at the invariant 33/7 anchor —
  so the rejections sit at the hinge-zone self-loop pair (a,b) = (24,25)/(25,26) instead of the
  mid-word positions. The k15↔k17 adjacent pair shares 8 shapes (the cross-member grammar,
  §2); verbatim recurrence is an adjacent-orbit property, exactly as the findings concluded.
  Note the residue is ARCHITECTURAL, not arithmetical: all 9 k25-only shapes verify (§3).
- **Self: the residue is a tail, not a member.** 567 single-base shapes (135@m5, 75@m6,
  103@m7, 60@m8, 52@m9, 142@m10), mostly low-instance path-dependent cycles whose slots are
  absolute (they occur where words with those paths exist). Largest single-m residue: 26
  instances of `4→5→6→(closed)` at m=5 only. Every one verifies (§3); none threatens the
  grammar — but the per-m shape SETS drift (0 core anchored; 54 core self clusters), which is
  why the lemma carries the grammar-stability hypothesis.

## 6. Anomalies / open items

1. **The tangency is real and structural**: the m=7 recorded product EXACTLY 1 (shape `3→6`,
   pattern (5,6)) is the pattern's own killing endpoint ($D = 48 \cdot 5 - 32 \cdot 7 - 16 = 0$;
   kills on $m \in [5,7]$, occurrences m ∈ {6,7}). Same tie-plane structure E894 found on the
   sliver lines; a Lean transcription must use the WEAK inequality + strict edges there, not
   $P < 1$.
2. **200 scoped self shapes have m-bounded or m-bottomed killing sets.** The uniform claim
   "one grammar kills at every m" holds for 907/1107 observed shapes; for the rest the death
   argument at large m must come from OTHER patterns (the m-dependence of the pattern grammar
   is the open piece). The exhaustive (DONE-status) runs at m = 11+ would settle whether the
   grammar stabilizes; the instrument here computes each candidate pattern's killing set
   on contact.
3. The anchored y ∈ {4,5} members and the k=48/81+ orbit translations are VACUOUS (no hinge
   words) — their upstream killing cycles are not in these artifacts (only the one traced
   instance for (4,13,19) in the findings §3). Extracting the upstream-cycle table uniformly
   needs an instrumented rerun of the vacuous members (named follow-up; ~10-20 min compute
   each at the current budgets).
4. The shape count is an upper bound (greedy over-splitting); the true shape count is ≤ 58
   (anchored) and ≤ 1107 (self). The skeleton counts (54/379) are exact.
5. Instrument notes: the reconstruction reproduces the v2 contamination semantics ONLY through
   the corrected table (irred products), by design; the self family's logs are clean (v3), so
   its irred certificates were validated directly against the recorded values (13,741/13,741
   includes them).

## 7. Repro

```
python3 -I v3_uniformity_lemma_v1.py > v3_uniformity_lemma_v1.out
# reads: v3_march_census_v2_y<y>k<k>.out (23 members + y6k48), v3_march_census_table_v1.out
#        (the 9 corrected irred certificates), v3_march_self_m5..m10.out.  Exact Fractions;
#        Sturm sequences and Cauchy bounds over Fraction polynomials; no floats anywhere.
```

New files only: `v3_uniformity_lemma_v1.py`, `v3_uniformity_lemma_v1.out`, this note. No
pre-existing file edited or removed; no git.
