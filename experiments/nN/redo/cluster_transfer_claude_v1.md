# Cluster transfer: exact hypotheses for the phased reduction (claude v1)

Script `cluster_transfer_claude_v1.py`, output `cluster_transfer_claude_v1.out`.
Exact Fraction/int arithmetic throughout; no float LP. Caps: <=2000 arrangements,
60s monotonic deadline, cascade move cap 300/case, single foreground process, no
multiprocessing/stdin. Actual run: 882 arrangements, 1.48s, 0 unfinished cases.
`cluster_transfer_claude_brief_v1.md`'s named main-running-log entries (E339,
E350, E373, E377) were not locatable anywhere under the LonelyRunner tree or in
git history (checked by content grep and commit-message grep); the brief marks
them optional ("if useful"), so the work below proceeds without them. Read
before writing: `cluster_window_v1.py`, `cluster_gap_v1.py`, `chains_modulo_cluster_v1.py`
(not imported -- its top-level body unconditionally loads three pickles, exactly
the "unguarded expensive top-level work" the brief warns against), `core.py`,
`walk.py`, `quantity_tests_v1.py`, `e151_block_v1.py`, `holef_cascade_v1.py`,
`tie_structure_v1.md`, `mapped_cascade_rules_v1.md`, `core_window_run_review_v1.md`,
`first_gate_formalisation_v1.md`, and the Lean files `InertReadingN.lean` and
`TrainCollapseN.lean`.

## Setup

R = 8 d_min t, d_min = 1, readings rho >= 1. Cluster rho_i = c·x_i, x_i >= 1,
x_min = 1. Decompose R = a + u/c. A cluster reading's actual value is
(c·x_i)·R = phi_i + x_i·u exactly, phi_i := (a·c·x_i) mod 8 -- an identity, not
a conjecture. A slow reading gives s·R = a·s + (s/c)·u. Clear is (d·R) mod 8 in
[1,7] inclusive; blocked (strict capture) otherwise, matching
`quantity_tests_v1.cascade`'s cd(d·t) </>= 1/8 after R = 8t.

**The mechanism is already proved, not rediscovered here.**
`LRC.InertReading.iterate_insert_clear` (`InertReadingN.lean`, E316/E327) proves:
inserting a reading that stays clear (circDist >= 1/8) at every one of the N
states visited by a run does not change that run's first N moves. Applied once
per slow reading, this is exactly the claim that on an admissible window [A,B]
where every slow reading is jointly clear, the full cascade's blocked set equals
the cluster-alone blocked set while the state stays in [A,B]. My contribution is
checking the exact algebra that turns this into the (a, c, x, phi) bookkeeping
above, and testing where two specific shortcuts people might take instead break.

## 1. Identity check (not a discovery)

213 bounded cases (c up to 20011; 1-2 slow readings; cluster size 2-4; near-
boundary phases phi_i in {0,1,7} in 127/213 cases). For each: find [A,B] via
exact joint-interval intersection on the slow readings, run the real cascade on
the full arrangement restricted to [A,B], and separately run the phased-cluster
cascade (variable u = c(R-a), delta_i = phi_i) from u=0, clipped to the same
window. **0/213 mismatches**, including degenerate (A=B) and the c=20011 cases.
This is VERIFIED-INSTANCE support for the algebra, not a new theorem; no ties
were encountered in this random family (ties were separately confirmed to be
handled correctly -- multiple simultaneous setters kept -- on one constructed
example at the primitive level, `run([(1/2,0),(1/3,1/3)], 0)`).

## 2. Two simplifications, falsified

**Dropping the phase** (forcing phi_i := 0, i.e. assuming the window entry
carries no phase) is wrong **even with a single slow reading**: phi_i =
(c·x_i) mod 8 is generically nonzero regardless, because a = A = 1 does not
make c·x_i mod 8 vanish. 94/103 single-slow and 48/50 multi-slow sampled cases
falsify it.

**Restarting the cluster at its own first opening** -- i.e. `cluster_window_v1.py`'s
own model: find the cluster's fresh unphased first lonely R' with R'>=c, predict
R = R'/c -- is **not a separate error** in the single-slow-reading case: there
it is provably a=1 always, and the sweep confirms 0/103 wrong. It is `cluster_window_v1.py`'s
own stated hypothesis (a slow runner alone below a cluster), correctly realised,
not a shortcut to reject. It **fails once a second slow reading is present**
(4/50 sampled cases, found by search over A != 1 configurations), because then
a = A != 1 generally, and "restart fresh" silently assumes a = 0.

Headline example (both failures on one arrangement): S = {1, 9, 27, 32, 63}
(s=[1,32], c=9, x=[1,3,7]). Slow window [A,B] = [33/32, 39/32]. True restricted
landing R = 65/63 (1 move). Phase-dropped prediction: R = 329/288 (wrong, inside
the window but the wrong point). Restart-at-own-opening prediction: R = 1
(wrong -- not even inside [A,B], since the slow part itself is blocked at R=1).
This generalises, not contradicts, `cluster_window_v1.py`: that script's c>=9,
one-slow-reading search is the a=1 special case, exact there; extending its
"ignore the phase" step to more than one slow reading is the error, and this is
a new small counterexample to that extension, not a re-run of a rejected test.

## 3. Rank word vs transfer map

Coarsened signature (sequence of |blocked set| per move, clipped to [A,B]) vs
fine signature (sequence of (rank, lap) of the actual setter(s)). Over 200 bounded
cases: 10 distinct coarse words, 8 with >1 member; within those, 120 pairs share
both the coarse word and the fine map, but **6 groups share the coarse word
with 2-7 *different* fine maps** (e.g. coarse=(1,): 35 members, 7 distinct
transfer maps). So a shared count-of-blocked-readings pattern does **not**
certify a shared mechanism; what does, by construction, is agreement on the
*ordered sequence of which ranks are blocked and the relative order of their
candidate closing values* at every move -- matching the full argmax trace, not
just its size. This is the "equal rank word, unequal transfer map" trap named
in the brief, demonstrated rather than merely asserted, and it is a caution about
*which* invariant is sufficient, not a new finite-catalogue claim.

## 4. Train collapse: recognize, don't recount

`LonelyRunner/LRC/Spec/TrainCollapseN.lean` (`lonely_of_train_collapse`) is
already proved, no sorry: core C (positive, <=m), offsets E (<=m), |C|+|E|<=7,
N>=56m, and some i<j in E with no e in E at the midpoint (2e != i+j for all
e in E). `recognize_train_collapse` checks exactly these hypotheses on a raw
readings set by trying every top-k split. On 300 bounded integer test shapes
(margin deliberately satisfied in ~60%, violated in ~40%), 183 recognized,
117 correctly rejected (bad margin or cardinality). One useful simplification
found: whenever E contains two offsets of opposite parity, that pair *always*
satisfies the midpoint hypothesis automatically (2e is even, i+j is odd), so the
midpoint search only needs to work at all when E is entirely one parity -- a
cheap pre-check before the full O(|E|^2) scan. Recognition should replace
re-running the cascade per N for any catalogue family matching this shape; the
Lean theorem already supplies the instant for every N>=56m from one (C,E,i,j).

## Scope

No claim of a universal finite catalogue (deliverable 5's instruction). The
identity check is VERIFIED-INSTANCE on bounded families, not a new theorem --
the underlying mechanism is `InertReadingN.lean`, already proved. The two
counterexamples are small and explicit, and distinguish a genuine failure
(extending "ignore the phase" past one slow reading) from a non-failure
(`cluster_window_v1.py`'s own documented a=1 case, which this work leaves
intact, not rejects). The rank-word/transfer-map finding is a demonstrated
caution, not a dichotomy theorem. No Lean, existing script, log, or git state
was edited.

## Summary (counts and caps)

- Arrangements used: 882 / 2000. Wall time: 1.48s / 60s. Cascade move cap 300;
  0 cases hit it (so 0 "unfinished, not inferred as terminated" cases to report).
- D1 identity: 213/213 matched, 0 mismatches.
- D2 counterexamples: phase-drop wrong in 94/103 (single-slow) and 48/50
  (multi-slow); restart-at-own-opening wrong in 0/103 (single-slow, as
  expected) and 4/50 (multi-slow); one small headline example falsifies both
  at once.
- D3 rank word vs transfer map: 6/8 multi-member coarse-word groups contain
  more than one transfer map (120 pairs agree, 6 groups disagree).
- D4 train collapse: 183/300 bounded shapes recognized and citable without
  re-running the cascade; 117 correctly rejected.
- Output file size: 2.4 KB (cap 100 KB). Not committed or pushed.
