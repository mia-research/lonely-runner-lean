## E952 (2026-11-25): E951's blocks in times. For every class-X attaining reading with single identifications, the block at the member is one inequality between a ratio of two window times and a ratio of the moved reading's laps: `b/a ≥ (8m_P+1)/(8m_A−1)` on the below side, mirrored above. For a pin the time ratio is a fixed number; for two readings it is `(g_P/g_A)·(r_jA/r_jP)`, and the closed cell's ratio graph bounds it past the threshold in 8,393 of 9,090 readings [T, exact; PROVISIONAL: covering, as tagged]

**Owner (2026-11-25):** the autonomous run toward a finite set of arrangement types through the cascade (E949). The step is E951's not-understood list, item 2 (the 625 cycle crossers' cell rows as zone memberships).

**Map:** E951's not-understood list, item 2. The cascade is the oracle; what is open is our description of it.

**Source test.** Each object used comes from the record: the pass formula (`one_mover_bound_v1.passes`; E930 item 1, E389); E949's facing ends; E951's ratio graph and provenance (`pin_form_v2`).

M2 class (d).
**Record search (rule 13; PARTIAL):** this entry uses E389 and E930 to E951, all read this session. The bodies of the other entries were not read this session.

Units and population as E951: `d_min = 1`, `R = 8t`; the 2,607 crossers of E949 item 6; every attaining reading of them with one identification for each facing end (11,621 readings; 164 with two or three are not tested here).

**1. The block as a time ratio** [P from the pass formula, PROVISIONAL: covering; the claim supported is that the moved reading blocks a window `[a, b]` at lap `m` exactly when `(8m−1)/(8a) < x < (8m+1)/(8b)` (E930 item 1); T 11,621/11,621; `cycle_read_v1.py` (SHA-256 begins `4233c30e`) and `_total.out`].
- Below side (10,763 readings): `x_P = (8m_P+1)/(8b)` with `b` the end of `W_k`, and `x_A = (8m_A−1)/(8a)` with `a` the start of the earlier window that gives A's facing end. The moved reading can block both windows at those laps only if `x_A < x_P`, that is `b/a < (8m_P+1)/(8m_A−1)`.
- Above side (858 readings): `x_P = (8m_P−1)/(8a)` at `W_k`'s start, `x_A = (8m_A+1)/(8b)` at an earlier window's end; both only if `a/b > (8m_P−1)/(8m_A+1)`.
- Checked in 11,621 of 11,621: both facing ends equal the formula, and at the member the inequality fails, so the reading is blocked (class X).
- So the block compares two numbers: a ratio of two window times, set by the frozen readings, and a ratio of two of the moved reading's lap edges.

**2. Pins and two readings** [T, exact; same artifact].
- In 2,531 readings both window times are zone edges of one reading (E951 item 4). The time ratio is then `(8u−1)/(8w+1)` below, a fixed number, and the block holds for every speed of the other readings while those windows keep those ends.
- In 9,090 readings the two window times are zone edges of two readings, `t_P = g_P / r_jP` and `t_A = g_A / r_jA` with `8g` an integer `≡ ±1 (mod 8)`: 9,090 of 9,090. The time ratio is `(g_P/g_A)·(r_jA/r_jP)`, so the block is a bound on one ratio of frozen readings.
- The closed cell's ratio graph (E951 item 1; least bounds by shortest paths, exact) bounds `r_jA/r_jP` past the threshold in 8,393 of 9,090 (7,724 below, 669 above). In those readings the path cell alone blocks the reading.
- **Rule 22 on the 697 readings the cell does not block.** (i) Feature: the cell's least bound on `r_jA/r_jP` does not reach the threshold, so the closed cell contains speeds at which the time-ratio inequality holds. (ii) Forced by the ratio graph: no chain of the path's zone memberships links `r_jA` and `r_jP` tightly enough. (iii) In each of their crossers another attaining reading is blocked (E951 item 2: 2,607 of 2,607). Whether these readings escape at cell points where the ratio crosses was not tested: **not understood** as to (iii) for the reading itself.

**3. What the blocking cell rows are.** Each edge of the ratio graph is one row of the path cell: at one state of the cascade path (setter `s`, lap end `t = c/r_s`), a reading `q` is in zone `m` or clear after it, which bounds `r_q / r_s`; or a max-exit choice between two readings in the way; or the order. A chain of these from `jP` to `jA` bounds `r_jA/r_jP`. So in the 625 cycle crossers, the block is: the path's own zone memberships fix the time order of two readings' zone edges closely enough that the moved reading cannot block both windows [T as item 2; PROVISIONAL: covering; the claim supported is that no speed of the moved reading blocks both `W_k` and the earlier window at laps `m_P` and `m_A` inside the closed cell]. The individual chains are not tabulated.

**Still not understood (rule 22), in order:**
- whether the 697 cell-free readings of item 2 escape at cell points (and whether E950 item 2's class-N witnesses are of this kind);
- the 5 open cells of E950 item 2;
- which earlier window gives A's facing end, as a rule (E942, E945; E950 item 5); window 1 gives it in 1,617 of 2,531 pin rows (E951 item 4) [OBS, a statistic of E340's member list];
- from E939: the single fast reading and the chain crossings below 11;
- from E938: the drop into window 1, the fall of `R*` with `H`, and the long paths near the AP.

Existence step named (rule 1): step 1, isolation proved at the AP/grid, is taken as proved, as the owner states. No displacement step is supplied.
**Consequence (M7) [T as counted; PROVISIONAL: covering]:**
- At the member, a reading is class X with identified ends exactly when one time ratio of the frozen readings' windows is at least one lap ratio of the moved reading. That gives a finite description per reading: the pair `(m_P, m_A)`, the two zone edges `(u, w)`, and the one or two readings that own them.
- Whether these descriptions form a finite list over all arrangements is not shown.
- Nothing is committed.
