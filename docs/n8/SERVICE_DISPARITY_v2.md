# Service disparity — all eight runners displaced in turn

2026-09-12. Supersedes `SERVICE_DISPARITY_v1.md`, which covered r1 and r2 only. n = 8,
individual isolation, threshold 1/8, base AP `(1,…,8)`.

Each runner in turn is transited across its neighbour interval (step 0.1, 19 positions) with the
others held at AP positions. The clock runs to the **coverage time** — the first moment every
runner has been lonely at least once — and each runner's isolations are counted up to it.

Artifact: `experiments/n8/ok_service_disparity_v1.py`.
Data: `experiments/n8/out_service_disparity_v1.csv` (152 configurations).

---

## 1. The disparity, all eight movers  `[VERIFIED — exact]`

| mover | positions at 1 : 1 | fair band around the AP | band width | worst ratio | at |
|---|---|---|---|---|---|
| **r1** | 3 | `1 .. 1` | **0.0** | 10 | 1.9 |
| **r2** | 2 | `2 .. 2.1` | 0.1 | 11 | 1.1 |
| **r3** | 5 | `2.9 .. 3.3` | 0.4 | 9 | 2.1 |
| **r4** | 7 | `3.8 .. 4.4` | **0.6** | 9 | 3.1 |
| **r5** | 7 | `4.6 .. 5.2` | **0.6** | 9 | 4.1 |
| **r6** | 5 | `5.7 .. 6.1` | 0.4 | 9 | 5.1 |
| **r7** | 2 | `6.9 .. 7` | 0.1 | 11 | 7.9 |
| **r8** | 3 | `8 .. 8` | **0.0** | 10 | 7.1 |

The band widths read `0.0, 0.1, 0.4, 0.6, 0.6, 0.4, 0.1, 0.0` — symmetric about the centre of the
pack. The worst ratios read `10, 11, 9, 9, 9, 9, 11, 10`, symmetric likewise.

**The middle runners can be displaced furthest before service becomes unequal; the end runners
cannot be displaced at all.** r4 and r5 tolerate `±0.3`; r1 and r8 tolerate nothing — one step
off the AP in either direction and some runner is being served two or three times while another
waits.

This is the end-runner asymmetry again, on a fourth observable. r1 and r8 were the zero-reserve
runners, the zero-duration runners, the only ones that can be *improved*, and now the only ones
with no fair band at all.

## 2. Two invariants across all 152 configurations  `[VERIFIED — exact]`

**The minimum tally is always 1.** In every configuration some runner is served exactly once
while the clock runs. The disparity is therefore always `max : 1` — the question is only how
large the maximum grows.

**Simultaneous service happens in exactly 8 of the 152 configurations**, and those eight are the
AP rows — the position where the mover sits at its own AP speed, i.e. the AP itself, reached
eight times over. Every other configuration has one or two runners served last, never all eight.

Ratios over the 152: minimum 1, median 3, maximum 11.

## 3. Who is served last

The last-served runner is always the mover, the neighbour it is approaching, or both — never a
runner elsewhere in the pack. This matches `DISTURBANCE_RULE_v1` §2 exactly, and has the same
cause: loneliness needs both adjacent gaps `≥ 1/8`, a gap is shared, so closing one costs
precisely the pair bordering it.

The worst ratios sit at the ends of each interval, where the mover is within 0.1 of a neighbour,
and are the `t ≥ 1/(8g)` bound rather than anything new.

## 4. Status and scope

`[VERIFIED — exact]` §1's table; §2's two invariants; §3's last-served pattern.
`[PROVED — arithmetic]` the `t ≥ 1/(8g)` bound behind the worst ratios.

**Scope.** One base, the AP. One runner displaced at a time — no pair is displaced together.
Step 0.1, so only `q ∈ {1,2,5,10}`; a finer step would sample inside the fair bands and could
narrow them. The band widths are therefore upper bounds at this resolution, not measured edges.

**Not established.** Why the band widths are `0, 0.1, 0.4, 0.6` and symmetric; whether they
survive a finer step; whether the pattern holds on a non-AP base; what happens when two runners
are displaced at once.

**n = 8 is not proved here, and is not the target here.**
