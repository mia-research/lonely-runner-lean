# DEVIATIONS — PREREG_anew_supersingularity_reaudit_v3.md

**2026-08-02.** Two deviations, both recorded after the run, neither affecting an adjudication.

## D1 — the named separability-exclusion list was range-specific and was not restated for the v3 sample

v2 §3 fixed the exclusion list by name:
`{(7,x³+7), (7,x³+2x+5), (11,x³+11), (31,x³+x+1), (101,x³+2x+5)}`.
v3 §1 replaced the prime sample but **did not restate the list**, so the script carried the stale
one. The exclusion actually hit on the v3 sample was **`(239, x³−x+3)`**, which is not on it
(`anew_cartier_audit_v2.log`, last lines).

**Assessment: letter violated, substance intact.** The substantive pre-committed rule is *"pairs with
`disc(f) ≡ 0 mod p` are excluded as not instances of the object"* — a property of the object, applied
uniformly by the code **before** any result is read. The specific pair is determined a priori:
`disc(x³−x+3) = −239` (executed: `sage -c` output in this session), so `p = 239` is the unique prime
at which that cubic is inseparable, fixed by the cubic and independent of any outcome.

**No post-hoc filtering occurred.** Correct handling for v4: derive the exclusion list from the
sample rather than copying it.

## D2 — the distinct-class count required by v2 §4 was under-implemented in the run script

v2 §4 `[G:M-6]` pre-committed that the `[VERIFIED, N]` shadow report **distinct cover-isomorphism
classes**, not raw `(p,f)` rows. `anew_cartier_audit_v2.sage` computed the collapse only for the
three curated `x³+B` cubics, not across the full 12-cubic set.

Completed after the run by `anew_distinct_classes_v1.sage` / `.log`, using the identical canonical
labelling:

```
MAIN     rows = 311   distinct cover-isomorphism classes = 287   (collapse 24)
CONTROL  rows = 288   distinct cover-isomorphism classes = 279   (collapse  9)
```

**This is completion of a pre-committed reporting requirement, not a post-hoc statistic**: the
requirement, the labelling rule and the direction of the correction were all fixed before the run,
and the correction can only *reduce* `N`. All reported counts use **287 / 279**, not 311 / 288.
