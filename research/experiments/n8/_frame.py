"""Frame guard.  Import this in any n=8 script that builds an arrangement.

Register item 12 is a STANDING BAN: never pin a runner at 0.  The conjecture is eight distinct
POSITIVE speeds.  On 2026-09-18 that ban was violated twice in one session -- once caught by the
owner in the slot analysis and withdrawn into MANUSCRIPT_v10 Appendix B.10, and then again in
three scripts written AFTER the withdrawal and after the cheat sheet recording it.

Instruction-based correction has a measured track record of ~0 on this project (CLAUDE.md sec2b).
So this is a decidable artifact instead of a reminder: it raises, it does not warn.

    from _frame import speeds, arrangements
    v = speeds(rng.sample(range(1, 90), 8))      # raises on 0, duplicates, negatives
    for v in arrangements(range(1, 25), 8): ...  # enumerates legal arrangements only
"""
from itertools import combinations

class FrameError(AssertionError):
    pass

def speeds(v):
    """Return v as a sorted tuple of 8 distinct positive speeds, or raise."""
    v = tuple(sorted(v))
    if len(v) != 8:
        raise FrameError(f"an arrangement has 8 runners, got {len(v)}")
    if len(set(v)) != 8:
        raise FrameError(f"speeds must be distinct: {v}")
    for x in v:
        if x <= 0:
            raise FrameError(
                f"speed {x} is not positive -- register item 12, no stationary runner. "
                f"If you meant a subject-centred disparity set, name it `ds`, not `v`.")
    return v

def arrangements(pool, k=8):
    """Enumerate legal arrangements from pool (which must contain no non-positive value)."""
    pool = list(pool)
    bad = [x for x in pool if x <= 0]
    if bad:
        raise FrameError(f"pool contains non-positive speeds {bad[:5]} -- start at 1, not 0")
    for c in combinations(pool, k):
        yield c

def disparities(v, i):
    """The subject's seven disparities.  Takes an ARRANGEMENT and an index, never a raw list,
    so a disparity set is never mistaken for a speed list."""
    v = speeds(v)
    return sorted(abs(v[j] - v[i]) for j in range(len(v)) if j != i)
