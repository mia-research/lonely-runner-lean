"""Probe -- EMPIRICAL lead, not a result (2026-09-24).
Region M = c-1 (exactly one disparity not divisible by n), c = n-1, all such sets in [1,H].
When the lone non-multiple x fails as a flank (the case R5 does not discharge), which flank
works?  Shapes fixed in advance: largest disparity; some multiple of n; smallest multiple."""
from itertools import combinations


def fw(n, ds, e):
    for j in range(e):
        a = n * j + 1
        if all(e <= (d * a) % (n * e) <= (n - 1) * e for d in ds):
            return j
    return None


for n, H in [(4, 40), (5, 50), (6, 48), (7, 56), (8, 64)]:
    fails = lg = anym = smallm = xsmall = 0
    ex = []
    mults = list(range(n, H + 1, n))
    for x in range(1, H + 1):
        if x % n == 0:
            continue
        for ms in combinations(mults, n - 2):
            c = tuple(sorted((x,) + ms))
            if fw(n, c, x) is not None:
                continue
            fails += 1
            xsmall += x < n
            lg += fw(n, c, max(c)) is not None
            if any(fw(n, c, m) is not None for m in ms):
                anym += 1
            else:
                ex.append(c)
            smallm += fw(n, c, min(ms)) is not None
    print(f"n={n} H={H}: lone-flank failures={fails}; x<n: {xsmall}; largest works {lg}; "
          f"some multiple works {anym}; smallest multiple works {smallm}; no multiple works: {ex[:5]}")
