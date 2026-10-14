"""transport_priority_claude_v2_reciprocal.py (2026-10-05). Second deliverable: for every x<e-restricted
counterexample found by transport_priority_claude_v2_search.py, compare reciprocal ratios e/x and x/e and
check whether each walker x, viewed as its OWN flank with e as one of ITS walkers, has a clear opening at
k=1 (the named clearance point of E398's first-lap rule). Blocked-at-k iff (8k+1)*a mod (8*b) outside [b,7b]
for flank b, walker a. Exact integers only.
"""
import math

def blocked(flank, walker, k):
    r = ((8 * k + 1) * walker) % (8 * flank)
    return r < flank or r > 7 * flank

witnesses = {
    8:  [1, 3, 4, 5, 7],
    10: [1, 2, 3, 5, 7],
    12: [1, 3, 4, 5, 7],
    14: [1, 2, 3, 5, 7],
    15: [2, 5, 7, 8, 12],
    16: [1, 3, 4, 5, 7],
    18: [1, 5, 6, 7, 9],
    20: [2, 3, 4, 7, 10],
    22: [3, 4, 7, 11, 20],
    24: [1, 5, 7, 11, 12],
}

lines = []
for e, xs in witnesses.items():
    lines.append("e=%d, walkers=%s" % (e, xs))
    for x in xs:
        if x == 1:
            lines.append("  x=1: own flank has only k=0, no k=1 to test; e/x=%d, x/e=1/%d" % (e, e))
            continue
        g = math.gcd(x, e)
        q = e // g
        p = x // g
        k1_blocked = blocked(x, e, 1)
        lines.append("  x=%-2d  e/x=%s  x/e=%s  (q=%d,p=%d)  e blocks x's own k=1 alone? %s"
                     % (x, "%d/%d" % (e, x), "%d/%d" % (x, e), q, p, k1_blocked))
    lines.append("")

out = "\n".join(lines)
with open("transport_priority_claude_v2_reciprocal.out", "w") as o:
    o.write(out + "\n")
print(out)
