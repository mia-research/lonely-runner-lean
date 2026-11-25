#!/usr/bin/env python3
"""m4_wide_triangle_box_v1 -- exact: where the triangle of m4_wide_triangle_v2 lies relative to each wide box.
Windows (reading pair, closing ratio): W1 lower 2 at 25, upper b at 31: open iff g_b/g_2 <= 31/25;
W2 lower 6 at 49, upper 2 at 15: open iff g_6/g_2 >= 49/15; W3 lower b at 33, upper 6 at 87: open iff g_6/g_b <= 29/11
(b = the reading with box value 5 or 6 in the profile's tally: 3, or 4 in (1,4,5,6,6,8,15)).  Each pair of the three
lines meets on a ray through the origin in (g_2, g_b, g_6); a vertex of the triangle is that ray.  Per box and vertex:
the interval of g_2 for which the ray lies inside the box faces (non-empty = the vertex is in the box), and which
window is open at the vertex (the third, by the cycle product 2697/2695 > 1, or none)."""
import json
from fractions import Fraction as F
from m4_fixedpoint_split_v1 import face
r1, r2, r3 = F(31, 25), F(49, 15), F(29, 11)       # g_b/g_2 at W1 closing, g_6/g_2 at W2 closing, g_6/g_b at W3 closing
verts = {"W1&W2": (r1, r2), "W1&W3": (r1, r1 * r3), "W2&W3": (r2 / r3, r2)}   # (g_b/g_2, g_6/g_2)
def open_at(x, y):   # x = g_b/g_2, y = g_6/g_2
    return {"W1": x <= r1, "W2": y >= r2, "W3": y / x <= r3}
for n, bs in (((1, 3, 4, 5, 6, 7, 13), (3,)), ((1, 3, 4, 5, 6, 7, 14), (3,)), ((1, 4, 5, 6, 6, 8, 15), (3, 4))):
    f = [face(v) for v in n]
    for b in bs:
        out = {}
        for name, (x, y) in verts.items():
            lo = max(f[2][0], f[b][0] / x, f[6][0] / y); hi = min(f[2][1], f[b][1] / x, f[6][1] / y)
            out[name] = {"g_b/g_2": str(x), "g_6/g_2": str(y), "g_2 interval in box": [str(lo), str(hi)] if lo <= hi else None,
                         "windows open at the vertex": [w for w, v in open_at(x, y).items() if v]}
        print(json.dumps({"n": list(n), "b": b, "vertices": out}))
