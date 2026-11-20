# v3_word_seams7b_v1 -- E877 item 7b: the seams of the 21-zone best word (B=34), and the cycle census.
# Readings are indices 0..6 (0 = pinned rho_1 = 1; index k = rho_{k+1}). u = 1/rho, u_0 = 1.
# Word (from v3_reach_v1_B34.out, the sup_exit = 4257/833 word):
WORD = [(3,1),(2,1),(4,2),(1,1),(5,5),(3,2),(4,3),(5,6),(2,2),(5,7),(6,10),(4,4),(3,3),(1,2),(4,5),(2,3),(3,4),(6,15),(5,11),(4,6),(6,16)]
# Row semantics (from v3_reach_v1.py / d0 base_system): u_p <= c*u_q. Per consecutive zone pair the search adds
#   add(y_new, y_cur, exit_i_num/(entry_{i+1}_num)) : the new zone CONTAINS the current state:
#       (8 j_{i+1} - 1) u_{i+1} < (8 j_i + 1) u_i                       (upper row on u_{i+1})
#   add(y_cur, y_new, exit_{i+1}_num/(exit_i_num))     : the new zone's exit strictly advances:
#       (8 j_i + 1) u_i < (8 j_{i+1} + 1) u_{i+1}                        (lower row on u_{i+1})
# First zone (y0,j0) contains R=1: (8j0-1)u_{y0} < 1 < (8j0+1)u_{y0}.
# System rows: sorted u_{k+1} <= u_k (k=1..5), faces u_k <= 1/B... wait faces: rho <= B means u >= 1/B (row (k,0,1/B)); rho_7 >= 25: u_6 <= 1/25; rho_6 > 17: u_5 < 1/17.
# Checks (all exact Fractions):
#   (2) slackness at the extremal arrangement u* (E877 item 6) -- which rows are TIGHT there;
#   (3) cycle census over ALL rows: every cycle's product must be > 1 if the cycle uses a strict row, else >= 1;
#   (4) the least-product bound on u_6 (rho_7) to node 0 and the number of distinct least-product chains.
from fractions import Fraction as F

WORD = [(3,1),(2,1),(4,2),(1,1),(5,5),(3,2),(4,3),(5,6),(2,2),(5,7),(6,10),(4,4),(3,3),(1,2),(4,5),(2,3),(3,4),(6,15),(5,11),(4,6),(6,16)]
USTAR = [F(1), F(5,21), F(7,39), F(1,7), F(2673,25823), F(5,91), F(33,833)]  # u*_0..u*_6
B = F(34)

def rn(y): return f"rho{y+1}" if y > 0 else "rho1"

rows = []  # (p, q, c, strict, tag)
for i in range(len(WORD)-1):
    (y1, j1), (y2, j2) = WORD[i], WORD[i+1]
    rows.append((y2, y1, F(8*j1+1, 8*j2-1), True, f"seam{i} up: ({rn(y1)},{j1})->({rn(y2)},{j2}): {8*j2-1}u_{{{y2}}} < {8*j1+1}u_{{{y1}}}"))
    rows.append((y1, y2, F(8*j2+1, 8*j1+1), True, f"seam{i} lo: ({rn(y1)},{j1})->({rn(y2)},{j2}): {8*j1+1}u_{{{y1}}} < {8*j2+1}u_{{{y2}}}"))
y0, j0 = WORD[0]
rows.append((y0, 0, F(1, 8*j0-1), True, f"front: ({rn(y0)},{j0}) contains 1, entry side: u_{{{y0}}} < 1/{8*j0-1}"))
rows.append((0, y0, F(8*j0+1), True, f"front: ({rn(y0)},{j0}) contains 1, exit side: 1 < {8*j0+1}u_{{{y0}}}"))
for k in range(1, 6):
    rows.append((k+1, k, F(1), False, f"sorted: u_{{{k+1}}} <= u_{{{k}}}"))
for k in range(1, 7):
    rows.append((0, k, B, False, f"face: u_{{{k}}} >= 1/{B} (rho_{k+1} <= B)"))
rows.append((6, 0, F(1, 25), False, "region: u_{6} <= 1/25 (rho_7 >= 25)"))
rows.append((5, 0, F(1, 17), True,  "region: u_{5} < 1/17 (rho_6 > 17)"))

print(f"rows total: {len(rows)}")

print("== (2) slackness at u* (E877 item 6 extremal arrangement):")
tight, slack = [], []
for (p, q, c, st, tag) in rows:
    s = c * USTAR[q] - USTAR[p]
    (tight if s == 0 else slack).append((tag, p, q, c, s, st))
for (tag, p, q, c, s, st) in tight:
    kind = "TIGHT(strict)" if st else "TIGHT(slack-ok)"
    print(f"  {kind:14s} {tag}")
print(f"  ({len(tight)} tight, {len(slack)} slack, of {len(rows)})")
viol = [(t, s) for (t, p, q, c, s, st) in slack if s < 0]
print(f"  rows VIOLATED at u* (must be 0 if u* is the true extremum): {len(viol)}")
for (t, s) in viol[:8]: print("   VIOLATED:", t, "slack", s)
mins = min((s for (t, p, q, c, s, st) in slack if s > 0), default=None)
print(f"  smallest positive slack: {mins}")

# (3) cycle census. Edges p->q with weight c (u_p <= c*u_q). A cycle visiting nodes with product P and
# at least one strict row forces P > 1; all-non-strict cycles force P >= 1.
adj = {}
for (p, q, c, st, tag) in rows:
    if p == 0 or q == 0: continue
    adj.setdefault(p, []).append((q, c, st, tag))

cycles = []
def dfs(start, node, prod, strict_any, path, visited):
    for (q, c, st, tag) in adj.get(node, []):
        if q == start:
            cycles.append((prod * c, strict_any or st, path + [tag]))
        elif q not in visited and q > start:
            dfs(start, q, prod * c, strict_any or st, path + [tag], visited | {q})
for s in range(1, 7):
    dfs(s, s, F(1), False, [], {s})
bad = [c for c in cycles if (c[0] <= 1 if c[1] else c[0] < 1)]
print(f"== (3) cycles: {len(cycles)} simple cycles; violations (product too small): {len(bad)}")
if bad:
    for pr, sa, path in bad[:12]: print("  VIOLATION product", pr, "strict" if sa else "nonstrict")
    for pr, sa, path in bad[:1]: print("   path:", " | ".join(path))
else:
    mn = min(cycles, key=lambda z: z[0])
    print(f"  minimal cycle product: {mn[0]} ({'with strict row' if mn[1] else 'all non-strict'})")
    print("  via:", " | ".join(mn[2]))
    prods = sorted(set(c[0] for c in cycles))[:6]
    print("  smallest six distinct products:", [str(p) for p in prods])

# (4) least-product bound on u_6 from ALL rows (relaxation on edges p->q, start at 6, target 0).
best = {6: (F(1), [])}
for _ in range(8):
    ch = False
    for (p, q, c, st, tag) in rows:
        if p in best:
            v = best[p][0] * c
            if q not in best or v < best[q][0]:
                best[q] = (v, best[p][1] + [(tag, str(c))]); ch = True
    if not ch: break
print("== (4) least-product bound u_6 -> 0:", best.get(0)[0] if 0 in best else None)
if 0 in best:
    for t in best[0][1]: print("   ", t[0], "factor", t[1])
    print("   129 * bound =", F(129) * best[0][0], " (4257/833 expected)")
    # distinct simple least-product chains 6 -> 0 (visited set; product exactly the bound)
    tgt = best[0][0]
    chains = []
    def dfs2(node, prod, path, visited):
        for (p, q, c, st, tag) in rows:
            if p == node and q not in visited:
                np_ = prod * c
                if q == 0:
                    if np_ == tgt: chains.append(path + [tag])
                else:
                    dfs2(q, np_, path + [tag], visited | {q})
    dfs2(6, F(1), [], {6})
    print(f"   distinct simple least-product chains achieving {tgt}: {len(chains)}")
    for ch in chains:
        print("    *", " | ".join(x.split(':')[0] for x in ch))
