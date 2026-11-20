# v3_word_seams7b_v2 -- E880 item 5's next step: the seam census generalized to any recorded best word.
# Computes the word's own extremal arrangement (per-reading least-product derivation chains to the pin,
# u_0 = 1 fixed), then: tight-row structure (spanning tree?), cycle census, uniqueness of the least-product
# chain for the LAST reading. Same row semantics as v3_word_seams7b_v1 (verified there against the B=34 word).
# Usage: python3 -I v3_word_seams7b_v2.py <name>   with WORDS[name] below. Exact Fractions throughout.
from fractions import Fraction as F
import sys

WORDS = {
  # B=34 record word (reach 4257/833; ends (rho_5? no: index 6 = rho_7, lap 16)); front (idx3, lap 1)
  "B34":  [(3,1),(2,1),(4,2),(1,1),(5,5),(3,2),(4,3),(5,6),(2,2),(5,7),(6,10),(4,4),(3,3),(1,2),(4,5),(2,3),(3,4),(6,15),(5,11),(4,6),(6,16)],
  # B=833/33 word (reach 231/47; ends idx4 lap 6 = rho_5); front (idx3, lap 1)
  "B833": [(3,1),(2,1),(4,2),(1,1),(5,5),(3,2),(4,3),(6,8),(5,6),(2,2),(5,7),(4,4),(3,3),(1,2),(4,5),(6,13),(2,3),(3,4),(4,6)],
  # B=25 word (reach 1863081/394289; ends idx3 lap 4 = rho_4); front (idx5, lap 3) = (rho_6, 3)
  "B25":  [(5,3),(3,1),(2,1),(6,5),(5,5),(1,1),(3,2),(4,4),(6,8),(5,8),(2,2),(4,5),(6,10),(5,10),(3,3),(5,11),(1,2),(2,3),(3,4)],
}

name = sys.argv[1] if len(sys.argv) > 1 else "B34"
WORD = WORDS[name]
B = F(34)

def rn(y): return f"rho{y+1}" if y > 0 else "rho1"

rows = []
for i in range(len(WORD)-1):
    (y1, j1), (y2, j2) = WORD[i], WORD[i+1]
    rows.append((y2, y1, F(8*j1+1, 8*j2-1), True, f"seam{i} up ({rn(y1)},{j1})->({rn(y2)},{j2})"))
    rows.append((y1, y2, F(8*j2+1, 8*j1+1), True, f"seam{i} lo ({rn(y1)},{j1})->({rn(y2)},{j2})"))
y0, j0 = WORD[0]
rows.append((y0, 0, F(1, 8*j0-1), True, f"front up ({rn(y0)},{j0}) contains 1"))
rows.append((0, y0, F(8*j0+1), True, f"front lo ({rn(y0)},{j0}) contains 1"))
for k in range(1, 6):
    rows.append((k+1, k, F(1), False, f"sorted u_{k+1}<=u_{k}"))
for k in range(1, 7):
    rows.append((0, k, B, False, f"face u_{k}>=1/{B}"))
rows.append((6, 0, F(1, 25), False, "region u_6<=1/25 (rho_7>=25)"))
rows.append((5, 0, F(1, 17), True,  "region u_5<1/17 (rho_6>17)"))

# extremal arrangement: per reading, the least-product chain to 0 (u_0 = 1 fixed).
ustar = {}
for y in range(1, 7):
    best = {y: (F(1), [])}
    for _ in range(8):
        ch = False
        for (p, q, c, st, tag) in rows:
            if p in best:
                v = best[p][0] * c
                if q not in best or v < best[q][0]:
                    best[q] = (v, best[p][1] + [(tag, str(c))]); ch = True
        if not ch: break
    ustar[y] = best.get(0)
ustar[0] = (F(1), [])

print(f"== word {name}: {len(WORD)} zones, front ({rn(WORD[0][0])},{WORD[0][1]}), last ({rn(WORD[-1][0])},{WORD[-1][1]}), rows {len(rows)}")
print("== extremal arrangement u* (least-product chains):")
for y in range(1, 7):
    b = ustar[y]
    print(f"   u*_{y} = {b[0]}   via: {' | '.join(t[0].split(' ')[0] for t in b[1])}")
last_exit = F(8*WORD[-1][1]+1) * ustar[WORD[-1][0]][0]
print(f"   last exit ({8*WORD[-1][1]+1}) * u*_{WORD[-1][0]} = {last_exit}")

tight, slack, viol = [], [], []
for (p, q, c, st, tag) in rows:
    s = c * ustar[q][0] - ustar[p][0]
    if s == 0: tight.append((tag, st))
    elif s < 0: viol.append((tag, s))
    else: slack.append((tag, s))
print(f"== tightness at u*: {len(tight)} tight, {len(slack)} slack, {len(viol)} VIOLATED (must be 0)")
for (t, st) in tight: print(f"   TIGHT({'strict' if st else 'nonstrict'}) {t}")
for (t, s) in viol[:6]: print(f"   VIOLATED {t} slack {s}")
if slack: print(f"   smallest positive slack: {min(s for (_, s) in slack)}")

# tight-edge graph: spanning tree over 0..6?
tedges = {}
for (p, q, c, st, tag) in rows:
    if ustar[q][0] * c == ustar[p][0]:
        tedges.setdefault(q, []).append((p, tag))  # derivation flows q -> p (u_p derived from u_q)
seen, stack = {0}, [0]
while stack:
    n = stack.pop()
    for (q, tag) in tedges.get(n, []):
        if q not in seen: seen.add(q); stack.append(q)
print(f"== tight-edge arborescence reachable from pin: {len(seen)} of 7 nodes {'(SPANNING TREE)' if len(seen)==7 else '(NOT spanning)'}")

# cycle census
adj = {}
for (p, q, c, st, tag) in rows:
    if p == 0 or q == 0: continue
    adj.setdefault(p, []).append((q, c, st, tag))
cycles = []
def dfs(start, node, prod, strict_any, path, visited):
    for (q, c, st, tag) in adj.get(node, []):
        if q == start: cycles.append((prod * c, strict_any or st, path + [tag]))
        elif q not in visited and q > start:
            dfs(start, q, prod * c, strict_any or st, path + [tag], visited | {q})
for s in range(1, 7):
    dfs(s, s, F(1), False, [], {s})
bad = [c for c in cycles if (c[0] <= 1 if c[1] else c[0] < 1)]
mn = min(cycles, key=lambda z: z[0]) if cycles else None
print(f"== cycles: {len(cycles)} simple; violations: {len(bad)}; min product: {mn[0] if mn else None}")

# uniqueness of the least-product chain for the LAST reading
ylast = WORD[-1][0]
tgt = ustar[ylast][0]
chains = []
def dfs2(node, prod, path, visited):
    for (p, q, c, st, tag) in rows:
        if p == node and q not in visited:
            np_ = prod * c
            if q == 0:
                if np_ == tgt: chains.append(path + [tag])
            else: dfs2(q, np_, path + [tag], visited | {q})
dfs2(ylast, F(1), [], {ylast})
print(f"== least-product chains for u_{ylast} achieving {tgt}: {len(chains)}")
for ch in chains: print("    *", " | ".join(x.split(' ')[0] for x in ch))
