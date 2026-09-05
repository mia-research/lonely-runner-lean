"""GAP 2 — algebraic relations among the exposed pubkeys (POINTS, not scalars).
The 7 unsolved-key points (#135..) + the 82 solved points. Cheap exact checks
no scalar test could do: P_i = c*P_j, P_i - P_j = small*G or a solved point,
P_i = a*P_j + b*G for small a,b (baby-step search). Exact integer point ops."""
import pickle, csv
from sig_lib import P, G, add, mul, N_ORD
from nonce_lattice import decompress
n = N_ORD

def neg(Pt): return None if Pt is None else (Pt[0], (-Pt[1]) % P)
def sub(A, B): return add(A, neg(B))

# exposed unsolved pubkeys (from 2019 sweep)
pubs = pickle.load(open('sweep2019_pubs.pkl', 'rb'))
recs = pickle.load(open('sweep2019_recs.pkl', 'rb'))
unsolved = [(r['idx'], r['pub'], decompress(r['pub'])) for r in recs if 'd' not in r]

# solved points (know d)
solved = []
with open('puzzles_verified.csv') as f:
    for row in csv.DictReader(f):
        d = int(row['private_key'], 16)
        solved.append((int(row['puzzle']), d, mul(d)))
solved_pts = {pt[2]: pt[0] for pt in solved}
solved_x = {pt[2][0]: pt[0] for pt in solved}

print(f"unsolved exposed points: {len(unsolved)}   solved points: {len(solved)}")

print("\n=== 1. small-multiple: P_i = c * P_j  (c up to 4096) among exposed pubkeys ===")
hit = False
for c in range(2, 4097):
    for ia, _, Pa in unsolved:
        cPa = mul(c, Pa)
        for ib, _, Pb in unsolved:
            if ia == ib: continue
            if cPa == Pb:
                print(f"  HIT: P(in{ib}) = {c} * P(in{ia})"); hit = True
if not hit: print("  none")

print("\n=== 2. P_i - P_j equals a solved point, or +-small*G (c up to 2^20) ===")
smallG = {}
acc = None
for c in range(1, 1 << 20):
    acc = add(acc, G); smallG[acc] = c
    smallG[neg(acc)] = -c
hit = False
pts = [(i, p) for i, _, p in unsolved]
for a in range(len(pts)):
    for b in range(len(pts)):
        if a == b: continue
        D = sub(pts[a][1], pts[b][1])
        if D in solved_pts:
            print(f"  HIT: P(in{pts[a][0]}) - P(in{pts[b][0]}) = solved #{solved_pts[D]}"); hit = True
        if D in smallG:
            print(f"  HIT: P(in{pts[a][0]}) - P(in{pts[b][0]}) = {smallG[D]}*G"); hit = True
if not hit: print("  none (differences are not small nor solved points)")

print("\n=== 3. P_i = a*P_j + b*G, small a (<=64), b via BSGS in +-2^20 ===")
hit = False
for a in range(1, 65):
    for ia, _, Pa in unsolved:
        aPa = mul(a, Pa)
        for ib, _, Pb in unsolved:
            if ia == ib: continue
            R = sub(Pb, aPa)
            if R is None:
                print(f"  HIT: P(in{ib}) = {a}*P(in{ia})"); hit = True
            elif R in smallG:
                print(f"  HIT: P(in{ib}) = {a}*P(in{ia}) + {smallG[R]}*G"); hit = True
if not hit: print("  none")

print("\n=== 4. any exposed point's X collide with a solved point's X (weak-key)? ===")
hit = False
for i, _, p in unsolved:
    if p[0] in solved_x:
        print(f"  HIT in{i} shares X with solved #{solved_x[p[0]]}"); hit = True
if not hit: print("  none")
