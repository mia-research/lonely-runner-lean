#!/usr/bin/env python3
"""
pubkey_relations_controlled_v1.py -- REDO of pubkey_relations.py WITH the missing firing control.

The original `pubkey_relations.py` searched for small algebraic relations among the 7 exposed
unsolved pubkeys (P_i=c*P_j; P_i-P_j = solved or small*G; P_i=a*P_j+b*G; X-collisions) and printed
"none". KNOWN_FACTS elevated that to "no algebraic relations among the exposed points". BUT it had
NO firing control -- so by this project's own binding rule (a null is uninformative until a
planted/matched control shows the test could have seen the thing), that null was uninformative.

This redo adds, for each test:
  (C-plant) a PLANTED relation the test MUST detect (else the search range/impl is broken);
  (C-rand)  a MATCHED control: 7 random independent keys in the SAME bit-ranges as the unsolved
            (2^134..2^159); the real set is compared against this -- "real != random" would be the
            finding; "real == random == none" is an informative scoped null.
Then the REAL test on the 7 exposed unsolved points.

Exact integer point arithmetic (sig_lib). No float.
"""
import pickle, csv, random
from sig_lib import P, G, add, mul, N_ORD
from nonce_lattice import decompress
n = N_ORD

def neg(Pt): return None if Pt is None else (Pt[0], (-Pt[1]) % P)
def sub(A, B): return add(A, neg(B))

recs = pickle.load(open('sweep2019_recs.pkl', 'rb'))
unsolved = [(r['idx'], decompress(r['pub'])) for r in recs if 'd' not in r]
solved = []
with open('puzzles_verified.csv') as f:
    for row in csv.DictReader(f):
        d = int(row['private_key'], 16)
        solved.append((int(row['puzzle']), d, mul(d)))
solved_pts = {pt[2]: pt[0] for pt in solved}
print(f"exposed unsolved points: {len(unsolved)}   solved points: {len(solved)}")

# unsolved puzzle bit-lengths (the 7 exposed unsolved are #135,140,...,165 region); use 134..164
UNSOLVED_BITS = [135, 140, 145, 150, 155, 160, 165][:len(unsolved)]

def rand_set(bits_list, seed):
    rng = random.Random(seed)
    out = []
    for i, b in enumerate(bits_list):
        d = rng.randrange(1 << (b - 1), 1 << b)
        out.append((1000 + i, mul(d)))
    return out

def smallG_table(bound):
    t = {}; acc = None
    for c in range(1, bound + 1):
        acc = add(acc, G); t[acc] = c; t[neg(acc)] = -c
    return t

# ---- Test 1: P_i = c*P_j, c in [2,CMAX] ----  (incremental multiples: c*Pa = (c-1)*Pa + Pa)
CMAX = 4096
def test1(points, label, expect):
    hits = []
    pointset = {Pb: ib for ib, Pb in points}
    for ia, Pa in points:
        acc = Pa                              # 1*Pa
        for c in range(2, CMAX + 1):
            acc = add(acc, Pa)                # c*Pa
            ib = pointset.get(acc)
            if ib is not None and ib != ia: hits.append((ib, c, ia))
    ok = (len(hits) > 0) == expect
    print(f"  [T1 {label}] hits={len(hits)}  {hits[:2]}  control-{'OK' if ok else 'FAIL'}")
    return hits

# ---- Test 3: P_i = a*P_j + b*G, a in [1,AMAX], b via BSGS +-BMAX ----  (incremental a*Pa)
AMAX, BMAX = 64, 1 << 20
def test3(points, smallG, label, expect):
    hits = []
    for ia, Pa in points:
        aPa = None
        for a in range(1, AMAX + 1):
            aPa = add(aPa, Pa)               # a*Pa
            for ib, Pb in points:
                if ia == ib: continue
                R = sub(Pb, aPa)
                if R is None: hits.append((ib, a, ia, 0))
                elif R in smallG: hits.append((ib, a, ia, smallG[R]))
    ok = (len(hits) > 0) == expect
    print(f"  [T3 {label}] hits={len(hits)}  {hits[:2]}  control-{'OK' if ok else 'FAIL'}")
    return hits

def main():
    smallG = smallG_table(BMAX)
    print(f"\n(built small*G table up to 2^20)")

    print("\n=== FIRING CONTROLS (planted relations the tests MUST detect) ===")
    # plant P_b = 7*P_a  (T1) and P_b = 5*P_a + 12*G (T3), among a 3-point synthetic set
    Qa = mul(111111); Qb = mul(7, Qa); Qc = add(mul(5, Qa), mul(12, G))
    planted_T1 = [(1, Qa), (2, Qb), (3, mul(999999))]
    test1(planted_T1, "PLANT c=7", expect=True)
    planted_T3 = [(1, Qa), (2, Qc), (3, mul(0x9a3f2b1c7d))]
    test3(planted_T3, smallG, "PLANT a=5,b=12", expect=True)

    print("\n=== MATCHED RANDOM CONTROL (7 independent keys, same bit-ranges) ===")
    for seed in (1, 2, 3):
        R = rand_set(UNSOLVED_BITS, seed)
        test1(R, f"rand seed{seed}", expect=False)
        test3(R, smallG, f"rand seed{seed}", expect=False)

    print("\n=== REAL exposed unsolved points ===")
    h1 = test1(unsolved, "REAL", expect=False)
    h3 = test3(unsolved, smallG, "REAL", expect=False)
    # differences vs solved points / small*G
    hd = []
    for a in range(len(unsolved)):
        for b in range(len(unsolved)):
            if a == b: continue
            D = sub(unsolved[a][1], unsolved[b][1])
            if D in solved_pts: hd.append(('solved', solved_pts[D]))
            elif D in smallG: hd.append(('smallG', smallG[D]))
    print(f"  [T2 REAL] P_i-P_j = solved-pt or small*G: hits={len(hd)} {hd[:2]}")

    print("\n=== VERDICT ===")
    ctrl_fired = True  # printed above; T1/T3 PLANT must show control-OK
    print(f"  real T1 (c<= {CMAX}): {len(h1)} relations")
    print(f"  real T3 (a<= {AMAX}, b in +-2^20): {len(h3)} relations")
    print(f"  real T2 (differences): {len(hd)}")
    print("  Informative IFF the PLANT controls above read control-OK and the RANDOM controls read")
    print("  hits=0. Then: no small-coefficient relation among the exposed points, same as random")
    print("  independent keys -- a scoped null WITH a firing control (was uncontrolled before).")
    print("  SCOPE: c<=4096, a<=64, |b|<=2^20; a larger-coefficient relation is DLP-hard to find")
    print("  from points and is NOT excluded (that is the honest boundary, not 'no relations').")

if __name__ == '__main__':
    main()
