#!/usr/bin/env python3
"""
twist_channel_types_v1.py

QUESTION: does the GLV/mu3 twist act on the MULTIPLICATIVE, ADDITIVE and
GEOMETRIC readouts by the same TYPE of operation?  Our difference-set batteries
put all three in one table under one shared "|M|/sqrt(pairs) ~ 1 random,
>>1 structured" normalization and one shared null.

PART A -- the type of the twist's action on each channel (exact).
PART B -- the actual per-channel null scale of the shared normalization.

Exact arithmetic in every verdict path: chi3 values in Z[w] as integer pairs;
sextant exact on integer Eisenstein coords; additive-sum vanishing decided by
the integer residue-count vector, never by a numeric evaluation.
Float appears only in the Part-B descriptive scale table.
"""
import random, sys
from collections import Counter

BTC = "/Users/trentpalelei/Desktop/Math Ex/btc_puzzle_investigation"
sys.path.insert(0, BTC)
from ecc_secp256k1 import P as FP, N_ORDER, scalar_mul
from int1_frame_operator_v1 import build

eis, eps = build(FP)
CB = (FP - 1) // 3

ZERO, ONE, W, W2 = (0, 0), (1, 0), (0, 1), (-1, -1)


def zadd(u, v):
    return (u[0] + v[0], u[1] + v[1])


def znorm(z):
    a, b = z
    return a * a - a * b + b * b


def chi3_exact(a):
    a %= FP
    if a == 0:
        return ZERO
    r = pow(a, CB, FP)
    if r == 1:
        return ONE
    return W if r < pow(r, 2, FP) else W2


def sextant(u, v):
    if u == 0 and v == 0:
        return 0
    for k in range(6):
        if v >= 0 and (u - v) >= 0 and u > 0:
            return k
        u, v = v, v - u
    return 0 if v >= 0 else 3


def add_affine(A, B):
    if A is None:
        return B
    if B is None:
        return A
    x1, y1 = A
    x2, y2 = B
    if x1 == x2:
        if (y1 + y2) % FP == 0:
            return None
        m = (3 * x1 * x1) * pow(2 * y1, -1, FP) % FP
    else:
        m = (y2 - y1) * pow(x2 - x1, -1, FP) % FP
    x3 = (m * m - x1 - x2) % FP
    return x3, (m * (x1 - x3) - y1) % FP


def neg(A):
    return (A[0], (-A[1]) % FP)


def beta_of_p():
    g = 3
    while pow(g, (FP - 1) // 3, FP) == 1:
        g += 1
    return pow(g, (FP - 1) // 3, FP)


# ===================================================== PART A
def part_a(beta, trials=400):
    print("=" * 78)
    print("PART A -- what TYPE of operation is the twist, per channel?")
    print("=" * 78)
    rng = random.Random(11)
    xs = [rng.randrange(1, FP) for _ in range(trials)]

    # --- A1 MULTIPLICATIVE: chi3(beta x) / chi3(x) -- is it a CONSTANT rotation?
    ratios = set()
    for x in xs:
        cx, cbx = chi3_exact(x), chi3_exact(beta * x % FP)
        # ratio in the group {1,w,w^2}: match cbx == cx * r
        for name, r in (("1", ONE), ("w", W), ("w^2", W2)):
            a, b = cx
            c, d = r
            prod = (a * c - b * d, a * d + b * c - b * d)
            if prod == cbx:
                ratios.add(name)
                break
    print(f"  A1 MULTIPLICATIVE  chi3(beta x)/chi3(x) over {trials} random x:")
    print(f"       distinct ratios observed = {sorted(ratios)}")
    print(f"       => acts on the VALUE by a FIXED rotation; a complete beta-orbit")
    print(f"          sums 1+w+w^2 = 0  ==>  EXACT ANNIHILATION")

    # --- A2 ADDITIVE: on a beta-closed set, F(b) vs F(w b) -- exact count vectors
    q = 1009  # small prime with an order-3 element, for an exact vanishing decision
    w3 = None
    for g in range(2, q):
        c = pow(g, (q - 1) // 3, q)
        if c != 1 and pow(c, 3, q) == 1:
            w3 = c
            break
    seen, orbs = set(), []
    for x in range(1, q):
        if x in seen:
            continue
        o = {x, w3 * x % q, w3 * w3 * x % q}
        seen |= o
        orbs.append(sorted(o))
    S = sorted({x for o in random.Random(5).sample(orbs, len(orbs) // 6) for x in o})

    def cvec(b):
        c = [0] * q
        for x in S:
            c[b * x % q] += 1
        return c

    eq = sum(1 for b in range(1, q) if cvec(b) == cvec(w3 * b % q))
    zeros = sum(1 for b in range(1, q) if len(set(cvec(b))) == 1)
    print(f"\n  A2 ADDITIVE  beta-closed S (|S|={len(S)}) in F_{q}:")
    print(f"       F(b) == F(w b):  {eq}/{q-1}      sums exactly zero: {zeros}/{q-1}")
    print(f"       => acts on the DUAL variable by PERMUTATION; magnitudes are")
    print(f"          EQUAL across the orbit  ==>  3x REDUNDANCY, never annihilation")

    # --- A3 GEOMETRIC: sextant shift under x -> beta x
    shifts = Counter()
    for x in xs:
        s0 = sextant(*eis(x))
        s1 = sextant(*eis(beta * x % FP))
        shifts[(s1 - s0) % 6] += 1
    top = shifts.most_common()
    print(f"\n  A3 GEOMETRIC  sextant(eis(beta x)) - sextant(eis(x)) mod 6, {trials} x:")
    print("       shift distribution: " +
          ", ".join(f"+{k}:{100*v//trials}%" for k, v in top))
    print(f"       => acts by a PARTIALLY FOLDED map (rhombus is 180deg-symmetric,")
    print(f"          not 120deg) ==> NO clean law: neither annihilates nor is redundant")


# ===================================================== PART B
def readouts(points, pairs):
    """The three shipped readouts, on one set of pairs."""
    cs = [0, 0]
    M3, M3xy = ZERO, ZERO
    cnt = 0

    def emul(z, v):
        a, b = z
        c, d = v
        return (a * c - b * d, a * d + b * c - b * d)

    for i, j in pairs:
        d = add_affine(points[i], neg(points[j]))
        if d is None:
            continue
        xd, yd = d
        c = emul(emul(eis(xd), eis(xd)), eis(xd))
        cs[0] += c[0]
        cs[1] += c[1]
        M3 = zadd(M3, chi3_exact(xd))
        M3xy = zadd(M3xy, chi3_exact(xd * yd % FP))
        cnt += 1
    s = cnt ** 0.5 if cnt else 1.0
    return (znorm(tuple(cs)) ** 0.5 / s, znorm(M3) ** 0.5 / s, znorm(M3xy) ** 0.5 / s)


def part_b(B=50, SZ=30):
    print("\n" + "=" * 78)
    print("PART B -- is the shared '~1 for random' normalization right per channel?")
    print("=" * 78)
    rng = random.Random(99)
    pairs = [(i, j) for i in range(SZ) for j in range(i + 1, SZ)]
    cols = {"eis_cube (additive/geom)": [], "M3 (multiplicative)": [],
            "M3xy (multiplicative)": []}
    keys = list(cols)
    for _ in range(B):
        pts = [scalar_mul(rng.randrange(1, N_ORDER)) for _ in range(SZ)]
        vals = readouts(pts, pairs)
        for k, v in zip(keys, vals):
            cols[k].append(v)

    print(f"  {B} random-curve sets, |S|={SZ}, {len(pairs)} pairs each")
    print(f"  {'channel':<26} {'null mean':>10} {'null sd':>9} {'max':>8}")
    for k in keys:
        v = cols[k]
        m = sum(v) / len(v)
        sd = (sum((t - m) ** 2 for t in v) / (len(v) - 1)) ** 0.5
        print(f"  {k:<26} {m:>10.3f} {sd:>9.3f} {max(v):>8.3f}")
    print("\n  READ: a shared '~1 random, >>1 structured' rule needs all three null")
    print("        means ~1 AND comparable sd. Different means/sd => the same")
    print("        threshold is a different number of sigma in each channel.")


if __name__ == "__main__":
    beta = beta_of_p()
    assert pow(beta, 3, FP) == 1 and beta != 1
    part_a(beta)
    part_b()
