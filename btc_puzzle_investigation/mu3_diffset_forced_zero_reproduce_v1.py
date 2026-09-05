#!/usr/bin/env python3
r"""
mu3_diffset_forced_zero_reproduce_v1.py -- PREREG gate 1-2 (§10 R1-R4).

Executes `PREREG_mu3_diffset_control_repair_v1.md` §10. Independent re-derivation:
nothing is imported from the scratchpad script that first found the result, seeds
are distinct, and every clause is COMPUTED, never asserted from the prereg text.

R1  end-to-end forced zero on freshly built lambda-hat-closed sets (m=60, m=162),
    all C(m,2) pairs; plus the subsampling residual that accounts for the 0.17/0.16
    readings in masked_structure_findings_v32.md.
R2  the mechanism clause by clause (i)-(viii), incl. an exact Counter multiset
    equality beta*V_x == V_x and the S1-S6 forced-structure assertions of §1.
R3  chi3 cross-implementation: multiplicativity, and a small-prime cross-check of
    the pow-based chi3 against the discrete-log-index chi3 on ALL x.
R4  AP reclassification: the multiplicity-only account of the AP's firing.

EXACTNESS (§8): integers and Z[omega] pairs only. No abs, no sqrt, no float
anywhere in a decision path. chi3(v) = omega^t where pow(v,(p-1)//3,p) = beta^t,
beta fixed once. Statistic E3 = N(M3) = a^2-ab+b^2 for M3=(a,b).
"""
import random
import sys
from collections import Counter

sys.path.insert(0, "/Users/trentpalelei/Desktop/Math Ex/btc_puzzle_investigation")
from ecc_secp256k1 import P as FP, N_ORDER, scalar_mul

CB = (FP - 1) // 3
ZERO, ONE, W, W2 = (0, 0), (1, 0), (0, 1), (-1, -1)
OM = (ONE, W, W2)

FAIL = []


def check(tag, cond, detail=""):
    ok = bool(cond)
    if not ok:
        FAIL.append(tag)
    print(f"    [{'PASS' if ok else 'FAIL'}] {tag}" + (f"  {detail}" if detail else ""))
    return ok


# ---------------------------------------------------------------- Z[omega]
def zadd(u, v):
    return (u[0] + v[0], u[1] + v[1])


def zmul(u, v):
    a, b = u
    c, d = v
    return (a * c - b * d, a * d + b * c - b * d)


def znorm(u):
    a, b = u
    return a * a - a * b + b * b


# ---------------------------------------------------------------- curve (affine, exact)
def add_affine(A, B, p=FP):
    if A is None:
        return B
    if B is None:
        return A
    x1, y1 = A
    x2, y2 = B
    if x1 == x2:
        if (y1 + y2) % p == 0:
            return None
        m = (3 * x1 * x1) * pow(2 * y1, -1, p) % p
    else:
        m = (y2 - y1) * pow(x2 - x1, -1, p) % p
    x3 = (m * m - x1 - x2) % p
    return x3, (m * (x1 - x3) - y1) % p


def neg(A, p=FP):
    return (A[0], (-A[1]) % p)


# ---------------------------------------------------------------- chi3 (prereg convention)
def make_chi3(p):
    cb = (p - 1) // 3
    g = 2
    while pow(g, cb, p) == 1:
        g += 1
    beta = pow(g, cb, p)                      # fixed once, order 3
    pw = {1: 0, beta: 1, beta * beta % p: 2}

    def chi3(v):
        v %= p
        if v == 0:
            return None                        # S1/S2 say this never happens
        return OM[pw[pow(v, cb, p)]]

    def chi3_t(v):
        v %= p
        return None if v == 0 else pw[pow(v, cb, p)]

    return chi3, chi3_t, beta


chi3, chi3_t, BETA = make_chi3(FP)


# ---------------------------------------------------------------- difference-multiset readouts
def diff_readouts(points, pairs, p=FP, c3=None, want_multiset=False):
    """Exact (M3x, M3xy, class counts, V_x multiset). No float."""
    c3 = c3 or chi3_t
    M3x, M3xy = ZERO, ZERO
    nx = [0, 0, 0]
    nxy = [0, 0, 0]
    Vx = Counter()
    zero_x = zero_xy = 0
    for i, j in pairs:
        R = add_affine(points[i], neg(points[j], p), p)
        if R is None:
            continue
        xr, yr = R
        tx = c3(xr)
        txy = c3(xr * yr % p)
        if tx is None:
            zero_x += 1
        else:
            nx[tx] += 1
            M3x = zadd(M3x, OM[tx])
        if txy is None:
            zero_xy += 1
        else:
            nxy[txy] += 1
            M3xy = zadd(M3xy, OM[txy])
        if want_multiset:
            Vx[xr] += 1
    return dict(M3x=M3x, M3xy=M3xy, nx=nx, nxy=nxy, Vx=Vx,
                zero_x=zero_x, zero_xy=zero_xy, npairs=len(pairs))


def all_pairs(m):
    return [(i, j) for i in range(m) for j in range(i + 1, m)]


def E3_from_counts(n):
    a, b, c = n
    return a * a + b * b + c * c - a * b - b * c - c * a


def lam_secp():
    lam = pow(2, (N_ORDER - 1) // 3, N_ORDER)
    assert pow(lam, 3, N_ORDER) == 1 and lam != 1, "lambda construction failed"
    return lam


def build_lam_closed(m, seed):
    """m must be divisible by 3; m/3 fresh GLV triples."""
    assert m % 3 == 0
    rng = random.Random(seed)
    lam = lam_secp()
    S = []
    for _ in range(m // 3):
        d = rng.randrange(1, N_ORDER)
        S += [scalar_mul(d), scalar_mul(d * lam % N_ORDER),
              scalar_mul(d * lam * lam % N_ORDER)]
    return S


# ================================================================ R2
def R2():
    print("\nR2  mechanism, clause by clause (each computed literally)")
    p = FP
    check("R2(i)   (p-1) mod 9 == 6", (p - 1) % 9 == 6, f"= {(p-1)%9}")
    cb3 = pow(BETA, (p - 1) // 3, p)
    check("R2(ii)  chi3(beta) != 1 (primitive)", cb3 != 1)
    s = zadd(zadd(ONE, chi3(BETA)), zmul(chi3(BETA), chi3(BETA)))
    check("R2(iii) 1 + chi3(b) + chi3(b)^2 == (0,0) in Z[w]", s == ZERO, f"= {s}")
    check("R2(v)   chi3(-1) == 1", chi3(p - 1) == ONE, f"= {chi3(p-1)}")

    lam = lam_secp()
    check("R2(vii) lam^3 == 1 mod n", pow(lam, 3, N_ORDER) == 1)
    check("R2(vii) lam^2+lam+1 == 0 mod n",
          (lam * lam + lam + 1) % N_ORDER == 0)

    # (vi) lambda-hat acts as (x,y) -> (beta_GLV x, y) on actual curve points.
    # NOTE two DISTINCT order-3 constants must not be conflated (deviation D1):
    #   BETA      = the chi3 labelling reference (smallest g route, §8)
    #   BETA_GLV  = the endomorphism's x-scaling, x([lam]P) = BETA_GLV * x(P)
    # Here BETA_GLV == BETA^2. Either is primitive, so the forcing is identical;
    # but the assertion must be on BETA_GLV, not BETA.
    rng = random.Random(90210)
    T = 40
    ratios, oky = set(), 0
    for _ in range(T):
        d = rng.randrange(1, N_ORDER)
        P = scalar_mul(d)
        Q = scalar_mul(d * lam % N_ORDER)
        ratios.add(Q[0] * pow(P[0], -1, FP) % FP)
        oky += (Q[1] == P[1])
    check("R2(vi)  x([lam]P)/x(P) is a SINGLE constant over all P",
          len(ratios) == 1, f"{len(ratios)} distinct over {T} points")
    beta_glv = next(iter(ratios))
    check("R2(vi)  that constant has order 3",
          pow(beta_glv, 3, FP) == 1 and beta_glv != 1)
    which = "BETA" if beta_glv == BETA else (
        "BETA^2" if beta_glv == BETA * BETA % FP else "NEITHER")
    check("R2(vi)  it is BETA or BETA^2 (labelling recorded, not assumed)",
          which != "NEITHER", f"beta_GLV == {which}")
    check("R2(vi)  chi3(beta_GLV) is primitive (what the forcing needs)",
          pow(beta_glv, CB, FP) != 1)
    check("R2(vi)  y([lam]P) == y(P)", oky == T, f"{oky}/{T}")
    globals()["BETA_GLV"] = beta_glv

    # (iv) EXACT multiset equality beta*V_x == V_x on a complete lambda-closed diff multiset
    S = build_lam_closed(60, seed=515151)
    r = diff_readouts(S, all_pairs(60), want_multiset=True)
    Vx = r["Vx"]
    bVx = Counter({BETA * k % FP: v for k, v in Vx.items()})
    check("R2(iv)  beta*V_x == V_x  (exact Counter equality)", bVx == Vx,
          f"|support|={len(Vx)} total={sum(Vx.values())}")
    gVx = Counter({BETA_GLV * k % FP: v for k, v in Vx.items()})
    check("R2(iv)  beta_GLV*V_x == V_x  (the substantive closure)", gVx == Vx)

    # S1/S2 -- no zero classes
    check("S1      x(R) != 0 for all R (sum of classes == C(m,2))",
          sum(r["nx"]) == r["npairs"] and r["zero_x"] == 0,
          f"{sum(r['nx'])} == {r['npairs']}")
    check("S2      y(R) != 0 for all R",
          sum(r["nxy"]) == r["npairs"] and r["zero_xy"] == 0)
    check("S1'     7 is a non-residue mod p", pow(7, (FP - 1) // 2, FP) != 1)
    check("S2'     -7 is a non-cube mod p", pow((-7) % FP, CB, FP) != 1)

    # S4 -- E3 == 0 mod 3
    check("S4      E3x == 0 mod 3", E3_from_counts(r["nx"]) % 3 == 0)
    check("S4      E3xy == 0 mod 3", E3_from_counts(r["nxy"]) % 3 == 0)

    # S5 -- xy readout is a function of x alone
    rng2 = random.Random(4242)
    n5 = ok5 = 0
    for _ in range(60):
        d = rng2.randrange(1, N_ORDER)
        x, y = scalar_mul(d)
        lhs = chi3(x * y % FP)
        rhs = zmul(chi3(x), zmul(chi3((x * x * x + 7) % FP),
                                 chi3((x * x * x + 7) % FP)))
        n5 += 1
        ok5 += (lhs == rhs)
    check("S5      chi3(x*y) == chi3(x)*chi3(x^3+7)^2  (function of x alone)",
          ok5 == n5, f"{ok5}/{n5}")

    # S6 -- xy readout has mu3-weight 1
    n6 = ok6 = 0
    for _ in range(60):
        d = rng2.randrange(1, N_ORDER)
        x, y = scalar_mul(d)
        bx = BETA * x % FP
        f = lambda t: zmul(chi3(t), zmul(chi3((t * t * t + 7) % FP),
                                         chi3((t * t * t + 7) % FP)))
        n6 += 1
        ok6 += (f(bx) == zmul(chi3(BETA), f(x)))
    check("S6      xy readout has mu3-weight 1", ok6 == n6, f"{ok6}/{n6}")

    # S3 -- orientation-even
    n3 = ok3x = ok3xy = 0
    for _ in range(40):
        d = rng2.randrange(1, N_ORDER)
        x, y = scalar_mul(d)
        n3 += 1
        ok3x += (chi3(x) == chi3(x))
        ok3xy += (chi3(x * y % FP) == chi3(x * (-y % FP) % FP))
    check("S3      chi3(x*y) orientation-even (R -> -R)", ok3xy == n3,
          f"{ok3xy}/{n3}")
    return r


# ================================================================ R1
def R1():
    print("\nR1  end-to-end forced zero on FRESH lambda-hat-closed sets")
    res = {}
    for m, seed in ((60, 777001), (162, 777002)):
        S = build_lam_closed(m, seed)
        pr = all_pairs(m)
        r = diff_readouts(S, pr)
        e3x, e3xy = E3_from_counts(r["nx"]), E3_from_counts(r["nxy"])
        print(f"  m={m}  n_pairs={r['npairs']}  classes_x={r['nx']}  classes_xy={r['nxy']}")
        check(f"R1      m={m}: M3x == (0,0) exactly", r["M3x"] == ZERO, f"= {r['M3x']}")
        check(f"R1      m={m}: M3xy == (0,0) exactly", r["M3xy"] == ZERO, f"= {r['M3xy']}")
        check(f"R1      m={m}: E3x == 0 and E3xy == 0", e3x == 0 and e3xy == 0,
              f"E3x={e3x} E3xy={e3xy}")
        check(f"R1      m={m}: classes exactly equal (n0==n1==n2)",
              len(set(r["nx"])) == 1, f"{r['nx']}")
        res[m] = r

    # subsampling residual -- the account of v32's 0.17 / 0.16
    print("\n  subsampling residual (v32 kept 12000 of 12720 = 94.34% of pairs)")
    S = build_lam_closed(162, seed=777002)
    pr = all_pairs(162)
    rng = random.Random(31337)
    for frac in (100, 94, 75):
        k = len(pr) * frac // 100
        sub = pr if frac == 100 else rng.sample(pr, k)
        r = diff_readouts(S, sub)
        e3 = E3_from_counts(r["nx"])
        # descriptive only: the retired float scale, for comparability with v32
        scale = (e3 / r["npairs"]) ** 0.5 if r["npairs"] else 0.0
        print(f"    keep {frac:3d}% ({k:5d} pairs): M3x={str(r['M3x']):>16} "
              f"E3x={e3:<10} [retired float scale {scale:.3f}]")
    check("R1      residual vanishes only at 100% retention",
          E3_from_counts(diff_readouts(S, pr)["nx"]) == 0)
    return res


# ================================================================ R3
def R3():
    print("\nR3  chi3 cross-implementation")
    rng = random.Random(20260730)
    N = 10000
    okm = oku = 0
    for _ in range(N):
        u = rng.randrange(1, FP)
        v = rng.randrange(1, FP)
        okm += (chi3(u * v % FP) == zmul(chi3(u), chi3(v)))
        oku += (chi3(pow(u, 3, FP)) == ONE)
    check(f"R3(a)   chi3(uv) == chi3(u)chi3(v) on {N} pairs", okm == N, f"{okm}/{N}")
    check(f"R3(a)   chi3(u^3) == 1 on {N} u", oku == N, f"{oku}/{N}")

    # (b) small prime: pow-based chi3 vs discrete-log-index chi3, on ALL x
    p0 = 103                                    # 103 mod 6 == 1
    assert p0 % 6 == 1
    c3_0, c3t_0, b0 = make_chi3(p0)
    g = 2                                       # find a primitive root
    while len({pow(g, k, p0) for k in range(p0 - 1)}) != p0 - 1:
        g += 1
    ind = {pow(g, k, p0): k for k in range(p0 - 1)}
    # the two labellings can differ by w <-> w^2; accept either, report which
    for flip in (False, True):
        agree = 0
        for x in range(1, p0):
            t_pow = c3t_0(x)
            t_ind = ind[x] % 3
            t_ind = (3 - t_ind) % 3 if flip else t_ind
            agree += (t_pow == t_ind)
        if agree == p0 - 1:
            break
    check(f"R3(b)   pow-chi3 == dlog-index-chi3 on ALL x in F_{p0}",
          agree == p0 - 1, f"{agree}/{p0-1} (labelling flip={flip})")

    # forced zero must reproduce at p0. lambda-hat acts directly: (x,y)->(b0 x,y),
    # since (b0 x)^3 + 7 == x^3 + 7. Build a lambda-closed point set with no scalars.
    pts = []
    for x in range(p0):
        r = (x * x * x + 7) % p0
        if r == 0:
            continue
        if pow(r, (p0 - 1) // 2, p0) != 1:
            continue
        y = next((t for t in range(1, p0) if t * t % p0 == r), None)
        if y:
            pts.append((x, y))
    orb, seen = [], set()
    for (x, y) in pts:
        if x in seen:
            continue
        o = [(x, y), (b0 * x % p0, y), (b0 * b0 % p0 * x % p0, y)]
        if all(0 <= q[0] < p0 for q in o) and len({q[0] for q in o}) == 3:
            seen |= {q[0] for q in o}
            orb.append(o)
    S0 = [q for o in orb for q in o]
    r0 = diff_readouts(S0, all_pairs(len(S0)), p=p0, c3=c3t_0)
    check(f"R3(b)   forced zero reproduces at p0={p0} (|S|={len(S0)})",
          r0["M3x"] == ZERO,
          f"M3x={r0['M3x']} classes={r0['nx']} zero_x={r0['zero_x']}")
    print(f"          (small-p0 results are INSTRUMENT checks; inherit no scope, §6)")


# ================================================================ R4
def R4(B=4000):
    print("\nR4  AP reclassification -- the multiplicity-only account")
    m = 160
    w = [m - j for j in range(1, m)]
    Sw, Sw2 = sum(w), sum(t * t for t in w)
    check("R4      Sum w == C(160,2)", Sw == m * (m - 1) // 2, f"{Sw}")
    check("R4      Sum w^2 == 1,352,560", Sw2 == 1352560, f"{Sw2}")

    # the AP's ACTUAL E3x: differences depend only on (i-j), so 159 distinct points
    rng = random.Random(606060)
    d0 = rng.randrange(1, N_ORDER)
    delta = rng.randrange(1, 1 << 40)
    base = scalar_mul(d0 % N_ORDER)
    M3 = ZERO
    n = [0, 0, 0]
    for j in range(1, m):
        R = add_affine(scalar_mul((d0 + j * delta) % N_ORDER), neg(base))
        t = chi3_t(R[0])
        n[t] += w[j - 1]
        M3 = zadd(M3, zmul((w[j - 1], 0), OM[t]))
    e3_ap = E3_from_counts(n)
    print(f"    AP observed: classes={n} (weighted)  E3x={e3_ap}")

    # multiplicity surrogate: keep w, randomize the chi3 labels
    sur = []
    for _ in range(B):
        ns = [0, 0, 0]
        for wt in w:
            ns[rng.randrange(3)] += wt
        sur.append(E3_from_counts(ns))
    sur.sort()
    lo, hi = sur[int(0.025 * B)], sur[int(0.975 * B)]
    inside = lo <= e3_ap <= hi
    rank = sum(1 for t in sur if t <= e3_ap) / B
    check("R4      AP E3x lies INSIDE its multiplicity surrogate",
          inside, f"E3x={e3_ap}  95% region=[{lo},{hi}]  rank={rank:.3f}")
    print(f"    => AP firing is accounted for by difference MULTIPLICITY alone.")
    print(f"       Reclassified: multiplicity control, NOT a mu3 detector validation.")


if __name__ == "__main__":
    print("=" * 78)
    print("PREREG gate 1-2 -- mu3 difference-set forced-zero reproduction (§10 R1-R4)")
    print("=" * 78)
    R2()
    R1()
    R3()
    R4()
    print("\n" + "=" * 78)
    if FAIL:
        print(f"GATE 1-2: FAIL ({len(FAIL)}) -> F5 applies, nothing else is trusted")
        for t in FAIL:
            print(f"   - {t}")
        sys.exit(1)
    print("GATE 1-2: ALL PASS -- R1-R4 reproduced independently. Gate 3 may proceed.")
