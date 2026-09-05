#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
c2_grouplaw_diffset_curve_v1.py -- executes frozen PREREG_chi2_diffset_characterization_v1.md.

Runs the IDENTICAL band-difference χ2 lean-check on any short-Weierstrass curve, to test whether the
reproduced secp256k1 χ2 difference-set structure is secp-SPECIFIC (a=0/j=0/μ6 CM) or GENERIC.
Primary control = P-256 (a=-3, no μ6). The verdict is read mechanically against PREREG §4 (frozen).

Exact-integer signal path; arm regenerated fresh per seed; pool fixed (P>=10M). C-GLV (μ6 forced-zero)
runs only where the curve has β (secp); elsewhere the 3 plants + fresh-vs-pool are the instrument gate.
Usage: python3 c2_grouplaw_diffset_curve_v1.py {secp|p256} [M] [P] [Rnull] [seed]
"""
import sys, time, bisect, random

CURVES = {
    "secp": dict(
        p=0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F, a=0, b=7,
        Gx=0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798,
        Gy=0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8,
        n=0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141,
        beta=0x7AE96A2B657C07106E64479EAC3434E99CF0497512F58995C1396C28719501EE),
    "p256": dict(
        p=0xFFFFFFFF00000001000000000000000000000000FFFFFFFFFFFFFFFFFFFFFFFF, a=-3,
        b=0x5AC635D8AA3A93E7B3EBBD55769886BC651D06B0CC53B0F63BCE3C3E27D2604B,
        Gx=0x6B17D1F2E12C4247F8BCE6E563A440F277037D812DEB33A0F4A13945D898C296,
        Gy=0x4FE342E2FE1A7F9B8EE7EB4A7C0F9E162BCE33576B315ECECBB6406837BF51F5,
        n=0xFFFFFFFF00000000FFFFFFFFFFFFFFFFBCE6FAADA7179E84F3B9CAC2FC632551,
        beta=None),
}


class Curve:
    def __init__(self, name):
        c = CURVES[name]
        self.name = name
        self.p = c["p"]; self.a = c["a"] % c["p"]; self.b = c["b"] % c["p"]
        self.G = (c["Gx"], c["Gy"]); self.n = c["n"]; self.beta = c["beta"]
        assert self.p % 4 == 3, "sqrt exponent needs p==3 mod 4"
        self.e2 = (self.p - 1) // 2
        self.has3 = (self.p % 3 == 1)
        self.e3 = (self.p - 1) // 3 if self.has3 else None
        self.sqrtexp = (self.p + 1) // 4
        # cube-root labels
        if self.has3:
            W = next(t for z in range(2, 100) if (t := pow(z, self.e3, self.p)) != 1)
            self.cube = {1: 0, W: 1, (W * W) % self.p: 2}
        # on-curve check for G
        Gx, Gy = self.G
        assert (Gy * Gy - (Gx ** 3 + self.a * Gx + self.b)) % self.p == 0, "G not on curve"

    def add(self, P, Q):
        if P is None: return Q
        if Q is None: return P
        x1, y1 = P; x2, y2 = Q; p = self.p
        if x1 == x2:
            if (y1 + y2) % p == 0: return None
            lam = (3 * x1 * x1 + self.a) % p * pow(2 * y1 % p, -1, p) % p
        else:
            lam = (y2 - y1) % p * pow((x2 - x1) % p, -1, p) % p
        x3 = (lam * lam - x1 - x2) % p
        return (x3, (lam * (x1 - x3) - y1) % p)

    def mul(self, k, P):
        R = None; Q = P
        while k:
            if k & 1: R = self.add(R, Q)
            Q = self.add(Q, Q); k >>= 1
        return R

    def rand_point(self, rng):
        p = self.p
        while True:
            x = rng.randrange(1, p)
            rhs = (x * x % p * x + self.a * x + self.b) % p
            if rhs == 0 or pow(rhs, self.e2, p) != 1: continue
            y = pow(rhs, self.sqrtexp, p)
            return (x, p - y if rng.getrandbits(1) else y)

    def code(self, x):
        b = 0 if pow(x % self.p, self.e2, self.p) == 1 else 1
        c = self.cube[pow(x % self.p, self.e3, self.p)] if self.has3 else 0
        return 3 * b + c

    def gl_diff_code(self, Pi, Pj):
        xj, yj = Pj
        D = self.add(Pi, (xj, (self.p - yj) % self.p))
        return None if D is None else self.code(D[0])


NAMES = ("E2", "E3", "E6")


def stats3(H):
    nb0 = H[0] + H[1] + H[2]; nb1 = H[3] + H[4] + H[5]
    E2 = (nb0 - nb1) ** 2
    nc0 = H[0] + H[3]; nc1 = H[1] + H[4]; nc2 = H[2] + H[5]
    A3 = nc0 - nc2; B3 = nc1 - nc2; E3 = A3 * A3 - A3 * B3 + B3 * B3
    nm = [H[0], H[5], H[1], H[3], H[2], H[4]]
    A6 = nm[0] - nm[2] - nm[3] + nm[5]; B6 = nm[1] + nm[2] - nm[4] - nm[5]
    E6 = A6 * A6 + A6 * B6 + B6 * B6
    return E2, E3, E6


def diffset_hist(cur, pts):
    H = [0] * 6
    for i in range(len(pts)):
        Pi = pts[i]
        for j in range(i + 1, len(pts)):
            c = cur.gl_diff_code(Pi, pts[j])
            if c is not None: H[c] += 1
    return H


def hist_e2(T, m):
    nb0 = T // 2 + m; nb1 = T - nb0
    H = [nb0 // 3] * 3 + [nb1 // 3] * 3
    for r in range(nb0 - 3 * (nb0 // 3)): H[r] += 1
    for r in range(nb1 - 3 * (nb1 // 3)): H[3 + r] += 1
    return H


def hist_e3(T, m):
    nc0 = T // 3 + m; nc1 = (T - nc0) // 2; nc2 = T - nc0 - nc1
    H = [0] * 6
    for nc, cells in ((nc0, (0, 3)), (nc1, (1, 4)), (nc2, (2, 5))):
        H[cells[0]] = nc // 2; H[cells[1]] = nc - nc // 2
    return H


def hist_e6(T, m):
    h0 = T // 6 + m; rest = T - h0; e = rest // 5
    H = [h0] + [e] * 5
    for r in range(rest - 5 * e): H[1 + r] += 1
    return H


def p_upper(nl, v):
    return (len(nl) - bisect.bisect_left(nl, v)) / len(nl)


def main():
    name = sys.argv[1] if len(sys.argv) > 1 else "secp"
    M = int(sys.argv[2]) if len(sys.argv) > 2 else 400
    P = int(sys.argv[3]) if len(sys.argv) > 3 else 4000
    Rnull = int(sys.argv[4]) if len(sys.argv) > 4 else 2000
    seed = int(sys.argv[5]) if len(sys.argv) > 5 else 20260802
    KS = [40, 64, 96, 128, 160, 200]; T = M * (M - 1) // 2
    cur = Curve(name); rng = random.Random(seed)
    print("=" * 80)
    print(f"C2 DIFFSET χ2 on curve={name} (a={cur.a if cur.a<10 else 'p-3'}, has_chi3={cur.has3}, "
          f"mu6={cur.beta is not None})  M={M} P={P} seed={seed}")
    print(f"  inflation T^2/C(P,2)={T*T/(P*(P-1)//2)/T*100:.2f}%")
    print("=" * 80)
    t0 = time.perf_counter()
    tp = time.perf_counter()
    pool = [cur.rand_point(rng) for _ in range(P)]
    code = [[0] * P for _ in range(P)]
    for i in range(P):
        Pi = pool[i]
        for j in range(i + 1, P):
            c = cur.gl_diff_code(Pi, pool[j]); code[i][j] = c if c is not None else -1
    print(f"[pool] {P} pts, C(P,2) gl-diff codes in {time.perf_counter()-tp:.0f}s")

    def null_draw():
        idx = rng.sample(range(P), M); idx.sort(); H = [0] * 6
        for a in range(M):
            row = code[idx[a]]
            for bb in range(a + 1, M):
                cd = row[idx[bb]]
                if cd >= 0: H[cd] += 1
        return stats3(H)
    null = {nm: [] for nm in NAMES}
    for _ in range(Rnull):
        for nm, v in zip(NAMES, null_draw()): null[nm].append(v)
    for nm in NAMES: null[nm].sort()
    v99 = {nm: null[nm][(99 * Rnull) // 100] for nm in NAMES}
    print(f"[null] {Rnull} draws | 99th " + " ".join(f"{nm}={v99[nm]}" for nm in NAMES))

    # fresh-vs-pool (E2 primary gate)
    fresh = {nm: [] for nm in NAMES}
    for _ in range(60):
        pts = [cur.rand_point(rng) for _ in range(M)]
        for nm, v in zip(NAMES, stats3(diffset_hist(cur, pts))): fresh[nm].append(v)
    fp = {nm: sum(1 - p_upper(null[nm], v) for v in fresh[nm]) / 60 for nm in NAMES}
    fp_ok = 0.42 <= fp["E2"] <= 0.58
    print(f"[fresh-vs-pool] " + " ".join(f"{nm}={fp[nm]:.3f}" for nm in NAMES)
          + f"  -> E2 {'PASS' if fp_ok else 'FAIL (enlarge P)'}")
    assert fp_ok, "fresh-vs-pool E2 FAIL"

    # plants (instrument gate for the primary — must fire on this curve)
    plant_ok = True
    print("[plants] fire own channel above 99th (E2 is the primary instrument gate):")
    for ch, builder in (("E2", hist_e2), ("E3", hist_e3), ("E6", hist_e6)):
        e2, e3, e6 = stats3(builder(T, int(0.05 * T)))
        val = {"E2": e2, "E3": e3, "E6": e6}[ch]; fired = val > v99[ch]
        print(f"    {ch}-plant f=0.05: {ch}={val} {'FIRES' if fired else 'DEAD'}  (E6={e6})")
        if ch == "E2" and not fired: plant_ok = False
    assert plant_ok, "E2 plant DEAD on this curve -- instrument invalid"

    # C-GLV only where mu6 exists
    if cur.beta is not None:
        S = []
        for _ in range(max(1, M // 3)):
            x, y = cur.rand_point(rng)
            S += [(x, y), ((cur.beta * x) % cur.p, y), ((cur.beta * cur.beta * x) % cur.p, y)]
        eg = stats3(diffset_hist(cur, S))
        print(f"[C-GLV] phi-closed E3={eg[1]} E6={eg[2]} -> {'PASS' if eg[1]==0 and eg[2]==0 else 'FAIL'}")
    else:
        print("[C-GLV] N/A (no μ6 on this curve) -- plants+fresh-vs-pool are the instrument gate")

    # arms + lean-check (the §4 decision variable is E2 mean arm pctile)
    allp = {nm: [] for nm in NAMES}
    for k in KS:
        for sd in range(5):
            arng = random.Random((seed ^ (k * 0x9E3779B1)) + sd)
            pts = [cur.mul(arng.randrange(1 << (k - 1), 1 << k), cur.G) for _ in range(M)]
            for nm, v in zip(NAMES, stats3(diffset_hist(cur, pts))):
                allp[nm].append(p_upper(null[nm], v))
    print("=" * 80)
    print(f"[VERDICT INPUT] χ2/E2 mean arm pctile (§4 decision variable) for seed {seed}:")
    for nm in NAMES:
        mp = sum(1 - p for p in allp[nm]) / len(allp[nm])
        lo = sum(1 for p in allp[nm] if p >= 0.90); hi = sum(1 for p in allp[nm] if p <= 0.10)
        flag = "LEAN" if not (0.44 <= mp <= 0.56) else "flat"
        print(f"    {nm}: mean pctile={mp:.3f} [{flag}]  low10%={lo}/30 high10%={hi}/30")
    print(f"  -> map this seed's E2 mean pctile against PREREG §4 (θ=0.57; both seeds needed).")
    print(f"TOTAL WALL TIME: {time.perf_counter()-t0:.0f}s")


if __name__ == "__main__":
    main()
