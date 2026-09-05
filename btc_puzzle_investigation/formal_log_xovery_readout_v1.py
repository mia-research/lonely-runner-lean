#!/usr/bin/env python3
"""
formal_log_xovery_readout_v1.py -- test the T = -x/y "formal logarithm" cheap readout.

THE PROPOSAL (user, 2026-07-17): T = -x/y is the local uniformizer at O; the formal group log is
L(T) = T + 3T^7 + (735/13)T^13 + ... (VERIFIED: = sum_k 7^k C(3k,k)/(6k+1) T^{6k+1}). Dropping
higher terms, L(T) ~ T, so d ~ T/T_G = (x y_G)/(y x_G) mod p is a cheap linear shadow of d.

THE THEORY PROBLEM (stated so the test is interpreted correctly, NOT to pre-empt it):
  L linearizes the FORMAL GROUP over Z_p = the kernel of reduction E_1(Q_p) (points reducing to
  O mod p, where T is divisible by p and the series CONVERGES p-adically). For P_d in E(F_p),
  T(P_d) is a generic element of F_p: no valuation, no convergence, and P -> -x/y is NOT a
  homomorphism. L([d]P) = d L(P) needs P in E_1(Q_p); getting [d]G there is the DLP
  (POSITIVE_FINDINGS_MASTER_v2 Part III, stated exactly this way).
  The construction DOES work when #E(F_p) = p (anomalous curve: lift, push into E_1, the formal
  log is then a genuine homomorphism -> d in linear time; Smart / Satoh-Araki / Semaev 1998).
  secp has #E = n != p (verified) -- which is why "anomalous" is a checked door in Part V.

WHY RUN IT ANYWAY: -x/y is a legitimate CHEAP JOINT (x,y) readout, and Part X.1 (the highest-value
open lead) asks precisely whether a cheap readout captures a FRACTION of the 0.93 joint alignment.
So this is a real Part-X.1 probe regardless of the formal-group framing.

PREDICTION (falsifiable, from KS): x/y has divisor with simple poles at the three 2-torsion points
(y=0; x != 0 there since x^3 = -7), and a simple zero at O => deg(x/y) = 3. So for additive psi,
KS Thm 1 + eq (3) gives |sum_P omega(P) psi(b * x/y)| <= 2*3*sqrt(p) = 6 sqrt(p) => the readout
e_p(b*x/y) sits at the sqrt(p) FLOOR. If it does NOT, KS is contradicted and that is the headline.

METRIC (matching the master / cheap_partial_shadow_v1):
    Corr_F(a) = (1/n) sum_d F(P_d) e_n(-a d) ;  C(F) = max_{a != 0} |Corr_F(a)| / ||F||_2
    floor = sqrt(ln n / n)  (the generic max-over-a scale) ; report C/floor.
Cheap readouts sit at ~1.2-1.5x floor; the planted aligned control grows with p.

Signal path exact (modular ints). Float only in the character-sum magnitude -- the analytic-size
carve-out named in btc_puzzle_investigation/CLAUDE.md -- and never as a threshold on data.
"""
import cmath, math, sys
from sympy import isprime

def curve_points_in_order(p):
    """Return G and the list [P_1..P_{n-1}] with P_d = [d]G, by repeated addition (no DLP needed:
    we ENUMERATE d -> P_d). Also returns n. Exact modular arithmetic."""
    def add(P, Q):
        if P is None: return Q
        if Q is None: return P
        x1, y1 = P; x2, y2 = Q
        if x1 == x2 and (y1 + y2) % p == 0: return None
        if P == Q: lam = (3 * x1 * x1) * pow(2 * y1, p - 2, p) % p
        else:      lam = (y2 - y1) * pow(x2 - x1, p - 2, p) % p
        x3 = (lam * lam - x1 - x2) % p
        return (x3, (lam * (x1 - x3) - y1) % p)
    # find a generator: any point of full order (n prime => every P != O works)
    G = None
    for x in range(p):
        rhs = ((x * x % p) * x + 7) % p
        if pow(rhs, (p - 1) // 2, p) != 1: continue
        y = pow(rhs, (p + 1) // 4, p) if p % 4 == 3 else None
        if y is None:
            for yy in range(p):
                if yy * yy % p == rhs: y = yy; break
        if y is not None and (y * y - rhs) % p == 0 and y != 0:
            G = (x, y); break
    if G is None: return None
    pts = []; P = G
    while P is not None:
        pts.append(P); P = add(P, G)
    n = len(pts) + 1
    return G, pts, n

def corr_over_floor(vals, n, label=None):
    """vals[d-1] = F(P_d), complex. Corr(a) = (1/n) sum_d F(P_d) e_n(-a d); return
    max_{a!=0}|Corr| / ||F||_2 / floor,  floor = sqrt(ln n / n)."""
    m = sum(vals) / len(vals)
    v = [z - m for z in vals]                       # center: a constant only feeds a=0
    nrm = math.sqrt(sum(abs(z) ** 2 for z in v) / len(v))
    if nrm == 0: return 0.0
    best = 0.0
    for a in range(1, n):
        s = 0j
        for d, z in enumerate(v, start=1):
            s += z * cmath.exp(-2j * math.pi * a * d / n)
        best = max(best, abs(s) / n)
    floor = math.sqrt(math.log(n) / n)
    return best / nrm / floor

def run(p, verbose=True):
    got = curve_points_in_order(p)
    if got is None: return None
    G, pts, n = got
    if not isprime(n): return None
    xG, yG = G
    inv = lambda t: pow(t, p - 2, p)
    ep = lambda t: cmath.exp(2j * math.pi * (t % p) / p)

    # the proposed readout: R_d = (x_d y_G) / (y_d x_G)  = T_d / T_G   (exact mod p)
    R = [(x * yG % p) * inv(y * xG % p) % p for (x, y) in pts]
    # the raw uniformizer T_d = -x_d/y_d (exact mod p)
    T = [(-x * inv(y)) % p for (x, y) in pts]

    out = {'p': p, 'n': n}
    # (a) the USER'S readout, raw value in F_p treated as an integer
    out['R_raw'] = corr_over_floor([complex(r) for r in R], n)
    # (b) additive character of it -- the object KS actually bounds (b=1)
    out['ep_R'] = corr_over_floor([ep(r) for r in R], n)
    # (c) additive character of the bare uniformizer T = -x/y
    out['ep_T'] = corr_over_floor([ep(t) for t in T], n)
    # (d) reference: e_p(xy), the best cheap readout on record (master: C/floor ~ 1.3)
    out['ep_xy'] = corr_over_floor([ep(x * y % p) for (x, y) in pts], n)
    # (e) PLANTED CONTROL -- must FIRE. F = e_n(a0 d) is the perfect aligned readout.
    a0 = 1
    out['PLANTED'] = corr_over_floor([cmath.exp(2j * math.pi * a0 * d / n)
                                      for d in range(1, n)], n)
    # (f) matched null: same readout, d -> P_d assignment destroyed
    import random
    rng = random.Random(p)
    sh = [ep(r) for r in R]; rng.shuffle(sh)
    out['R_shuffled'] = corr_over_floor(sh, n)
    return out

def main():
    ps = [int(a) for a in sys.argv[1:]] or [211, 433, 733, 1051, 1669, 2503]
    print("C/floor  (cheap readouts sit ~1.2-1.5 ; the PLANTED aligned control must grow with p)")
    print(f"{'p':>6} {'n':>6} | {'R_raw':>8} {'ep_R':>8} {'ep_T':>8} | {'ep_xy':>8} | "
          f"{'PLANTED':>9} {'R_shuf':>8}")
    for p in ps:
        if p % 6 != 1 or not isprime(p): continue
        r = run(p)
        if r is None:
            print(f"{p:>6}   -- n composite / no generator"); continue
        print(f"{r['p']:>6} {r['n']:>6} | {r['R_raw']:>8.3f} {r['ep_R']:>8.3f} {r['ep_T']:>8.3f} | "
              f"{r['ep_xy']:>8.3f} | {r['PLANTED']:>9.2f} {r['R_shuffled']:>8.3f}")

if __name__ == '__main__':
    main()
