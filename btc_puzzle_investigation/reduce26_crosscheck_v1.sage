#!/usr/bin/env sage
"""reduce26_crosscheck_v1.sage -- verify the convolution identity (#26) holds AND cross-check the
P^1 character-sum reduction. The A1 self-test already certified f[d]=h2[d]-(h1*h1)[d]=0 for d!=0.
This script: (1) re-verifies the convolution identity at p=43, (2) computes the rational/conjugate
pair sums for several R, (3) computes sum_t chi_2(gF) independently, and reconciles the three.
If sum_t chi_2(gF) != 0 but the convolution identity holds, the reduction's claimed EQUIVALENCE has
a gap (not #26)."""
from sage.all import GF, EllipticCurve, ZZ
import audit_n1_vsign_v2_core as core


def chi2(a, p):
    a = int(a) % p
    if a == 0: return 0
    return 1 if pow(a, (p-1)//2, p) == 1 else -1


if __name__ == "__main__":
    p, A, B = 43, 0, 7
    Fp = GF(p); Fp2 = GF(p**2, 'a')
    E = EllipticCurve(Fp, [A, B]); n = E.order()
    G = next(P for P in E if P.order() == n)
    print("p=%d n=%d  E:y^2=x^3+%d" % (p, n, B))

    # (1) convolution identity (#26) via the V2-V1^2 form (A1 route)
    dl = core.dlog_table(p, n); h1 = core.hist_k1(p, n, dl); h2 = core.hist_k2(p, n, dl)
    conv = core.polymul_mod_cyc(h1, h1, n)
    fZ = [h2[d] - conv[d] for d in range(n)]
    off0 = fZ[1:]
    const_ok = len(set(off0)) == 1
    c = off0[0] if off0 else 0
    eps = core.legendre(-1, p)
    measured = fZ[0] - c
    print("(1) convolution identity: const_off_zero=%s c=%d  V2-V1^2=%d target=%d  HOLDS=%s"
          % (const_ok, c, measured, -2*eps*p, const_ok and measured == -2*eps*p))

    # (2) for several R: rational-sum and conjugate-sum of chi_2(y1 y2)
    print("\n(2) pair sums by R, and (3) sum_t chi_2(gF):")
    for e in (1, 2, 3, 5, 7):
        R = e*G
        if R.is_zero(): continue
        E2 = E.change_ring(Fp2); R2 = E2(R[0], R[1])
        seen = set(); sr = sc = 0; nr = nc = 0
        # also collect the t->cgF table for sum_t chi_2(gF)
        ttable = {}   # t (as F_p int) -> cgF  (but careful: which t coordinate?)
        xR, yR = ZZ(R[0]), ZZ(R[1])
        for x1 in Fp2:
            rhs = x1**3 + A*x1 + B
            if not rhs.is_square(): continue
            y1 = rhs.sqrt()
            for sg in (1, -1):
                P1 = E2(x1, sg*y1); P2 = R2 - P1
                if P1.is_zero() or P2.is_zero(): continue
                inFp = (P1[0] in Fp) and (P1[1] in Fp)
                Pf = E2(P1[0]**p, P1[1]**p)
                is_conj = (Pf == P2) and not inFp
                is_rat = inFp and ((R2 - P1)[0] in Fp)
                if not (is_conj or is_rat): continue
                key = frozenset((tuple(P1), tuple(P2)))
                if key in seen: continue
                seen.add(key)
                py = P1[1]*P2[1]
                if py != py**p: continue
                cF = chi2(py, p)
                cg = 1 if is_rat else -1
                if is_rat: sr += cF; nr += 1
                else: sc += cF; nc += 1
                # the t-coordinate x1 + x(R-P1):
                if x1 == xR: continue
                xRmP = ((yR + P1[1])/(xR - P1[0]))**2 - P1[0] - xR   # x(R-P1)
                t = P1[0] + xRmP
                if t in Fp:
                    ttable[int(t)] = (cg, cF)
        sum_gF = sum(cg*cF for (cg,cF) in ttable.values())
        print("  R=[%d]G: rat(%d,sum=%d) conj(%d,sum=%d) diff=%d  | sum_t chi_2(gF) over %d t-values = %d"
              % (e, nr, sr, nc, sc, sr-sc, len(ttable), sum_gF))
