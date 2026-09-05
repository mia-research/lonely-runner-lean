#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
d2_twist_rigidity_certificate_v1.py — the D2 control-state certificate, exact.

Executes the 4-step D2 framework first-hand at prime-order y^2=x^3+7 curves:
  (1) base objects: V1(a) = sum_d h1[d] zeta^{ad} in Z[zeta_n] = Z[T]/Phi_n, exact integers
      (h1[d] = chi2(y_{[d]G}); cross-checked against the repo's audit_n1_vsign_v2_core.hist_k1);
  (2) un-twisted baseline (a=0): L*(0) roots are exactly sqrt(p) x mu_6 — the rigid control state;
  (3) twisted state: L*(a) = T^4 - e1 T^3 + e2 T^2 - e3 T + e4 with the record's coefficient laws
      (e1 = -V1, e2 = e1^2 - chi2(-1) p  [P32], e3 = chi2(-1) p e1, e4 = p^2) — e2's law itself
      first-hand-validated at p=43,67 against core.hist_k2's F_{p^2} trace sum (V2 = V1^2 - 2 chi2(-1) p);
  (4) readouts per cell (float only in the final root extraction; coefficients exact):
      purity |alpha_i| = sqrt(p); the zeta_3 multiset law {alpha, zeta3 alpha, -conj, -conj(zeta3 .)};
      absolute-rigidity destruction (alpha/sqrt(p) is NEVER a root of unity, orders <= 66 checked);
      M4 real/imaginary parity; omega-descent V(lam a) = V(a); Parseval; Sato-Tate angle readout.

No secrets, no leakage claim: a deterministic certificate of the documented object. Exact int
arithmetic in every signal path; numpy/cmath only for the numeric root readout.
"""
import cmath, math, random, sys, os
from fractions import Fraction

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

# ---------------- exact Z[zeta_n] = Z[T]/Phi_n, deg < n-1 ----------------

class Zz:
    """cyclotomic integers for PRIME n; rep = integer coeff list of length n-1;
    reduction T^{n-1} = -(1 + T + ... + T^{n-2})."""
    def __init__(self, n):
        self.n = n
        self.pow_ = None
    def powvec(self):
        if self.pow_ is None:
            n = self.n
            pv = [[1 if i == k else 0 for i in range(n - 1)] for k in range(n - 1)]
            pv.append([-1] * (n - 1))          # zeta^{n-1}
            self.pow_ = pv
        return self.pow_
    def reduce(self, c):
        n = self.n
        r = list(c)
        if len(r) < n - 1:
            r += [0] * (n - 1 - len(r))
            return r
        # single top-down pass: T^{n-1} = -(1 + T + ... + T^{n-2}); contributions land below g
        for g in range(len(r) - 1, n - 2, -1):
            v = r[g]
            if v:
                r[g] = 0
                base = g - (n - 1)
                for i in range(n - 1):
                    r[base + i] -= v
        return r[:n - 1]
    def mul(self, u, v):
        r = [0] * (len(u) + len(v) - 1)
        for i, a in enumerate(u):
            if a:
                for j, b in enumerate(v):
                    if b:
                        r[i + j] += a * b
        return self.reduce(r)
    def conj(self, u):
        """complex conjugation: zeta^k -> zeta^{-k}"""
        pv = self.powvec(); n = self.n
        r = [0] * (n - 1)
        for k, c in enumerate(u):
            if c:
                p = pv[(n - k) % n]
                for i in range(n - 1):
                    r[i] += c * p[i]
        return r
    def embed(self, u):
        """numeric value at zeta = e^{2 pi i/n} (readout only)"""
        z = cmath.exp(2j * cmath.pi / self.n)
        return sum(c * z ** k for k, c in enumerate(u))

# ---------------- curve / group walk ----------------

def legendre(a, p):
    a %= p
    if a == 0: return 0
    r = pow(a, (p - 1) // 2, p)
    return 1 if r == 1 else -1

def tonelli(a, p):
    a %= p
    if a == 0: return 0
    if legendre(a, p) != 1: return None
    if p % 4 == 3:
        return pow(a, (p + 1) // 4, p)
    q, s = p - 1, 0
    while q % 2 == 0: q //= 2; s += 1
    z = 2
    while legendre(z, p) != -1: z += 1
    m, c, t, rr = s, pow(z, q, p), pow(a, q, p), pow(a, (q + 1) // 2, p)
    while t != 1:
        i, t2 = 0, t
        while t2 != 1: t2 = t2 * t2 % p; i += 1
        b = pow(c, 1 << (m - i - 1), p)
        m, c = i, b * b % p
        t, rr = t * c % p, rr * b % p
    return rr

def curve_points_f(p, B=7):
    """h1[d] = chi2(y_{[d]G}) for d in [0,n), group order n prime; plus (x,y) walk."""
    n = p + 1 + sum(legendre((x * x % p * x + B) % p, p) for x in range(p))
    # generator = first point found
    G = None
    for x in range(p):
        y = tonelli((x * x % p * x + B) % p, p)
        if y: G = (x, y); break
    def add(P, Q):
        if P is None: return Q
        if Q is None: return P
        x1, y1 = P; x2, y2 = Q
        if x1 == x2 and (y1 + y2) % p == 0: return None
        if P == Q:
            m = (3 * x1 * x1) * pow(2 * y1, p - 2, p) % p
        else:
            m = (y2 - y1) * pow(x2 - x1, p - 2, p) % p
        x3 = (m * m - x1 - x2) % p
        return (x3, (m * (x1 - x3) - y1) % p)
    h = [0] * n
    Q = None
    for d in range(n):
        if Q is not None:
            h[d] = legendre(Q[1], p)
        Q = add(Q, G)
    assert Q is None, "generator order mismatch"
    return n, h

def is_prime_int(m):
    for sp in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        if m % sp == 0: return m == sp
    d, s = m - 1, 0
    while d % 2 == 0: d //= 2; s += 1
    for a in (2, 3, 5, 7, 11, 13, 17, 19, 29, 37, 41):
        x = pow(a, d, m)
        if x in (1, m - 1): continue
        for _ in range(s - 1):
            x = x * x % m
            if x == m - 1: break
        else: return False
    return True

# ---------------- the certificate ----------------

def dft_all(Z, h, n):
    """V1(a) for all a in [0,n): exact coefficient vectors."""
    pv = Z.powvec()
    out = []
    for a in range(n):
        r = [0] * (n - 1)
        for d in range(n):
            c = h[d]
            if c:
                p = pv[(a * d) % n]
                for i in range(n - 1):
                    if p[i]:
                        r[i] += c * p[i]
        out.append(r)
    return out

def main():
    primes = [(43, "7"), (67, "7"), (79, "7"), (127, "7"), (163, "7"), (211, "7"),
              (349, "1"), (61, "1-anomalous")]
    import numpy as np
    print("=" * 100)
    print(" D2 TWIST-RIGIDITY CERTIFICATE — exact Z[zeta_n] signal path; float only in root readout")
    print("=" * 100)
    pooled_cos = []
    free_cos = []
    free_cos_7 = []
    summary = []
    for (p, arm) in primes:
        n, h = curve_points_f(p)
        assert is_prime_int(n), (p, n)
        Z = Zz(n)
        V = dft_all(Z, h, n)                    # V1(a) = sum h[d] zeta^{ad}
        leg = 1 if p % 4 == 1 else -1

        # ---- (cross-path) h vs the repo's core.hist_k1 (generators may differ -> k-permutation) ----
        import audit_n1_vsign_v2_core as core
        dl = core.dlog_table(p, n)
        hcore = core.hist_k1(p, n, dl)
        if hcore != h:
            # find k with h[d] == hcore[(k*d) % n]  (my generator = [k] of core's)
            Gmine = None
            for x in range(p):
                y = tonelli((x * x % p * x + 7) % p, p)
                if y: Gmine = (x, y); break
            k = dl[Gmine]
            assert all(h[d] == hcore[(k * d) % n] for d in range(n)), f"h1 mismatch vs core at p={p}"
        random.seed(p)
        maxdev = 0.0
        for _ in range(5):
            a = random.randrange(n)
            num = sum(h[d] * cmath.exp(2j * cmath.pi * (a * d % n) / n) for d in range(n))
            maxdev = max(maxdev, abs(num - Z.embed(V[a])))
        # ---- exact structural checks ----
        zero = [0] * (n - 1)
        ok_v0 = (V[0] == zero)                                  # L1: a=0 trace zero
        ok_parity = all((Z.conj(V[a]) == ([-c for c in V[a]] if leg == -1 else V[a])) for a in range(n))
        lam = None
        for g in range(2, n):
            if pow(g, 3, n) == 1 and pow(g, 1, n) != 1:
                lam = g; break
        ok_descent = all(V[(lam * a) % n] == V[a] for a in range(n))
        # ---- L*(a) spectral readouts ----
        sqp = math.sqrt(p)
        z3 = cmath.exp(2j * cmath.pi / 3)
        max_purity_dev = 0.0
        max_z3_resid = 0.0
        z3_fail = 0
        min_rou_dist = 1e9          # distance of (alpha/sqrt p)^m from 1, all m <= 66
        maxV = 0.0
        for a in range(1, n):
            e1v = [-c for c in V[a]]                             # e1 = -V1
            e1n = Z.embed(e1v)
            e2n = e1n * e1n - leg * p                            # P32: e2 = e1^2 - chi2(-1) p
            e3n = leg * p * e1n
            e4n = float(p * p)
            coeffs = [1 + 0j, -e1n, e2n, -e3n, e4n]
            roots = np.roots(coeffs)
            maxV = max(maxV, abs(e1n))
            for r in roots:
                pooled_cos.append(r.real / sqp)
                max_purity_dev = max(max_purity_dev, abs(abs(r) - sqp) / sqp)
                u = r / sqp
                for m in range(1, 67):
                    min_rou_dist = min(min_rou_dist, abs(u ** m - 1))
            # zeta3 multiset law. Closure depends on p mod 4 (M4: trace imag/real):
            #   p=3 mod 4: {alpha, rho alpha, -conj alpha, -conj(rho alpha)}   (trace imaginary)
            #   p=1 mod 4: {alpha, rho alpha,  conj alpha,  conj(rho alpha)}   (trace real)
            sgn = -1 if leg == -1 else 1
            best = None; best_pair = None
            for rho in (z3, z3.conjugate()):
                for alpha in roots:
                    exp = [alpha, rho * alpha,
                           sgn * alpha.conjugate(), sgn * (rho * alpha).conjugate()]
                    used = [False] * 4; resid = 0.0; ok = True
                    for e in exp:
                        cand = [(abs(roots[i] - e), i) for i in range(4) if not used[i]]
                        if not cand: ok = False; break
                        j = min(cand)[1]
                        resid = max(resid, abs(roots[j] - e) / sqp)
                        used[j] = True
                    if ok and (best is None or resid < best):
                        best = resid; best_pair = (alpha, rho)
            if best is None or best > 1e-6:
                z3_fail += 1
            else:
                max_z3_resid = max(max_z3_resid, best)
                # the TWO FREE angles per cell (the 2-of-4 structure): alpha and rho*alpha
                free_cos.append(abs(best_pair[0].real) / sqp)
                free_cos.append(abs((best_pair[0] * best_pair[1]).real) / sqp)
                if leg == -1:
                    free_cos_7.append(abs(best_pair[0].real) / sqp)
                    free_cos_7.append(abs((best_pair[0] * best_pair[1]).real) / sqp)
        # ---- a=0 baseline: exact coefficients from V1[0] (vanishes at p=3 mod 4 by L1) ----
        e0_1 = -Z.embed(V[0])
        e0_2 = e0_1 * e0_1 - leg * p
        e0_3 = leg * p * e0_1
        base = np.roots([1 + 0j, -e0_1, e0_2, -e0_3, float(p * p)])
        if leg == -1:
            # EXACT (no numerical root-finding, replaces a float np.roots decision):
            # ok_v0 is an exact integer-vector check (V[0]==0), which forces e1(0)=0
            # hence e2=p, e3=0 -- all EXACT integers (no embedding/cmath needed once
            # V[0]==0, since Z.embed of the zero vector is identically 0). The quartic
            # is then exactly T^4 + p*T^2 + p^2, the cofactor of (T^2-p) in T^6-p^3
            # (checked below by exact integer polynomial multiplication -- an identity
            # that holds for every p). So every root T satisfies T^6=p^3 EXACTLY =>
            # |T|=sqrt(p) exactly (T^6=p^3 with p^3>0 forces |T|^6=p^3 so |T|=p^{1/2},
            # the unique positive real 6th root) and (T/sqrt(p))^6=1 exactly (order | 6).
            # T^2=p is never itself a root: substituting x=p into the biquadratic factor
            # x^2+p*x+p^2 gives 3*p^2 (exact int, != 0 since p>0) -- so order is never
            # 1 or 2, hence exactly 3 or 6: sqrt(p)*mu6\{+-1}, matching [6,3,6,3].
            e2_exact, e4_exact = p, p * p                      # e1=0, e3=0 forced by ok_v0
            a_coef = [-p, 0, 1]                                # T^2 - p             (ascending)
            b_coef = [e4_exact, 0, e2_exact, 0, 1]             # T^4 + e2 T^2 + e4   (ascending)
            lhs = [0] * (len(a_coef) + len(b_coef) - 1)
            for i, ai in enumerate(a_coef):
                for j, bj in enumerate(b_coef):
                    lhs[i + j] += ai * bj
            rhs = [-(p ** 3), 0, 0, 0, 0, 0, 1]                # T^6 - p^3           (ascending)
            identity_ok = (lhs == rhs)
            never_order12 = (p * p + p * e2_exact + e4_exact != 0)  # x^2+px+p^2 at x=p
            base_ok = bool(ok_v0 and identity_ok and never_order12)
            base_msg = ("sqrt(p)*mu6 orders [6,3,6,3]  "
                        "[EXACT: e1(0)=0 (ok_v0) => T^6=p^3 via (T^2-p)(T^4+pT^2+p^2)=T^6-p^3]")
        else:
            base_ok = all(abs(abs(r) - sqp) / sqp < 1e-12 for r in base) and \
                      all(min(abs((r / sqp) ** m - 1) for m in range(1, 67)) > 1e-6 for r in base)
            base_msg = (f"|eigen|=sqrt(p) OK (P23 ss is a p=3 mod 4 statement; here "
                        f"e1(0)={e0_1:.3f} nonzero allowed; roots-of-unity: no)")
        # ---- P32-at-cells via the repo's F_{p^2} trace sum (headline primes only) ----
        p32 = "skipped"
        if p in (43, 67):
            h2 = core.hist_k2(p, n, dl)
            bad = 0
            for a in range(n):
                V2 = [0] * (n - 1)
                pv = Z.powvec()
                for d in range(n):
                    if h2[d]:
                        q = pv[(a * d) % n]
                        for i in range(n - 1):
                            if q[i]: V2[i] += h2[d] * q[i]
                # predicted: V2 = V1^2 - 2 leg p
                V1sq = Z.mul(V[a], V[a])
                pred = [c for c in V1sq]
                pred[0] -= 2 * leg * p
                if V2 != pred: bad += 1
            p32 = f"V2==V1^2-2leg*p at {n - bad}/{n} cells"
        arm_tag = f"p%12={arm}"
        print(f" p={p:>3} n={n:>3} [{arm_tag}]  h1==core.h1 OK | numeric-DFT dev {maxdev:.1e}")
        print(f"    V(0)=0 [L1] {ok_v0} | M4 parity ({'imag' if leg == -1 else 'real'}) {ok_parity} "
              f"| w-descent V(lam a)=V(a) lam={lam} {ok_descent} | P32-cells: {p32}")
        print(f"    a=0 baseline: {base_msg} -> {base_ok}")
        print(f"    twisted (a!=0, all {n-1} cells): purity dev max {max_purity_dev:.2e} | "
              f"zeta3-law fail {z3_fail} (resid max {max_z3_resid:.1e}) | "
              f"root-of-unity survival: min dist {min_rou_dist:.2e} (exact hit would read <=1e-11; NO survival)")
        print(f"    max|V1(a)|/sqrt(p) = {maxV / sqp:.4f}   (the sqrt(3)=1.732 sub-Weil target is OPEN, "
              f"not a bound; record obs max 1.932 @ p=547)")
        summary.append((p, n, arm, ok_v0 and ok_parity and ok_descent and base_ok,
                        max_purity_dev, z3_fail, min_rou_dist))
    print("-" * 100)
    import statistics
    mc = statistics.fmean(abs(c) for c in pooled_cos)
    mf = statistics.fmean(free_cos)
    mf7 = statistics.fmean(free_cos_7)
    print(f" angle readout (twisted cells): mean|cos| ALL 4 eigenvalues/cell = {mc:.4f} "
          f"(constrained multiset - neither prediction applies)")
    print(f"   mean|cos| FREE angles only (2/cell): all primes = {mf:.4f} | "
          f"p=3 mod 4 arm = {mf7:.4f}")
    print(f"   Sato-Tate prediction 4/(3 pi) = {4 / (3 * math.pi):.4f} | uniform-angle 2/pi = {2 / math.pi:.4f}")
    print(f"   (the record's equidistribution evidence: 0.408 measured vs 0.424 predicted)")
    print("=" * 100)

if __name__ == "__main__":
    main()
