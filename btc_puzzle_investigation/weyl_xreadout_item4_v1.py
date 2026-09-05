#!/usr/bin/env python3
"""weyl_xreadout_item4_v1.py -- ITEM 4: quadratic (Weyl) phases on the x-readout.

OBJECT.   H_F(a) = sum_d F(x([d]G)) * e_n(a d^2),  F in {chi_2, chi_3, chi_6} of the x-coordinate.
          Flagged untested in masked_structure_findings_v5.md:137.

WHY THIS IS NOT A RERUN OF THE CHIRP PLANE.  The chirp work used c(d) = chi_2(y_d), which is ODD in
d, against e_n(k d^2), which is EVEN.  That parity MISMATCH is exactly what capped the best possible
alignment at 0.16n and forced the record to conclude "a +-1 sequence cannot track a quadratic phase;
the sign is all it has."  The x-readout is EVEN in d (x(-d) = x(d)), so it is PARITY-MATCHED with the
quadratic phase.  The obstruction that limited the y-readout does not apply here.

FORCED SYMMETRIES (must be respected by the null, or the test manufactures a phantom):
  (1) x(-d) = x(d)              => F(x_d) is EVEN in d.
  (2) x(lambda d) = beta x_d    => chi_2: chi_2(beta)=1 so chi_2(x) is mu_3-INVARIANT;
                                   chi_3, chi_6: pick up a cube root, so |F| is unchanged.
      Substituting d -> lambda d gives  |H(a)| = |H(a lambda^2)|  for EVERY character readout.
  => the readout is a CLASS FUNCTION on the mu_6 classes of d, and |H| is a class function on the
     mu_6 classes of the FREQUENCY a.  Statistics run on the (n-1)/6 FREE frequency classes.

REFORMULATION (used as a control).  d -> d^2 is 2-to-1 for n odd, so with F even
    H(a) = 2 * sum over QUADRATIC RESIDUES s of F(x_{sqrt s}) e_n(a s),
i.e. H is the DFT of a QR-supported sequence.  Parseval then fixes  mean|H|^2 = 2n  exactly.

NULL.  Class-permutation: permute the readout's class-values among the mu_6 classes of d.  Preserves
every forced symmetry exactly and destroys only the pairing between the readout and the phase.
CONTROLS.  C-CLASS (readout constant on mu_6 d-classes; |H| constant on mu_6 a-classes),
           C-PARSEVAL (mean|H|^2 == 2n exactly), C-PLANT (a coherent quadratic alignment must fire).
"""

import numpy as np
import sys

sys.path.insert(0, ".")
from twist_orbit_spectrum_run_v1 import curve_orbit


def isprime(m):
    if m < 2:
        return False
    for d in range(2, int(m**0.5) + 1):
        if m % d == 0:
            return False
    return True


def chi(a, p, k):
    """chi_k(a) as a complex k-th root of unity (0 if a==0)."""
    a %= p
    if a == 0:
        return 0j
    e = pow(a, (p - 1)//k, p)
    g0 = None
    for g in range(2, p):
        c = pow(g, (p - 1)//k, p)
        if all(pow(c, j, p) != 1 for j in range(1, k)):
            g0 = c
            break
    cur = 1
    for j in range(k):
        if cur == e:
            return np.exp(2j*np.pi*j/k)
        cur = cur*g0 % p
    return 0j


def build(p, kchar):
    r = curve_orbit(p, 7)
    if r is None:
        return None
    X, Y, n = r
    if (n - (p + 1))**2 > 4*p or not isprime(n) or n % 6 != 1:
        return None
    if (p - 1) % kchar:
        return None
    xs = np.asarray(X, dtype=np.int64) % p
    # matched lambda/beta: x_{lambda d} = beta x_d
    lams = [t for t in range(2, n) if pow(t, 3, n) == 1 and t != 1]
    betas = [t for t in range(2, p) if pow(t, 3, p) == 1 and t != 1]
    lam = beta = None
    for L_ in lams:
        for B_ in betas:
            if all(int(xs[(d*L_) % n]) == (B_*int(xs[d])) % p for d in (1, 2, 3, 5, 7)):
                lam, beta = L_, B_
                break
        if lam:
            break
    if lam is None:
        return None
    c = np.array([0j] + [chi(int(xs[d]), p, kchar) for d in range(1, n)])
    return n, c, lam, beta


def mu6_classes(n, lam):
    """classes of {+-d, +-lam d, +-lam^2 d} on 1..n-1."""
    seen = np.zeros(n, dtype=bool)
    cls = []
    for d in range(1, n):
        if seen[d]:
            continue
        o = set()
        for s in (d, lam*d % n, lam*lam*d % n):
            o.add(s)
            o.add((n - s) % n)
        for z in o:
            seen[z] = True
        cls.append(sorted(o))
    return cls


def H_of(c, n):
    d = np.arange(n)
    sq = (d*d) % n
    W = np.exp(2j*np.pi*np.outer(np.arange(n), sq)/n)
    return W @ c


def stats(Hm, free):
    v = Hm[free]
    return {"max": float(v.max()), "top5": float(np.sort(v)[-5:].mean()),
            "frac_hi": float((v > 2.5*np.sqrt(v.size)).mean()), "var": float(v.var())}


KEYS = ["max", "top5", "frac_hi", "var"]


def orbits3(n, lam):
    """mu_6 orbits, returned as the three lam-levels each holding a +- PAIR:
         level k = { lam^k d , -lam^k d }   with value zeta^k * v.
       BOTH forced symmetries are then respected simultaneously:
         c(-d) = c(d)          (evenness -- x(-d) = x(d))
         c(lam d) = zeta c(d)  (lam-equivariance)
       A lam-only orbit breaks evenness and makes the null's mean|H|^2 = n instead of 2n."""
    seen = np.zeros(n, dtype=bool)
    out = []
    for d in range(1, n):
        if seen[d]:
            continue
        lv = []
        for k in range(3):
            a = (d*pow(lam, k, n)) % n
            pair = [a, (n - a) % n]
            for z in pair:
                seen[z] = True
            lv.append(pair)
        out.append(lv)
    return out


def run(p, kchar, R=400, seed=1):
    b = build(p, kchar)
    if b is None:
        return None
    n, c, lam, beta = b
    zeta = chi(beta, p, kchar)                       # c(lam d) = zeta * c(d)  (zeta = 1 for chi_2)
    cls = orbits3(n, lam)
    # C-CLASS: readout EQUIVARIANT on mu_3 orbits (constancy is the zeta = 1 special case)
    ok_c = all(abs(c[o[1][0]] - zeta*c[o[0][0]]) < 1e-9
               and abs(c[o[2][0]] - zeta*zeta*c[o[0][0]]) < 1e-9
               and all(abs(c[lv[1]] - c[lv[0]]) < 1e-9 for lv in o) for o in cls)
    H = H_of(c, n)
    Hm = np.abs(H)
    # FREQUENCY classes: |H(-a)| = |H(a)| requires c REAL.  That holds for chi_2 only; for the
    # complex chi_3 / chi_6 the +- frequency symmetry does NOT hold and the free set is mu_3.
    real_readout = bool(np.max(np.abs(np.imag(c))) < 1e-12)
    if real_readout:
        acls = mu6_classes(n, lam)
    else:
        acls = [[a, a*lam % n, a*lam*lam % n] for a in range(1, n)]
        seen = set()
        acls = [o for o in acls if not (set(o) & seen) and not seen.update(o)]
    free = np.array([o[0] for o in acls])
    ok_a = all(np.allclose(Hm[o], Hm[o[0]], atol=1e-6*max(1, Hm.max())) for o in acls)
    mean2 = float((Hm[1:]**2).mean())
    rng = np.random.default_rng(seed)
    obs = stats(Hm, free)
    ge = {k: 0 for k in KEYS}
    vals = np.array([c[o[0][0]] for o in cls])

    def draw():
        """permute orbit values; re-impose BOTH the zeta-twist across lam-levels and evenness
           within each +- pair.  C-PARSEVAL below verifies the draws really carry mean|H|^2 = 2n."""
        perm = rng.permutation(vals)
        cn = np.zeros(n, dtype=complex)
        for v, o in zip(perm, cls):
            for k, lv in enumerate(o):
                w = v*(zeta**k)
                cn[lv[0]] = w
                cn[lv[1]] = w
        return cn

    null_par = []
    for _ in range(R):
        cn = draw()
        Hn = np.abs(H_of(cn, n))
        null_par.append(float((Hn[1:]**2).mean()))
        s = stats(Hn, free)
        for k in KEYS:
            if s[k] >= obs[k]:
                ge[k] += 1
    nullpar = float(np.mean(null_par))/(2*n)
    # C-PLANT: a single-frequency quadratic phase is NOT realisable within the forced symmetry
    # (a d^2 -> a lam^2 d^2 under d -> lam d).  The realisable coherent target is the phase summed
    # over the whole FREQUENCY class of a0, which IS mu_3-invariant in d.
    a0 = 7
    acl = [a0, a0*lam % n, a0*lam*lam % n]
    dd = np.arange(n)
    sq = (dd*dd) % n
    tgt = sum(np.exp(2j*np.pi*(aa*sq % n)/n) for aa in acl)
    pl = np.zeros(n, dtype=complex)
    for o in cls:
        v = tgt[o[0][0]]
        v = v/abs(v) if abs(v) > 1e-12 else 1.0
        for k, lv in enumerate(o):
            w = v*(zeta**k)
            pl[lv[0]] = w
            pl[lv[1]] = w
    sp = stats(np.abs(H_of(pl, n)), free)
    gp = {k: 0 for k in KEYS}
    for _ in range(R):
        s = stats(np.abs(H_of(draw(), n)), free)
        for k in KEYS:
            if s[k] >= sp[k]:
                gp[k] += 1
    return n, ok_c, ok_a, mean2, obs, ge, gp, R, len(free), nullpar


if __name__ == "__main__":
    R = int(sys.argv[1]) if len(sys.argv) > 1 else 400
    for kchar in (2, 3, 6):
        print("\n" + "=" * 98)
        print("ITEM 4 -- H(a) = sum_d chi_%d(x_d) e_n(a d^2)   [x-readout: EVEN, parity-MATCHED to d^2]"
              % kchar)
        print("=" * 98)
        print("  %-6s %-6s %-6s | %-9s %-9s | %s"
              % ("p", "n", "free", "C-CLASS", "C-PARSEV", "  ".join("%-14s" % k for k in KEYS)))
        for p in range(100, 700):
            if not isprime(p) or p % 3 != 1:
                continue
            r = run(p, kchar, R)
            if r is None:
                continue
            n, ok_c, ok_a, mean2, obs, ge, gp, R_, nf, nullpar = r
            cells = []
            for k in KEYS:
                pv = (ge[k] + 1)/(R_ + 1)
                pv2 = min(pv, 1 - pv + 1.0/(R_ + 1))*2
                cells.append("%-14s" % ("%.4f%s" % (pv2, "*" if pv2 <= 0.05 else "")))
            pfire = sum(1 for k in KEYS if (gp[k] + 1)*20 <= (R_ + 1))
            print("  %-6d %-6d %-6d | %-9s %-9s | %s  [plant fires %d/4]"
                  % (p, n, nf, "OK" if ok_c and ok_a else "*** FAIL ***",
                     "d%.3f/n%.3f" % (mean2/(2*n), nullpar), "  ".join(cells), pfire))
