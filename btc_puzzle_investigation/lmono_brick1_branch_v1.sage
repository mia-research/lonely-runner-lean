#!/usr/bin/env sage
# lmono_brick1_branch_v1.sage — L-mono brick 1, the decisive new observable: the per-cell RHO-BRANCH.
# Brick 2 (7/7 exact) shows roots(g2) = rho * roots(g1) over K = Q(zeta_{12n}). The branch
# rho(a) in {zeta3, zbar3} is a function of the cell a — the arithmetic fingerprint of the Kummer
# character psi in the centralizer conjecture. THE TEST: is rho(a) = the cubic character of a?
#   candidates: chi3_n(a) = a^((n-1)/3) mod n  (order-3 char of (Z/n)*)
#               chi3_p(a) = a^((p-1)/3) mod p  (order-3 char of (Z/p)*)
# Convention: g1 := facs[0] as sage deterministically returns it; test both branch orientations.
import sys, time, json
sys.path.insert(0, "/Users/trentpalelei/Desktop/Math Ex/btc_puzzle_investigation")
import audit_n1_vsign_v2_core as core

def build_L(p, a, Kn, zn, n):
    dl = core.dlog_table(p, n); h1 = core.hist_k1(p, n, dl); h2 = core.hist_k2(p, n, dl)
    V1 = sum(h1[d]*zn**((a*d) % n) for d in range(n))
    V2 = sum(h2[d]*zn**((a*d) % n) for d in range(n))
    leg = 1 if p % 4 == 1 else -1
    e1 = -V1; e2 = (V1**2 + V2)/2; e3 = leg*p*e1; e4 = Kn(p**2)
    R = PolynomialRing(Kn, 'T'); T = R.gen()
    return T**4 - e1*T**3 + e2*T**2 - e3*T + e4

def canon_order(facs, K):
    """canonical order of the two quadratic factors: lexicographic on the power-basis
    coefficient vectors of [T^2-coeff=1, T-coeff, constant] — representation-independent."""
    def key(f):
        return tuple(tuple(c.vector()) for c in f.list())
    return sorted(facs, key=key)

def run(p, max_cells=None):
    n = core.curve_order(p); m = 12*n
    K = CyclotomicField(m); z = K.gen()
    Kn = CyclotomicField(n); zn = Kn.gen()
    phi = Kn.hom([z**12], K)
    R = PolynomialRing(K, 'T'); T = R.gen()
    z3a = z**(4*n); assert z3a**3 == 1 and z3a != 1
    cells = [a for a in range(1, n) if gcd(a, n) == 1]
    if max_cells: cells = cells[:max_cells]
    # reference elements for the two cubic characters
    hn = next(h for h in range(2, n) if pow(h, 3, n) == h**3 % n and pow(h, (n-1)//3, n) != 1)
    hp = next(h for h in range(2, p) if pow(h, (p-1)//3, p) != 1)
    rows = []
    descent_ok = True
    lam_ = next(g for g in range(2, n) if pow(g, 3, n) == 1 and g != 1)
    t0 = time.time()
    Lcache = {}
    for a in cells:
        L = build_L(p, a, Kn, zn, n)
        Lb = sum(phi(c)*T**i for i, c in enumerate(L.list()))
        if a not in Lcache:
            Lcache[a] = Lb
        al = lam_ * a % n
        if al in cells and al not in Lcache:
            Lal = build_L(p, al, Kn, zn, n)
            Lcache[al] = sum(phi(c)*T**i for i, c in enumerate(Lal.list()))
        if al in Lcache and Lcache[al] != Lb:
            descent_ok = False
        facs = [f for f, e in Lb.factor()]
        if sorted(f.degree() for f in facs) != [2, 2]:
            rows.append((a, None, None, None)); continue
        g1, g2 = canon_order(facs, K)     # CANONICAL: equal polynomials -> identical order
        s1 = -g1[1]; u1 = g1[0]
        rho = None
        for r in (z3a, z3a**2):
            if T**2 - r*s1*T + r**2*u1 == g2:
                rho = r; break
        branch = None if rho is None else (1 if rho == z3a else 2)
        cn = 0 if pow(a, (n-1)//3, n) == 1 else (1 if pow(a, (n-1)//3, n) == hn else 2)
        cp = 0 if pow(a, (p-1)//3, p) == 1 else (1 if pow(a, (p-1)//3, p) == hp else 2)
        rows.append((a, branch, cn, cp))
    # correlation read: does branch track cn (or cp), possibly with flipped orientation?
    valid = [r for r in rows if r[1] is not None]
    res = {}
    for name, idx in (("chi3_n", 2), ("chi3_p", 3)):
        m01 = sum(1 for (a, b, c1, c2) in valid if (b == 1) == ((a and [c1, c2][idx-2] == 1)))
        m02 = sum(1 for (a, b, c1, c2) in valid if (b == 2) == ([c1, c2][idx-2] == 1))
        # cleaner: agreement rates of branch with each character value
        agree = sum(1 for r in valid if r[1] == r[idx])
        flipped = sum(1 for r in valid if (3 - r[1]) % 3 == r[idx] and r[1] != 0)
        res[name] = (agree, flipped, len(valid))
        print(f"  vs {name}: branch==char {agree}/{len(valid)} | branch==(char+1) {flipped}/{len(valid)}", flush=True)
    print(f"p={p} n={n}: {len(valid)} cells factored [{time.time()-t0:.0f}s] | descent L*(a)==L*(lam a): {descent_ok}", flush=True)
    # branch marginal + descent consistency: branch(lambda a) should equal branch(a)?
    lam = None
    for g in range(2, n):
        if pow(g, 3, n) == 1 and g != 1: lam = g; break
    bmap = {a: b for (a, b, _, _) in rows}
    desc = [(a, bmap.get(lam*a % n)) for a in bmap if bmap.get(lam*a % n) is not None and bmap[a] is not None]
    dsame = sum(1 for (b1, b2) in desc if b1 == b2)
    print(f"  branch on mu3-orbits: same-branch {dsame}/{len(desc)} (descent says V is constant; branch should be too)", flush=True)
    return rows

if __name__ == "__main__":
    out = {}
    for p, mx in [(43, None), (61, None), (79, None)]:
        print(f"=== p={p} ===", flush=True)
        out[p] = run(p, mx)
    json.dump({str(k): v for k, v in out.items()},
              open("/Users/trentpalelei/Desktop/Math Ex/btc_puzzle_investigation/lmono_brick1_branch.json", "w"))
    print("dumped lmono_brick1_branch.json", flush=True)
