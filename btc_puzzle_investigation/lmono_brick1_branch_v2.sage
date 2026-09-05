#!/usr/bin/env sage
# lmono_brick1_branch_v2.sage — the RHO-BRANCH, take 2: correct analysis, safe dump.
# Invariant observable: #distinct branch values across cells (1 = canonical plane labeling,
# 2 = per-orbit labeling). Branch MUST be mu3-orbit-constant (L*(a)=L*(lam a) + canonical
# factor order). Characters tested per prime with their orbit-constancy (chi(lam)) reported.
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

def canon(facs):
    return sorted(facs, key=lambda f: tuple(tuple(c.vector()) for c in f.list()))

def run(p):
    n = core.curve_order(p); m = 12*n
    K = CyclotomicField(m); z = K.gen()
    Kn = CyclotomicField(n); zn = Kn.gen()
    phi = Kn.hom([z**12], K)
    R = PolynomialRing(K, 'T'); T = R.gen()
    z3a = z**(4*n)
    lam = next(g for g in range(2, n) if pow(g, 3, n) == 1 and g != 1)
    t0 = time.time()
    bmap = {}
    for a in range(1, n):
        if gcd(a, n) != 1: continue
        Lb = sum(phi(c)*T**i for i, c in enumerate(build_L(p, a, Kn, zn, n).list()))
        facs = [f for f, e in Lb.factor()]
        if sorted(f.degree() for f in facs) != [2, 2]:
            bmap[a] = None; continue
        g1, g2 = canon(facs)
        s1 = -g1[1]; u1 = g1[0]
        bmap[a] = 1 if T**2 - z3a*s1*T + z3a**2*u1 == g2 else 2
    valid = {a: b for a, b in bmap.items() if b is not None}
    # orbits
    seen = set(); orbits = []
    for a in valid:
        if a in seen: continue
        o = [a, lam*a % n, lam*lam*a % n]
        seen.update(o)
        orbits.append(o)
    mixed = [o for o in orbits if len({valid[x] for x in o if x in valid}) > 1]
    dist = {}
    for b in valid.values(): dist[b] = dist.get(b, 0) + 1
    # characters and their orbit-constancy
    def chi2(a, mod): return 1 if pow(a, (mod-1)//2, mod) == 1 else 2
    def chi3_class(a, mod):
        v = pow(a, (mod-1)//3, mod)
        return 0 if v == 1 else (1 if v == lam_n(mod) else 2)
    lam_n_cache = {}
    def lam_n(mod):
        if mod not in lam_n_cache:
            lam_n_cache[mod] = next(g for g in range(2, mod) if pow(g, 3, mod) == 1 and g != 1)
        return lam_n_cache[mod]
    print(f"p={p} n={n}: branch distribution {dist} | orbits {len(orbits)}, mixed-branch orbits: {len(mixed)} "
          f"(must be 0) | [{time.time()-t0:.0f}s]", flush=True)
    for (name, chi) in (("chi2_n", lambda a: chi2(a, n)), ("chi2_p", lambda a: chi2(a, p)),
                        ("chi3_n", lambda a: chi3_class(a, n)), ("chi3_p", lambda a: chi3_class(a, p))):
        # orbit-constancy of the character itself
        oc = all(len({chi(x) for x in o}) == 1 for o in orbits)
        if not oc:
            print(f"   {name}: NOT orbit-constant (chi(lam) cycles) — cannot equal the branch", flush=True)
            continue
        reps = [o[0] for o in orbits]
        match = sum(1 for a in reps if valid[a] == chi(a) or (3 - valid[a]) % 3 == chi(a) or valid[a] % 3 == chi(a) or chi(a) == 0)
        strict = sum(1 for a in reps if (valid[a] == 2) == (chi(a) == 2))
        print(f"   {name}: orbit-constant; on {len(reps)} orbit reps: branch-vs-char agreement {strict}/{len(reps)}", flush=True)
    return {str(a): int(b) for a, b in valid.items()}

if __name__ == "__main__":
    out = {}
    for p in (43, 61, 79, 163):
        out[str(p)] = run(p)
        json.dump(out, open("/Users/trentpalelei/Desktop/Math Ex/btc_puzzle_investigation/lmono_brick1_branch.json", "w"))
    print("dumped (incrementally)", flush=True)
