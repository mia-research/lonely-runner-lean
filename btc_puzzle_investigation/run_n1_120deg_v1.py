#!/usr/bin/env python3
"""run_n1_120deg_v1.py -- execute PREREG_n1_120deg_exact_ideal_v4.md.

EXACT INTEGER/MODULAR ARITHMETIC ONLY (no float in the signal path).
Reuses the record's exact histograms (audit_n1_vsign_v2_core.hist_k1/hist_k2) and adds the
PRIMARY statistic g(p,a) = deg gcd(L*(T), L*(zeta3 T)) computed MULTI-MODULARLY (deviation D2):
for several primes l == 1 mod 3n, embed zeta_n,zeta3 -> fixed roots of unity in F_l, reduce the
L* coefficients, deg gcd over F_l by Euclid.  Reduction only RAISES gcd degree, so
    min_l g_l >= g_true      (CORRECTION_120deg_census_certification_direction_v1.md).
This statistic is therefore an UPPER BOUND on g_true: a computed 0 certifies g_true = 0 exactly,
a computed 2 certifies only g_true <= 2 (consistent with g_true in {0,1,2}).  The lower-bound half
(g_true >= 2) is supplied by PART 1 (verify_120deg_symbolic_factorization_v1: D|L and D|L(zeta3 T)
symbolically => deg gcd >= 2 unconditionally) conjoined with PART 2
(verify_120deg_exact_certificate_v2: exact per-prime residual V2-V1^2 = -2*eps*p).  The conjoined
certificate is verify_120deg_conjoined_certificate_v1.py; THIS script supplies only the upper bound.
"""
import sys, time
import audit_n1_vsign_v2_core as core

# ---------- mu_6 classes (pinned by the freeze's zeta3 rule) ----------
def cube_root_of_unity(n):
    rt = core.tonelli((-3) % n, n)
    inv2 = pow(2, n-2, n)
    c1 = (-1 + rt) * inv2 % n
    c2 = (-1 - rt) * inv2 % n
    assert (c1*c1+c1+1) % n == 0 and (c2*c2+c2+1) % n == 0
    return min(c1, c2)

def mu6_reps(n):
    z3 = cube_root_of_unity(n); z3sq = z3*z3 % n
    U = [1 % n, (n-1) % n, z3, (n-z3) % n, z3sq, (n-z3sq) % n]
    seen = bytearray(n); reps = []
    for m in range(1, n):
        if seen[m]: continue
        reps.append(m)
        for u in U: seen[m*u % n] = 1
    assert len(reps) == (n-1)//6
    return reps

# ---------- exact poly gcd over F_l ----------
def _norm(A, l):
    A = [c % l for c in A]
    while A and A[-1] == 0: A.pop()
    return A

def _rem(A, B, l):
    A = _norm(A, l); B = _norm(B, l)
    inv = pow(B[-1], l-2, l)
    while len(A) >= len(B):
        f = A[-1]*inv % l; sh = len(A)-len(B)
        for i in range(len(B)): A[sh+i] = (A[sh+i]-f*B[i]) % l
        A = _norm(A, l)
        if not A: break
    return A

def deg_gcd(A, B, l):
    A = _norm(A[:], l); B = _norm(B[:], l)
    while B: A, B = B, _rem(A, B, l)
    return (len(A)-1) if A else -1

# ---------- multi-modular g for one cell ----------
def primitive_root_of_order(m, l):
    """some element of F_l of order exactly m (m | l-1, m prime-power handled: here m prime)."""
    e = (l-1)//m
    b = 2
    while True:
        r = pow(b, e, l)
        if r != 1: return r        # m prime -> order is exactly m
        b += 1

def ell_primes(n, k=5):
    """first k primes l == 1 mod 3n (deterministic; frozen ell-selection, D2)."""
    step = 3*n; l = step + 1; out = []
    while len(out) < k:
        if core.is_prime(l): out.append(l)
        l += step
    return out

def g_and_flags(p, n, h1, h2, a, ells):
    """returns (g, is_zero, is_repeated) for cell a, min over ell."""
    gmin = 4; zero_all = True; rep_min = 4
    for l in ells:
        r  = primitive_root_of_order(n, l)      # zeta_n -> r
        w  = primitive_root_of_order(3, l)      # zeta3  -> w
        inv2 = pow(2, l-2, l)
        # V1(a), V2(a) mod l  via  sum_d h[d] r^{a d}
        ra = pow(r, a % n, l)                    # r^a
        rp = 1; V1 = 0; V2 = 0
        for d in range(n):
            if h1[d]: V1 = (V1 + h1[d]*rp) % l
            if h2[d]: V2 = (V2 + h2[d]*rp) % l
            rp = rp*ra % l
        if V1 != 0: zero_all = False
        e1 = (-V1) % l
        e2 = (V1*V1 + V2)*inv2 % l
        # e3 forced by closure, whose SIGN is chi2(-1) = legendre(-1,p):
        #   p==3 mod4 (V imaginary, alpha|->-abar closure) -> e3 = -p*e1
        #   p==1 mod4 (V real,      alpha|->abar  closure) -> e3 = +p*e1
        leg = 1 if p % 4 == 1 else -1                      # chi2(-1)
        e3 = (leg*p*e1) % l
        e4 = (p*p) % l
        L  = [e4, (-e3) % l, e2, (-e1) % l, 1]                 # low->high
        wk = [1, w, w*w % l, pow(w,3,l), pow(w,4,l)]
        Lz = [L[k]*wk[k] % l for k in range(5)]                # L*(w T)
        gmin = min(gmin, deg_gcd(L, Lz, l))
        Ld = [L[1], 2*L[2] % l, 3*L[3] % l, 4*L[4] % l]        # derivative
        rep_min = min(rep_min, deg_gcd(L, Ld, l))
    return gmin, zero_all, (rep_min > 0)

# ---------- per-prime driver ----------
def run_prime(p, tag, budget_s=900):
    t0 = time.time()
    n = core.curve_order(p)
    assert core.is_prime(n), (p, n)
    dl = core.dlog_table(p, n)
    h1 = core.hist_k1(p, n, dl)
    h2 = core.hist_k2(p, n, dl)                                 # O(p^2)
    reps = mu6_reps(n)
    ells = ell_primes(n, 5)
    dist = {}; zero = 0; rep = 0; nonlaw = []
    for a in reps:
        if time.time()-t0 > budget_s:
            print(f"  [{tag}] p={p} ABSTAIN (budget {budget_s}s exceeded) after "
                  f"{len(dist)+zero+rep}/{len(reps)} cells")
            return None
        g, is0, isrep = g_and_flags(p, n, h1, h2, a, ells)
        if is0: zero += 1; continue
        if isrep: rep += 1; continue
        dist[g] = dist.get(g, 0) + 1
        if g != 2: nonlaw.append((a, g))
    dt = time.time()-t0
    survivors = sum(dist.values())
    alllaw = (set(dist.keys()) <= {2}) and survivors > 0     # = "every survivor has min_l g_l == 2"
    # NOTE: this is min_l g_l == 2 at every survivor, i.e. g_true <= 2 (an upper bound), NOT g = 2.
    # The g_true >= 2 half is PART 1 (symbolic) + PART 2 (exact residual); see
    # verify_120deg_conjoined_certificate_v1.py for the conjoined g = 2 certificate.
    print(f"  [{tag}] p={p:>5} n={n:>5} cells={len(reps):>4} | "
          f"g-dist(survivors)={dict(sorted(dist.items()))} census[V=0]={zero} rep={rep} | "
          f"{'ALL g<=2' if alllaw else 'NOT all g<=2: '+str(nonlaw[:6])} | {dt:.1f}s")
    return {"p": p, "n": n, "cells": len(reps), "dist": dist, "zero": zero,
            "rep": rep, "nonlaw": nonlaw, "all_g_le_2": alllaw, "secs": dt}

# ---------- controls: plants through the SAME deg_gcd routine over F_l ----------
def plant_check():
    # l == 1 mod 12 so F_l contains i=sqrt(-1) and a primitive cube root zeta3.
    l = 157
    while not (core.is_prime(l) and (l-1) % 12 == 0): l += 1
    i0 = core.tonelli((l-1) % l, l)                 # sqrt(-1) in F_l
    w  = primitive_root_of_order(3, l)              # zeta3 in F_l  (its conj is w^2)
    w2 = w*w % l
    # Weil numbers of norm 13 (as in the gate's pinned plants).  conj: i -> -i.
    alpha = (3 + 2*i0) % l; ca = (3 - 2*i0) % l       # alpha, conj(alpha)
    beta  = (2 + 3*i0) % l; cb = (2 - 3*i0) % l       # beta,  conj(beta)
    def poly_from_roots(rs):
        P = [1]
        for rt in rs:
            Q = [0]*(len(P)+1)
            for idx, c in enumerate(P):
                Q[idx]   = (Q[idx]   - c*rt) % l      # multiply by (T - rt)
                Q[idx+1] = (Q[idx+1] + c) % l
            P = Q
        return P
    A = poly_from_roots([alpha, w*alpha % l, (-ca) % l, (-w2*ca) % l])   # {a, z3 a, -conj a, -z3bar conj a}
    B = poly_from_roots([alpha, beta, (-ca) % l, (-cb) % l])            # {a, b, -conj a, -conj b}
    U = poly_from_roots([alpha, (-ca) % l, alpha, (-ca) % l])           # {a, -conj a, a, -conj a}
    Z = [169 % l, 0, (-13) % l, 0, 1]                                    # T^4 - 13 T^2 + 169
    def gof(P):
        wk = [pow(w, k, l) for k in range(len(P))]
        Pz = [P[k]*wk[k] % l for k in range(len(P))]
        return deg_gcd(P, Pz, l)
    e1A = (-A[3]) % l                                                    # sanity: PLANT-A e1 != 0 ; PLANT-Z e1 == 0
    res = {"PLANT-A(want2)": gof(A), "PLANT-B(want0)": gof(B),
           "PLANT-U1(want0)": gof(U), "PLANT-Z(want2)": gof(Z),
           "PLANT-Z e1(want0)": (-Z[3]) % l}
    ok = res["PLANT-A(want2)"] == 2 and res["PLANT-B(want0)"] == 0 and \
         res["PLANT-U1(want0)"] == 0 and res["PLANT-Z(want2)"] == 2 and res["PLANT-Z e1(want0)"] == 0
    print("CONTROLS (deg_gcd over F_%d):" % l, res, "->", "ALL FIRE" if ok else "*** FAIL ***")
    return ok

if __name__ == "__main__":
    import json
    print("=== C-PLANTS ==="); assert plant_check(), "plant controls failed -> HALT"
    IN_P = (43, 67, 79, 127, 163, 211, 547)
    S_P  = (823, 907, 967, 991, 1051, 1303, 1831, 2143, 2251, 2503)
    C_P  = (577, 733, 1237, 1249, 1669)
    out = {"freeze_sha256": "a964f246b87fbe302b4740c3123a40a25ff0376b60cc45f8c3ef14d3c23c9fdf",
           "IN": [], "S": [], "C": []}
    print("\n=== IN-SAMPLE I (validation: law should be exact here) ===")
    for p in IN_P:
        r = run_prime(p, "IN"); out["IN"].append(r)
    print("\n=== STRATUM S (PRIMARY, out-of-sample) ===")
    for p in S_P:
        r = run_prime(p, "S "); out["S"].append(r)
    print("\n=== STRATUM C (cross-stratum control, p==1 mod 12) ===")
    for p in C_P:
        r = run_prime(p, "C "); out["C"].append(r)
    with open("RESULT_n1_120deg_exact_v1.json", "w") as f:
        json.dump(out, f, indent=1)
    def verdict(rows):
        done = [r for r in rows if r]
        return f"{sum(1 for r in done if r['all_g_le_2'])}/{len(done)} primes ALL g<=2" + \
               ("" if len(done)==len(rows) else f" ({len(rows)-len(done)} ABSTAINED)")
    print("\n=== VERDICT ===")
    print("  IN-SAMPLE:", verdict(out["IN"]))
    print("  STRATUM S:", verdict(out["S"]), " <-- PRIMARY")
    print("  STRATUM C:", verdict(out["C"]))
