#!/usr/bin/env python3
"""verify_120deg_symbolic_factorization_v1.py

PART 1 of the exact 120-degree certificate (repairs CORRECTION_120deg_census_certification_direction_v1.md).

Instead of a resultant in Z[zeta_M] (M = lcm(N,3)) this EXHIBITS the common quadratic factor
symbolically, once, in the ring

        R = Z[e1, p, w] / (w^2 + w + 1)

with e1, p FREE INDETERMINATES.  Verifying that an exhibited D divides both L(T) and L(wT) is a
polynomial IDENTITY -- it is a lower bound on deg gcd, which is precisely the direction the
multi-modular census cannot certify.

Premises used (both graded [PROVED - FORCED] by ANALYSIS_n1_charpoly_collapse_v1.md section 1,
derived from the closure alpha -> -conj(alpha) / alpha -> conj(alpha) plus |alpha|^2 = p):
        e3 = eps * p * e1 ,   e4 = p^2 ,   eps = chi2(-1) = legendre(-1, p)
The ONE measured input is then e2, and the claim under test is a single relation between e2, e1, p.

EXACT INTEGER ARITHMETIC ONLY.  No float anywhere.
"""

# ---------------------------------------------------------------- ring R = Z[e1,p,w]/(w^2+w+1)
# element: dict {(i, j, k): c}  meaning  c * e1^i * p^j * w^k , with k in {0,1} after reduction.

def rnorm(d):
    return {m: c for m, c in d.items() if c != 0}

def radd(a, b):
    out = dict(a)
    for m, c in b.items():
        out[m] = out.get(m, 0) + c
    return rnorm(out)

def rneg(a):
    return {m: -c for m, c in a.items()}

def rsub(a, b):
    return radd(a, rneg(b))

def rmul(a, b):
    out = {}
    for (i1, j1, k1), c1 in a.items():
        for (i2, j2, k2), c2 in b.items():
            i, j, k, c = i1 + i2, j1 + j2, k1 + k2, c1 * c2
            if k >= 3:
                k -= 3                      # w^3 = 1
            if k == 2:
                # w^2 = -1 - w
                for kk, sgn in ((0, -1), (1, -1)):
                    m = (i, j, kk)
                    out[m] = out.get(m, 0) + sgn * c
                continue
            m = (i, j, k)
            out[m] = out.get(m, 0) + c
    return rnorm(out)

def const(c):
    return rnorm({(0, 0, 0): c})

E1 = {(1, 0, 0): 1}
P  = {(0, 1, 0): 1}
W  = {(0, 0, 1): 1}
W2 = rmul(W, W)                              # = -1 - w
ZERO = {}
ONE = const(1)

def rstr(a):
    if not a:
        return "0"
    parts = []
    for (i, j, k), c in sorted(a.items()):
        t = []
        if c != 1 or (i == j == k == 0):
            t.append(str(c))
        if i:
            t.append("e1" + ("^%d" % i if i > 1 else ""))
        if j:
            t.append("p" + ("^%d" % j if j > 1 else ""))
        if k:
            t.append("w" + ("^%d" % k if k > 1 else ""))
        parts.append("*".join(t))
    return " + ".join(parts)

# ---------------------------------------------------------------- polynomials in T over R
def pmul(A, B):
    C = [ZERO] * (len(A) + len(B) - 1)
    for i, a in enumerate(A):
        if not a:
            continue
        for j, b in enumerate(B):
            if not b:
                continue
            C[i + j] = radd(C[i + j], rmul(a, b))
    return C

def peq(A, B):
    n = max(len(A), len(B))
    for i in range(n):
        a = A[i] if i < len(A) else ZERO
        b = B[i] if i < len(B) else ZERO
        if rnorm(rsub(a, b)):
            return False
    return True

def subst_wT(A):
    """A(T) |-> A(w*T):  coefficient of T^k gets multiplied by w^k."""
    out = []
    wk = ONE
    for k, a in enumerate(A):
        out.append(rmul(a, wk))
        wk = rmul(wk, W)
    return out

# ---------------------------------------------------------------- the claim
def build(eps, e2_sign):
    """L (low->high) with e2 = e1^2 + e2_sign*p, e3 = eps*p*e1, e4 = p^2.
       Candidate common factor D = T^2 + w*e1*T + eps*p*w^2."""
    e1 = E1
    e2 = radd(rmul(E1, E1), rmul(const(e2_sign), P))
    e3 = rmul(const(eps), rmul(P, E1))
    e4 = rmul(P, P)
    L = [e4, rneg(e3), e2, rneg(e1), ONE]                 # T^4 - e1 T^3 + e2 T^2 - e3 T + e4
    D = [rmul(const(eps), rmul(P, W2)), rmul(W, E1), ONE]  # T^2 + w e1 T + eps p w^2
    Dbar = [rmul(const(eps), rmul(P, W)), rmul(W2, E1), ONE]
    return L, D, Dbar, e2

def report(eps):
    print("=" * 78)
    print("eps = chi2(-1) = %+d      (p = %s mod 4)" % (eps, "1" if eps == 1 else "3"))
    print("=" * 78)
    ok_any = False
    for e2_sign in (+1, -1):
        L, D, Dbar, e2 = build(eps, e2_sign)
        f1 = peq(pmul(D, Dbar), L)                       # L = D * Dbar ?
        Lw = subst_wT(L)
        # L(wT) should equal  w * (T^2 + e1 T + eps*p) * D
        cof = [rmul(const(eps), P), E1, ONE]
        f2 = peq(pmul([W], pmul(cof, D)), Lw)
        tag = "e2 = e1^2 %s p" % ("+" if e2_sign > 0 else "-")
        print("  %-16s :  L = D*Dbar  -> %-5s |  L(wT) = w*(T^2+e1*T+eps*p)*D -> %-5s   %s"
              % (tag, f1, f2, "BOTH HOLD" if (f1 and f2) else ""))
        if f1 and f2:
            ok_any = True
            print("      D    = " + " | ".join("T^%d: %s" % (i, rstr(c)) for i, c in enumerate(D)))
            print("      Dbar = " + " | ".join("T^%d: %s" % (i, rstr(c)) for i, c in enumerate(Dbar)))
            print("      => deg gcd(L(T), L(wT)) >= 2  UNCONDITIONALLY in e1, p  (D is monic, never degenerate)")
    return ok_any


def negative_control():
    """A control that must NOT fire: perturb e2 off the relation and confirm D stops dividing."""
    print("=" * 78)
    print("NEGATIVE CONTROL -- the identity must FAIL when e2 is off-relation")
    print("=" * 78)
    fired = []
    for eps in (+1, -1):
        for delta in (1, 2, -3):
            e1 = E1
            e2 = radd(radd(rmul(E1, E1), rmul(const(-eps), P)), const(delta))   # correct relation + delta
            e3 = rmul(const(eps), rmul(P, E1))
            e4 = rmul(P, P)
            L = [e4, rneg(e3), e2, rneg(e1), ONE]
            D = [rmul(const(eps), rmul(P, W2)), rmul(W, E1), ONE]
            Dbar = [rmul(const(eps), rmul(P, W)), rmul(W2, E1), ONE]
            holds = peq(pmul(D, Dbar), L)
            print("  eps=%+d  e2 = e1^2 %+d*p %+d  ->  L = D*Dbar : %s" % (eps, -eps, delta, holds))
            if holds:
                fired.append((eps, delta))
    print("  control verdict:", "PASS (no false divisor)" if not fired else "*** FAIL *** " + str(fired))
    return not fired


if __name__ == "__main__":
    r1 = report(-1)
    r2 = report(+1)
    ctl = negative_control()
    print("=" * 78)
    print("SYMBOLIC PART VERDICT:", "PASS" if (r1 and r2 and ctl) else "*** FAIL ***")
