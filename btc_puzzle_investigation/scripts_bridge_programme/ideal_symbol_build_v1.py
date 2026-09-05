#!/usr/bin/env python3
"""IDEAL-LEVEL OBJECT BUILD (not yet an inferential test -- no association statistic is computed here).

Object: the curve has CM by Z[omega].  p = pi*pibar (Cornacchia, 4p=t^2+3v^2), and n splits in Z[omega]
as n = nu*nubar with nu = 1-pi (record's cubic-bridge setup, RESULT_cubic_sextic_bridge_v1).
Since 3|n-1 (L3) the quotient Z[omega]/(nu) = F_n, so pi mod nu is an element of F_n and, because
n == 1 mod ell, it HAS an ell-th power residue symbol.

    chi_ell(p mod n) = chi_ell(pi mod nu) * chi_ell(pibar mod nu)          (*)

(*) is FORCED by p = pi*pibar.  The rational symbol we already bounded (marginal + conditional MI)
is the PRODUCT; the two factor symbols are strictly finer.  An ideal-level relation between the
factors can cancel in the product -- this is the concrete wash-out mechanism.

THIS SCRIPT ONLY: builds the factor symbols and checks FORCED identities (instrument validity).
No inference. Any association test comes AFTER an experiment-designer prereg (CLAUDE.md section 2).
Exact integers throughout."""
import random
from collections import Counter
exec(open('ell_mi_v3f.py').read().split('# ==== MACHINERY M0 ====')[0])  # is_prime, cornacchia3, lpr, expo

def omega_mod(nu_a, nu_b, n):
    """image of omega in Z[omega]/(nu) = F_n, where nu = nu_a + nu_b*omega.
    nu == 0  =>  omega == -nu_a / nu_b  (mod n)."""
    if nu_b % n == 0: return None
    return (-nu_a * pow(nu_b, -1, n)) % n

def elt_mod(a, b, om, n):
    """image of a + b*omega in F_n."""
    return (a + b * om) % n

def sym_exp(x, n, ell, zeta):
    """ell-th power residue symbol of x in F_n, as an exponent m with x^((n-1)/ell) = zeta^m."""
    x %= n
    if x == 0: return None
    val = pow(x, (n - 1) // ell, n); z = 1
    for m in range(ell):
        if z == val: return m
        z = z * zeta % n
    return None

def build(ell, target, bits, rnd, cap=2000000):
    """one uniformly-chosen prime-order twist per p (rule N5, same as the marginal/conditional probes)."""
    rows = []; tries = 0
    while len(rows) < target and tries < cap:
        tries += 1
        p = rnd.randrange(1 << (bits - 1), 1 << bits); p -= (p % ell) - 1
        if p % 2 == 0: p += ell
        if p % ell != 1 or p % 3 != 1 or p < 7 or not is_prime(p, bases=(2, 3, 5, 7, 11, 13)): continue
        rep = cornacchia3(p, rnd)
        if not rep: continue
        a, b = rep
        if a * a + 3 * b * b != p: continue
        # pi = a + b*(1+2w)? -- use the record's convention: 4p = t^2+3v^2, pi = (t+v)/2 + v*omega
        cand = []
        for t in (a + 3*b, -(a + 3*b), a - 3*b, -(a - 3*b)):
            n = p + 1 - t
            if n <= 3 or n % ell != 1 or n % 3 != 1 or t == 1: continue
            if not is_prime(n, bases=(2, 3, 5, 7, 11, 13)): continue
            if p % n == 0: continue
            cand.append((t, n))
        if not cand: continue
        t, n = cand[rnd.randrange(len(cand))]
        # v from 4p = t^2 + 3v^2
        r = 4*p - t*t
        if r <= 0 or r % 3: continue
        v2 = r // 3; v = isqrt(v2)
        if v*v != v2: continue
        for vs in (v, -v):                       # pi = (t+vs)/2 + vs*omega must be an algebraic integer
            if (t + vs) % 2: continue
            pa, pb = (t + vs) // 2, vs           # pi   = pa + pb*w
            qa, qb = pa - pb, -pb                # pibar = conj(pi) = (pa - pb) - pb*w   (since conj(w)=-1-w)
            na, nb = 1 - pa, -pb                 # nu   = 1 - pi
            if (na*na - na*nb + nb*nb) != n:     # N(nu) = n  (norm of x+y*w is x^2-xy+y^2)
                continue
            om = omega_mod(na, nb, n)
            if om is None: continue
            if (om*om + om + 1) % n != 0: continue          # omega must be a primitive cube root mod n
            zn = pow(lpr(n), (n - 1) // ell, n)             # zeta_ell in F_n
            xpi = elt_mod(pa, pb, om, n); xpb = elt_mod(qa, qb, om, n)
            if xpi % n == 0 or xpb % n == 0: continue
            m_pi = sym_exp(xpi, n, ell, zn); m_pb = sym_exp(xpb, n, ell, zn)
            m_p  = sym_exp(p % n, n, ell, zn)                # the RATIONAL symbol (the product)
            if None in (m_pi, m_pb, m_p): continue
            rows.append(dict(p=p, n=n, t=t, v=vs, m_pi=m_pi, m_pb=m_pb, m_p=m_p,
                             xpi=xpi, xpb=xpb, om=om))
            break
    return rows

if __name__ == "__main__":
    print("=== IDEAL-LEVEL OBJECT: CM-factor symbols chi_ell(pi mod nu), chi_ell(pibar mod nu) ===")
    print("    (build + FORCED-identity checks only; no inference)\n")
    for ell in (5, 7, 11, 13):
        rnd = random.Random(31337)
        rows = build(ell, 400, 26, rnd)
        if not rows:
            print(f"  ell={ell}: NO INSTANCES"); continue
        # FORCED CHECK 1: chi(p) = chi(pi)*chi(pibar)  <=>  m_p == m_pi + m_pb (mod ell).  Must be 100%.
        ok1 = sum(1 for r in rows if (r['m_pi'] + r['m_pb']) % ell == r['m_p'])
        # FORCED CHECK 2: N(pi)=p and N(nu)=n structurally (already enforced); re-verify pi*pibar = p mod n
        ok2 = sum(1 for r in rows if (r['xpi'] * r['xpb'] - r['p']) % r['n'] == 0)
        # FORCED CHECK 3: omega^3 = 1, omega != 1 mod n
        ok3 = sum(1 for r in rows if pow(r['om'], 3, r['n']) == 1 and r['om'] % r['n'] != 1)
        N = len(rows)
        dpi = Counter(r['m_pi'] for r in rows); dp = Counter(r['m_p'] for r in rows)
        print(f"  ell={ell:>2} N={N:>4} | FORCED: chi(p)=chi(pi)chi(pibar) {ok1}/{N} | "
              f"pi*pibar=p mod n {ok2}/{N} | omega^3=1 {ok3}/{N}")
        print(f"        m_pi spread: {sorted(dpi.items())}")
        print(f"        m_p  spread: {sorted(dp.items())}")
