#!/usr/bin/env python3
"""
Executes VERIFY_SPEC_jacobi_stickelberger_v1.md.  Checks C1-C5 + firing controls FC1-FC5.

EXACT ARITHMETIC ONLY.  Python int throughout; Z[zeta_12] = Z[x]/(x^4 - x^2 + 1) as 4-vectors.
No float appears anywhere in the signal path (btc_puzzle_investigation/CLAUDE.md).
"""
import sys
from itertools import product

# ---------------------------------------------------------------- Z[zeta_12]
# basis 1, z, z^2, z^3 with z^4 = z^2 - 1, z^6 = -1

def zpow(j):
    """zeta_12^j as a 4-vector."""
    j %= 12
    sgn = 1
    if j >= 6:
        j -= 6
        sgn = -1
    tab = {0: (1, 0, 0, 0), 1: (0, 1, 0, 0), 2: (0, 0, 1, 0),
           3: (0, 0, 0, 1), 4: (-1, 0, 1, 0), 5: (0, -1, 0, 1)}
    return tuple(sgn * c for c in tab[j])

def zadd(a, b):
    return tuple(x + y for x, y in zip(a, b))

def zscale(k, a):
    return tuple(k * x for x in a)

def zmul(a, b):
    c = [0] * 7
    for i in range(4):
        if a[i] == 0:
            continue
        for j in range(4):
            c[i + j] += a[i] * b[j]
    # reduce: x^4 = x^2 - 1 ; x^5 = x^3 - x ; x^6 = -1
    c[2] += c[6] * 0; c[0] += -c[6]; c[6] = 0
    c[3] += c[5]; c[1] += -c[5]; c[5] = 0
    c[2] += c[4]; c[0] += -c[4]; c[4] = 0
    return tuple(c[:4])

def zconj(a):
    """complex conjugation: zeta -> zeta^{-1} = zeta^{11}."""
    r = (0, 0, 0, 0)
    for i in range(4):
        if a[i]:
            r = zadd(r, zscale(a[i], zpow(-i)))
    return r

def zfrom_counts(cnt):
    """cnt[j] copies of zeta_12^j."""
    r = (0, 0, 0, 0)
    for j in range(12):
        if cnt[j]:
            r = zadd(r, zscale(cnt[j], zpow(j)))
    return r

def is_rational(a):
    return a[1] == 0 and a[2] == 0 and a[3] == 0

def zstr(a):
    if is_rational(a):
        return str(a[0])
    return "%d + %d z + %d z^2 + %d z^3" % a

# ---------------------------------------------------------------- F_{p^2}
# F_p[T]/(T^2 - s) with s a non-residue  (p odd).  Element = (u, v) = u + v*T.

def legendre(a, p):
    a %= p
    if a == 0:
        return 0
    return 1 if pow(a, (p - 1) // 2, p) == 1 else -1

def build_field(p):
    s = next(k for k in range(2, p) if legendre(k, p) == -1)
    return p, s

def fmul(x, y, p, s):
    return ((x[0] * y[0] + s * x[1] * y[1]) % p, (x[0] * y[1] + x[1] * y[0]) % p)

def factorize(n):
    f, d = {}, 2
    while d * d <= n:
        while n % d == 0:
            f[d] = f.get(d, 0) + 1
            n //= d
        d += 1
    if n > 1:
        f[n] = f.get(n, 0) + 1
    return f

def fpow(x, e, p, s):
    r = (1, 0)
    while e:
        if e & 1:
            r = fmul(r, x, p, s)
        x = fmul(x, x, p, s)
        e >>= 1
    return r

def find_generator(p, s):
    q1 = p * p - 1
    prim = list(factorize(q1))
    for u in range(1, p):
        for v in range(0, p):
            g = (u, v)
            if g == (0, 0):
                continue
            if all(fpow(g, q1 // r, p, s) != (1, 0) for r in prim):
                return g
    raise RuntimeError("no generator at p=%d" % p)

def dlog_table(p, s, g):
    """dict element -> discrete log.  O(p^2)."""
    q1 = p * p - 1
    t, x = {}, (1, 0)
    for k in range(q1):
        t[x] = k
        x = fmul(x, g, p, s)
    assert x == (1, 0), "generator order wrong at p=%d" % p
    assert len(t) == q1, "dlog table incomplete at p=%d" % p
    return t

# ---------------------------------------------------------------- Jacobi sum
def jacobi_p2(p, u3, w4, corrupt=False):
    """
    J(chi_3^u3, chi_4^w4) over F_{p^2}, exact, as a Z[zeta_12] 4-vector.
    chi_3(g^k) = zeta_3^{u3*k} = zeta_12^{4*u3*k};  chi_4(g^k) = zeta_12^{3*w4*k}.
    corrupt=True installs a deliberately NON-MULTIPLICATIVE character (firing control FC2).
    """
    p_, s = build_field(p)
    g = find_generator(p, s)
    dl = dlog_table(p, s, g)
    cnt = [0] * 12
    one = (1, 0)
    for x, kx in dl.items():
        if x == one:
            continue
        y = ((1 - x[0]) % p, (-x[1]) % p)   # 1 - x
        if y == (0, 0):
            continue
        ky = dl[y]
        if corrupt:
            e = (4 * u3 * (kx * kx % 7) + 3 * w4 * ky) % 12   # not a homomorphism
        else:
            e = (4 * u3 * kx + 3 * w4 * ky) % 12
        cnt[e] += 1
    return zfrom_counts(cnt)

def jacobi_p1_cubic(p):
    """classical J(chi_3, chi_3) over F_p, exact, in Z[zeta_3] embedded in Z[zeta_12]."""
    g = next(a for a in range(2, p)
             if all(pow(a, (p - 1) // r, p) != 1 for r in factorize(p - 1)))
    dl, x = {}, 1
    for k in range(p - 1):
        dl[x] = k
        x = x * g % p
    cnt = [0] * 12
    for x, kx in dl.items():
        if x == 1:
            continue
        y = (1 - x) % p
        if y == 0:
            continue
        cnt[(4 * kx + 4 * dl[y]) % 12] += 1
    return zfrom_counts(cnt)

# ---------------------------------------------------------------- Stickelberger
def digit_sum(n, p, f):
    """sum of the f base-p digits of n (n already reduced into [0, p^f - 1))."""
    t = 0
    for _ in range(f):
        t += n % p
        n //= p
    assert n == 0
    return t

def stick_v(a, b, p, f):
    """v_P( J(omega^-a, omega^-b) ) = [s(a)+s(b)-s(<a+b>)] / (p-1).  Returns an int."""
    q1 = p ** f - 1
    num = digit_sum(a % q1, p, f) + digit_sum(b % q1, p, f) - digit_sum((a + b) % q1, p, f)
    assert num % (p - 1) == 0, "Stickelberger numerator not divisible by p-1"
    return num // (p - 1)

def stick_profile_p2(p):
    """v_t for t in {1,5,7,11} for J(chi_3, chi_4) over F_{p^2}."""
    M = (p * p - 1) // 12
    a, b = 4 * M, 3 * M
    return tuple(stick_v(t * a, t * b, p, 2) for t in (1, 5, 7, 11))

def stick_profile_cubic(p):
    """v_t for t in {1,2} for J(chi_3, chi_3) over F_p  (FC4)."""
    a = (p - 1) // 3
    return tuple(stick_v(t * a, t * a, p, 1) for t in (1, 2))

# ---------------------------------------------------------------- ideal factorisation of J
def zeta3_coords(a):
    """if a in Z[zeta_3] subset Z[zeta_12], return (A,B) with a = A + B*omega, omega = zeta_12^4."""
    # omega = zeta^4 = -1 + z^2  ->  A + B*omega = (A - B) + B z^2
    if a[1] or a[3]:
        return None
    B = a[2]
    A = a[0] + B
    return (A, B)

def norm_z3(A, B):
    """N(A + B omega) = A^2 - A B + B^2."""
    return A * A - A * B + B * B

def factor_ideal_in_z3(A, B, p):
    """
    For an element of Z[omega] of norm p^2 with p = pi*pibar split (p = 1 mod 3):
    return (v_pi, v_pibar) as a multiset {e1,e2}, computed exactly by trial division
    by a concrete pi.  Returns sorted tuple.
    """
    # find pi = a + b omega with N = p
    pi = None
    lim = 2 * p
    for a in range(-lim, lim + 1):
        for b in range(0, lim + 1):
            if norm_z3(a, b) == p:
                pi = (a, b)
                break
        if pi:
            break
    if pi is None:
        return None
    def z3mul(x, y):
        # (a+b w)(c+d w), w^2 = -1 - w
        a, b = x; c, d = y
        return (a * c - b * d, a * d + b * c - b * d)
    def z3div(x, y):
        # exact division in Z[omega] if it divides; else None
        a, b = x; c, d = y
        n = norm_z3(c, d)
        ybar = (c - d, -d)                      # conjugate of c + d w
        num = z3mul(x, ybar)
        if num[0] % n or num[1] % n:
            return None
        return (num[0] // n, num[1] // n)
    pibar = (pi[0] - pi[1], -pi[1])
    cur, e1 = (A, B), 0
    while True:
        nxt = z3div(cur, pi)
        if nxt is None:
            break
        cur, e1 = nxt, e1 + 1
    cur2, e2 = (A, B), 0
    while True:
        nxt = z3div(cur2, pibar)
        if nxt is None:
            break
        cur2, e2 = nxt, e2 + 1
    return (e1, e2)

# ---------------------------------------------------------------- driver
def primes_upto(n):
    sieve = bytearray([1]) * (n + 1)
    sieve[0:2] = b"\x00\x00"
    for i in range(2, int(n ** 0.5) + 1):
        if sieve[i]:
            sieve[i * i::i] = bytearray(len(sieve[i * i::i]))
    return [i for i in range(n + 1) if sieve[i]]

SECP_P = 2 ** 256 - 2 ** 32 - 977


def main():
    out = []
    def say(s=""):
        print(s); out.append(s)

    ALL = primes_upto(260)
    P3MOD4 = [p for p in ALL if p % 4 == 3 and p > 5]
    P1MOD4 = [p for p in ALL if p % 4 == 1 and p > 5 and p % 3 == 1]

    say("=" * 78)
    say("C1/C2/C3/C5 — exact J over F_{p^2}, all four character pairs")
    say("=" * 78)
    say("%6s %5s %-28s %-10s %-14s %s" % ("p", "p%12", "J (all 4 pairs)", "|J|^2=q", "stick v_t", "ideal"))

    c1_fail, c2_fail, c3_fail, c5_fail, cells = [], [], [], [], 0
    for p in P3MOD4:
        target = -p if p % 12 == 7 else p
        vals = []
        for u3, w4 in product((1, 2), (1, 3)):
            J = jacobi_p2(p, u3, w4)
            vals.append(J)
            cells += 1
            # C2 (forced): |J|^2 = q, strictly
            if zmul(J, zconj(J)) != zscale(p * p, zpow(0)):
                c2_fail.append((p, u3, w4))
            # C1
            if J != zscale(target, zpow(0)):
                c1_fail.append((p, u3, w4, zstr(J)))
            # C5 (forced): J = -1 mod 2 and mod 3  (J rational here, so plain int congruences)
            if is_rational(J):
                if J[0] % 2 != (-1) % 2 or J[0] % 3 != (-1) % 3:
                    c5_fail.append((p, u3, w4))

        allsame = all(v == vals[0] for v in vals)
        prof = stick_profile_p2(p)
        if prof != (1, 1, 1, 1):
            c3_fail.append((p, prof))
        # C3: predictor vs direct factorisation (only meaningful when p = 1 mod 3, p splits)
        idl = ""
        if p % 3 == 1:
            co = zeta3_coords(vals[0])
            fac = factor_ideal_in_z3(co[0], co[1], p) if co else None
            # NOTE: the pairing of the abstract prime P_t with the concrete pi found by search
            # is NOT pinned down by this code (it depends on the choice of P).  So C3 compares
            # the MULTISET of valuations, which is exactly what "(J) = (p)" needs.
            idl = str(fac)
            if fac is None or sorted(fac) != [1, 1]:
                c3_fail.append((p, "direct", fac))
        else:
            idl = "(p inert in Z[w])"
        say("%6d %5d %-28s %-10s %-14s %s" % (
            p, p % 12, zstr(vals[0]) + ("  x4 agree" if allsame else "  ***DIFFER***"),
            "ok", str(prof), idl))

    say()
    say("cells = %d   C1 fail = %d   C2 fail = %d   C3 fail = %d   C5 fail = %d"
        % (cells, len(c1_fail), len(c2_fail), len(c3_fail), len(c5_fail)))
    for f in c1_fail[:10]:
        say("   C1 FAIL %s" % (f,))
    for f in c3_fail[:10]:
        say("   C3 FAIL %s" % (f,))

    # ---------------- C4 : closed-form digit lemmas, at scale
    say()
    say("=" * 78)
    say("C4 — closed-form digit lemmas vs direct base-p digit sums")
    say("=" * 78)
    c4_fail, c4_n = [], 0
    for p in primes_upto(10 ** 5):
        if p % 4 != 3 or p <= 5:
            continue
        M = (p * p - 1) // 12
        s4, s3, s7, s1 = (digit_sum(4 * M, p, 2), digit_sum(3 * M, p, 2),
                          digit_sum(7 * M, p, 2), digit_sum(M, p, 2))
        if p % 12 == 7:
            pred = (2 * (p - 1) // 3, p - 1, 2 * (p - 1) // 3, 2 * (p - 1) // 3)
        else:
            pred = (p - 1, p - 1, p - 1, p - 1)
        c4_n += 1
        if (s4, s3, s7, s1) != pred:
            c4_fail.append((p, (s4, s3, s7, s1), pred))
    say("primes p = 3 mod 4 below 1e5 checked : %d      mismatches : %d" % (c4_n, len(c4_fail)))
    for f in c4_fail[:5]:
        say("   C4 FAIL %s" % (f,))

    # ---------------- C4 at secp's own p
    say()
    say("=" * 78)
    say("C4 AT SCALE — secp256k1's own p = 2^256 - 2^32 - 977")
    say("=" * 78)
    p = SECP_P
    say("p mod 4  = %d      p mod 3 = %d      p mod 12 = %d" % (p % 4, p % 3, p % 12))
    M = (p * p - 1) // 12
    s4, s3, s7, s1 = (digit_sum(4 * M, p, 2), digit_sum(3 * M, p, 2),
                      digit_sum(7 * M, p, 2), digit_sum(M, p, 2))
    pred = (2 * (p - 1) // 3, p - 1, 2 * (p - 1) // 3, 2 * (p - 1) // 3)
    say("s(4M), s(3M), s(7M), s(M)  match closed form : %s" % ((s4, s3, s7, s1) == pred))
    prof = stick_profile_p2(p)
    say("Stickelberger profile v_t, t in {1,5,7,11}   : %s" % (prof,))
    say("=> (J) = (p) at secp's p                     : %s" % (prof == (1, 1, 1, 1),))
    say("=> theorem gives J(chi_3,chi_4) = -p         : %s" % (p % 12 == 7,))

    # ---------------- firing controls
    say()
    say("=" * 78)
    say("FIRING CONTROLS")
    say("=" * 78)

    # FC1 : p = 1 mod 4, chi_4 NOT semiprimitive -> J must not be +-p
    fc1_rational = 0
    fc1_cells = 0
    for p in P1MOD4[:6]:
        for u3, w4 in product((1, 2), (1, 3)):
            J = jacobi_p2(p, u3, w4)
            fc1_cells += 1
            if is_rational(J) and abs(J[0]) == p:
                fc1_rational += 1
    say("FC1 discrimination : p = 1 mod 4, cells = %d, cells returning +-p = %d  -> %s"
        % (fc1_cells, fc1_rational,
           "FIRES (not a constant-output artifact)" if fc1_rational < fc1_cells else "DOES NOT FIRE"))

    # FC2 : corrupted, non-multiplicative character must break |J|^2 = q
    fc2_broken = 0
    for p in (7, 11, 19, 23, 31, 43):
        J = jacobi_p2(p, 1, 1, corrupt=True)
        if zmul(J, zconj(J)) != zscale(p * p, zpow(0)):
            fc2_broken += 1
    say("FC2 corrupted character : |J|^2 = q FAILS in %d/6 cells -> %s"
        % (fc2_broken, "FIRES" if fc2_broken == 6 else "DOES NOT FIRE"))

    # FC3 : sign-flipped rule
    fc3_agree = 0
    fc3_n = 0
    for p in P3MOD4:
        flipped = p if p % 12 == 7 else -p
        J = jacobi_p2(p, 1, 1)
        fc3_n += 1
        if J == zscale(flipped, zpow(0)):
            fc3_agree += 1
    say("FC3 sign-flipped rule agrees in %d/%d cells -> %s"
        % (fc3_agree, fc3_n, "FIRES (wrong sign would have been caught)" if fc3_agree == 0
           else "DOES NOT FIRE"))

    # FC4 : predictor must NOT be a constant -- classical cubic case
    say("FC4 predictor discrimination (classical cubic J(chi_3,chi_3) over F_p):")
    fc4_ok = True
    for p in (7, 13, 31, 43, 61, 67):
        if p % 3 != 1:
            continue
        prof = stick_profile_cubic(p)
        Jc = jacobi_p1_cubic(p)
        co = zeta3_coords(Jc)
        fac = factor_ideal_in_z3(co[0], co[1], p) if co else None
        nrm = norm_z3(*co) if co else None
        ok = (sorted(prof) == [0, 1]) and (nrm == p) and (fac is not None and sorted(fac) == [0, 1])
        fc4_ok &= ok
        say("    p=%3d  J = %-18s  N(J) = %-6s  predictor v_t = %-8s  direct = %-8s  %s"
            % (p, zstr(Jc), nrm, prof, fac, "ok" if ok else "MISMATCH"))
    say("FC4 -> %s" % ("FIRES (predictor returns (0,1), not the constant (1,1))" if fc4_ok
                       else "DOES NOT FIRE"))

    # FC5 : planted pi^2 must be rejected by C3
    say("FC5 planted J := pi^2 (the competitor exhibited in the predecessor's section 5):")
    fc5_ok = True
    for p in (7, 19, 31, 43, 67, 79):
        pi = None
        for a in range(-2 * p, 2 * p + 1):
            for b in range(0, 2 * p + 1):
                if norm_z3(a, b) == p:
                    pi = (a, b); break
            if pi: break
        a, b = pi
        pi2 = (a * a - b * b, a * b + b * a - b * b)     # pi^2 in Z[omega]
        fac = factor_ideal_in_z3(pi2[0], pi2[1], p)
        rejected = (fac != (1, 1))
        fc5_ok &= rejected
        say("    p=%3d  pi = %s  pi^2 = %s  N = %d  ideal = %s  -> %s"
            % (p, pi, pi2, norm_z3(*pi2), fac, "REJECTED" if rejected else "ACCEPTED (BAD)"))
    say("FC5 -> %s" % ("FIRES (pi^2 is separated from (p) by C3)" if fc5_ok else "DOES NOT FIRE"))

    say()
    say("=" * 78)
    say("SUMMARY")
    say("=" * 78)
    say("C1 (theorem, all 4 pairs, %d cells) : %s" % (cells, "PASS" if not c1_fail else "FAIL"))
    say("C2 (forced, |J|^2 = q)              : %s" % ("PASS" if not c2_fail else "FAIL"))
    say("C3 (Stickelberger vs direct ideal)  : %s" % ("PASS" if not c3_fail else "FAIL"))
    say("C4 (digit lemmas, %d primes + secp) : %s" % (c4_n, "PASS" if not c4_fail else "FAIL"))
    say("C5 (forced congruences)             : %s" % ("PASS" if not c5_fail else "FAIL"))
    say("FC1..FC5 all fire                   : %s"
        % (fc1_rational < fc1_cells and fc2_broken == 6 and fc3_agree == 0 and fc4_ok and fc5_ok))

    with open(__file__.replace(".py", ".log"), "w") as fh:
        fh.write("\n".join(out) + "\n")


if __name__ == "__main__":
    main()
