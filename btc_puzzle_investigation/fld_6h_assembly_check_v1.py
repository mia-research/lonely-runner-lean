#!/usr/bin/env python3
"""
fld_assembly_check_v1.py -- Does the (dagger)-route ALREADY prove |FLD| = 6 h(-p)?

Exact integers only. Assembles BOTH routes and cross-checks every link:

  Route A (flap-lemmas v3 + dagger proof of (dagger)):
     S' = A + C                          [flap-lemmas PROVED]
     A  = sum_{s=1}^{H} chi2(s) = (2-chi2(2)) h        [Dirichlet, PROVED]
     C' - C = 3h        (dagger)         [dagger PROVED + reviewed]
     C + C' = A                          [flap-lemmas PROVED]
   =>  S' = (3h/2)(1 - chi2(2))          [assembly]
   =>  FLD = 2 S+ = (3h)(1 - chi2(2))    [master: FLD=2 S+ PROVED]
   =>  |FLD| = 6h at p=19 mod24, 0 else.  *** No L1 used. ***

  The ONE bridge joining the geometric FLD to the arithmetic (dagger) route:
     S+  (geometric, sum over sigma(x)=+1 of chi2(x))
         ==?  S'  (arithmetic, flap-lemmas T+)          <-- must hold
  and L1 as a COROLLARY (not an input):
     |S+| ==? F4 = sum_{p/4<a<p/2} chi2(a)

Everything is an exact integer identity. A false "already proved" reading dies here.
"""
import sys
sys.path.insert(0, "/Users/trentpalelei/Desktop/Math Ex/btc_puzzle_investigation")
from sympy import isprime, primitive_root
from _sigma_chi2_scan_v1 import chi2_table, build, sigma_fn


def classnum_neg(p):
    """h(-p), p = 3 mod 4 prime, fundamental disc D=-p: count reduced forms."""
    D = -p; h = 0; a = 1
    while 3 * a * a <= p:
        for b in range(-a, a + 1):
            num = b * b - D
            if num % (4 * a):
                continue
            c = num // (4 * a)
            if c < a:
                continue
            if (abs(b) == a or a == c) and b < 0:
                continue
            h += 1
        a += 1
    return h


def geometric_side(p):
    """Return (FLD, S_plus, S_minus) from the geometric Cap-Law sigma, or None."""
    chi2 = chi2_table(p)
    eis, eps, beta, R1, R2, DET = build(p)
    sig, orient = sigma_fn(p, eis, eps, R1, R2, DET)
    if sig is None:
        return None
    FLD = Splus = Sminus = 0
    for x in range(p):
        s = sig(x)
        if s == 0:
            continue
        c = chi2(x)
        FLD += s * c
        if s == 1:
            Splus += c
        else:
            Sminus += c
    return FLD, Splus, Sminus, orient


def arithmetic_side(p, chi2):
    """rho-route quantities (p = 7 mod 12). Returns dict."""
    H = (p - 1) // 2
    g = primitive_root(p)
    rho = pow(g, (p - 1) // 6, p)          # primitive 6th root
    assert pow(rho, 6, p) == 1 and pow(rho, 3, p) == p - 1 and pow(rho, 2, p) != 1
    # T+ (flap-lemmas):  s in [1,H] : rho*s mod p in [(p+1)/2, H+s]
    lo = (p + 1) // 2
    Sprime = 0
    A = 0
    C = 0
    Cp = 0
    for s in range(1, H + 1):
        cs = chi2(s)
        A += cs
        r = (rho * s) % p
        if lo <= r <= H + s:
            Sprime += cs
        if r > s:
            Cp += cs
        elif r < s:
            C += cs
        # r == s impossible for s in [1,H] (rho != 1)
    return {'H': H, 'rho': rho, 'Sprime': Sprime, 'A': A, 'C': C, 'Cp': Cp}


def F4(p, chi2):
    return sum(chi2(a) for a in range(p // 4 + 1, (p + 1) // 2))  # p/4 < a < p/2


def main():
    lo = int(sys.argv[1]) if len(sys.argv) > 1 else 100
    hi = int(sys.argv[2]) if len(sys.argv) > 2 else 3000
    fails = []
    n19 = n7 = n1mod4 = 0
    # link tallies
    t = {k: [0, 0] for k in
         ['FLD=2S+', 'S+=S\'(|.|)', 'A=(2-x2)h', "C+C'=A", "S'=A+C",
          "C'-C=3h", "S'=(3h/2)(1-x2)", '|FLD|=6h@19', 'FLD=0 off19', '|S+|=F4', 'sign S+=S\'']}

    def rec(key, cond):
        t[key][0] += 1 if cond else 0
        t[key][1] += 1

    print(f"# p=1 mod6 primes in [{lo},{hi}). Exact-integer assembly of |FLD|=6h via the (dagger) route.")
    print("# {:>6} {:>4} {:>6} {:>6} {:>4} {:>5} {:>6} {:>13} {:>6} {:>6} {:>6} {:>5} {:>6}".format(
          'p', 'm24', 'FLD', '2S+', 'h', '6h', "Sp", '(3h/2)(1-x2)', 'A', 'C', 'Cp', 'F4', 'x2(2)'))
    for p in range(lo, hi):
        if p % 6 != 1 or not isprime(p) or p == 7:
            continue
        chi2 = chi2_table(p)
        geo = geometric_side(p)
        if geo is None:
            continue
        FLD, Splus, Sminus, orient = geo
        x22 = chi2(2)
        rec('FLD=2S+', FLD == 2 * Splus)

        m24 = p % 24
        if p % 4 == 1:                       # p = 1 or 13 mod 24
            n1mod4 += 1
            rec('FLD=0 off19', FLD == 0)
            print(f"  {p:>6} {m24:>4} {FLD:>6} {2*Splus:>6} {'-':>4} {'-':>5} "
                  f"{'-':>6} {'-':>13} {'-':>6} {'-':>6} {'-':>6} {'-':>5} {x22:>6}   (p=1 mod4)")
            continue

        # p = 3 mod 4 and 1 mod 3  => p = 7 mod 12
        h = classnum_neg(p)
        ari = arithmetic_side(p, chi2)
        Sprime, A, C, Cp = ari['Sprime'], ari['A'], ari['C'], ari['Cp']
        f4 = F4(p, chi2)
        target_Sprime = (3 * h * (1 - x22)) // 2   # (3h/2)(1-x2), integer since 1-x2 in {0,2}

        rec('A=(2-x2)h', A == (2 - x22) * h)
        rec("C+C'=A", C + Cp == A)
        rec("S'=A+C", Sprime == A + C)
        rec("C'-C=3h", Cp - C == 3 * h)
        rec("S'=(3h/2)(1-x2)", Sprime == target_Sprime)
        rec('S+=S\'(|.|)', abs(Splus) == abs(Sprime))
        rec('sign S+=S\'', Splus == Sprime)
        rec('|S+|=F4', abs(Splus) == abs(f4))

        if m24 == 19:
            n19 += 1
            ok = abs(FLD) == 6 * h
            rec('|FLD|=6h@19', ok)
            if not ok:
                fails.append(('|FLD|=6h', p, FLD, h))
        else:                                 # m24 == 7
            n7 += 1
            rec('FLD=0 off19', FLD == 0)
            if FLD != 0:
                fails.append(('FLD!=0 off19', p, FLD, h))

        print(f"  {p:>6} {m24:>4} {FLD:>6} {2*Splus:>6} {h:>4} {6*h:>5} {Sprime:>6} "
              f"{target_Sprime:>13} {A:>6} {C:>6} {Cp:>6} {f4:>5} {x22:>6}")

    print()
    print(f"# counts: p=19 mod24: {n19}   p=7 mod24: {n7}   p=1 mod4: {n1mod4}")
    print("# LINK TALLIES (hits/total):")
    for k, (a, b) in t.items():
        flag = "" if a == b else "   <-- MISMATCH"
        print(f"   {k:<20} {a:>4}/{b:<4}{flag}")
    if fails:
        print("\nFAILURES:")
        for f in fails:
            print("  ", f)
    else:
        print("\nALL LINKS CLEAN on this range.")


if __name__ == "__main__":
    main()
