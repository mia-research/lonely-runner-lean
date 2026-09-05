#!/usr/bin/env python3
"""
Reproduce, from scratch, every number in the pasted analysis, and derive the
conditional rate directly from counts (no asserted normalization).

Checks:
  A. nu_analytic == nu_brute for ALL primes < 1200 (+ spot large primes), not <60.
  B. Reproduce the paste's twin COUNT sequence (161,551,962,3532,6064 at 1e4..1e6)
     by trying explicit enumeration conventions until one matches.
  C. Independently recompute the Euler-product constant C_Eis (target 2.06277).
  D. Derive P(n prime | p prime) DIRECTLY as twins/Fprime at each X -> kappa,
     with NO use of C_Eis. Report the scaling honestly.
"""
import math

def sieve(N):
    s = bytearray([1]) * (N + 1)
    s[0] = s[1] = 0
    for i in range(2, int(N**0.5) + 1):
        if s[i]:
            s[i*i::i] = bytearray(len(range(i*i, N + 1, i)))
    return s

def primes_upto(N):
    s = sieve(N)
    return [i for i in range(2, N + 1) if s[i]]

# ---------- A. nu formula check over a REAL range ----------
def nu_analytic(q):
    if q == 2: return 2
    if q == 3: return 6
    if q % 3 == 1: return 4*q - 4
    return 2

def nu_brute(q):
    nu = 0
    for a in range(q):
        for b in range(q):
            if (a*a - a*b + b*b) % q == 0 or ((a-1)*(a-1) - (a-1)*b + b*b) % q == 0:
                nu += 1
    return nu

def check_A():
    bad = []
    for q in primes_upto(1200):
        if nu_analytic(q) != nu_brute(q):
            bad.append(q)
    for q in [1999, 2003, 3001, 4999, 5003, 6997, 7001]:  # both residue classes, larger
        if nu_analytic(q) != nu_brute(q):
            bad.append(q)
    print(f"A. nu_analytic == nu_brute for all primes < 1200 and 7 spot primes to 7001: "
          f"{'OK, 0 mismatches' if not bad else 'MISMATCH at ' + str(bad)}")

# ---------- B. reproduce the paste's count sequence ----------
def twin_counts(Xs, conv):
    """conv in {'all','b3','bpos','fund'}. Returns {X: (twins, Fprime)}."""
    Xmax = max(Xs)
    s = sieve(Xmax + 4 * int(Xmax**0.5) + 10)   # N(pi-1) can exceed N(pi)
    out = {X: [0, 0] for X in Xs}
    Xs_sorted = sorted(Xs)
    bmax = int((4 * Xmax / 3) ** 0.5) + 2
    for b in range(-bmax, bmax + 1):
        if conv == 'b3' and b % 3 != 0:
            continue
        for a in range(-bmax - 1, bmax + 2):
            F = a*a - a*b + b*b
            if F < 2 or F > Xmax:
                continue
            if conv == 'bpos' and not (b > 0 or (b == 0 and a > 0)):
                continue
            if conv == 'fund':
                # one representative per associate class: pick canonical (a,b)
                # canonical = lexicographically max over the 6 units*{+-}? use: a>=b>0 style
                # simpler dedup: require 0 <= b, and a > b/2 ... use a>b>=0 or a>=0,b>0 wedge
                if not (a > 0 and 0 < b <= a):
                    continue
            if not s[F]:
                continue
            G = (a-1)*(a-1) - (a-1)*b + b*b
            for X in Xs_sorted:
                if F <= X:
                    out[X][1] += 1
                    if G >= 2 and s[G]:
                        out[X][0] += 1
    return out

def check_B():
    Xs = [10**4, 5*10**4, 10**5, 5*10**5, 10**6]
    target = {10**4: 161, 5*10**4: 551, 10**5: 962, 5*10**5: 3532, 10**6: 6064}
    print("\nB. reproduce paste twin counts (target: 161/551/962/3532/6064):")
    for conv in ['all', 'b3', 'bpos', 'fund']:
        res = twin_counts(Xs, conv)
        row = "  %-5s: " % conv + "  ".join(f"{res[X][0]}" for X in Xs)
        match = all(res[X][0] == target[X] for X in Xs)
        print(row + ("   <== MATCHES PASTE" if match else ""))
    return Xs

# ---------- C. independent Euler product ----------
def euler_C(qmax):
    """C_Eis = prod_q (1 - nu(q)/q^2)/(1-1/q)^2 (same product as the singular series)."""
    C = 1.0
    for q in primes_upto(qmax):
        C *= (1 - nu_analytic(q) / (q*q)) / (1 - 1/q)**2
    return C

def check_C():
    print("\nC. independent Euler product C_Eis (paste target 2.06277):")
    for qmax in [100, 1000, 10000, 100000, 500000]:
        print(f"  q <= {qmax:>7}: {euler_C(qmax):.8f}")

# ---------- D. conditional rate directly from counts ----------
def check_D(Xs):
    print("\nD. conditional P(n|p) = twins/Fprime DIRECTLY (no C_Eis), per convention:")
    for conv in ['all', 'b3']:
        res = twin_counts(Xs, conv)
        print(f"  convention '{conv}':")
        for X in Xs:
            tw, Fp = res[X]
            pcond = tw / Fp
            print(f"    X={X:>8}: twins={tw:>5} Fprime={Fp:>6}  P(n|p)={pcond:.4f}  "
                  f"kappa=P*ln X={pcond*math.log(X):.3f}")
    n = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141
    print(f"  ln(n) at secp = {math.log(n):.2f}")

if __name__ == "__main__":
    check_A()
    Xs = check_B()
    check_C()
    check_D(Xs)
