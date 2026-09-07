"""
n=8 fibre core.  EXACT INTEGER ARITHMETIC ONLY -- no floats anywhere.

Setup (re-derived, see report):
  E = (e_1..e_7) distinct positive ints, gcd 1.  L = lcm(E), N = 8L.
  k in {1..N-1} written k = b + r*L with b in [0,L), r in Z/8.
  For runner e:  e*b = t_e*L + rem,  t_e = floor(e*b/L),  0 <= rem < L.
    e*k mod N = ((t_e + e*r) mod 8)*L + rem.
  Condition (e*k mod N) in [L,7L]:
      needs (t_e + e*r) mod 8 in {1..6}, OR ==7 with rem==0, OR ==0 with rem>=L (impossible).
  So a SUFFICIENT condition, uniform in rem, is
      (t_e + e*r) mod 8 not in {0,7}
   <=> r not in Sol(e,-t_e) u Sol(e,-(t_e+1)) = bad(e,t_e,8).
"""
from math import gcd

def lcm2(a, b):
    return a // gcd(a, b) * b

def L_of(E):
    l = 1
    for e in E:
        l = lcm2(l, e)
    return l

def sol(e, j, m=8):
    """{r in Z/m : e*r = j mod m}"""
    e %= m; j %= m
    return frozenset(r for r in range(m) if (e * r - j) % m == 0)

def bad(e, t, m=8):
    """bad(e,t,m) = Sol(e,-t) u Sol(e,-(t+1))"""
    return sol(e, -t, m) | sol(e, -(t + 1), m)

def t_of(e, b, L):
    """floor(e*b/L)  -- exact integer floor division"""
    return (e * b) // L

def sector(e, b, L):
    """T_e(b) = t_e(b) mod 8 = floor(8*frac(e*b/N)) with N=8L."""
    return ((e * b) // L) % 8

def blocked_non(E_non, b, L):
    s = set()
    for e in E_non:
        s |= bad(e, t_of(e, b, L))
    return s

def safe(E_non, b, L):
    return len(blocked_non(E_non, b, L)) < 8

def div_ok(E_div, b, L):
    """For e = 8e' in E_div: bad(e,t) = Z/8 if t mod 8 in {0,7} else empty.
       So the fibre is usable iff every divisible runner has t mod 8 in {1..6}."""
    for e in E_div:
        if ((e * b) // L) % 8 in (0, 7):
            return False
    return True

def split(E):
    return [e for e in E if e % 8 == 0], [e for e in E if e % 8 != 0]

def x0_bruteforce(E):
    """#{k in 1..N-1 : (e k mod N) in [L,7L] for all e}.  Exact ints."""
    L = L_of(E); N = 8 * L
    c = 0
    for k in range(1, N):
        ok = True
        for e in E:
            v = (e * k) % N
            if v < L or v > 7 * L:
                ok = False; break
        if ok:
            c += 1
    return c

def witness_from_fibre(E, b):
    """If b is div_ok and safe, return a k in 1..N-1 certified by the fibre argument."""
    L = L_of(E); N = 8 * L
    Ed, En = split(E)
    if not div_ok(Ed, b, L):
        return None
    blk = blocked_non(En, b, L)
    for r in range(8):
        if r in blk:
            continue
        k = b + r * L
        if k <= 0 or k >= N:
            continue
        if all(L <= (e * k) % N <= 7 * L for e in E):
            return k
    return None
