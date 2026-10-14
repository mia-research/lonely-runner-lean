"""Test a DERIVATION of the 2-adic cap table against brute force, uniformly in p.

Claim.  N = 8p, targets j = r + pt (t=0..3), covered iff jv mod N < p or > N-p.
Write rv mod N = p*q + s, 0 <= s < p, q in 0..7.  Block identity gives
    jv mod N = p*((q + tv) mod 8) + s.
Hence target t is covered  <=>  (q+tv) mod 8 == 0,  or  ((q+tv) mod 8 == 7 and s > 0).
Everything else follows from |{0,7}| = 2 and the orbit {tv mod 8 : t=0..3}.
"""
import sys
def brute(r, v, p):
    N = 8*p
    return frozenset(t for t in range(4)
                     if (( (r+p*t)*v) % N < p or ((r+p*t)*v) % N > N-p))
def derived(r, v, p):
    N = 8*p
    rv = (r*v) % N
    q, s = divmod(rv, p)
    ok = set()
    for t in range(4):
        m = (q + t*v) % 8
        if m == 0 or (m == 7 and s > 0): ok.add(t)
    return frozenset(ok)

for p in (31, 37, 43, 47, 53, 59, 61, 67, 71, 163):
    N, H = 8*p, 4*p
    bad = 0
    caps = {"8|v": set(), "v=4(8)": set(), "v=2(4)": set(), "odd": set()}
    types = {"odd": set(), "v=4(8)": set()}
    for v in range(1, H+1):
        if v % p == 0: continue
        key = ("8|v" if v % 8 == 0 else "v=4(8)" if v % 8 == 4
               else "v=2(4)" if v % 2 == 0 else "odd")
        for r in range(1, p+1):
            b, d = brute(r, v, p), derived(r, v, p)
            if b != d: bad += 1
            caps[key].add(len(b))
            if key in types and len(b) == 2:
                a = sorted(b); types[key].add("adjacent" if (a[1]-a[0]) % 4 in (1,3) else "opposite")
    print(f"p={p:>4}  derivation mismatches: {bad}   "
          f"caps 8|v:{sorted(caps['8|v'])} 4(8):{sorted(caps['v=4(8)'])} "
          f"2(4):{sorted(caps['v=2(4)'])} odd:{sorted(caps['odd'])}   "
          f"pair-types odd:{sorted(types['odd'])} 4(8):{sorted(types['v=4(8)'])}")
