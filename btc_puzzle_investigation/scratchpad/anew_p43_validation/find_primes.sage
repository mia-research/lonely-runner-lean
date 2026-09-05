# Fast pre-scan (NO cover build): p == 7 mod 12 with a twist B giving prime nE and 3|(nE-1).
# Reports first good primes in each target window with estimated orbit-sample N ~ nE/6.
def good(p):
    Fp = GF(p)
    for B in range(1, 80):
        try: nE = Integer(EllipticCurve(Fp, [0, B]).order())
        except Exception: continue
        if nE.is_prime() and (nE - 1) % 3 == 0:
            return B, nE
    return None
for (lo, hi, want) in [(600, 800, 2), (1400, 1700, 2), (2900, 3300, 2), (5800, 6300, 2)]:
    found = 0
    print("window [%d,%d]:" % (lo, hi), flush=True)
    q = lo
    while q < hi and found < want:
        if is_prime(q) and q % 12 == 7:
            g = good(q)
            if g: print("   p=%d  B=%d  nE=%d  N~%d" % (q, g[0], g[1], (g[1]//6)), flush=True); found += 1
        q += 1
