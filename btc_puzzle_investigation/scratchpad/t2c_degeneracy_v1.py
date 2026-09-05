#!/usr/bin/env python3
"""
t2c_degeneracy_v1.py  —  T2c part (a), DETERMINISTIC structural degeneracy (gate-free).

OPEN_d2: d ≡ d0·(-1)^j − floor(d0·λ^j/n) (mod 3), d0 = orbit-min of d under <±λ>.
Q: for keys d in a bit-range [2^(b-1),2^b) with 2^b << m, is d its OWN orbit-min (d0=d, j=0, s=0,
carry=0), so the decomposition is degenerate and gives NO constraint on d mod 3? Find the crossover
bit-length b* where the carry first becomes nonzero (an orbit sibling ±λ^k d mod m drops below d).

This is a deterministic characterization (no statistic, no j-vs-target association) — it does NOT
touch the T2c part-(b) leakage test, which waits for its frozen pre-registration.
Exact integers only.
"""
from eps_to_d_run_v1 import prime_order_curve, full_orbit, find_glv
from collections import defaultdict


def carry_of(d, lam, m):
    orb = []
    for k in range(3):
        lk = pow(lam, k, m)
        orb += [(lk * d) % m, (-lk * d) % m]
    d0 = min(x for x in orb if x != 0)
    js = None
    for k in range(3):
        lk = pow(lam, k, m)
        if (lk * d0) % m == d % m:
            js = (k, 0); break
        if (-lk * d0) % m == d % m:
            js = (k, 1); break
    j, s = js
    c = (((-1) ** s) * d0 * pow(lam, j, m) - d) // m
    return d0, j, s, c


def main():
    for (lo, hi) in [(907, 908), (2089, 2090)]:
        r = prime_order_curve(lo, hi)
        if not r:
            continue
        p, m, G = r
        xs = full_orbit(G, p, m)
        lam, beta, wp = find_glv(xs, p, m)
        print(f"=== curve p={p} m={m} (log2 m = {m.bit_length()-1}), lam={lam} ===")
        bybit = defaultdict(lambda: [0, 0, 0])   # bit -> [count, #c==0, #(j==0 and s==0 and c==0)]
        for d in range(1, m):
            d0, j, s, c = carry_of(d, lam, m)
            b = d.bit_length()
            bybit[b][0] += 1
            if c == 0:
                bybit[b][1] += 1
            if j == 0 and s == 0 and c == 0:
                bybit[b][2] += 1
        print(f"  {'bit':>4} {'#keys':>6} {'frac c=0':>9} {'frac degenerate(j=s=c=0)':>26}")
        first_nonzero = None
        for b in sorted(bybit):
            cnt, cz, deg = bybit[b]
            fz = cz / cnt
            fd = deg / cnt
            if fz < 1.0 and first_nonzero is None:
                first_nonzero = b
            print(f"  {b:>4} {cnt:>6} {fz:>9.3f} {fd:>26.3f}")
        print(f"  crossover: smallest bit-length with any nonzero carry = {first_nonzero} "
              f"(m has {m.bit_length()} bits)\n")


if __name__ == "__main__":
    main()
