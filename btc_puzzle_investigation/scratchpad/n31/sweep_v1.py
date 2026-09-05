import sys, time
sys.path.insert(0, 'scratchpad/n31')
from sympy import isprime
from purity_citationfree_widen_v1 import chi_coeffs, run

# all p>7 with #E(F_p) prime, up to a budget
lo, hi = 11, int(sys.argv[1]) if len(sys.argv) > 1 else 400
done = []
for p in range(lo, hi):
    if not isprime(p) or p in (2, 3, 7):
        continue
    npts = 1 + sum(1 for x in range(p) for y in range(p)
                   if y*y % p == (x*x % p * x + 7) % p)
    if not isprime(npts):
        continue
    try:
        v = run(p)
        done.append((p, npts, v))
    except Exception as e:
        print(f"p={p}: ERROR {type(e).__name__}: {e}", flush=True)
    sys.stdout.flush()
print("\nSUMMARY:", len(done), "primes tested;",
      sum(1 for _, _, v in done if v), "PURE;",
      [p for p, _, v in done if not v], "FAILURES")
