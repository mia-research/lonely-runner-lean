"""The phi(8) multipliers at a pinch.  At a pinch-off instant t* (pinchoff_v1: the slowest runner; runner a exactly at
the leaving edge 1/8, runner b exactly at the entering edge 7/8, the others clear), the multiples lambda*t* with
lambda = 3, 5 (mod 8) put a and b at 3/8 and 5/8: strictly clear.  If every other runner is also STRICTLY clear at some
lambda*t*, that instant stays lonely under every small change of the speeds, so the pinch cannot destroy the isolation.
Test, exactly, at every pinch of pinchoff_v1's 85 paths: the smallest lambda in 3, 5, 11, 13, 19, 21, ... (lambda = 3, 5
mod 8) at which all seven readings are strictly clear (circDist > 1/8), up to lambda = 200."""
from fractions import Fraction as F
from collections import Counter
from multiprocessing import Pool
from arrangement_lib import nd
from pinchoff_v1 import targets, readings_at, study

LAMS = [l for l in range(3, 201) if l % 8 in (3, 5)]

def run(args):
    name, V = args
    D1 = [F(v - V[0]) for v in V[1:]]; W = D1[-1]; D0 = [W * j / 7 for j in range(1, 8)]
    out = []
    for r in study(D0, D1):
        if r['kind'] != 'pinch': continue
        ds = readings_at(D0, D1, r['sstar']); ts = (r['k'] + F(1, 8)) / ds[r['a']]
        lam = next((l for l in LAMS if all(nd(d * l * ts) > F(1, 8) for d in ds)), None)
        out.append((lam, float(r['Rstar'])))
    return out

if __name__ == '__main__':
    with Pool() as pool: res = [x for part in pool.map(run, targets()) for x in part]
    c = Counter(l for l, _ in res)
    print(f"pinch-offs {len(res)}; strictly lonely at lambda*t* for the smallest lambda (3, 5 mod 8):")
    print("  ", sorted(((l if l is not None else 999), n) for l, n in c.items()))
    print(f"  at lambda = 3 or 5: {c[3] + c[5]} of {len(res)}; none up to 200: {c[None]}")
