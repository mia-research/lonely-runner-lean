"""
The phi(n) reach law above n = 24.

v2 tested n <= 24, where the widest phi-class was {15,16,20,24}. This extends to
n <= 60, which brings phi = 16 at {32,40,48,60} and phi = 20 at {25,33,44,50} --
classes spanning n by 28 and 25 respectively. If phi still sets the ordering there,
the law is not an artefact of the small-n range.

Same object, same criterion, same boundary discipline as v2; only the n list and the
sample size differ. Sample size falls with n to keep the cost bounded, so the standard
errors are larger at the top of the range and are reported per row.
"""
import sys
from collections import defaultdict
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from phi_reach_scale_v2 import phi, run, keff, selfcheck

NS = [8, 10, 12, 13, 15, 16, 20, 21, 22, 24, 25, 26, 28, 32, 33, 36, 40, 44, 48, 50, 60]

def budget(n, M0):
    """Keep M * n^2 * phi(n) roughly flat against the n = 24 cell."""
    ref = 24 * 24 * 8
    cost = n * n * phi(n)
    return max(300, int(M0 * ref / cost))

if __name__ == "__main__":
    M0 = int(sys.argv[1]) if len(sys.argv) > 1 else 2000
    selfcheck()
    print()
    for mult in (10, 50):
        print(f"=== speeds drawn from [1, {mult}n] ===")
        print(f"{'n':>3} {'phi':>4} {'M':>6} {'inst':>7} {'spine':>7} {'se':>7} "
              f"{'ctrlA':>7} {'ctrlB':>7} {'q(1/n)':>7} {'k_eff':>6}")
        print("-" * 76)
        rows = defaultdict(list)
        for n in NS:
            M = budget(n, M0)
            tot, hit, cA, cB, q1, se = run(n, mult * n, M, seed=104729 * n + mult)
            R, q = hit / tot, q1 / tot
            rows[phi(n)].append((n, R, se))
            print(f"{n:>3} {phi(n):>4} {M:>6} {tot:>7} {R:>7.4f} {se:>7.4f} "
                  f"{cA/tot:>7.4f} {cB/tot:>7.4f} {q:>7.4f} {keff(R, q):>6.2f}",
                  flush=True)
        print()
        print("  phi-class flatness")
        for ph in sorted(rows):
            if len(rows[ph]) < 2:
                continue
            vals = [R for _, R, _ in rows[ph]]
            ses = [s for _, _, s in rows[ph]]
            spread = max(vals) - min(vals)
            print(f"    phi={ph:>3}  n-span {max(n for n,_,_ in rows[ph]) - min(n for n,_,_ in rows[ph]):>3}"
                  f"  spread {spread:.4f} ({spread/max(ses):.1f} se)   "
                  + " ".join(f"n={n}:{R:.4f}" for n, R, _ in rows[ph]))
        print()
