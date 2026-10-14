r"""
hp_omax_v1 -- maximise o (and u+o, u+2o) over unit 4-tuples using the NORMAL FORM
   o = |{ y in [0,1) : (floor(e_rho y) mod 4) XOR mu(rho) is a permutation }|,
   u = |{ y : that holds at y and at y + 1/2 }|.
Exact Fractions; cell ENTRY evaluation on the grid of all j/(2 e_rho).

usage:  python3 hp_omax_v1.py exhaustive QMAX
        python3 hp_omax_v1.py random NTRIALS EMAX SEED
"""
import itertools, sys, random
from math import lcm, gcd
from fractions import Fraction as F

R4 = (1, 3, 5, 7)
MU = (0, 1, 2, 3)


def ou(sp):
    D = lcm(*[2 * e for e in sp])
    pts = set()
    for e in sp:
        pts.update(range(0, D, D // (2 * e)))
    p = sorted(pts); p.append(D)
    half = D // 2
    perm = {}
    for i in range(len(p) - 1):
        a = p[i]
        perm[a] = (len({(((e * a) // D) % 4) ^ m for e, m in zip(sp, MU)}) == 4)
    o = u = 0
    for i in range(len(p) - 1):
        a = p[i]; w = p[i + 1] - a
        if perm[a]:
            o += w
            b = (a + half) % D
            # b is a breakpoint of the same grid (the grid is half-period symmetric)
            if perm[b]:
                u += w
    return F(o, D), F(u, D)


def report(tag, it, total=None):
    best = {}
    n = 0
    for sp in it:
        n += 1
        o, u = ou(sp)
        for k, v in (("o", o), ("u", u), ("u+o", u + o), ("u+2o", u + 2 * o)):
            if k not in best or v > best[k][0]:
                best[k] = (v, sp)
        if n % 5000 == 0:
            print(f"   ... {n}", flush=True)
    print(f"{tag}: {n} tuples")
    for k in ("o", "u", "u+o", "u+2o"):
        v, sp = best[k]
        print(f"   max {k:5s} = {v}  = {float(v):.6f}   at {sp}")
    return best


if __name__ == "__main__":
    mode = sys.argv[1]
    if mode == "exhaustive":
        Q = int(sys.argv[2])
        def gen():
            for qs in itertools.product(range(Q + 1), repeat=4):
                sp = tuple(8 * q + r for q, r in zip(qs, R4))
                if len(set(sp)) == 4:
                    yield sp
        report(f"exhaustive q <= {Q} (speeds <= {8*Q+7})", gen())
    else:
        N = int(sys.argv[2]); EMAX = int(sys.argv[3]); seed = int(sys.argv[4])
        random.seed(seed)
        def gen():
            for _ in range(N):
                sp = tuple(8 * random.randrange(0, EMAX // 8) + r for r in R4)
                if len(set(sp)) == 4:
                    yield sp
        report(f"random {N} tuples, speeds < {EMAX}, seed {seed}", gen())
