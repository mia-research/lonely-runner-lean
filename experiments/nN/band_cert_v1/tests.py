"""Checks on concrete shapes. For every shape: (i) exact least clear R (direct, independent of the
certificate); (ii) certificate witness R, independently checked clear and in [1,7]u[9,15]."""
import sys, random
from fractions import Fraction as F
from multiprocessing import Pool
from core import clear_set, is_clear
from walk import Cert

C = None
def init():
    global C
    C = Cert("cert15.pkl")

def check(s):
    s = [F(v) for v in s]
    S = clear_set(s, F(1), F(40))
    least = S[0][0] if S else None
    R = C.witness(s)
    okR = R is not None and is_clear(s, R) and (1 <= R <= 7 or 9 <= R <= 15)
    return (least, R, okR)

def rnd_fine(seed):
    rng = random.Random(seed)
    while True:
        d = rng.randint(1, 10**4)
        s6 = F(rng.randint(7 * d, 9 * d), d)
        if not 7 < s6 < 9:
            continue
        xs = set()
        while len(xs) < 5:
            d = rng.randint(1, 10**4)
            lo = d + 1; hi = -(-s6 * d // 1) - 1   # numerators with 1 < n/d < s6
            if lo > hi: continue
            x = F(rng.randint(lo, hi), d)
            if 1 < x < s6: xs.add(x)
        return [F(1)] + sorted(xs) + [s6]

def summarise(name, shapes, res):
    bad = [(s, r) for s, r in zip(shapes, res) if not r[2]]
    leasts = [r[0] for r in res]
    none = sum(1 for v in leasts if v is None)
    mx = max((v for v in leasts if v is not None), default=None)
    over15 = sum(1 for v in leasts if v is None or v > 15)
    arg = max(range(len(res)), key=lambda i: res[i][0] if res[i][0] is not None else F(10**9))
    print(f"[{name}] shapes={len(shapes)}  certificate-witness failures={len(bad)}  "
          f"no clear R<=40: {none}  least-clear>15: {over15}  max least-clear={float(mx):.6f}")
    print(f"    argmax shape: {[str(x) for x in shapes[arg]]}")
    for s, r in bad[:5]:
        print("    WITNESS FAIL", [str(x) for x in s], r)

if __name__ == "__main__":
    which = sys.argv[1]
    with Pool(10, initializer=init) as p:
        if which == "extremal":
            dec = "1 2.3509 3.2412 4.1886 5.2223 5.7871 7.4378".split()
            s_dec = [F(x) for x in dec]
            s_int = [round(x * 27720) for x in s_dec]
            shapes = [s_dec, [F(v, s_int[0]) for v in s_int]]
            for e in [F(1, 1000), F(1, 10**6), F(1, 10**12)]:
                shapes.append([F(1), F(2), F(3), F(4), F(5), F(6), F(7) + e])
            shapes.append([F(1), F(2), F(2973, 1000), F(3969, 1000), F(4955, 1000), F(5923, 1000), F(700005, 100000)])
            # adversarial maxima (adv.py)
            shapes.append([F(x) for x in ['1', '73984383/32000000', '207112661/64000000', '267982237/64000000', '334233169/64000000', '23154003/4000000', '476061891/64000000']])
            shapes.append([F(x) for x in ['1', '148724719/64000000', '102647591/32000000', '26799413/6400000', '167113869/32000000', '46326973/8000000', '476114701/64000000']])
            # perturbations of the extremal shape: 2000 random nudges of size <= 10^-3
            rng = random.Random(7)
            for _ in range(2000):
                t = [s_dec[0]] + [x + F(rng.randint(-1000, 1000), 10**6) for x in s_dec[1:]]
                shapes.append(t)
            res = p.map(check, shapes, chunksize=20)
            for s, r in list(zip(shapes, res))[:9]:
                print("  ", [str(x) for x in s], "least=", float(r[0]), "witness R=", r[1], float(r[1]), "ok=", r[2])
            summarise("extremal + 2000 perturbations", shapes, res)
        elif which == "random":
            n = int(sys.argv[2])
            shapes = p.map(rnd_fine, range(n), chunksize=200)
            res = p.map(check, shapes, chunksize=200)
            summarise("random fine shapes (denominators <= 10^4)", shapes, res)
            hist = {}
            for r in res:
                b = int(r[0]); hist[b] = hist.get(b, 0) + 1
            print("    histogram of floor(least clear R):", dict(sorted(hist.items())))
        elif which == "integer":
            N = int(sys.argv[2])
            from itertools import combinations
            shapes = []
            for a in range(1, N + 1):
                for c in range(7 * a + 1, min(9 * a, N + 1)):
                    for mid in combinations(range(a + 1, c), 5):
                        shapes.append([F(a, a)] + [F(m, a) for m in mid] + [F(c, a)])
            res = p.map(check, shapes, chunksize=500)
            summarise(f"all integer 7-tuples up to {N} in the band", shapes, res)
