"""Check against the cascade, across arrangements and every subject, the relocation mechanism read off circle_deform_v1:
(i) just before every relocation, two runners sit at the same edge of the subject's slot (1/8 or 7/8): the pinner leaving
and a second runner arriving from the other direction;  (ii) the isolation moves to where the arriving runner leaves the
slot on the far side, so after the relocation the arriving runner is the pinner, at the opposite edge -- or, when other
runners have entered meanwhile, the cascade relays on.  Exact positions at the bisected bracket ends (2^-40); an edge
coincidence is |8p - 1| or |8p - 7| below 10^-6.  Paths from the progression as in circle_deform_v1."""
import random
from fractions import Fraction as F
from multiprocessing import Pool
from circle_deform_v1 import iso

def run(args):
    V, k, N = args
    W = V[-1] - V[0]; AP = [V[0] + F(W * i, 7) for i in range(8)]
    at = lambda s: [a + s * (b - a) for a, b in zip(AP, V)]
    out = []; prevs, prevR = None, None
    for q in range(1, N + 1):
        s = F(q, N); t, pos, setter, dm = iso(at(s), k); R = 8 * dm * t
        if prevR is not None and abs(R - prevR) > F(1, 50):
            lo, hi = prevs, s
            for _ in range(40):
                mid = (lo + hi) / 2; tm, _, _, dmm = iso(at(mid), k)
                if abs(8 * dmm * tm - prevR) <= F(1, 50): lo = mid; prevR = 8 * dmm * tm
                else: hi = mid
            tb, pb, sb, db = iso(at(lo), k); ta, pa, sa, da = iso(at(hi), k)
            vb = at(lo)
            edge = lambda p: min(abs(8 * p - 1), abs(8 * p - 7))
            at_edge = [j for j, p in pb.items() if edge(p) < F(1, 10**6)]
            # the arriving runner: at an edge, moving INTO the slot (at 1/8 moving down = slower than subject; at 7/8 moving up = faster)
            arriving = [j for j in at_edge if (abs(8 * pb[j] - 1) < F(1, 10**6) and vb[j] < vb[k]) or (abs(8 * pb[j] - 7) < F(1, 10**6) and vb[j] > vb[k])]
            out.append(dict(two_at_edge=len(at_edge) >= 2, arriving=arriving, pinner_after=sa,
                            carried=bool(arriving) and sa in arriving, dR=float(8 * da * ta - 8 * db * tb)))
        prevs, prevR = s, R
    return out

if __name__ == '__main__':
    rnd = random.Random(26); tasks = []
    for _ in range(25):
        V = sorted(rnd.sample(range(1, 250), 8))
        for k in range(8): tasks.append((V, k, 300))
    with Pool() as pool: res = [x for part in pool.map(run, tasks) for x in part]
    n = len(res)
    print(f"relocations {n} (25 arrangements x 8 subjects, paths from the progression)")
    print(f"  (i)  two runners at the same slot edge just before: {sum(r['two_at_edge'] for r in res)}; an arriving runner identified: {sum(bool(r['arriving']) for r in res)}")
    print(f"  (ii) the arriving runner pins the relocated isolation from the far edge: {sum(r['carried'] for r in res)}; relayed on by others: {sum(bool(r['arriving']) and not r['carried'] for r in res)}")
    print(f"  displaced forward {sum(r['dR'] > 0 for r in res)}, back {sum(r['dR'] < 0 for r in res)}")
