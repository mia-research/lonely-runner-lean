"""Trace every relocation of the off-grid paths (offgrid_v1) through the cascade.  For each runner that relocates on the
path from its nearest grid to the target: locate each relocation (300-step scan, bisection to 2^-40), and read off:
  forward (pinch): the runner arriving at the slot edge (at an edge, moving into the slot); whether the isolation lands
    where that runner leaves the slot (it pins the relocated isolation) or is relayed on; the relay (setters in order,
    from the pinched instant, in the arrangement just past the relocation); R before and after.
  back (birth): the runners pinning the new component's two ends just past the relocation (the setter that opens it and
    the runner whose entry closes it); R before and after.
Signed readings (runners on both sides of the subject).  Exact (Fraction)."""
from fractions import Fraction as F
from math import floor
from collections import Counter
from multiprocessing import Pool
from arrangement_lib import nd
from offgrid_v1 import nearest_grid
from circle_deform_v1 import iso

E8 = F(1, 8)

def chain_from(v, k, t):
    ds = [v[j] - v[k] for j in range(8) if j != k]; others = [j for j in range(8) if j != k]
    ch = []
    while True:
        way = [i for i, d in enumerate(ds) if nd(d * t) < E8]
        if not way: return ch, t
        cand = {i: (F(floor(abs(ds[i]) * t - E8) + 1) + E8) / abs(ds[i]) for i in way}
        i = max(cand, key=lambda x: cand[x]); ch.append(others[i]); t = cand[i]

def right_end(v, k, t):
    """the runner whose zone entry closes the lonely component starting at t"""
    best = None
    for j in range(8):
        if j == k: continue
        d = abs(v[j] - v[k]); m = floor(d * t + E8) + 1; e = (m - E8) / d
        if best is None or e < best[0]: best = (e, j)
    return best[1]

def run(V):
    G, delta = nearest_grid(V)
    at = lambda s: [a + s * (b - a) for a, b in zip(map(F, G), map(F, V))]
    out = []
    for k in range(8):
        N = 300; prevs = None; prevR = None
        for q in range(0, N + 1):
            s = F(q, N); t, pos, setter, dm = iso(at(s), k); R = 8 * dm * t
            if prevR is not None and abs(R - prevR) > F(1, 50):
                lo, hi = prevs, s
                for _ in range(40):
                    mid = (lo + hi) / 2; tm, _, _, dmm = iso(at(mid), k)
                    if abs(8 * dmm * tm - prevR) <= F(1, 50): lo = mid; prevR = 8 * dmm * tm
                    else: hi = mid
                tb, pb, sb, db = iso(at(lo), k); ta, pa, sa, da = iso(at(hi), k)
                vb, va = at(lo), at(hi)
                Rb, Ra = 8 * db * tb, 8 * da * ta
                if Ra > Rb:
                    edge = [j for j, p in pb.items() if min(abs(8 * p - 1), abs(8 * p - 7)) < F(1, 10**6)]
                    arriving = [j for j in edge if (abs(8 * pb[j] - 1) < F(1, 10**6) and vb[j] < vb[k]) or
                                (abs(8 * pb[j] - 7) < F(1, 10**6) and vb[j] > vb[k])]
                    ch, tl = chain_from(va, k, tb)
                    out.append(dict(kind='fwd', V=V, k=k, Rb=float(Rb), Ra=float(Ra), pin_before=sb, arriving=arriving,
                                    relay=ch, carried=(len(ch) == 1 and ch[0] in arriving),
                                    gap_rank=None))
                else:
                    out.append(dict(kind='back', V=V, k=k, Rb=float(Rb), Ra=float(Ra), opener=sa,
                                    closer=right_end(va, k, ta), pin_before=sb))
            prevs, prevR = s, R
    return out

if __name__ == '__main__':
    import random
    rnd = random.Random(41)
    Vs = [sorted(rnd.sample(range(1, 200), 8)) for _ in range(60)]
    with Pool() as pool: res = [x for part in pool.map(run, Vs) for x in part]
    fw = [r for r in res if r['kind'] == 'fwd']; bk = [r for r in res if r['kind'] == 'back']
    print(f"relocations {len(res)}: forward {len(fw)}, back {len(bk)}")
    print(f"FORWARD: an arriving runner identified {sum(bool(r['arriving']) for r in fw)}; "
          f"carried straight across by it (lands at its exit, no relay) {sum(r['carried'] for r in fw)}")
    print(f"  relay length (moves from the pinched instant): {sorted(Counter(len(r['relay']) for r in fw).items())}")
    print(f"  first setter of the relay is the arriving runner: {sum(1 for r in fw if r['relay'] and r['relay'][0] in r['arriving'])}")
    print(f"  arriving runner = the runner that held the isolation before (same runner, other edge): "
          f"{sum(1 for r in fw if r['pin_before'] in r['arriving'])}")
    print(f"  R after / R before: max {max(r['Ra'] / r['Rb'] for r in fw):.3f}; hist {sorted(Counter(round(r['Ra']/r['Rb'], 1) for r in fw).items())}")
    print(f"BACK: the new place is opened (left end) by the runner that pinned the old one: {sum(1 for r in bk if r['opener'] == r['pin_before'])}")
    print(f"  R after / R before: min {min(r['Ra'] / r['Rb'] for r in bk):.3f}; hist {sorted(Counter(round(r['Ra']/r['Rb'], 1) for r in bk).items())}")
    for r in fw[:10]:
        print(f"  fwd  V {r['V']} runner {r['k']}: R {r['Rb']:.3f} -> {r['Ra']:.3f}; pinned by {r['pin_before']}; arriving {r['arriving']}; relay {r['relay']}")
    for r in bk[:8]:
        print(f"  back V {r['V']} runner {r['k']}: R {r['Rb']:.3f} -> {r['Ra']:.3f}; was pinned by {r['pin_before']}; new place opened by {r['opener']}, closed by {r['closer']}")
