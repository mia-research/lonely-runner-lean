"""relocation_v1 follow-up.  (i) Slot at t* by NEAREST eighth (v1 used floor, which puts a runner just under a slot
line into the slot below).  (ii) What each move cures: at the instant before a move, the setter's position in eighths
mod 8 (a near-sharer sits in the subject's own slot 0, or just under it at slot 7 + deviation).  (iii) Two traces,
move by move, positions of all seven others in eighths at each scale.  Exact."""
import random
from fractions import Fraction as F
from math import floor
from collections import Counter
from relocation_v1 import trace, nd

def positions(ds, t): return [(8 * d * t) % 8 for d in ds]

def show(V, i):
    t, setters, ds = trace(V, i)
    m = min(abs(d) for d in ds); tt = F(1, 8 * m)
    print(f"\n  arrangement {V}, runner {V[i]}; signed differences {ds}")
    for step in setters + [None]:
        pos = positions(ds, tt)
        way = [x for x, p in zip(ds, pos) if nd(p / 8) < F(1, 8)]
        print(f"    t = {tt} (scale D = {float(1/(8*tt)):.2f}): eighths " +
              " ".join(f"{float(p):.2f}" for p in pos) + (f"   in the way: {way}" if way else "   CLEAR"))
        if step is None: break
        d, K = step
        tt = (K + F(1, 8)) / abs(d)
        print(f"      move: setter {d} to its lap {K} + 1/8, i.e. {8*K+1} eighths")

if __name__ == '__main__':
    rnd = random.Random(2609); g = 840
    cured = Counter(); comp = Counter(); nr = 0
    for rho in (F(1, 100), F(1, 8), F(1), F(16)):
        for _ in range(400):
            e = [rnd.randint(-int(rho * g), int(rho * g)) for _ in range(8)]
            V = sorted(10 * g + g * k + e[k] for k in range(8))
            if len(set(V)) < 8: continue
            for i in range(8):
                t, setters, ds = trace(V, i); nr += 1
                slots = sorted(round(p) for p in positions(ds, t))
                comp[(str(rho), slots == list(range(1, 8)))] += 1
                tt = F(1, 8 * min(abs(d) for d in ds))
                for d, K in setters:
                    p = (8 * d * tt) % 8
                    cured['setter sat in slot 0 (on the subject), eighths in [0,1)' if p < 1 else
                          'setter sat just under the subject, eighths in (7,8)'] += 1
                    tt = (K + F(1, 8)) / abs(d)
    print(f"{nr} runners.  Slot pattern at t* by nearest eighth, complete system {{1..7}}:")
    for rho in ('1/100', '1/8', '1', '16'):
        a, b = comp[(rho, True)], comp[(rho, False)]
        print(f"   rho {rho}: {a} of {a+b}")
    print("What each move cures (setter's position just before the move):", dict(cured))
    print("\nTwo traces:")
    show([8400, 9240, 10081, 10918, 11763, 12600, 13440, 14282], 3)
    rnd2 = random.Random(7)
    while True:
        e = [rnd2.randint(-840, 840) for _ in range(8)]
        V = sorted(8400 + 840 * k + e[k] for k in range(8))
        if len(set(V)) == 8:
            best = max(range(8), key=lambda i: len(trace(V, i)[1]))
            if len(trace(V, best)[1]) >= 4: show(V, best); break
