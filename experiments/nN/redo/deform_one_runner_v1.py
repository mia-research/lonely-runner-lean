"""One runner deformed from the AP, traced exactly through the cascade (owner, 2026-09-26).
AP speeds v_k = k G, G = 840, k = 1..8 (all positive; nobody at rest).  One runner j has its speed moved by delta,
-G < delta < G (kept distinct and positive).  For chosen subjects: the cascade's event t* (shown as t* G, so the AP's
global instant is 1/8), d_min, S = d_max/d_min, R = 8 d_min t* (the event on the subject's own AP scale), and the
runner that pins the event at exactly 1/8 (Thm 6.2(d)).  Exact (Fraction)."""
from fractions import Fraction as F
from math import floor
from arrangement_lib import nd

G = 840
def cascade(ds):
    t = F(1, 8 * min(ds))
    while True:
        way = [d for d in ds if nd(d * t) < F(1, 8)]
        if not way: return t
        t = max((F(floor(d * t - F(1, 8)) + 1) + F(1, 8)) / d for d in way)

def trace(j, subjects, deltas):
    for sub in subjects:
        print(f"\n  subject = runner {sub}" + (" (the deformed runner)" if sub == j else ""))
        print(f"  {'delta/G':>8s} {'d_min/G':>8s} {'S':>7s} {'R':>7s} {'t* G':>8s}  pinned by (runner: reads)")
        for dl in deltas:
            V = [k * G for k in range(1, 9)]; V[j - 1] += dl
            if len(set(V)) < 8 or min(V) <= 0: continue
            vs = V[sub - 1]
            ds = sorted({abs(v - vs) for i, v in enumerate(V) if i != sub - 1})
            t = cascade(ds); dmin = min(ds); S = F(max(ds), dmin); R = 8 * dmin * t
            pins = [k + 1 for k, v in enumerate(V) if k != sub - 1 and nd(abs(v - vs) * t) == F(1, 8)]
            print(f"  {float(F(dl, G)):>8.3f} {float(F(dmin, G)):>8.3f} {float(S):>7.3f} {str(R):>7s} {float(t * G):>8.4f}  {pins}")

steps = [-G + 42] + [int(G * F(k, 20)) for k in range(-19, 20)] + [G - 42]
print("RUNNER 8 (the fastest) deformed: speed 8G + delta")
trace(8, [8, 1, 4], sorted(set(steps)))
print("\nRUNNER 4 (interior) deformed: speed 4G + delta")
trace(4, [4, 1, 8], sorted(set(steps)))
