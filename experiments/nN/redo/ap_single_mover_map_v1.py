# The complete one-deformed-runner map of the AP: speeds s+1..s+7 (readings 1..7), the runner with reading m moved to reading rho in (0.35, 14).
# For each m: the landing R*(rho) as a piecewise function, each piece labelled by its flank (runner, lap) and whether the flank is the mover
# (R* = (8j+1)/rho: slides) or a frozen runner (R* constant: the frozen runners' own isolation point).  Breakpoints located exactly (bisection)
# and shown as fractions.  Exact Fractions.
import sys
from fractions import Fraction as F
exec(open('hop_is_gap_event_v1.py').read().split('from collections import Counter')[0].split("sys.argv = [sys.argv[0]]\n")[1])
def landing(rhos):
    L = lonely_set(rhos)
    return L[0][0] if L else None
def flank(rhos, R, m):
    # which (runner, lap) has its opening at R, preferring the mover; 'start' if R = 1/rho_min
    out = []
    for i, r in enumerate(rhos):
        j = (R * r - 1) / 8
        if j.denominator == 1 and j >= 0: out.append((i, int(j)))
    if R == 1 / min(rhos): out.append(("start", 0))
    return out
def label(rhos, m):
    R = landing(rhos)
    if R is None: return None
    fl = flank(rhos, R, m)
    mv = [x for x in fl if x[0] == m]
    if mv: return ("mover", mv[0][1])
    fr = [x for x in fl if x[0] != m and x[0] != "start"]
    if fr: return ("frozen", fr[0][0] + 1, fr[0][1], R)
    return ("start", R) if fl else ("other",)
def seq_for(m, lo=F(7, 20), hi=F(14), step=F(1, 2000)):
    base = [F(x) for x in range(1, 8)]
    def lab(rho):
        rr = list(base); rr[m] = rho; return label(rr, m)
    pts = []; x = lo; prev = lab(x); start = x
    while x < hi:
        x2 = x + step; cur = lab(x2)
        if cur != prev:
            a, b = x, x2
            for _ in range(40):
                mid = (a + b) / 2
                if lab(mid) == prev: a = mid
                else: b = mid
            pts.append(((a + b) / 2, prev, cur)); 
        prev = cur; x = x2
    return pts, lab(lo)
if __name__ == "__main__":
    ms = [int(a) for a in sys.argv[1:]] or [6]
    for m in ms:
        pts, first = seq_for(m)
        print("=" * 100); print("mover = the runner with reading %d (speed s+%d); landing R*(rho), rho = its new reading" % (m + 1, m + 1))
        segs = []; start = F(7, 20); cur = first
        for b, l0, l1 in pts:
            segs.append((start, b, cur)); start = b; cur = l1
        segs.append((start, F(14), cur))
        for a, b, lab_ in segs:
            if lab_ is None: txt = "no lonely R in range"
            elif lab_[0] == "mover": txt = "R* = %d/rho   (mover's opening, lap %d: slides with the mover)" % (8 * lab_[1] + 1, lab_[1])
            elif lab_[0] == "frozen": txt = "R* = %s = %.4f (opening of the frozen runner with reading %d, lap %d: does not move)" % (lab_[3], float(lab_[3]), lab_[1], lab_[2])
            elif lab_[0] == "start": txt = "R* = %s = 1/rho_min (the start state itself)" % lab_[1]
            else: txt = "other"
            print("  rho in (%8.4f, %8.4f)  ~ (%s, %s) : %s" % (float(a), float(b), a.limit_denominator(200), b.limit_denominator(200), txt))
