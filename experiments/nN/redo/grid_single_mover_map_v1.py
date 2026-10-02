# One deformed runner, but the frozen set is a COMPLETE GRID WITH EXTRA LAPS (residues mod 8 = {1..7}, some readings carry whole laps).
# Same catalogue as ap_single_mover_map_v1: landing R*(rho) as pieces, flank (mover: slides / frozen: constant), exact breakpoints.
import sys
from fractions import Fraction as F
exec(open('ap_single_mover_map_v1.py').read().split('if __name__')[0])
def seq_for_base(base, m, lo, hi, step):
    def lab(rho):
        rr = list(base); rr[m] = rho; return label(rr, m)
    pts = []; x = lo; prev = lab(x); first = prev
    while x < hi:
        x2 = x + step; cur = lab(x2)
        if cur != prev:
            a, b = x, x2
            for _ in range(40):
                mid = (a + b) / 2
                if lab(mid) == prev: a = mid
                else: b = mid
            pts.append(((a + b) / 2, prev, cur))
        prev = cur; x = x2
    return pts, first
def describe(lab_):
    if lab_ is None: return "no lonely R"
    if lab_[0] == "mover": return "mover lap %d  R*=%d/rho" % (lab_[1], 8 * lab_[1] + 1)
    if lab_[0] == "frozen": return "frozen reading %s lap %d  R*=%s=%.4f" % (lab_[1], lab_[2], lab_[3], float(lab_[3]))
    if lab_[0] == "start": return "start R*=%s" % lab_[1]
    return "other"
if __name__ == "__main__":
    base = [F(x) for x in eval(sys.argv[1])]; ms = [int(a) for a in sys.argv[2:]]
    print("frozen set (readings, base d_min = %s):" % base[0], [str(x) for x in base], " lonely components of the base in (0,14]:", [(str(lo), str(hi)) for lo, hi in lonely_set(base)])
    for m in ms:
        pts, first = seq_for_base(base, m, F(7, 20), F(20), F(1, 800))
        segs = []; start = F(7, 20); cur = first
        for b, l0, l1 in pts: segs.append((start, b, cur)); start = b; cur = l1
        segs.append((start, F(20), cur))
        print("-" * 100); print("mover = runner with base reading %s (index %d)" % (base[m], m + 1))
        for a, b, l in segs: print("   rho in (%7.3f, %7.3f) ~ (%s, %s): %s" % (float(a), float(b), a.limit_denominator(150), b.limit_denominator(150), describe(l)))
