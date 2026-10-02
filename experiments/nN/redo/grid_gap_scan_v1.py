# Is a real residual member near SOME grid?  Readings rho_x = x/d_min.  For a gap D (in units of d_min) the reading sits at
# idx = round(rho/D), deviation eps = rho/D - idx (in units of D).  Scan D; report the smallest max|eps| and D = 0.7.
import sys
sys.argv = [sys.argv[0]]
exec(open('anatomy_members_v1.py').read().split('if __name__')[0])
def dev(rho, D):
    out = []
    for r in rho:
        q = r / D; i = round(q); out.append((i, q - i))
    return out
def scan(rho, lo=0.2, hi=1.3, steps=22000):
    best = None
    for s in range(steps + 1):
        D = lo + (hi - lo) * s / steps
        m = max(abs(e) for _, e in dev(rho, D))
        if best is None or m < best[0]: best = (m, D)
    return best
def show(S, name):
    S = sorted(S); rho = [float(F(x, S[0])) for x in S]
    print("=" * 90); print(name, "rho =", [round(r, 3) for r in rho])
    d07 = dev(rho, 0.7)
    print(" D = 0.7: idx", [i for i, _ in d07], " eps", [round(e, 3) for _, e in d07], " max|eps| %.3f" % max(abs(e) for _, e in d07))
    m, D = scan(rho); dv = dev(rho, D)
    print(" best D in [0.2,1.3]: D = %.4f  max|eps| = %.4f  idx %s  eps %s  idx mod 8 %s" % (
        D, m, [i for i, _ in dv], [round(e, 3) for _, e in dv], [i % 8 for i, _ in dv]))
    # for D = 1 / (integer m)  (the 'integer' grids): D = 1/m
    for mm in (1, 2, 3, 4):
        dvv = dev(rho, 1.0 / mm); print("   D = 1/%d: max|eps| = %.3f" % (mm, max(abs(e) for _, e in dvv)))
if __name__ == "__main__":
    for i in (0, 1, 7, 3, 5): show(B[i], "B1 #%d" % i)
    for i in (0, 1): show(C[i], "C1 #%d" % i)
