# Two deformed runners of the AP (readings 1..7): the plane of their new readings (rho_a, rho_b).  Each cell: where the cascade lands.
# Symbol = the landing flank: '.' R*=1 (the ideal's first event, unmoved), digits/letters for other landings (legend lists R* and flank).
# Exact Fractions at the cell centre.
import sys
from fractions import Fraction as F
exec(open('ap_single_mover_map_v1.py').read().split('if __name__')[0])
SYMS = "123456789abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ"
def pairmap(a, b, lo, hi, n=64):
    base = [F(x) for x in range(1, 8)]; legend = {}; rows = []
    for iy in range(n - 1, -1, -1):
        rb = lo + (hi - lo) * (F(iy) + F(1, 2)) / n; row = ""
        for ix in range(n):
            ra = lo + (hi - lo) * (F(ix) + F(1, 2)) / n
            rr = list(base); rr[a] = ra; rr[b] = rb
            L = lonely_set(rr)
            if not L: row += "?"; continue
            R = L[0][0]
            key = round(float(R), 3)
            if key == 1.0: row += "."; continue
            fl = [(i, int((R * r - 1) / 8)) for i, r in enumerate(rr) if ((R * r - 1) / 8).denominator == 1 and R * r >= 1]
            if key not in legend:
                legend[key] = SYMS[len(legend) % len(SYMS)]
            row += legend[key]
        rows.append(row)
    return rows, legend
if __name__ == "__main__":
    a = int(sys.argv[1]) - 1; b = int(sys.argv[2]) - 1; lo = F(sys.argv[3]); hi = F(sys.argv[4]); n = int(sys.argv[5]) if len(sys.argv) > 5 else 64
    rows, legend = pairmap(a, b, lo, hi, n)
    print("movers: readings %d (x axis) and %d (y axis), both in (%s, %s); '.' = R*=1" % (a + 1, b + 1, lo, hi))
    for i, r in enumerate(rows):
        y = float(hi - (hi - lo) * (F(i) + F(1, 2)) / n); print("%6.2f %s" % (y, r))
    print("       " + "".join("|" if (ix % 8 == 0) else " " for ix in range(n)))
    print("x:", ", ".join("%.2f" % float(lo + (hi - lo) * F(ix, n)) for ix in range(0, n, 8)))
    print("legend (symbol: landing R*):", ", ".join("%s: %.3f" % (v, k) for k, v in sorted(legend.items())))
