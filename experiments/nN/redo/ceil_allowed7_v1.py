# For six readings (rho_1=1<...<rho_6): exact set of rho_7 (> rho_6, <= CAP) for which the 7-reading arrangement has no clear point in [1,9]
# i.e. every component of the clear set K6 of readings 1..6 on [1,9] lies in one open zone of reading 7.  Exact Fractions.
import sys; sys.path.insert(0, '.')
from fractions import Fraction as F
from ceil_k6_lib_v1 import *
def allowed7(six, cap=F(200), H=F(9)):
    comps = clear_components(six, H)
    cur = [(six[-1], cap)]       # open intervals of allowed rho_7 (lo, hi); start with (rho_6, cap)
    for a, b in comps:
        ivs = []; j = 1
        while True:
            lo = F(8*j - 1) / a; hi = F(8*j + 1) / b
            if lo >= cap: break
            if lo < hi: ivs.append((lo, hi))
            j += 1
            if j > 10**5: break
        new = []
        for (l1, h1) in cur:
            for (l2, h2) in ivs:
                l = max(l1, l2); h = min(h1, h2)
                if l < h: new.append((l, h))
        cur = sorted(new)
        if not cur: return comps, []
    return comps, cur
def crosses7(x):
    exec(open('cascade_path_map_v1.py').read().split('\nif __name__ ==')[0], globals())
if __name__ == "__main__":
    from ceil_lib_v1 import X7, path, norm
    c, al = allowed7(norm(X7)[:6])
    print(len(c), [(float(l), float(h)) for l, h in al], 'X7 rho7 inside:', any(l < X7[6] < h for l, h in al))
