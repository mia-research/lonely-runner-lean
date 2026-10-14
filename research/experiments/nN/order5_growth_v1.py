"""The mechanism: min u grows faster than (5Q+1)/4, so R = (5Q+1)/u falls away above lap 6.

R = (5Q+1)/u where Q is the LAST setter's lap and u its reading (in units of d_min).
R >= 4 requires u <= (5Q+1)/4.  From the S=18 lap table, the attained u at each max lap:
"""
from fractions import Fraction as F
rows = [(1, F(27,8)), (2, F(121,36)), (3, F(88,27)), (4, F(231,76)), (5, F(121,36)),
        (6, F(31,9)), (7, F(22,7)), (8, F(11,4)), (9, F(23,8)), (10, F(561,196))]
print(f"{'Q':>3} {'sup R':>10} {'u = (5Q+1)/R':>14} {'threshold (5Q+1)/4':>20} {'u / Q':>8} {'R<4?':>6}")
for Q, R in rows:
    num = F(5*Q + 1)
    u = num / R
    thr = num / 4
    print(f"{Q:>3} {float(R):>10.4f} {float(u):>14.4f} {float(thr):>20.4f} {float(u)/Q:>8.3f} {str(R < 4):>6}")
print()
print("u/Q settles near 1.8 while the threshold grows like 1.25*Q, so R = (5Q+1)/u -> 5/1.8 = 2.78.")
print("A bound  u >= (5Q+1)/4  for Q >= 7  would truncate the enumeration at lap 6 and close")
print("the certificate for UNBOUNDED ratio.  Observed slack at each lap:")
for Q, R in rows:
    num = F(5*Q+1); u = num / R; thr = num / 4
    print(f"   Q={Q:>2}: u = {float(u):8.4f}   needs >= {float(thr):8.4f}   slack {float(u - thr):+8.4f}"
          f"   {'OK' if u >= thr else 'BELOW -- R >= 4 here'}")
