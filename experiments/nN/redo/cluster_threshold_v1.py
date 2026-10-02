# Where does "the six cluster readings alone have a lonely point in [c, 7c]" start to hold?  sup q = (first lonely R' >= c)/c over six-reading sets with
# smallest reading 1 (so the smallest of the arrangement's other readings is c times d_min).  q <= 7 <=> the slow runner's first clear window [1, 7] already contains a lonely R.
import sys
exec(open('cluster_window_v1.py').read().split('\nif __name__ ==')[0])
c = float(sys.argv[1]); W = float(sys.argv[2]) if len(sys.argv) > 2 else 25.0
v, rho = search(c, W, 40, 1500, int(c * 100) + 3)
print("c = %-5.2f spread <= %-3.0f: sup q found %7.3f  (%s)  cluster %s" % (c, W, v, "<= 7" if v <= 7 else "> 7: needs d_min's later windows", [round(x, 4) for x in rho]), flush=True)
