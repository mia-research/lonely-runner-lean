# Transformation 2: rho_y moved within its INERT INTERVAL: the connected component, containing rho_y, of {v : v clear at every state R_0..R_n of the path (landing included)}.
# Exact component: for each state R the clear set of v is the union of [(8k+1)/R,(8k+7)/R]; component = intersection of the one interval per state that contains rho_y.
import sys; sys.path.insert(0, '.')
from equiv_lib_v1 import *
from collections import Counter
arrs, rnd = pool(2002, 3500)
def comp(rho, sts):
    lo, hi = F(1), None
    for R in sts:
        k = (R * rho - 1) // 8                      # floor; rho clear at R so 1 <= R*rho-8k <= 7
        l, h = (8 * k + 1) / R, (8 * k + 7) / R
        lo = max(lo, l); hi = h if hi is None else min(hi, h)
    return lo, hi
tab = Counter(); cnt = Counter(); worst = {}
widthsum = 0; nint = 0
for a in arrs:
    ia = ident(a); sts = ia['S']
    for y in range(1, 7):
        if not clear_all(a[y], sts): continue
        lo, hi = comp(a[y], sts); nint += 1
        assert lo <= a[y] <= hi
        pts = [("endpoint lo", lo), ("endpoint hi", hi), ("interior", lo + (hi - lo) * F(rnd.randint(1, 999), 1000)), ("interior", lo + (hi - lo) * F(rnd.randint(1, 999), 1000)),
               ("outside above (hi + 1/1000 of width)", hi + max(F(1, 1000), (hi - lo) / 1000))]
        for name, v in pts:
            if v <= 1 or v in a: continue
            b = list(a); b[y] = v; ib = ident(b)
            if min(b) != 1: continue                  # unit would change
            c = cmpi(ia, ib); inside = name != pts[-1][0]
            key = "inside component" if inside else "just outside component"
            tab[(key, 'n')] += 1
            for k2, val in c.items(): tab[(key, k2)] += val
            # rank-labelled
            if inside:
                oa, ob = full(a), full(b); tab[(key, 'P (rank,lap) equal')] += oa['path'] == ob['path']
                tab[(key, 'rank of y unchanged')] += (sorted(a).index(a[y]) == sorted(b).index(b[y]))
                # closer rule
                cpred = ia['C'][0] != y and entry_after(ia['L'], v)[0] > ia['E']
                tab[(key, 'closer-rule predicted')] += cpred; tab[(key, 'closer-rule predicted & identity closer equal')] += (cpred and c['C'])
                tab[(key, 'closer-rule not met & closer equal')] += ((not cpred) and c['C'])
            if inside and not c['C']: tab[('C fails by point type', name)] += 1
            if not c['S'] and inside:
                k3 = cx_key(a)
                if 'S' not in worst or k3 < worst['S'][0]: worst['S'] = (k3, a, y, v, lo, hi, ia, ib)
            if not c['C'] and inside:
                k3 = cx_key(a)
                if 'C' not in worst or k3 < worst['C'][0]: worst['C'] = (k3, a, y, v, lo, hi, ia, ib)
print("TRANSFORMATION 2: reading y (rank>=2, inert at all states incl. landing) moved inside / just outside its inert component; inert readings examined:", nint)
for key in ("inside component", "just outside component"):
    print("\n", key, "n =", tab[(key, 'n')])
    for k2 in ('S', 'I', 'L', 'O', 'C', 'P (rank,lap) equal', 'rank of y unchanged', 'closer-rule predicted', 'closer-rule predicted & identity closer equal', 'closer-rule not met & closer equal'):
        if (key, k2) in tab: print("   %-48s %d" % (k2, tab[(key, k2)]))
print('\nC (identity closer) fails inside the component, by point type:', {k[1]: v for k, v in tab.items() if k[0] == 'C fails by point type'})
for k, w in worst.items():
    key3, a, y, v, lo, hi, ia, ib = w
    print("\nSmallest inside-component counterexample for", k, ": rho =", fmt(a), "y(rank)=%d -> %s; component [%s, %s]" % (y + 1, v, lo, hi))
    print("  before: states", [str(s) for s in ia['S']], "closer", ia['C'], "entry", ia['E']); print("  after : states", [str(s) for s in ib['S']], "closer", ib['C'], "entry", ib['E'])
