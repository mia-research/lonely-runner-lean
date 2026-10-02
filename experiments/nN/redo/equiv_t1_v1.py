# Transformation 1: rho_y -> rho_y + 8m (whole laps), one reading y>=2, m in {1,2,3} (and -1 when rho_y>9).
import sys; sys.path.insert(0, '.')
from equiv_lib_v1 import *
from collections import Counter, defaultdict
arrs, rnd = pool(1001, 3500)
tab = defaultdict(Counter); worst = {}
status_R0 = Counter(); n = 0
for a in arrs:
    o = full(a); sts = o['states']
    for y in range(1, 7):
        for m in rnd.sample((1, 2, 3, -1), 2):
            v = a[y] + 8 * m
            if v <= 1 or v in a: continue
            b = list(a); b[y] = v; ob = full(b)
            if min(b) != 1: continue
            n += 1
            inert_o = clear_all(a[y], sts); new_clear = clear_all(v, sts)
            cls = ("y inert, y' clear at all original states" if inert_o and new_clear else
                   "y inert, y' blocks at some original state" if inert_o else
                   "y blocks at some state, y' clear at all original states" if new_clear else
                   "y blocks at some state, y' blocks at some state")
            c = cmp(o, ob); ia, ib = ident(a), ident(b); ci = cmpi(ia, ib); c['I'] = ci['I']; c['Ci'] = ci['C']; c['Oi'] = ci['O']
            cpred = (ia['S'] == ib['S']) and ia['C'][0] != y and (entry_after(ia['L'], v)[0] > ia['E'])
            tab[cls]['Cpred_n'] += cpred; tab[cls]['Cpred_ok'] += (cpred and ci['C'])
            tab[cls]['Sequal_Cnot_pred'] += (ia['S'] == ib['S'] and (not cpred) and ci['C'])
            tab[cls]['n'] += 1
            for k, val in c.items(): tab[cls][k] += val
            # status at R_0 = 1 (integer)
            status_R0[blocks(F(1), a[y]) == blocks(F(1), v)] += 1
            if not c['S']:
                key = cx_key(a)
                if cls not in worst or key < worst[cls][0]: worst[cls] = (key, a, y, v, o, ob)
print("TRANSFORMATION 1: rho_y -> rho_y + 8m, y in ranks 2..7; trials", n, "on", len(arrs), "arrangements (about 60% with >=1 move)")
print("block status of y vs y' at R_0=1 (integer R) equal:", status_R0)
for cls, c in tab.items():
    print("\nclass:", cls, "| n =", c['n'])
    print("   states S equal %d, (rank,lap) path P equal %d, landing L equal %d, opener O equal %d, closer C equal %d" % (c['S'], c['P'], c['L'], c['O'], c['C']))
    print("   identity-labelled (index,lap) path I equal %d, identity opener %d, identity closer %d" % (c['I'], c['Oi'], c['Ci']))
    print("   closer rule 'S equal, y is not the original closer, y' next entry after R* > closer entry': predicted-preserved %d, of which identity closer equal %d; S-equal, rule not met, closer equal anyway (ties/same reading) %d" % (c['Cpred_n'], c['Cpred_ok'], c['Sequal_Cnot_pred']))
print("\nSmallest counterexamples (S fails), by class:")
for cls, (key, a, y, v, o, ob) in worst.items():
    print(" ", cls); print("   rho =", fmt(a), " y(rank)=%d  rho_y -> %s" % (y + 1, v))
    print("   states before:", [str(s) for s in o['states']], "path", o['path']); print("   states after :", [str(s) for s in ob['states']], "path", ob['path'])
# AP check
print("\nAP (1..7): y=7, m=1 (7->15), m=2 (->23), m=3 (->31)")
for m in (0, 1, 2, 3):
    b = [F(x) for x in range(1, 7)] + [F(7 + 8 * m)]; ob = full(b); print("  m=%d" % m, "states", [str(s) for s in ob['states']], "path", ob['path'], "opener", ob['opener'], "closer", ob['closer'])
