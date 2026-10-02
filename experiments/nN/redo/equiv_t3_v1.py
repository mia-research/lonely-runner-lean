# Transformation 3: rho_y -> v = rho_y + 8k/R*  (same residue class modulo 8/R*, so R*·v = R*·rho_y + 8k: same position at the landing), y rank>=2, k in {+-1,+-2,+-3}.
import sys; sys.path.insert(0, '.')
from equiv_lib_v1 import *
from collections import Counter, defaultdict
arrs, rnd = pool(3003, 3500)
tab = defaultdict(Counter); worst = {}; n = 0; pos_same = Counter(); setters_hit = Counter()
for a in arrs:
    ia = ident(a); sts = ia['S']; Rs = ia['L']
    setset = {s for s in ident_setters(a)} if False else set()
    for y in range(1, 7):
        for k in rnd.sample((1, 2, 3, -1, -2, -3), 3):
            v = a[y] + F(8 * k) / Rs
            if v <= 1 or v in a: continue
            b = list(a); b[y] = v
            if min(b) != 1: continue
            n += 1
            pos_same[(Rs * v) % 8 == (Rs * a[y]) % 8] += 1
            ib = ident(b); c = cmpi(ia, ib)
            early = sts[:-1]
            y_inert = clear_all(a[y], early); v_inert = clear_all(v, early)
            cls = ("y clear and v clear at every state before R*" if y_inert and v_inert else
                   "y clear at every earlier state, v blocks at an earlier state" if y_inert else
                   "y blocks at an earlier state, v clear at every earlier state" if v_inert else
                   "y blocks at an earlier state, v blocks at an earlier state")
            tab[cls]['n'] += 1
            for kk, val in c.items(): tab[cls][kk] += val
            cpred = (ia['S'] == ib['S']) and ia['C'][0] != y and entry_after(Rs, v)[0] > ia['E']
            tab[cls]['Cpred'] += cpred; tab[cls]['Cpred&ok'] += (cpred and c['C'])
            if not c['S']:
                kk3 = cx_key(a)
                if cls not in worst or kk3 < worst[cls][0]: worst[cls] = (kk3, a, y, v, k, ia, ib)
            if not c['L'] and 'L' not in worst:
                worst['L'] = (cx_key(a), a, y, v, k, ia, ib)
print("TRANSFORMATION 3: v = rho_y + 8k/R*; trials", n, "; position R*·v mod 8 equals R*·rho_y mod 8 in", dict(pos_same))
for cls, c in tab.items():
    print("\nclass:", cls, "| n =", c['n'])
    print("   states S %d, identity path I %d, landing L %d, opener O %d, closer C %d ; closer rule predicted %d, of which C equal %d" % (c['S'], c['I'], c['L'], c['O'], c['C'], c['Cpred'], c['Cpred&ok']))
for cls, w in worst.items():
    kk3, a, y, v, k, ia, ib = w
    print("\nsmallest counterexample (", cls, "):", fmt(a), " y(rank)=%d -> %s (k=%d, R*=%s)" % (y + 1, v, k, ia['L']))
    print("   before: states", [str(s) for s in ia['S']], "closer", ia['C']); print("   after : states", [str(s) for s in ib['S']], "closer", ib['C'])
