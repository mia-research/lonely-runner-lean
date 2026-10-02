# The frozen runners' isolation set does not change when the others move: L(V) = L(frozen) ∩ L(movers).  Show it: the fixed list
# of components of L(frozen), and which of them the landing sits in as the two movers deform.
import sys
sys.argv = [sys.argv[0]]
exec(open('two_mover_track_v1.py').read().split('if __name__')[0])
def show(name, base, movers, target, steps=40):
    n = len(base); frozen = [i for i in range(n) if i not in movers]
    Lf = lonely([base[i] for i in frozen])
    print("=" * 100); print(name, "movers (readings #%d,#%d) %s -> %s" % (movers[0] + 1, movers[1] + 1, [round(float(base[m]), 2) for m in movers], [round(float(target[m]), 2) for m in movers]))
    print(" frozen runners' lonely set (fixed for the whole path): ", describe(Lf))
    seq = []
    for st in range(steps + 1):
        s = F(st, steps); rho = list(base)
        for m in movers: rho[m] = base[m] + (target[m] - base[m]) * s
        L = lonely(rho)
        if not L: seq.append((s, None, None)); continue
        land = L[0][0]; seq.append((s, comp_index(Lf, land), land))
    out = []
    for s, ci, land in seq:
        if out and out[-1][0] == ci: out[-1][2] = s; out[-1][3] = land
        else: out.append([ci, s, s, land])
    for ci, a, b, land in out:
        print("   s %.2f-%.2f : landing in frozen component #%s  %s (last landing R = %s)" % (float(a), float(b), ci, ("[%s]" % describe([Lf[ci]])) if ci is not None else "", "%.4f" % float(land) if land is not None else "-"))
AP = [F(k) for k in range(1, 8)]
def tgt(base, d):
    t = list(base)
    for m, v in d.items(): t[m] = v
    return t
show("AP, speeds s+1..s+7", AP, (5, 6), tgt(AP, {5: F(63, 10), 6: F(17, 2)}))
show("AP", AP, (4, 6), tgt(AP, {4: F(5), 6: F(81, 10)}))
show("AP", AP, (3, 6), tgt(AP, {3: F(46, 10), 6: F(78, 10)}))
show("AP", AP, (2, 6), tgt(AP, {2: F(27, 10), 6: F(75, 10)}))
show("AP", AP, (1, 6), tgt(AP, {1: F(2), 6: F(8)}))
show("AP", AP, (0, 6), tgt(AP, {0: F(1), 6: F(89, 10)}))
