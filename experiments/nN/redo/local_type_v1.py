"""E282/E283 (2026-10-02): does the local type at the bound fix the isolation's role?  Design: log E282.
Type tau(t): per reading, status ok / r0 / r1- / r7+ of P = 8 d t rounded to the nearest grid point (n + eps)."""
import sys, os, json, random
from fractions import Fraction as F
from math import floor
from collections import Counter, defaultdict
from multiprocessing import Pool
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import many_arrangements_v1 as MA
E8 = F(1, 8)

def status(P):
    n = floor(P + F(1, 2)); eps = P - n; r = n % 8
    if r == 0: return 'r0', 1 - eps
    if r == 1: return ('o', None) if eps >= 0 else ('-', -eps)
    if r == 7: return ('o', None) if eps <= 0 else ('+', 2 - eps)
    return 'o', None
def tau(T, t):
    out = []; rho = {}
    for i, d in enumerate(T):
        s, rr = status(8 * d * t)
        out.append({'r0': '0'}.get(s, s)); 
        if rr is not None: rho[i] = rr
    return ''.join(out), rho
def nd(x):
    x = x % 1; return min(x, 1 - x)
def run(T):
    m = min(T); t = F(1, 8 * m); rec = dict(T=T)
    tp, rho = tau(T, t); rec['tau0'] = tp
    chk1 = all((c == 'o') == (nd(d * t) >= E8) for c, d in zip(tp, T))
    rec['chk_F1'] = chk1
    moves = 0; first = None; last = None; chk2 = True; tau1 = None
    while True:
        way = [i for i, d in enumerate(T) if nd(d * t) < E8]
        if not way: break
        # F2: setter = argmax rho_d / d among bad
        tp_, rho_ = tau(T, t)
        pred = max(rho_, key=lambda i: rho_[i] / T[i])
        best = None
        for i in way:
            k = floor(T[i] * t - E8) + 1; c = (F(k) + E8) / T[i]
            if best is None or c > best[0]: best = (c, i)
        if moves == 0:
            first = best[1]; chk2 = (rho_[pred] / T[pred] == max(rho_[i] / T[i] for i in rho_)) and (t + rho_[pred] / (8 * T[pred]) == best[0])
        t = best[0]; last = best[1]; moves += 1
        if moves == 1: tau1 = tau(T, t)[0]
        if moves > 500: raise RuntimeError
    rec.update(M=moves, first=first, last=last, tau1=tau1, chk_F2=chk2, nbad=sum(1 for c in tp if c != 'o'), R=float(8 * m * t))
    return rec
def chunk(Ts): return [run(T) for T in Ts]
def build():
    pops = {}
    for (fam, par) in MA.CELLS:
        rnd = random.Random(7000 + MA.CELLS.index((fam, par))); lst = []
        for _ in range(300):
            T = MA.gen(fam, par, rnd)
            if len(set(T)) == 7 and min(T) > 0: lst.append(tuple(T))
        pops.setdefault(fam, []).extend(lst)
    mem = json.load(open('members_5978_v1.json')); pops['residual'] = [tuple(sorted(x[2])) for x in mem]
    return pops
if __name__ == '__main__':
    out = open('local_type_v1.out', 'w'); out.write(__doc__ + "\n")
    def w(s): out.write(s + "\n"); out.flush()
    pops = build()
    with Pool(10) as pool:
        res = {}
        for name, Ts in pops.items():
            res[name] = [r for part in pool.map(chunk, [Ts[i::40] for i in range(40)]) for r in part]
    allr = [(n, r) for n, rs in res.items() for r in rs]
    w("arrangements: %s" % {n: len(rs) for n, rs in res.items()})
    w("CHECKS: F1 (lonely iff all ok) failures %d; F2 (first setter = argmax rho/d, and its exit time) failures %d" % (
        sum(1 for n, r in allr if not r['chk_F1']), sum(1 for n, r in allr if r['M'] > 0 and not r['chk_F2'])))
    for n, rs in res.items():
        w("  %-9s lonely at the bound: %d of %d; moves max %d; nbad (at the bound) distribution %s" % (
            n, sum(1 for r in rs if r['M'] == 0), len(rs), max(r['M'] for r in rs), dict(sorted(Counter(r['nbad'] for r in rs).items()))))
    # determinism
    notl = [(n, r) for n, r in allr if r['M'] > 0]
    groups = defaultdict(list)
    for n, r in notl: groups[r['tau0']].append(r)
    w("\nnot lonely at the bound: %d arrangements in %d distinct types tau(bound)" % (len(notl), len(groups)))
    def purity(key, minsz=3):
        G = [(t, rs) for t, rs in groups.items() if len(rs) >= minsz]
        pure = sum(1 for t, rs in G if len({key(r) for r in rs}) == 1)
        return len(G), pure, sum(len(rs) for t, rs in G), sum(len(rs) for t, rs in G if len({key(r) for r in rs}) == 1)
    for name, key in (('first setter rank', lambda r: r['first']), ('number of moves', lambda r: r['M']), ('next type tau(t1)', lambda r: r['tau1']), ('landing setter rank', lambda r: r['last'])):
        g, p, na, npu = purity(key)
        w("  groups with >= 3 members: %d; %s determined by tau(bound) in %d groups (%d of %d arrangements)" % (g, name, p, npu, na))
    for nb in (1, 2, 3):
        sub = {t: rs for t, rs in groups.items() if sum(1 for c in t if c != 'o') == nb}
        for name, key in (('first setter rank', lambda r: r['first']), ('landing setter rank', lambda r: r['last']), ('moves', lambda r: r['M'])):
            G = [(t, rs) for t, rs in sub.items() if len(rs) >= 3]
            w("  nbad = %d: groups >= 3: %d; %s pure in %d" % (nb, len(G), name, sum(1 for t, rs in G if len({key(r) for r in rs}) == 1)))
    w("\nthe largest mixed groups (tau(bound), size, distinct landing ranks, distinct moves, distinct tau(t1)):")
    mixed = sorted([(len(rs), t, rs) for t, rs in groups.items() if len({r['last'] for r in rs}) > 1], reverse=True)[:12]
    for sz, t, rs in mixed:
        w("  %s size %d landing ranks %s moves %s tau1 %d kinds" % (t, sz, dict(Counter(r['last'] for r in rs)), dict(Counter(r['M'] for r in rs)), len({r['tau1'] for r in rs})))
    out.close(); print(open('local_type_v1.out').read()[len(__doc__):])
