# v3_reach_death_v1 -- replay the best reach word of v3_reach_v1 and, at its last zone, list every candidate next zone (reading y, lap j)
# with the reason it fails (ENTRY / PROGRESS / IRRED) and the cycle of rows that kills it (new row + least-product path back).  Exact Fractions.
# [PROVISIONAL: covering] claim named: the word has no continuation, so it supports no cover of [1,7].
import sys, json
from fractions import Fraction as F
sys.path.insert(0, '.')
import v3_reach_v1 as R
from d0_points_only_k6_v2 import base_system

def path_q_to_p(s, q, p):
    k = s.k; best = {q: (F(1), [])}
    for _ in range(k + 1):
        ch = False
        for (a, b, c, st) in s.log:
            if a in best:
                v = best[a][0] * c
                if b not in best or v < best[b][0]:
                    best[b] = (v, best[a][1] + [(a, b, str(c), st)]); ch = True
        if not ch: break
    return best.get(p)

def replay(B, word, h=F(1), lo=F(1), hi=F(7), nread=7):
    B = F(B)
    s = base_system(nread, B)
    assert s.add(nread-2, 0, 1/F(17), True); assert s.add(nread-1, 0, 1/F(25), False)
    cur = None; prev = None
    for (y, j) in word:
        ce, cv = (lo, 0) if cur is None else (8*cur[1]+h, cur[0])
        t = s.copy()
        assert t.add(y, cv, F(ce)/(8*j-h), True)
        assert t.add(cv, y, (8*j+h)/F(ce), True)
        if prev is not None:
            pe, pv = prev
            assert t.add(pv, y, (8*j-h)/F(pe), True)
        prev = (ce, cv); cur = (y, j); s = t
    return s, cur, prev

if __name__ == "__main__":
    B = sys.argv[1]; wordfile = sys.argv[2]; idx = int(sys.argv[3])
    r = json.load(open(wordfile)); word = [tuple(w) for w in r['best'][idx]['word']]
    s, cur, prev = replay(B, word)
    h = F(1); lo, hi = F(1), F(7); nread = 7; Bf = F(B)
    ce, cv = 8*cur[1] + h, cur[0]; M = s.M
    print('word depth', len(word), 'last zone (reading idx, lap)', cur, 'exit numerator', ce, 'sup exit', ce*M[cv][0][0])
    xmin = ce / M[0][cv][0]; xmax = ce * M[cv][0][0]; jmax = int((hi*Bf + h)//8) + 1
    tally = {'ENTRY': 0, 'PROGRESS': 0, 'IRRED': 0, 'OK': 0}; cyc = {}
    chain = [(0, y, j) for (y, j) in word]
    for y in range(1, nread):
        uymin = 1 / M[0][y][0]; uymax = M[y][0][0]
        for j in range(max(1, int((xmin/uymax - h)//8)), min(jmax, int((xmax/uymin + h)//8) + 1) + 1):
            if (0, y, j) in chain: continue
            t = s.copy(); rows = []
            rows.append(('ENTRY', (y, cv, F(ce)/(8*j-h))))
            rows.append(('PROGRESS', (cv, y, (8*j+h)/F(ce))))
            pe, pv = prev
            rows.append(('IRRED', (pv, y, (8*j-h)/F(pe))))
            reason = 'OK'; kill = None
            for name, (p, q, c) in rows:
                if not t.add(p, q, c, True):
                    reason = name
                    pp = path_q_to_p(s, q, p)
                    kill = dict(new_row=(p, q, str(c)), back_path=(pp[1] if pp else None), back_product=(str(pp[0]) if pp else None))
                    break
            tally[reason] += 1
            key = (y, j, reason)
            cyc[key] = kill
    print('candidates', tally)
    for (y, j, reason), kill in sorted(cyc.items()):
        print(' ', (y, j), reason, json.dumps(kill))
