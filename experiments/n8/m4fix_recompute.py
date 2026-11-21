# m4fix_recompute.py -- recording re-run of merged_kill (m4comp_uclosure_v1.py, key='aA')
# on the smallest checkpoint-killed box, dumping EVERYTHING the Lean Fixpoint bank needs:
# the opening record (pre-fold seed), the final record (states keys, tables, P, Aex), and
# the convergence round count.  Machinery mk/add/gt/tranges/tzones/reach_utc imported
# verbatim from m4comp_lib_v1.py -- no reimplementation, so the recomputed verdict must
# reproduce the checkpoint line exactly.
import sys, os, json
from fractions import Fraction as F

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from m4comp_lib_v1 import mk, add, gt, tranges, tzones, reach_utc

def looser(U1, U2):
    V = []
    for i in range(7):
        row = []
        for j in range(7):
            a = U1[i][j]; b = U2[i][j]
            if a is None: row.append(None)
            elif b is None: row.append(None)
            elif a[0] > b[0]: row.append(a)
            elif b[0] > a[0]: row.append(b)
            else: row.append((a[0], a[1] and b[1]))
        V.append(row)
    return V

def dump_table(U):
    return [[(str(v[0]), v[1]) if v is not None else None for v in row] for row in U]

def merged_kill_recorded(t, key='aA'):
    """Verbatim merged_kill with recording.  Returns (killed, nstates, ceil, record)."""
    n = (1,) + tuple(t)
    rec = dict(t=list(t), key=key)
    U0 = mk(n)
    rec['mk_none'] = U0 is None
    if U0 is None: return True, 0, F(1), rec
    rec['U0'] = dump_table(U0)
    R0 = tranges(U0, t)
    Z0 = tzones(U0, t)
    st = {}
    opening = {}          # recorded opening record (pre-fold seed)
    frontier_global = F(1)
    def kfun(a, Aex):
        return a if key == 'a' else (a, Aex)
    for e in range(6):
        lo_e, hi_e = R0[e]
        for A0, B0, e0, x0 in Z0[e]:
            if e0 >= F(1) or x0 <= F(1): continue
            Us = add(U0, 0, e + 1, F(1, A0), True)
            if Us is None: continue
            Us = add(Us, e + 1, 0, F(B0), True)
            if Us is None: continue
            P1 = x0 if lo_e >= A0 else F(B0) / max(lo_e, F(A0))
            kk = kfun(e, B0)
            opening.setdefault(kk, []).append(
                dict(a=e, Aex=str(B0), P=str(P1), U=dump_table(Us)))
            cur = st.get(kk)
            if cur is None: st[kk] = [Us, P1, B0]
            else:
                cur[0] = looser(cur[0], Us)
                cur[1] = max(cur[1], P1)
                cur[2] = max(cur[2], B0)
    rec['opening'] = opening
    rounds = 0
    converged = False
    for _round in range(600):
        rounds = _round + 1
        changed = False
        newst = {}
        for kk, (U, P, Aex) in list(st.items()):
            a = kk if key == 'a' else kk[0]
            if add(U, a + 1, 0, F(Aex, 7), True) is not None:
                rec['exit_state'] = [str(kk[0]), str(kk[1])]
                return False, -1, F(7), rec
            compl, nst, pmax = reach_utc(U, t, P, a + 2)
            frontier_global = max(frontier_global, pmax)
            if not compl:
                continue
            Zs = tzones(U, t)
            for b in range(6):
                if b == a: continue
                for A, B, e, x in Zs[b]:
                    if e >= P or e >= F(7): continue
                    V = gt(U, Aex, a + 1, A, b + 1)
                    if V is None: continue
                    V = gt(V, B, b + 1, Aex, a + 1)
                    if V is None: continue
                    Pc = x
                    k2 = kfun(b, B)
                    cur = newst.get(k2)
                    if cur is None: newst[k2] = [V, Pc, B]
                    else:
                        cur[0] = looser(cur[0], V)
                        cur[1] = max(cur[1], Pc)
                        cur[2] = max(cur[2], B)
        for k2, val in newst.items():
            if k2 not in st:
                st[k2] = val; changed = True
            else:
                old = st[k2]
                nl = looser(old[0], val[0]); nP = max(old[1], val[1]); nA = max(old[2], val[2])
                if nl != old[0] or nP != old[1] or nA != old[2]:
                    st[k2] = [nl, nP, nA]; changed = True
        if not changed:
            converged = True
            break
    rec['rounds'] = rounds
    rec['converged'] = converged
    rec['frontier'] = str(frontier_global)
    rec['final'] = [dict(a=kk[0], Aex=str(kk[1]), P=str(v[1]), storedAex=str(v[2]),
                         U=dump_table(v[0]))
                    for kk, v in sorted(st.items())]
    if not converged:
        rec['exit_state'] = None
        return False, len(st), frontier_global, rec
    return True, len(st), frontier_global, rec

def main():
    box = (1, 1, 1, 5, 7, 12)          # smallest checkpoint-killed aA box (nstates=1)
    killed, nst, ceil, rec = merged_kill_recorded(box, 'aA')
    # cross-check against the checkpoint line
    ck = None
    with open(os.path.join(HERE, 'm4comp_uclosure_ckpt_v2.jsonl')) as f:
        for line in f:
            d = json.loads(line)
            if d['key'] == 'aA' and tuple(d['t']) == box:
                ck = d; break
    match = (ck is not None and ck['killed'] == killed and ck['nstates'] == nst
             and ck['ceil'] == str(ceil))
    rec['ckpt'] = ck
    rec['match'] = match
    rec['killed'] = killed; rec['nstates'] = nst; rec['ceil'] = str(ceil)
    rec['opening'] = {'%d|%s' % k: v for k, v in rec['opening'].items()}
    out = os.path.join(HERE, 'm4fix_recompute_%s.json' % '_'.join(map(str, box)))
    with open(out, 'w') as f:
        json.dump(rec, f, indent=1)
    print('box', box, 'killed', killed, 'nstates', nst, 'ceil', ceil,
          'rounds', rec.get('rounds'), 'converged', rec.get('converged'))
    print('checkpoint line match:', match)
    print('opening states:', len(rec['opening']))
    for k, v in sorted(rec['opening'].items()):
        print('  opening key', k, 'openings', len(v))
    print('final states:', [(r['a'], r['Aex']) for r in rec['final']])
    for r in rec['final']:
        print('  state a=%s Aex=%s P=%s' % (r['a'], r['Aex'], r['P']))
        for i, row in enumerate(r['U']):
            print('   row%d %s' % (i, row))
    print('dump:', out, os.path.getsize(out), 'bytes')

if __name__ == '__main__':
    main()
