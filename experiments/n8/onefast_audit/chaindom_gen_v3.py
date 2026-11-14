# chaindom_gen_v3.py -- stage 3: FINAL data for Fresh/ChainDomData.lean
#
# Transcribed-trace-table pattern: for each of the 3 boxes with a sparse-start (u0Of, a=0,
# Aex=1) single-chain dominator, run the attesting chain from the SPARSE table with the Lean
# semantics mirror (uStep = two uAdds), snapshot the table after each STEP (T_1..T_T), verify
# survival + final entries <= caps at every record pair, re-verify the dump controls
# (chains_enumerated / jprov / join_domination_all_chains), and EMIT the Lean file
# LonelyRunnerFresh/Fresh/ChainDomData.lean (the ONLY new Fresh file; nothing else edited).
#
# Controls: [T 3/3] per-box (dump regression flags reproduced) + record caps verified.
# Exact Fractions throughout; floats nowhere.  Nothing committed.
import os, sys, json, time
from fractions import Fraction as F

N8 = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
os.chdir(N8)
src = open('j2_cycle_v2.py').read()
exec(src.split("\nif __name__ == '__main__':")[0])
# have: mk, add, gt, zones (via j2_nchain_v8)

# ---- Lean semantics mirror (values only; Fresh/UClosureKill verbatim) ----
def l_keepcur(U, i, j, c, s):
    e = U[i][j]
    if e is None: return False
    cc, ss = e
    return cc < c or (cc == c and (ss or not s))
def l_back(U, i, j, c, s):
    e = U[j][i]
    if e is None: return False
    d, t = e
    pr = d * c
    return pr < 1 or (pr == 1 and (s or t))
def l_tighter(nv, old):
    if old is None: return nv
    w0, w1 = old
    if nv[0] < w0 or (nv[0] == w0 and nv[1] and not w1): return nv
    return old
def l_prop(U, i, j, c, s):
    V = [[U[p][q] for q in range(7)] for p in range(7)]
    for p in range(7):
        a = U[p][i]
        if a is None: continue
        for q in range(7):
            b = U[j][q]
            if b is None: continue
            V[p][q] = l_tighter((a[0] * c * b[0], a[1] or s or b[1]), V[p][q])
    return V
def l_add(U, i, j, c, s):
    if l_keepcur(U, i, j, c, s): return U
    if l_back(U, i, j, c, s): return None
    return l_prop(U, i, j, c, s)
def l_gt(U, A, a, B, b):
    if A > 0 and B <= 0: return U
    if A <= 0 and B > 0: return None
    if A == 0: return U if B < 0 else None
    if B == 0: return U if A > 0 else None
    if A > 0: return l_add(U, a, b, F(A, B), True)
    return l_add(U, b, a, F(-B, -A), True)
def l_step_snap(U, a, b, Aex, A, B):
    V = l_gt(U, Aex, a, A, b)
    if V is None: return None
    return l_gt(V, B, b, Aex, a)

def strip(T):
    return [[None if e is None else (e[0], e[1]) for e in row] for row in T]

def join_tables(Ts):
    J = [r[:] for r in Ts[0]]
    for W in Ts[1:]:
        for i in range(7):
            for j in range(7):
                a, b = J[i][j], W[i][j]
                if a is None or b is None: J[i][j] = None
                elif b[0] > a[0] or (b[0] == a[0] and a[1] and not b[1]): J[i][j] = b
    return J

def w0chains2(n):
    U0 = mk(n); Z = zones(n); out = []
    def rec(U, a, Aex, seen, w):
        W = add(U, a, 0, F(Aex, 7), True)
        if W is not None: out.append((W, U, w, a, Aex))
        for b, Bn, Ax in Z:
            if (b, Ax) in seen: continue
            V = gt(U, Aex, a, Bn, b)
            if V is None: continue
            V = gt(V, Ax, b, Aex, a)
            if V is None: continue
            rec(V, b, Ax, seen | {(b, Ax)}, w + [(b, Bn, Ax)])
    for y, Bn, Ax in Z:
        V = add(U0, 0, y, F(1, Bn), True)
        if V is None: continue
        V = add(V, y, 0, F(Ax), True)
        if V is None: continue
        rec(V, y, Ax, {(y, Ax)}, [(y, Bn, Ax)])
    return out

FQ = F
# box name -> (n, records [(x,y,P,Q,cap)], sparse entries {(i,j):(v,s)})
DATA = [
    ('1_3_4_4_5_5_7', (1,3,4,4,5,5,7),
     [(6,0,13,3,FQ(1,7)), (6,1,65,31,FQ(33,70)), (6,1,5,3,FQ(33,70)), (6,1,65,47,FQ(33,70)),
      (6,2,5,3,FQ(825,1457)), (6,2,65,47,FQ(825,1457)), (6,2,13,11,FQ(825,1457)), (6,2,65,63,FQ(825,1457))],
     {(0,6):(FQ(2,13),False), (1,6):(FQ(7,13),False), (2,6):(FQ(9,13),True)}),
    ('1_3_4_5_6_6_7', (1,3,4,5,6,6,7),
     [(6,0,13,3,FQ(1,7)), (6,1,65,31,FQ(99,235)), (6,1,5,3,FQ(99,235)), (6,1,65,47,FQ(99,235)),
      (6,2,5,3,FQ(363,611)), (6,2,65,47,FQ(363,611)), (6,2,13,11,FQ(363,611)), (6,2,65,63,FQ(363,611))],
     {(0,6):(FQ(2,13),False), (1,6):(FQ(7,13),False), (2,6):(FQ(9,13),False)}),
    ('1_4_4_5_6_6_7', (1,4,4,5,6,6,7),
     [(6,0,13,3,FQ(1,7)), (6,1,5,3,FQ(3179,5499)), (6,1,65,47,FQ(3179,5499)), (6,1,13,11,FQ(3179,5499))],
     {(0,6):(FQ(2,13),False), (1,6):(FQ(9,13),True)}),
]

def sparse_tab(entries):
    T = [[None]*7 for _ in range(7)]
    for i in range(7): T[i][i] = (FQ(1), False)
    for (i, j), (v, s) in entries.items(): T[i][j] = (v, s)
    return T

def main():
    jsonl = {}
    for l in open('onefast_audit/joinedge2_perbox_v1.jsonl'):
        r = json.loads(l); jsonl[tuple(r['box'])] = r
    log = open('onefast_audit/chaindom_gen_v3.out', 'w')
    out = {}
    allctrl = True
    for (name, n, recs, sp) in DATA:
        t0 = time.time()
        dump = jsonl[n]
        spT = sparse_tab(sp)
        caps = {}; pairs = []
        for (x, y, P, Q, cap) in recs:
            if (y, x) not in caps or cap < caps[(y, x)]: caps[(y, x)] = cap
            if (y, x) not in pairs: pairs.append((y, x))
        # full-start enumeration (for the dump controls + the chain words)
        chains = w0chains2(n)
        c1 = (len(chains) == dump['chains_enumerated'])
        closed = [strip(W) for (W, V, w, a, A) in chains]
        J = join_tables(closed)
        jprov_ok = True; join_dom_ok = True
        for key, att_dump in dump['jprov'].items():
            i, j = (int(t) for t in key.split(','))
            jv = J[i][j][0]; att = None
            for ci, T in enumerate(closed):
                e = T[i][j]
                if e is not None:
                    if e[0] > jv: join_dom_ok = False
                    if att is None and e[0] == jv: att = ci
            if att_dump != att: jprov_ok = False
            if att is None: join_dom_ok = False
        ctrl = c1 and jprov_ok and join_dom_ok and dump['regression']['join_domination_all_chains']
        allctrl = allctrl and ctrl
        # sparse-start dominators, shortest first
        cands = []
        for ci, (W, V, w, a, A) in enumerate(chains):
            U = [row[:] for row in spT]; aS, AexS = 0, FQ(1); ok = True
            for (b, Bn, Ax) in w:
                V2 = l_step_snap(U, aS, b, AexS, FQ(Bn), FQ(Ax))
                if V2 is None: ok = False; break
                U, aS, AexS = V2, b, FQ(Ax)
            if ok and all(U[y][x] is not None and U[y][x][0] <= caps[(y, x)] for (y, x) in pairs):
                cands.append((len(w), ci))
        cands.sort()
        if not cands:
            print('%s: NO sparse dominator (unexpected)' % name); continue
        L, chosen = cands[0]
        word = chains[chosen][2]
        # instrumented sparse run: snapshot after each STEP
        U = [row[:] for row in spT]; aS, AexS = 0, FQ(1)
        snaps = []; steps_data = []
        for (b, Bn, Ax) in word:
            V2 = l_step_snap(U, aS, b, AexS, FQ(Bn), FQ(Ax))
            assert V2 is not None, 'sparse run died'
            U, aS, AexS = V2, b, FQ(Ax)
            snaps.append(strip(U))
            steps_data.append((b, Bn, Ax))
        # final verification: entries <= caps at every record pair
        finals = {}
        for (y, x) in pairs:
            e = U[y][x]; assert e is not None
            assert e[0] <= caps[(y, x)], 'cap violated'
            finals['%d,%d' % (y, x)] = [str(e[0]), e[1]]
        out[name] = {'box': list(n), 'chain_index': chosen, 'word_len': L,
                     'steps': [[b, Bn, Ax] for (b, Bn, Ax) in steps_data],
                     'tables': [[[ [p, q, str(T[p][q][0]), T[p][q][1]] for q in range(7)
                                   if T[p][q] is not None] for p in range(7)] for T in snaps],
                     'finals': finals,
                     'caps': {'%d,%d' % k: str(caps[k]) for k in caps},
                     'records': [[x, y, P, Q, str(cap)] for (x, y, P, Q, cap) in recs],
                     'sparse': [[i, j, str(v), s] for (i, j), (v, s) in sorted(sp.items())],
                     'controls': {'chains_enumerated': c1, 'jprov': jprov_ok,
                                  'join_domination_all_chains': join_dom_ok,
                                  'dump_flag': dump['regression']['join_domination_all_chains'],
                                  'overall': ctrl}}
        line = ('%s ctrl=%s chosen ci=%d len=%d steps=%d tables=%d t=%.1fs' %
                (name, ctrl, chosen, L, len(steps_data), len(snaps), time.time() - t0))
        print(line, flush=True); log.write(line + '\n'); log.flush()
    json.dump(out, open('onefast_audit/chaindom_data_v3.json', 'w'), indent=1)
    log.write('ALL CONTROLS: %s\n' % allctrl); log.close()
    print('=== gen v3 done; ALL CONTROLS %s' % allctrl, flush=True)

if __name__ == '__main__':
    main()
