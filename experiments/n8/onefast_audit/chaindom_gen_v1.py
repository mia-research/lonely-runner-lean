# chaindom_gen_v1.py -- per-chain J-carrier data for Fresh/ChainDomData.lean
#
# For the 11 strict-complete boxes of joinedge2_perbox_v1.jsonl (census section 7): recompute
# the W0 chain enumeration VERBATIM (j2_cycle_v2.w0chains machinery), verify against the
# dump's per-box records (chains_enumerated, jprov first-attesting-chain per join entry,
# join_domination_all_chains), and find the ATTESTING CHAIN for each banked compFam record
# (Fresh/OneSidedComposed.compFam_<box>, the 52 strict-class records): a chain whose trace
# dominates the record's cap at the record's pair (y, x).
#
# Two start tables are tracked:
#   FULL  mk(n)        -- the dump's own start (chain closed tables = the dump's Cs);
#   SPARSE u0Tab_<box> -- Fresh/DumpDomData.u0Of's literal (exact at census pairs, diagonal
#                         default elsewhere): the start the corrected consumption
#                         capChainsRealized_of_chainDomU0 fixes.  The deliverable datum is
#                         the trace of the attesting chain FROM THE SPARSE TABLE, folded by
#                         the Lean semantics mirror (l_chainrun: uStep/uGt/uAdd/uProp/
#                         uTighter/uKeepCur/uBack of Fresh/UClosureKill, value-verbatim).
#
# NEW files only (chaindom_gen_v1.py/.out/chaindom_data_v1.json); nothing existing modified.
# Exact Fractions throughout; floats nowhere.  Nothing committed.
import os, sys, json, time
from fractions import Fraction as F

N8 = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
os.chdir(N8)  # the machinery opens its files by relative name
src = open('j2_cycle_v2.py').read()
exec(src.split("\nif __name__ == '__main__':")[0])
# have: mk, add, gt, zones (j2_nchain_v8 via j2_cycle_v2)

def strip(T):
    return [[None if e is None else (e[0], e[1]) for e in row] for row in T]

def join_tables(Ts):
    # verbatim joinedge_perbox_v1.join_tables (j2_cycle_v6/v7)
    J = [r[:] for r in Ts[0]]
    for W in Ts[1:]:
        for i in range(7):
            for j in range(7):
                a, b = J[i][j], W[i][j]
                if a is None or b is None: J[i][j] = None
                elif b[0] > a[0] or (b[0] == a[0] and a[1] and not b[1]): J[i][j] = b
    return J

# ---- chain enumeration with pre-end tracking (structure verbatim w0chains) ----
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

# ---- Lean semantics mirror (Fresh/UClosureKill, values only) ----
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

def l_step(U, a, b, Aex, A, B):
    V = l_gt(U, Aex, a, A, b)
    if V is None: return None
    return l_gt(V, B, b, Aex, a)

def l_chainrun(U, a, Aex, steps):
    # steps: list of (b, A, B) -- Fresh.Step fields; returns None or (U', a', Aex')
    for (b, A, B) in steps:
        V = l_step(U, a, b, Aex, A, B)
        if V is None: return None
        U, a, Aex = V, b, B
    return U, a, Aex

# ---- the 11 strict boxes; banked compFam records (x, y, P, Q, cap); sparse u0Of tables ----
FQ = F
BOXES = [
    ((1,3,4,4,5,5,7), '1_3_4_4_5_5_7',
     [(6,0,13,3,FQ(1,7)), (6,1,65,31,FQ(33,70)), (6,1,5,3,FQ(33,70)), (6,1,65,47,FQ(33,70)),
      (6,2,5,3,FQ(825,1457)), (6,2,65,47,FQ(825,1457)), (6,2,13,11,FQ(825,1457)), (6,2,65,63,FQ(825,1457))],
     {(0,6):(FQ(2,13),False), (1,6):(FQ(7,13),False), (2,6):(FQ(9,13),True)}),
    ((1,3,4,5,5,5,7), '1_3_4_5_5_5_7',
     [(6,0,13,3,FQ(1870,13113)), (6,1,65,31,FQ(55,117)), (6,1,5,3,FQ(55,117)), (6,1,65,47,FQ(55,117))],
     {(0,6):(FQ(2,13),False), (1,6):(FQ(7,13),False)}),
    ((1,3,4,5,6,6,7), '1_3_4_5_6_6_7',
     [(6,0,13,3,FQ(1,7)), (6,1,65,31,FQ(99,235)), (6,1,5,3,FQ(99,235)), (6,1,65,47,FQ(99,235)),
      (6,2,5,3,FQ(363,611)), (6,2,65,47,FQ(363,611)), (6,2,13,11,FQ(363,611)), (6,2,65,63,FQ(363,611))],
     {(0,6):(FQ(2,13),False), (1,6):(FQ(7,13),False), (2,6):(FQ(9,13),False)}),
    ((1,3,4,5,7,7,9), '1_3_4_5_7_7_9',
     [(5,0,13,3,FQ(594,4277)), (5,1,65,31,FQ(99,235)), (5,1,5,3,FQ(99,235)), (5,1,65,47,FQ(99,235))],
     {(0,5):(FQ(2,13),True), (1,5):(FQ(7,13),True)}),
    ((1,4,4,5,6,6,7), '1_4_4_5_6_6_7',
     [(6,0,13,3,FQ(1,7)), (6,1,5,3,FQ(3179,5499)), (6,1,65,47,FQ(3179,5499)), (6,1,13,11,FQ(3179,5499))],
     {(0,6):(FQ(2,13),False), (1,6):(FQ(9,13),True)}),
    ((1,4,5,5,5,6,7), '1_4_5_5_5_6_7',
     [(6,0,13,3,FQ(50,351)), (6,1,5,3,FQ(23375,41067)), (6,1,65,47,FQ(23375,41067)), (6,1,13,11,FQ(23375,41067))],
     {(0,6):(FQ(2,13),False), (1,6):(FQ(9,13),False)}),
    ((1,4,5,5,6,7,9), '1_4_5_5_6_7_9',
     [(3,0,49,15,FQ(98,527)), (3,1,49,39,FQ(245,341)), (3,1,49,47,FQ(245,341)), (3,1,49,55,FQ(245,341))],
     {(0,3):(FQ(2,9),True), (1,3):(FQ(1),True)}),
    ((1,4,5,6,6,7,8), '1_4_5_6_6_7_8',
     [(6,0,73,15,FQ(6,47)), (6,1,73,47,FQ(27,47)), (6,1,73,55,FQ(27,47)), (6,1,73,63,FQ(27,47))],
     {(0,6):(FQ(2,15),False), (1,6):(FQ(3,5),False)}),
    ((1,5,5,5,6,7,8), '1_5_5_5_6_7_8',
     [(6,0,73,15,FQ(6358,49491)), (6,1,73,47,FQ(3179,5499)), (6,1,73,55,FQ(3179,5499)), (6,1,73,63,FQ(3179,5499))],
     {(0,6):(FQ(2,15),False), (1,6):(FQ(11,15),True)}),
    ((1,5,5,6,6,7,8), '1_5_5_6_6_7_8',
     [(6,0,73,15,FQ(6,47)), (6,1,73,47,FQ(3179,5499)), (6,1,73,55,FQ(3179,5499)), (6,1,73,63,FQ(3179,5499))],
     {(0,6):(FQ(2,15),False), (1,6):(FQ(11,15),True)}),
    ((1,5,5,6,7,8,8), '1_5_5_6_7_8_8',
     [(2,0,49,15,FQ(311542,1639125)), (2,1,49,47,FQ(155771,170469)), (2,1,49,55,FQ(155771,170469)), (2,1,7,9,FQ(155771,170469))],
     {(0,2):(FQ(2,9),True), (1,2):(FQ(1),True)}),
]

def sparse_tab(entries):
    T = [[None]*7 for _ in range(7)]
    for i in range(7): T[i][i] = (FQ(1), False)
    for (i, j), (v, s) in entries.items(): T[i][j] = (v, s)
    return T

def entry_le(T, i, j, cap):
    e = T[i][j]
    return e is not None and e[0] <= cap

def main():
    only = set(eval(sys.argv[1])) if len(sys.argv) > 1 else None
    jsonl = {}
    for l in open('onefast_audit/joinedge2_perbox_v1.jsonl'):
        r = json.loads(l); jsonl[tuple(r['box'])] = r
    out = {'boxes': {}, 'controls': {}}
    log = open('onefast_audit/chaindom_gen_v1.out', 'w')
    for (n, name, recs, sp_entries) in BOXES:
        if only is not None and n not in only: continue
        t0 = time.time()
        dump = jsonl[n]
        chains = w0chains2(n)          # (W_closed, V_preend, word, a_last, Aex_last)
        # control 1: chains_enumerated
        c1 = (len(chains) == dump['chains_enumerated'])
        closed = [strip(W) for (W, V, w, a, A) in chains]
        # control 2/3: jprov + join_domination_all_chains (recompute)
        J = join_tables(closed)
        jprov_ok = True; join_dom_ok = True
        for key, att_dump in dump['jprov'].items():
            i, j = (int(t) for t in key.split(','))
            jv = J[i][j][0]
            att = None
            for ci, T in enumerate(closed):
                e = T[i][j]
                if e is not None:
                    if e[0] > jv: join_dom_ok = False
                    if att is None and e[0] == jv: att = ci
            if att_dump != att: jprov_ok = False
            if att is None: join_dom_ok = False
        # control 4: dump closed tables == my closed (via the plain machinery W = add(V, a,0,Aex/7))
        # (implicit: c1 + jprov/join_dom agreement already pin the enumeration; also assert
        #  the Lean-mirror from the FULL start reproduces every pre-end table)
        mirror_ok = True
        for (W, V, w, a, A) in chains:
            r = l_chainrun(strip(mk(n)), 0, 1, w)
            if r is None or strip(r[0]) != strip(V) or r[1] != a or r[2] != A:
                mirror_ok = False; break
        # per-record attestation
        sp = sparse_tab(sp_entries)
        recdata = []
        inter_sp = None; inter_fullV = None; inter_fullW = None
        for (x, y, P, Q, cap) in recs:
            attW = [ci for ci, T in enumerate(closed) if entry_le(T, y, x, cap)]
            attV = []
            attSP = []; spTab = {}
            for ci, (W, V, w, a, A) in enumerate(chains):
                if entry_le(strip(V), y, x, cap): attV.append(ci)
                r = l_chainrun([row[:] for row in sp], 0, 1, w)
                if r is not None:
                    if entry_le(strip(r[0]), y, x, cap): attSP.append(ci)
            inter_fullW = set(attW) if inter_fullW is None else inter_fullW & set(attW)
            inter_fullV = set(attV) if inter_fullV is None else inter_fullV & set(attV)
            inter_sp = set(attSP) if inter_sp is None else inter_sp & set(attSP)
            recdata.append({'x': x, 'y': y, 'P': P, 'Q': Q, 'cap': str(cap),
                            'attW_n': len(attW), 'attV_n': len(attV), 'attSP_n': len(attSP),
                            'attSP_sample': (min(attSP) if attSP else None)})
        inter_sp = sorted(inter_sp or [])
        # choose: shortest word among the sparse-start dominators
        chosen = None
        if inter_sp:
            chosen = min(inter_sp, key=lambda ci: (len(chains[ci][2]), ci))
        W0, V0, word, alast, Axlast = chains[chosen] if chosen is not None else (None,)*5
        spres = None
        if chosen is not None:
            r = l_chainrun([row[:] for row in sp], 0, 1, word)
            spres = {'table': [[None if e is None else [str(e[0]), e[1]] for e in row]
                               for row in strip(r[0])],
                     'af': r[1], 'Af': str(r[2]),
                     'entries_at_pairs': {f'{y},{x}': ([str(strip(r[0])[y][x][0]),
                                                        strip(r[0])[y][x][1]])
                                          for (x, y, P, Q, cap) in set(recs)}}
        out['boxes'][name] = {
            'box': list(n), 'n_chains': len(chains),
            'controls': {'chains_enumerated': c1, 'jprov': jprov_ok,
                         'join_domination_all_chains': join_dom_ok,
                         'lean_mirror_full_start': mirror_ok,
                         'dump_join_dom_flag': dump['regression']['join_domination_all_chains']},
            'records': recdata,
            'inter_sizes': {'fullW': len(inter_fullW or []), 'fullV': len(inter_fullV or []),
                            'sparse': len(inter_sp)},
            'chosen': {'ci': chosen, 'word': word, 'a_last': alast, 'Aex_last': str(Axlast)},
            'sparse_result': spres}
        line = ('%s chains=%d ctrl(c1=%s jprov=%s joinDom=%s mirror=%s) inter(W,V,sp)=(%d,%d,%d) '
                'chosen=%s word=%s t=%.1fs' %
                (name, len(chains), c1, jprov_ok, join_dom_ok, mirror_ok,
                 len(inter_fullW or []), len(inter_fullV or []), len(inter_sp),
                 chosen, word, time.time() - t0))
        print(line, flush=True); log.write(line + '\n'); log.flush()
    json.dump(out, open('onefast_audit/chaindom_data_v1.json', 'w'), indent=1)
    log.close()
    print('=== chaindom_gen_v1 done; data in onefast_audit/chaindom_data_v1.json', flush=True)

if __name__ == '__main__':
    main()
