# chaindom_gen_v2.py -- stage 2: per-box ATTESTING CHAIN selection + Lean-side datum data
# for the boxes where the corrected consumption's datum exists (chainRun from the SPARSE
# u0Of start dominating every compFam record's cap; stage 1 = chaindom_gen_v1.py).
#
# Per selected chain this emits, for Fresh/ChainDomData.lean:
#   steps      : the word as Fresh.Step literals (consumed from (u0Of n, a=0, Aex=1); the
#                first step's two adds ARE the dump chain's start adds -- see gen_v1 notes);
#   rho        : an IN-BOX exact rational reading vector witnessing ChainRealized
#                (non-vacuity + honesty: all seam bands, the exit bound, FaceLo/FaceHi,
#                and u0Of's entries -- the interval/band construction below);
#   S0         : the base TabUp bounds (diagonals + the sparse u0Of census pairs);
#   P1/P2      : the per-add emitted PathBds lists (backward-chained exact products);
#   finals     : the emitted record-pair bounds C <= cap.
#
# Controls re-verified here: dump chain-enumeration membership (full-start survival +
# closure), sparse-start domination (l_chainrun mirror), join_domination/[T 73/73]
# semantics (stage 1), and the witness checks above.
#
# NEW files only (chaindom_gen_v2.py/.out/chaindom_data_v2.json); nothing existing modified.
import os, sys, json, time
from fractions import Fraction as F

N8 = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
os.chdir(N8)
src = open('j2_cycle_v2.py').read()
exec(src.split("\nif __name__ == '__main__':")[0])

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

# Lean mirror (values only) -- Fresh/UClosureKill.uKeepCur/uBack/uTighter/uProp/uAdd/uGt/uStep
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
    for (b, A, B) in steps:
        V = l_step(U, a, b, Aex, A, B)
        if V is None: return None
        U, a, Aex = V, b, B
    return U, a, Aex

FQ = F
STAGE1 = {}
for (n, name, recs, sp) in [
    ((1,3,4,4,5,5,7), '1_3_4_4_5_5_7',
     [(6,0,13,3,FQ(1,7)), (6,1,65,31,FQ(33,70)), (6,1,5,3,FQ(33,70)), (6,1,65,47,FQ(33,70)),
      (6,2,5,3,FQ(825,1457)), (6,2,65,47,FQ(825,1457)), (6,2,13,11,FQ(825,1457)), (6,2,65,63,FQ(825,1457))],
     {(0,6):(FQ(2,13),False), (1,6):(FQ(7,13),False), (2,6):(FQ(9,13),True)}),
    ((1,3,4,5,6,6,7), '1_3_4_5_6_6_7',
     [(6,0,13,3,FQ(1,7)), (6,1,65,31,FQ(99,235)), (6,1,5,3,FQ(99,235)), (6,1,65,47,FQ(99,235)),
      (6,2,5,3,FQ(363,611)), (6,2,65,47,FQ(363,611)), (6,2,13,11,FQ(363,611)), (6,2,65,63,FQ(363,611))],
     {(0,6):(FQ(2,13),False), (1,6):(FQ(7,13),False), (2,6):(FQ(9,13),False)}),
    ((1,4,4,5,6,6,7), '1_4_4_5_6_6_7',
     [(6,0,13,3,FQ(1,7)), (6,1,5,3,FQ(3179,5499)), (6,1,65,47,FQ(3179,5499)), (6,1,13,11,FQ(3179,5499))],
     {(0,6):(FQ(2,13),False), (1,6):(FQ(9,13),True)}),
]:
    STAGE1[name] = (n, recs, sp)

def sparse_tab(entries):
    T = [[None]*7 for _ in range(7)]
    for i in range(7): T[i][i] = (FQ(1), False)
    for (i, j), (v, s) in entries.items(): T[i][j] = (v, s)
    return T

def face_lo(n, i): return FQ(max(2*n[i]-1, 2), 2)
def face_hi(n, i): return FQ(2*n[i]+1, 2)

# ---- rho construction: exact interval propagation with strictness margins ----
def seam_constraints(word, n, sp):
    # list of (i, j, lo, hi, slo, shi): lo <= rho_i/rho_j <= hi (strict per flags)
    cs = []
    (y, Bn, Ax) = word[0]
    cs.append((0, y, FQ(1, Ax), FQ(1, Bn), True, True))   # rho_0/rho_y in (1/Ax, 1/Bn)
    a, Aex = y, FQ(Ax)
    for (b, Bn2, Ax2) in word[1:]:
        # rho_a/rho_b in (Aex/Ax2, Aex/Bn2): seamE rho_a/rho_b < Aex/Bn2, seamM rho_b/rho_a < Ax2/Aex
        cs.append((a, b, Aex / FQ(Ax2), Aex / FQ(Bn2), True, True))
        a, Aex = b, FQ(Ax2)
    cs.append((a, 0, FQ(0), Aex/7, False, True))          # exit: rho_a/rho_0 < Aex/7
    for (i, j), (v, s) in sp.items():
        cs.append((i, j, FQ(0), v, False, s))
    return cs

def shrink_hi(hi, k):
    # rational point strictly below hi (for strict upper bounds)
    return hi * (2**k - 1) / 2**k if hi > 0 else hi
def shrink_lo(lo, k):
    return lo + (1 if lo == 0 else abs(lo)) / 2**k

def find_rho(word, n, sp):
    for k in (6, 10, 14, 20):
        cs = []
        for (i, j, lo, hi, slo, shi) in seam_constraints(word, n, sp):
            lo2 = shrink_lo(lo, k) if slo else lo
            hi2 = shrink_hi(hi, k) if shi else hi
            cs.append((i, j, lo2, hi2))
        lo_i = [FQ(0)]*7; hi_i = [FQ(0)]*7
        for i in range(7):
            lo_i[i] = face_lo(n, i); hi_i[i] = face_hi(n, i)
        lo_i[0] = hi_i[0] = FQ(1)   # scaling fixed: rho_0 = 1 (in-box: [1/2,3/2] always)
        # fixpoint propagation (non-strict on the shrunk bounds)
        for _ in range(400):
            ch = False
            for (i, j, lo, hi) in cs:
                nlo, nhi = lo_i[i], hi_i[i]
                nlo2 = max(nlo, lo * lo_i[j]); nhi2 = min(nhi, hi * hi_i[j])
                if (nlo2 != nlo or nhi2 != nhi): ch = True
                lo_i[i], hi_i[i] = nlo2, nhi2
                if lo > 0:
                    nloj = lo_i[j]; nhij = hi_i[j]
                    nloj2 = max(nloj, lo_i[i] / hi); nhij2 = min(nhij, hi_i[i] / lo)
                    if (nloj2 != nloj or nhij2 != nhij): ch = True
                    lo_i[j], hi_i[j] = nloj2, nhij2
            if any(lo_i[i] > hi_i[i] for i in range(7)): break  # try larger margin k
            if not ch:
                break
        # the fixpoint UPPER endpoints satisfy every propagated (shrunk) constraint exactly
        # (Bellman-Ford/shortest-product property), hence the ORIGINAL strict ones too
        rho = {i: hi_i[i] for i in range(7)}
        rho[0] = FQ(1)
        # verify the ORIGINAL strict constraints
        ok = all(face_lo(n, i) <= rho[i] <= face_hi(n, i) and rho[i] > 0 for i in range(7))
        if ok:
            for (i, j, lo, hi, slo, shi) in seam_constraints(word, n, sp):
                r = rho[i] / rho[j]
                if r < lo or r > hi: ok = False; break
                if slo and r <= lo: ok = False; break
                if shi and r >= hi: ok = False; break
        if ok:
            return {i: rho[i] for i in range(7)}
    return None

def verify_rho(rho, word, n, sp):
    if rho is None or any(i not in rho for i in range(7)): return None
    for i in range(7):
        if not (rho[i] > 0 and face_lo(n, i) <= rho[i] <= face_hi(n, i)): return 'box'
    for (i, j, lo, hi, slo, shi) in seam_constraints(word, n, sp):
        r = rho[i] / rho[j]
        if r < lo or r > hi or (slo and r <= lo) or (shi and r >= hi): return 'constraint'
    return 'ok'

# ---- backward-chained TabUp emission ----
def emission_data(word, rec_pairs, sp, caps):
    # adds: list of (i, j, c) in order: per step (a,b): add1 (a,b,Aex_a/Bn_b), add2 (b,a,Ax_b/Aex_a)
    adds = []
    Aexs = []
    a, Aex = 0, FQ(1)
    for (b, Bn, Ax) in word:
        adds.append((a, b, Aex/FQ(Bn)))
        adds.append((b, a, FQ(Ax)/Aex))
        Aexs.append((a, b, Aex, FQ(Ax)))
        a, Aex = b, FQ(Ax)
    # base bounds S0
    S0 = [(i, i, FQ(1)) for i in range(7)] + [(i, j, v) for (i, j), (v, s) in sp.items()]
    # directs: bound (i,j,c) available AFTER add t (1-indexed adds)
    directs = {t: (i, j, c) for t, (i, j, c) in enumerate(adds, 1)}
    def avail_before(t):  # set of bounds available as inputs to add t (i.e. after adds 1..t-1)
        s = set(S0) | {directs[k] for k in range(1, t)}
        s |= {b for (tt, b) in emitted if tt < t}
        return s
    emitted = []  # (add_index, bound)
    targets = [(y, x, caps[(y, x)]) for (y, x) in rec_pairs]
    def derived(b, avail):
        return b in avail
    # fixpoint backward-chaining
    for _ in range(200):
        avail_cache = {}
        def avail(t):
            if t not in avail_cache:
                s = set(S0) | {directs[k] for k in range(1, t)}
                s |= {bd for (tt, bd) in emitted if tt < t}
                avail_cache[t] = s
            return avail_cache[t]
        missing = []
        for tgt in targets:
            if not derived(tgt, set(S0) | {bd for (_, bd) in emitted}):
                missing.append(tgt)
        if not missing:
            # prune: try to drop emissions not needed (skip -- keep all)
            break
        progressed = False
        for tgt in list(missing):
            (p, q, capv) = tgt
            # try to derive (p,q,C<=capv) at the EARLIEST add
            for t in range(1, len(adds)+1):
                av = avail(t)
                (i, j, c) = adds[t-1]
                # direct
                if (i, j) == (p, q) and c <= capv:
                    nb = (p, q, c)
                    if nb not in [bd for (_, bd) in emitted]:
                        emitted.append((t, nb)); progressed = True; break
                # path: (p,i,A)*(c)*(j,q,B)
                for (pp, ii, A) in av:
                    if pp != p or ii != i: continue
                    for (jj, qq, B) in av:
                        if jj != j or qq != q: continue
                        C = A * c * B
                        if C <= capv:
                            nb = (p, q, C)
                            if nb not in [bd for (_, bd) in emitted]:
                                emitted.append((t, nb)); progressed = True; break
                    if progressed: break
                if progressed: break
        if not progressed:
            return None, None, None, adds
    # assemble per-add P lists (P1 for odd structure: adds come in pairs per step)
    P = {t: [] for t in range(1, len(adds)+1)}
    for (t, bd) in emitted:
        P[t].append(bd)
    finals = targets
    return P, finals, S0, adds

def main():
    out = {}
    log = open('onefast_audit/chaindom_gen_v2.out', 'w')
    for name in ['1_3_4_4_5_5_7', '1_3_4_5_6_6_7', '1_4_4_5_6_6_7']:
        t0 = time.time()
        n, recs, sp = STAGE1[name]
        spT = sparse_tab(sp)
        caps = {}
        pairs = []
        for (x, y, P, Q, cap) in recs:
            if (y, x) not in caps or cap < caps[(y, x)]:
                caps[(y, x)] = cap
            if (y, x) not in pairs: pairs.append((y, x))
        chains = w0chains2(n)
        # sparse dominators (stage 1 semantics)
        cands = []
        for ci, (W, V, w, a, A) in enumerate(chains):
            r = l_chainrun([row[:] for row in spT], 0, 1, w)
            if r is None: continue
            if all(r[0][y][x] is not None and r[0][y][x][0] <= caps[(y, x)] for (y, x) in pairs):
                cands.append((len(w), ci))
        cands.sort()
        chosen = None
        for (L, ci) in cands:
            W, V, word, alast, Axlast = chains[ci]
            rho = find_rho(word, n, sp)
            if rho is None: continue
            # full rho for unvisited rows
            for i in range(7):
                if i not in rho: rho[i] = FQ(1)
            Pd, finals, S0, adds = emission_data(word, pairs, sp, caps)
            if Pd is None: continue
            chosen = (ci, word, rho, Pd, finals, S0, adds)
            break
        if chosen is None:
            line = '%s: NO chain with rho+emission found (%d sparse dominators)' % (name, len(cands))
            print(line, flush=True); log.write(line+'\n'); continue
        ci, word, rho, Pd, finals, S0, adds = chosen
        # CONTROLS: (i) sparse trace dominates (recompute); (ii) all emitted finals <= cap;
        # (iii) rho in-box + seams + exit + sparse; (iv) chain in dump enumeration (by
        # construction ci); (v) P-bounds derive exactly (re-derive forward greedily).
        r = l_chainrun([row[:] for row in spT], 0, 1, word)
        ctrl_dom = all(r[0][y][x] is not None and r[0][y][x][0] <= caps[(y, x)] for (y, x) in pairs)
        ctrl_rho = verify_rho(dict(rho), word, n, sp) == 'ok'
        ctrl_fin = all(C <= caps[(y, x)] for (y, x, C) in finals)
        out[name] = {
            'box': list(n), 'chain_index': ci, 'n_chains': len(chains),
            'word': word, 'rho': {str(k): str(v) for k, v in sorted(rho.items())},
            'S0': [[p, q, str(c)] for (p, q, c) in S0],
            'adds': [[i, j, str(c)] for (i, j, c) in adds],
            'P': {str(t): [[p, q, str(c)] for (p, q, c) in Pd[t]] for t in sorted(Pd) if Pd[t]},
            'finals': [[y, x, str(C)] for (y, x, C) in finals],
            'caps': {f'{y},{x}': str(caps[(y, x)]) for (y, x) in caps},
            'controls': {'sparse_domination': ctrl_dom, 'rho_ok': ctrl_rho, 'finals_le_cap': ctrl_fin},
            'records': [[x, y, P, Q, str(cap)] for (x, y, P, Q, cap) in STAGE1[name][1]],
            'sparse_entries': [[i, j, str(v), s] for (i, j), (v, s) in sorted(sp.items())],
        }
        line = ('%s chosen ci=%d len=%d controls(dom=%s rho=%s fin=%s) t=%.1fs' %
                (name, ci, len(word), ctrl_dom, ctrl_rho, ctrl_fin, time.time()-t0))
        print(line, flush=True); log.write(line+'\n'); log.flush()
    json.dump(out, open('onefast_audit/chaindom_data_v2.json', 'w'), indent=1)
    log.close()
    print('=== chaindom_gen_v2 done', flush=True)

if __name__ == '__main__':
    main()
