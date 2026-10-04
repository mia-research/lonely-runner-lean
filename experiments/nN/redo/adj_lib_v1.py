# adj_lib_v1 -- adjacency of fine cells of gate-crossing arrangements.  Exact facts: Fractions via cell_rows/path/crosses and exact
# verification of every point used.  Floats (scipy highs) only choose points and propose directions.
import sys, math, time, random, hashlib
sys.path.insert(0, '.')
from fractions import Fraction as F
import numpy as np
from scipy.optimize import linprog
exec(open('tmpl_lib_v1.py').read())          # template(), tstr(), clear_components, path, outcome
from ceil_lib_v1 import cell_rows, sigkey, norm, row_val, row_meaning, solve_exact
BOXROW = [25, 0, 0, 0, 0, 0, -1]             # 25 rho_1 - rho_7 >= 0  (bounded mode)
UB = 1e6
def crosses2(x):
    st, R = path(x)
    return (any(s['setter'] == 0 for s in st) and R > 7), st, R

def rv(a, x):
    return a[0] * x[0] + sum(a[k] * x[k] for k in range(1, 7))

def cell_of(x, box=None):
    """x normalised exact list (sorted, x[0]=1).  returns dict rows, tags, sig, steps, R"""
    rows, tags, (steps, R) = cell_rows(x)
    rows = [list(a) for a in rows]; tags = list(tags)
    if box is not None:
        rows.append([box, 0, 0, 0, 0, 0, -1]); tags.append(('box',))
    return rows, tags, steps, R

def hsig(tags, steps):
    return hashlib.blake2b(repr(sigkey(tags, steps)).encode(), digest_size=16).hexdigest()

def sig_of(x, box=None):
    rows, tags, steps, R = cell_of(x, box)
    return hsig(tags, steps), len(steps), R

def groups_of(rows):
    D = {}
    for i, a in enumerate(rows):
        g = math.gcd(*[abs(v) for v in a])
        if g == 0: continue
        D.setdefault(tuple(v // g for v in a), []).append(i)
    return D

def lp_prep(keys):
    A = np.array([[float(v) for v in k[1:]] for k in keys]); b = np.array([float(k[0]) for k in keys])
    n = np.linalg.norm(A, axis=1); n[n == 0] = 1.0
    return A / n[:, None], b / n, n

def cheb(An, bn):
    """max t : bn + An z >= t, z in [1,UB]^6, t<=1"""
    m = len(bn)
    c = np.zeros(7); c[6] = -1.0
    Aub = np.hstack([-An, np.ones((m, 1))]); bub = bn
    r = linprog(c, A_ub=Aub, b_ub=bub, bounds=[(1, UB)] * 6 + [(None, 1)], method='highs')
    if r.status != 0: return None, None
    return r.x[:6], r.x[6]

def facet_lp(An, bn, i, keys_idx):
    """max t : row i = 0, others >= t (same-hyperplane rows are not in the key list)"""
    m = len(bn)
    others = [j for j in range(m) if j != i]
    c = np.zeros(7); c[6] = -1.0
    Aub = np.hstack([-An[others], np.ones((len(others), 1))]); bub = bn[others]
    Aeq = np.hstack([An[i:i+1], np.zeros((1, 1))]); beq = np.array([-bn[i]])
    r = linprog(c, A_ub=Aub, b_ub=bub, A_eq=Aeq, b_eq=beq, bounds=[(1, UB)] * 6 + [(None, 1)], method='highs')
    if r.status != 0: return None, None
    return r.x[:6], r.x[6]

def ratz(z, den):
    return [F(1)] + [F(float(t)).limit_denominator(den) for t in z]

def project_to(a, x):
    """exact projection of x (list 7, x[0]=1) onto a.x = 0 within the slice: moves x[1:] along a[1:]"""
    v = rv(a, x); n2 = sum(F(t) * t for t in a[1:])
    return [x[0]] + [x[k] - v * a[k] / n2 for k in range(1, 7)]


# ---------- exact linear algebra helpers (Fractions) ----------
def indep(vecs):
    """indices of a maximal subset independent in the variable part (cols 1..6) ; returns list of indices"""
    basis = []; piv = []; keep = []
    for i, v in enumerate(vecs):
        w = [F(t) for t in v[1:]]
        for b, pc in zip(basis, piv):
            if w[pc] != 0:
                f = w[pc] / b[pc]; w = [wi - f * bi for wi, bi in zip(w, b)]
        pc = next((k for k, t in enumerate(w) if t != 0), None)
        if pc is not None:
            basis.append(w); piv.append(pc); keep.append(i)
    return keep

def gram_solve(Eg, rhs):
    """solve (Eg Eg^T) lam = rhs exactly; Eg independent rows (variable parts)"""
    k = len(Eg)
    G = [[sum(F(Eg[a][m]) * Eg[b][m] for m in range(6)) for b in range(k)] for a in range(k)]
    return solve_exact(G, rhs)

def proj_hull(E, x):
    """exact projection of x (7-list, x[0]=1) onto {E_k . x = 0}; E independent 7-vectors"""
    if not E: return list(x)
    Eg = [[F(t) for t in e[1:]] for e in E]
    lam = gram_solve(Eg, [rv(e, x) for e in E])
    return [x[0]] + [x[m + 1] - sum(lam[k] * Eg[k][m] for k in range(len(E))) for m in range(6)]

def null_proj_vec(E, g):
    """projection of gradient g (6-list) onto null(E-gradients)"""
    if not E: return [F(t) for t in g]
    Eg = [[F(t) for t in e[1:]] for e in E]
    lam = gram_solve(Eg, [sum(Eg[k][m] * g[m] for m in range(6)) for k in range(len(E))])
    return [F(g[m]) - sum(lam[k] * Eg[k][m] for k in range(len(E))) for m in range(6)]

def rowspace_dir(E, k, sgn):
    """direction d (6-list) with E_j.d = sgn*delta_jk"""
    Eg = [[F(t) for t in e[1:]] for e in E]
    lam = gram_solve(Eg, [F(sgn) if j == k else F(0) for j in range(len(E))])
    return [sum(lam[j] * Eg[j][m] for j in range(len(E))) for m in range(6)]

def reduce_key(vec, E):
    """reduce 7-vector modulo the hull equations (eliminate E pivot columns) ; returns normalised integer tuple (or None if zero)"""
    w = [F(t) for t in vec]
    # RREF-ish elimination using E rows in order, each with a pivot among cols 1..6
    basis = []; piv = []
    for e in E:
        u = [F(t) for t in e]
        for b, pc in zip(basis, piv):
            if u[pc] != 0:
                f = u[pc] / b[pc]; u = [ui - f * bi for ui, bi in zip(u, b)]
        pc = next(k for k in range(1, 7) if u[k] != 0)
        basis.append(u); piv.append(pc)
    for b, pc in zip(basis, piv):
        if w[pc] != 0:
            f = w[pc] / b[pc]; w = [wi - f * bi for wi, bi in zip(w, b)]
    if all(t == 0 for t in w): return None
    den = 1
    for t in w: den = den * t.denominator // math.gcd(den, t.denominator)
    iv = [int(t * den) for t in w]; g = math.gcd(*[abs(t) for t in iv])
    return tuple(t // g for t in iv)

def certify_nonpos(keys, e, supp_hint):
    """exact certificate that row e <= 0 on P: find lam>=0 on rows with sum lam_j r_j = -e (7-vectors).  Returns dict j->lam or None."""
    # opposite row
    neg = tuple(-v for v in e)
    if neg in supp_hint: return {neg: F(1)}
    return None

def expand(x, box=None, deadline=None):
    rows, tags, steps, R = cell_of(x, box)
    sig = hsig(tags, steps)
    D = groups_of(rows); keys = list(D.keys())
    out = dict(sig=sig, n_rows=len(rows), n_dist=len(keys), nmoves=len(steps), R=R, tags=tags, D=D)
    An, bn, nn = lp_prep(keys)
    zc, tc = cheb(An, bn)
    E = []; Elab = []                       # hull equations (independent 7-vectors) and labels
    c = None
    if zc is not None and tc > 1e-9:
        for den in (10**6, 10**9, 10**12, 10**15):
            cc = ratz(zc, den)
            if all(rv(k, cc) > 0 for k in keys): c = cc; break
        if c is None:
            out['status'] = 'exactfail'; out['tc'] = tc; return out
    else:
        # lower-dimensional or thin: implicit equalities by float screen, certified exactly as opposite pairs
        kset = set(keys); cand = []
        for k in keys:
            neg = tuple(-v for v in k)
            if neg in kset and k not in cand: cand.append(k)
        if not cand:
            out['status'] = 'nofloatinterior'; out['tc'] = tc; return out
        allE = list(cand)                                      # both members of each opposite pair are rows; keep one per pair
        pairs = []; used = set()
        for k in cand:
            if k in used: continue
            neg = tuple(-v for v in k); used.add(k); used.add(neg); pairs.append(k)
        ii = indep(pairs)
        E = [list(pairs[i]) for i in ii]
        Elab = [(pairs[i], tuple(-v for v in pairs[i])) for i in ii]
        # relative interior: LP with E equalities, others >= t
        nonE = [k for k in keys if k not in used]
        # if every row is in a pair there is nothing else
        A2 = np.array([[float(v) for v in k[1:]] for k in nonE]); b2 = np.array([float(k[0]) for k in nonE])
        n2 = np.linalg.norm(A2, axis=1); n2[n2 == 0] = 1.0; A2 = A2 / n2[:, None]; b2 = b2 / n2
        Ae = np.array([[float(v) for v in e[1:]] for e in E] + [[0.0] * 6]); 
        Aeq = np.hstack([np.array([[float(v) for v in e[1:]] for e in E]), np.zeros((len(E), 1))])
        beq = np.array([-float(e[0]) for e in E])
        cc_ = np.zeros(7); cc_[6] = -1.0
        r = linprog(cc_, A_ub=np.hstack([-A2, np.ones((len(nonE), 1))]), b_ub=b2, A_eq=Aeq, b_eq=beq, bounds=[(1, UB)] * 6 + [(None, 1)], method='highs')
        if r.status != 0 or r.x[6] <= 1e-9:
            out['status'] = 'nofloatinterior'; out['tc'] = tc; return out
        c = None
        for den in (10**6, 10**9, 10**12, 10**15):
            cc = proj_hull(E, ratz(r.x[:6], den))
            if all(rv(e, cc) == 0 for e in E) and all(rv(k, cc) > 0 for k in nonE) and all(rv(k, cc) >= 0 for k in used): c = cc; break
        if c is None:
            out['status'] = 'exactfail'; out['tc'] = r.x[6]; return out
        tc = r.x[6]
    out['status'] = 'ok'; out['center'] = c; out['tc'] = tc; out['codim'] = len(E)
    # float maxima (steering and reporting candidates only), inside the hull
    fmax = {}
    Aeq = np.array([[float(v) for v in e[1:]] for e in E]) if E else None
    beq = np.array([-float(e[0]) for e in E]) if E else None
    for k in range(6):
        cvec = np.zeros(6); cvec[k] = -1.0
        r = linprog(cvec, A_ub=-An, b_ub=bn, A_eq=Aeq, b_eq=beq, bounds=[(1, UB)] * 6, method='highs')
        fmax[k + 2] = (-r.fun if r.status == 0 else None)
    out['fmax'] = fmax
    # groups modulo the hull
    G = {}
    for k in keys:
        rk = reduce_key(k, E) if E else k
        if rk is None: continue
        if all(t == 0 for t in rk[1:]): continue          # constant constraint
        G.setdefault(rk, []).append(k)
    gkeys = list(G.keys())
    Ag, bg, ng = lp_prep(gkeys)
    # LP equalities for the hull (in the normalised z scale: rows kept raw)
    facets = []; thin = 0; nofacet = 0
    for i, rk in enumerate(gkeys):
        others = [j for j in range(len(gkeys)) if j != i]
        cvec = np.zeros(7); cvec[6] = -1.0
        Aub = np.hstack([-Ag[others], np.ones((len(others), 1))]); bub = bg[others]
        Aeq_ = [np.hstack([Ag[i:i+1], np.zeros((1, 1))])]; beq_ = [-bg[i]]
        for e in E:
            Aeq_.append(np.array([[float(v) for v in e[1:]] + [0.0]])); beq_.append(-float(e[0]))
        r = linprog(cvec, A_ub=Aub, b_ub=bub, A_eq=np.vstack(Aeq_), b_eq=np.array(beq_), bounds=[(1, UB)] * 6 + [(None, 1)], method='highs')
        if r.status != 0 or r.x[6] <= 1e-12: nofacet += 1; continue
        t = r.x[6]; z = r.x[:6]
        idx = [ix for k in G[rk] for ix in D[k]]
        if t <= 1e-7:
            thin += 1; facets.append(dict(key=rk, idx=idx, t=t, y=None, why='thin')); continue
        p = None
        # exact point on the facet within the hull
        for den in (10**6, 10**9, 10**12, 10**15):
            q = proj_hull(E + [list(rk)] if (E and indep(E + [list(rk)]) == list(range(len(E) + 1))) else ([list(rk)] if not E else E + [list(rk)]), ratz(z, den))
            if all(rv(e, q) == 0 for e in E) and rv(rk, q) == 0 and all(rv(j, q) > 0 for j in gkeys if j != rk) and q[1] >= 1:
                p = q; break
        if p is None:
            facets.append(dict(key=rk, idx=idx, t=t, y=None, why='exactfail')); continue
        g = [F(u) for u in rk[1:]]
        Pg = null_proj_vec(E, g); n2_ = sum(u * u for u in Pg)
        d = [F(0)] + [-u / n2_ for u in Pg]
        eps = F(1, 2 ** (int(max(1, math.ceil(-math.log2(t)))) + 8))
        y = None
        for tries in range(40):
            yy = [F(1)] + [p[m] + eps * d[m] for m in range(1, 7)]
            if rv(rk, yy) < 0 and all(rv(e, yy) == 0 for e in E) and all(rv(j, yy) > 0 for j in gkeys if j != rk):
                y2 = [F(1)] + [p[m] + (eps / 8) * d[m] for m in range(1, 7)]
                a1 = sorted(yy); a2 = sorted(y2)
                a1 = [v / a1[0] for v in a1]; a2 = [v / a2[0] for v in a2]
                if sig_of(a1, box)[0] == sig_of(a2, box)[0]:
                    y = a1; break
            eps = eps / 4
        if y is None:
            facets.append(dict(key=rk, idx=idx, t=t, y=None, why='unstable')); continue
        facets.append(dict(key=rk, idx=idx, t=t, y=y, why='ok', p=p, eps=eps, kind='rel'))
    # off-hull crossings (single implicit equality, both signs) for lower-dimensional cells
    hullcross = []
    for kk in range(len(E)):
        for sgn in (1, -1):
            d = rowspace_dir(E, kk, sgn)
            eps = F(1, 2 ** 20); y = None
            for tries in range(40):
                yy = [F(1)] + [c[m + 1] + eps * d[m] for m in range(6)]
                if all(rv(j, yy) > 0 for j in gkeys) and all(rv(E[j], yy) == (eps * sgn if j == kk else 0) for j in range(len(E))):
                    y2 = [F(1)] + [c[m + 1] + (eps / 8) * d[m] for m in range(6)]
                    a1 = sorted(yy); a2 = sorted(y2); a1 = [v / a1[0] for v in a1]; a2 = [v / a2[0] for v in a2]
                    if sig_of(a1, box)[0] == sig_of(a2, box)[0]: y = a1; break
                eps = eps / 4
            hullcross.append(dict(eq=Elab[kk], sgn=sgn, y=y))
    out['facets'] = facets; out['thin'] = thin; out['nofacet'] = nofacet; out['hullcross'] = hullcross
    return out

def kind_of(tag):
    return tag[0] if tag[0] in ('exit', 'clear-low', 'clear-high', 'setter', 'order', 'box') else 'entry'

def row_class(tags, idx):
    ks = sorted(set(kind_of(tags[i]) for i in idx))
    return '+'.join(ks)

def eq_string(k):
    nz = [(m + 1, v) for m, v in enumerate(k) if v != 0 and m > 0]
    a0 = k[0]
    s = ' + '.join('%d*rho%d' % (v, m) for m, v in nz)
    return ('%d*rho1 + ' % a0 if a0 else '') + s + ' >= 0'

def describe(tags, idx):
    # meaning of the first row of the group, in the framework's words
    return row_meaning(tags[idx[0]])
