"""E169 (v2): generate the Lean proof of the band theorem from the certified wall-cut tree band_cover_tree_v3.json.gz (E124).
Every node's region is carried as hypotheses in their original form (root rows as linear inequalities in x_c = s_{c+1}-1,
cut walls as the case split states them: W or not W).  Split node: flat chain `by_cases r_{n+l} : W_l; case neg => child l`
then the cell rule (cone_band) with every wall proved by `linarith only` from its certificate's rows plus nonnegativity.
'in' leaf: the cell rule.  'empty' leaf: `exfalso; linarith only [...]`.  Subtrees are packed into lemmas of at most LIM
nodes; a lemma restates only its root's region.  Usage: gen_band_lean_v1.py OUTDIR [SUBTREE_KEY] [LIM]."""
import gzip, json, sys, os
from fractions import Fraction as F
tree = json.load(gzip.open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'band_cover_tree_v3.json.gz')))
OUT = sys.argv[1]; SUB = ''; LIM = int(sys.argv[2]) if len(sys.argv) > 2 else 60
PAIRS = [(i, j) for i in range(7) for j in range(7) if i != j]
XS = "x0 x1 x2 x3 x4 x5"; HX = "hx0 hx1 hx2 hx3 hx4 hx5"
def S(c): return "1" if c == 0 else "(1 + x%d)" % (c - 1)
def fr(q):
    q = F(q); return ("(%d : ℝ)" % q.numerator) if q.denominator == 1 else "((%d : ℝ) / %d)" % (q.numerator, q.denominator)
def xrow(a, b, strict):
    terms = [("%s * x%d" % (fr(v), c)) for c, v in enumerate(a) if v != 0]
    return "%s %s %s" % (" + ".join(terms) if terms else "(0 : ℝ)", "<" if strict else "≤", fr(b))
def wall_s(k, i, j): return "(%d : ℝ) * %s ≤ %d * %s" % (8 * k[i] + 1, S(j), 8 * k[j] + 7, S(i))
ROOT = [([1 if c == i else (-1 if c == i + 1 else 0) for c in range(6)], 0, False) for i in range(5)]
ROOT += [([0, 0, 0, 0, 0, 1], 8, False), ([0, 0, 0, 0, 0, -1], -6, False)]
ROOT_ROWS = [xrow(a, b, st) for a, b, st in ROOT]
def children(key, rec): return [(key + ',' if key else '') + str(m) for m in range(len(rec.get('cut', []))) if rec['kind'] == 'split']
size = {}
def sz(key):
    if key in size: return size[key]
    rec = tree[key]; n = 1 + sum(sz(c) for c in children(key, rec)); size[key] = n; return n
sys.setrecursionlimit(100000)
sz(SUB)
# choose lemma roots: greedy inline under LIM
lemma_roots = set([SUB])
def pack(key, budget):
    """returns nodes consumed inline; marks children that must be separate lemmas"""
    used = 1
    for c in children(key, tree[key]):
        if sz(c) <= LIM - used - 0 and used + sz(c) <= LIM: used += pack(c, LIM)
        else: lemma_roots.add(c); pack(c, LIM)
    return used
pack(SUB, LIM)
def lname(key): return "bc_" + ("root" if key == '' else key.replace(',', '_'))
def names(n): return " ".join("r%d" % t for t in range(n))
def cert_names(cert): return [int(t) for t in cert.keys()]
def wall_proof(ids): return "(by push_cast; linarith only [%s])" % ", ".join(["r%d" % t for t in ids] + HX.split())
def node_proof(key, rows, ind):
    """rows: list of Lean statements (index = row id); returns proof lines at indentation ind"""
    rec = tree[key]; pad = " " * ind; n = len(rows); L = []
    if key != SUB and key in lemma_roots and ind > 0:
        L.append(pad + "exact %s %s %s %s" % (lname(key), XS, HX, names(n))); return L
    if rec['kind'] == 'empty':
        ids = [t for t in cert_names(dict(rec['cert'][1])) if t < n]
        L.append(pad + "exfalso; linarith only [%s]" % ", ".join(["r%d" % t for t in ids] + HX.split())); return L
    k = rec['k']; cut = [tuple(c) for c in rec['cut']]
    for l, (i, j) in enumerate(cut):
        L.append(pad + "by_cases r%d : %s" % (n + l, wall_s(k, i, j)))
        L.append(pad + "case neg =>")
        L += node_proof((key + ',' if key else '') + str(l), rows + [wall_s(k, a, b) for a, b in cut[:l]] + ["¬ (" + wall_s(k, i, j) + ")"], ind + 2)
    args = []
    for (i, j) in PAIRS:
        if (i, j) in cut: args.append("(by push_cast; linarith only [r%d])" % (n + cut.index((i, j))))
        else: args.append(wall_proof(cert_names(rec['certs']['%d,%d' % (i, j)])))
    L.append(pad + "exact cone_band %s %s %s %s" % (XS, HX, " ".join(str(v) for v in k), " ".join(args)))
    return L
# region rows for every lemma root (rebuilt along paths)
region = {'': ROOT_ROWS}
order = []
def walk(key, rows):
    region[key] = rows; rec = tree[key]
    if rec['kind'] == 'split':
        k = rec['k']; cut = [tuple(c) for c in rec['cut']]
        for l, (i, j) in enumerate(cut):
            walk((key + ',' if key else '') + str(l), rows + [wall_s(k, a, b) for a, b in cut[:l]] + ["¬ (" + wall_s(k, i, j) + ")"])
    if key in lemma_roots: order.append(key)      # post-order: children first
# rebuild rows down to SUB
rows = ROOT_ROWS; path = SUB.split(',') if SUB else []
cur = ''
for step in path:
    rec = tree[cur]; k = rec['k']; cut = [tuple(c) for c in rec['cut']]; l = int(step)
    rows = rows + [wall_s(k, a, b) for a, b in cut[:l]] + ["¬ (" + wall_s(k, *cut[l]) + ")"]
    cur = (cur + ',' if cur else '') + step
walk(SUB, rows)
CONCL = "∃ t : ℝ, 0 < t ∧ ∀ i, (8 : ℝ)⁻¹ ≤ circDist (bandS x0 x1 x2 x3 x4 x5 i * t)"
def lemma(key):
    rows = region[key]
    hyps = "\n".join("    (r%d : %s)" % (t, s) for t, s in enumerate(rows))
    body = node_proof(key, rows, 2) if key == SUB else None
    # proof of this lemma: same generator but treat this key as the start
    global_sub = key
    lines = node_proof_start(key, rows)
    return ("theorem %s (x0 x1 x2 x3 x4 x5 : ℝ) (hx0 : 0 ≤ x0) (hx1 : 0 ≤ x1) (hx2 : 0 ≤ x2) (hx3 : 0 ≤ x3)\n"
            "    (hx4 : 0 ≤ x4) (hx5 : 0 ≤ x5)\n%s :\n    %s := by\n%s\n" % (lname(key), hyps, CONCL, "\n".join(lines)))
def node_proof_start(key, rows):
    rec = tree[key]; n = len(rows); L = []; pad = "  "
    if rec['kind'] == 'empty':
        ids = [t for t in cert_names(dict(rec['cert'][1])) if t < n]
        return [pad + "exfalso; linarith only [%s]" % ", ".join(["r%d" % t for t in ids] + HX.split())]
    k = rec['k']; cut = [tuple(c) for c in rec['cut']]
    for l, (i, j) in enumerate(cut):
        L.append(pad + "by_cases r%d : %s" % (n + l, wall_s(k, i, j)))
        L.append(pad + "case neg =>")
        L += node_proof((key + ',' if key else '') + str(l), rows + [wall_s(k, a, b) for a, b in cut[:l]] + ["¬ (" + wall_s(k, i, j) + ")"], 4)
    args = []
    for (i, j) in PAIRS:
        if (i, j) in cut: args.append("(by push_cast; linarith only [r%d])" % (n + cut.index((i, j))))
        else: args.append(wall_proof(cert_names(rec['certs']['%d,%d' % (i, j)])))
    L.append(pad + "exact cone_band %s %s %s %s" % (XS, HX, " ".join(str(v) for v in k), " ".join(args)))
    return L

exec(open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'gen_band_lean_v2_driver.py')).read())
