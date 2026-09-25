"""Order 8: every cascade climb from R = 1 into (7, 9), followed exactly, as cells of reading space -- v2.

Same mathematics as climb_cells_v1 (read its docstring): readings 1 = s_1 <= s_2 <= ... <= s_7 = S <= B, S >= Slo;
coarse labels per runner per step (clear in gap M, or in the subject's slot at lap M); the latest-opening setter;
every condition a linear inequality in (s_2..s_7); strict ones carry the margin tau; a cell is realisable iff
max tau > 0.  Exact rational arithmetic (gmpy2.mpq), no floating point in any decision.

What v2 changes (organisation only; the search tree is identical to v1's):
 * Witness shortcut.  A child cell only ADDS rows to its parent.  Each state carries a witness point x with
   tau(x) > 0; if x satisfies the added rows, the child is realisable and no LP is solved.  Otherwise the LP is
   solved, warm-started from the parent's final dual basis (still dual-feasible: rows are only appended).
 * Work units.  The main process expands the tree to the states after the FIRST MOVE; each is one task, fed to a
   shared queue (imap_unordered), so every core stays busy.
 * Checkpoints.  Each finished task is appended to <tag>.jsonl (counts + its terminal cells); a restart skips
   finished task ids.  Progress to <tag>.progress after every task.
 * Early positive.  Any climb into (7, 9) is appended to <tag>.TERMINALS.txt the moment it is found.
Run it under caffeinate:  caffeinate -i python3 climb_cells_v2.py B Slo
"""
import sys, os, time, json, hashlib
from gmpy2 import mpq
from multiprocessing import Pool
from collections import Counter
from climb_cells_v1 import (NV, TAU, Z, ONE, solve7, base_rows, le, reading_rows, order, from_order)

# ------------------------------------------------------------------ exact LP with warm start
def lp_max(rows, c, basis):
    """max c.x s.t. a.x <= b (rows), via the dual (min b.y, A^T y = c, y >= 0), primal simplex, Bland.
    basis: 7 row indices that are dual feasible for c.  Returns (value, x, basis) or None if infeasible."""
    basis = list(basis)
    while True:
        AB = [rows[i][0] for i in basis]
        ABt = [[AB[j][i] for j in range(NV)] for i in range(NV)]
        yB = solve7(ABt, c)
        x = solve7(AB, [rows[i][1] for i in basis])
        if yB is None or x is None: raise RuntimeError('singular basis')
        if any(v < 0 for v in yB): raise RuntimeError('basis not dual feasible')
        bset = set(basis); enter = -1
        for j, (a, b) in enumerate(rows):
            if j in bset: continue
            if b - sum(ai * xi for ai, xi in zip(a, x)) < 0: enter = j; break
        if enter < 0:
            return sum(ci * xi for ci, xi in zip(c, x)), x, basis
        d = solve7(ABt, rows[enter][0])
        leave = -1; best = None
        for i in range(NV):
            if d[i] > 0:
                r = yB[i] / d[i]
                if best is None or r < best or (r == best and basis[i] < basis[leave]):
                    best = r; leave = i
        if leave < 0: return None
        basis[leave] = enter

CT = [Z] * NV; CT[TAU] = ONE                    # objective: max tau
def cold_basis(c):
    return [i if c[i] >= 0 else 6 + i for i in range(6)] + [12 if c[TAU] >= 0 else 13]

def sat(x, new_rows):
    return all(sum(ai * xi for ai, xi in zip(a, x)) <= b for a, b in new_rows)

class Search:
    def __init__(self, B, Slo, sink=None):
        self.B = mpq(B); self.rows0 = base_rows(B)
        a = [Z] * NV; a[5] = -ONE; self.rows0.append((a, -mpq(Slo)))
        self.maxo = 2 * ((7 * int(B) + 1) // 8) + 2
        self.nlp = 0; self.nskip = 0; self.cells = 0; self.early = 0; self.terms = []
        self.sink = sink

    def feasible(self, rows, nparent, wit):
        """wit = (x, basis) valid for rows[:nparent].  Returns new wit if max tau > 0 on rows, else None."""
        x, basis = wit
        if x is not None and x[TAU] > 0 and sat(x, rows[nparent:]):
            self.nskip += 1; return wit
        self.nlp += 1
        r = lp_max(rows, CT, basis)
        if r is None or r[0] <= 0: return None
        return (r[1], r[2])

    def srange(self, rows):
        closed = [(a, b) if i in (12, 13) else (a[:TAU] + [Z], b) for i, (a, b) in enumerate(rows)]
        c = [Z] * NV; c[5] = ONE
        hi = lp_max(closed, c, cold_basis(c)); c[5] = -ONE
        lo = lp_max(closed, c, cold_basis(c))
        return (-lo[0] if lo else None), (hi[0] if hi else None)

    def labels(self, rows, wit, N, p, prev, k_list, i, cur, out):
        if i == len(k_list):
            out.append((dict(cur), rows, wit)); return
        k = k_list[i]; o = order(prev[k]); seen = False
        while o <= self.maxo:
            lab = from_order(o)
            r2 = rows + reading_rows(k, N, p, lab)
            w2 = self.feasible(r2, len(rows), wit)
            if w2 is not None:
                seen = True; cur[k] = lab
                self.labels(r2, w2, N, p, prev, k_list, i + 1, cur, out)
                del cur[k]
            elif seen:
                break
            o += 1

    def children(self, st):
        """one cascade step from state st; returns child states (and records terminals / early events)."""
        rows, wit, N, p, lab, word = st
        self.cells += 1
        W = [k for k in range(2, 8) if lab[k][0] == 'way']
        if not W:
            self.early += 1; return []
        kids = []
        for q in W:
            Mq = lab[q][1]
            r2 = list(rows)
            for k in W:
                if k != q:
                    r2.append(le({k: -mpq(8 * Mq + 1), q: mpq(8 * lab[k][1] + 1)}))
            rx = r2 + [le({q: mpq(7)}, mpq(8 * Mq + 1), strict=True)]
            wx = self.feasible(rx, len(rows), wit)
            if wx is not None:
                lo, hi = self.srange(rx)
                t = (word + [(q, Mq)], lo, hi)
                self.terms.append(t)
                if self.sink:
                    with open(self.sink, 'a') as f:
                        f.write(f"{t[0]}\t{t[1]}\t{t[2]}\n"); f.flush()
            rs = r2 + [le({q: -mpq(7)}, -mpq(8 * Mq + 1))]
            ws = self.feasible(rs, len(rows), wit)
            if ws is None: continue
            Nn = mpq(8 * Mq + 1)
            prev = {}
            for k in range(2, 8):
                if k == q: continue
                prev[k] = ('gap', lab[k][1]) if k in W else lab[k]
            others = [k for k in range(2, 8) if k != q]
            outs = []
            self.labels(rs, ws, Nn, q, prev, others, 0, {}, outs)
            for newlab, rr, ww in outs:
                newlab[q] = ('gap', Mq)
                kids.append((rr, ww, Nn, q, newlab, word + [(q, Mq)]))
        return kids

    def roots(self):
        """the cells at R = 1 (every label assignment), each with its witness."""
        rows = self.rows0
        w = self.feasible(rows, 0, (None, cold_basis(CT)))
        if w is None: return []
        prev = {k: ('gap', 0) for k in range(2, 8)}
        outs = []
        self.labels(rows, w, ONE, 1, prev, [7, 6, 5, 4, 3, 2], 0, {}, outs)
        return [(rr, ww, ONE, 1, lab, []) for lab, rr, ww in outs]

    def dfs(self, st):
        stack = [st]
        while stack:
            stack.extend(self.children(stack.pop()))

def task_id(st):
    # the FULL cell: every constraint row, plus the state.  (v2's first id hashed only word + labels, so two cells
    # with different histories could share an id and the bookkeeping dropped one: found by the v1/v2 regression.)
    rows, wit, N, p, lab, word = st
    key = repr(([(list(map(str, a)), str(b)) for a, b in rows], str(N), p, sorted(lab.items()), word))
    return hashlib.sha256(key.encode()).hexdigest()[:24]

def work(args):
    st, B, Slo, sink = args
    S = Search(B, Slo, sink)
    S.dfs(st)
    return task_id(st), S.nlp, S.nskip, S.cells, S.early, [(str(w), str(lo), str(hi)) for w, lo, hi in S.terms]

if __name__ == '__main__':
    B = int(sys.argv[1]); Slo = mpq(sys.argv[2])
    tag = f"climb_cells_v2_B{B}_S{str(Slo).replace('/', '_')}"
    t0 = time.time()
    M = Search(B, Slo, tag + '.TERMINALS.txt')
    roots = M.roots()
    tasks = []
    for r in roots:
        tasks.extend(M.children(r))          # expand to the states after the first move (records any terminal)
    main_cells, main_early, main_terms = M.cells, M.early, list(M.terms)
    done = {}
    if os.path.exists(tag + '.jsonl'):
        for line in open(tag + '.jsonl'):
            d = json.loads(line); done[d['id']] = d
    ids = [task_id(st) for st in tasks]
    if len(set(ids)) != len(ids): raise RuntimeError('task id collision')
    todo = [st for st in tasks if task_id(st) not in done]
    print(f"{tag}: {len(roots)} root cells, {len(tasks)} tasks after the first move ({len(done)} already done), "
          f"setup {time.time() - t0:.0f}s", flush=True)
    with Pool() as pool, open(tag + '.jsonl', 'a') as ck:
        for n, (tid, nlp, nskip, cells, early, terms) in enumerate(
                pool.imap_unordered(work, [(st, B, Slo, tag + '.TERMINALS.txt') for st in todo]), 1):
            d = {'id': tid, 'nlp': nlp, 'nskip': nskip, 'cells': cells, 'early': early, 'terms': terms}
            ck.write(json.dumps(d) + '\n'); ck.flush(); done[tid] = d
            tot_cells = main_cells + sum(v['cells'] for v in done.values())
            tot_terms = len(main_terms) + sum(len(v['terms']) for v in done.values())
            with open(tag + '.progress', 'w') as pf:
                pf.write(f"{len(done)}/{len(tasks)} tasks; cells {tot_cells}; terminal cells {tot_terms}; "
                         f"elapsed {time.time() - t0:.0f}s\n")
    # summary (same fields as v1)
    terms = [(str(w), str(lo), str(hi)) for w, lo, hi in main_terms] + [tuple(t) for v in done.values() for t in v['terms']]
    nlp = M.nlp + sum(v['nlp'] for v in done.values()); nskip = M.nskip + sum(v['nskip'] for v in done.values())
    cells = main_cells + sum(v['cells'] for v in done.values()); early = main_early + sum(v['early'] for v in done.values())
    print(f"climb cells v2: readings in [1, {B}], S >= {Slo}; exact; {time.time() - t0:.0f}s")
    print(f"  LPs solved {nlp}; LPs skipped by the witness {nskip}; cells explored {cells}; early events {early}")
    print(f"  climbs exiting into (7, 9) (terminal cells): {len(terms)}")
    if terms:
        lo = min(mpq(t[1]) for t in terms); hi = max(mpq(t[2]) for t in terms)
        print(f"  far reading S over every terminal cell: [{lo}, {hi}]")
        words = Counter(t[0] for t in terms)
        print(f"  distinct setter words among terminal cells: {len(words)}")
        with open(tag + '_words.txt', 'w') as f:
            for w, l, h in terms: f.write(f"{w}\tNA\t{l}\t{h}\n")
