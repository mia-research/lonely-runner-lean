"""modgap_open_v1 (2026-10-06): the real exception candidates.  Population: every stored residual member (all 22 fields, full_residual): residual_members_C_list_v1.json (C),
both_shadowed_members_v1.json (BS), divisible_members_v2.json A and B (DA, DB), and members_5978_v1.json minus those lists (T1).  Each member is classed with the record's own
functions (lean_case_reach_v3): 'Lean' (settled by the residue cases with M(2,2)), 'grid' (the grid corollary), 'M13' (needs M(1,3)), 'open'.
Exact structure along the cascade path (Fractions; no float): at each state t_i, B_i = readings in the way; per jump the laps traversed by each reading floor(d (t_{i+1} - t_i)) and
the unrounded d (t_{i+1} - t_i); simultaneous openers at t* and closers at t_R (readings at exactly 1/8 and 7/8); re-blocks (a reading in the way at two different states);
setters P; the derivation check cascade(P + {d_min}) = t*.  Reported per class: counts, maxima, and the individual extreme members (top 8 by each measure).
No claim is made beyond the counts."""
import sys, json, math, collections, itertools
sys.path.insert(0, '.')
from fractions import Fraction as F
from members_reach_check_v1 import load, full_residual, cascade as casc, cd
from lean_case_reach_v2 import settled, typ
from lean_case_reach_v3 import grid
sys.path.insert(0, '.')
from modgap_lib_v1 import cascade_path, openers, component, E8
def cls(S):
    mult = [d for d in S if d % 8 == 0]; rs = tuple(sorted(d % 8 for d in S if d % 8))
    if settled(len(mult), rs, '22'): return 'Lean'
    if grid(S): return 'grid'
    if settled(len(mult), rs, 'both'): return 'M13'
    return 'open'
C = [S for S in dict.fromkeys(load('../residual_members_C_list_v1.json')) if full_residual(S)]
BS = [S for S in dict.fromkeys(load('both_shadowed_members_v1.json')) if full_residual(S)]
st = json.load(open('divisible_members_v2.json'))
DA = list(dict.fromkeys(tuple(sorted(S)) for S in st['A'])); DB = list(dict.fromkeys(tuple(sorted(S)) for S in st['B']))
known = set(C) | set(BS) | set(DA) | set(DB)
T1 = [S for S in dict.fromkeys(tuple(sorted(x[2])) for x in json.load(open('members_5978_v1.json'))) if S not in known and full_residual(S)]
out = open('modgap_open_v1.out', 'w'); out.write(__doc__ + "\n")
rows = []
for name, sets in (('C', C), ('BS', BS), ('DA', DA), ('DB', DB), ('T1', T1)):
    for S in sets:
        path = cascade_path(S); ts = [p for p, _ in path]; t = ts[-1]
        P = {d for _, d in path if d}
        op = openers(S, t); tR, cl = component(S, t)
        maxwrap = 0; maxd = F(0); maxB = 0; reb = 0; seen = {}
        for i, ti in enumerate(ts):
            B = [d for d in S if cd(d * ti) < E8]
            maxB = max(maxB, len(B))
            for d in B:
                if d in seen and seen[d] != i: reb += 1
                seen[d] = i
            if i + 1 < len(ts):
                dt = ts[i + 1] - ti
                for d in S:
                    maxwrap = max(maxwrap, math.floor(d * dt)); maxd = max(maxd, d * dt)
        chk = casc(sorted(P | {S[0]})) == t
        rows.append(dict(src=name, cls=cls(S), S=S, nmoves=len(ts) - 1, nset=len(P), nop=len(op), ncl=len(cl), maxB=maxB, reb=reb, maxwrap=maxwrap, maxd=maxd, chk=chk, lenS=len(str(S[-1]))))
by = collections.defaultdict(list)
for r in rows: by[r['cls']].append(r)
out.write("members: %d (C %d, BS %d, DA %d, DB %d, T1 %d)\n" % (len(rows), len(C), len(BS), len(DA), len(DB), len(T1)))
out.write("derivation check cascade(P + {d_min}) = t*: [T %d/%d]\n" % (sum(r['chk'] for r in rows), len(rows)))
for k in ('Lean', 'grid', 'M13', 'open'):
    R = by[k]
    if not R: out.write("\nclass %s: 0\n" % k); continue
    out.write("\nclass %s: %d members\n" % (k, len(R)))
    for f in ('nmoves', 'nset', 'nop', 'ncl', 'maxB', 'reb', 'maxwrap'):
        out.write("  %-8s distribution: %s\n" % (f, dict(sorted(collections.Counter(r[f] for r in R).items()))))
    out.write("  max of d*(t_{i+1}-t_i) over jumps (exact, display decimal): %s ~ %.6f\n" % (max(r['maxd'] for r in R), float(max(r['maxd'] for r in R))))
    if k == 'open':
        for f in ('nop', 'ncl', 'reb', 'maxwrap', 'maxB'):
            out.write("  extremes by %s (top 8): %s\n" % (f, [(r['src'], r['S'] if r['lenS'] < 14 else '[%d-digit readings] %s...' % (r['lenS'], str(r['S'][0])[:12]), r[f]) for r in sorted(R, key=lambda r: -r[f])[:8]]))
out.close(); print(open('modgap_open_v1.out').read()[len(__doc__):][:7000])
