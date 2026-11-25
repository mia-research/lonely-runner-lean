#!/usr/bin/env python3
"""m4_wide_triangle_v2 -- v1 reading both profile outputs (v1, and v2 for (1,4,5,6,6,8,15)), and taking, among the
eight most frequent window ends, every 3-cycle of readings (each reading in two of the three), reported in order of
total frequency (v1 took the top three, which for (1,4,5,6,6,8,15) are not a cycle).  Otherwise as v1: E925 item 5(iii), the wide BUDGET trees.  From m4_wide_tree_profile_v1.out, per box:
the three window-end pairs most frequent among the sampled non-leaf cells at the last level, each giving the
hyperplane (8j+1) g_k = (8j'+7) g_i on which that window closes (window open iff g_k/g_i <= (8j'+7)/(8j+1) for
lower reading i, upper reading k, read in the direction R in [(8j+1)/g_i, (8j'+7)/g_k]).  Exact:
  - the readings the three involve, and whether they form a cycle (each reading in two of them);
  - the cycle product P of the three closing ratios taken round the cycle (P = 1 iff the three hyperplanes share a
    positive point, a common closing point); delta = P - 1;
  - the readings the three do not involve, m of them; the predicted growth of the non-leaf count per round of six
    cuts while the cells are wider than the triangle: 2^m;
  - the observed growth over the last two complete rounds of the profile."""
import json
from fractions import Fraction as F
rows = [json.loads(l) for l in open('m4_wide_tree_profile_v1.out')] + [json.loads(l) for l in open('m4_wide_tree_profile_v2.out')]
for st in [r for r in rows if r.get('status') == 'STOPPED']:
    n = st['n']; lv = {r['level']: r['nonleaf'] for r in rows if r.get('n') == n and 'level' in r}
    import itertools
    tal = sorted(st.get('window_ends_in_sample', {}).items(), key=lambda kv: -kv[1])[:8]
    cyc = []
    for tri in itertools.combinations(tal, 3):
        ed = [eval(k) for k, _ in tri]
        vs = [x for (i, _), (k, _) in ed for x in (i, k)]
        if len(set(vs)) == 3 and all(vs.count(x) == 2 for x in set(vs)) and all(i != k for (i, _), (k, _) in ed):
            cyc.append((sum(v for _, v in tri), ed, [v for _, v in tri]))
    cyc.sort(key=lambda c: -c[0])
    counts = cyc[0][2] if cyc else None
    others = [[str(e) for e in c[1]] + [c[0]] for c in cyc[1:]]
    top = cyc[0][1] if cyc else [eval(k) for k, _ in tal[:3]]
    rat = []
    for (i, el), (k, eh) in top:
        rat.append((i, k, F(eh, el)))          # window open iff g_k / g_i <= eh/el
    inv = sorted({x for i, k, _ in rat for x in (i, k)})
    deg = {x: sum(x in (i, k) for i, k, _ in rat) for x in inv}
    cycle = len(inv) == 3 and all(v == 2 for v in deg.values())
    P = None
    if cycle:
        # orient round the cycle a -> b -> c -> a; ratio g_k/g_i for edge i->k, inverse if traversed backwards
        a = rat[0][0]; cur = a; used = set(); P = F(1)
        for _ in range(3):
            for idx, (i, k, q) in enumerate(rat):
                if idx in used: continue
                if i == cur: P *= q; cur = k; used.add(idx); break
                if k == cur: P /= q; cur = i; used.add(idx); break
    free = [x for x in range(1, 7) if x not in inv]
    full = sorted(l for l in lv if l % 6 == 0)
    obs = [(full[j], full[j + 1], round(lv[full[j + 1]] / lv[full[j]], 2)) for j in range(len(full) - 1)][-3:]
    print(json.dumps({"n": n, "status": st['status'], "last_level": st.get('at_level', st.get('depth')),
                      "top3 window ends (lower reading,edge),(upper reading,edge)": [str(t) for t in top],
                      "closing ratios g_k/g_i": [[i, k, str(q)] for i, k, q in rat],
                      "sample counts of the three": counts, "other 3-cycles in the top eight": others, "readings involved": inv, "cycle": cycle,
                      "cycle product P": None if P is None else str(P), "delta = |P-1|": None if P is None else str(abs(P - 1)),
                      "common closing point": None if P is None else (P == 1),
                      "readings not involved (cut anyway)": free, "predicted factor per round 2^m": 2 ** len(free),
                      "observed factor per round (from, to, ratio)": obs}))
