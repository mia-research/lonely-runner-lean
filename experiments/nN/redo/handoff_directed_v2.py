"""Follow-up to handoff_directed_v1.  (i) In every handoff, is t_pred the START of a later core cell (the
event waits for the core to reopen) or interior (the train opened first)?  (ii) The case the Lean lemma
lonely_at_period does NOT cover: a core blocked at every period point k/g (g divides every core reading).
Does t_pred still exist, where, and does the cascade still meet it within 1/N?  Exact."""
from fractions import Fraction as F
from collections import Counter
from handoff_directed_v1 import run, core_cells, t_pred
from arrangement_lib import nd
tab = Counter()
for b in (61, 63, 65, 67, 68, 69):
    for d in (12, 14, 16, 18, 20):
        for f in (4, 5):
            for N in (10**4, 10**5, 10**6):
                r = run(10, b, d, f, N)
                cells = core_cells([10, b], r['tC'], r['tC'] + 1)
                starts = {u for u, v in cells}
                kind = 'at t_C' if r['tp'] == r['tC'] else ('start of a later core cell' if r['tp'] in starts else 'interior of a core cell')
                tab[(('handoff' if r['idx'] else 'first cell'), kind)] += 1
for k, v in sorted(tab.items()): print(f"  {k}: {v}")
print("\n(ii) core blocked at every period point k/g:")
for a, b, d, f in [(32, 208, 16, 5), (16, 96, 16, 5), (48, 320, 16, 4), (32, 224, 16, 4), (24, 162, 6, 5)]:
    g = d
    blocked = all(any(nd(c * F(k, g)) < F(1, 8) for c in (a, b)) for k in range(1, g + 1))
    for N in (10**4, 10**5, 10**6):
        r = run(a, b, d, f, N)
        print(f"  core ({a},{b}) train step {d} x{f} N={N}: core blocked at all k/g: {blocked}; t_C {r['tC']}; "
              f"t_pred {r['tp']}; event {float(r['t']):.7f} (core cell #{r['idx']}); (t-t_pred)N {float(r['off']):.3f}")
