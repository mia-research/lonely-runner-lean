"""E239 (2026-10-01): positive control for the f = 3 record "the winning flank's index is 0" (hole_g_flank_v1.out).

first_exit_three_v1.out: the compact triple T = (8, 15, 29) has the start s0 = 57/232 at which no first exit is clear.
A block lam*T has the same positions at tau_C as T has at lam*tau_C, so lam = (s0 + n)/tau_C puts the hole's entry
instant on that start.  Cores are taken from the E233 population (gen(232, 2000)) in order until one gives a block with
x1 = 8*lam in the strip [9m, 35m/3) and no proved rule covering the set (holef_cascade_v1.covered).  The set is scaled by lam's denominator to whole
numbers (the scale symmetry; positions at every instant are unchanged).  Then: the block's
relay from tau_C, its winning flank and index j (hole_g_flank_v1.study), and where the full set lands (the cascade).
"""
import sys
from fractions import Fraction as F
sys.path.insert(0, '../band_cert_v1')
from e151_block_v1 import trace
import hole3_cascade_v1 as H3, holef_cascade_v1 as HF
import hole_g_flank_v1 as G

T = (8, 15, 29); s0 = F(57, 232)
out = open('hole_g_three_control_v1.out', 'w'); out.write(__doc__ + "\n"); w = lambda s: (out.write(s + "\n"), out.flush())
found = 0
for core, _ in H3.gen(232, 2000):
    m = max(core); tc, _ = trace(core)
    for n in range(0, 4):
        lam = (s0 + n) / tc
        D = lam.denominator
        block = tuple(int(lam * x * D) for x in T); core_i = tuple(c * D for c in core)
        if not (9 * m * D <= block[0] < F(35, 3) * m * D):
            continue
        core = core_i
        if HF.covered(sorted(list(core) + list(block))):
            continue
        r = G.study((3, core, block, 'tau_C'))
        b = HF.study((core, block))
        w("core %s  block %s  (scaled by %d; lam = %s)" % (core, block, D, lam))
        w("   checks %s; block clear at tau_C: %s; winner rank %s index j %s; relay setters (rank, j) %s" % (
            dict(r['chk']) or 'G1-G3 0 failures', r['clear0'], r.get('rank'), r.get('j'), r.get('setters')))
        w("   full set: checks %s; lands in %s; pattern of moves after tau_C: %s" % (
            dict(b['chk']) or 'C1, F1, F2 0 failures', b['k_land'], [(x[1], x[2]) for x in b['rows'] if x[0] >= 0]))
        found += 1
        break
    if found >= 5:
        break
w("constructed: %d" % found)
out.close()
print(open('hole_g_three_control_v1.out').read()[len(__doc__):])
