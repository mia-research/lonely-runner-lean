# E643: per-core certificates for Fresh.ScaledCoreChain.real_all.  For a core (whole numbers) emit L, the chain of pieces covering [3/8, y0], the small window, the large window and y0 = 1/(4 w).
import sys, math
from fractions import Fraction as F
from classes_lib_v1 import clear_iv, meet
def cert(core):
    g = 0
    for d in core: g = math.gcd(g, d)
    T = F(1, g)
    J = clear_iv(F(core[0]), T)
    for s in core[1:]: J = meet(J, clear_iv(F(s), T))
    J = [(lo, hi) for lo, hi in J if hi >= lo and lo > 0]
    jw = max(J, key=lambda w: w[1] - w[0]); w = jw[1] - jw[0]; y0 = 1 / (4 * w)
    cand = []
    for lo, hi in J:
        for n in range(0, 80):
            d = F(n) * T
            if hi + d == 0: continue
            k = 0
            while F(8 * k + 1, 8) / (hi + d) <= y0 * 2:
                a = F(8 * k + 1, 8) / (hi + d); b = F(8 * k + 7, 8) / (lo + d)
                cand.append((a, b, lo, hi, d, k)); k += 1
    cur = F(3, 8); chain = []
    while True:
        opts = [c for c in cand if c[0] <= cur and c[1] > cur]
        if not opts: return None
        c = max(opts, key=lambda c: c[1]); chain.append(c); cur = c[1]
        if cur >= y0: break
    small = min(J)  # lowest window; lo <= T
    return dict(core=core, T=T, y0=y0, chain=chain, small=small, large=jw)
def q(x): x = F(x); return '(%d / %d : ℚ)' % (x.numerator, x.denominator) if x.denominator != 1 else '(%d : ℚ)' % x.numerator
def lean(core, c):
    nm = '_'.join(map(str, core))
    L = '[' + ', '.join(map(str, core)) + ']'
    ps = ', '.join('⟨%s, %s, %s, %s, %s, %d⟩' % (q(a), q(b), q(lo), q(hi), q(d), k) for a, b, lo, hi, d, k in c['chain'])
    s0 = c['small']; l0 = c['large']
    return ('theorem real_core_%s {y : ℝ} (hy : 0 < y) :\n    ∃ t : ℝ, 0 < t ∧ (∀ s ∈ coreSet %s, (1 / 8 : ℝ) ≤ distInt (s * t)) ∧ (1 / 8 : ℝ) ≤ distInt (y * t) :=\n'
            '  real_all (L := %s) (by decide) (ps := [%s]) (lo := %s) (hi := %s) (τ := %s) (lo2 := %s) (hi2 := %s) (y0 := %s)\n    (by decide +kernel) hy\n') % (
            nm, L, L, ps, q(s0[0]), q(s0[1]), q(c['T']), q(l0[0]), q(l0[1]), q(c['y0']))
if __name__ == '__main__':
    core = tuple(int(x) for x in sys.argv[1].split(','))
    c = cert(core); print('chain pieces', len(c['chain']), 'y0', c['y0'])
    print(lean(core, c))
