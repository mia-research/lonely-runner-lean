#!/usr/bin/env python3
"""The good set G in the phase torus, §5 k = 1 fast regime (alpha -> 0 within a lap): for runner 1 at P, runners 4 and 5
starting lap j at phases (phi4, phi5), the lap has a lonely instant iff some y in [0, 1) has
  y, y + P, (1 + beta) y + phi4, (1 + gamma) y + phi5  all in [1/6, 5/6] (mod 1).
For representative (P, beta, gamma): the measure of G, the share of phi5 for which the phi4-section of G contains an arc of
length >= beta (so runner 4's progression of step beta cannot jump it), and the largest product box A4 x A5 inside G
(grid search)."""
import math
N = 240
def section_y(P, be, ga, f4, f5):
    # union of y-intervals where all four are in band; we only need existence
    ivs = [(1 / 6, 5 / 6)]
    def band_ivs(slope, off):
        out = []
        for m in range(-2, int(slope) + 3):
            a, b = (m + 1 / 6 - off) / slope, (m + 5 / 6 - off) / slope
            a, b = max(a, 0), min(b, 1)
            if b >= a: out.append((a, b))
        return out
    for slope, off in ((1, P), (1 + be, f4), (1 + ga, f5)):
        B = band_ivs(slope, off); new = []
        for a, b in ivs:
            for c, d in B:
                lo, hi = max(a, c), min(b, d)
                if hi >= lo: new.append((lo, hi))
        ivs = new
        if not ivs: return False
    return True
def study(P, be, ga):
    G = [[section_y(P, be, ga, i / N, k / N) for i in range(N)] for k in range(N)]   # G[k][i]: phi5 = k/N, phi4 = i/N
    meas = sum(map(sum, G)) / N / N
    # phi4-sections: longest circular run per phi5
    def longest(row):
        if all(row): return 1.0
        best = run = 0
        for x in row + row:
            run = run + 1 if x else 0; best = max(best, run)
        return min(best, N) / N
    secs = [longest(G[k]) for k in range(N)]
    ok_share = sum(1 for s in secs if s >= be) / N
    # largest square box (side s) inside G: try sides
    best = 0
    for side in range(N // 2, 0, -1):
        found = False
        for k0 in range(0, N, 4):
            for i0 in range(0, N, 4):
                if all(G[(k0 + dk) % N][(i0 + di) % N] for dk in range(0, side, max(1, side // 8)) for di in range(0, side, max(1, side // 8))):
                    found = True; break
            if found: break
        if found: best = side / N; break
    return meas, ok_share, min(secs), best
for P in (1 / 6, 1 / 4, 1 / 3):
    for be, ga in ((0.05, 0.1), (0.1, 0.5), (0.2, 0.3), (0.3, 1.0), (0.45, 0.5), (0.5, 2.0), (0.25, 0.75)):
        m, sh, mn, box = study(P, be, ga)
        print(f"P {P:.3f} beta {be} gamma {ga}: |G| {m:.3f}; phi5 with a phi4-arc >= beta: {sh:.3f}; min longest phi4-arc {mn:.3f}; square box side ~{box:.3f}")
