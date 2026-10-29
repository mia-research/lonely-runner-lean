# E644: exhaustive float SCREEN of all gcd-1 six-subsets of [1, N] (steers only); flagged sets re-checked exactly.  usage: N [NSHIFT]
import sys, math, itertools, time
sys.argv_save = sys.argv[:]
N = int(sys.argv[1]); NS = int(sys.argv[2]) if len(sys.argv) > 2 else 12
sys.argv = ['x', '1', '1', '1']
exec(open('gap_search_v1.py').read().split('rnd = random.Random')[0])
t0 = time.time(); tested = 0; nowin = []; flagged = []; conf = []
for C in itertools.combinations(range(1, N + 1), 6):
    g = 0
    for d in C: g = math.gcd(g, d)
    if g != 1: continue
    tested += 1
    J, T = windows(C)
    if J is None: nowin.append(C); continue
    gap, y0 = screen(J, T, NS)
    if gap:
        flagged.append(C)
        gx, _ = screen(J, T, 80, exact=True)
        if gx: conf.append((C, str(gx[0]), str(gx[1])))
print('N', N, 'gcd-1 six-subsets', tested, 'no window', len(nowin), 'float-flagged', len(flagged), 'exact gaps (shifts<=80)', len(conf), 'seconds', int(time.time() - t0))
print(conf[:12]); print(nowin[:5])
