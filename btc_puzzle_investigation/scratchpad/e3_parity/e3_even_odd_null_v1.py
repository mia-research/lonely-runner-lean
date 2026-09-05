"""
DIAGNOSTIC (post-hoc; NOT a pre-registered test -- see caveat below).

Exact identity:  E3 = A3^2 - A3*B3 + B3^2  with A3=a-c, B3=b-c   (stats3, verbatim)
                    = 1/4*(2A3-B3)^2 + 3/4*(B3)^2
   EVEN  = 2A3-B3 = 2a-b-c = 1^T C 1   (orientation-even: swapping w<->w2 fixes it)
   ODD   = B3     = b-c                (orientation-odd:  swapping w<->w2 negates it)

Real 82 (field-difference): A3=-100, B3=-125 -> EVEN=-75 (10.7% of E3), ODD=-125 (89.3%).
`RESULT_spectral_decomp_v1.md` tested ONLY the EVEN mode (its `allones`=|2a-b-c|/82=75/82).

This regenerates the FROZEN structural null (seed 20260818, identical rand_curve_x stream,
so set i here == set i of the 20000-set frozen run) and percentiles EVEN and ODD separately.
qr_bit is skipped: cube_marginals sums over the qr bit, so it cannot affect (a,b,c), and it
consumes no RNG -- the sets are bit-identical.

CAVEAT: the 89/11 split of the REAL value is an exact algebraic fact. The percentiles below
are a POST-HOC diagnostic computed after seeing that split; any grade move needs its own
experiment-designer prereg + OOS. Reported as a diagnostic, not a verdict.
"""
import random, sys, time, json
try:
    from gmpy2 import mpz, powmod
    def _pw(z, e, m): return int(powmod(mpz(z), e, m))
    FAST = True
except ImportError:
    def _pw(z, e, m): return pow(int(z), e, m)
    FAST = False

P    = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
Bc   = 7
BETA = 0x7AE96A2B657C07106E64479EAC3434E99CF0497512F58995C1396C28719501EE
BETA2 = pow(BETA, 2, P)
E2EXP = (P - 1) // 2
E3EXP = (P - 1) // 3

def cube_class(z):
    r = _pw(z, E3EXP, P)
    return 0 if r == 1 else (1 if r == BETA else 2)

def rand_curve_x(rng):                      # IDENTICAL to e3_owed_measurement_v1.py
    while True:
        x = rng.randrange(0, P)
        rhs = (x * x % P * x + Bc) % P
        if rhs == 0:
            continue
        if _pw(rhs, E2EXP, P) == 1:
            return x

def abc(xs):
    n = len(xs); C = [0, 0, 0]
    for i in range(n):
        xi = xs[i]
        for j in range(i + 1, n):
            C[cube_class((xi - xs[j]) % P)] += 1
    return C

N = int(sys.argv[1]) if len(sys.argv) > 1 else 2000
rng = random.Random(20260818)               # FROZEN seed of the original run
t0 = time.perf_counter(); rows = []
for i in range(N):
    xs = [rand_curve_x(rng) for _ in range(82)]
    a, b, c = abc(xs)
    A3, B3 = a - c, b - c
    rows.append((a, b, c, A3, B3, A3*A3 - A3*B3 + B3*B3, 2*A3 - B3))
    if (i + 1) % 100 == 0:
        print(f"  {i+1}/{N}  ({time.perf_counter()-t0:.0f}s)", flush=True)

E3n   = sorted(r[5] for r in rows)
EVENn = sorted(abs(r[6]) for r in rows)
ODDn  = sorted(abs(r[4]) for r in rows)
def pct(sn, v): return 100.0 * sum(1 for u in sn if u < v) / len(sn)
def ptwo(sn, v): return sum(1 for u in sn if u >= v) / len(sn)   # one-sided (high) on |.|

REAL = dict(E3=13125, EVEN=75, ODD=125)
out = dict(N=N, frozen_seed=20260818, real=REAL,
           E3_pctile=pct(E3n, REAL['E3']),   E3_p_high=ptwo(E3n, REAL['E3']),
           EVEN_pctile=pct(EVENn, REAL['EVEN']), EVEN_p_high=ptwo(EVENn, REAL['EVEN']),
           ODD_pctile=pct(ODDn, REAL['ODD']),   ODD_p_high=ptwo(ODDn, REAL['ODD']),
           null_med_E3=E3n[N//2], null_med_EVEN=EVENn[N//2], null_med_ODD=ODDn[N//2])
print(json.dumps(out, indent=2))
json.dump(out, open("scratchpad/e3_parity/e3_even_odd_null_v2_N20000.json", "w"), indent=2)
