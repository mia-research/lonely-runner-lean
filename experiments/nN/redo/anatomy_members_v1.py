# Anatomy of the cascade on REAL EightResidual members (all 22 fields): B1 from residual_members_v5's generator,
# C1 from residual_members_C_list_v1.json.  Exact (Fractions); display in units of d_min.
import sys, json, os
from fractions import Fraction as F
os.chdir('..')
src = open('residual_members_v5.py').read().split("E8 = F(1, 8)")[0]
import io, contextlib
with contextlib.redirect_stdout(io.StringIO()):
    exec(src)
B = [tuple(S) for S in found]
Cj = json.load(open('residual_members_C_list_v1.json'))
C = [tuple(S) for S in Cj['A']] + [tuple(S) for S in Cj['B']]
assert all(all(f(S) for _, f in FIELDS) for S in B[:5]), "fields"
def cd(x): x = x % 1; return min(x, 1 - x)
def run(S):
    S = sorted(S); t = F(1, 8 * S[0]); steps = []
    while True:
        bl = [d for d in S if cd(d * t) < F(1, 8)]
        if not bl: return steps, t
        c = max(((F(8 * round(d * t) + 1, 8 * d), d, round(d * t)) for d in bl))
        steps.append((t, bl, c)); t = c[0]
def show(S, name):
    S = sorted(S); m = S[0]; steps, t = run(S)
    print("=" * 100); print(name, " readings / d_min:", [round(float(F(x, m)), 4) for x in S])
    print(" d_min mod 8 =", m % 8, "; residues of readings mod 8:", [x % 8 for x in S])
    print(" cascade moves:", len(steps))
    pos = lambda x, t: float((8 * x * t) % 8)
    for i, (t0, bl, (t1, d, k)) in enumerate(steps):
        r0 = float(8 * m * t0); r1 = float(8 * m * t1)
        print("  move %d: R=%.4f -> %.4f ; blockers at start: ranks %s ; setter rank %d lap %d" % (
            i + 1, r0, r1, [S.index(x) + 1 for x in bl], S.index(d) + 1, k))
        for j, x in enumerate(S):
            p0, p1 = pos(x, t0), pos(x, t1)
            print("     rank %d  x/dmin=%7.3f  pos %7.3f -> %7.3f  (shift %7.3f)%s" % (
                j + 1, float(F(x, m)), p0, p1, float(8 * x * (t1 - t0)), "  *in the way" if min(p1, 8 - p1) < 1 else ""))
    # landing
    cands = [(b, (t * 8 * b - 1) / 8) for b in S if ((t * 8 * b - 1) / 8).denominator == 1]
    b, k = cands[0][0], int(cands[0][1])
    print(" LANDING t: R=%.4f ; flank rank %d, lap k=%d ; all (rank,k) representations: %s" % (
        float(8 * m * t), S.index(b) + 1, k, [(S.index(bb) + 1, int(kk)) for bb, kk in cands]))
    print("  grid D=b: reading a = b*q + r, eps=r/b; position = q + eps + 8{k eps} (mod 8), in eighths")
    for j, a in enumerate(S):
        q, r = divmod(a, b); eps = F(r, b); fr = (k * eps) % 1
        p = float((q + eps + 8 * fr) % 8)
        print("     rank %d  q=%d  eps=%.4f  {k eps}=%.4f   pos=%7.3f  margin beyond edge=%6.3f" % (j + 1, q % 8, float(eps), float(fr), p, min(p, 8 - p) - 1))
if __name__ == "__main__":
    print("B1 members:", len(B), " C1 members:", len(C))
    for i in (0, 1, 7): show(B[i], "B1 #%d" % i)
    for i in (0, 1): show(C[i], "C1 #%d" % i)
