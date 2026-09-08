r"""
hp_peel_v1 -- the PEELING bound, corrected.

The error in hp_iterated_v1's intermediate levels was using MERGED components of D_k.
The discrepancy lemma needs the ambient set X to be split into intervals on which the
TARGET residue class is constant; on a merged component of D_3 the missing value phi
can change.  The correct count is the number of CELLS of the sub-grid of the peeled-off
runners that lie in D_k.  (The closed form of hp_iterated_v1 already used the cell
bound, which is why it never failed.)

PEELING IDENTITY.  Fix rho and let D^rho = { the other three nu's are distinct }.  On
each cell of the 3-runner grid contained in D^rho the missing value phi is constant, and
   { nu_rho = phi } = { floor(e_rho y) = phi XOR mu(rho)  (mod 4) }
is periodic of period 4/e_rho, density 1/4, ONE interval per period.  The discrepancy
lemma gives, per cell, an error at most (1/4)(3/4)(4/e_rho) = 3/(4 e_rho).  Hence

   | o - |D^rho|/4 |  <=  3 N^rho / (4 e_rho),          N^rho = #cells of the 3-runner
                                                        grid that lie in D^rho
   N^rho <= (sum of the other three speeds) - 2.

COROLLARY (proved).   o <= |D^rho|/4 + 3 N^rho/(4 e_rho)  <=  1/4 + 3 Sigma^rho/(4 e_rho),
so   o < 1/2   whenever   e_rho > 3 Sigma^rho   for some rho,  Sigma^rho = sum of the
other three speeds.  In particular o < 1/2 whenever the largest speed exceeds three
times the sum of the other three.

Sharper, still finite: o < 1/2 as soon as  e_rho > 3 N^rho / (2 - |D^rho|).
"""
import itertools, sys, random
from math import lcm, gcd
from fractions import Fraction as F

RHOS = (1, 3, 5, 7)
MU = {1: 0, 3: 1, 5: 2, 7: 3}


def peel(sp, k):
    """peel runner index k.  Returns (|D|, N, o, e_k, Sigma) with N the exact number of
    cells of the OTHER-THREE grid lying in D, all exact."""
    others = [i for i in range(4) if i != k]
    three = [sp[i] for i in others]
    mus3 = [MU[RHOS[i]] for i in others]
    D3 = lcm(*three)
    pts = sorted({a for e in three for a in range(0, D3, D3 // e)})
    pts.append(D3)
    dm = 0; N = 0
    segs = []
    for i in range(len(pts) - 1):
        a = pts[i]; w = pts[i + 1] - a
        nu = [(((three[j] * a) // D3) % 4) ^ mus3[j] for j in range(3)]
        if len(set(nu)) == 3:
            dm += w; N += 1
            missing = ({0, 1, 2, 3} - set(nu)).pop()
            segs.append((F(a, D3), F(pts[i + 1], D3), missing))
    # exact o via the peeled runner
    e = sp[k]; mu = MU[RHOS[k]]
    o = F(0)
    for lo, hi, miss in segs:
        tgt = miss ^ mu
        # measure of { y in [lo,hi) : floor(e y) = tgt mod 4 }
        j0 = int(lo * e); j1 = int(hi * e) + 1
        acc = F(0)
        for j in range(j0, j1):
            if j % 4 == tgt:
                a2 = max(lo, F(j, e)); b2 = min(hi, F(j + 1, e))
                if a2 < b2:
                    acc += b2 - a2
        o += acc
    return F(dm, D3), N, o, e, sum(three)


def bounds(sp):
    out = []
    for k in range(4):
        dm, N, o, e, S = peel(sp, k)
        err = F(3 * N, 4 * e)
        out.append(dict(k=k, D=dm, N=N, o=o, e=e, S=S, bound=dm / 4 + err,
                        crude=F(1, 4) + F(3 * S, 4 * e),
                        thresh=F(3 * N, 1) / (2 - dm)))     # e > thresh  =>  o < 1/2
    return out


from hp_omax_v1 import ou

tests = [(1,3,5,7),(1,11,5,7),(17,3,5,7),(9,3,21,15),(1,3,13,15),(41,43,13,15),
         (1,11,5,151),(1,3,5,1007),(9,19,101,4001),(1,3,5,71),(1,3,5,47)]
print("peeling: exact o reproduced through every peel, and the bound")
print(f"{'tuple':>22} {'o(nf)':>9} {'best bound':>11} {'<1/2':>5}  min threshold e* needed")
bad = 0
for sp in tests:
    o_ref, _ = ou(sp)
    bs = bounds(sp)
    for b in bs:
        if b['o'] != o_ref:
            bad += 1
            print("   O MISMATCH", sp, b['k'], b['o'], o_ref)
    best = min(b['bound'] for b in bs)
    th = min(float(b['thresh']) for b in bs)
    print(f"{str(sp):>22} {float(o_ref):>9.6f} {float(best):>11.6f} {str(best < F(1,2)):>5}"
          f"   {th:.1f}  (speeds {sp})")
print("   o reproduced by every peel:", bad == 0)

print("\ncoverage of the proved criterion  o < 1/2")
for label, gen in (
    ("exhaustive q<=5", (tuple(8*q+r for q, r in zip(qs, RHOS))
                          for qs in itertools.product(range(6), repeat=4))),
):
    n = c_sharp = c_crude = 0
    for sp in gen:
        if len(set(sp)) != 4:
            continue
        n += 1
        bs = bounds(sp)
        if min(b['bound'] for b in bs) < F(1, 2):
            c_sharp += 1
        if min(b['crude'] for b in bs) < F(1, 2):
            c_crude += 1
    print(f"   {label}: {n} tuples;  sharp form closes {c_sharp} ({100*c_sharp/n:.2f}%);"
          f"  crude form e > 3*Sigma closes {c_crude} ({100*c_crude/n:.2f}%)")

print("\nrandom, one dominant speed:  e_7 = 8*q+7 with q large, others small")
random.seed(5)
n = c = 0
for _ in range(400):
    sp = (8*random.randrange(0, 4)+1, 8*random.randrange(0, 4)+3,
          8*random.randrange(0, 4)+5, 8*random.randrange(20, 400)+7)
    if len(set(sp)) != 4:
        continue
    n += 1
    if min(b['bound'] for b in bounds(sp)) < F(1, 2):
        c += 1
print(f"   {n} tuples with a dominant e_7: closed {c} ({100*c/n:.1f}%)")
