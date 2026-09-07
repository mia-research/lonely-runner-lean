"""
The n=8 pacemaker/slot architecture -- the Method-2 (eleven_lonely_runners_v33)
window machinery, instantiated at n=8.  Exact rational arithmetic (Fraction).

Definitions, translated term-for-term from v33 sec 2 (n=11) to n=8:
  normalise a_i = 7 e_i / e_7, so a_7 = 7 and 0 < a_1 < ... < a_6 < 7.
  bad intervals   B_{j,k}(a_j) = [ (8k+7)/(8 a_j), (8k+9)/(8 a_j) ],  k >= 0
                  (width 2/(8 a_j) = 1/(4 a_j), centre (k+1)/a_j)
  pacemaker slots I_s = [ (8s+1)/56, (8s+7)/56 ],  s = 1..6   (width 6/56 = 3/28)
                  -- the gaps between consecutive bad intervals of the pacemaker a_7 = 7.
  window          W_ref = [ 1/(8 a_1), 7/(8 a_1) ]   (runner 1 lonely throughout)
  GF(I_s)         = |I_s \\ union_j B_{j,k}| / |I_s|,  union over j = 2..6.

At n=11 the counts are 9 slots / 8 free runners; at n=8 they are 6 slots / 5 free
runners.  Both are the general-n count (n-2 slots, n-3 free runners): surplus 1.

This script emits the AP-limit ownership table and the covering chains, with every
touch point and every slack reported as an exact rational.
"""
from fractions import Fraction as F
import sys

N = 8
def I(s):                       # pacemaker slot s, s = 1..N-2
    return (F(N*s+1, N*(N-1)), F(N*s+N-1, N*(N-1)))

def B(aj, k):                   # bad interval k of a runner at normalised speed aj
    return (F(N*k+N-1, N*aj), F(N*k+N+1, N*aj))

def W_ref(a1):
    return (F(1, N*a1), F(N-1, N*a1))

def clip(iv, box):
    lo = max(iv[0], box[0]); hi = min(iv[1], box[1])
    return (lo, hi) if lo < hi else None

def covering_pieces(a, box, skip=()):
    """All bad intervals of runners a[j] (1-indexed dict) meeting box."""
    out = []
    for j, aj in a.items():
        if j in skip: continue
        k = 0
        # first k with right endpoint > box[0]
        while B(aj, k)[1] <= box[0]: k += 1
        while B(aj, k)[0] < box[1]:
            c = clip(B(aj, k), box)
            if c: out.append((c[0], c[1], j, k))
            k += 1
    return sorted(out)

def uncovered(pieces, box):
    """Exact maximal uncovered subintervals of box, given covering pieces."""
    gaps, cur = [], box[0]
    for lo, hi, j, k in pieces:
        if lo > cur: gaps.append((cur, lo))
        if hi > cur: cur = hi
    if cur < box[1]: gaps.append((cur, box[1]))
    return gaps

def ap_report():
    a = {j: F(j) for j in range(1, N)}          # AP limit a_j = j
    w = W_ref(a[1])
    print(f"AP limit a_j = j.  W_ref = [{w[0]}, {w[1]}] = [{F(w[0]*56)}/56, {F(w[1]*56)}/56]")
    print(f"free runners (blockers) = 2..{N-2};  pacemaker a_{N-1} = {N-1};  slots s = 1..{N-2}\n")
    for s in range(1, N-1):
        box = clip(I(s), w)
        lab = s + 1                              # witness label m with I_s <-> t_m = m/n
        head = f"I_{s}  = [{F(I(s)[0]*56)}/56, {F(I(s)[1]*56)}/56]   witness t_{lab} = {F(lab,N)}"
        if box is None:
            print(head + "   -- EMPTY inside W_ref at a_1 = 1"); print()
            continue
        pieces = covering_pieces(a, box, skip=(1, N-1))
        gaps = uncovered(pieces, box)
        # owners: runners whose bad-interval ENDPOINT equals the witness (tight touch)
        owners = []
        for j in range(2, N-1):
            k = 0
            while B(a[j], k)[0] < 1:
                if B(a[j], k)[0] == F(lab, N) or B(a[j], k)[1] == F(lab, N):
                    owners.append(j); break
                k += 1
        print(head)
        print("   chain: " + " ".join(
            f"r{j}[{float(lo)*56:.3f},{float(hi)*56:.3f}]" for lo, hi, j, k in pieces))
        print(f"   covered: {'YES' if not gaps else 'NO  gaps=' + str(gaps)}"
              f"   |  AP-limit owners (tight touch at t_{lab}): {owners if owners else 'NONE -- UNCLAIMED'}")
        # slack: min overlap along the chain, and the two overhangs
        ov = []
        cur = pieces[0][1]
        for lo, hi, j, k in pieces[1:]:
            ov.append(cur - lo); cur = max(cur, hi)
        print(f"   left overhang {F((box[0]-pieces[0][0])*56)}/56, "
              f"right overhang {F((pieces[-1][1]-box[1])*56)}/56, "
              f"chain overlaps {[str(F(x*56))+'/56' for x in ov]}")
        print()

if __name__ == "__main__":
    ap_report()
