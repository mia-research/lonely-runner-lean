"""
n=8 pacemaker/slot architecture -- v2.  Adds arbitrary configurations to v1's
AP-limit report, so the three TIGHT instances found by tight_sets_v2.py can be
read in the same frame.  Exact rational arithmetic throughout.

Conventions (v33 sec 2, translated to n=8; see pacemaker_n8_v1.py header):
  a_i = 7 e_i / e_7,   a_7 = 7,   B_{j,k} = [(8k+7)/(8a_j), (8k+9)/(8a_j)]
  I_s = [(8s+1)/56, (8s+7)/56]   (gaps of the pacemaker a_7 = 7)
  W_ref = [1/(8a_1), 7/(8a_1)]
A slot is CLAIMED by runner j when an endpoint of some B_{j,k} equals the slot's
AP witness t_m = m/8, m = s+1; that endpoint contact is the tight touch.
"""
from fractions import Fraction as F
import sys

N = 8
def I(s):   return (F(N*s+1, N*(N-1)), F(N*s+N-1, N*(N-1)))
def B(aj,k):return (F(N*k+N-1, N*aj), F(N*k+N+1, N*aj))

def pieces_on(a, box, skip):
    out=[]
    for j,aj in a.items():
        if j in skip: continue
        k=0
        while B(aj,k)[1] <= box[0]: k+=1
        while B(aj,k)[0] < box[1]:
            lo,hi = max(B(aj,k)[0],box[0]), min(B(aj,k)[1],box[1])
            if lo<hi: out.append((lo,hi,j,k))
            k+=1
    return sorted(out)

def gaps_of(pieces, box):
    g,cur=[],box[0]
    for lo,hi,_,_ in pieces:
        if lo>cur: g.append((cur,lo))
        if hi>cur: cur=hi
    if cur<box[1]: g.append((cur,box[1]))
    return g

def touches(pieces, box):
    """Zero-length contacts: right endpoint of one piece == left endpoint of the next
    uncovered frontier.  These are the points where the configuration is tight."""
    t,cur=[],box[0]
    for lo,hi,j,k in pieces:
        if lo==cur and cur>box[0]: t.append((cur,j,k))
        if hi>cur: cur=hi
    return t

def report(T, nslots=None):
    e=sorted(T); top=e[-1]
    a={i+1: F((N-1)*v, top) for i,v in enumerate(e)}
    a1=a[1]; w=(F(1,N*a1), F(N-1,N*a1))
    print(f"=== T = {tuple(e)}   ratio e_max/e_min = {F(top,e[0])} ===")
    print(f"a = {[str(a[i]) for i in range(1,N)]}")
    print(f"W_ref = [{w[0]}, {w[1]}]  (a_1 = {a1}{'  < 1  LARGE-RATIO' if a1<1 else '  >= 1  bounded'})")
    s=1; shown=0; ncov=0; ntouch=0
    while I(s)[0] < w[1]:
        box=(max(I(s)[0],w[0]), min(I(s)[1],w[1]))
        if box[0]>=box[1]: s+=1; continue
        p=pieces_on(a,box,skip=(1,N-1)); g=gaps_of(p,box); tc=touches(p,box)
        m=s+1
        wit=F(m,N) if F(m,N)>=box[0] and F(m,N)<=box[1] else None
        tag = "COVERED" if not g else f"GF>0 gaps={[ (str(x),str(y)) for x,y in g ]}"
        print(f" I_{s} [{box[0]},{box[1]}] {tag}"
              f"  touches={[(str(x),f'r{j}') for x,j,k in tc]}"
              f"{'  witness t='+str(wit) if wit is not None else ''}")
        ncov += (not g); ntouch += len(tc); shown+=1; s+=1
        if nslots and shown>=nslots: break
    print(f" -> {shown} slots inspected, {ncov} fully covered, {ntouch} tight touches\n")

if __name__=="__main__":
    for T in [(1,2,3,4,5,6,7),(1,2,3,4,5,7,12),(1,4,5,6,7,11,13)]:
        report(T)
