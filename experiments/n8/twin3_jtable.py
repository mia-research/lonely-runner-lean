"""twin3_jtable.py -- the exact J-table: which twin residues j kill which window.

For each rho0, each base window (a,b,V), and each admissible rho', print
  J = { j : V subset of bad(rho', j) },  |J|, and the gap profile of A(e',J):
gaps of A(e',J) inside one period of 8/e' have lengths d/e' listed as `gaps`.
"""
from twin3_core import bad, J_set
from twin3_window import _BW

def gap_profile(J):
    """Lengths (in units of 1/c) of the maximal runs of Z/8 \\ J, cyclically."""
    if not J: return [8]
    comp = [j for j in range(8) if j not in J]
    runs=[]; 
    # cyclic runs
    start=None
    j=0
    seq=[(j in J) for j in range(8)]
    # rotate so that index 0 is in J
    k=min(J)
    order=[(k+i)%8 for i in range(8)]
    cur=0
    for idx in order:
        if idx in J:
            if cur: runs.append(cur); cur=0
        else:
            cur+=1
    if cur: runs.append(cur)
    return sorted(runs, reverse=True)

def comp_profile(J):
    """Lengths (in units 1/c) of maximal runs of J, cyclically."""
    if not J: return [0]
    k=min(i for i in range(8) if i not in J) if len(J)<8 else 0
    order=[(k+i)%8 for i in range(8)]
    runs=[]; cur=0
    for idx in order:
        if idx in J: cur+=1
        else:
            if cur: runs.append(cur); cur=0
    if cur: runs.append(cur)
    return sorted(runs, reverse=True)

if __name__=="__main__":
    for rho0 in (2,4,6):
        print(f"===== rho0 = {rho0} =====")
        for rho2 in (1,3,5,7,rho0):
            print(f"  rho' = {rho2}")
            for a,b,V in _BW[rho0]:
                J=J_set(rho2,V)
                print(f"    W=[{a},{b}) len={b-a}  V={sorted(V)}  J={sorted(J)} |J|={len(J)}"
                      f"  maxcomp={max(comp_profile(J))}  maxgap={max(gap_profile(J))}")
