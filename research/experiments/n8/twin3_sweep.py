"""twin3_sweep.py -- exact sweep of the whole twin family.
E = {1,3,5,7,rho0} u {e'=8q'+rho'} u {8m}.  Reports the exact safe measure and
flags any tuple with safe measure 0 (which would be a counterexample to the goal).
"""
import sys
from fractions import Fraction as F
from twin3_core import uncovered_cells, measure, bad, FULL

def safe_cells(E):
    return uncovered_cells(list(E))

def run(QMAX, MMAX, verbose_min=8):
    zeros = []
    worst = []
    for rho0 in (2,4,6):
        for rho2 in (1,3,5,7,rho0):
            for q in range(1, QMAX+1):
                e2 = 8*q + rho2
                for m in range(1, MMAX+1):
                    E = tuple(sorted({1,3,5,7,rho0,e2,8*m}))
                    if len(E) != 7:
                        continue
                    cells = safe_cells(E)
                    mu = measure(cells)
                    if mu == 0:
                        zeros.append((rho0,rho2,q,m,E))
                    worst.append((mu, rho0, rho2, q, m, E))
    worst.sort(key=lambda z: z[0])
    print(f"swept q'<={QMAX}, m<={MMAX}:  {len(worst)} admissible tuples")
    print(f"ZERO-safe-measure tuples: {len(zeros)}")
    for z in zeros[:20]:
        print("   ", z)
    print("smallest safe measures:")
    for mu,rho0,rho2,q,m,E in worst[:verbose_min]:
        print(f"   mu={mu}={float(mu):.6f}  rho0={rho0} rho'={rho2} q'={q} m={m}  E={E}")
    return zeros, worst

if __name__ == "__main__":
    QMAX = int(sys.argv[1]) if len(sys.argv)>1 else 12
    MMAX = int(sys.argv[2]) if len(sys.argv)>2 else 20
    run(QMAX, MMAX)
