"""twin3_sweep2.py -- wide exact sweep using the validated window engine."""
import sys
from twin3_window import safe_measure

def run(QMAX, MMAX, show=15):
    rows=[]; zeros=[]
    for rho0 in (2,4,6):
        for rho2 in (1,3,5,7,rho0):
            for q in range(1,QMAX+1):
                e2=8*q+rho2
                for m in range(1,MMAX+1):
                    if len({1,3,5,7,rho0,e2,8*m})!=7: continue
                    mu=safe_measure(rho0,rho2,q,m)
                    rows.append((mu,rho0,rho2,q,m))
                    if mu==0: zeros.append((rho0,rho2,q,m))
    rows.sort(key=lambda z:z[0])
    print(f"q'<={QMAX}, m<={MMAX}: {len(rows)} tuples, zeros = {len(zeros)}")
    for z in zeros[:30]: print("  ZERO:",z)
    for mu,r0,r2,q,m in rows[:show]:
        print(f"  mu={mu} = {float(mu):.7f}  rho0={r0} rho'={r2} q'={q} (e'={8*q+r2}) m={m}")
    # per-rho0 minima
    for r0 in (2,4,6):
        sub=[r for r in rows if r[1]==r0]
        print(f"  min over rho0={r0}: {sub[0][0]} = {float(sub[0][0]):.7f} at rho'={sub[0][2]} q'={sub[0][3]} m={sub[0][4]}")
    return rows

if __name__=="__main__":
    run(int(sys.argv[1]), int(sys.argv[2]))
