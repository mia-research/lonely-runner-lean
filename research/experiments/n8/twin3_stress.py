"""twin3_stress.py -- stress the lemma boundaries: very large e' with tiny m, and
tiny e' with very large m.  Exact safe measure of the FULL seven-runner set."""
from twin3_window import safe_measure
tot=0; zeros=[]; worst=None
for rho0 in (2,4,6):
    for rho2 in (1,3,5,7,rho0):
        for q in list(range(1,13))+list(range(280,301)):
            for m in list(range(1,13))+list(range(280,301)):
                if len({1,3,5,7,rho0,8*q+rho2,8*m})!=7: continue
                mu=safe_measure(rho0,rho2,q,m); tot+=1
                if mu==0: zeros.append((rho0,rho2,q,m))
                if worst is None or mu<worst[0]: worst=(mu,rho0,rho2,q,m)
print(f"stress: {tot} tuples (q' and m each in 1..12 u 280..300), zeros={len(zeros)}")
print("min safe measure:",worst)
