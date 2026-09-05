# AUDIT re-run: record UNCENSORED first-fall d_ff (cheap) for ALL rungs in the REDUCED system,
# and push Dmax high to try to RESOLVE the reduced solving degree. Decides finding #1.
import random as pyr
_ns=dict(globals()); _ns["__name__"]="h"; exec(open("semaev_elimination_v1.py").read(),_ns)
globals().update({k:v for k,v in _ns.items() if not k.startswith("__")})
exec(open("semaev_symmetric_reduction_lastfall_v1.py").read().split("def main()")[0], globals())
F=GF(307); A=0; B=7; E=EllipticCurve(F,[A,B]); Gp=E.gens()[0]; N=int(E.order())
rng=pyr.Random(1234+307)                                   # SAME frozen construction as the run
Vx=None; tau=None
for _ in range(3000):
    R=int(rng.randrange(1,N))*Gp
    if R==E(0): continue
    xs=[]; good=True
    for _ in range(2):
        Qa=int(rng.randrange(1,N))*Gp; Qb=int(rng.randrange(1,N))*Gp; Qc=R-Qa-Qb
        if E(0) in (Qa,Qb,Qc): good=False; break
        xs+=[int(Qa[0]),int(Qb[0]),int(Qc[0])]
    if good and len(set(xs))==6 and int(R[0]) not in set(xs):
        Vx=xs; tau=int(R[0]); break
planted_e=sym_of([F(v) for v in Vx[:3]])
P,Rer,ok,S4tau,Rx=build_reduction(F,A,B,tau)
r_eqs=remainder_eqs(Rer,Vx); support=list(P.monomials())
print("tau=%d ok=%s"%(tau,ok))
# (a) UNCENSORED first-fall across rungs (Dmax=12 is well above d_ff=5)
sem12=last_fall_of(F,[P]+r_eqs,list(Rer.gens()),12)
print("dff CROSS-CHECK (Dmax=12, uncensored):")
print("  SEMAEV reduced d_ff=%s"%sem12["d_ff"])
dffs=[]
for k in range(12):
    r2=pyr.Random(9000+307+k); Pr=Rer(0)
    for mon in support: Pr+=F(r2.randrange(1,307))*mon
    Pr=Pr-Pr(planted_e[0],planted_e[1],planted_e[2])
    dffs.append(last_fall_of(F,[Pr]+r_eqs,list(Rer.gens()),12)["d_ff"])
print("  12 random d_ff distinct set = %s"%sorted(set(dffs)))
# (b) try to RESOLVE the reduced solving degree at high Dmax (Semaev + 3 randoms)
print("d_solv RESOLUTION attempt (Dmax=52):")
r=last_fall_of(F,[P]+r_eqs,list(Rer.gens()),52)
print("  SEMAEV reduced d_ff=%s d_LF=%s d_solv=%s quo=%s"%(r["d_ff"],r["d_LF"],r["d_solv"],r["quo"]))
for k in range(3):
    r2=pyr.Random(9000+307+k); Pr=Rer(0)
    for mon in support: Pr+=F(r2.randrange(1,307))*mon
    Pr=Pr-Pr(planted_e[0],planted_e[1],planted_e[2])
    rr=last_fall_of(F,[Pr]+r_eqs,list(Rer.gens()),52)
    print("  rand %d d_ff=%s d_LF=%s d_solv=%s"%(k,rr["d_ff"],rr["d_LF"],rr["d_solv"]))
print("AUDIT DONE")
