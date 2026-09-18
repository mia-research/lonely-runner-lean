# DOOR 3 is over REAL difference sets.  Its distinctive structure: the closure of the orbit
#   { (d_1 t, ..., d_7 t) mod 1 : t in R }  is a closed connected subgroup of the 7-torus.
# If the d_i are Q-LINEARLY INDEPENDENT, Kronecker makes that closure the WHOLE torus, so some t
# puts every runner within eps of 1/2 -- distance ~1/2 >> 1/8.  Loneliness is then immediate and
# the margin is huge, not marginal.  Test that, and test where the difficulty actually sits.
import random, math
def circ(x): 
    f = x - math.floor(x); return min(f, 1-f)
def best_over(ds, T, steps):
    best = 0.0; arg=None
    for j in range(1, steps+1):
        t = T*j/steps
        m = min(circ(d*t) for d in ds)
        if m > best: best, arg = m, t
    return best, arg
rng = random.Random(1)
print("[A] Q-independent (generic irrational) speeds: how close to 1/2 can we drive the MINIMUM?")
res=[]
for _ in range(60):
    ds=[rng.uniform(1,40) for _ in range(7)]          # generically Q-independent
    b,_=best_over(ds, 4000, 400000)
    res.append(b)
res.sort()
print(f"    60 sets: min {res[0]:.4f}  median {res[len(res)//2]:.4f}  max {res[-1]:.4f}   (1/8 = 0.125, 1/2 = 0.5)")
print(f"    sets failing to reach 1/8 : {sum(1 for x in res if x < 0.125)}")
print(f"    sets reaching 0.45 or better: {sum(1 for x in res if x >= 0.45)}")
print()
print("[B] fully DEPENDENT speeds (all integer multiples of one unit) -- the hard case:")
for ds in [(1,2,3,4,5,6,7),(1,2,3,4,5,7,12),(1,4,5,6,7,11,13)]:
    b,arg=best_over([float(x) for x in ds], 1.0, 2000000)
    print(f"    {ds}: best min-distance {b:.6f}  at t~{arg:.6f}   (exactly 1/8 = {1/8})")
print()
print("[C] PARTIAL dependence: 6 integers plus one irrational -- does the free direction rescue it?")
worst=None
for _ in range(40):
    base=sorted(rng.sample(range(1,20),6))
    ds=[float(x) for x in base]+[rng.uniform(1,20)]
    b,_=best_over(ds, 3000, 300000)
    if worst is None or b<worst[0]: worst=(b,base)
print(f"    40 sets, worst best-min-distance {worst[0]:.4f} (integers {worst[1]} + 1 irrational)")
