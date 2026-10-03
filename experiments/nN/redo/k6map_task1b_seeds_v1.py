# Task 1(b) part 2: R2 on six-tuples taken from the 11,176 exact gate-crossing arrangements of stress_seeds_v1.pkl (their sixes have a nonempty allowed set for rho_7),
# plus 1000 exact perturbations of those sixes (ties moved off / on), compared with the direct cascade path() of the seven readings.
import pickle, random, time
exec(open('k6map_task1b_v1.py').read().split('t0 = time.time(); tuples = []')[0])
seeds = list(pickle.load(open('stress_seeds_v1.pkl', 'rb')).keys())
rnd2 = random.Random(77); rnd2.shuffle(seeds)
tuples = []
for x in seeds[:1000]:
    six = list(x[:6]); tuples.append(("seed six", six, x[6]))
for x in seeds[1000:2000]:           # perturbed sixes: each reading 2..6 moved by an exact amount up to 1e-3 (kept strictly increasing)
    six = [x[0]] + [t + F(rnd2.randint(-1000, 1000), 10**6) for t in x[1:6]]
    if all(a < b for a, b in zip(six, six[1:])): tuples.append(("perturbed six", six, None))
t0 = time.time(); tested = mism = ct = cf = nonempty = own_in = 0; ratios = []
for name, s, r7 in tuples:
    c, A = allowed(s)
    if A: nonempty += 1
    if r7 is not None and inA(A, r7): own_in += 1
    pts = points(s, A)
    if r7 is not None: pts = sorted(set(pts + [r7]))
    for x in pts:
        R = path(s + [x])[1]; direct = R > 7; pred = inA(A, x); tested += 1
        if direct != pred:
            mism += 1
            if mism <= 5: print("MISMATCH", name, [str(t) for t in s], x, direct, pred, R)
        if direct: ct += 1
        else: cf += 1
    if A:
        ratios.append(max(h for l, h in A) * max(b - a for a, b in c) / 2)
    if time.time() - t0 > 480: print("time budget reached at tuple", tuples.index((name, s, r7))); break
print("six-tuples", len(tuples), "(seed sixes %d, perturbed %d)" % (sum(1 for t in tuples if t[0] == "seed six"), sum(1 for t in tuples if t[0] != "seed six")))
print("with nonempty allowed set:", nonempty, "| seed sixes whose own rho_7 lies in the allowed set:", own_in)
print("test points:", tested, "| direct crossing:", ct, "not crossing:", cf, "| mismatches R2 vs direct path():", mism)
print("sup(A) * L_max / 2: max %.6f min %.6f (each < 1 by W)" % (float(max(ratios)), float(min(ratios))))
