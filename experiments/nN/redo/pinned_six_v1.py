"""E390 (2026-10-05), pinned_six_v1: one explicit crossing six read in full: pins, windows, and the speeds of reading 7 that nest them.
Owner: "Yes, do that and keep going on layer 5".  For the first six of X24 (E354) and of the J=2 crossing members with the largest
reading 7: exact K6 windows in [1,7] and K'6 in [9,15], each endpoint named (the exit (8j+1)/rho_y of a reading's zone, or the
entry (8k-1)/rho_w of a reading's zone), then N_A and N_B (E389) as exact intervals of v, and the gap between the pieces nearest the
member's own reading 7.  Exact (Fractions); decimals only as renderings.
"""
import sys, pickle
from fractions import Fraction as F
sys.path.insert(0, '../band_cert_v1')
from core import clear_set
from nesting_overlap_v1 import nest_set

def name_end(R, six, kind):
    out = []
    for y, r in enumerate(six):
        if kind == 'exit':
            j = (R * r - 1) / 8
        else:
            j = (R * r + 1) / 8
        if j.denominator == 1 and j >= 0:
            out.append("%s of reading %d lap %d" % (kind, y + 1, int(j) if kind == 'exit' else int(j)))
    return out or ['(not a zone edge)']

def show(label, x):
    six = x[:6]
    print("==", label, " six=", [float(a) for a in six], " own rho7=%.6f" % float(x[6]))
    for name, lo, hi in (("A [1,7]", F(1), F(7)), ("B [9,15]", F(9), F(15))):
        k = clear_set(six, lo, hi)
        print(" K6 windows in", name, ":", len(k))
        for a, b in k:
            print("   [%.6f, %.6f] len %.3e  left:%s right:%s" % (float(a), float(b), float(b - a), name_end(a, six, 'exit')[:2], name_end(b, six, 'entry')[:2]))
    kA = clear_set(six, F(1), F(7)); kB = clear_set(six, F(9), F(15))
    nA = nest_set(kA, six[5], 7 * six[5]); nB = nest_set(kB, six[5], 7 * six[5])
    print(" N_A pieces:", [(round(float(a), 6), round(float(b), 6)) for a, b in nA])
    print(" N_B pieces:", [(round(float(a), 6), round(float(b), 6)) for a, b in nB][:12], "(%d pieces)" % len(nB))
    near = min((abs(x[6] - (a + b) / 2), (a, b)) for a, b in nB) if nB else None
    if near: print(" nearest N_B piece to own rho7: (%.6f, %.6f)" % (float(near[1][0]), float(near[1][1])))

x24 = [F(1), F(2752864293769, 970238379379), F(3691147638604, 961559468885), F(4851775667488, 988103849833), F(5240560485773, 830842598345), F(2806730537001, 400961505286), F(474233610200591258564537783, 19451412054102649094869700)]
show("X24", x24)
t = pickle.load(open('terminals7_J2.pkl', 'rb'))
cross = {i for i, y in enumerate(t) if y[1] >= 8.999999}
d = pickle.load(open('cell_members7_J2.pkl', 'rb'))
big = sorted([(x[6], i, x) for i, x in d if i in cross and x[6] > 9], reverse=True)[:2]
for r7, i, x in big:
    show("J2 member %d" % i, x)
small = [(x[6], i, x) for i, x in d if i in cross and x[6] < 7.01][:1]
for r7, i, x in small:
    show("J2 member %d (rho7 just above 7)" % i, x)
