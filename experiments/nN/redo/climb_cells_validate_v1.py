"""Completeness check for climb_cells_v1: every real late climb's word (setter reading index, lap) must appear
among the terminal cells of the enumeration, and its real far reading S must lie in that word's S-range.  Exact."""
import sys, re, ast
from fractions import Fraction as F
from gmpy2 import mpq
from late_word_validate_v1 import word_of, cases
from arrangement_lib import readings
fn = sys.argv[1]
cells = {}
for line in open(fn):
    w, t, lo, hi = line.rstrip('\n').split('\t')
    cells.setdefault(w, []).append((mpq(lo), mpq(hi)))
found = missing = 0
for V, sub in cases:
    ds = readings(V, V.index(sub)); s, w = word_of(ds)
    key = str([(j, M) for j, M in w])
    S = mpq(max(ds), min(ds))
    if key in cells and any(lo <= S <= hi for lo, hi in cells[key]): found += 1
    else: missing += 1; print("MISSING", V, sub, key, float(S))
print(f"real late climbs found among terminal cells (word and S-range): {found}; missing {missing}")
