#!/usr/bin/env python3
"""Generates the Lean case tree for lam = 1, c = 1, D >= 20 (from s6_lam_cert_v1's tree with L = 1/20) and the 37 small
cases (c = 1, D = 15..19) of s6_lam_small_v1, as Lean tactic text inserted into S6Branch_v1.lean."""
import sys
from fractions import Fraction as F
sys.setrecursionlimit(100000)
exec(open("s6_lam_cert_v1.py").read().split("roots = {")[0])
def q(x): return f"({x.numerator}/{x.denominator} : ℝ)" if x.denominator != 1 else f"({x.numerator} : ℝ)"
VAR = {0: "U", 1: "Q", 2: "M"}
def emit(t, ind, L):
    sp = " " * ind
    if t[0] == "leaf":
        kind, m, a = t[1]
        if kind == "after":
            return f"{sp}exact closeA {m} {q(a)} {q(L)} (by norm_num) (by norm_num) (by norm_num) (by norm_num) (fun p h1 h2 => by nlinarith) (fun p h1 h2 => by nlinarith)\n"
        if kind == "before":
            return f"{sp}exact closeB {m} {q(a)} {q(L)} (by norm_num) (by norm_num) (by norm_num) (by norm_num) (fun p h1 h2 => by nlinarith) (fun p h1 h2 => by nlinarith)\n"
        return f"{sp}exact closeS {q(a)} {q(L)} (by norm_num) (by norm_num) (fun p h1 h2 => by nlinarith) (fun p h1 h2 => by nlinarith)\n"
    _, d, mid, l, r = t
    v = VAR[d]
    return (f"{sp}rcases le_total {v} {q(mid)} with h{v}{ind} | h{v}{ind}\n{sp}· \n" + emit(l, ind + 2, L).replace(" " * (ind + 2), " " * (ind + 2), 1)
            + f"{sp}· \n" + emit(r, ind + 2, L))
cell = ((F(2), F(2)), (F(1), F(4, 3)), (F(0), F(1, 3)))
st = {"leaf": 0, "node": 0}
tree = build(cell, 1, F(1, 20), True, 0, st)
txt = emit(tree, 6, F(1, 20)).replace("· \n" + " " * 8, "· ")
open("S6LamTree_v1.txt", "w").write(txt)
print(st); print(txt[:1500])
