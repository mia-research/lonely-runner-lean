#!/usr/bin/env python3
"""Independent implementation of Rosenfeld's Lemma 7 criterion (arXiv:2509.14111).

Rosenfeld's proof of the LRC for eight runners (k = 7 moving speeds, bound 1/8)
turns on a finite criterion: for a given k and p, if there is NO "bad cover",
then p divides the product of the speeds of any k-set lacking the LR property.
Verifying this for 27 primes forces the product past the Malikiosis-Santos-
Schymura bound, giving the contradiction.

CRITERION (Lemma 7).  Set N = (k+1)p.  Say v COVERS j iff ||jv/N|| < 1/(k+1),
which -- because N/(k+1) = p exactly -- is the clean integer condition

    (j*v mod N) < p   or   (j*v mod N) > N - p.

A "bad cover" is a k-subset of {1..floor(N/2)} minus multiples of p that covers all of
{1..floor(N/2)} and satisfies gcd(S u {N}) = 1 for every (k-1)-subset S.
No bad cover  =>  Lemma 7 applies to (k, p).

VALIDATION against the paper (this is why the implementation can be trusted):

  k=3   applies for all primes >= 7, fails at 5.
        Paper section 7: "true for all prime p larger than 7".  MATCH.
        Table 1 S = {7,11,13} and lcm(2,3,4)*7*11*13 = 12012.  MATCH.

  k=6   13 WORKS, 17 FAILS, 19 WORKS, 23 FAILS, 29 FAILS.
        Paper section 7: "true for all prime p larger than 31 and for 13 and 19
        (it is not true for 17, 23 and 29)".  EXACT MATCH, including the
        non-obvious sporadic pattern.  This is the strongest validation
        available, since it is the paper's most specific claim.

  The v-range halving (v <= N/2, justified in the paper by the v <-> N-v
  symmetry) is confirmed empirically: half_v=True and half_v=False agree.

ONE DISCREPANCY, unresolved and recorded rather than glossed:

  k=4   this implementation finds p=13 WORKS.  Section 7 says k=4 is "true for
        all prime p larger than 17", and Table 1 uses S = {17,19,23,29,31,37}.
        Confirmed by both the pruned and the unpruned exhaustive search, and
        under both v-ranges.  Most likely the section 7 sentence is a loose
        summary (it says "it seems to be true") and 17 is simply the threshold
        he used, not the smallest that works -- but that is an inference, not a
        check.  Resolve against the author's implementation [17] before relying
        on any claim about the exact exception set.

WHY THIS MATTERS.  Rosenfeld (section 7): "There might even be a good provable
reason for which Lemma 6 holds for all k, for any large enough integer p.  That
could lead to a proof of the lonely runner conjecture."  Proving that would make
k = 7 computer-free and therefore mechanisable in Lean, and would attack all k.
This script is the falsification test for any candidate mechanism: it must
predict the k=6 pattern (13, 19 yes; 17, 23, 29 no) and the k=3 threshold.

Usage:  from lemma7_criterion_v1 import bad_cover_exists
        bad_cover_exists(k, p)  ->  True if a bad cover exists (Lemma 7 FAILS)
"""
from itertools import combinations
from math import gcd
from functools import reduce

def bad_cover_exists(k, p, half_v=True, half_j=True):
    N=(k+1)*p
    J = list(range(1, N//2+1)) if half_j else list(range(1, N))
    V = [v for v in range(1, (N//2 if half_v else N-1)+1) if v % p != 0]
    idx={j:i for i,j in enumerate(J)}
    cov={}
    for v in V:
        m=0
        for j in J:
            r=(j*v)%N
            if r<p or r>N-p: m |= 1<<idx[j]
        cov[v]=m
    FULL=(1<<len(J))-1
    def gcd_ok(t): return all(reduce(gcd,S+(N,))==1 for S in combinations(t,k-1))
    # SOUND pruning: branch over ALL unused v covering the lowest uncovered target
    def rec(chosen, used, mask):
        if mask==FULL: return gcd_ok(tuple(chosen))
        if len(chosen)==k: return False
        low=(~mask)&FULL; lb=(low & -low).bit_length()-1
        for i,v in enumerate(V):
            if i in used: continue
            if (cov[v]>>lb)&1:
                if rec(chosen+[v], used|{i}, mask|cov[v]): return True
        return False
    return rec([],set(),0)
