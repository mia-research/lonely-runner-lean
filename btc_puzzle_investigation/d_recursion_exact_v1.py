#!/usr/bin/env python3
"""
The USER'S EXACT D-recursion (source), validated against their Findings, then
applied to real keys to see what signatures actual keys produce.
"""
import csv

def d_recursion(N, error):
    signature = []
    e = abs(error)
    while e > 0:
        D = N // e
        if D == 0: break
        signature.append(D)
        correction = N // D
        e = abs(e - correction)
    return signature

def reconstruct_error(N, D_terms):
    D_last = D_terms[-1]
    e_min = N // (D_last + 1) + 1
    e_max = N // D_last
    possible = list(range(e_min, e_max + 1))
    for D in reversed(D_terms[:-1]):
        correction = N // D
        new_possible = []
        for e_next in possible:
            for sign in (+1, -1):
                e_cand = correction + sign * e_next
                if e_cand > 0 and N // e_cand == D:
                    new_possible.append(e_cand)
        possible = sorted(set(new_possible))
        if not possible: return None
    return possible

# ---- validate against Finding B ----
print("VALIDATE Finding B (error = N//3 + N//7):")
for P in (20,40,80,160,256):
    N=1<<P; err=N//3+N//7; sig=d_recursion(N,err)
    print(f"  {P:>3}-bit: steps={len(sig)}  sig={sig if P<=40 else sig[:3]+['...2^%d'%sig[-1].bit_length()] if len(sig)>3 else sig}")
# ---- validate Finding C ----
print("\nVALIDATE Finding C (error = N//3 + N//7 + N//13 + 2^(P/8)):")
for P in (40,80,160,256):
    N=1<<P; err=N//3+N//7+N//13+2**(P//8); sig=d_recursion(N,err)
    print(f"  {P:>3}-bit: steps={len(sig)}  D-term bitlens={[round(d.bit_length()-1,1) if d>1 else 0.0 for d in sig]}")

# ---- apply to REAL solved keys: what signature does an actual key give? ----
print("\nREAL solved keys — d_recursion on the private key and on the band-offset:")
rows=[r for r in csv.DictReader(open("puzzles_verified.csv")) if int(r["bits"])>=40]
for r in rows[:6]+rows[-4:]:
    P=int(r["bits"]); d=int(r["private_key"],16); N=1<<P
    sig_full=d_recursion(N,d)
    off=d-(1<<(P-1)); sig_off=d_recursion(N,off) if off>0 else []
    print(f"  puzzle {r['puzzle']:>3} ({P}b): full-key steps={len(sig_full)}  band-offset steps={len(sig_off)}")

# ---- how many terms for RANDOM keys vs structured? ----
import random; rnd=random.Random(1)
print("\nRANDOM keys vs STRUCTURED (sum-of-fractions) — step counts at each bit size:")
for P in (80,160,256):
    N=1<<P
    rand_steps=[len(d_recursion(N,(1<<(P-1))+rnd.randrange(1<<(P-1)))) for _ in range(200)]
    struct=len(d_recursion(N,N//3+N//7+N//13+2**(P//8)))
    print(f"  {P:>3}-bit: random mean steps={sum(rand_steps)/len(rand_steps):.1f} "
          f"(range {min(rand_steps)}-{max(rand_steps)})   structured(3 fracs)={struct}")
