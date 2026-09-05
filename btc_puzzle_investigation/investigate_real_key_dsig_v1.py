#!/usr/bin/env python3
"""
Pure investigation: what does the D-recursion actually DO on real solved keys?
No leakage test. Show full step-by-step traces, term counts, magnitudes, and try a
few 'error' definitions so we can see which structure matches the intended model.
"""
import csv, random
rnd=random.Random(1)

def d_recursion(N, error, trace=False):
    sig=[]; e=abs(error); steps=[]
    while e>0:
        D=N//e
        if D==0: break
        c=N//D; ne=abs(e-c)
        steps.append((D, e, c, ne))
        sig.append(D); e=ne
    if trace: return sig, steps
    return sig

rows=[(int(r["bits"]), int(r["private_key"],16)) for r in csv.DictReader(open("puzzles_verified.csv"))]
rows=[(P,d) for P,d in rows if P>=8]

# ---- Part 1: full step-by-step traces on a few real keys ----
print("="*70)
print("PART 1 — full recursion trace on real keys (error = full private key, N=2^P)")
for P,d in [r for r in rows if r[0] in (16,24,40,64)][:4]:
    N=1<<P; sig,steps=d_recursion(N,d,trace=True)
    print(f"\n  puzzle P={P}, d={d}  ->  {len(sig)} terms")
    for i,(D,e,c,ne) in enumerate(steps):
        print(f"    step {i}: D={D:<22d} e={e}  corr={c}  ->  e'={ne}")

# ---- Part 2: try 3 error definitions, compare term counts ----
print("\n"+"="*70)
print("PART 2 — term counts under 3 'error' definitions (all real keys):")
defs={
  "full key   N=2^P":       lambda P,d:(1<<P, d),
  "offset-bottom N=2^(P-1)": lambda P,d:(1<<(P-1), d-(1<<(P-1))),
  "offset-top  N=2^(P-1)":   lambda P,d:(1<<(P-1), (1<<P)-d),
}
for name,f in defs.items():
    cnts=[]
    for P,d in rows:
        N,e=f(P,d)
        if e>0: cnts.append(len(d_recursion(N,e)))
    import statistics as st
    print(f"  {name:26s}: mean {st.mean(cnts):.2f}  min {min(cnts)} max {max(cnts)}  n={len(cnts)}")

# ---- Part 3: real vs random term count, by bit-length band ----
print("\n"+"="*70)
print("PART 3 — real vs random term count (full key N=2^P), by bit band:")
def band(P): return (P//32)*32
from collections import defaultdict
real_b=defaultdict(list); rand_b=defaultdict(list)
for P,d in rows:
    real_b[band(P)].append(len(d_recursion(1<<P,d)))
    for _ in range(20):
        rd=(1<<(P-1))+rnd.randrange(1<<(P-1)); rand_b[band(P)].append(len(d_recursion(1<<P,rd)))
import statistics as st
for b in sorted(real_b):
    r=real_b[b]; a=rand_b[b]
    print(f"  P~{b:>3}-{b+31}: real mean={st.mean(r):.2f} (n={len(r)})   random mean={st.mean(a):.2f}")

# ---- Part 4: reconstruction check + magnitude pattern ----
print("\n"+"="*70)
print("PART 4 — reconstruction + magnitude pattern (full key):")
def reconstruct(N,D):
    Dl=D[-1]; poss=list(range(N//(Dl+1)+1, N//Dl+1))
    for d in reversed(D[:-1]):
        c=N//d; nn=[]
        for e in poss:
            for s in (1,-1):
                x=c+s*e
                if x>0 and N//x==d: nn.append(x)
        poss=sorted(set(nn))
        if not poss: return None
    return poss
okc=0
for P,d in rows[:20]:
    N=1<<P; sig=d_recursion(N,d); rec=reconstruct(N,sig)
    if rec and d in rec: okc+=1
print(f"  reconstruction exact on {okc}/20 sampled real keys")
P,d=[r for r in rows if r[0]>=60][0]
sig=d_recursion(1<<P,d)
print(f"  example P={P}: D-term bit-lengths = {[max(x.bit_length()-1,0) for x in sig]}")
