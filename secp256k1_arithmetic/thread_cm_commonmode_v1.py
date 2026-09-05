#!/usr/bin/env python3
"""
Verify Finding 3 of vertical_zfr_replication.md (2026-07-11): "the CM/Eisenstein
(mu_6) common mode is rank-3, vs Dirichlet rank-1, ratio 3 = |mu6|/|mu2|."

Suspected flaw: it counts eigenvalues above the iid Marchenko-Pastur edge
(1+sqrt(gamma))^2.  But character values are NOT iid Gaussian, and the more-rigid
sextic (mu_6) characters are LESS iid than quadratic -- so more of them poke above
the *iid* edge for a null reason.  The correct test compares real top eigenvalues
to a MATCHED SHUFFLE NULL (permute each character's values across primes, which
preserves the per-character marginal but destroys cross-character correlation).

Construction (faithful to the finding's spirit):
  moduli q prime (q==1 mod 6 so order-6 chars exist); samples = primes p coprime to
  all q; feature per character chi = (chi(p))_p standardized.
  QUAD family = the quadratic characters (order 2, the '±1' Dirichlet analogue).
  SEXTIC family = the order-6 characters (the 'mu_6 / CM' analogue).
  K = char-correlation; eigenvalues; count above (a) iid MP edge, (b) matched
  shuffle-null top eigenvalues (mean + 3 sigma over 200 shuffles).
"""
import numpy as np, math
rng=np.random.default_rng(11)

def sieve(L):
    bs=bytearray([1])*(L+1); bs[0:2]=b'\x00\x00'
    for i in range(2,int(L**.5)+1):
        if bs[i]: bs[i*i::i]=bytearray(len(bs[i*i::i]))
    return [i for i in range(L+1) if bs[i]]
P=sieve(200000)
def prim_root(q):
    f=set(); m=q-1; d=2
    while d*d<=m:
        while m%d==0: f.add(d); m//=d
        d+=1
    if m>1: f.add(m)
    for g in range(2,q):
        if all(pow(g,(q-1)//x,q)!=1 for x in f): return g

def char_matrix(order):
    """rows = primes p, cols = characters of the chosen ORDER across several moduli."""
    qs=[q for q in P if 40<q<160 and (q-1)%6==0][:8]      # moduli q==1 mod 6
    samp=[p for p in P if 200<p<200+2000]                  # ~ many sample primes
    samp=samp[:400]
    cols=[]
    for q in qs:
        g=prim_root(q); ind={}; cur=1
        for e in range(q-1): ind[cur%q]=e; cur=cur*g%q
        # characters of exact order `order`: chi_k with k*order == 0 mod (q-1),
        # gcd(k,(q-1)) = (q-1)/order.  Enumerate primitive ones of that order.
        base=(q-1)//order
        for k in range(1,order):
            if math.gcd(k,order)!=1: continue
            kk=k*base
            col=[]
            for p in samp:
                if p%q==0: col.append(0.0+0.0j)
                else: col.append(np.exp(2j*np.pi*kk*ind[p%q]/(q-1)))
            cols.append(col)
    M=np.array(cols).T                                      # (#primes) x (#chars)
    # standardize each character column: subtract mean, unit norm
    M=M-M.mean(0,keepdims=True)
    nrm=np.linalg.norm(M,axis=0,keepdims=True); nrm[nrm==0]=1
    return M/nrm

def spectrum(M):
    n,d=M.shape
    K=(M.conj().T@M).real                                   # d x d char-correlation
    ev=np.sort(np.linalg.eigvalsh(K))[::-1]
    gamma=d/n; edge=(1+math.sqrt(gamma))**2
    return ev, edge, n, d

def shuffle_null_top(M, k=4, reps=200):
    n,d=M.shape
    tops=np.zeros((reps,k))
    for r in range(reps):
        Ms=np.empty_like(M)
        for j in range(d): Ms[:,j]=M[rng.permutation(n),j]
        Ms=Ms-Ms.mean(0,keepdims=True)
        nrm=np.linalg.norm(Ms,axis=0,keepdims=True); nrm[nrm==0]=1; Ms/=nrm
        ev=np.sort(np.linalg.eigvalsh((Ms.conj().T@Ms).real))[::-1]
        tops[r]=ev[:k]
    return tops.mean(0), tops.std(0)

print(f"{'family':>8} {'d':>3} {'n':>4} {'MPedge':>7} | top-4 eigenvalues | "
      f"#>MPedge | #>null(mean+3σ)")
for name,order in (("QUAD",2),("SEXTIC",6)):
    M=char_matrix(order)
    ev,edge,n,d=spectrum(M)
    nmean,nstd=shuffle_null_top(M,k=4)
    above_mp=int((ev[:6]>edge).sum())
    thr=nmean+3*nstd
    above_null=int(sum(1 for i in range(4) if ev[i]>thr[i]))
    print(f"{name:>8} {d:>3} {n:>4} {edge:>7.3f} | "
          f"{'  '.join('%.3f'%x for x in ev[:4])} | {above_mp:>7} | {above_null:>3}"
          f"   (null top-4 = {'  '.join('%.3f'%x for x in nmean)})")

print("\nRead-out:")
print(" If SEXTIC shows '#>MPedge' = 3 but '#>null' = 0-1, then the 'rank-3' is the")
print(" iid-MP-edge being the WRONG null for rigid mu_6 characters -- the matched")
print(" shuffle null already sits at that level. Genuine common mode => #>null >= 1.")
