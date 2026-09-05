# Is the M4 statistic broken, or are the readouts simply not spectrally low-rank?
# Plant a GENUINE rank-2 sequence (DFT supported on 2 frequencies) and see if M4 sees it.
import numpy as np
n=1249
t=np.arange(n)
plant2 = np.cos(2*np.pi*7*t/n)+np.cos(2*np.pi*103*t/n)      # true spectral rank 2
plant1 = np.cos(2*np.pi*7*t/n)                               # true spectral rank 1
rng=np.random.default_rng(int(7)); rnd=rng.choice([-1.0,1.0],size=int(n))
def M4(s):
    V=np.fft.fft(s); return float((np.abs(V)**4).sum()/n)/float(n)**2
for nm,s in (("TRUE spectral rank 1",plant1),("TRUE spectral rank 2",plant2),
             ("random +-1",rnd)):
    print("   %-22s  M4/n^2 = %12.2f" % (nm, M4(s)))
print()
print("   n = %d ; a true low-rank object should read ~O(n), not ~2." % n)
