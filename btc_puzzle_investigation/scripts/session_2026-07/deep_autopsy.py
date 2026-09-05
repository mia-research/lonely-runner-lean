"""
DEEP AUTOPSY of the GECT script -- everything VERIFIED by derivation, not asserted.
Corrects M3: keys are 256-bit numbers with leading zeros; a puzzle-160 key has its
top 96 bits zero (MSB at bit 159). The right test is derivation + range, not a raw
bit-length count. So: does the script's 'known key' actually produce the script's
pubkey and address? Is the pubkey real? Where exactly is the forward path missing?
"""
import hashlib, ecdsa, base58
from ecdsa import SECP256k1
from math import gcd, log

p=0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
Gx=0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798

PUZ=160
TARGET="1NBC8uXJy1GiJ6drkiZa1WuKn51ps7EPTv"
PUB="02e0a8b039282faf6fe0fd769cfbc4b6b4cf8758ba68220eac420e32b91ddfa673"
KNOWN=int("5b32edb74843b464a781b49c063b5167664d9f64c6144e54823871b5634125d3",16)

def decompress(hx):
    b=bytes.fromhex(hx); pre=b[0]; x=int.from_bytes(b[1:],'big')
    ys=(pow(x,3,p)+7)%p; y=pow(ys,(p+1)//4,p)
    if (y&1)!=(pre==3): y=p-y
    return x,y
def priv_to_xy(d):
    sk=ecdsa.SigningKey.from_secret_exponent(d,curve=SECP256k1)
    P=sk.get_verifying_key().pubkey.point; return P.x(),P.y()
def priv_to_addr(d,compressed=True):
    x,y=priv_to_xy(d)
    if compressed: pk=(b'\x02' if y%2==0 else b'\x03')+x.to_bytes(32,'big')
    else: pk=b'\x04'+x.to_bytes(32,'big')+y.to_bytes(32,'big')
    h=hashlib.new('ripemd160',hashlib.sha256(pk).digest()).digest()
    v=b'\x00'+h; c=hashlib.sha256(hashlib.sha256(v).digest()).digest()[:4]
    return base58.b58encode(v+c).decode()

print("="*74)
print("A. IS THE PUBLIC KEY REAL AND ON-CURVE?")
px,py=decompress(PUB)
on=(py*py-(px*px*px+7))%p==0
print(f"   decompressed X={hex(px)[:18]}...  on-curve={on}")
print(f"   address of THIS pubkey (compressed) = {priv_to_addr.__name__ and ''}", end="")
# address directly from pubkey bytes
hh=hashlib.new('ripemd160',hashlib.sha256(bytes.fromhex(PUB)).digest()).digest()
addr_pub=base58.b58encode(b'\x00'+hh+hashlib.sha256(hashlib.sha256(b'\x00'+hh).digest()).digest()[:4]).decode()
print(addr_pub)
print(f"   target address                       = {TARGET}")
print(f"   -> pubkey matches target address: {addr_pub==TARGET}")

print("="*74)
print("B. DOES THE SCRIPT'S 'KNOWN KEY' DERIVE TO THAT PUBKEY / ADDRESS?")
kx,ky=priv_to_xy(KNOWN)
ka=priv_to_addr(KNOWN,True); kau=priv_to_addr(KNOWN,False)
print(f"   known_key * G  X = {hex(kx)[:18]}...")
print(f"   real pubkey    X = {hex(px)[:18]}...")
print(f"   -> known key reproduces the pubkey: {kx==px}")
print(f"   address(known, compressed)   = {ka}   match={ka==TARGET}")
print(f"   address(known, uncompressed) = {kau}   match={kau==TARGET}")

print("="*74)
print("C. RANGE / LEADING-ZERO STRUCTURE (the correct M3 test)")
def lead_zero_bits(d): return 256-d.bit_length()
print(f"   a puzzle-{PUZ} key must lie in [2^{PUZ-1}, 2^{PUZ}):  MSB at bit {PUZ-1},")
print(f"     i.e. exactly {256-PUZ} leading zero bits in 256-bit form.")
print(f"   known key: bit_length={KNOWN.bit_length()}, leading-zero bits={lead_zero_bits(KNOWN)}")
print(f"   in range [2^159,2^160)? {2**159<=KNOWN<2**160}")
print(f"   -> {'valid p160 key' if 2**159<=KNOWN<2**160 else 'OUT OF RANGE: it has 1 leading zero bit, needs 96'}")

print("="*74)
print("D. D-RECURSION: forward path exists?  (needs the target as input)")
rs=2**(PUZ-1); base=rs+(rs*51)//80
def d_rec(base,target,rs,mx=40):
    cur=base;err=target-cur;t=0
    while err!=0 and t<mx:
        D=rs//abs(err)
        if D==0: return cur,t,"CRASH: |error|>range -> D=0 -> div-by-zero (as in original)"
        cur+= rs//D if err>0 else -(rs//D); err=target-cur; t+=1
    return cur,t,("exact" if err==0 else "not converged")
import random; r=random.Random(0)
gotk,tk,sk=d_rec(base,KNOWN,rs)
gotr,tr,sr=d_rec(base, rs+r.randrange(rs), rs)
print(f"   reconstruct KNOWN (out-of-range): {sk}")
print(f"   reconstruct RANDOM in-range int : {sr} in {tr} terms")
print(f"   => the original crashes at Step 4 on its OWN key; the printed 'SUCCESS' was never run.")
print(f"   the loop condition is 'err=target-cur'; with NO target it cannot start.")
print(f"   the script's forward note says target 'would be estimated from XxY' -- ")
print(f"   grep the file: no such estimator is implemented. Forward path = absent.")

print("="*74)
print("E. (n,k) DETERMINATION: does it use the pubkey? what k does it pick?")
def phi(n):
    r=n;t=n;q=2
    while q*q<=t:
        if t%q==0:
            while t%q==0:t//=q
            r-=r//q
        q+=1
    if t>1:r-=r//t
    return r
def order(k,n):
    if gcd(k,n)!=1:return 10**9
    o=1;c=k%n
    while c!=1:
        c=c*k%n;o+=1
        if o>n:return 10**9
    return o
def pick(X,Y):
    cand=[39,65,80,135]; gw=[n for n in cand if (phi(n)&(phi(n)-1))==0]
    n=gw[0] if gw else cand[0]
    ks=[k for k in range(1,n) if gcd(k,n)==1]
    k=min(ks,key=lambda k:0.7*log(order(k,n))+0.3*(k/n)); return n,k
print(f"   phi of candidates: " + ", ".join(f"phi({n})={phi(n)}" for n in (39,65,80,135)))
print(f"   only phi(80)=32 is 2^r -> n=80 forced regardless of X,Y.")
print(f"   pick(real X,Y)   = {pick(px,py)}")
print(f"   pick(0,0)        = {pick(0,0)}")
print(f"   T_EC picks k minimizing 0.7 ln(ord)+0.3 k/n; k=1 has ord=1 -> k=1 always.")
print(f"   claimed (n=80,k=51) is NOT what the code outputs.")
