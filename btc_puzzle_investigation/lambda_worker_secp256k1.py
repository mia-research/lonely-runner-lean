"""
lambda_worker_secp256k1.py  —  deployable AWS Lambda that IS a key-scan worker for
puzzle135_bruteforce_toy.py. Self-contained (stdlib only). Deploy as the function's
handler `lambda_handler`, enable a Function URL, then point the toy at it:

    python3 puzzle135_bruteforce_toy.py --backend lambda --url https://<id>.lambda-url.<region>.on.aws/

Contract (must match the toy exactly):
    request  JSON: {"start":"0x<hex>", "count":<int>, "target":"02..<compressed pubkey>"}
    response JSON: {"checked":<int>, "found":<bool>, "key":"0x<hex>"|null}   (wrapped in statusCode/body)
"""
import json

P  = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
Gx = 0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798
Gy = 0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8
G  = (Gx, Gy)

def _inv(x): return pow(x % P, P - 2, P)

def _add(A, B):
    if A is None: return B
    if B is None: return A
    x1, y1 = A; x2, y2 = B
    if x1 == x2 and (y1 + y2) % P == 0: return None
    m = (3 * x1 * x1) * _inv(2 * y1) % P if A == B else (y2 - y1) * _inv(x2 - x1) % P
    x3 = (m * m - x1 - x2) % P
    return (x3, (m * (x1 - x3) - y1) % P)

def _mul(k):
    R = None; A = G
    while k:
        if k & 1: R = _add(R, A)
        A = _add(A, A); k >>= 1
    return R

def scan_chunk(start, count, target):
    tx = int(target[2:], 16); tpar = int(target[:2], 16) & 1
    for i in range(count):
        Pt = _mul(start + i)                     # full d*G per key, no shortcut
        if Pt[0] == tx and (Pt[1] & 1) == tpar:
            return {"checked": i + 1, "found": True, "key": hex(start + i)}
    return {"checked": count, "found": False, "key": None}

def lambda_handler(event, context=None):
    try:
        body = event.get("body", event) if isinstance(event, dict) else event
        if isinstance(body, str): body = json.loads(body)
        res = scan_chunk(int(body["start"], 16), int(body["count"]), body["target"])
        return {"statusCode": 200, "body": json.dumps(res)}
    except Exception as e:
        return {"statusCode": 500, "body": json.dumps({"error": str(e)})}
