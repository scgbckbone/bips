#!/usr/bin/env python3
"""Test-vector generator for the Anti-Exfil (sign-to-contract) BIP.

Self-contained pure-Python secp256k1 so the secret nonce k = (q + tweak) mod n
can be injected directly into both ECDSA and BIP-340 Schnorr signing — something
production libraries deliberately do not expose.

Every vector is verified internally:
  * the binding is reconstructed offline as R = Q + tweak*G and x(R) is checked
    against the published r / R_x, and
  * the resulting signature is checked with an independent verifier.

The four PSBTs in Vector 4 are serialized by hand using the first-class
per-input keytypes (0x21-0x26) defined by the BIP and have been confirmed to
parse with the `embit` library. The
BIP-143 (P2WPKH) and BIP-341 (P2TR key-path, SIGHASH_DEFAULT) sighashes are
computed per those specifications; both have since been cross-validated against
embit's independent sighash implementations (and the resulting signatures
against libsecp256k1 via coincurve) — they are not cross-validated against
Bitcoin Core in this script.

WARNING: this is a test-vector generator, not production code. The EC arithmetic
is pure Python and not constant-time; never use it with real keys.

No external dependencies. Run: python3 generate-test-vectors.py
"""
import hashlib, base64

# --------------------------------------------------------------------------
# secp256k1
# --------------------------------------------------------------------------
p  = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
n  = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141
Gx = 0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798
Gy = 0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8
G  = (Gx, Gy)

def inv(a, m=p): return pow(a, m - 2, m)
def padd(P, Q):
    if P is None: return Q
    if Q is None: return P
    x1, y1 = P; x2, y2 = Q
    if x1 == x2 and (y1 + y2) % p == 0: return None
    l = (3*x1*x1)*inv(2*y1) % p if P == Q else (y2-y1)*inv(x2-x1) % p
    x3 = (l*l - x1 - x2) % p
    return (x3, (l*(x1 - x3) - y1) % p)
def pmul(k, P=G):
    R = None; k %= n
    while k:
        if k & 1: R = padd(R, P)
        P = padd(P, P); k >>= 1
    return R
def x(P): return P[0]
def has_even_y(P): return P[1] % 2 == 0
def b32(i): return i.to_bytes(32, 'big')
def ser_comp(P): return (b'\x02' if has_even_y(P) else b'\x03') + b32(x(P))
def lift_x(xc):
    y2 = (pow(xc, 3, p) + 7) % p
    y = pow(y2, (p + 1)//4, p)
    if pow(y, 2, p) != y2: raise ValueError("not on curve")
    return (xc, y if y % 2 == 0 else p - y)

def sha256(b): return hashlib.sha256(b).digest()
def dsha(b): return sha256(sha256(b))
def tagged(tag, msg):
    t = sha256(tag.encode())
    return sha256(t + t + msg)

# --------------------------------------------------------------------------
# Anti-exfil construction
# --------------------------------------------------------------------------
# ECDSA wire format is byte-for-byte the deployed secp256k1-zkp `anti_exfil`
# (ecdsa_s2c module) construction: same tags, same RFC6979-with-extra-entropy
# nonce derivation, same tweak layout. The Schnorr tags mirror that naming
# scheme with "schnorr" in place of "ecdsa"; they are this BIP's own additions.
HOST_COMMITMENT_TAG        = "s2c/ecdsa/data"     # deployed; ECDSA inputs
SCHNORR_HOST_COMMITMENT_TAG = "s2c/schnorr/data"  # Schnorr inputs
ECDSA_TWEAK_TAG            = "s2c/ecdsa/point"    # deployed
SCHNORR_TWEAK_TAG          = "s2c/schnorr/point"

def hmac_sha256(key, msg):
    import hmac
    return hmac.new(key, msg, hashlib.sha256).digest()

def rfc6979_nonce(sk, digest, extra32):
    """libsecp256k1 nonce_function_rfc6979: HMAC-DRBG keyed with
    key32 || msg32 || extra32 (no bits2octets, no algo16). Candidate i is the
    i-th 32-byte DRBG output block; first valid scalar wins."""
    keydata = sk + digest + extra32
    V = b'\x01' * 32; K = b'\x00' * 32
    K = hmac_sha256(K, V + b'\x00' + keydata); V = hmac_sha256(K, V)
    K = hmac_sha256(K, V + b'\x01' + keydata); V = hmac_sha256(K, V)
    c = 0
    while True:
        if c > 0:   # re-key between generate calls (retry flag)
            K = hmac_sha256(K, V + b'\x00'); V = hmac_sha256(K, V)
        V = hmac_sha256(K, V)
        qi = int.from_bytes(V, 'big')
        if 1 <= qi < n: return qi, V, c
        c += 1

def ecdsa_verify(P, digest, r, s):
    z = int.from_bytes(digest, 'big')
    if not (1 <= r < n and 1 <= s < n): return False
    w = inv(s, n); u1 = z*w % n; u2 = r*w % n
    R = padd(pmul(u1), pmul(u2, P))
    return R is not None and x(R) % n == r

def der_sig(r, s):
    def enc(v):
        b = v.to_bytes((v.bit_length() + 7)//8 or 1, 'big')
        return (b'\x00' + b) if b[0] & 0x80 else b
    rb, sb = enc(r), enc(s)
    body = b'\x02' + bytes([len(rb)]) + rb + b'\x02' + bytes([len(sb)]) + sb
    return b'\x30' + bytes([len(body)]) + body

def ae_ecdsa(sk, digest, rho):
    d = int.from_bytes(sk, 'big'); z = int.from_bytes(digest, 'big')
    hc = tagged(HOST_COMMITMENT_TAG, rho)
    qi, qb, ctr = rfc6979_nonce(sk, digest, hc)
    Q = pmul(qi); Q33 = ser_comp(Q)
    tweak = tagged(ECDSA_TWEAK_TAG, Q33 + rho); ti = int.from_bytes(tweak, 'big') % n
    k = (qi + ti) % n
    assert k != 0, "degenerate zero nonce (abort per spec)"
    R = pmul(k); r = x(R) % n
    s = inv(k, n) * (z + r*d) % n
    if s > n//2: s = n - s                       # low-S
    assert r == x(padd(Q, pmul(ti))) % n, "ECDSA binding fail"
    assert ecdsa_verify(pmul(d), digest, r, s), "ECDSA verify fail"
    return dict(host_commitment=hc, q=qb, counter=ctr, Q33=Q33, tweak=tweak,
                k=b32(k), r=b32(r), s=b32(s), pub=ser_comp(pmul(d)), der=der_sig(r, s))

def bip340_verify(pk, m, sig):
    P = lift_x(int.from_bytes(pk, 'big'))
    r = int.from_bytes(sig[:32], 'big'); s = int.from_bytes(sig[32:], 'big')
    if r >= p or s >= n: return False
    e = int.from_bytes(tagged("BIP0340/challenge", sig[:32] + pk + m), 'big') % n
    R = padd(pmul(s), pmul(n - e, P))
    return R is not None and has_even_y(R) and x(R) == r

def ae_schnorr(sk, digest, rho):
    dprime = int.from_bytes(sk, 'big')
    d = dprime if has_even_y(pmul(dprime)) else n - dprime      # even-y signing scalar
    pk = b32(x(pmul(d)))
    hc = tagged(SCHNORR_HOST_COMMITMENT_TAG, rho)
    # BIP-340 nonce derivation with the host commitment as auxiliary data:
    # t = bytes(d) XOR tagged("BIP0340/aux", hc); q = tagged("BIP0340/nonce", t || pk || digest)
    t = bytes(a ^ b for a, b in zip(b32(d), tagged("BIP0340/aux", hc)))
    qb = tagged("BIP0340/nonce", t + pk + digest)
    qi = int.from_bytes(qb, 'big') % n
    assert qi != 0, "degenerate zero nonce (abort per spec)"
    ctr = 0                                                     # BIP-340 derivation has no counter
    if not has_even_y(pmul(qi)): qi = n - qi                    # force even-y Q
    Q32 = b32(x(pmul(qi)))
    tweak = tagged(SCHNORR_TWEAK_TAG, Q32 + rho); ti = int.from_bytes(tweak, 'big') % n
    k0 = (qi + ti) % n
    assert k0 != 0, "degenerate zero nonce (abort per spec)"
    R = pmul(k0)
    k = k0 if has_even_y(R) else n - k0                          # BIP-340 internal even-R
    r = x(R)
    e = int.from_bytes(tagged("BIP0340/challenge", b32(r) + pk + digest), 'big') % n
    s = (k + e*d) % n
    sig = b32(r) + b32(s)
    assert r == x(padd(lift_x(int.from_bytes(Q32, 'big')), pmul(ti))), "Schnorr binding fail"
    assert bip340_verify(pk, digest, sig), "BIP340 verify fail"
    return dict(host_commitment=hc, q=qb, counter=ctr, Q32=Q32, tweak=tweak,
                k=b32(k), sig=sig, pk=pk, d_evenY=b32(d), q_evenY=b32(qi))

hx = lambda b: b.hex()

# ==========================================================================
# Cross-check against libsecp256k1-zkp ecdsa_s2c official fixed vectors
# (src/modules/ecdsa_s2c/tests_impl.h): privkey 0x55*32, message 0x88*32.
# Proves the ECDSA nonce derivation is byte-compatible with the deployed
# anti_exfil module on both the s2c_sign and signer_commit paths.
# ==========================================================================
_ZKP_KEY, _ZKP_MSG = b'\x55'*32, b'\x88'*32
_ZKP = [
    # (s2c_data, expected s2c_sign opening, expected anti_exfil signer_commit opening)
    ("1bf6fb42f41eb876c4d7aa0d67242b00baab99dc2084493e4e63277fa1f77f22",
     "03f030def3188c0f56fcea87435b307643f45dafe22cbc82fd56034fae97417d3a",
     "02df63755d1f3292bffed82986b106497c93b1f8bdc0454b6b0b0a4779c0ef7188"),
    ("35199a8fbf84ad6ef69a184c1b19285befbe06e60b6264e6d373893f6855e24a",
     "03901717ce7c7484a2ce1b7dc7403b14e0354971393ec092a7f3e0c8e4e2d2639d",
     "02c04ac7f771e8ebdbf315ff5e58b7fe9516102103500066172c4fac5b20f9e0ea"),
]
for _d, _exp_s2c, _exp_exfil in _ZKP:
    _db = bytes.fromhex(_d)
    # s2c_sign path: extra entropy = tagged("s2c/ecdsa/data", s2c_data)
    _q = rfc6979_nonce(_ZKP_KEY, _ZKP_MSG, tagged(HOST_COMMITMENT_TAG, _db))[0]
    assert ser_comp(pmul(_q)).hex() == _exp_s2c, "zkp s2c_sign vector mismatch"
    # signer_commit path: extra entropy = host commitment passed directly
    _q = rfc6979_nonce(_ZKP_KEY, _ZKP_MSG, _db)[0]
    assert ser_comp(pmul(_q)).hex() == _exp_exfil, "zkp signer_commit vector mismatch"
print("libsecp256k1-zkp ecdsa_s2c fixed vectors: MATCH (wire-compatible)")

# ==========================================================================
# Vectors 1 & 2 — ECDSA
# ==========================================================================
rho    = bytes(range(0, 32))
sk     = bytes(range(1, 33))
digest = bytes(range(32, 64))

print("="*64); print("VECTORS 1 & 2 — ECDSA (opaque digest)"); print("="*64)
e = ae_ecdsa(sk, digest, rho)
for label, val in [("rho", rho), ("sk", sk), ("digest", digest),
                   ("signer pubkey (33)", e['pub']), ("host_commitment", e['host_commitment']),
                   ("q (counter=%d)" % e['counter'], e['q']), ("Q (33, compressed)", e['Q33']),
                   ("tweak", e['tweak']), ("k = (q+tweak) mod n", e['k']),
                   ("r", e['r']), ("s (low-S)", e['s']), ("DER signature", e['der'])]:
    print("%-22s %s" % (label, hx(val)))
EXP = ("d8dcbddb588f8bdf776acba632f4e3b6a93e175621aa39a627cb9e7193dc3c91",
       "2c91c078530d6e5c20e34bc08383e22fe2bd4983fa60f7052577aff11375287d",
       "03bb78cd652c9fcfc645237b296f206aba0155f05b3886c0374011d8ee655a4248")
print("self-check:",
      "PASS" if (hx(e['host_commitment']), hx(e['q']), hx(e['Q33'])) == EXP else "FAIL")

# ==========================================================================
# Vector 3 — Taproot / BIP-340 Schnorr
# ==========================================================================
print(); print("="*64); print("VECTOR 3 — Taproot / BIP-340 Schnorr (opaque digest)"); print("="*64)
s = ae_schnorr(sk, digest, rho)
for label, val in [("rho", rho), ("sk (signing scalar)", sk), ("d (even-y)", s['d_evenY']),
                   ("signer pubkey (x-only)", s['pk']), ("digest", digest),
                   ("host_commitment", s['host_commitment']),
                   ("q", s['q']), ("q (even-y adjusted)", s['q_evenY']),
                   ("Q (32, x-only)", s['Q32']), ("tweak", s['tweak']),
                   ("k (final nonce)", s['k']), ("BIP-340 sig (64)", s['sig'])]:
    print("%-22s %s" % (label, hx(val)))

# ==========================================================================
# Vector 4 — PSBT round-trips (P2WPKH ECDSA + P2TR key-path Schnorr)
# ==========================================================================
print(); print("="*64); print("VECTOR 4 — PSBT round-trips (first-class keytypes 0x21-0x26)"); print("="*64)

def cs(i):
    if i < 0xfd: return bytes([i])
    if i <= 0xffff: return b'\xfd' + i.to_bytes(2, 'little')
    if i <= 0xffffffff: return b'\xfe' + i.to_bytes(4, 'little')
    return b'\xff' + i.to_bytes(8, 'little')
def le(v, nb): return v.to_bytes(nb, 'little')
def vstr(b): return cs(len(b)) + b
def kv(key, val): return vstr(key) + vstr(val)

# keys / scripts
sk0 = bytes(range(1, 33))
pub0 = ser_comp(pmul(int.from_bytes(sk0, 'big')))
h160 = hashlib.new('ripemd160', sha256(pub0)).digest()
spk0 = b'\x00\x14' + h160

sk1 = bytes([0x22])*32
dint = int.from_bytes(sk1, 'big')
dint_e = dint if has_even_y(pmul(dint)) else n - dint
xint = b32(x(pmul(dint_e)))
tap_t = int.from_bytes(tagged("TapTweak", xint), 'big') % n
dout = (dint_e + tap_t) % n
xout = b32(x(pmul(dout)))
spk1 = b'\x51\x20' + xout
sk_sign1 = b32(dout)

# transaction skeleton
txid0 = bytes.fromhex("11"*32); txid1 = bytes.fromhex("22"*32)
op0 = txid0 + le(0, 4); op1 = txid1 + le(1, 4)
amt0, amt1 = 100000, 150000
seq = 0xffffffff
out_spk = b'\x00\x14' + bytes.fromhex("33"*20); out_val = 240000
txout = le(out_val, 8) + vstr(out_spk)
version, locktime = 2, 0

# BIP-143 sighash for input0 (P2WPKH)
scriptCode = b'\x19\x76\xa9\x14' + h160 + b'\x88\xac'
sighash0 = dsha(le(version, 4) + dsha(op0 + op1) + dsha(le(seq, 4) + le(seq, 4)) +
                op0 + scriptCode + le(amt0, 8) + le(seq, 4) + dsha(txout) +
                le(locktime, 4) + le(1, 4))

# BIP-341 sighash for input1 (P2TR key-path, SIGHASH_DEFAULT)
SigMsg = (b'\x00' + le(version, 4) + le(locktime, 4) +
          sha256(op0 + op1) + sha256(le(amt0, 8) + le(amt1, 8)) +
          sha256(vstr(spk0) + vstr(spk1)) + sha256(le(seq, 4) + le(seq, 4)) +
          sha256(txout) + b'\x00' + le(1, 4))
sighash1 = tagged("TapSighash", b'\x00' + SigMsg)

print("input0 BIP-143 sighash :", hx(sighash0))
print("input1 BIP-341 sighash :", hx(sighash1))

rho0 = bytes([0xAA])*32
rho1 = bytes([0xBB])*32
E = ae_ecdsa(sk0, sighash0, rho0)
S = ae_schnorr(sk_sign1, sighash1, rho1)

# First-class per-input keytypes assigned by the BIP:
#   ECDSA family (keydata = 33-byte compressed pubkey):  0x21 / 0x22 / 0x23
#   Taproot family (keydata = 32-byte x-only output key): 0x24 / 0x25 / 0x26
# field index: 1 = host_commitment, 2 = signer_commitment, 3 = host_entropy
def ae_key(idx, keydata, taproot):
    base = 0x24 if taproot else 0x21
    return bytes([base + idx - 1]) + keydata

def unsigned_tx():
    return (le(version, 4) + cs(2) + op0 + b'\x00' + le(seq, 4) +
            op1 + b'\x00' + le(seq, 4) + cs(1) + txout + le(locktime, 4))

def in0(stage, signed):
    m = kv(b'\x01', le(amt0, 8) + vstr(spk0))                 # WITNESS_UTXO
    if signed: m += kv(b'\x02' + pub0, E['der'] + b'\x01')    # PARTIAL_SIG
    m += kv(ae_key(1, pub0, False), E['host_commitment'])
    if stage >= 1: m += kv(ae_key(2, pub0, False), E['Q33'])
    if stage >= 2: m += kv(ae_key(3, pub0, False), rho0)
    return m + b'\x00'

def in1(stage, signed):
    m = kv(b'\x01', le(amt1, 8) + vstr(spk1))                 # WITNESS_UTXO
    if signed: m += kv(b'\x13', S['sig'])                     # TAP_KEY_SIG
    m += kv(ae_key(1, xout, True), S['host_commitment'])
    if stage >= 1: m += kv(ae_key(2, xout, True), S['Q32'])
    if stage >= 2: m += kv(ae_key(3, xout, True), rho1)
    return m + b'\x00'

def build(stage, signed=False):
    return (b'psbt\xff' + kv(b'\x00', unsigned_tx()) + b'\x00' +
            in0(stage, signed) + in1(stage, signed) + b'\x00')   # one (empty) output map

for name, blob in [("ROUND-1 host->signer        ", build(0)),
                   ("ROUND-1 signer reply (no sig)", build(1)),
                   ("ROUND-2 host->signer        ", build(2)),
                   ("ROUND-2 signed result       ", build(2, signed=True))]:
    print("\n%s (%d bytes)\n%s" % (name, len(blob), base64.b64encode(blob).decode()))
