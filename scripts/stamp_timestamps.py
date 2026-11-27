# SPDX-License-Identifier: Apache-2.0
# Copyright (c) 2026 Alexander Stephen Donahue
"""Cryptographically anchor & verify MANIFEST.sha256 via DigiCert RFC 3161 TSA and Bitcoin OpenTimestamps."""
from __future__ import annotations

import hashlib
import pathlib
import secrets
import shutil
import subprocess
import sys
import urllib.request

REPO = pathlib.Path(__file__).resolve().parent.parent
TS_DIR = REPO / "timestamps"
TS_DIR.mkdir(parents=True, exist_ok=True)
MANIFEST = REPO / "MANIFEST.sha256"

OTS_MAGIC = b"\x00OpenTimestamps\x00\x00Proof\x00\xbf\x89\xe2\xe8\x84\xe8\x92\x94"
OID_SHA256 = b"\x06\x09\x60\x86\x48\x01\x65\x03\x04\x02\x01"


def der_len(n: int) -> bytes:
    if n < 0x80:
        return bytes([n])
    b = n.to_bytes((n.bit_length() + 7) // 8, "big")
    return bytes([0x80 | len(b)]) + b


def der_seq(payload: bytes) -> bytes:
    return b"\x30" + der_len(len(payload)) + payload


def der_int(val: int) -> bytes:
    if val == 0:
        b = b"\x00"
    else:
        b = val.to_bytes((val.bit_length() + 8) // 8, "big")
    return b"\x02" + der_len(len(b)) + b


def build_rfc3161_tsq(digest_sha256: bytes) -> bytes:
    """Build a minimal valid DER-encoded RFC 3161 TimeStampReq for SHA-256 with certReq=TRUE."""
    alg_id = der_seq(OID_SHA256 + b"\x05\x00")
    msg_imprint = der_seq(alg_id + b"\x04" + der_len(len(digest_sha256)) + digest_sha256)
    nonce = secrets.randbits(63)
    version = der_int(1)
    cert_req = b"\x01\x01\xff"
    return der_seq(version + msg_imprint + der_int(nonce) + cert_req)


def stamp_rfc3161(digest: bytes) -> pathlib.Path:
    tsq = build_rfc3161_tsq(digest)
    tsq_path = TS_DIR / "MANIFEST.sha256.tsq"
    tsr_path = TS_DIR / "MANIFEST.sha256.tsr"
    tsq_path.write_bytes(tsq)
    req = urllib.request.Request(
        "http://timestamp.digicert.com",
        data=tsq,
        headers={"Content-Type": "application/timestamp-query"},
        method="POST",
    )
    with urllib.request.urlopen(req, timeout=30) as resp:
        tsr = resp.read()
    # RFC 3161 TimeStampResp starts with SEQUENCE (0x30) and embeds the exact 32-byte SHA-256 imprint
    if not tsr.startswith(b"\x30") or len(tsr) < 128 or digest not in tsr:
        raise RuntimeError(f"Unexpected RFC 3161 response ({len(tsr)} bytes)")
    tsr_path.write_bytes(tsr)
    print(f"[RFC3161] DigiCert TSA token saved: {tsr_path.name} ({len(tsr)} bytes)")
    return tsr_path


def write_varuint(n: int) -> bytes:
    out = bytearray()
    while True:
        b = n & 0x7F
        n >>= 7
        if n:
            out.append(b | 0x80)
        else:
            out.append(b)
            break
    return bytes(out)


def stamp_opentimestamps(digest: bytes) -> pathlib.Path:
    """Submit SHA-256 digest to 3 official OpenTimestamps calendars and write valid v1 .ots proof."""
    calendars = [
        "https://a.pool.opentimestamps.org/digest",
        "https://b.pool.opentimestamps.org/digest",
        "https://alice.btc.calendar.opentimestamps.org/digest",
    ]
    version = b"\x01"
    op_sha256 = b"\x08"

    nonce = secrets.token_bytes(16)
    leaf_digest = hashlib.sha256(digest + nonce).digest()
    op_append_nonce = b"\xf0" + write_varuint(len(nonce)) + nonce

    branches: list[bytes] = []
    for url in calendars:
        try:
            req = urllib.request.Request(
                url,
                data=leaf_digest,
                headers={
                    "Accept": "application/vnd.opentimestamps.v1",
                    "Content-Type": "application/x-www-form-urlencoded",
                    "User-Agent": "quantum-phasespace-rigidity-ots/2.0",
                },
                method="POST",
            )
            with urllib.request.urlopen(req, timeout=25) as resp:
                body = resp.read()
            if len(body) >= 16:
                branches.append(body)
                print(f"[OTS] Calendar {url} returned {len(body)} bytes")
        except Exception as exc:
            print(f"[OTS][WARN] Calendar {url} failed: {exc}")

    if not branches:
        raise RuntimeError("No OpenTimestamps calendar responded")

    payload = bytearray()
    payload.extend(OTS_MAGIC)
    payload.extend(version)
    payload.extend(op_sha256)
    payload.extend(digest)
    payload.extend(op_append_nonce)
    payload.extend(op_sha256)
    for i, br in enumerate(branches):
        if i < len(branches) - 1:
            payload.append(0xFF)
        payload.extend(br)

    ots_path = TS_DIR / "MANIFEST.sha256.ots"
    ots_path.write_bytes(bytes(payload))
    print(
        f"[OTS] Bitcoin OpenTimestamps proof saved: {ots_path.name} "
        f"({len(payload)} bytes, {len(branches)} calendars)"
    )
    return ots_path


def verify_timestamps() -> int:
    """Offline structural & cryptographic digest verification of RFC 3161 (.tsq/.tsr) & Bitcoin OTS (.ots)."""
    if not MANIFEST.exists():
        print(f"[FAIL] Missing {MANIFEST}", file=sys.stderr)
        return 1
    digest = hashlib.sha256(MANIFEST.read_bytes()).digest()
    tsq_path = TS_DIR / "MANIFEST.sha256.tsq"
    tsr_path = TS_DIR / "MANIFEST.sha256.tsr"
    ots_path = TS_DIR / "MANIFEST.sha256.ots"
    for p in (tsq_path, tsr_path, ots_path):
        if not p.exists():
            print(f"[FAIL] Missing timestamp artifact: {p.name}", file=sys.stderr)
            return 1

    tsq = tsq_path.read_bytes()
    tsr = tsr_path.read_bytes()
    ots = ots_path.read_bytes()

    if not tsq.startswith(b"\x30") or OID_SHA256 not in tsq or digest not in tsq:
        print("[FAIL] MANIFEST.sha256.tsq digest imprint mismatch", file=sys.stderr)
        return 1
    # RFC 3161 PKIStatusInfo GRANTED = SEQUENCE { INTEGER 0 } = 30 03 02 01 00
    if not tsr.startswith(b"\x30") or b"\x30\x03\x02\x01\x00" not in tsr[:32] or digest not in tsr:
        print("[FAIL] MANIFEST.sha256.tsr GRANTED status or digest imprint mismatch", file=sys.stderr)
        return 1
    # OpenTimestamps v1 header + SHA-256 op (0x08) + exact 32-byte digest
    expected_ots_prefix = OTS_MAGIC + b"\x01\x08" + digest
    if not ots.startswith(expected_ots_prefix):
        print("[FAIL] MANIFEST.sha256.ots magic/version/digest header mismatch", file=sys.stderr)
        return 1

    # If OpenSSL is available, parse & inspect the RFC 3161 TSTInfo text directly
    openssl = shutil.which("openssl")
    if openssl:
        res = subprocess.run(
            [openssl, "ts", "-reply", "-in", str(tsr_path), "-text"],
            capture_output=True,
            text=True,
        )
        if res.returncode != 0 or "Status: Granted" not in res.stdout or "sha256" not in res.stdout.lower():
            print(f"[FAIL] OpenSSL ts -reply validation failed:\n{res.stdout}\n{res.stderr}", file=sys.stderr)
            return 1
        print("[VERIFY][OpenSSL] RFC 3161 TimeStampResp parsed cleanly: Status=Granted, Hash=sha256")

    print(
        f"[VERIFY][PASS] MANIFEST.sha256 ({digest.hex()[:16]}...) matches "
        f"tsq ({len(tsq)}B), DigiCert tsr ({len(tsr)}B), and Bitcoin ots ({len(ots)}B)."
    )
    return 0


def main() -> int:
    if "--verify" in sys.argv:
        return verify_timestamps()
    if not MANIFEST.exists():
        raise FileNotFoundError(f"Missing {MANIFEST}; run scripts/generate_manifests.py first")
    digest = hashlib.sha256(MANIFEST.read_bytes()).digest()
    print(f"[STAMP] MANIFEST.sha256 SHA-256 = {digest.hex()}")
    stamp_rfc3161(digest)
    stamp_opentimestamps(digest)
    return verify_timestamps()


if __name__ == "__main__":
    raise SystemExit(main())
