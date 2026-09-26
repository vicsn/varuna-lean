#!/usr/bin/env python3
"""Generate Varuna/Fingerprint/Capture.lean from a captured snarkVM V2 proof.

The capture (fixtures/fingerprint/v2_lc_capture.json) is produced by the
test-only instrumentation in fixtures/fingerprint/capture.patch; see
fixtures/fingerprint/PROVENANCE.md. This script only transcribes the decimal
field elements into Lean literals; it computes nothing.

Usage: scripts/fingerprint_to_lean.py [capture.json] [out.lean]
then run `lean-fmt` on the output.
"""
from __future__ import annotations

import hashlib
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
SRC = ROOT / "fixtures/fingerprint/v2_lc_capture.json"
OUT = ROOT / "Varuna/Fingerprint/Capture.lean"


def lean_name(key: str) -> str:
    """`row_col_val_a@gamma` -> `rowColValAAtGamma`, `inv_C` -> `invC`."""
    base, _, point = key.partition("@")
    parts = base.split("_")
    name = parts[0] + "".join(p[:1].upper() + p[1:] for p in parts[1:])
    if point:
        name += "At" + point[:1].upper() + point[1:]
    return name


def lc_name(label: str) -> str:
    return {"rowcheck_zerocheck": "rowcheckTerms", "lineval_sumcheck": "linevalTerms",
            "matrix_sumcheck": "matrixTerms"}[label]


def main() -> None:
    src = Path(sys.argv[1]) if len(sys.argv) > 1 else SRC
    out = Path(sys.argv[2]) if len(sys.argv) > 2 else OUT
    raw = src.read_bytes()
    d = json.loads(raw)
    sha = hashlib.sha256(raw).hexdigest()
    lines = [
        "/-",
        "Copyright (c) 2026 Provable Inc.",
        "Licensed under the Apache License, Version 2.0; see LICENSE.md for details.",
        "-/",
        "",
        "import Mathlib.Data.ZMod.Basic",
        "",
        "/-!",
        "# Captured V2 proof (generated; do not edit)",
        "",
        "Field elements of one honest snarkVM `VarunaVersion::V2` proof in hiding",
        "mode, transcribed by `scripts/fingerprint_to_lean.py` from",
        f"`fixtures/fingerprint/v2_lc_capture.json` (SHA-256 `{sha}`).",
        "Provenance and regeneration: `fixtures/fingerprint/PROVENANCE.md`.",
        "-/",
        "",
        "namespace Varuna.Fingerprint",
        "",
        "/-- BLS12-377 scalar field modulus. -/",
        f"abbrev q : ℕ := {d['modulus']}",
        "",
        "/-- The scalar field of the captured proof. -/",
        "abbrev Fr := ZMod q",
        "",
    ]
    for k, v in d["sizes"].items():
        lines += [f"/-- Captured domain size `|{k}|`. -/", f"def size{k} : ℕ := {v}", ""]
    for k, v in d["scalars"].items():
        lines += [f"/-- Captured `{k}`. -/", f"def {lean_name(k)} : Fr := {v}", ""]
    for lc in d["lcs"]:
        lines.append(f"/-- Captured `{lc['label']}` terms `(label, coefficient, value)`. -/")
        lines.append(f"def {lc_name(lc['label'])} : List (String × Fr × Fr) := [")
        body = [f"  (\"{t['term']}\", {t['coeff']}, {t['value']})" for t in lc["terms"]]
        lines.append(",\n".join(body))
        lines += ["]", ""]
    lines += ["end Varuna.Fingerprint", ""]
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text("\n".join(lines))
    print(f"wrote {out} from {src} (sha256 {sha})")


if __name__ == "__main__":
    main()
