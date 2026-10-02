#!/usr/bin/env python3
"""Generate Varuna/Fingerprint/Capture.lean from a captured snarkVM V3 proof.

The capture (fixtures/fingerprint/v3_lc_capture.json) is produced by the
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
SRC = ROOT / "fixtures/fingerprint/v3_lc_capture.json"
OUT = ROOT / "Varuna/Fingerprint/Capture.lean"

# What the less self-explanatory capture keys are.
DOC = {
    "combiner_1": "First-round batch combiner (`rowcheck_zerocheck`); `1` when first.",
    "combiner_3": "Third-round batch combiner (`lineval_sumcheck`); `1` when first.",
    "sigma_a": "Prepare-third sum `σ_A`.",
    "sigma_b": "Prepare-third sum `σ_B`.",
    "sigma_c": "Prepare-third sum `σ_C`.",
    "sum4_a": "Fourth-round sum `σ^K_A`.",
    "sum4_b": "Fourth-round sum `σ^K_B`.",
    "sum4_c": "Fourth-round sum `σ^K_C`.",
    "x_at_beta": "`x̂(β)` from the formatted public input.",
    "inv_C": "Inverse witness `|C|^{-1}`.",
    "inv_selden_R": "Inverse witness `(v_{R_i}(α) |R|)^{-1}`.",
    "inv_selden_C": "Inverse witness `(v_{C_i}(β) |C|)^{-1}`.",
    "inv_selden_KA": "Inverse witness `(v_{K_A}(γ) |K|)^{-1}`.",
    "inv_selden_KB": "Inverse witness `(v_{K_B}(γ) |K|)^{-1}`.",
    "inv_selden_KC": "Inverse witness `(v_{K_C}(γ) |K|)^{-1}`.",
}


def lean_name(key: str) -> str:
    """`row_col_val_a@gamma` -> `rowColValAAtGamma`, `inv_C` -> `invC`."""
    base, _, point = key.partition("@")
    parts = base.split("_")
    name = parts[0] + "".join(p[:1].upper() + p[1:] for p in parts[1:])
    if point:
        name += "At" + point[:1].upper() + point[1:]
    return name


def doc(key: str) -> str:
    return DOC.get(key, f"Captured `{key}`.")


def lc_name(label: str) -> str:
    return {"rowcheck_zerocheck": "rowcheckTerms", "lineval_sumcheck": "linevalTerms",
            "matrix_sumcheck": "matrixTerms"}[label]


def main() -> None:
    src = Path(sys.argv[1]) if len(sys.argv) > 1 else SRC
    out = Path(sys.argv[2]) if len(sys.argv) > 2 else OUT
    raw = src.read_bytes()
    d = json.loads(raw)
    sha = hashlib.sha256(raw).hexdigest()
    circuits = d["circuits"]
    shape = ", ".join(f"`{c['label']}` with {len(c['instances'])} instances" for c in circuits)
    lines = [
        "/-",
        "Copyright (c) 2026 Provable Inc.",
        "Licensed under the Apache License, Version 2.0; see LICENSE.md for details.",
        "-/",
        "",
        "import Mathlib.Data.ZMod.Basic",
        "",
        "/-!",
        "# Captured V3 proof (generated; do not edit)",
        "",
        "Field elements of one honest snarkVM `VarunaVersion::V3` batch proof in",
        f"hiding mode over {len(circuits)} circuits ({shape}).",
        "Transcribed by `scripts/fingerprint_to_lean.py` from",
        f"`fixtures/fingerprint/v3_lc_capture.json` (SHA-256 `{sha}`).",
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
        lines += [f"/-- Captured batch domain size `|{k}|` (the largest circuit's). -/",
                  f"def size{k} : ℕ := {v}", ""]
    for k, v in d["scalars"].items():
        lines += [f"/-- {doc(k)} -/", f"def {lean_name(k)} : Fr := {v}", ""]

    inst_keys = list(circuits[0]["instances"][0])
    lines += ["/-- One instance of a captured circuit. -/", "structure CapturedInstance where"]
    for k in inst_keys:
        lines += [f"  /-- {doc(k)} -/", f"  {lean_name(k)} : Fr"]
    lines.append("")
    size_keys, scalar_keys = list(circuits[0]["sizes"]), list(circuits[0]["scalars"])
    lines += ["/-- One captured circuit: its domain sizes, its per-circuit scalars, and its",
              "instances. -/", "structure CapturedCircuit where"]
    for k in size_keys:
        lines += [f"  /-- Domain size `|{k}|` of this circuit. -/", f"  size{k} : ℕ"]
    for k in scalar_keys:
        lines += [f"  /-- {doc(k)} -/", f"  {lean_name(k)} : Fr"]
    lines += ["  /-- The circuit's instances, in proof order. -/",
              "  instances : List CapturedInstance", ""]

    for c in circuits:
        label = c["label"]
        assert list(c["sizes"]) == size_keys and list(c["scalars"]) == scalar_keys
        names = []
        for j, inst in enumerate(c["instances"]):
            assert list(inst) == inst_keys
            name = f"{label}i{j}"
            names.append(name)
            lines += [f"/-- Captured instance {j} of circuit `{label}`. -/",
                      f"def {name} : CapturedInstance where"]
            lines += [f"  {lean_name(k)} := {v}" for k, v in inst.items()]
            lines.append("")
        lines += [f"/-- Captured circuit `{label}` (snarkVM id `{c['id']}`). -/",
                  f"def {label} : CapturedCircuit where"]
        lines += [f"  size{k} := {v}" for k, v in c["sizes"].items()]
        lines += [f"  {lean_name(k)} := {v}" for k, v in c["scalars"].items()]
        lines += [f"  instances := [{', '.join(names)}]", ""]
    lines += ["/-- The captured circuits, in `CircuitId` order. -/",
              f"def circuits : List CapturedCircuit := [{', '.join(c['label'] for c in circuits)}]", ""]

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
