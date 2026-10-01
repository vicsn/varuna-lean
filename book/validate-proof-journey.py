#!/usr/bin/env python3
"""Check that proof-map.html names real Lean declarations.

Every `proven` node's anchor, and every edge `via`, must name a declaration
in `Varuna/**/*.lean`. Anchors are split on `·`. A dotted name
`Varuna.Outer.inner` matches a declaration `inner` in a file that also
declares the namespace or structure `Outer`.
"""

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
HTML = ROOT / "book" / "src" / "formal-verification" / "proof-map.html"
LEAN = ROOT / "Varuna"

DECL = re.compile(
    r"\b(?:(?:private|noncomputable|protected|unsafe)\s+)*"
    r"(?:theorem|lemma|def|abbrev|structure|inductive)\s+"
    r"(?:[\w.]+\.)?(\w+)\b"
)
NS = re.compile(
    r"\b(?:namespace|structure|inductive|def|abbrev|theorem|lemma)\s+(\w+)\b"
)


def load_sources():
    files = []
    for path in LEAN.rglob("*.lean"):
        files.append((path, path.read_text()))
    return files


def has_decl(text, name):
    return any(match.group(1) == name for match in DECL.finditer(text))


def check_name(files, qual):
    parts = [part for part in qual.strip().split(".") if part]
    if parts and parts[0] == "Varuna":
        parts = parts[1:]
    if not parts:
        return False
    name, namespaces = parts[-1], parts[:-1]
    for _, text in files:
        if not has_decl(text, name):
            continue
        declared = set(NS.findall(text))
        if all(ns in declared or f"{ns}.{name}" in text for ns in namespaces):
            return True
    return False


def segments(text):
    return [part.strip() for part in text.split("·") if part.strip()]


def nodes(html):
    for chunk in re.split(r"(?=\{ id:)", html):
        if not chunk.startswith("{ id:"):
            continue
        ident = re.search(r"id:'([^']+)'", chunk)
        status = re.search(r"status:'([^']+)'", chunk)
        anchor = re.search(r"anchor:'([^']*)'", chunk)
        if ident and status and anchor:
            yield ident.group(1), status.group(1), anchor.group(1)


def edges(html):
    body = html.split("const edges = [", 1)[1].split("];", 1)[0]
    return re.findall(
        r"\['([^']*)',\s*'([^']*)',\s*'([^']*)'(?:,\s*'([^']*)')?\]", body
    )


def main():
    html = HTML.read_text()
    files = load_sources()
    missing = []
    proven = 0
    for ident, status, anchor in nodes(html):
        if status != "proven":
            continue
        proven += 1
        for name in segments(anchor):
            if not check_name(files, name):
                missing.append(f"node {ident}: {name}")
    via_count = 0
    for src, _dst, _kind, via in edges(html):
        if not via:
            continue
        for name in segments(via):
            via_count += 1
            if not check_name(files, name):
                missing.append(f"edge {src}: {name}")
    if missing:
        print(f"{len(missing)} missing name(s):")
        for item in missing:
            print(f"  {item}")
        return 1
    print(f"ok: {proven} proven nodes, {via_count} edge names")
    return 0


if __name__ == "__main__":
    sys.exit(main())
