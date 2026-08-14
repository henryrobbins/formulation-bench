#!/usr/bin/env python3
"""Verify every citekey used in the dataset resolves against `dataset/ref.bib`.

Walks the `metadata.source` of each `problem.json` and `formulation.json`
(including nested `origin` sources) along with the roles cited from their
`metadata.notes`, and reports keys with no matching BibTeX entry, plus entries
in the bibliography that nothing cites.
"""

import argparse
import json
import re
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
DATASET_DIR = REPO / "dataset"

BIB_ENTRY = re.compile(r"^@\w+\{([^,\s]+)\s*,", re.M)

#: A MyST citation role, as notes write it: ``{cite:t}`key```.
CITE_ROLE = re.compile(r"\{cite:\w+\}`([^`]+)`")


def _cited_keys(source: object) -> set[str]:
    if not isinstance(source, dict):
        return set()
    keys = set()
    if "citekey" in source:
        keys.add(str(source["citekey"]))
    return keys | _cited_keys(source.get("origin"))


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--dataset", type=Path, default=DATASET_DIR)
    args = parser.parse_args()

    defined = set(BIB_ENTRY.findall((args.dataset / "ref.bib").read_text()))

    used: dict[str, list[str]] = {}
    files = list(args.dataset.glob("problems/p*/problem.json"))
    files += list(args.dataset.glob("problems/p*/formulations/*/formulation.json"))
    for path in sorted(files):
        metadata = json.loads(path.read_text()).get("metadata", {})
        keys = _cited_keys(metadata.get("source"))
        for note in metadata.get("notes", []):
            keys |= set(CITE_ROLE.findall(note))
        for key in keys:
            used.setdefault(key, []).append(str(path.relative_to(args.dataset)))

    missing = {k: v for k, v in used.items() if k not in defined}
    for key, paths in sorted(missing.items()):
        print(f"missing from ref.bib: {key} (cited by {len(paths)} file(s))")
        for path in paths[:5]:
            print(f"    {path}")
    for key in sorted(defined - set(used)):
        print(f"uncited entry in ref.bib: {key}")

    if missing:
        return 1
    print(f"OK: {len(used)} citekeys across {len(files)} files resolve in ref.bib")
    return 0


if __name__ == "__main__":
    sys.exit(main())
