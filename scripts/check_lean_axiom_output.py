#!/usr/bin/env python3
"""Validate any `#print axioms` reports emitted during a Lean file check."""

from pathlib import Path
import re
import sys


ALLOWED = {"propext", "Classical.choice", "Quot.sound"}


def main() -> int:
    if len(sys.argv) != 2:
        print("usage: check_lean_axiom_output.py OUTPUT_FILE", file=sys.stderr)
        return 2

    output = Path(sys.argv[1]).read_text(encoding="utf-8")
    if "sorryAx" in output:
        print("Lean axiom output contains sorryAx", file=sys.stderr)
        return 1

    reports = re.findall(r"depends on axioms:\s*\[(.*?)\]", output, re.DOTALL)
    for report in reports:
        axioms = {
            re.sub(r"\s+", "", item)
            for item in report.split(",")
            if item.strip()
        }
        unexpected = axioms - ALLOWED
        if unexpected:
            print(f"unexpected Lean axioms: {sorted(unexpected)}", file=sys.stderr)
            return 1

    print(f"axiom output passed ({len(reports)} report(s))")
    return 0


if __name__ == "__main__":
    sys.exit(main())
