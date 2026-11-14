#!/usr/bin/env python3
"""Compile and audit the Lean modules produced for prompt Luna A."""

from __future__ import annotations

import re
import subprocess
import sys


MODULES = [
    "CarrySelfAdjointOperator/AllPrefixPSDNonrecurrence.lean",
    "CarrySelfAdjointOperator/CompletedNativeSemidefiniteHardyGate.lean",
    "CarrySelfAdjointOperator/CompletedNativeSemidefiniteHardyGateAudit.lean",
]
TARGETS = [
    "CarrySelfAdjointOperator.AllPrefixPSDNonrecurrence",
    "CarrySelfAdjointOperator.CompletedNativeSemidefiniteHardyGate",
    "CarrySelfAdjointOperator.CompletedNativeSemidefiniteHardyGateAudit",
]
AUDIT_MODULE = MODULES[-1]
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def run(args: list[str], *, capture: bool = False) -> subprocess.CompletedProcess[str]:
    result = subprocess.run(args, text=True, capture_output=capture)
    if result.returncode:
        if capture:
            sys.stderr.write(result.stdout)
            sys.stderr.write(result.stderr)
        raise SystemExit(result.returncode)
    return result


def audit_axioms(output: str) -> int:
    matches = re.findall(r"depends on axioms:\s*\[(.*?)\]", output, re.S)
    if not matches:
        raise SystemExit("axiom audit emitted no theorem dependency lists")
    seen: set[str] = set()
    for match in matches:
        axioms = {
            re.sub(r"\s+", "", item)
            for item in match.split(",")
            if item.strip()
        }
        unexpected = axioms - ALLOWED_AXIOMS
        if unexpected:
            raise SystemExit(f"unexpected theorem axioms: {sorted(unexpected)}")
        seen.update(axioms)
    if not seen <= ALLOWED_AXIOMS:
        raise SystemExit(f"unexpected axiom set: {sorted(seen - ALLOWED_AXIOMS)}")
    print(f"Axiom audit passed for {len(matches)} declarations: {', '.join(sorted(seen))}")
    return len(matches)


def main() -> None:
    run(["lake", "build", *TARGETS], capture=True)
    print("Lake build passed for all prompt A modules.")

    for module in MODULES:
        run(["lake", "env", "lean", "-DwarningAsError=true", module], capture=True)
        print(f"Direct warning-as-error compile passed: {module}")

    audit = run(
        ["lake", "env", "lean", "-DwarningAsError=true", AUDIT_MODULE],
        capture=True,
    )
    audit_axioms(audit.stdout)
    run(["git", "diff", "--check"], capture=True)
    print("git diff --check passed.")


if __name__ == "__main__":
    main()
