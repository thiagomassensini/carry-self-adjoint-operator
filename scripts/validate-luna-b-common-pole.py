#!/usr/bin/env python3
"""Compile and audit all modules added for Luna B."""
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
MODULES = [
    "CarrySelfAdjointOperator/CommonPoleHankelCancellation.lean",
    "CarrySelfAdjointOperator/CompletedNativeCommonPoleCancellation.lean",
    "CarrySelfAdjointOperator/CompletedNativeCommonPoleAdapter.lean",
    "CarrySelfAdjointOperator/CommonPoleRegression.lean",
    "CarrySelfAdjointOperator/CommonPoleCancellationAudit.lean",
]
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}

def run(args: list[str]) -> str:
    result = subprocess.run(args, cwd=ROOT, text=True, stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT)
    sys.stdout.write(result.stdout)
    if result.returncode:
        raise SystemExit(result.returncode)
    return result.stdout

for source in MODULES[:-1]:
    module = source.removesuffix(".lean").replace("/", ".")
    output = ROOT / ".lake/build/lib/lean" / f"{module}.olean"
    output.parent.mkdir(parents=True, exist_ok=True)
    run(["lake", "env", "lean", "-DwarningAsError=true", "-o", str(output), source])

sources = [ROOT / p for p in MODULES[:-1]]
for path in sources:
    body = path.read_text()
    if re.search(r"\b(sorry|admit)\b|^\s*axiom\s", body, re.MULTILINE):
        raise SystemExit(f"forbidden proof token found in {path.relative_to(ROOT)}")

audit_module = MODULES[-1].removesuffix(".lean").replace("/", ".")
audit_output_path = ROOT / ".lake/build/lib/lean" / f"{audit_module}.olean"
audit_output_path.parent.mkdir(parents=True, exist_ok=True)
audit = run(["lake", "env", "lean", "-DwarningAsError=true", "-o",
             str(audit_output_path), MODULES[-1]])
run(["git", "diff", "--check"])
blocks = re.findall(r"depends on axioms: \[(.*?)\]", audit, re.DOTALL)
if not blocks:
    raise SystemExit("axiom audit emitted no theorem dependency blocks")
for block in blocks:
    axioms = {entry.strip() for entry in block.replace("\n", " ").split(",")}
    unexpected = axioms - ALLOWED_AXIOMS
    if unexpected:
        raise SystemExit(f"unexpected axioms: {sorted(unexpected)}")
if "sorryAx" in audit:
    raise SystemExit("audit found sorryAx")
print(f"validated {len(MODULES)} Lean modules; {len(blocks)} axiom reports use only accepted foundations")
