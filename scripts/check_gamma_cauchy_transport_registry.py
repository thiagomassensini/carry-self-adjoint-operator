#!/usr/bin/env python3
"""Check the complete public Gamma/material surface and audit coverage."""
from pathlib import Path
import json
import re

root = Path(__file__).resolve().parents[1]
registry = json.loads((root / "audit/gamma-cauchy-transport-registry.json").read_text())
total = 0
registered = {module["module"] for module in registry["modules"]}
available = {path.stem for path in (root / "CarrySelfAdjointOperator").glob("NativeGamma*.lean")
             if not path.stem.endswith("Audit")}
assert registered == available, f"Unregistered Gamma modules: {registered ^ available}"
for module in registry["modules"]:
    name = module["module"]
    source = (root / f"CarrySelfAdjointOperator/{name}.lean").read_text()
    audit = (root / f"CarrySelfAdjointOperator/{name}Audit.lean").read_text()
    actual = re.findall(r"^(?:def|theorem|lemma|abbrev) ([A-Za-z0-9_]+)", source, re.MULTILINE)
    assert actual == module["declarations"], f"Public surface drift: {name}"
    for declaration in actual:
        assert re.search(rf"^#check {declaration}$", audit, re.MULTILINE), declaration
        assert re.search(rf"^#print axioms {declaration}$", audit, re.MULTILINE), declaration
    guard = audit.split("#audit_physical_sewing\n", 1)[1].split("\nend ", 1)[0]
    assert guard.split() == actual, f"Type/body guard coverage: {name}"
    assert not re.search(r"\b(?:sorry|admit|axiom|unsafe)\b", source), name
    total += len(actual)
assert total == registry["public_declarations"]
print(f"Gamma/material inventory passed: {total} public declarations in {len(registry['modules'])} modules")
