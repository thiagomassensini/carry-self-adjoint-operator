"""Record the historical comment matches and require a clean current scan."""
import json
import subprocess

pattern = r"(^|[^A-Za-z])(sorry|admit|axiom|unsafe)([^A-Za-z]|$)"
legacy = subprocess.run(
    ["git", "grep", "-n", "-E", pattern,
     "cb33c845a7ee0ca1c6bf195d34d7f3ac1628edfa", "--",
     "CarrySelfAdjointOperator", "CarrySelfAdjointOperator.lean"],
    text=True, capture_output=True, check=False,
)
current = subprocess.run(
    ["rg", "-n", "--glob", "*.lean", pattern,
     "CarrySelfAdjointOperator", "CarrySelfAdjointOperator.lean"],
    text=True, capture_output=True, check=False,
)
assert legacy.returncode == 0 and len(legacy.stdout.splitlines()) == 5
assert current.returncode == 1 and not current.stdout, current.stdout + current.stderr
print(json.dumps({"legacy_comment_matches": 5, "current_matches": 0,
                  "legacy_matches_repaired_only_in_comments": True}))
