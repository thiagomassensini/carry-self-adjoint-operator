#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/.."

base_sha="${1:-}"
head_sha="${2:-HEAD}"

# Manual runs and new branches without a usable comparison keep the full audit.
if [[ -z "$base_sha" ]] || ! git cat-file -e "$base_sha^{commit}" 2>/dev/null; then
  bash scripts/audit.sh
  exit 0
fi

full_audit=0
modules=()
while IFS=$'\t' read -r status path _; do
  [[ -n "${status:-}" ]] || continue

  case "$path" in
    CarrySelfAdjointOperator.lean|lakefile.toml|lake-manifest.json|lean-toolchain|scripts/audit.sh)
      full_audit=1
      ;;
    *.lean)
      if [[ "$status" == A ]]; then
        module="${path%.lean}"
        modules+=("${module//\//.}")
      else
        full_audit=1
      fi
      ;;
  esac
done < <(git diff --name-status "$base_sha" "$head_sha")

if (( full_audit )); then
  echo "Existing Lean sources or build inputs changed; running the complete kernel audit."
  bash scripts/audit.sh
  exit 0
fi

if (( ${#modules[@]} == 0 )); then
  echo "No Lean source additions changed; static source audit is the applicable check."
  exit 0
fi

echo "Building ${#modules[@]} newly added Lean module(s): ${modules[*]}"
lake build --wfail "${modules[@]}"

for module in "${modules[@]}"; do
  lean_file="${module//.//}.lean"
  output="$(mktemp)"
  if ! lake env lean -DwarningAsError=true "$lean_file" >"$output" 2>&1; then
    cat "$output"
    rm -f "$output"
    exit 1
  fi
  cat "$output"
  python3 scripts/check_lean_axiom_output.py "$output"
  rm -f "$output"
done

echo "Changed Lean module audit passed."
