#!/usr/bin/env bash
# Validate the CSA fifth native C3 source channel against the ORIGINAL
# geometry-of-numbers PR #324 Lean proof; never postulate its sign.
set -euo pipefail

here=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
gon_git=${GON_GIT_ROOT:-/home/thlinux/geometry-of-numbers}
gon_pr_cache=${GON_PR_CACHE_ROOT:-/home/thlinux/worktrees/c3-cofactor-chiral-certification-20261112}
gon_build=${GON_BUILD_ROOT:-/home/thlinux/geometry-of-numbers}
carry_build=${CARRY_BUILD_ROOT:-/home/thlinux/carry-self-adjoint-operator}
orientation_cache=${GON_ORIENTATION_ROOT:-/home/thlinux/geometry-of-numbers-c3-source-orientation}
tilt_cache=${GON_TILT_ROOT:-/home/thlinux/geometry-of-numbers-critical-tilt-prime}
upstream_commit=6c5c97b03925c398bf77a561d6e76b14563265e0

for dir in "$gon_git/.git" "$here/scratch_local" "$gon_build/.lake/build/lib/lean" \
  "$gon_pr_cache/research/c3-cofactor-chiral-certification/.cache" \
  "$gon_pr_cache/research/c3-cofactor-correlation-gate/.cache"; do
  if [[ ! -e "$dir" ]]; then
    echo "Required directory/cache missing: $dir" >&2
    echo "Rebuild GoN PR #324 research prerequisites with its validate.sh first." >&2
    exit 2
  fi
done
git -C "$gon_git" cat-file -e "$upstream_commit^{commit}"
test "$(cat "$gon_git/lean-toolchain")" = "leanprover/lean4:v4.32.0"

tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
mkdir -p "$tmp/src" "$tmp/olean/scratch_local"

# Dependencies of NativeEvenCertificate were built by GoN's source validators.
# The final five upstream modules are ALWAYS rebuilt from pinned Git blobs.
# A clean GoN environment must first run:
#   bash research/c3-cofactor-chiral-certification/validate.sh
# This validator is a leaf integration check, not a substitute for the
# transitive source certificate auditor in that upstream validator.
base=$(cd "$here" && lake env printenv LEAN_PATH)
cache_paths=$(find \
    "$gon_pr_cache/research" "$gon_build/research" "$carry_build/research" \
    "$orientation_cache/research" "$tilt_cache/research" \
    -type d -path '*/.cache*' -printf '%p:' 2>/dev/null || true)
research_build_paths=$(find \
    "$gon_build/.lake/build/research" "$carry_build/.lake/build/research" \
    -mindepth 1 -maxdepth 1 -type d -printf '%p:' 2>/dev/null || true)
export LEAN_PATH="$tmp/olean:$gon_pr_cache/research/c3-cofactor-chiral-certification/.cache:$gon_pr_cache/research/c3-cofactor-correlation-gate/.cache:$cache_paths$research_build_paths$gon_build/.lake/build/lib/lean:$base"

source_of() {
  local name=$1 rel=$2
  git -C "$gon_git" show "$upstream_commit:$rel" > "$tmp/src/$name.lean"
  local expected actual
  expected=$(git -C "$gon_git" rev-parse "$upstream_commit:$rel")
  actual=$(git -C "$gon_git" hash-object "$tmp/src/$name.lean")
  [[ "$expected" == "$actual" ]] || {
    echo "Pinned upstream blob mismatch: $name" >&2; exit 3;
  }
  echo "PR324 source: $name blob=$actual"
}

source_of SourceSchurShift "research/c3-source-orientation/SourceSchurShift.lean"
source_of SourceGate "research/c3-cofactor-chiral-certification/SourceGate.lean"
source_of CofactorTransport "research/c3-cofactor-chiral-certification/CofactorTransport.lean"
source_of FiniteReferenceTable "research/c3-cofactor-correlation-gate/FiniteReferenceTable.lean"
source_of NativeEvenCertificate "research/c3-cofactor-chiral-certification/NativeEvenCertificate.lean"

if rg -n '(^|[[:space:]])(sorry|admit|axiom)([[:space:]]|$)' "$tmp/src" -g '*.lean'; then
  echo 'Upstream source contains a proof hole or newly declared axiom' >&2
  exit 4
fi

for module in SourceSchurShift SourceGate CofactorTransport FiniteReferenceTable NativeEvenCertificate; do
  echo "Compile pinned GoN PR324: $module"
  lean -DwarningAsError=true --root="$tmp/src" \
    -o "$tmp/olean/$module.olean" "$tmp/src/$module.lean"
done

for module in \
  NativeSchurJetConvolution20261120 \
  SourceReductionParityStageFour20261120 \
  NativeFifthPositiveSourceGate20261120 \
  SourceFifthJetExtraction20261120 \
  FifthNativeSourceClosed20261120 \
  FifthNativePositiveKernel20261120; do
  echo "Compile CSA source: $module"
  lean -DwarningAsError=true --root="$here" \
    -o "$tmp/olean/scratch_local/$module.olean" "$here/scratch_local/$module.lean"
done

echo "Verify unconditional GoN→CSA C3 sign and five-channel Green kernel"
lean -DwarningAsError=true --root="$here" \
  "$here/scratch_local/NativeC3EvenThirdCertificateImport20261120.lean"

echo "PR324_SOURCE_IMPORT_7_OF_7_PASSED"
