#!/usr/bin/env bash
set -euo pipefail
G=/home/thlinux/geometry-of-numbers
D=$G/research/native-cauchy-residual-return
SELF=$(cd "$(dirname "$0")" && pwd)
cd /home/thlinux/carry-self-adjoint-operator
export PATH="$HOME/.elan/bin:$PATH"
export LEAN_PATH="$SELF/.cache:$D/.cache:$D/../native-return-boundary-deflation/.cache:$D/../native-positive-square-kernel/.cache:$D/../source-euler-residual-control/.cache:$D/../source-euler-residual-control/.cache/pr34:$D/../native-jet-overlap-budget/.cache:$D/../native-jet-overlap-budget/.cache/pr41:$G/.lake/build/lib/lean:$D/../native-fiber-transport/.cache:$D/../physical-trace-fiber/.cache:$G/.lake/build/research/sixth-odd-twelve-sources:$G/.lake/build/research/sixth-even-source-schur:$G/.lake/build/research/theta-fifth-odd-pattern:$G/.lake/build/research/critical-source-return:$G/.lake/build/research/return-block-compatibility:$G/.lake/build/research/corrected-green-source-ports:$G/.lake/build/research/material-integral-certificate:$G/.lake/build/research/prime-camera-schur:$G/.lake/build/research/material-pivot-certificate:$(lake env printenv LEAN_PATH)"
lean -DwarningAsError=true "$1"
