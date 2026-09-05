"""Recompile the archived Lean sources against the working repository pins.

Usage from the repository root:
  lake env python3 research/hp-notes-audit-2026-09-04/recheck_original_lean.py

Outputs go to a fresh temporary directory, not into the archived evidence.
"""
from pathlib import Path
import hashlib
import json
import os
import subprocess
import tempfile

archive = Path(__file__).resolve().parent
repo = archive.parents[1]
sources = archive / 'original-lean'
build = Path(tempfile.mkdtemp(prefix='carry-hp-lean-recheck-'))
names = ['FiniteCanonicalCameraReadout', 'FiniteEnrichedCameraState',
         'FiniteStencilCutoffRefinement', 'CanonicalNaimarkStateReadout',
         'ExactCutoffCameraGram', 'C3ProjectiveCompletedJetBridge',
         'C3ProjectiveHilbertRBBridge', 'C3CameraStencilEscapeClosure',
         'C3TwoVariableGreenGamma']
env = os.environ.copy()
env['LEAN_PATH'] = str(build) + ':' + env.get('LEAN_PATH', '')
results = []
for name in names:
    source = sources / (name + '.lean')
    run = subprocess.run(['lean', '-R', str(sources), str(source),
                          '-o', str(build / (name + '.olean'))],
                         cwd=repo, env=env, capture_output=True, text=True)
    output = run.stdout + run.stderr
    (build / (name + '.log')).write_text(output)
    results.append({'module': name, 'exit_code': run.returncode,
                    'sha256': hashlib.sha256(source.read_bytes()).hexdigest(),
                    'warnings': output.count('warning:')})
    print(name, run.returncode, flush=True)
(build / 'results.json').write_text(json.dumps(results, indent=2) + '\n')
print('Results:', build)
raise SystemExit(any(item['exit_code'] != 0 for item in results))
