# Reproduction: height coordinates and complete C3 cutoffs

Research date: 2026-09-04. Source baseline:
`carry-self-adjoint-operator@a52230c5cba4918fb5f05d00c8f31b27bc828d09`.

See [the source audit](../../docs/auditoria-coordenadas-altura-cortes-c3.md).

The height source lab was supplied by Thiago at
`/home/thlinux/Downloads/hp/native_carry_height_moment_jacobi_operator_lab.py`.
Its bytes are preserved under `source/`. The other seven source modules were
copied unchanged from the server directory
`/home/thlinux/carry-lab/native_carry_transverse_coercivity_cutoff_bundle_20260815`.
`manifest.json` records SHA-256 for all archived files except itself.

The new wrapper calls the supplied lab's moment/Jacobi/height functions with
the existing native theta moment reference. It does not call the source lab's
Cauchy/zeta construction or its optional zero comparison. Calls to `mp.zeta`
and `mp.zetazero` are explicitly rejected inside this wrapper.

From this directory, with Python and mpmath:

```bash
python3 audit_height_coordinates.py \
  --reference ../geometric-kernel-search-2026-09-04/reference/native_moments.json \
  --dps 220 --output /tmp/carry-height-coordinates.json
```

The camera audit requires NumPy and SciPy in addition to Python:

```bash
OPENBLAS_NUM_THREADS=1 python3 source/native_carry_camera_completeness_audit.py \
  --sizes 16,32,64,128 --time 2 \
  --output /tmp/carry-camera-completeness.json
```

The camera lab is preserved as historical source. Its automatic interpretation
strings are not formal conclusions. The new report cites specific finite
rows. The Pythagorean control module uses SciPy's zeta function for its
arithmetic weight formulas; this is separate from the height wrapper, which
does not evaluate zeta or zero heights.

From the repository root, with Lean 4.32.0:

```bash
bash scripts/audit.sh
```

`lean-audit.log` records the successful static audit and all 14 build calls,
including the four new declarations in
`CompletedC3GeometricCutoffCalibration.lean`. Each new declaration depends
only on the standard `propext`, `Classical.choice` and `Quot.sound` footprint
(or a subset). The log includes replayed informational tactic suggestions;
there are no lines starting with `error:` or `warning:`.

Finite numerical positivity does not establish an all-order native measure.
The C3 theorem concerns only the existing fixed standard orthogonal-sum
metric. No identification of that metric or of the material log generator
with the native moment realization is added.
