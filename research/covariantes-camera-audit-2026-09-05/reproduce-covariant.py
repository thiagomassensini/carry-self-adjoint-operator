#!/usr/bin/env python3
"""Reproduce the existing covariant-camera diagnostic without rebuilding its model."""
from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import sys
import tempfile

sys.dont_write_bytecode = True


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source", type=Path, default=Path("/home/thlinux/covariantes"))
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    script = args.source / "script/c2_covariant_multibase_connection.py"
    digest = hashlib.sha256(script.read_bytes()).hexdigest()
    spec = importlib.util.spec_from_file_location("covariant_research_source", script)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"Cannot load {script}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    cameras = [2, 3, 5, 7, 11, 13]
    seed = 20260905
    rows = [
        {
            "cameras": cameras,
            "centers_per_camera": cut,
            "seed": seed,
            **module.exact_connection_audit(cameras, cut, seed),
        }
        for cut in (8, 64, 256)
    ]
    destination = args.output
    if destination is None:
        destination = Path(tempfile.mkdtemp(prefix="covariant-camera-reproduction-"))
    destination.mkdir(parents=True, exist_ok=True)
    with (destination / "covariant-diagnostics.json").open("x") as stream:
        json.dump(rows, stream, indent=2)
        stream.write("\n")
    with (destination / "source.json").open("x") as stream:
        json.dump({"script": str(script.resolve()), "sha256": digest}, stream, indent=2)
        stream.write("\n")
    print(destination)


if __name__ == "__main__":
    main()
