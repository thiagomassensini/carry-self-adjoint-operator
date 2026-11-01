#!/usr/bin/env python3
"""Generate Lean floor certificates for T16 from Cells14_00..Cells14_17.

For each block b in 00..17:
- reads CarrySelfAdjointOperator/ThetaFourteenthSourceCertificateData/Cells14_{b}.lean
- extracts theorem headers thetaFourteenth_cell_bounds_14_jjj
- computes q_j = floor(j^2 * num * 10^18 / (512^2 * den))
- writes scratch_local/Theta16FloorBlock{b}.lean with 32 Lean theorems

Also writes a JSON report to scratch_local/theta16_floor_generation_report.json.
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
from pathlib import Path
from typing import Iterable

HEADER_RE = re.compile(
    r"theorem thetaFourteenth_cell_bounds_14_(\d{3})\s*:\s*"
    r"\((\d+)/(\d+):ℝ\)\s*≤\s*"
    r"\(∫ x in \(([^)]+):ℝ\)\.\.\(([^)]+):ℝ\),\s*x\^14\*thetaFirstMode x\)\s*∧",
    re.MULTILINE,
)


def generate_block(root: Path, block: int, out_dir: Path) -> dict:
    src = root / f"CarrySelfAdjointOperator/ThetaFourteenthSourceCertificateData/Cells14_{block:02d}.lean"
    text = src.read_text()

    rows = []
    for j_s, num_s, den_s, left_ep, right_ep in HEADER_RE.findall(text):
        j = int(j_s)
        num = int(num_s)
        den = int(den_s)
        q = (j * j * num * 10**18) // (512**2 * den)
        rows.append((j, num, den, q, left_ep, right_ep))

    rows.sort(key=lambda t: t[0])
    expected = list(range(32 * block, 32 * block + 32))
    got = [r[0] for r in rows]
    if got != expected:
        raise ValueError(
            f"Block {block:02d} j mismatch: expected {expected[0]}..{expected[-1]}, got count={len(got)}"
        )

    out = [
        f"import CarrySelfAdjointOperator.ThetaFourteenthSourceCertificateData.Cells14_{block:02d}",
        "import Mathlib.Tactic",
        "",
        "open MeasureTheory",
        "namespace CarrySelfAdjointOperator",
        "noncomputable section",
        "set_option maxHeartbeats 4000000",
        "set_option maxRecDepth 8192",
        "",
    ]

    for j, num, den, q, left_ep, right_ep in rows:
        out.append(
            f"""theorem theta16_floor_cell_{j:03d} :
    ({q} : ℝ) / 1000000000000000000 ≤
      (({j} : ℝ)/512)^2 *
        (∫ x in ({left_ep}:ℝ)..({right_ep}:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_{j:03d}).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ (({j} : ℝ)/512)^2 by positivity)
  have hn :
      ({q} : ℝ) / 1000000000000000000 ≤
        (({j} : ℝ)/512)^2 *
          ({num}/{den} : ℝ) := by
    norm_num
  have ht :
      (({j} : ℝ)/512)^2 *
        ({num}/{den} : ℝ) ≤
      (({j} : ℝ)/512)^2 *
        (∫ x in ({left_ep}:ℝ)..({right_ep}:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht
"""
        )

    out += ["end", "end CarrySelfAdjointOperator", ""]

    dst = out_dir / f"Theta16FloorBlock{block:02d}.lean"
    dst.write_text("\n".join(out))

    block_sum = sum(r[3] for r in rows)
    return {
        "block": block,
        "source_file": str(src),
        "output_file": str(dst),
        "row_count": len(rows),
        "j_start": expected[0],
        "j_end": expected[-1],
        "block_sum": block_sum,
    }


def compile_blocks(root: Path, files: Iterable[Path]) -> None:
    for file_path in files:
        rel = file_path.relative_to(root)
        print(f"Compiling {rel}")
        proc = subprocess.run(
            ["lake", "env", "lean", str(rel)],
            cwd=root,
            text=True,
            capture_output=True,
        )
        if proc.returncode != 0:
            print(proc.stdout, end="")
            print(proc.stderr, end="")
            raise RuntimeError(f"Compilation failed for {rel}")


def main() -> None:
    parser = argparse.ArgumentParser(description="Generate Theta16 floor block certificates")
    parser.add_argument(
        "--root",
        default=".",
        help="Repository root (default: current directory)",
    )
    parser.add_argument(
        "--compile",
        action="store_true",
        help="Compile all generated block files with lake env lean",
    )
    args = parser.parse_args()

    root = Path(args.root).resolve()
    out_dir = root / "scratch_local"
    out_dir.mkdir(exist_ok=True)

    generated_files = []
    block_reports = []
    grand_total = 0
    theorem_count = 0

    for block in range(18):
        rep = generate_block(root, block, out_dir)
        block_reports.append(rep)
        generated_files.append(Path(rep["output_file"]))
        theorem_count += rep["row_count"]
        grand_total += rep["block_sum"]
        print(f"block {block:02d} sum {rep['block_sum']}")

    report = {
        "blocks": block_reports,
        "grand_total": grand_total,
        "theorem_count": theorem_count,
    }

    report_path = out_dir / "theta16_floor_generation_report.json"
    report_path.write_text(json.dumps(report, indent=2))

    print(f"grand_total {grand_total}")
    print(f"theorem_count {theorem_count}")
    print(f"report {report_path.relative_to(root)}")

    if args.compile:
        compile_blocks(root, generated_files)
        print("compile_status ALL_SUCCEEDED")


if __name__ == "__main__":
    main()
