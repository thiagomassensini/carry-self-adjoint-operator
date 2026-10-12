#!/usr/bin/env python3
"""Exact diagnostics of two specified multibase candidates, not a theory-wide no-go.

Profiles and levels are literal definitions from the pinned Weyl
Camera/PeriodicProfiles.lean. The whole period and every camera cross are kept.
This script is a rational test, not a Lean certificate of a physical sewing map.
"""
from fractions import Fraction as Q
import json
from pathlib import Path

BASES = tuple(range(2, 8))

def level(b):
    return 4 if b == 2 else b

def profile(b, n):
    if b == 2:
        return 1-int(n % 2 == 0)-2*int(n % 4 == 0)
    if b % 2:
        return 1-b*int(n % b == 0)
    return 1+int(n % (b//2) == 0)-(b+2)*int(n % b == 0)

def periodic_mean(b, c):
    return Q(sum(profile(b, n)*profile(c, n) for n in range(420)), 420)

def kernel(i, j, per_atom):
    result = Q(0)
    for b in BASES:
        for c in BASES:
            weights = profile(b, i+1)*profile(c, j+1) if per_atom else 1
            h = min(level(b), level(c))
            result += weights*periodic_mean(b, c)*Q(
                h**(i+j+2), (i+j+2)*level(b)**(i+1)*level(c)**(j+1))
    return result

def run():
    rows = {}
    for name, per_atom, expected in (
        ("whole_stencil_replication", False, Q(59, 54)),
        ("profile_weighted_per_atom", True, Q(-157, 54)),
    ):
        k00, k01 = kernel(0, 0, per_atom), kernel(0, 1, per_atom)
        defect = 2*k00-3*k01
        assert defect == expected and defect != 0
        rows[name] = {"K00": str(k00), "K01": str(k01),
                      "2K00_minus_3K01": str(defect)}
    c2 = [profile(2, j+1) for j in range(3)]
    c4 = [profile(4, j+1) for j in range(3)]
    assert c2 == [1, 0, 1] and c4 == [1, 2, 1]
    result = {"status": "PASS_EXACT_RATIONAL_NO_GO",
              "candidate_grams": rows,
              "c2_weighted_stencil_coefficients": [c2[0], -2*c2[1], c2[2]],
              "c4_weighted_stencil_coefficients": [c4[0], -2*c4[1], c4[2]],
              "scope": "Specified candidate maps only; no physical signed positivity or theory-wide impossibility."}
    Path(__file__).with_name("physical_sewing_canaries.json").write_text(
        json.dumps(result, ensure_ascii=False, indent=2)+"\n")
    print(json.dumps(result, ensure_ascii=False, indent=2))

if __name__ == "__main__":
    run()
