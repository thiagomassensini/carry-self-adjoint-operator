#!/usr/bin/env python3
"""Native reference from the archived theta quadrature cache, never spectral data."""
import argparse, hashlib, json, sys
from pathlib import Path
import mpmath as mp
BASE=Path(__file__).resolve().parent
sys.path.insert(0,str(BASE/"source"))
import native_carry_adaptive_height_spectrum as native
ap=argparse.ArgumentParser()
ap.add_argument("--cache",type=Path,default=BASE/"source/theta-even-moments-v1-dps1600.json")
ap.add_argument("--output",type=Path,default=BASE/"reference/native_moments_rebuilt.json")
args=ap.parse_args()
mp.mp.dps=500
d=json.loads(args.cache.read_text())
a=[mp.mpf(d["moments"][str(k)]) for k in range(82)]
f=native.completed_even_coefficients(81,a)
h=native.logarithmic_moments(f,80)
fmt=lambda x:mp.nstr(x,450)
out={"method":"native theta quadrature cache -> completed even coefficients -> logarithmic recurrence; no spectral input",
"working_dps":500,"cache_dps":d["dps"],
"source_path":str(BASE/"source/native_carry_adaptive_height_spectrum.py"),
"source_sha256":hashlib.sha256((BASE/"source/native_carry_adaptive_height_spectrum.py").read_bytes()).hexdigest(),
"cache_path":str(args.cache),"cache_sha256":hashlib.sha256(args.cache.read_bytes()).hexdigest(),
"theta_even_moments":[fmt(x) for x in a],"f":[fmt(x) for x in f],"h":[fmt(x) for x in h],
"scale_free_moments":[fmt(h[k]*h[0]**(k-1)/h[1]**k) for k in range(12)],
"cache_independent_validation":"Run validate_reference.py; archived result is reference/quadrature_validation.json"}
args.output.parent.mkdir(exist_ok=True,parents=True)
args.output.write_text(json.dumps(out,indent=2)+"\n")
original=json.loads((BASE/"reference/native_moments.json").read_text())
keys=["theta_even_moments","f","h","scale_free_moments","cache_sha256","source_sha256"]
assert all(original[k]==out[k] for k in keys)
print("Rebuilt native coefficients and moments match archived decimal strings and source hashes.")
