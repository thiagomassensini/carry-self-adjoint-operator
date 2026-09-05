#!/usr/bin/env python3
"""Necessary finite cyclic constraints computed from native moments.
These are benchmarks, not an independently derived geometric operator.
"""
import json, sys
from pathlib import Path
import mpmath as mp
BASE=Path(__file__).resolve().parent
sys.path.insert(0,str(BASE/"source"))
import native_carry_adaptive_height_spectrum as native
mp.mp.dps=350
ref=json.loads((BASE/"reference/native_moments.json").read_text())
h=[mp.mpf(v) for v in ref["h"]]
n=8
g,k=native.hankel_pair(h,n)
b,pivots=native.canonical_ldl_whitener(g)
j=b*k*b.T
off=mp.sqrt(h[2]/h[0]-(h[1]/h[0])**2)
fmt=lambda x:mp.nstr(x,100)
report={"scope":"Necessary matrix elements of V=S^2 in the cyclic basis u,Vu,... . Constructed from target moments for comparison only; not a geometric identification.",
"order":n,"working_dps":350,
"source_norm_squared":fmt(h[0]),
"V_first_diagonal":fmt(h[1]/h[0]),
"V_first_off_diagonal":fmt(off),
"trace_effective_rank_if_HS_realization":fmt(h[0]**2/h[1]),
"diagonal":[fmt(j[i,i]) for i in range(n)],
"off_diagonal":[fmt(j[i,i+1]) for i in range(n-1)],
"off_tridiagonal_max":fmt(max(abs(j[i,jj]) for i in range(n) for jj in range(n) if abs(i-jj)>1)),
"whitening_max":fmt(max(abs((b*g*b.T-mp.eye(n))[i,jj]) for i in range(n) for jj in range(n)))}
(BASE/"reference/cyclic_constraints.json").write_text(json.dumps(report,indent=2)+"\n")
print(json.dumps({k:report[k] for k in ["source_norm_squared","V_first_diagonal","V_first_off_diagonal","trace_effective_rank_if_HS_realization","off_tridiagonal_max","whitening_max"]},indent=2))
