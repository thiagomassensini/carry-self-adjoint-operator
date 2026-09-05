#!/usr/bin/env python3
"""Exact finite Naimark/source/determinant check for the material fiber m=12."""
import json
from pathlib import Path
import sympy as sp
a,b=sp.symbols("a b",positive=True)
x,z,t=sp.symbols("x z t",real=True)
A=sp.Matrix([[1/sp.sqrt(2),1/sp.sqrt(2),0],[0,0,1]])
S=sp.diag(1/a,1/a,1/b)
T=sp.diag(1/a,1/b)
u=sp.Matrix([1/a,1/a,1/b])
v=A*u
r=lambda s:(sp.eye(3)-s*s*S*S).inv()*u
phi=lambda s:r(s).col_join(s*S*r(s))
response=lambda s:s*(u.T*r(s))[0]
full=sp.factor((sp.eye(3)-t*t*S*S).det())
compressed=sp.factor((sp.eye(2)-t*t*T*T).det())
zero=lambda expr: all(sp.simplify(e)==0 for e in expr) if isinstance(expr,sp.MatrixBase) else sp.simplify(expr)==0
checks={
"coisometry":zero(A*A.T-sp.eye(2)),
"clock_intertwining":zero(A*S-T*A),
"source_multiplicity":zero(v-sp.Matrix([sp.sqrt(2)/a,1/b])),
"source_norm_preserved":zero((v.T*v-u.T*u)[0]),
"off_diagonal_kernel":zero((phi(x).T*phi(z))[0]-(response(z)-response(x))/(z-x)),
"diagonal_kernel":zero((phi(t).T*phi(t))[0]-sp.diff(response(t),t)),
"characteristic_log_derivative":zero(response(t)+sp.diff(full,t)/(2*full)),
"hidden_determinant_factor":zero(full-compressed*(1-t*t/a**2)),
"vector_trace":zero(response(t)-t*sp.trace(S*S*(sp.eye(3)-t*t*S*S).inv())),
"compressed_source_readout":zero(response(t)-t*(v.T*(sp.eye(2)-t*t*T*T).inv()*v)[0]),
}
assert all(checks.values()),checks
report={"material_fiber":12,"clock_symbols":{"a":"log 2","b":"log 3"},
"scope":"Exact rational/symbolic identities on their nonzero-denominator domains, not a Lean proof or native readout identification.",
"checks":checks,"full_determinant":str(full),"compressed_determinant":str(compressed),"compressed_source":[str(e) for e in v]}
Path(__file__).with_suffix(".json").write_text(json.dumps(report,indent=2)+"\n")
print(json.dumps(report,indent=2))
