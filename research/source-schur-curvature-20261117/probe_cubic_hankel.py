#!/usr/bin/env python3
"""Audit the cubic rank-one and fifth-order null-direction source symbols.

The exact third-order defect is in HigherOrderCayleyDefect.lean and
NativePhysicalCubicBridge.lean. The fifth-order identity in this script is
CAS-checked symbolic series, NOT a Lean analytic-limit theorem.

No zeros or heights of the zeta function enter. All source coefficients
come from the canonical completed-native logarithmic moment genealogy.
"""
from pathlib import Path
import json
import sys
import mpmath as mp
import sympy as s

t = s.symbols("t", real=True)
h0, h1, h2 = s.symbols("h0 h1 h2", real=True)
u = lambda z: 2*z*(h0-h1*z*z+h2*z**4)
q = lambda z: (u(z)-1)/(u(z)+1)
a = lambda i: s.Rational(i, i+2)*(1-q(t)*q((i+1)*t))
b = lambda i: q((i+1)*t)-q(t)
aa = {i: s.series(a(i), t, 0, 7).removeO().expand() for i in (1, 2)}
bb = {i: s.series(b(i), t, 0, 7).removeO().expand() for i in (1, 2)}
K = lambda i, j: s.series(
    (aa[i]*aa[j]-bb[i]*bb[j])/(t*(i+j+2)), t, 0, 6
).removeO().expand()
k11,k12,k22 = K(1,1),K(1,2),K(2,2)
coeff3=s.Matrix([[s.factor(k11.coeff(t,3)),s.factor(k12.coeff(t,3))],
                 [s.factor(k12.coeff(t,3)),s.factor(k22.coeff(t,3))]])
expected3=32*h0*h1*s.Matrix([[1,2],[2,4]])
assert all(s.expand(x)==0 for x in (coeff3-expected3))
Q=s.expand(4*k11-4*k12+k22)
c5=s.factor(Q.coeff(t,5))
expected5=128*(h0*h2-h1*h1+4*h0**3*h1)
assert s.expand(c5-expected5)==0
assert s.expand(Q.coeff(t,3)) == 0
assert s.expand(Q.coeff(t,4)) == 0
print("Rank-one t^3 kernel: 32*h0*h1 * [[1,2],[2,4]] [SYMBOLIC VERIFIED]")
print("Null direction (2,-1), t^3 and t^4 coefficients: 0")
print("Null direction t^5 coefficient:",c5,"[SYMBOLIC VERIFIED]")
print("Lean analytic-limit certificate at t^5: NOT YET AVAILABLE")

if len(sys.argv) > 1:
    path=Path(sys.argv[1])
    mp.mp.dps=90
    data=json.loads(path.read_text())
    h=[mp.mpf(x) for x in data["canonical_h"]]
    predicted=128*(h[0]*h[2]-h[1]**2+4*h[0]**3*h[1])
    def H(w):
        return mp.polyval(list(reversed(h[:14])),w)
    def qnum(z):
        uz=2*z*H(-z*z)
        return (uz-1)/(uz+1)
    def num_a(i,z):
        return mp.mpf(i)/(i+2)*(1-qnum(z)*qnum((i+1)*z))
    def num_b(i,z):
        return qnum((i+1)*z)-qnum(z)
    def num_K(i,j,z):
        return (num_a(i,z)*num_a(j,z)-num_b(i,z)*num_b(j,z))/(z*(i+j+2))
    print("predicted c5 =", mp.nstr(predicted,20))
    for zstr in ["0.02","0.01","0.005","0.001"]:
        z=mp.mpf(zstr)
        qval=(4*num_K(1,1,z)-4*num_K(1,2,z)+num_K(2,2,z))/z**5
        print("radial t =",zstr,"normalized null energy =",mp.nstr(qval,20),
              "ratio =",mp.nstr(qval/predicted,15))
