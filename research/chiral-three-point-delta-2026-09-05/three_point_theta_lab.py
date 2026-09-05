#!/usr/bin/env python3
"""Evaluate the existing theta-tail representation; no spectral fitting.

Quadrature and finite mode/tail truncations are diagnostics, not interval
certificates. The independent exact calculation uses rational polynomials.
"""
import argparse
import json
from fractions import Fraction as Q

import mpmath as mp
import sympy as sp


def exact_diagnostics():
    e, h0, h1, h2 = sp.symbols("epsilon h0 h1 h2")
    def entry(i, j):
        return sum(h * (-1)**n * e**(2*n) *
                   sp.Rational(i**(2*n+1) + j**(2*n+1), i+j)
                   for n, h in enumerate((h0, h1, h2)))
    det = sp.Poly(sp.expand(sp.det(sp.Matrix(3, 3,
                        lambda i, j: entry(i+1, j+1)))), e)
    assert all(det.nth(n) == 0 for n in range(6))
    leading = sp.factor(det.nth(6))
    assert sp.expand(leading - 4*h1*(h0*h2-h1**2)) == 0
    a0, a2, a4, a6 = Q(23,2000), Q(1,4000), Q(19,1000000), Q(3,1000000)
    mu = (Q(1,2)-a0/4, 2*a0-a2/4, 12*a2-a4/4, 30*a4-a6/4)
    numerator = 15*mu[1]**2*mu[2] + 3*mu[0]*mu[1]*mu[3] - 10*mu[0]*mu[2]**2
    assert a0 > Q(113,10000) and a2 < Q(51,200000)
    assert all(x > 0 for x in mu)
    assert mu[0]*mu[2] < 3*mu[1]**2 and numerator < 0
    certificate = (15*Q(287,12500)**2*Q(37,12500) +
                   3*Q(497,1000)*Q(287,12500)*Q(299,500000) -
                   10*Q(249,500)*Q(593,200000)**2)
    assert certificate == Q(4861191,50000000000000)
    return {"truncated_kernel_det_coefficients": {
                str(i): str(sp.factor(det.nth(i))) for i in range(det.degree()+1)},
            "sixth_coefficient": str(leading),
            "abstract_coarse_bounds_witness": {
                "tail_moments": list(map(str,(a0,a2,a4,a6))),
                "cosine_moments": list(map(str,mu)),
                "numerator": str(numerator),
                "is_canonical_native_data": False},
            "sufficient_rational_box_margin": str(certificate)}


def run(dps, modes, cap):
    mp.mp.dps = dps
    knots = [mp.mpf(x) for x in (1,2,4,8,16) if x < cap] + [mp.mpf(cap)]
    def weight(x):
        return x**(-mp.mpf(3)/4) * mp.fsum(mp.exp(-mp.pi*n*n*x)
                                         for n in range(1,modes+1))
    def integral(f):
        return mp.quad(lambda x: f(mp.log(x)/2)*weight(x), knots)
    tail = [integral(lambda u, n=n: u**n) for n in (0,2,4,6)]
    mu = [mp.mpf('.5')-tail[0]/4, 2*tail[0]-tail[1]/4,
          12*tail[1]-tail[2]/4, 30*tail[2]-tail[3]/4]
    h0 = mu[1]/(2*mu[0])
    h1 = mu[1]**2/(4*mu[0]**2)-mu[2]/(12*mu[0])
    h2 = mu[1]**3/(8*mu[0]**3)-mu[1]*mu[2]/(16*mu[0]**2)+mu[3]/(240*mu[0])
    numerator = 15*mu[1]**2*mu[2]+3*mu[0]*mu[1]*mu[3]-10*mu[0]*mu[2]**2
    delta = h0*h2-h1**2
    assert mp.almosteq(delta, numerator/(1440*mu[0]**3))
    def response_im(y):
        a = integral(lambda u: mp.cosh(y*u))
        b = integral(lambda u: u*mp.sinh(y*u))
        f = mp.mpf('.5')-(mp.mpf('.25')-y*y)*a
        return (y*a-(mp.mpf('.25')-y*y)*b/2)/f
    rows=[]
    for den in (20,40,80):
        eps=mp.mpf(1)/den
        a=[response_im(j*eps) for j in (1,2,3)]
        kernel=mp.matrix(3,3)
        for i in range(3):
            for j in range(3):
                kernel[i,j]=(a[i]+a[j])/((i+j+2)*eps)
        normalized=mp.det(kernel)/eps**6
        rows.append({"epsilon": f"1/{den}",
                     "det_over_epsilon6": mp.nstr(normalized,35),
                     "ratio_to_limit": mp.nstr(normalized/(4*h1*delta),30)})
    return {"dps":dps,"theta_modes":modes,"x_cutoff":cap,
            "is_interval_certificate":False,
            "tail_moments":list(map(lambda x:mp.nstr(x,35),tail)),
            "cosine_moments":list(map(lambda x:mp.nstr(x,35),mu)),
            "native_log_moments":list(map(lambda x:mp.nstr(x,35),(h0,h1,h2))),
            "numerator":mp.nstr(numerator,35),"delta2":mp.nstr(delta,35),
            "three_point_leading_coefficient":mp.nstr(4*h1*delta,35),
            "samples":rows}


if __name__ == "__main__":
    parser=argparse.ArgumentParser()
    parser.add_argument("--dps",type=int,default=45)
    parser.add_argument("--modes",type=int,default=8)
    parser.add_argument("--cap",type=int,default=32)
    args=parser.parse_args()
    print(json.dumps({"exact":exact_diagnostics(),
                      "quadrature":run(args.dps,args.modes,args.cap)},indent=2))
