#!/usr/bin/env python3
"""External ball-arithmetic check of the native sixth-moment sign.

Requires python-flint==0.9.0. This certificate is not a Lean proof.
Finite integration uses Arb with analytic branch checking. The two omitted
tails are bounded by positive exponential-polynomial integrals as documented
in the accompanying map. No computed bounds are imported as Lean premises.
"""
import argparse
import json
import math
import flint
from flint import acb, arb, ctx


def exp_power_tail(p, rate, cutoff):
    """Integral_cutoff^infinity x^p exp(-rate*x) dx, enclosed by Arb."""
    return (-rate*cutoff).exp() * sum(
        arb(math.factorial(p)//math.factorial(p-j)) * cutoff**(p-j) / rate**(j+1)
        for j in range(p+1))


def main(bits, modes, cutoff):
    assert bits >= 80 and modes >= 1 and cutoff >= 2
    ctx.prec = bits
    pi = arb.pi()
    records=[]
    A=[]
    for p in (0,2,4,6):
        def f(x, analytic):
            logx = x.log(analytic=analytic)
            return (logx/2)**p * (-arb(3)*logx/4).exp() * sum(
                (-acb(pi)*n*n*x).exp() for n in range(1,modes+1))
        knots = [x for x in (1,2,4,8,16,32,64) if x < cutoff]+[cutoff]
        finite = sum((acb.integral(f,a,b) for a,b in zip(knots,knots[1:])), acb(0))
        assert finite.is_finite() and finite.imag.contains(0)
        # x^(-3/4) <= 1 and (log(x)/2)^p <= (x/2)^p for x >= 1.
        # n^2 >= 1+3(n-1), hence sum exp(-pi*n^2*x) <=
        # exp(-pi*x)/(1-exp(-3*pi*cutoff)) on x >= cutoff.
        spatial = exp_power_tail(p,pi,arb(cutoff)) / (
            2**p * (1-(-3*pi*cutoff).exp()))
        # n=modes+1+j: n^2 >= (modes+1)^2+(2*modes+3)*j.
        # Bounding the geometric denominator at x=1 yields the omitted modes.
        rate=pi*(modes+1)**2
        modal = exp_power_tail(p,rate,arb(1)) / (
            2**p * (1-(-pi*(2*modes+3)).exp()))
        error=spatial+modal
        assert error > 0
        total=finite.real+arb(0,error.upper())
        A.append(total)
        records.append({"power":p,"finite_integral":str(finite),
                        "spatial_tail_upper_ball":str(spatial),
                        "omitted_modes_upper_ball":str(modal),
                        "infinite_moment_enclosure":str(total)})
    mu=[arb(1)/2-A[0]/4,2*A[0]-A[1]/4,12*A[1]-A[2]/4,30*A[2]-A[3]/4]
    checks={"mu0_lower":mu[0]>arb('497/1000'),
            "mu0_upper":mu[0]<arb('249/500'),
            "mu2_lower":mu[1]>arb('287/12500'),
            "mu4_lower":mu[2]>arb('37/12500'),
            "mu4_upper":mu[2]<arb('593/200000'),
            "mu6_lower":mu[3]>arb('299/500000')}
    assert all(checks.values())
    numerator=15*mu[1]**2*mu[2]+3*mu[0]*mu[1]*mu[3]-10*mu[0]*mu[2]**2
    delta=numerator/(1440*mu[0]**3)
    assert numerator > 0 and delta > 0
    assert delta > arb('19/10000000000') and delta < arb('2/1000000000')
    return {"python_flint_version":flint.__version__,"precision_bits":bits,
            "modes":modes,"x_cutoff":cutoff,"analytic_branch_flag_forwarded":True,
            "is_lean_certificate":False,
            "trust_boundary":"Arb ball integration plus the stated analytic tail envelopes; not imported into Lean.",
            "tail_moments":records,"cosine_moment_enclosures":list(map(str,mu)),
            "rational_box_checks":checks,"numerator_enclosure":str(numerator),
            "delta2_enclosure":str(delta),
            "delta2_rational_interval":["19/10000000000","2/1000000000"]}


if __name__ == '__main__':
    p=argparse.ArgumentParser()
    p.add_argument('--bits',type=int,default=128)
    p.add_argument('--modes',type=int,default=3)
    p.add_argument('--cutoff',type=int,default=16)
    a=p.parse_args()
    print(json.dumps(main(a.bits,a.modes,a.cutoff),indent=2))
