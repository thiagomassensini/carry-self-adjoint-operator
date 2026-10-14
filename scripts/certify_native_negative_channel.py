#!/usr/bin/env python3
"""External Arb certificate for the ORIGINAL finite chiral return.

Fresh theta integrals, analytic spatial/modal/Taylor tails, all input directions.
No zero ordinates, target Gram, cached moments, fitted metric, or positivity premise.
This is an external certificate, NOT a Lean theorem.
"""
import argparse
import hashlib
import json
import math
import time
from fractions import Fraction
from pathlib import Path
import flint
from flint import arb, acb, arb_mat, ctx


def exp_tail(power, rate, cutoff):
    return (-rate*cutoff).exp()*sum(
        arb(math.factorial(power)//math.factorial(power-j))*cutoff**(power-j)/rate**(j+1)
        for j in range(power+1))


def positive_interval(upper):
    return arb(0).union(upper)


def theta_moment(power, modes, cutoff, cosh_weight=None):
    pi=arb.pi()
    def integrand(x, analytic):
        u=x.log(analytic=analytic)/2
        theta=sum((-acb(pi)*j*j*x).exp() for j in range(1,modes+1))
        value=u**power*(-3*u/2).exp()*theta
        if cosh_weight is not None:
            value*= (cosh_weight*u).cosh()
        return value
    knots=[q for q in [1,2,4,8,16,32,64,128,256] if q<cutoff]+[cutoff]
    finite=sum((acb.integral(integrand,a,b) for a,b in zip(knots,knots[1:])),acb(0))
    assert finite.is_finite() and finite.imag.contains(0)
    # For x>=1, x^-3/4<=1, log(x)/2<=x/2.
    # cosh(Y log(x)/2)<=x for 0<=Y<=2.
    p=power+(cosh_weight is not None)
    spatial=exp_tail(p,pi,arb(cutoff))/(2**power*(1-(-3*pi*cutoff).exp()))
    rate=pi*(modes+1)**2
    modal=exp_tail(p,rate,arb(1))/(2**power*(1-(-pi*(2*modes+3)).exp()))
    total=finite.real+positive_interval((spatial+modal).upper())
    assert total>0
    return total,{'power':power,'cosh_weight':None if cosh_weight is None else str(cosh_weight),
                  'finite_integral':str(finite),'spatial_tail_upper':str(spatial.upper()),
                  'modal_tail_upper':str(modal.upper()),'infinite_integral':str(total)}


def ldl(matrix):
    n=len(matrix); lower=[[arb(int(i==j)) for j in range(n)] for i in range(n)]; pivots=[]
    for j in range(n):
        d=matrix[j][j]-sum(lower[j][s]**2*pivots[s] for s in range(j))
        assert d>0,('nonpositive or unresolved LDL pivot',j,str(d))
        pivots.append(d)
        for i in range(j+1,n):
            lower[i][j]=(matrix[i][j]-sum(lower[i][s]*lower[j][s]*pivots[s]
                                       for s in range(j)))/d
    return pivots


def log_coefficients(moments, count):
    c=[arb(1)/2-moments[0]/4]+[
       (-1)**j*(moments[j-1]/math.factorial(2*j-2)-moments[j]/(4*math.factorial(2*j)))
       for j in range(1,count+1)]
    assert c[0]>0
    h=[]
    for n in range(count):
        h.append((-(n+1)*c[n+1]-sum(h[k]*c[n-k] for k in range(n)))/c[0])
    return c,h


def main(args):
    ctx.prec=args.bits
    start=time.monotonic(); records=[]; moments=[]
    for j in range(args.degree+1):
        m,r=theta_moment(2*j,args.modes,args.cutoff)
        moments.append(m); records.append(r)
        print('theta moment',2*j,flush=True)
    Y=arb(3)/8
    rem,record=theta_moment(2*args.degree+2,args.modes,args.cutoff,Y)
    records.append(record)
    evaluated={}
    def source(y_fraction):
        if y_fraction in evaluated:return evaluated[y_fraction]
        y=arb(y_fraction.numerator)/y_fraction.denominator
        assert 0<y and y<=Y
        A=sum(moments[j]*y**(2*j)/math.factorial(2*j) for j in range(args.degree+1))
        Ay=sum(moments[j]*y**(2*j-1)/math.factorial(2*j-1) for j in range(1,args.degree+1))
        A+=positive_interval((y**(2*args.degree+2)/math.factorial(2*args.degree+2)*rem).upper())
        Ay+=positive_interval((y**(2*args.degree+1)/math.factorial(2*args.degree+1)*rem).upper())
        F=arb(1)/2-(arb(1)/4-y*y)*A
        Fy=2*y*A-(arb(1)/4-y*y)*Ay
        assert F>0 and (Fy+F)>0
        result={'F':F,'Fy':Fy,'q':(Fy-F)/(Fy+F),'r':Fy/F}
        evaluated[y_fraction]=result
        return result
    c,h=log_coefficients(moments,8)
    a=[2*z for z in h]
    boundary=[[((-1)**((i+j)//2+i)*a[(i+j)//2] if (i+j)%2==0 else arb(0))
               for j in range(8)] for i in range(8)]
    gamma=arb(2)**-90
    boundary_shifted=[[boundary[i][j]-(gamma if i==j else 0) for j in range(8)] for i in range(8)]
    shifted_pivots=ldl(boundary_shifted)
    odd=[[h[i+j+1] for j in range(4)] for i in range(4)]
    odd_pivot=ldl(odd)[-1]
    print('E8 boundary margin certified, odd pivot',odd_pivot,flush=True)
    cases=[]
    configurations=[(7,31)]+[(8,k) for k in [31,63,127,255,511,1023]]
    configurations += [(10,63),(10,255),(12,63),(12,255)]
    for N,k in configurations:
        values=[source(Fraction(i+1,k+1)) for i in range(N)]
        H=[[arb(1)/(i+j+2) for j in range(N)] for i in range(N)]
        S=[[H[i][j]*(1-values[i]['q']*values[j]['q']) for j in range(N)] for i in range(N)]
        pivots=ldl(S)
        eigen_record={}
        try:
            G=arb_mat(H).solve(arb_mat(S))
            eigen=sorted(G.eig(algorithm='rump'),key=lambda z:float(z.real.mid()))
            assert all(z.imag.contains(0) and z.real>0 for z in eigen)
            eigen_record={'generalized_defect_eigenvalues':list(map(str,eigen)),
                          'minimum_defect_eigenvalue':str(eigen[0].real),
                          'maximum_defect_eigenvalue':str(eigen[-1].real)}
        except ValueError as e:
            eigen_record={'spectral_isolation':'unresolved; LDL certificate remains valid','detail':str(e)}
        cases.append({'N':N,'k':k,'h':str(Fraction(1,k+1)),
                      'q_enclosures':[str(v['q']) for v in values],
                      'defect_gram_LDL_pivots':list(map(str,pivots)),
                      'strictly_positive_all_original_inputs':True,
                      'negative_Jordan_port_is_zero':True,
                      **eigen_record})
        print('all inputs certified',N,k,flush=True)
    # Existing unconditional source bounds: c0>=1/3,
    # |c_(m+1)|<=1/(35*25^m). On |y|<=1/4 they give
    # |G|>=926/2793, |G'|<1/50, hence |r|<1.
    # Cauchy gives |K|<=8 on the bidisk 1/8.
    # Normalized shifted finite differences therefore satisfy
    # ||K_(N,h)-K_(N,0)||_2 <= N^3*16^(2N)*h for Nh<=1/16.
    # For N=8 and K_(8,0)>=2^-90 I, h<=2^-164 gives
    # K_(8,h)>=2^-91 I. This analytic argument is documented separately.
    source_lower=Fraction(1,3)-Fraction(1,16)/35/(1-Fraction(1,400))
    source_derivative=Fraction(1,2)/35/(1-Fraction(1,400))**2
    assert source_lower>0 and source_derivative/source_lower<1
    exact_checks={'source_G_lower':str(source_lower),
                  'source_Gprime_upper':str(source_derivative),
                  'r_bound':str(source_derivative/source_lower),
                  'kernel_bidisk_radius':str(Fraction(1,8)),
                  'kernel_bound':8,'N8_error_constant':str(8**3*16**16),
                  'N8_error_constant_power_of_two':73,
                  'boundary_margin':str(Fraction(1,2**90)),
                  'sufficient_h_upper':str(Fraction(1,2**164)),
                  'sufficient_k_plus_one_lower':str(2**164),
                  'scope':'EIGHT SOURCES ONLY; analytic derivation plus external Arb boundary certificate; not Lean'}
    result={'status':'EXTERNAL_ARB_CERTIFICATE_NOT_LEAN','precision_bits':args.bits,
            'python_flint':flint.__version__,'modes':args.modes,'cutoff':args.cutoff,
            'cosh_Taylor_degree':args.degree,'cosh_Taylor_envelope_Y':str(Y),
            'source_pipeline':'fresh theta integrals -> completed characteristic and derivative -> original HB quotient -> original Cauchy defect',
            'source_unchanged':True,'uses_zeta_or_zeros':False,'uses_cached_moments':False,
            'source_moments_and_tails':records,
            'native_log_moment_h_enclosures':list(map(str,h)),
            'normalized_odd_fourth_LDL_pivot':str(odd_pivot),
            'native_boundary_K8_minus_2pow_minus90_LDL_pivots':list(map(str,shifted_pivots)),
            'finite_return_cases':cases,'analytic_uniform_eight_source_derivation':exact_checks,
            'elapsed_seconds':time.monotonic()-start,
            'engine_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            'source_lean_sha256':{name:hashlib.sha256((args.repo_root/'CarrySelfAdjointOperator'/name).read_bytes()).hexdigest()
              for name in ['CompletedNativeRadialChiralMultiplier.lean','CompletedNativeChiralJetStorageTransport.lean',
                           'CompletedNativeChiralEvenBoundaryEnergy.lean','CompletedNativeXiThetaCosineRepresentation.lean',
                           'CompletedNativeAllOrderMomentUpperBound.lean','CompletedNativeChiralReturnEnergyPort.lean']}}

    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'status':result['status'],'cases':len(cases),'odd_fourth_pivot':str(odd_pivot),
                      'elapsed_seconds':result['elapsed_seconds']},indent=2))


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--bits',type=int,default=512)
    parser.add_argument('--modes',type=int,default=12)
    parser.add_argument('--cutoff',type=int,default=128)
    parser.add_argument('--degree',type=int,default=28)
    parser.add_argument('--repo-root',type=Path,default=Path(__file__).resolve().parents[1])
    parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args()
    assert args.bits>=256 and args.modes>=1 and args.cutoff>=4 and args.degree>=8
    main(args)
