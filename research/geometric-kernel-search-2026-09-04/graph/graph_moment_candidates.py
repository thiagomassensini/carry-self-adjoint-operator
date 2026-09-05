"""Geometrically defined diagonal candidates; never fitted to native h.

Euler--Maclaurin tails are computed from derivatives with exact integer
coefficients. For a completely monotone f, the analytic remainder after
corrections r=1,...,m-1 has magnitude <= |B_(2m)|/(2m)! |f^(2m-1)(N)|.
Floating arithmetic is NOT interval arithmetic; that remainder bound controls
truncation only. Independent N and precision runs check numerical stability.
"""
from pathlib import Path
import json, hashlib
import mpmath as mp
import sympy as sp

ROOT = Path(__file__).resolve().parent

def log_tail(q, N, m):
    logN = mp.log(N)
    tail = logN**(1-q)/(q-1) + 1/(2*mp.mpf(N)*logN**q)
    coeff = [1]
    remainder = None
    for r in range(1, 2*m):
        nxt = [r*c for c in coeff] + [0]
        for j,c in enumerate(coeff):
            nxt[j+1] += (q+j)*c
        coeff = nxt
        if r % 2:
            derivative_abs = mp.fsum(mp.mpf(c)*logN**(-q-j) for j,c in enumerate(coeff))*mp.mpf(N)**(-r-1)
            bernoulli = mp.bernoulli(r+1)/mp.factorial(r+1)
            correction = bernoulli*derivative_abs
            if r == 2*m-1:
                remainder = abs(correction)
            else:
                tail += correction
    return tail,remainder

def log_moments(N,m,dps,count=8):
    with mp.workdps(dps):
        result=[]; errors=[]
        for k in range(count):
            q=2*k+2
            finite=mp.fsum(1/(mp.mpf(n)*mp.log(n)**q) for n in range(2,N))
            tail,bound=log_tail(q,N,m)
            result.append(finite+tail); errors.append(bound)
        return result,errors

def power_sum(q,N=512,m=64):
    tail=mp.mpf(N)**(1-q)/(q-1)+mp.mpf(N)**(-q)/2
    for r in range(1,m):
        tail += mp.bernoulli(2*r)/mp.factorial(2*r)*mp.rf(q,2*r-1)*mp.mpf(N)**(-q-2*r+1)
    bound=abs(mp.bernoulli(2*m)/mp.factorial(2*m)*mp.rf(q,2*m-1)*mp.mpf(N)**(-q-2*m+1))
    return mp.fsum(mp.mpf(n)**(-q) for n in range(1,N))+tail,bound

def invariants(moments):
    return [moments[0]**(k-1)*moments[k]/moments[1]**k for k in range(2,len(moments))]

def strings(xs,digits=100): return [mp.nstr(x,digits) for x in xs]

def main():
    mp.mp.dps=160
    ref_path=ROOT.parent/'reference/native_moments.json'
    ref=json.loads(ref_path.read_text()); native=[mp.mpf(x) for x in ref['h'][:8]]
    log_a, err_a=log_moments(256,48,120)
    log_b, err_b=log_moments(512,64,160)
    tower_pairs=[power_sum(2*k+2) for k in range(8)]
    tower=[x[0] for x in tower_pairs]
    candidates=[
        {'name':'inverse_log_n_with_critical_regularized_source',
         'S':'diag(1/log n), n>=2','u':'1/(sqrt(n)*log n)',
         'moments':strings(log_b),'invariants':strings(invariants(log_b)),
         'uniform_operator_bound':'1/log 2',
         'Neumann_domain':'abs(t)<log 2',
         'truncation_remainder_bounds':strings(err_b),
         'first_run':{'N':256,'m':48,'dps':120,'moments':strings(log_a),'bounds':strings(err_a)},
         'second_run':{'N':512,'m':64,'dps':160},
         'relative_independent_run_discrepancy':strings([abs(a-b)/abs(b) for a,b in zip(log_a,log_b)]),
         'provenance':'Chosen regularization of carry amplitude by inverse log clock; not an existing native-readout theorem.'},
        {'name':'inverse_tower_clock_unit_mass',
         'S':'diag(1/j), j>=1','u':'1/j',
         'moments':strings(tower),'invariants':strings(invariants(tower)),
         'truncation_remainder_bounds':strings([x[1] for x in tower_pairs]),
         'uniform_operator_bound':'1','Neumann_domain':'abs(t)<1',
         'provenance':'h_j=1/j occurs explicitly in old endpoint graph. S=N^-1 is the candidate spectral observable.'}]
    for p in (3,5,7):
        count=1200
        variants=[('inverse_tower_clock_critical_source',lambda j,k:mp.mpf(p)**(-j)*mp.mpf(j)**(-2*k-2)),
                  ('critical_semigroup_unit_mass_source',lambda j,k:mp.mpf(p)**(-j*k)*mp.mpf(j)**(-2)),
                  ('critical_semigroup_critical_source',lambda j,k:mp.mpf(p)**(-j*(k+1))*mp.mpf(j)**(-2))]
        for name,term in variants:
            ms=[mp.fsum(term(j,k) for j in range(1,count+1)) for k in range(8)]
            if name=='critical_semigroup_unit_mass_source': ms[0]=tower[0]
            candidates.append({'name':name,'base':p,'moments':strings(ms),'invariants':strings(invariants(ms)),
                'summation_cutoff':count,'geometric_tail_bound':mp.nstr(mp.mpf(p)**(-count)/(p-1),30),
                'definition':('S_j=1/j, u_j=p^(-j/2)/j' if name.startswith('inverse') else 'S_j=p^(-j/2), '+('u_j=1/j' if 'unit_mass' in name else 'u_j=p^(-j/2)/j'))})
    for c in candidates:
        inv=[mp.mpf(x) for x in c['invariants']]
        c['inv2_relative_error_to_native']=mp.nstr(inv[0]/invariants(native)[0]-1,30)
        c['inv3_relative_error_to_native']=mp.nstr(inv[1]/invariants(native)[1]-1,30)
    # Rational finite identity; no spectral data enter this exact calculation.
    x,z=sp.Rational(1,7),sp.Rational(2,11)
    w=[sp.Rational(1,j*j) for j in range(1,9)]
    v=w[:]
    response=lambda t: t*sum(a/(1-t*t*b) for a,b in zip(w,v))
    kernel=sum(a*(1+x*z*b)/((1-x*x*b)*(1-z*z*b)) for a,b in zip(w,v))
    moments=[sum(a*b**k for a,b in zip(w,v)) for k in range(10)]
    grams=[]
    for size in range(1,5):
        for shift in (0,1):
            determinant=sp.Matrix(size,size,lambda i,j:moments[i+j+shift]).det()
            assert determinant>0
            grams.append({'size':size,'shift':shift,'determinant':str(determinant)})
    exact={'size':8,'x':str(x),'z':str(z),'division_free_polarized_residual':str(sp.factor((z-x)*kernel-response(z)+response(x))),
           'gram_determinants':grams}
    payload={'working_dps':160,'native_reference_sha256':hashlib.sha256(ref_path.read_bytes()).hexdigest(),
             'native_invariants':strings(invariants(native)),
             'candidates':candidates,'exact_finite_kernel_test':exact,
             'scope':'Each candidate is defined before comparison. A failed scale-free invariant rules out matching all moments by a scalar source normalization and one spectral dilation. It does not rule out different observables or richer geometry. No primes or zero ordinates supplied the native reference here.'}
    (ROOT/'geometric_diagonal_candidates.json').write_text(json.dumps(payload,indent=2)+'\n')
    for c in candidates: print(c['name'],c.get('base',''),c['invariants'][0][:35],c['invariants'][1][:35],c['inv2_relative_error_to_native'])
    print('native',strings(invariants(native)[:2],35))
    print('log EM max run discrepancy',max(abs(a-b)/abs(b) for a,b in zip(log_a,log_b)))

if __name__=='__main__':main()
