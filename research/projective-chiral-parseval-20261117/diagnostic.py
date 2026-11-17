#!/usr/bin/env python3
"""Numerical, non-interval canaries for native Cauchy/Pick radial defect.
Not an implementation of the physical C2/TFVD source-to-Cauchy map.
"""
import json
from pathlib import Path
import mpmath as m
m.mp.dps=130
I=m.j

def L(z):
    s=m.mpf("0.5")+I*z
    return I*(1/s+1/(s-1)-m.log(m.pi)/2+m.digamma(s/2)/2 +
              m.zeta(s,derivative=1)/m.zeta(s))
def q(z):
    l=L(z)
    return (-l-I)/(-l+I)
def amplitude(z):
    return (-L(z)+I)/m.sqrt(2)
def R(z):
    return -L(z)/2
def sample(k,n):
    z=[I*m.mpf(i+1)/(k+1) for i in range(n)]
    qs=[q(v) for v in z]
    aa=[amplitude(v) for v in z]
    D=m.matrix(n);K=m.matrix(n)
    for i in range(n):
        for j in range(n):
            D[i,j]=m.mpf(k+1)/(i+j+2)*(1-m.conj(qs[i])*qs[j])
            K[i,j]=(R(z[j])-R(m.conj(z[i])))/(z[j]-m.conj(z[i]))
    err=max(abs(K[i,j]-m.conj(aa[i])*aa[j]*D[i,j]/2)
            for i in range(n) for j in range(n))
    eig=m.eighe(D,eigvals_only=True)
    return {"k":k,"n":n,"min_eigenvalue":m.nstr(eig[0],25),
            "max_eigenvalue":m.nstr(eig[n-1],25),
            "min_positive":bool(eig[0]>0),
            "max_congruence_error":m.nstr(err,10),
            "max_abs_chiral_quotient":m.nstr(max(abs(t) for t in qs),18)}
if __name__=="__main__":
    a={"precision_dps":m.mp.dps,
       "identity":"K_ij=conj(amplitude_i)*amplitude_j*D_ij/2",
       "status":"NUMERICAL, not certified or all-order",
       "cases":[sample(k,n) for k,n in [(12,3),(32,4),(64,6),(80,8),(100,10)]]}
    out=json.dumps(a,indent=2)
    print(out)
    Path(__file__).with_name("numerical-results.json").write_text(out+"\n")
