#!/usr/bin/env python3
"""Fresh theta quadrature checks of the native reference; no spectral input."""
import concurrent.futures as cf
import json, time, sys, hashlib
from pathlib import Path
import mpmath as mp
BASE=Path(__file__).resolve().parent
sys.path.insert(0,str(BASE/"source"))
import native_carry_adaptive_height_spectrum as native

def one(task):
    k,dps=task
    # Independent integration coordinates x=log(original theta variable)/2.
    # A_k = 2^(2k+1) integral psi(exp(2x))*exp(x/2)*x^(2k) dx.
    mp.mp.dps=dps
    tol=mp.mpf(10)**(-dps-15)
    U=native._integration_ceiling(k,dps)/2
    def fun(x):
        return 2**(2*k+1)*native._theta_kernel(2*x,tol)*mp.exp(x/2)*x**(2*k)
    value=mp.quad(fun,[0,mp.mpf(".25"),mp.mpf(".5"),1,2,U])
    return k,dps,mp.nstr(value,dps+8)

def main():
    start=time.time()
    ref=json.loads((BASE/"reference/native_moments.json").read_text())
    tasks=[(k,dps) for dps in [90,150] for k in range(17)]
    with cf.ProcessPoolExecutor(max_workers=24) as pool:
        results=list(pool.map(one,tasks))
    mp.mp.dps=200
    rows=[]
    for k,dps,value in results:
        expected=mp.mpf(ref["theta_even_moments"][k])
        err=abs(mp.mpf(value)/expected-1)
        rows.append({"k":k,"dps":dps,"value":value,"relative_error_vs_cache":mp.nstr(err,12),"relative_digits_vs_cache":float(-mp.log10(err)) if err else None})
    f90=native.completed_even_coefficients(16,[mp.mpf(next(v for k,d,v in results if k==j and d==90)) for j in range(17)])
    f150=native.completed_even_coefficients(16,[mp.mpf(next(v for k,d,v in results if k==j and d==150)) for j in range(17)])
    h90=native.logarithmic_moments(f90,16)
    h150=native.logarithmic_moments(f150,16)
    checks=[]
    for k in range(16):
        expected=mp.mpf(ref["h"][k])
        checks.append({"k":k,"digits_90_vs_cache":float(-mp.log10(abs(h90[k]/expected-1))),"digits_150_vs_cache":float(-mp.log10(abs(h150[k]/expected-1)))})
    report={"elapsed_seconds":time.time()-start,"workers":24,"method":"Fresh quadrature in half-log coordinate at 90 and 150 digits; same positive theta sum, cache is not read by workers","theta":rows,"native_h":checks,"scope":"Numerical reproduction with independent quadrature, not interval proof."}
    (BASE/"reference/quadrature_validation.json").write_text(json.dumps(report,indent=2)+"\n")
    print(json.dumps({"elapsed_seconds":report["elapsed_seconds"],"theta_min_digits":min(r["relative_digits_vs_cache"] for r in rows if r["relative_digits_vs_cache"] is not None),"h_min_digits90":min(r["digits_90_vs_cache"] for r in checks),"h_min_digits150":min(r["digits_150_vs_cache"] for r in checks)},indent=2))
if __name__=="__main__":main()
