#!/usr/bin/env python3
"""Cutoff experiment on the existing native camera stencils; no fitted target.
All cutoffs retain whole centers, both legs, seeds and the even antipodal end.
Large-cutoff coefficient formula is checked against the original lab builder.
"""
from pathlib import Path
import sys, json, math, hashlib, os
from fractions import Fraction
from concurrent.futures import ProcessPoolExecutor
import numpy as np
import mpmath as mp
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT/"source"))
import native_carry_primitive_real_operator_all_bases_fixed as native
import native_carry_collective_operator_lab as collective
CAMERAS=list(range(2,17))+[32,64]
TIMES=[0.,1.,7.,25.]
WINDOWS=[2**k for k in range(0,21)]
COUNTS=[2**k for k in range(0,19)]
COV_CAMERAS=list(range(2,9))
LAMBDAS=[complex(0,1),complex(3,2)]
def slope(b): return 4 if b==2 else b
def width(b): return 1 if b==2 else b//2
def factor(b,s):
    if b==2: return (1+2**(-s))*(1-2**(1-s))
    if b%2: return 1-b**(1-s)
    return 1+(b//2)**(-s)-(b+2)*b**(-s)
def profile(b,n):
    if b==2: return 1-(n%2==0).astype(np.int64)-2*(n%4==0)
    if b%2: return 1-b*(n%b==0).astype(np.int64)
    return 1+(n%(b//2)==0).astype(np.int64)-(b+2)*(n%b==0)
def coefficients(b,M,size):
    n=np.arange(1,size+1,dtype=np.int64)
    end=slope(b)*M+width(b)
    row=profile(b,n).astype(float)
    row[n>end]=0
    if b!=2 and b%2==0 and end<=size: row[end-1]-=1
    return row
def exact_gram(cams):
    G=np.zeros((len(cams),len(cams)))
    rational=[]
    for i,b in enumerate(cams):
        rr=[]
        for j,c in enumerate(cams):
            period=math.lcm(slope(b),slope(c))
            n=np.arange(period,dtype=np.int64)
            g=Fraction(int(np.dot(profile(b,n),profile(c,n)))*min(slope(b),slope(c)),period)
            G[i,j]=float(g); rr.append(str(g))
        rational.append(rr)
    return G,rational
def characteristic_job(b):
    ell,h=slope(b),width(b)
    largest=max(0,(max(WINDOWS)-h)//ell)
    centers=ell*np.arange(1,largest+1,dtype=float)
    output=[]
    for t in TIMES:
        s=.5+1j*t
        blocks=np.zeros(largest,dtype=np.complex128)
        amplitude=np.exp(-s*np.log(centers))
        for r in range(1,h+1):
            q=r/centers
            blocks+=amplitude*(np.expm1(-s*np.log1p(-q))+np.expm1(-s*np.log1p(q)))
        partial=np.concatenate(([0j],np.cumsum(blocks,dtype=np.clongdouble))).astype(np.complex128)
        for N in WINDOWS:
            M=max(0,(N-h)//ell)
            seeds=sum(r**(-s) for r in range(1,min(h,N)+1))
            raw=seeds+partial[M]
            af=factor(b,s)
            assert abs(af)>1e-9
            # Direct specialization of the existing (conservative) Lean bound.
            radii_sq=sum(r*r for r in range(1,h+1))
            bound=(2/3)*abs(s*(s+1))*radii_sq*M**(-1.5)/abs(af) if M else None
            output.append(dict(camera=b,t=t,physical_cutoff=N,complete_centers=M,
              seed_complete=N>=h,first_complete_center=ell+h,
              raw=[raw.real,raw.imag],normalized=[(raw/af).real,(raw/af).imag],
              factor=[af.real,af.imag],normalized_tail_bound_from_lean_formula=bound))
    return output
def covariance_job(args):
    M,z=args
    cams=COV_CAMERAS
    size=max(slope(b)*M+width(b) for b in cams)
    rows=np.stack([coefficients(b,M,size) for b in cams])
    logs=np.log(np.arange(1,size+1,dtype=float))
    weights=1/abs(z-logs)**2
    mass=float(weights[:M].sum())
    mean=float(np.dot(weights[:M],logs[:M])/mass)
    Gm=(rows*weights)@rows.T/mass
    # Same centered logarithmic first and second moments, no new Jacobi.
    yc=logs-mean
    Hm=(rows*(weights*yc))@rows.T/mass
    Jm=(rows*(weights*yc*yc))@rows.T/mass
    G,_=exact_gram(cams)
    e,U=np.linalg.eigh(G); W=(U*(1/np.sqrt(e)))@U.T
    corr=Gm/np.sqrt(np.outer(np.diag(Gm),np.diag(Gm)))
    T=np.diag(np.log([slope(b) for b in cams]))
    Aw=W@(Hm-Gm@T)@W
    out=dict(center_cutoff=M,resolvent=[z.real,z.imag],ambient_size=size,
      diagonal=np.diag(Gm).tolist(),correlation_3_5=float(corr[1,3]),
      unit_distance_sq_3_5=float(2-2*corr[1,3]),
      whitened_covariance_error=float(np.linalg.norm(W@Gm@W-np.eye(len(cams)),2)),
      covariance_error=float(np.linalg.norm(Gm-G,2)),
      return_singular_values=np.linalg.svd(Aw,compute_uv=False).tolist())
    return out
def validation():
    checks=[]
    for b in CAMERAS:
        for M in [1,2,7,31]:
            model=native.build_camera_model(b,M)
            size=slope(b)*M+width(b)
            original=collective.native_camera_row(model,size)
            fast=coefficients(b,M,size)
            assert np.array_equal(original,fast),(b,M)
            for t in [0.,7.]:
                x=np.arange(1,size+1)
                direct=original@np.exp(-(.5+1j*t)*np.log(x))
                # independently evaluate original seed + complete brackets
                f=lambda a: a**(-.5)*np.exp(-1j*t*np.log(a))
                raw=sum(f(np.arange(1,width(b)+1)))
                for m in range(1,M+1):
                    for r in range(1,width(b)+1):
                        raw+=f(slope(b)*m-r)-2*f(slope(b)*m)+f(slope(b)*m+r)
                assert abs(raw-direct)<3e-11,(b,M,t,raw,direct)
            checks.append([b,M])
    mp.mp.dps=60
    hp=[]
    for b in [2,8,64]:
        for t in [1.,25.]:
            s=mp.mpc(.5,t); M=31; ell,h=slope(b),width(b)
            exact=sum(mp.mpf(r)**(-s) for r in range(1,h+1))
            approx=sum(r**(-complex(s)) for r in range(1,h+1))
            for m in range(1,M+1):
                for r in range(1,h+1):
                    exact+=mp.mpf(ell*m-r)**(-s)-2*mp.mpf(ell*m)**(-s)+mp.mpf(ell*m+r)**(-s)
                    approx+=(ell*m)**(-complex(s))*(np.expm1(-complex(s)*np.log1p(-r/(ell*m)))+np.expm1(-complex(s)*np.log1p(r/(ell*m))))
            err=float(abs(exact-complex(approx)))
            assert err<3e-12,(b,t,err)
            hp.append(dict(camera=b,t=t,M=M,error=err))
    return dict(original_builder_exact_coefficient_checks=checks,mpmath_60_digit_checks=hp)
def main():
    check=validation()
    with ProcessPoolExecutor(max_workers=min(12,os.cpu_count() or 1)) as pool:
        char=[r for batch in pool.map(characteristic_job,CAMERAS) for r in batch]
        cov=list(pool.map(covariance_job,[(M,z) for z in LAMBDAS for M in COUNTS]))
    summary=[]
    for t in TIMES:
        for N in WINDOWS:
            rows=[r for r in char if r['t']==t and r['physical_cutoff']==N]
            vals=np.array([complex(*r['normalized']) for r in rows])
            raw=np.array([complex(*r['raw']) for r in rows])
            spread=float(np.max(abs(vals[:,None]-vals[None,:])))
            rawspread=float(np.max(abs(raw[:,None]-raw[None,:])))
            summary.append(dict(t=t,N=N,normalized_pairwise_spread=spread,raw_pairwise_spread=rawspread,
              normalized_energy_spread=float(np.ptp(abs(vals)**2))))
    out=dict(cameras=CAMERAS,times=TIMES,physical_cutoffs=WINDOWS,
      reference="Native camera-3 factorization only; no external target, zeros or zeta",
      finite_proof_status="Numerical evidence. Convergence theorems are separately audited in Lean.",
      validation=check,resultants=char,covariances=cov,spread=summary,
      covariance_cameras=COV_CAMERAS,exact_gram=exact_gram(COV_CAMERAS)[1],
      sources_sha256={p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in (ROOT/'source').glob('*.py')})
    (ROOT/'cutoff_results.json').write_text(json.dumps(out,indent=2)+'\n')
    import matplotlib
    matplotlib.use('Agg')
    import matplotlib.pyplot as plt
    plt.rcParams.update({'font.size':10})
    fig,axs=plt.subplots(2,2,figsize=(12,8),constrained_layout=True)
    for b in [2,3,5,8,16,64]:
        r=[r for r in char if r['camera']==b and r['t']==0.]
        axs[0,0].plot([x['physical_cutoff'] for x in r],[abs(complex(*x['raw'])) for x in r],label=f'C{b}',marker='.',lw=1)
        axs[0,1].plot([x['physical_cutoff'] for x in r],[complex(*x['normalized']).real for x in r],label=f'C{b}',marker='.',lw=1)
    for ax in axs[0]: ax.set_xscale('log',base=2);ax.set_xlabel('Corte físico N; apenas centros completos');ax.legend(ncol=3)
    axs[0,0].set_title('Resultantes brutas: limites dependem da câmera (t=0)')
    axs[0,0].set_ylabel('|χ_b,N|')
    axs[0,1].set_title('Após o fator geométrico: mesmo escalar (t=0)')
    axs[0,1].set_ylabel('Re(χ_b,N / A_b)')
    for t in TIMES:
        r=[r for r in summary if r['t']==t]
        axs[1,0].loglog([x['N'] for x in r],[x['normalized_pairwise_spread'] for x in r],label=f't={t:g}')
    axs[1,0].set_title('Maior diferença normalizada entre as 17 câmeras')
    axs[1,0].set_xlabel('Corte físico N');axs[1,0].set_ylabel('Diferença absoluta');axs[1,0].legend()
    for z in LAMBDAS:
        r=[r for r in cov if r['resolvent']==[z.real,z.imag]]
        axs[1,1].semilogx([x['center_cutoff'] for x in r],[x['unit_distance_sq_3_5'] for x in r],label=f'λ={z}')
    axs[1,1].axhline(2,color='black',ls='--',label='Limite exato = 2')
    axs[1,1].set_title('Câmeras 3 e 5 unitárias: distância² não vai a zero')
    axs[1,1].set_xlabel('Centros completos M por câmera');axs[1,1].set_ylabel('2 − 2 correlação');axs[1,1].legend()
    for ax in axs.flat: ax.grid(alpha=.25)
    fig.suptitle('Platôs e limites das câmeras — mesmo escalar, geometria preservada')
    fig.savefig(ROOT/'camera_cutoff_convergence.png',dpi=170)
    fig.savefig(ROOT/'camera_cutoff_convergence.pdf')
    print(json.dumps(dict(final_spread=[r for r in summary if r['N']==max(WINDOWS)],
      final_covariance=[r for r in cov if r['center_cutoff']==max(COUNTS)]),indent=2))
if __name__=='__main__': main()
