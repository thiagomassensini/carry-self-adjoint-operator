"""New finite calculations using copied native graph/Green definitions."""
from pathlib import Path
import sys,json,hashlib
import numpy as np
import sympy as sp
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT/'source_labs'))
import native_carry_pythagorean_green_measure_lab as pyth
import native_carry_quadratic_weighted_green_atlas_lab as green
import native_carry_pythagorean_node_weyl_colligation_lab as node
import native_carry_primitive_real_operator_all_bases_fixed as native
import native_carry_collective_operator_lab as collective

def moments(V,u,count=8):
    v=u.copy(); out=[]
    for k in range(count):
        out.append(float(u@v)); v=V@v
    return out
def inv(ms): return [ms[0]**(k-1)*ms[k]/ms[1]**k for k in range(2,len(ms))]

def main():
    polarized=[]
    for cutoff in (4,8,16):
        models=[native.build_camera_model(c,cutoff) for c in (2,3,4)]
        C,size=collective.native_readout_matrix(models)
        coll=node.normalized_colligation(size);E=coll['endpoint'];P=coll['poisson']
        G=np.eye(E.shape[0])+P.T@P
        ell=np.log(np.arange(1,size+1));z=0.4+1.3j;w=1.7+0.8j
        rz=1/(z-ell);rw=1/(w-ell)
        Sz=(C*rz)@E.T;Sw=(C*rw)@E.T
        K=Sz@G@Sw.conj().T
        direct=(C*(rz*rw.conjugate()))@C.T
        Bz=(C*rz)@C.T;Bw=(C*rw)@C.T
        polarized.append({'cutoff':cutoff,'state_size':size,'endpoint_size':E.shape[0],
          'metric_isometry_residual':float(np.linalg.norm(E.T@G@E-np.eye(size),2)),
          'polarized_covariance_residual':float(np.linalg.norm(K-direct,2)),
          'division_free_resolvent_residual':float(np.linalg.norm((w.conjugate()-z)*K-(Bz-Bw.conj().T),2)),
          'identity':'(conj(w)-z) Sz G Sw* = Bz-Bw*; Bz=C(z-L)^-1 C*',
          'spectral_parameter_distinct_from_native_time':True})
    rows=[]
    for size in (8,16,32,64,128,256):
        E,B,meta=pyth.build_analyses(size)
        F=E.T@E+B.T@B
        vals,vecs=np.linalg.eigh(F)
        Fhalf=(vecs*np.sqrt(vals))@vecs.T
        Finvhalf=(vecs/np.sqrt(vals))@vecs.T
        En=E@Finvhalf;Bn=B@Finvhalf;V=Bn.T@Bn
        Pl=Bn@np.linalg.solve(En.T@En,En.T)
        cases=[]
        for seed in (1,4):
            e=np.eye(size)[:,seed-1]
            for name,u in [('normalized_coordinate',e),('original_geometry_seed',Fhalf@e)]:
                ms=moments(V,u)
                cases.append({'seed':seed,'source':name,'moments':ms,'invariants':inv(ms)})
        rows.append({'size':size,'V':'F^-1/2 B*B F^-1/2; S=sqrt(V)',
          'V_min_eigenvalue':float(np.linalg.eigvalsh(V)[0]),'V_max_eigenvalue':float(np.linalg.eigvalsh(V)[-1]),
          'frame_error':float(np.linalg.norm(En.T@En+V-np.eye(size),2)),
          'poisson_left_inverse_error':float(np.linalg.norm(Pl@En-Bn,2)),
          'cases':cases})
    # Weighted curvature B*B is rational although B itself contains sqrt(2).
    J=20;size=2*J+1;V=sp.zeros(size)
    for j in range(1,J+1):
        n=2*j;power=0
        while n%2==0:power+=1;n//=2
        weight=sp.Rational(1,2**power)
        row=sp.zeros(size,1)
        row[2*j-2]=1;row[2*j-1]=-2;row[2*j]=1
        V+=weight**2/2*(row*row.T)
    curvature=[]
    for seed in (1,2,3,4):
        u=sp.eye(size)[:,seed-1];v=u;ms=[]
        for k in range(8):ms.append((u.T*v)[0]);v=V*v
        invariants=[ms[0]**(k-1)*ms[k]/ms[1]**k for k in range(2,len(ms))]
        curvature.append({'seed':seed,'moments':[str(x) for x in ms],'invariants':[str(x) for x in invariants],
          'invariants_decimal':[float(x) for x in invariants],
          'cutoff_independence':'Exact first eight moments: supports stay away from final boundary; finite propagation proves same infinite moments.'})
    payload={'polarized_return_metric':polarized,'pythagorean_bulk_observable':rows,
      'C2_curvature_energy':{'V':'B*C2 B_C2','S':'positive square root of V','bound':'||S||<=sqrt(2) from weighted second difference bound','cells':J,'cases':curvature},
      'C2_fully_normalized_bulk':{'algebraic_result':'If T=[B;Tr] is square invertible, O=T(T*T)^-1/2 is unitary. Therefore (B(T*T)^-1/2)* B(T*T)^-1/2 is an orthogonal projection.','consequence':'For this chosen observable, all positive powers agree; shifted Gram rank<=1. This is not an obstruction to the unnormalized curvature energy or another enriched observable.'},
      'scope':'All sources and operators chosen from explicit geometric maps before numerical native comparison; no identity with native characteristic asserted. Float matrices provide finite evidence; exact curvature moments use rational arithmetic.'}
    (ROOT/'geometric_operator_checks.json').write_text(json.dumps(payload,indent=2)+'\n')
    print('Polarized errors',polarized)
    for r in rows:
        print('Green',r['size'],r['V_max_eigenvalue'],[(c['seed'],c['source'],c['invariants'][:2]) for c in r['cases']])
    print('C2 exact',[(c['seed'],c['invariants'][:2]) for c in curvature])
if __name__=='__main__':main()
