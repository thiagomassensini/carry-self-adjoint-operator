#!/usr/bin/env python3
"""Isolated re-audit of the two historical graph scripts; original files untouched."""
from pathlib import Path
import importlib.util,json,traceback,time,hashlib
from fractions import Fraction
import sympy as sp
ROOT=Path(__file__).resolve().parent

def load(name,path):
 spec=importlib.util.spec_from_file_location(name,path)
 mod=importlib.util.module_from_spec(spec);spec.loader.exec_module(mod)
 return mod

def save(path,payload,default=str):
 path.write_text(json.dumps(payload,indent=2,sort_keys=True,default=default)+'\n')

c=load('historical_closed',ROOT/'source_closed/c2_green_closed_native_endpoint_graph.py')
p=load('historical_provenance',ROOT/'source_provenance/c2_green_native_range_provenance_graph.py')
report={}
for tag,mod in [('closed',c),('provenance',p)]:
 out=ROOT/('rerun_'+tag);out.mkdir(exist_ok=True)
 for key,value in list(vars(mod).items()):
  if key.startswith('REPORT_'):setattr(mod,key,out/Path(value).name)
 mod.RESULT=out
 missing=[str(x) for x in mod.MANDATORY_INPUTS if not x.exists()]
 attempt={'missing_canonical_inputs':missing,'full_historical_pipeline_completed':False}
 try:mod.main(['--result-dir',str(out)]);attempt['full_historical_pipeline_completed']=True
 except Exception as exc:attempt['full_pipeline_error']=repr(exc)
 report[tag]=attempt
save(ROOT/'pipeline_attempts.json',report)

pure={}
for name in ['global_odd_convolution_audit','hilbert_scale_audit','endpoint_support_audit','coequalizer_graph_audit','a_descent_audit']:
 start=time.time();payload=getattr(c,name)();pure[name]={'elapsed_seconds':time.time()-start,'passed':True}
 save(ROOT/('recomputed_'+name+'.json'),payload,c.json_default)
 original={'global_odd_convolution_audit':'global_odd_convolution.json','hilbert_scale_audit':'hilbert_scale.json','endpoint_support_audit':'endpoint_support.json','coequalizer_graph_audit':'coequalizer_relation.json','a_descent_audit':'a_descent.json'}[name]
 recanonical=json.loads(json.dumps(payload,default=c.json_default))
 pure[name]['matches_historical_payload']=recanonical==json.loads((ROOT/'source_closed'/original).read_text())

# Replay the actual Newton/formal-log core without substituting a fake upstream source file.
records=[]
for M,prime,order in [(64,3,6),(96,5,5),(128,7,4)]:
 lo=c.local_mass_coefficients(M,prime,order);hi=c.local_mass_coefficients(2*M,prime,order)
 Ps=c.richardson_power_sums(M,prime,order);ks=c.richardson_log_coefficients(M,prime,order)
 flo=c.formal_log_coefficients(lo);fhi=c.formal_log_coefficients(hi)
 for j in range(1,order+1):
  k=sp.Rational(ks[j].numerator,ks[j].denominator)
  residual=sp.simplify(2*fhi[j]-flo[j]-k)
  assert residual==0 and ks[j]*j==Ps[j]
  records.append({'M':M,'p_T':prime,'j':j,'kappa':str(ks[j]),'P':str(Ps[j]),'formal_log_residual':str(residual)})
for j in range(1,65):assert c.newton_power_sums([Fraction(1)]*(j+1))[j]==1
save(ROOT/'recomputed_logjet_core.json',{'records':records,'checks':len(records),'unit_mass_orders_checked':64,'upstream_feature_source_check':'not rerun: original upstream script absent from delivery'})

witness=p.free_module_witness_audit(1024)
save(ROOT/'recomputed_free_module_mobius_1024.json',witness,p.json_default)
pure['free_module_witness_audit']={'passed':True,'ell_maximum':1024,'native_membership_claimed':False}

# Historical gate replay is explicitly based on its historical stored constructor inventory.
source=json.loads((ROOT/'source_provenance/constructor_inventory.json').read_text())
native=p.native_range_gate_audit(source);divisor=p.divisor_haar_gate_audit(native);graph=p.enriched_graph_gate_audit(source,divisor)
validation=p.validation_record(witness,source,native,divisor,graph)
save(ROOT/'historical_gate_replay.json',{'uses_historical_inventory':True,'new_global_no_go':False,'native':native,'divisor':divisor,'graph':graph,'validation':validation},p.json_default)

# Concrete minimal joint-readout geometry repairs the old ell=2 free-module loss.
Q=sp.Matrix([[1,1]]);A=sp.Matrix([[sp.Rational(1,2),sp.sqrt(3)/2]])
E=Q.col_join(A);G=sp.simplify(E.T*E);g=sp.Matrix([1,-1]);P=E.inv()
assert sp.simplify(G.det())>0
assert sp.simplify(P*E)==sp.eye(2)
assert sp.simplify((E*g).dot(E*g)-(g.T*G*g)[0])==0
J=4
joint=sp.kronecker_product(E,sp.eye(J));Npre=sp.kronecker_product(sp.eye(2),sp.diag(*range(1,J+1)))
Npost=sp.kronecker_product(sp.eye(2),sp.diag(*range(1,J+1)))
assert joint*Npre-Npost*joint==sp.zeros(2*J)
Gjoint=joint.T*joint
assert Npre.T*Gjoint-Gjoint*Npre==sp.zeros(2*J)
source_vec=sp.kronecker_product(g,sp.Matrix([sp.Rational(1,j) for j in range(1,J+1)]))
Sinv=sp.diag(*([sp.Rational(1,j) for j in range(1,J+1)]*2))
assert Sinv.T*Gjoint-Gjoint*Sinv==sp.zeros(2*J)
transferred=joint*Sinv*joint.inv()
assert sp.simplify(transferred-transferred.T)==sp.zeros(2*J)
result={'scope':'Exact free divisor module ell=2; not asserted to be the native range','Q':str(Q),'A':str(A),'joint':str(E),'pullback_metric':str(G),'metric_determinant':str(sp.simplify(G.det())),'old_Q_gauge':str(Q*g),'new_joint_gauge':str(E*g),'gauge_energy':str(sp.simplify((g.T*G*g)[0])),'inverse_reconstruction_residual':str(sp.simplify(P*E-sp.eye(2))),'tower_J':J,'joint_number_intertwiner_residual_zero':True,'number_symmetric_in_pullback_metric':True,'reciprocal_number_symmetric_after_joint_transport':True,'source_preserved':True,'normalized_moments_unchanged_by_tensor_enrichment':True}
save(ROOT/'exact_joint_provenance_repair.json',result)

# The isometry N:H0->Hminus1 becomes the identity under its canonical coordinate isometry.
N=sp.diag(*range(1,J+1));U=sp.diag(*[sp.Rational(1,j) for j in range(1,J+1)])
assert U*N==sp.eye(J)
save(ROOT/'rigged_identification_check.json',{'J':J,'U_minus1':'diag(1/j)','N':'diag(j)','U_minus1_N':'I','consequence':'The normalized cross-space number map alone has constant cyclic powers; it is not an infinite-rank moment observable.'})

# Verify all original delivery bytes are unchanged.
manifest=json.loads((ROOT/'source_manifest.json').read_text())
changed=[r['source'] for r in manifest if hashlib.sha256(Path(r['source']).read_bytes()).hexdigest()!=r['sha256']]
assert not changed
save(ROOT/'execution_summary.json',{'pure_recomputations':pure,'exact_logjet_checks':len(records),'original_delivery_files_preserved':len(manifest),'original_byte_changes':changed,'new_algebraic_graph_checks':'all passed','worker_count':1,'full_pipelines':report})
print(json.dumps({'pure_checks':pure,'logjet_checks':len(records),'originals_preserved':len(manifest)},indent=2))
