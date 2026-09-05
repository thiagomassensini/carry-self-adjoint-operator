#!/usr/bin/env python3
"""Comparison only. Moment mass/mean normalization is diagnostic, not geometric fitting."""
import json, math
from pathlib import Path
BASE=Path(__file__).resolve().parent.parent
a=json.loads((BASE/'candidates/carry_candidates.json').read_text())
ref=json.loads((BASE/'reference/native_moments.json').read_text())
h=[float(v) for v in ref['h'][:13]]
c=[(v/h[0])/((h[1]/h[0])**k) for k,v in enumerate(h)]
rows=[]
for r in a['results']:
 if r.get('N') not in (512,4096,None):continue
 ri=dict(r); inv=r['scale_free_moments'];err=[inv[k]/c[k]-1 for k in range(2,min(len(c),len(inv)))]
 ri['scale_free_relative_error_orders_2_to_12']=err
 ri['rms_log_error_orders_2_to_12']=math.sqrt(sum(math.log1p(e)**2 for e in err)/len(err))
 ri['raw_moment_relative_error_orders_0_to_12']=[m/hn-1 for m,hn in zip(r['moments'],h)]
 ri['diagnostic_only_mass_multiplier']=h[0]/r['mass'];ri['diagnostic_only_observable_multiplier']=(h[1]/h[0])/r['mean']
 if r['family']=='analysis_gram': vb=(1/r['q']+2+r['q'])**2
 elif r['family'] in ('synthesis_gram','green_gram'): vb=(r['q']/(1-r['q'])**2)**2
 elif r['family']=='depth_inverse_logcell_square': vb=1/math.log(2)**2
 else: vb=1.0
 ri['observable_norm_upper_bound']=vb; ri['normalized_neumann_radius_lower_bound']=math.sqrt(r['mean']/vb)
 def kernel(seq,x,z,order):return sum(seq[n]*sum(x**j*z**(2*n-j) for j in range(2*n+1)) for n in range(order+1))
 ri['diagnostic_normalized_kernel_comparison']=[{'x':x,'z':z,'within_candidate_neumann_bound':max(abs(x),abs(z))<ri['normalized_neumann_radius_lower_bound'],'candidate_order12':kernel(inv,x,z,12),'native_order12':kernel(c,x,z,12),'relative_error':kernel(inv,x,z,12)/kernel(c,x,z,12)-1,'candidate_12_minus_8':kernel(inv,x,z,12)-kernel(inv,x,z,8)} for x,z in [(0,.05),(.02,.07),(-.05,.09),(.1,.1)]]
 rows.append(ri)
rows.sort(key=lambda r:r['rms_log_error_orders_2_to_12'])
lookup={(r['family'],r.get('base'),r.get('source'),r.get('N')):r for r in a['results']}
conv=[]
for r in rows:
 if r.get('N')!=512:continue
 k=(r['family'],r.get('base'),r.get('source'))
 e={}
 for n in (64,128,256):
  p=lookup[(*k,n)]
  e[str(n)]=max(abs(x/y-1) for x,y in zip(p['moments'],r['moments']))
 conv.append({'family':k[0],'base':k[1],'source':k[2],'maximum_relative_moment_error_to_N512':e})
out={'schema':'carry-geometric-candidate-comparison-v1','status':'numerical_diagnostic_no_proof','reference':str(BASE/'reference/native_moments.json'),'target_scale_free_moments':c,'ranking_metric':'RMS log ratio for scale-free moment orders2..12; normalizing mass and mean is diagnostic only','kernel_note':'Truncated moment series on normalized mass/mean coordinates, with order12-minus-order8 recorded; not a rigorous tail bound','ranked_candidates':rows,'cutoff_comparison':conv}
(BASE/'candidates/comparison.json').write_text(json.dumps(out,indent=2))
for r in rows[:15]:
 print(r['family'],r.get('base'),r.get('source'), 'logerr',round(r['rms_log_error_orders_2_to_12'],6),'c2-4',[round(v,8) for v in r['scale_free_moments'][2:5]],'e2-4',[round(v,6) for v in r['scale_free_relative_error_orders_2_to_12'][:3]])
print('CUTOFF_MAX', {str(n):max(r['maximum_relative_moment_error_to_N512'][str(n)] for r in conv) for n in (64,128,256)})
