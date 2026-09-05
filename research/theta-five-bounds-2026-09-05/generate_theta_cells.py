#!/usr/bin/env python3
"""Generate kernel-checkable rational theta certificates using only Fraction arithmetic."""
from pathlib import Path
from fractions import Fraction as F
import json
import argparse
parser=argparse.ArgumentParser()
parser.add_argument("--output-directory", default="/tmp/theta-five-bounds-generated")
args=parser.parse_args()
N=128
src=Path(args.output_directory)
rs=json.loads((src/'nodes.json').read_text())
nodes={F(r['q']):r for r in rs}

def t(x):
    return f'({x.numerator}/{x.denominator}:ℝ)'

def lo(x):return F(nodes[x]['l'])
def hi(x):return F(nodes[x]['r'])
def name(x):return f"thetaFirstMode_node_{nodes[x]['id']:03d}"
imports=''.join('import CarrySelfAdjointOperator.ThetaMomentCertificateData.ThetaNodes%02d\n'%i for i in range(17))
header=imports+'import CarrySelfAdjointOperator.CompletedNativeThetaFirstModeQuadrature\n\nnamespace CarrySelfAdjointOperator\nnoncomputable section\nset_option maxHeartbeats 4000000\nset_option maxRecDepth 8192\n\n'
results={}
allcellfiles=[]
for p in [0,2,4,6]:
    ls=[];us=[]
    for j in range(N):
        a,b=F(j,N),F(j+1,N)
        mass=(b**(p+1)-a**(p+1))/(p+1)
        first=(b**(p+2)-a**(p+2))/(p+2)
        m=first/mass
        U=((b*hi(a)-a*hi(b))*mass+(hi(b)-hi(a))*first)/(b-a)
        us.append(U)
        group=j//32
        path=src/f'ThetaCells{p}_{group}.lean'
        if j%32==0:
            path.write_text(header)
            allcellfiles.append(path.stem)
        code=''
        if p<6:
            L=lo(m)*mass;ls.append(L)
            code+=f'''theorem thetaFirstMode_cell_lower_{p}_{j:03d} :
    {t(L)} ≤ ∫ x in {t(a)}..{t(b)}, x^{p}*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower {p} {t(a)} {t(b)} {t(m)} {t(lo(m))}
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) ({name(m)}).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

'''
        code+=f'''theorem thetaFirstMode_cell_upper_{p}_{j:03d} :
    (∫ x in {t(a)}..{t(b)}, x^{p}*thetaFirstMode x) ≤ {t(U)} := by
  have h := thetaFirstMode_weighted_cell_upper {p} {t(a)} {t(b)} {t(hi(a))} {t(hi(b))}
    (by norm_num) (by norm_num) ({name(a)}).2 ({name(b)}).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

'''
        with path.open('a') as f:f.write(code)
        if j%32==31:
            with path.open('a') as f:f.write('end\nend CarrySelfAdjointOperator\n')
    results[p]={'L':sum(ls),'U':sum(us)}
    print(p,'first-mode lower',float(sum(ls)),'upper',float(sum(us)))
AL={p:results[p]['L'] for p in results}
AU={p:F(8000,7999)*(results[p]['U']+F(1,10**8)) for p in results}
print('mu bounds:',float(F(1,2)-AU[0]/4),float(2*AL[0]-AU[2]/4),float(12*AL[2]-AU[4]/4),float(12*AU[2]-AL[4]/4),float(30*AL[4]-AU[6]/4))
(src/'cell-summary.json').write_text(json.dumps({p:{k:str(v) for k,v in r.items()} for p,r in results.items()},indent=2))
# Final finite sums, connected to integrals by the existing adjacent-interval theorem.
agg=''.join('import CarrySelfAdjointOperator.ThetaMomentCertificateData.'+x+'\n' for x in allcellfiles)
agg+='\nopen MeasureTheory\nnamespace CarrySelfAdjointOperator\nnoncomputable section\nset_option maxHeartbeats 8000000\nset_option maxRecDepth 8192\n\n'
agg+='''theorem thetaFirstMode_integral_eq_sum_cells (p : ℕ) :
    (∫ x in (0:ℝ)..1, x^p*thetaFirstMode x) =
      ∑ j ∈ Finset.range 128, ∫ x in ((j:ℝ)/128)..(((j+1:ℕ):ℝ)/128), x^p*thetaFirstMode x := by
  have hint : ∀ k : ℕ, k < 128 → IntervalIntegrable (fun x : ℝ ↦ x^p*thetaFirstMode x)
      volume ((k:ℝ)/128) (((k+1:ℕ):ℝ)/128) := by
    intro k _
    apply Continuous.intervalIntegrable
    unfold thetaFirstMode
    fun_prop
  simpa using (intervalIntegral.sum_integral_adjacent_intervals hint).symm

'''
for p in results:
    for side in ['lower','upper']:
        if p==6 and side=='lower':continue
        value=results[p]['L' if side=='lower' else 'U']
        stmt=(f'{t(value)} ≤ (∫ x in (0:ℝ)..1, x^{p}*thetaFirstMode x)' if side=='lower' else f'(∫ x in (0:ℝ)..1, x^{p}*thetaFirstMode x) ≤ {t(value)}')
        hs=[f'thetaFirstMode_cell_{side}_{p}_{j:03d}' for j in range(N)]
        # Balanced expression avoids deep elaborator recursion and proves exactly the sum.
        while len(hs)>1:hs=[f'(add_le_add {hs[i]} {hs[i+1]})' for i in range(0,len(hs),2)]
        agg+=f'''theorem thetaFirstMode_integral_{side}_{p} :
    {stmt} := by
  have h := {hs[0]}
  rw [thetaFirstMode_integral_eq_sum_cells]
  norm_num [Finset.sum_range_succ] at h ⊢
  linarith only [h]

'''
agg+='end\nend CarrySelfAdjointOperator\n'
(src/'CompletedNativeThetaFiniteMomentCertificate.lean').write_text(agg)
