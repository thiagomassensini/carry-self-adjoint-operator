#!/usr/bin/env python3
"""Generate source-only order-ten theta certificates using exact rationals.

Usage: python3 research/theta-tenth-source-certificate-generate.py
Optional: --output-dir /tmp/regenerated-theta-certificate
Requires SymPy for an exact polynomial expansion, never as a trusted oracle.
All generated statements are subsequently checked by Lean norm_num/ring.
This reuses the certified source nodes from the eighth-order quadrature.
"""
from fractions import Fraction as F
from math import factorial, floor, ceil
from pathlib import Path
import argparse, re
import sympy as sym

repo=Path(__file__).resolve().parents[1]
parser=argparse.ArgumentParser()
parser.add_argument('--repo-root',type=Path,default=repo)
parser.add_argument('--output-dir',type=Path)
args=parser.parse_args()
out=args.output_dir or args.repo_root/'CarrySelfAdjointOperator'
out.mkdir(parents=True,exist_ok=True)
root=out/'ThetaTenthSourceCertificateData';root.mkdir(exist_ok=True)
nodes={}
for path in (args.repo_root/'CarrySelfAdjointOperator'/'ThetaEighthMomentCertificateData').glob('ThetaNodes*.lean'):
 text=path.read_text()
 for match in re.finditer(r'theorem thetaFirstMode_refined_node_(\d+) :.*?apply thetaFirstMode_node_bounds (.*?)\n',text,re.S):
  nums=re.findall(r'\((\d+)/(\d+):ℝ\)',match[2])
  q,el,eu,l,u=[F(int(a),int(b)) for a,b in nums]
  nodes[q]=(int(match[1]),el,eu,l,u)
assert len(nodes)>256, 'Certified eighth-order source nodes are required.'
t=sym.symbols('t0 t2 t4 t6 t8 t10')
a,b,c,d,e,f=(sym.Rational(1,2)-t[0]/4,2*t[0]-t[1]/4,
 12*t[1]-t[2]/4,30*t[2]-t[3]/4,56*t[3]-t[4]/4,90*t[4]-t[5]/4)
P=sym.Poly(105*a*a*b*d*f-180*a*a*b*e*e-350*a*a*c*c*f+2520*a*a*c*d*e
 -2646*a*a*d**3+525*a*b*b*c*f-2205*a*b*b*d*e-9450*a*b*c*c*e
 +26460*a*b*c*d*d-14700*a*c**3*d+14175*b**3*c*e-35280*b**3*d*d
 +22050*b*b*c*c*d,*t)
term=lambda x:f'({x.numerator}/{x.denominator}:ℝ)'
ns=lambda q:f'thetaFirstMode_refined_node_{nodes[q][0]:04d}'
imports='import CarrySelfAdjointOperator.CompletedNativeThetaEighthMomentCertificate\nimport CarrySelfAdjointOperator.CompletedNativeThetaCurvatureQuadrature\n'
gammas={}
for j in range(256):
 a,b=F(j,256),F(j+1,256)
 S=sum((2*a)**i/factorial(i) for i in range(12));Q=F(floor(F(3141592,10**6)*S*10**10),10**10)
 l=nodes[b][3];exact=(F(1,4)-6*Q+4*Q*Q)*l;g=F(floor(exact*10**18),10**18);gammas[j]=g
 group=j//32;path=root/f'Curvature{group}.lean'
 if j%32==0:path.write_text(imports+'\nnamespace CarrySelfAdjointOperator\nnoncomputable section\nset_option maxHeartbeats 4000000\n\n')
 code=f'''theorem thetaSource_cell_curvature_{j:03d} :
    ∀ u ∈ Set.Icc {term(a)} {term(b)}, {term(g)} ≤ thetaFirstModeSecond u := by
  have hQ : {term(Q)} ≤ Real.pi*Real.exp (2*{term(a)}) := by
    calc
      {term(Q)} ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*{term(a)})^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*{term(a)}) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower {term(a)} {term(b)} {term(Q)} {term(l)}
    (by norm_num) (by norm_num) hQ (by norm_num) ({ns(b)}).1
  intro u hu
  exact (show {term(g)} ≤ (1/4-6*{term(Q)}+4*{term(Q)}^2)*{term(l)} by norm_num).trans (h u hu)

'''
 with path.open('a') as w:w.write(code)
 if j%32==31:
  with path.open('a') as w:w.write('end\nend CarrySelfAdjointOperator\n')
totals={};files=[]
for p in (0,2,4,6,8,10):
 lows=[];highs=[]
 for j in range(256):
  a,b=F(j,256),F(j+1,256);M=lambda q:(b**(q+1)-a**(q+1))/(q+1);m=M(p+1)/M(p);g=gammas[j]
  hi=((b*nodes[a][4]-a*nodes[b][4])*M(p)+(nodes[b][4]-nodes[a][4])*M(p+1))/(b-a)-g/2*(-M(p+2)+(a+b)*M(p+1)-a*b*M(p))
  U=F(ceil(hi*10**24),10**24);highs.append(U)
  group=j//32;path=root/f'Cells{p}_{group}.lean'
  if j%32==0:
   path.write_text(f'import CarrySelfAdjointOperator.ThetaTenthSourceCertificateData.Curvature{group}\n\nopen MeasureTheory\nnamespace CarrySelfAdjointOperator\nnoncomputable section\nset_option maxHeartbeats 4000000\nset_option maxRecDepth 8192\n\n');files.append(path.stem)
  zero_simp='  norm_num only [pow_zero, one_mul]\n' if p==0 else ''
  code=''
  if p<10:
   lo=nodes[m][3]*M(p)+g/2*(M(p+2)-m*m*M(p));L=F(floor(lo*10**24),10**24);lows.append(L)
   code+=f'''theorem thetaSource_curvature_cell_lower_{p}_{j:03d} :
    {term(L)} ≤ ∫ x in {term(a)}..{term(b)}, x^{p}*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower {p} {term(a)} {term(b)}
    {term(m)} {term(nodes[m][3])} {term(g)}
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_{j:03d}
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) ({ns(m)}).1
  norm_num [thetaPowerMass] at h
{zero_simp}  linarith only [h]

'''
  code+=f'''theorem thetaSource_curvature_cell_upper_{p}_{j:03d} :
    (∫ x in {term(a)}..{term(b)}, x^{p}*thetaFirstMode x) ≤ {term(U)} := by
  have h := thetaFirstMode_weighted_curvature_cell_upper {p} {term(a)} {term(b)}
    {term(nodes[a][4])} {term(nodes[b][4])} {term(g)} (by norm_num) (by norm_num)
    thetaSource_cell_curvature_{j:03d} ({ns(a)}).2 ({ns(b)}).2
  norm_num [thetaPowerMass] at h
{zero_simp}  linarith only [h]

'''
  with path.open('a') as w:w.write(code)
  if j%32==31:
   with path.open('a') as w:w.write('end\nend CarrySelfAdjointOperator\n')
 totals[p]=sum(lows),sum(highs)
agg=''.join(f'import CarrySelfAdjointOperator.ThetaTenthSourceCertificateData.{f}\n' for f in files)
agg+='import CarrySelfAdjointOperator.CompletedNativeThetaDecayingTail\n\nopen MeasureTheory\nnamespace CarrySelfAdjointOperator\nnoncomputable section\nset_option maxHeartbeats 16000000\nset_option maxRecDepth 8192\n\n'
box=[]
for p,(L,U) in totals.items():
 for side,val in [('lower',L),('upper',U)]:
  if p==10 and side=='lower':continue
  bound=(f'{term(val)} ≤ (∫ x in (0:ℝ)..1, x^{p}*thetaFirstMode x)' if side=='lower' else f'(∫ x in (0:ℝ)..1, x^{p}*thetaFirstMode x) ≤ {term(val)}')
  names=[f'thetaSource_curvature_cell_{side}_{p}_{j:03d}' for j in range(256)]
  while len(names)>1:names=[f'(add_le_add {names[i]} {names[i+1]})' for i in range(0,len(names),2)]
  agg+=f'''theorem thetaSource_curvature_integral_{side}_{p} :
    {bound} := by
  have h := {names[0]}
  rw [thetaFirstMode_refined_integral_eq_sum_cells]
  norm_num [Finset.sum_range_succ] at h ⊢
  linarith only [h]

'''
 low=F(floor(L*10**15),10**15);up=F(ceil((U+F(1,20000000000)+F(factorial(p),100000*23**(p+1)))*10**15),10**15)
 box.append((low,up))
 agg+=f'''theorem nativeSourceThetaIntegral_curvature_box_{p} :
    {term(low)} ≤ completedNativeThetaTailMoment {p} ∧
      completedNativeThetaTailMoment {p} ≤ {term(up)} := by
  constructor
'''
 if p<10:agg+=f'  · linarith [thetaSource_curvature_integral_lower_{p}, completedNativeThetaTailMoment_finite_lower {p}]\n'
 else:agg+='  · simpa only [zero_div] using completedNativeThetaTailMoment_nonneg 10\n'
 agg+=f'  · have h := completedNativeThetaTailMoment_finite_upper_decaying {p} (by norm_num)\n    norm_num only [Nat.factorial, Nat.reduceAdd, Nat.reducePow] at h\n    linarith [thetaSource_curvature_integral_upper_{p}]\n\n'
 print(p,float(low),float(up))
agg+='end\nend CarrySelfAdjointOperator\n'
(out/'CompletedNativeThetaTenthSourceCertificate.lean').write_text(agg)


# Normalize the certified enclosure for a polynomial bound, without altering
# the source or the metric. Every coefficient is checked by a Lean ring identity.
s=sym
x=s.symbols('x0:6')
poly=s.Poly(P.as_expr().subs({t:s.Rational(l.numerator,l.denominator)+
 (s.Rational(u.numerator,u.denominator)-s.Rational(l.numerator,l.denominator))*xi
 for t,xi,(l,u) in zip(P.gens,x,box)},simultaneous=True),*x)
lo=poly.coeff_monomial(1)+sum(v for _,v in poly.terms() if v<0)
assert lo>s.Rational(1,10**13), 'Exact certificate margin must be positive.'
D=int(s.ilcm(*[v.q for _,v in poly.terms()])); lower=int(lo*D)
def rat(v):return f'({v.numerator}/{v.denominator}:ℝ)'
def mono(m):return '*'.join(f'x{i}' if p==1 else f'x{i}^{p}' for i,p in enumerate(m) if p) or '1'
terms=poly.terms();exp=' +\n    '.join(f'({int(c*D)}:ℝ)*({mono(m)})' for m,c in terms)
aff=[f'({rat(l)}+({rat(u)}-{rat(l)})*x{i})' for i,(l,u) in enumerate(box)]
raw=lambda ts:f'nativeSourceTenthMixedNumerator (1/2-{ts[0]}/4) (2*{ts[0]}-{ts[1]}/4) (12*{ts[1]}-{ts[2]}/4) (30*{ts[2]}-{ts[3]}/4) (56*{ts[3]}-{ts[4]}/4) (90*{ts[4]}-{ts[5]}/4)'
h='''import CarrySelfAdjointOperator.CompletedNativeChiralReturnFiveBoundaryFace

/-! Exact rational enclosure of the EXISTING mixed source polynomial.
The unit-cube coordinates merely express a certified theta integral box.
They define neither a source state nor a metric. Every coefficient below
is the exact expansion of the original polynomial, checked by `ring`. -/
namespace CarrySelfAdjointOperator
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8192

'''
h+=f'private def tenthThetaExpansion (x0 x1 x2 x3 x4 x5 : ℝ) : ℝ :=\n    {exp}\n\n'
h+=f'private theorem tenthThetaExpansion_eq (x0 x1 x2 x3 x4 x5 : ℝ) :\n    ({D}:ℝ)*{raw(aff)} = tenthThetaExpansion x0 x1 x2 x3 x4 x5 := by\n  unfold nativeSourceTenthMixedNumerator tenthThetaExpansion\n  ring\n\n'
h+='private theorem tenthThetaExpansion_lower (x0 x1 x2 x3 x4 x5 : ℝ)\n'
for i in range(6):h+=f'    (hx{i} : 0 ≤ x{i} ∧ x{i} ≤ 1)\n'
h+=f'    : ({lower}:ℝ) ≤ tenthThetaExpansion x0 x1 x2 x3 x4 x5 := by\n'
for i in range(6):h+=f'  have hx{i}_nonneg : 0 ≤ x{i} := hx{i}.1\n'
for i in range(6):
 for p in range(2,6):h+=f'  have hp{i}_{p} : x{i}^{p} ≤ 1 := pow_le_one₀ hx{i}.1 hx{i}.2\n'
for j,(m,c) in enumerate(terms):
 if not any(m):continue
 ci=int(c*D);M=mono(m)
 h+=f'  have hm{j} : 0 ≤ {M} := by positivity\n'
 if ci<0:
  hp=['hx%d.2'%i if p==1 else f'hp{i}_{p}' for i,p in enumerate(m) if p]
  def combine(v):
   if len(v)==1:return v[0]
   return f'(mul_le_one₀ ({combine(v[:-1])}) (by positivity) {v[-1]})'
  h+=f'  have hu{j} : {M} ≤ 1 := {combine(hp) if hp else "le_rfl"}\n'
  h+=f'  have ht{j} : ({ci}:ℝ) ≤ ({ci}:ℝ)*({M}) := by\n    simpa only [mul_one] using mul_le_mul_of_nonpos_left hu{j} (by norm_num : ({ci}:ℝ) ≤ 0)\n'
 else:h+=f'  have ht{j} : 0 ≤ ({ci}:ℝ)*({M}) := mul_nonneg (by norm_num) hm{j}\n'
h+='  unfold tenthThetaExpansion\n  linear_combination '+' + '.join(f'ht{j}' for j in (j for j,(m,_) in enumerate(terms) if any(m)))+'\n\n'
h+='''/-- A strict positive margin for the original mixed polynomial on a raw
THETA integral enclosure, including all correlations fixed by integrations
by parts. This finite rational lemma invokes no moment positivity. -/
theorem nativeSourceTenthMixedNumerator_thetaIntegral_box_pos
    (t0 t2 t4 t6 t8 t10 : ℝ)
'''
for i,(t,(l,u)) in enumerate(zip(['t0','t2','t4','t6','t8','t10'],box)):h+=f'    (h{i} : {rat(l)} ≤ {t} ∧ {t} ≤ {rat(u)})\n'
h+=f'    : (1/10000000000000:ℝ) < {raw(["t0","t2","t4","t6","t8","t10"])} := by\n'
for i,(t,(l,u)) in enumerate(zip(['t0','t2','t4','t6','t8','t10'],box)):
 h+=f'  let x{i} := ({t}-{rat(l)})/({rat(u)}-{rat(l)})\n'
 h+=f'  have hx{i} : 0 ≤ x{i} ∧ x{i} ≤ 1 := by\n    dsimp [x{i}]\n    constructor\n    · exact div_nonneg (by linarith [h{i}.1]) (by norm_num)\n    · apply (div_le_one (by norm_num : 0 < {rat(u)}-{rat(l)})).mpr\n      linarith [h{i}.2]\n'
 h+=f'  have he{i} : {t} = {aff[i]} := by dsimp [x{i}]; field_simp; ring\n'
h+='  rw ['+', '.join(f'he{i}' for i in range(6))+']\n'
h+=f'  apply (mul_lt_mul_iff_right₀ (show (0:ℝ) < {D} by norm_num)).mp\n  rw [tenthThetaExpansion_eq]\n  exact (show ({D}:ℝ)*(1/10000000000000) < {lower} by norm_num).trans_le\n    (tenthThetaExpansion_lower x0 x1 x2 x3 x4 x5 hx0 hx1 hx2 hx3 hx4 hx5)\n\nend\nend CarrySelfAdjointOperator\n'
# unused hp are linter warnings: generate only needed exponents
used={(i,p) for m,c in terms if c<0 for i,p in enumerate(m) if p>1}
for i in range(6):
 for p in range(2,6):
  if (i,p) not in used:h=h.replace(f'  have hp{i}_{p} : x{i}^{p} ≤ 1 := pow_le_one₀ hx{i}.1 hx{i}.2\n','')
# hm negative terms unused but needed positivity solver sees them? hm is unused by linter if only positivity not implicit? remove; positivity knows hx anyway
for j,(m,c) in enumerate(terms):
 if c<0:h=h.replace(f'  have hm{j} : 0 ≤ {mono(m)} := by positivity\n','')
(out/'CompletedNativeThetaTenthPolynomialEnclosure.lean').write_text(h)
print('generated',len(h),'bytes')
