#!/usr/bin/env python3
"""Generate source-only power-twelve theta certificates, all checked by Lean.
Reference for the motivating external enclosure audit: Yanxin Liu and Jianxi Mao,
Infinite log-concavity of the Taylor coefficients of the Riemann xi-function,
arXiv:2610.04972v1, https://arxiv.org/abs/2610.04972 .
No formula, code or external coefficient enclosure is imported from that work.
The algorithm here refines this repository's existing theta curvature quadrature.
"""
from fractions import Fraction as F
from math import factorial, floor, ceil
from pathlib import Path
import argparse, re, sympy as s
parser=argparse.ArgumentParser()
parser.add_argument('--repo-root',type=Path,default=Path(__file__).resolve().parents[1])
parser.add_argument('--output-dir',type=Path)
args=parser.parse_args()
root=args.output_dir or args.repo_root/'CarrySelfAdjointOperator'
root.mkdir(parents=True,exist_ok=True)
data=root/'ThetaTwelfthSourceCertificateData';data.mkdir(exist_ok=True)
nodes={}
for path in (args.repo_root/'CarrySelfAdjointOperator'/'ThetaEighthMomentCertificateData').glob('ThetaNodes*.lean'):
 text=path.read_text()
 for match in re.finditer(r'theorem thetaFirstMode_refined_node_(\d+) :.*?apply thetaFirstMode_node_bounds (.*?)\n',text,re.S):
  nums=re.findall(r'\((\d+)/(\d+):ℝ\)',match[2])
  q,el,eu,l,u=[F(int(a),int(b)) for a,b in nums]
  nodes[q]=(int(match[1]),el,eu,l,u)
assert len(nodes)>512
term=lambda q:f'({q.numerator}/{q.denominator}:ℝ)'
ns=lambda q:f'thetaFirstMode_refined_node_{nodes[q][0]:04d}'
qlo=lambda q:F(floor(F(3141592,10**6)*sum((2*q)**i/factorial(i) for i in range(20))*10**12),10**12)
qhi=lambda q:F(3141593,10**6)*nodes[q][2]
def qlo_code(q,Q):return f'''  have hlo : {term(Q)} ≤ Real.pi*Real.exp (2*{term(q)}) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*{term(q)})^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
'''
selected={}
for p in range(0,13,2):
 for j in range(512):
  a,b=F(j,512),F(j+1,512);M=lambda v:(b**(v+1)-a**(v+1))/(v+1)
  selected[p,j]=min((q for q in nodes if a<=q<=b),key=lambda q:abs(q-M(p+1)/M(p)))
dervs=sorted(set(selected.values()));di={q:i for i,q in enumerate(dervs)}
print('derivative nodes',len(dervs),flush=True)
for i,q in enumerate(dervs):
 group=i//32;path=data/f'Derivative{group:02d}.lean'
 if i%32==0:path.write_text('import CarrySelfAdjointOperator.CompletedNativeThetaEighthMomentCertificate\nimport CarrySelfAdjointOperator.CompletedNativeThetaSharpCurvature\nnamespace CarrySelfAdjointOperator\nset_option maxHeartbeats 4000000\nset_option maxRecDepth 8192\n')
 QL,QU=qlo(q),qhi(q);l,u=nodes[q][3:5];DL=(F(1,2)-2*QU)*u;DU=(F(1,2)-2*QL)*l
 code=f'''theorem thetaTwelfth_derivative_node_{i:04d} :
    {term(DL)} ≤ thetaFirstModeFirst {term(q)} ∧ thetaFirstModeFirst {term(q)} ≤ {term(DU)} := by
{qlo_code(q,QL)}  have hi : Real.exp (2*{term(q)}) ≤ {term(nodes[q][2])} := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*{term(q)}) (by norm_num : 2*{term(q)} ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*{term(q)}) ≤ {term(QU)} := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds {term(q)} {term(QL)} {term(QU)} {term(l)} {term(u)}
    (by norm_num) hlo hhi (by norm_num) ({ns(q)}).1 ({ns(q)}).2
  convert h using 1 <;> first | rfl | norm_num

'''
 with path.open('a') as w:w.write(code)
 if i%32==31 or i==len(dervs)-1:
  with path.open('a') as w:w.write('end CarrySelfAdjointOperator\n')
gammas={}
for j in range(512):
 a,b=F(j,512),F(j+1,512);QL=qlo(b);l=nodes[b][3]
 gam=F(floor((F(1,4)-6*QL+4*QL**2)*l*10**24),10**24);gammas[j]=gam
 group=j//32;path=data/f'Curvature{group:02d}.lean'
 if j%32==0:path.write_text('import CarrySelfAdjointOperator.CompletedNativeThetaEighthMomentCertificate\nimport CarrySelfAdjointOperator.CompletedNativeThetaSharpCurvature\nnamespace CarrySelfAdjointOperator\nset_option maxHeartbeats 4000000\n')
 code=f'''theorem thetaTwelfth_cell_curvature_{j:03d} :
    ∀ u ∈ Set.Icc {term(a)} {term(b)}, {term(gam)} ≤ thetaFirstModeSecond u := by
{qlo_code(b,QL)}  have h := thetaFirstModeSecond_endpoint_cell_lower {term(a)} {term(b)} {term(QL)} {term(l)}
    (by norm_num) (by norm_num) hlo (by norm_num) ({ns(b)}).1
  intro u hu
  exact (show {term(gam)} ≤ (1/4-6*{term(QL)}+4*{term(QL)}^2)*{term(l)} by norm_num).trans (h u hu)

'''
 with path.open('a') as w:w.write(code)
 if j%32==31:
  with path.open('a') as w:w.write('end CarrySelfAdjointOperator\n')
files=[];totals={}
for p in range(0,13,2):
 lows=[];highs=[]
 for j in range(512):
  a,b=F(j,512),F(j+1,512);M=lambda v:(b**(v+1)-a**(v+1))/(v+1)
  m=selected[p,j];gam=gammas[j];QL,QU=qlo(m),qhi(m)
  D=((F(1,2)-2*QU)*nodes[m][4] if M(p+1)-m*M(p)>=0 else (F(1,2)-2*QL)*nodes[m][3])
  lower=nodes[m][3]*M(p)+D*(M(p+1)-m*M(p))+gam/2*(M(p+2)-2*m*M(p+1)+m*m*M(p))
  upper=((b*nodes[a][4]-a*nodes[b][4])*M(p)+(nodes[b][4]-nodes[a][4])*M(p+1))/(b-a)-gam/2*(-M(p+2)+(a+b)*M(p+1)-a*b*M(p))
  L=F(floor(lower*10**24),10**24);U=F(ceil(upper*10**24),10**24);lows.append(L);highs.append(U)
  path=data/f'Cells{p}_{j//32:02d}.lean'
  if j%32==0:
   req=sorted({di[selected[p,v]]//32 for v in range(j,j+32)})
   path.write_text(f'import CarrySelfAdjointOperator.ThetaTwelfthSourceCertificateData.Curvature{j//32:02d}\n'+''.join(f'import CarrySelfAdjointOperator.ThetaTwelfthSourceCertificateData.Derivative{n:02d}\n' for n in req)+'\nopen MeasureTheory\nnamespace CarrySelfAdjointOperator\nset_option maxHeartbeats 4000000\nset_option maxRecDepth 8192\n');files.append(path.stem)
  dprop='.1' if M(p+1)-m*M(p)>=0 else '.2'
  dmul='mul_le_mul_of_nonneg_right' if dprop=='.1' else 'mul_le_mul_of_nonpos_right'
  simplify='  norm_num only [pow_zero, one_mul]\n' if p==0 else ''
  code=f'''theorem thetaTwelfth_cell_lower_{p}_{j:03d} :
    {term(L)} ≤ ∫ x in {term(a)}..{term(b)}, x^{p}*thetaFirstMode x := by
  have hd : {term(D)}*(thetaPowerMass {p+1} {term(a)} {term(b)}-{term(m)}*thetaPowerMass {p} {term(a)} {term(b)}) ≤
      thetaFirstModeFirst {term(m)}*(thetaPowerMass {p+1} {term(a)} {term(b)}-{term(m)}*thetaPowerMass {p} {term(a)} {term(b)}) := by
    exact {dmul} (thetaTwelfth_derivative_node_{di[m]:04d}{dprop}) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower {p} {term(a)} {term(b)}
    {term(m)} {term(nodes[m][3])} {term(D)} {term(gam)}
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_{j:03d}
    (by norm_num [thetaPowerMass]) ({ns(m)}).1 hd
  norm_num [thetaPowerMass] at h
{simplify}  linarith only [h]

theorem thetaTwelfth_cell_upper_{p}_{j:03d} :
    (∫ x in {term(a)}..{term(b)}, x^{p}*thetaFirstMode x) ≤ {term(U)} := by
  have h := thetaFirstMode_weighted_curvature_cell_upper {p} {term(a)} {term(b)}
    {term(nodes[a][4])} {term(nodes[b][4])} {term(gam)} (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_{j:03d} ({ns(a)}).2 ({ns(b)}).2
  norm_num [thetaPowerMass] at h
{simplify}  linarith only [h]

'''
  with path.open('a') as w:w.write(code)
  if j%32==31:
   with path.open('a') as w:w.write('end CarrySelfAdjointOperator\n')
 totals[p]=sum(lows),sum(highs)
agg=''.join(f'import CarrySelfAdjointOperator.ThetaTwelfthSourceCertificateData.{f}\n' for f in files)
agg+='import CarrySelfAdjointOperator.CompletedNativeThetaDecayingTail\n\nopen MeasureTheory\nnamespace CarrySelfAdjointOperator\nnoncomputable section\nset_option maxHeartbeats 16000000\nset_option maxRecDepth 8192\n\n'
agg+='''theorem thetaTwelfth_integral_eq_sum_cells (p : ℕ) :
    (∫ x in (0:ℝ)..1, x^p*thetaFirstMode x) =
      ∑ j ∈ Finset.range 512, ∫ x in ((j:ℝ)/512)..(((j+1:ℕ):ℝ)/512), x^p*thetaFirstMode x := by
  have hint : ∀ k : ℕ, k < 512 → IntervalIntegrable (fun x : ℝ => x^p*thetaFirstMode x)
      volume ((k:ℝ)/512) (((k+1:ℕ):ℝ)/512) := by
    intro k _
    apply Continuous.intervalIntegrable
    unfold thetaFirstMode
    fun_prop
  simpa using (intervalIntegral.sum_integral_adjacent_intervals hint).symm

'''
box=[]
for p,(L,U) in totals.items():
 for side,val in [('lower',L),('upper',U)]:
  bound=(f'{term(val)} ≤ (∫ x in (0:ℝ)..1, x^{p}*thetaFirstMode x)' if side=='lower' else f'(∫ x in (0:ℝ)..1, x^{p}*thetaFirstMode x) ≤ {term(val)}')
  names=[f'thetaTwelfth_cell_{side}_{p}_{j:03d}' for j in range(512)]
  while len(names)>1:names=[f'(add_le_add {names[i]} {names[i+1]})' for i in range(0,len(names),2)]
  agg+=f'''theorem thetaTwelfth_integral_{side}_{p} :
    {bound} := by
  have h := {names[0]}
  rw [thetaTwelfth_integral_eq_sum_cells]
  norm_num [Finset.sum_range_succ] at h ⊢
  linarith only [h]

'''
 low=F(floor((L+F(2,10**12))*10**15),10**15);up=F(ceil((U+F(9,10**12)+F(factorial(p),100000*23**(p+1)))*10**15),10**15);box.append((low,up))
 agg+=f'''theorem nativeSourceThetaIntegral_twelfth_box_{p} :
    {term(low)} ≤ completedNativeThetaTailMoment {p} ∧ completedNativeThetaTailMoment {p} ≤ {term(up)} := by
  constructor
  · linarith [thetaTwelfth_integral_lower_{p}, completedNativeThetaTailMoment_finite_lower_twelve {p}]
  · have h := completedNativeThetaTailMoment_finite_upper_twelve {p} (by norm_num)
    norm_num only [Nat.factorial, Nat.reduceAdd, Nat.reducePow] at h
    linarith [thetaTwelfth_integral_upper_{p}]

'''
 print(p,float(low),float(up),flush=True)
agg+='end\nend CarrySelfAdjointOperator\n';(root/'CompletedNativeThetaTwelfthSourceCertificate.lean').write_text(agg)
# The original existing raw source polynomial, not an external moment target.
a=s.symbols('a b c d e f g');t=s.symbols('t0 t2 t4 t6 t8 t10 t12');x=s.symbols('x0:7')
text=(args.repo_root/'CarrySelfAdjointOperator'/'CompletedNativeChiralReturnSixBoundaryFace.lean').read_text().split('def nativeSourceTwelfthMixedNumerator',1)[1].split(':=',1)[1].split('/--',1)[0].strip().replace('^','**')
P=s.sympify(text,locals=dict(zip('abcdefg',a)))
TP=s.Poly(P.subs(dict(zip(a,[s.Rational(1,2)-t[0]/4]+[(2*n)*(2*n-1)*t[n-1]-t[n]/4 for n in range(1,7)])),simultaneous=True),*t)
pol=s.Poly(TP.as_expr().subs({tt:s.Rational(l.numerator,l.denominator)+(s.Rational(u.numerator,u.denominator)-s.Rational(l.numerator,l.denominator))*xx for tt,xx,(l,u) in zip(t,x,box)},simultaneous=True),*x)
lo=pol.coeff_monomial(1)+sum(v for m,v in pol.terms() if any(m) and v<0)
print('certificate lower',float(lo),flush=True);assert lo>s.Rational(1,10**19)
poly=pol
D=int(s.ilcm(*[v.q for _,v in poly.terms()])); lower=int(lo*D)
def rat(v):return f'({v.numerator}/{v.denominator}:ℝ)'
def mono(m):return '*'.join(f'x{i}' if p==1 else f'x{i}^{p}' for i,p in enumerate(m) if p) or '1'
terms=poly.terms();exp=' +\n    '.join(f'({int(c*D)}:ℝ)*({mono(m)})' for m,c in terms)
aff=[f'({rat(l)}+({rat(u)}-{rat(l)})*x{i})' for i,(l,u) in enumerate(box)]
raw=lambda ts:f'nativeSourceTwelfthMixedNumerator (1/2-{ts[0]}/4) (2*{ts[0]}-{ts[1]}/4) (12*{ts[1]}-{ts[2]}/4) (30*{ts[2]}-{ts[3]}/4) (56*{ts[3]}-{ts[4]}/4) (90*{ts[4]}-{ts[5]}/4) (132*{ts[5]}-{ts[6]}/4)'
h='''import CarrySelfAdjointOperator.CompletedNativeChiralReturnSixBoundaryFace

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
h+=f'private def twelfthThetaExpansion (x0 x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=\n    {exp}\n\n'
h+=f'private theorem twelfthThetaExpansion_eq (x0 x1 x2 x3 x4 x5 x6 : ℝ) :\n    ({D}:ℝ)*{raw(aff)} = twelfthThetaExpansion x0 x1 x2 x3 x4 x5 x6 := by\n  unfold nativeSourceTwelfthMixedNumerator twelfthThetaExpansion\n  ring\n\n'
h+='private theorem twelfthThetaExpansion_lower (x0 x1 x2 x3 x4 x5 x6 : ℝ)\n'
for i in range(7):h+=f'    (hx{i} : 0 ≤ x{i} ∧ x{i} ≤ 1)\n'
h+=f'    : ({lower}:ℝ) ≤ twelfthThetaExpansion x0 x1 x2 x3 x4 x5 x6 := by\n'
for i in range(7):h+=f'  have hx{i}_nonneg : 0 ≤ x{i} := hx{i}.1\n'
for i in range(7):
 for p in range(2,10):h+=f'  have hp{i}_{p} : x{i}^{p} ≤ 1 := pow_le_one₀ hx{i}.1 hx{i}.2\n'
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
h+='  unfold twelfthThetaExpansion\n  linear_combination '+' + '.join(f'ht{j}' for j in (j for j,(m,_) in enumerate(terms) if any(m)))+'\n\n'
h+='''/-- A strict positive margin for the original mixed polynomial on a raw
theta integral enclosure, including all correlations fixed by integrations
by parts. This finite rational lemma invokes no moment positivity. -/
theorem nativeSourceTwelfthMixedNumerator_thetaIntegral_box_pos
    (t0 t2 t4 t6 t8 t10 t12 : ℝ)
'''
for i,(t,(l,u)) in enumerate(zip(['t0','t2','t4','t6','t8','t10','t12'],box)):h+=f'    (h{i} : {rat(l)} ≤ {t} ∧ {t} ≤ {rat(u)})\n'
h+=f'    : (1/10000000000000000000:ℝ) < {raw(["t0","t2","t4","t6","t8","t10","t12"])} := by\n'
for i,(t,(l,u)) in enumerate(zip(['t0','t2','t4','t6','t8','t10','t12'],box)):
 h+=f'  let x{i} := ({t}-{rat(l)})/({rat(u)}-{rat(l)})\n'
 h+=f'  have hx{i} : 0 ≤ x{i} ∧ x{i} ≤ 1 := by\n    dsimp [x{i}]\n    constructor\n    · exact div_nonneg (by linarith [h{i}.1]) (by norm_num)\n    · apply (div_le_one (by norm_num : 0 < {rat(u)}-{rat(l)})).mpr\n      linarith [h{i}.2]\n'
 h+=f'  have he{i} : {t} = {aff[i]} := by dsimp [x{i}]; field_simp; ring\n'
h+='  rw ['+', '.join(f'he{i}' for i in range(7))+']\n'
h+=f'  apply (mul_lt_mul_iff_right₀ (show (0:ℝ) < {D} by norm_num)).mp\n  rw [twelfthThetaExpansion_eq]\n  exact (show ({D}:ℝ)*(1/10000000000000000000) < {lower} by norm_num).trans_le\n    (twelfthThetaExpansion_lower x0 x1 x2 x3 x4 x5 x6 hx0 hx1 hx2 hx3 hx4 hx5 hx6)\n\nend\nend CarrySelfAdjointOperator\n'
# unused hp are linter warnings: generate only needed exponents
used={(i,p) for m,c in terms if c<0 for i,p in enumerate(m) if p>1}
for i in range(7):
 for p in range(2,10):
  if (i,p) not in used:h=h.replace(f'  have hp{i}_{p} : x{i}^{p} ≤ 1 := pow_le_one₀ hx{i}.1 hx{i}.2\n','')
# hm negative terms unused but needed positivity solver sees them? hm is unused by linter if only positivity not implicit? remove; positivity knows hx anyway
for j,(m,c) in enumerate(terms):
 if c<0:h=h.replace(f'  have hm{j} : 0 ≤ {mono(m)} := by positivity\n','')
(root/'CompletedNativeThetaTwelfthPolynomialEnclosure.lean').write_text(h)
print('generated',len(h),'bytes')

# Keep certificate arithmetic unchanged while bounding polynomial chunks.
D=int(s.ilcm(*[v.q for _,v in poly.terms()]));lower=int(lo*D)
term=lambda q:f'({q.numerator}/{q.denominator}:ℝ)'
mono=lambda m:'*'.join(f'x{i}' if p==1 else f'x{i}^{p}' for i,p in enumerate(m) if p) or '1'
raw=lambda v:f'nativeSourceTwelfthMixedNumerator (1/2-{v[0]}/4) (2*{v[0]}-{v[1]}/4) (12*{v[1]}-{v[2]}/4) (30*{v[2]}-{v[3]}/4) (56*{v[3]}-{v[4]}/4) (90*{v[4]}-{v[5]}/4) (132*{v[5]}-{v[6]}/4)'
h='''import CarrySelfAdjointOperator.CompletedNativeChiralReturnSixBoundaryFace

/-! Exact rational enclosure of the unchanged source polynomial.
Chunking bounds only reduces proof elaboration cost. It changes neither the
source enclosure nor the raw polynomial. Every expansion is checked by ring. -/
namespace CarrySelfAdjointOperator
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8192

'''
terms=poly.terms();groups=[terms[j:j+32] for j in range(0,len(terms),32)];calls=[];proofcalls=[];chunkdefs=[];chL=[]
for j,ts in enumerate(groups):
 ids=sorted({i for m,_ in ts for i,p in enumerate(m) if p});args=' '.join(f'x{i}' for i in ids);params=f'({args} : ℝ)' if ids else ''
 name=f'twelfthThetaChunk{j}';chunkdefs.append(name);calls.append(f'({name} {args})')
 expr=' +\n    '.join(f'({int(c*D)}:ℝ)*({mono(m)})' for m,c in ts)
 h+=f'private def {name} {params} : ℝ :=\n    {expr}\n\n'
 vlow=sum(int(c*D) for m,c in ts if not any(m) or c<0);chL.append(vlow)
 h+=f'private theorem {name}_lower {params}\n'
 for i in ids:h+=f'    (hx{i} : 0 ≤ x{i} ∧ x{i} ≤ 1)\n'
 h+=f'    : ({vlow}:ℝ) ≤ {name} {args} := by\n'
 for i in ids:h+=f'  have hx{i}_nonneg : 0 ≤ x{i} := hx{i}.1\n'
 used={(i,p) for m,c in ts if c<0 for i,p in enumerate(m) if p>1}
 for i,p in sorted(used):h+=f'  have hp{i}_{p} : x{i}^{p} ≤ 1 := pow_le_one₀ hx{i}.1 hx{i}.2\n'
 ht=[]
 for k,(m,c) in enumerate(ts):
  if not any(m):continue
  ci=int(c*D);M=mono(m);ht.append(f'ht{k}')
  if ci<0:
   hp=['hx%d.2'%i if p==1 else f'hp{i}_{p}' for i,p in enumerate(m) if p]
   def combine(v):return v[0] if len(v)==1 else f'(mul_le_one₀ ({combine(v[:-1])}) (by positivity) {v[-1]})'
   h+=f'  have hu{k} : {M} ≤ 1 := {combine(hp)}\n'
   h+=f'  have ht{k} : ({ci}:ℝ) ≤ ({ci}:ℝ)*({M}) := by\n    simpa only [mul_one] using mul_le_mul_of_nonpos_left hu{k} (by norm_num : ({ci}:ℝ) ≤ 0)\n'
  else:
   h+=f'  have hm{k} : 0 ≤ {M} := by positivity\n'
   h+=f'  have ht{k} : 0 ≤ ({ci}:ℝ)*({M}) := mul_nonneg (by norm_num) hm{k}\n'
 h+=f'  unfold {name}\n  linear_combination '+' + '.join(ht)+'\n\n'
 proofcalls.append(f'{name}_lower {args} '+ ' '.join(f'hx{i}' for i in ids))
xs='x0 x1 x2 x3 x4 x5 x6';h+=f'private def twelfthThetaExpansion ({xs} : ℝ) : ℝ :=\n    '+' +\n    '.join(calls)+'\n\n'
aff=[f'({term(l)}+({term(u)}-{term(l)})*x{i})' for i,(l,u) in enumerate(box)]
h+=f'private theorem twelfthThetaExpansion_eq ({xs} : ℝ) :\n    ({D}:ℝ)*{raw(aff)} = twelfthThetaExpansion {xs} := by\n  unfold nativeSourceTwelfthMixedNumerator twelfthThetaExpansion '+ ' '.join(chunkdefs)+'\n  ring\n\n'
h+=f'private theorem twelfthThetaExpansion_lower ({xs} : ℝ)\n'
for i in range(7):h+=f'    (hx{i} : 0 ≤ x{i} ∧ x{i} ≤ 1)\n'
h+=f'    : ({lower}:ℝ) ≤ twelfthThetaExpansion {xs} := by\n'
for j,c in enumerate(proofcalls):h+=f'  have h{j} := {c}\n'
h+='  unfold twelfthThetaExpansion\n  linear_combination '+' + '.join(f'h{j}' for j in range(len(groups)))+'\n\n'
# preserve the exact public theorem and source box
old=(root/'CompletedNativeThetaTwelfthPolynomialEnclosure.lean').read_text();h+=old[old.index('/-- A strict positive margin'):]
(root/'CompletedNativeThetaTwelfthPolynomialEnclosure.lean').write_text(h)
print(len(h),'bytes',len(groups),'chunks',sum(chL)==lower)
