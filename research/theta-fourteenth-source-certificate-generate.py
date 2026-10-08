#!/usr/bin/env python3
"""Generate exact source-only theta certificates through power fourteen.

The grid extends the existing theta coordinate to 9/8. Cubic Taylor cells
retain all source derivative terms and bound their fourth-derivative error.
No canonical moments, target Gram, spectral data, fitted metric or positivity input
is used. All emitted arithmetic and identities must be checked by Lean.
Requires sympy; the integral/node enclosures use exact Fraction arithmetic.
"""
import argparse
from pathlib import Path
parser = argparse.ArgumentParser()
parser.add_argument('--repo-root', type=Path, default=Path(__file__).resolve().parents[1])
parser.add_argument('--output-dir', type=Path)
args = parser.parse_args()
output_root = args.output_dir or args.repo_root / 'CarrySelfAdjointOperator'
output_root.mkdir(parents=True, exist_ok=True)
from fractions import Fraction as F
from math import factorial,floor,ceil
S=10**23;T=10**20
PL=F(314159265358979323846,10**20);PU=F(314159265358979323847,10**20)
lo=lambda x,d:F(floor(x*d),d)
hi=lambda x,d:F(ceil(x*d),d)
E=lambda x:sum((x/32)**i/factorial(i) for i in range(12))**32
EU=lambda x:(sum((x/32)**i/factorial(i) for i in range(12))+(x/32)**12*F(13,factorial(12)*12))**32
vals=[]
for j in range(577):
 q=F(j,512);el=lo(E(2*q),T);eu=hi(EU(2*q),T)
 fl=lo(2/EU(PU*eu-q/2),S);fu=hi(2/E(PL*el-q/2),S)
 ql=lo(PL*el,T);qu=hi(PU*eu,T)
 dl=[fl,fl/2-2*qu*fu,fl/4-6*qu*fu+4*ql**2*fl,fl/8-F(31,2)*qu*fu+30*ql**2*fl-8*qu**3*fu]
 du=[fu,fu/2-2*ql*fl,fu/4-6*ql*fl+4*qu**2*fu,fu/8-F(31,2)*ql*fl+30*qu**2*fu-8*ql**3*fl]
 vals.append([q,el,eu,fl,fu,ql,qu,dl,du])
 if j%100==0:print('node',j,flush=True)
boxes=[];cells=[]
for p in range(0,15,2):
 L=U=F(0);cs=[]
 for j in range(576):
  a,b=F(j,512),F(j+1,512)
  M=lambda v:(b**(v+1)-a**(v+1))/(v+1)
  W=[sum(F(factorial(r),factorial(i)*factorial(r-i))*(-a)**(r-i)*M(p+i) for i in range(r+1)) for r in range(5)]
  q,el,eu,fl,fu,ql,qu,dl,du=vals[j]
  QU=vals[j+1][6];C=hi((16*QU**4+112*QU**3+166*QU**2+39*QU+F(1,16))*fu,10**18)
  lc=sum(dl[i]*W[i]/factorial(i) for i in range(4))-C*W[4]/6
  uc=sum(du[i]*W[i]/factorial(i) for i in range(4))+C*W[4]/6
  lc=lo(lc,S);uc=hi(uc,S)
  L+=lc;U+=uc;cs.append([lc,uc,C])
 lower=lo(L,10**20);upper=hi(U+F(2,10**13)+F(factorial(p),10**5*23**(p+1)),10**20)
 boxes.append([lower,upper]);cells.append(cs)
 print(p,float(lower),float(upper), 'width',float(upper-lower),flush=True)

box=boxes
root=output_root
data=root/'ThetaFourteenthSourceCertificateData';data.mkdir(exist_ok=True)
t=lambda q:f'({q.numerator}/{q.denominator}:ℝ)'
ns=lambda j:f'thetaFourteenth_node_{j:03d}'
ds=lambda j:f'thetaFourteenth_derivatives_{j:03d}'
PL=F(314159265358979323846,10**20);PU=F(314159265358979323847,10**20)
for group in range((len(vals)+15)//16):
 path=data/f'Nodes{group:02d}.lean'
 code='import CarrySelfAdjointOperator.CompletedNativeThetaCubicQuadrature\nnamespace CarrySelfAdjointOperator\nset_option maxHeartbeats 4000000\nset_option maxRecDepth 8192\n'
 for j in range(group*16,min((group+1)*16,len(vals))):
  q,el,eu,fl,fu,ql,qu,dl,du=vals[j]
  code+=f'''theorem {ns(j)} :
    ({t(fl)} ≤ thetaFirstMode {t(q)} ∧ thetaFirstMode {t(q)} ≤ {t(fu)}) ∧
    ({t(ql)} ≤ Real.pi*Real.exp (2*{t(q)}) ∧ Real.pi*Real.exp (2*{t(q)}) ≤ {t(qu)}) := by
  have hf := thetaFirstMode_precise_node_bounds {t(q)} {t(el)} {t(eu)} {t(fl)} {t(fu)}
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaExpLower,Finset.sum_range_succ])
    (by norm_num [thetaExpUpper,Finset.sum_range_succ])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaExpUpper,Finset.sum_range_succ])
    (by norm_num [thetaExpLower,Finset.sum_range_succ])
  have he := thetaExp_bounds (x:=2*{t(q)}) (by norm_num) (by norm_num)
  have hel : {t(el)} ≤ Real.exp (2*{t(q)}) :=
    (show {t(el)} ≤ thetaExpLower (2*{t(q)}) by norm_num [thetaExpLower,Finset.sum_range_succ]).trans he.1
  have heu : Real.exp (2*{t(q)}) ≤ {t(eu)} :=
    he.2.trans (by norm_num [thetaExpUpper,Finset.sum_range_succ])
  have hlo := mul_le_mul (show {t(PL)} ≤ Real.pi by linarith [Real.pi_gt_d20])
    hel (by norm_num : (0:ℝ) ≤ {t(el)}) Real.pi_pos.le
  have hhi := mul_le_mul (show Real.pi ≤ {t(PU)} by linarith [Real.pi_lt_d20])
    heu (Real.exp_pos _).le (by norm_num : (0:ℝ) ≤ {t(PU)})
  refine ⟨hf,?_,?_⟩
  · exact (show {t(ql)} ≤ {t(PL)}*{t(el)} by norm_num).trans hlo
  · exact hhi.trans (by norm_num)

theorem {ds(j)} :
    ({t(dl[1])} ≤ thetaFirstModeFirst {t(q)} ∧ thetaFirstModeFirst {t(q)} ≤ {t(du[1])}) ∧
    ({t(dl[2])} ≤ thetaFirstModeSecond {t(q)} ∧ thetaFirstModeSecond {t(q)} ≤ {t(du[2])}) ∧
    ({t(dl[3])} ≤ thetaFirstModeThird {t(q)} ∧ thetaFirstModeThird {t(q)} ≤ {t(du[3])}) := by
  have h := thetaFirstMode_cubic_node_derivative_bounds {t(q)} {t(ql)} {t(qu)} {t(fl)} {t(fu)}
    (by norm_num) (by norm_num) ({ns(j)}).2.1 ({ns(j)}).2.2 ({ns(j)}).1.1 ({ns(j)}).1.2
  convert h using 1 <;> norm_num

'''
 code+='end CarrySelfAdjointOperator\n';path.write_text(code)
for p in range(0,15,2):
 for gr in range(18):
  path=data/f'Cells{p}_{gr:02d}.lean'
  groups=sorted({j//16 for j in range(32*gr,32*(gr+1)+1)})
  code=''.join(f'import CarrySelfAdjointOperator.ThetaFourteenthSourceCertificateData.Nodes{g:02d}\n' for g in groups)
  code+='open MeasureTheory\nnamespace CarrySelfAdjointOperator\nset_option maxHeartbeats 4000000\nset_option maxRecDepth 8192\n'
  for j in range(32*gr,32*(gr+1)):
   a,b=F(j,512),F(j+1,512);q,el,eu,fl,fu,ql,qu,dl,du=vals[j]
   L,U,C=cells[p//2][j]
   simplify = "  norm_num only [pow_zero,one_mul]\n" if p==0 else ""
   code+=f'''theorem thetaFourteenth_cell_bounds_{p}_{j:03d} :
    {t(L)} ≤ (∫ x in {t(a)}..{t(b)}, x^{p}*thetaFirstMode x) ∧
      (∫ x in {t(a)}..{t(b)}, x^{p}*thetaFirstMode x) ≤ {t(U)} := by
  have hc := thetaFirstModeFourth_cell_bound {t(a)} {t(b)} {t(vals[j+1][6])} {t(fu)}
    (by norm_num) ({ns(j+1)}).2.2 ({ns(j)}).1.2
  have hC : ∀ x ∈ Set.Icc {t(a)} {t(b)}, |thetaFirstModeFourth x| ≤ {t(C)} := by
    intro x hx
    exact (hc x hx).trans (by norm_num)
  have h := thetaFirstMode_weighted_cubic_cell_bounds {p} {t(a)} {t(b)}
    {' '.join(t(v) for v in dl)} {' '.join(t(v) for v in du)} {t(C)}
    (by norm_num) (by norm_num) ({ns(j)}).1 ({ds(j)}).1 ({ds(j)}).2.1 ({ds(j)}).2.2 hC
  norm_num [thetaCubicCellMass,thetaPowerMass] at h
{simplify}  constructor <;> linarith only [h.1,h.2]

'''
  code+='end CarrySelfAdjointOperator\n';path.write_text(code)
agg=''.join(f'import CarrySelfAdjointOperator.ThetaFourteenthSourceCertificateData.Cells{p}_{g:02d}\n' for p in range(0,15,2) for g in range(18))
agg+='import CarrySelfAdjointOperator.CompletedNativeThetaFourteenthTail\nopen MeasureTheory\nnamespace CarrySelfAdjointOperator\nnoncomputable section\nset_option maxHeartbeats 16000000\nset_option maxRecDepth 8192\n'
agg+='''theorem thetaFourteenth_integral_eq_sum_cells (p : ℕ) :
    (∫ x in (0:ℝ)..(9/8), x^p*thetaFirstMode x) =
      ∑ j ∈ Finset.range 576, ∫ x in ((j:ℝ)/512)..(((j+1:ℕ):ℝ)/512), x^p*thetaFirstMode x := by
  have hint : ∀ k : ℕ, k < 576 → IntervalIntegrable (fun x : ℝ => x^p*thetaFirstMode x)
      volume ((k:ℝ)/512) (((k+1:ℕ):ℝ)/512) := by
    intro k _
    apply Continuous.intervalIntegrable
    unfold thetaFirstMode
    fun_prop
  convert (intervalIntegral.sum_integral_adjacent_intervals hint).symm using 1
  norm_num

'''
for p in range(0,15,2):
 for idx,side in enumerate(['lower','upper']):
  val=sum(cs[idx] for cs in cells[p//2]);L,U=box[p//2]
  bound=f'{t(val)} ≤ (∫ x in (0:ℝ)..(9/8), x^{p}*thetaFirstMode x)' if idx==0 else f'(∫ x in (0:ℝ)..(9/8), x^{p}*thetaFirstMode x) ≤ {t(val)}'
  names=[f'(thetaFourteenth_cell_bounds_{p}_{j:03d}).{idx+1}' for j in range(576)]
  while len(names)>1:
   names=[f'(add_le_add {names[i]} {names[i+1]})' if i+1<len(names) else names[i] for i in range(0,len(names),2)]
  agg+=f'''theorem thetaFourteenth_integral_{side}_{p} :
    {bound} := by
  have h := {names[0]}
  rw [thetaFourteenth_integral_eq_sum_cells]
  generalize (fun x : ℝ => x^{p}*thetaFirstMode x) = f at *
  norm_num [Finset.sum_range_succ] at h ⊢
  linarith only [h]

'''
 agg+=f'''theorem nativeSourceThetaIntegral_fourteenth_box_{p} :
    {t(L)} ≤ completedNativeThetaTailMoment {p} ∧ completedNativeThetaTailMoment {p} ≤ {t(U)} := by
  constructor
  · linarith [thetaFourteenth_integral_lower_{p}, completedNativeThetaTailMoment_finite_lower_fourteen {p}]
  · have h := completedNativeThetaTailMoment_finite_upper_fourteen {p} (by norm_num)
    norm_num only [Nat.factorial, Nat.reduceAdd, Nat.reducePow] at h
    linarith [thetaFourteenth_integral_upper_{p}]

'''
agg+='end\nend CarrySelfAdjointOperator\n';(root/'CompletedNativeThetaFourteenthSourceCertificate.lean').write_text(agg)
print('Generated',len(list(data.glob('*.lean'))),'data modules',flush=True)

import sympy as s
box=[tuple(s.Rational(v.numerator,v.denominator) for v in pair) for pair in box]
a=s.symbols('a0:8')
fc=[(-1)**j*a[j]/s.factorial(2*j) for j in range(8)]
cc=[]
for n in range(7):
    cc.append(s.cancel((-(2*n+2)*fc[n+1]-sum(cc[j]*fc[n-j] for j in range(n)))/a[0]))
c0,c1,c2,c3,c4,c5,c6=cc
# The published source seam, with all its actual couplings.
D3=c0*c2*c4+2*c1*c2*c3-c0*c3**2-c1**2*c4-c2**3
n0=c1*c4**2-2*c2*c3*c4+c3**3-c1*c3*c5+c2**2*c5
n1=c0*c4**2-c1*c3*c4+c2*c3**2-c2**2*c4-c0*c3*c5+c1*c2*c5
n2=c0*c3*c4-c1*c2*c4-c1*c3**2+c2**2*c3-c0*c2*c5+c1**2*c5
P,den=s.fraction(s.factor(D3*c6+c3*n0-c4*n1+c5*n2))
assert s.expand(den-13153940405570764800000*a[0]**7)==0
params='a b c d e f g h'
PS=s.Poly(P,*a)
def mono(m,labels):return '*'.join(labels[i] if p==1 else f'{labels[i]}^{p}' for i,p in enumerate(m) if p) or '1'
expr=' +\n  '.join(f'({int(c)}:ℝ)*({mono(m,params.split())})' for m,c in PS.terms())
code=f'''import CarrySelfAdjointOperator.CompletedNativeChiralReturnSevenBoundaryFace

/-! Exact polynomial of the original seven-coordinate source discriminant.
No matrix, canonical moment or new metric is used. The coefficients follow
from the source product-rule recurrence; the identity is checked by ring. -/
namespace CarrySelfAdjointOperator
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 8192

def nativeSourceFourteenthMixedNumerator ({params} : ℝ) : ℝ :=
  {expr}

theorem nativeSourceSevenEvenDiscriminant_integral_formula :
    nativeSourceSevenEvenDiscriminant =
      nativeSourceFourteenthMixedNumerator
        (completedNativeXiCosineMoment 0) (completedNativeXiCosineMoment 1)
        (completedNativeXiCosineMoment 2) (completedNativeXiCosineMoment 3)
        (completedNativeXiCosineMoment 4) (completedNativeXiCosineMoment 5)
        (completedNativeXiCosineMoment 6) (completedNativeXiCosineMoment 7) /
        (13153940405570764800000 * completedNativeXiCosineMoment 0^7) := by
  obtain ⟨h0,h1,h2,h3⟩ := nativeSourceOddBoundaryCoefficient_integral_formulas
  unfold nativeSourceSevenEvenDiscriminant nativeSourceSevenEvenCoupling0
    nativeSourceSevenEvenCoupling1 nativeSourceSevenEvenCoupling2 nativeSourceFiveEvenDiscriminant
  rw [h0,h1,h2,h3, nativeSourceOddBoundaryCoefficient_four_integral_formula,
    nativeSourceOddBoundaryCoefficient_five_integral_formula,
    nativeSourceOddBoundaryCoefficient_six_integral_formula]
  unfold nativeSourceFourteenthMixedNumerator nativeSourceSeventhNumerator nativeSourceNinthNumerator
    nativeSourceEleventhNumerator nativeSourceThirteenthNumerator
  field_simp [(completedNativeXiCosineMoment_pos 0).ne']
  ring
end
end CarrySelfAdjointOperator
'''
(root/'CompletedNativeChiralReturnFourteenthSourcePolynomial.lean').write_text(code)
tvars=s.symbols('t0:8');xvars=s.symbols('x0:8')
TP=s.Poly(P.subs(dict(zip(a,[s.Rational(1,2)-tvars[0]/4]+[(2*n)*(2*n-1)*tvars[n-1]-tvars[n]/4 for n in range(1,8)])),simultaneous=True),*tvars)
poly=s.Poly(TP.as_expr().subs({tt:l+(u-l)*xx for tt,xx,(l,u) in zip(tvars,xvars,box)},simultaneous=True),*xvars)
K=4*10**20
D=K**7
assert all((v*D).q==1 for _,v in poly.terms())
lo=poly.coeff_monomial(1)+sum(v for m,v in poly.terms() if any(m) and v<0);low=int(lo*D)
assert lo>s.Rational(1,10**22)
term=lambda v:f'({v.p}/{v.q}:ℝ)'
xs='x0 x1 x2 x3 x4 x5 x6 x7'
rawcall=lambda v: 'nativeSourceFourteenthMixedNumerator '+ ' '.join([f'(1/2-{v[0]}/4)']+[f'({2*i*(2*i-1)}*{v[i-1]}-{v[i]}/4)' for i in range(1,8)])
code='''import CarrySelfAdjointOperator.CompletedNativeChiralReturnFourteenthSourcePolynomial

/-! Exact rational enclosure of the unchanged raw source polynomial.
The cube describes integral bounds only, not a source, Hilbert carrier or metric.
All algebra and inequality certificates are checked by the Lean kernel. -/
namespace CarrySelfAdjointOperator
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8192
'''
groups=[poly.terms()[i:i+24] for i in range(0,len(poly.terms()),24)];names=[];proofs=[]
for j,ts in enumerate(groups):
 ids=sorted({i for m,_ in ts for i,p in enumerate(m) if p});args=' '.join(f'x{i}' for i in ids);name=f'fourteenthThetaChunk{j}';names.append(name)
 expression=' +\n    '.join(f'({int(c*D)}:ℝ)*({mono(m,xs.split())})' for m,c in ts)
 vlow=sum(int(c*D) for m,c in ts if not any(m) or c<0)
 code+=f'\nprivate def {name} ({args} : ℝ) : ℝ :=\n    {expression}\n\n'
 code+=f'private theorem {name}_lower ({args} : ℝ)\n'
 for i in ids:code+=f'    (hx{i} : 0 ≤ x{i} ∧ x{i} ≤ 1)\n'
 code+=f'    : ({vlow}:ℝ) ≤ {name} {args} := by\n'
 for i in ids:code+=f'  have hx{i}_nonneg : 0 ≤ x{i} := hx{i}.1\n'
 used={(i,p) for m,c in ts if c<0 for i,p in enumerate(m) if p>1}
 for i,p in sorted(used):code+=f'  have hp{i}_{p} : x{i}^{p} ≤ 1 := pow_le_one₀ hx{i}.1 hx{i}.2\n'
 ht=[]
 def comb(v):return v[0] if len(v)==1 else f'(mul_le_one₀ ({comb(v[:-1])}) (by positivity) {v[-1]})'
 for k,(m,c) in enumerate(ts):
  if not any(m):continue
  ci=int(c*D);M=mono(m,xs.split());ht.append(f'ht{k}')
  if ci<0:
   hp=[f'hx{i}.2' if p==1 else f'hp{i}_{p}' for i,p in enumerate(m) if p]
   code+=f'  have hu{k} : {M} ≤ 1 := {comb(hp)}\n'
   code+=f'  have ht{k} : ({ci}:ℝ) ≤ ({ci}:ℝ)*({M}) := by\n    simpa only [mul_one] using mul_le_mul_of_nonpos_left hu{k} (by norm_num : ({ci}:ℝ) ≤ 0)\n'
  else:
   code+=f'  have hm{k} : 0 ≤ {M} := by positivity\n'
   code+=f'  have ht{k} : 0 ≤ ({ci}:ℝ)*({M}) := mul_nonneg (by norm_num) hm{k}\n'
 code+=f'  unfold {name}\n  linear_combination '+' + '.join(ht)+'\n'
 proofs.append(f'({name}_lower {args} '+' '.join(f'hx{i}' for i in ids)+')')
calls=[f'({name} '+' '.join(f'x{i}' for i in sorted({i for m,_ in ts for i,p in enumerate(m) if p}))+')' for name,ts in zip(names,groups)]
code+=f'\nprivate def fourteenthThetaExpansion ({xs} : ℝ) : ℝ :=\n    '+' +\n    '.join(calls)+'\n\n'
aff=[f'({term(l)}+({term(u)}-{term(l)})*x{i})' for i,(l,u) in enumerate(box)]
# Homogeneity clears fixed arithmetic denominators before the large expansion.
# K changes neither the source nor its metric; it is proof-only integer arithmetic.
mu_aff=[s.Rational(1,2)-tvars[0]/4]+[(2*i)*(2*i-1)*tvars[i-1]-tvars[i]/4 for i in range(1,8)]
mu_aff=[s.expand(v.subs({tt:l+(u-l)*xx for tt,xx,(l,u) in zip(tvars,xvars,box)},simultaneous=True)*K) for v in mu_aff]
assert all(c.q==1 for v in mu_aff for _,c in s.Poly(v,*xvars).terms())
def int_aff(v):
 return '('+' + '.join(f'({int(c)}:ℝ)*({mono(m,xs.split())})' for m,c in s.Poly(v,*xvars).terms())+')'
ints=[int_aff(v) for v in mu_aff]
code+=f'private theorem fourteenthSource_homogeneous ({params} : ℝ) :\n    ({D}:ℝ)*nativeSourceFourteenthMixedNumerator '+' '.join(f'({v}/({K}:ℝ))' for v in params.split())+' =\n      nativeSourceFourteenthMixedNumerator '+params+' := by\n  unfold nativeSourceFourteenthMixedNumerator\n  ring\n\n'
code+=f'private theorem fourteenthThetaExpansion_integer_eq ({xs} : ℝ) :\n    nativeSourceFourteenthMixedNumerator '+' '.join(ints)+f' = fourteenthThetaExpansion {xs} := by\n  unfold nativeSourceFourteenthMixedNumerator fourteenthThetaExpansion '+' '.join(names)+'\n  ring\n\n'
code+=f'private theorem fourteenthThetaExpansion_eq ({xs} : ℝ) :\n    ({D}:ℝ)*{rawcall(aff)} = fourteenthThetaExpansion {xs} := by\n'
raw_args=[f'(1/2-{aff[0]}/4)']+[f'({2*i*(2*i-1)}*{aff[i-1]}-{aff[i]}/4)' for i in range(1,8)]
for i,(v,w) in enumerate(zip(raw_args,ints)):
 code+=f'  have h{i} : {v} = {w}/({K}:ℝ) := by ring\n'
code+='  rw ['+', '.join(f'h{i}' for i in range(8))+', fourteenthSource_homogeneous, fourteenthThetaExpansion_integer_eq]\n\n'
code+=f'private theorem fourteenthThetaExpansion_lower ({xs} : ℝ)\n'
for i in range(8):code+=f'    (hx{i} : 0 ≤ x{i} ∧ x{i} ≤ 1)\n'
code+=f'    : ({low}:ℝ) ≤ fourteenthThetaExpansion {xs} := by\n'
for j,proof in enumerate(proofs):code+=f'  have h{j} := {proof}\n'
code+='  unfold fourteenthThetaExpansion\n  linear_combination '+' + '.join(f'h{j}' for j in range(len(groups)))+'\n\n'
code+='theorem nativeSourceFourteenthMixedNumerator_thetaIntegral_box_pos\n    (t0 t2 t4 t6 t8 t10 t12 t14 : ℝ)\n'
labels=[f't{2*i}' for i in range(8)]
for i,(tt,(l,u)) in enumerate(zip(labels,box)):code+=f'    (h{i} : {term(l)} ≤ {tt} ∧ {tt} ≤ {term(u)})\n'
code+=f'    : (1/10000000000000000000000:ℝ) < {rawcall(labels)} := by\n'
for i,(tt,(l,u)) in enumerate(zip(labels,box)):
 code+=f'''  let x{i} := ({tt}-{term(l)})/({term(u)}-{term(l)})
  have hx{i} : 0 ≤ x{i} ∧ x{i} ≤ 1 := by
    dsimp [x{i}]
    constructor
    · exact div_nonneg (by linarith [h{i}.1]) (by norm_num)
    · apply (div_le_one (by norm_num : 0 < {term(u)}-{term(l)})).mpr
      linarith [h{i}.2]
  have he{i} : {tt} = {aff[i]} := by dsimp [x{i}]; field_simp; ring
'''
code+='  rw ['+', '.join(f'he{i}' for i in range(8))+']\n'
code+=f'''  apply (mul_lt_mul_iff_right₀ (show (0:ℝ) < {D} by norm_num)).mp
  rw [fourteenthThetaExpansion_eq]
  exact (show ({D}:ℝ)*(1/10000000000000000000000) < {low} by norm_num).trans_le
    (fourteenthThetaExpansion_lower {xs} {' '.join(f'hx{i}' for i in range(8))})
end
end CarrySelfAdjointOperator
'''
(root/'CompletedNativeThetaFourteenthPolynomialEnclosure.lean').write_text(code)
print('Generated source identity and',len(code),'bytes polynomial certificate',flush=True)
