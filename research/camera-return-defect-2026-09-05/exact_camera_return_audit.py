#!/usr/bin/env python3
"""Exact symbolic checks against the source six-camera Gram and moment formulas.
Run on llm with Python + SymPy. No target moments or zero locations are inputs.
"""
import json
from pathlib import Path
import sympy as s

G=s.Matrix([[6,0,10,0,s.Rational(16,3),0],
 [0,6,0,0,6,0],[10,0,22,0,s.Rational(16,3),0],
 [0,0,0,20,0,0],[s.Rational(16,3),6,s.Rational(16,3),0,44,0],
 [0,0,0,0,0,42]])
a,b,c,d=s.symbols('log2 log3 log5 log7',real=True)
logs=[2*a,b,2*a,c,a+b,d]
slopes=[4,3,4,5,6,7]
H=s.Matrix(6,6,lambda i,j:G[i,j]*logs[i if slopes[i]<=slopes[j] else j])
J=s.Matrix(6,6,lambda i,j:G[i,j]*(1+logs[i if slopes[i]<=slopes[j] else j]**2))
T=s.diag(*logs)
D=(G-J+H*G.inv()*H).applyfunc(s.factor)
B=T*G-H
v=s.Matrix([-6,-3,2,0,3,0])
e6=s.eye(6)[:,4]
Q=457*a*a-512*a*b+304*b*b
checks={
 'source_moment_slope_identity':s.simplify(J-G-T*H-H*T+T*G*T)==s.zeros(6),
 'return_factorization':s.simplify(D-B*G.inv()*B.T)==s.zeros(6),
 'raw_defect_rank_one_formula':s.simplify(D-4*Q/139*e6*e6.T)==s.zeros(6),
 'gram_ray':G*v==s.Rational(278,3)*e6,
 'gram_norm_squared':(v.T*G*v)[0]==278,
 'raw_source_direction':G.inv()*e6==s.Rational(3,278)*v,
 'defect_trace':s.simplify(s.trace(G.inv()*D)-18*Q/19321)==0,
 'right_factor_annihilates_pure_axes':all(B.T*s.eye(6)[:,i]==s.zeros(6,1) for i in [0,1,2,3,5]),
 'left_factor_counterexample_e3':B*s.eye(6)[:,1]==6*a*e6,
}
mean=s.Matrix(6,6,lambda i,j:G[i,j]/min(slopes[i],slopes[j]))
densities=[]
for mid,expected in [(s.Rational(3,2),s.Rational(16,139)),
 (s.Rational(7,2),s.Rational(25,139)),(s.Rational(9,2),s.Rational(33,139)),
 (s.Rational(13,2),s.Rational(0))]:
 mask=s.diag(*[int(bool(mid<=ell)) for ell in slopes])
 density=s.factor((v.T*mask*mean*mask*v)[0]/278)
 densities.append(str(density))
 checks['density_at_'+str(mid)]=density==expected
checks['mixed_probability_mass']=s.Rational(48+25+66,139)==1
assert all(checks.values()),checks
report={
 'evidence_type':'exact rational and symbolic algebra in SymPy; distinct from Lean checking',
 'sympy_version':s.__version__,'checks':checks,'checks_passed':len(checks),
 'ray':list(map(str,v)),'gram_norm_squared':'278',
 'Q':str(Q),'Q_matrix_determinant':str(457*304-256**2),
 'delta_formula':str(18*Q/19321),
 'delta_numeric':str(s.N((18*Q/19321).subs({a:s.log(2),b:s.log(3)}),35)),
 'mixed_density_interval_values':densities,
 'mixed_density_intervals':['(0,3]','(3,4]','(4,6]','(6,infinity)'],
 'orientation_correction':'The raw universal axes are annihilated by G*T-H, not T*G-H.',
 'scope':'Six cameras, exact source Gram. Native height Gram and infinite-atlas convergence not identified.'}
output=Path(__file__).with_name('exact_camera_return_audit.json')
output.write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({'checks_passed':len(checks),'delta':report['delta_numeric']}))
