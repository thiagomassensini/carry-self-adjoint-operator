#!/usr/bin/env python3
"""Illustrative plot only; use the JSON/Lean audit for rigorous claims."""
import argparse
import json
from pathlib import Path
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from flint import arb,ctx

p=argparse.ArgumentParser(description=__doc__)
p.add_argument('--certificate',type=Path,required=True)
p.add_argument('--output',type=Path,required=True)
args=p.parse_args()
ctx.prec=768
d=json.loads(args.certificate.read_text())
c0=float(arb(d['source_c0']).mid())
mu1=float(arb(d['source_mu1']).mid())
zero=float(arb(d['positive_to_negative_transition_u']).mid())
u=np.linspace(0,1.05,1500)
phi=np.zeros_like(u)
for j in range(1,17):
    phi+=4*np.pi*j*j*np.exp(5*u/2)*(2*np.pi*j*j*np.exp(2*u)-3)*np.exp(-np.pi*j*j*np.exp(2*u))
value=(mu1/(4*c0)*u*u-u**4/12)*phi
fig,ax=plt.subplots(figsize=(8.5,4.8),layout='constrained')
fig.suptitle('Primeiro resto ímpar: integral positiva com contribuição negativa',fontsize=12)
ax.plot(u,value,color='#263747',linewidth=1.7)
ax.fill_between(u,value,0,where=value>=0,color='#3c9d74',alpha=.65,label=r'$M_+\approx8{,}34837\times10^{-5}$')
ax.fill_between(u,value,0,where=value<0,color='#dc7847',alpha=.65,label=r'$M_-\approx6{,}50044\times10^{-5}$')
ax.axhline(0,color='#65717b',linewidth=.7)
ax.axvline(zero,color='#5a6570',linestyle='--',linewidth=1)
ax.annotate(r'$u_*\approx0{,}372330$',xy=(zero,0),xytext=(zero+.09,max(value)*.40),
            arrowprops={'arrowstyle':'->','color':'#5a6570'},fontsize=10)
ax.set(xlabel=r'$u$',ylabel=r'$\mathcal{R}_{1,0}(u)\,\Phi(u)$',xlim=(0,1.05))
ax.ticklabel_format(axis='y',style='sci',scilimits=(0,0))
ax.grid(alpha=.17)
ax.legend(loc='upper right',frameon=False,fontsize=10)
ax.text(.98,.08,r'$R_{1,0}=M_+-M_-\approx1{,}84793\times10^{-5}$',
        transform=ax.transAxes,ha='right',fontsize=10)
fig.supxlabel('Ilustração numérica do caso inicial; o sinal geral ainda está aberto.',fontsize=9)
fig.savefig(args.output,dpi=180)
