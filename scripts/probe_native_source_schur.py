#!/usr/bin/env python3
"""Replay published source intervals to inspect native Schur cancellation.

This is finite external evidence, not a new integration or all-order proof.
The native coefficients and all old-new couplings are kept unchanged.
"""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import sys
from flint import arb, arb_mat, ctx

sys.dont_write_bytecode = True


def main(args):
    ctx.prec = 1200
    root = args.repo_root
    engine = root/'scripts/certify_native_negative_channel.py'
    spec = importlib.util.spec_from_file_location('theta_engine',engine)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    source_path = root/'research/native-kernel-series-2026-10-14/certificate-1024.json'
    data = json.loads(source_path.read_text())
    assert data['theta_engine_sha256'] == hashlib.sha256(engine.read_bytes()).hexdigest()
    for name,digest in data['source_lean_sha256'].items():
        assert hashlib.sha256((root/'CarrySelfAdjointOperator'/name).read_bytes()).hexdigest() == digest
    moments = [arb(z['infinite_integral']) for z in data['source_moments_and_tails']]
    c,m = mod.log_coefficients(moments,12)
    cases = []
    for s in [0,1]:
        for n in range(1,6):
            H = arb_mat([[m[i+j+s] for j in range(n)] for i in range(n)])
            b = arb_mat([[m[i+n+s]] for i in range(n)])
            v = H.solve(b)
            absorbed = (b.transpose()*v)[0,0]
            pivot = m[2*n+s]-absorbed
            remainder = -(2*n+s+1)*c[2*n+s+1]-sum(m[k]*c[2*n+s-k]
                                                               for k in range(2*n+s))-c[0]*absorbed
            assert (remainder-c[0]*pivot).contains(0)
            assert pivot > 0 and remainder > 0
            full = arb_mat([[m[i+j+s] for j in range(n+1)] for i in range(n+1)])
            critical = arb_mat([[-v[i,0]] for i in range(n)]+[[arb(1)]])
            critical_energy = (critical.transpose()*full*critical)[0,0]
            assert (critical_energy-pivot).contains(0)
            independent_pivot = mod.ldl([[full[i,j] for j in range(n+1)] for i in range(n+1)])[-1]
            assert pivot.overlaps(independent_pivot)
            cases.append({'offset':s,'old_size':n,'new_size':n+1,
                          'native_diagonal':str(m[2*n+s]),'old_new_coupling_energy':str(absorbed),
                          'native_Schur_pivot':str(pivot),'native_source_recurrence_remainder':str(remainder),
                          'pivot_divided_by_new_diagonal':str(pivot/m[2*n+s]),
                          'critical_direction_and_LDL_cross_checks':True})
    eighth = next(x for x in cases if x['offset']==1 and x['old_size']==3)
    old_eighth = json.loads((root/'research/native-negative-channel-2026-10-14/certificate-768.json').read_text())
    assert arb(eighth['native_Schur_pivot']).overlaps(arb(old_eighth['normalized_odd_fourth_LDL_pivot']))
    output = {'status':'EXTERNAL_REPLAY_OF_PUBLISHED_SOURCE_INTERVALS_NOT_LEAN',
              'fresh_source_integration':False,
              'engine_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'native_source_and_normalizations_unchanged':True,
              'source_certificate_sha256':hashlib.sha256(source_path.read_bytes()).hexdigest(),
              'source_certificate':str(source_path.relative_to(root)),
              'source_engine_sha256':hashlib.sha256(engine.read_bytes()).hexdigest(),
              'cases':cases,'eighth_source_pivot_matches_previous_certificate':True,
              'all_order_positivity_proved':False}
    args.output.write_text(json.dumps(output,indent=2)+'\n')
    print(json.dumps({'status':output['status'],'finite_cases':len(cases),
                      'last_even_relative_margin':cases[4]['pivot_divided_by_new_diagonal'],
                      'last_odd_relative_margin':cases[-1]['pivot_divided_by_new_diagonal']},indent=2))


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--repo-root',type=Path,default=Path(__file__).resolve().parents[1])
    p.add_argument('--output',type=Path,required=True)
    main(p.parse_args())
