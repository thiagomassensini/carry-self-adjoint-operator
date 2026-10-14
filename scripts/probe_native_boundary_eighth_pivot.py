"""Explore the first open source pivot; numerical readings are NOT proofs.

Uses the preserved theta-integral cache and the unchanged division-free
characteristic/response recurrence. No zero ordinates or fitted moments enter.
"""
from pathlib import Path
import hashlib, itertools, json, re
import mpmath as mp

repo = Path('/home/thlinux/carry-self-adjoint-operator')
cache = Path('/home/thlinux/.native_height_cache/theta-even-moments-v1-dps1600.json')
data = json.loads(cache.read_text())
certificate = repo / 'CarrySelfAdjointOperator/CompletedNativeThetaFourteenthSourceCertificate.lean'
s = certificate.read_text()
boxes = []
for j in range(8):
    frag = s.split('theorem nativeSourceThetaIntegral_fourteenth_box_'+str(2*j)+' :')[1].split(':= by')[0]
    rr = re.findall(r'\((\d+)/(\d+):ℝ\)', frag)
    assert len(rr) == 2
    boxes.append([(int(a),int(b)) for a,b in rr])

def moments(a):
    c = [mp.mpf(1)/2-a[0]/4]+[
        (-1)**j*(a[j-1]/mp.factorial(2*j-2)-a[j]/(4*mp.factorial(2*j)))
        for j in range(1,9)]
    h = []
    for n in range(8):
        h.append((-(n+1)*c[n+1]-mp.fsum(h[k]*c[n-k] for k in range(n)))/c[0])
    return h

def pivot(a):
    h = moments(a)
    M = mp.matrix(3); v = mp.matrix(3,1)
    for i in range(3):
        v[i] = h[i+4]
        for j in range(3): M[i,j] = h[i+j+1]
    return h[7]-(v.T*mp.lu_solve(M,v))[0]

runs = []
for dps in [100,180]:
    mp.mp.dps = dps
    a = [mp.mpf(data['moments'][str(j)])/2**(2*j) for j in range(9)]
    h = moments(a)
    p = pivot(a)
    c0 = mp.mpf(1)/2-a[0]/4
    c8 = a[7]/mp.factorial(14)-a[8]/(4*mp.factorial(16))
    ceiling_gap = c0*p/8
    result = {'dps':dps,'h':[mp.nstr(x,60) for x in h],
              'odd_four_pivot':mp.nstr(p,60),
              'odd_four_threshold':mp.nstr(h[7]-p,60),
              'relative_margin':mp.nstr(p/h[7],40),
              'theta16':mp.nstr(a[8],60),
              'characteristic_c8':mp.nstr(c8,60),
              'characteristic_ceiling':mp.nstr(c8+ceiling_gap,60),
              'characteristic_ceiling_gap':mp.nstr(ceiling_gap,60),
              'raw_mu16':mp.nstr(mp.factorial(16)*c8,60),
              'variations':[]}
    for j,bounds in enumerate(boxes):
        vals=[]
        for num,den in bounds:
            b=a.copy(); b[j]=mp.mpf(num)/den
            vals.append(mp.nstr(pivot(b),45))
        result['variations'].append({'theta_power':2*j,'pivot_at_certified_endpoints':vals})
    candidates=[]
    for choices in itertools.product(range(2),repeat=8):
        b = [mp.mpf(boxes[j][choices[j]][0])/boxes[j][choices[j]][1] for j in range(8)] + [a[8]]
        candidates.append((pivot(b),choices))
    low,lc=min(candidates); high,hc=max(candidates)
    result['sampled_corners']={'min_pivot':mp.nstr(low,60),'min_choices':lc,
                               'max_pivot':mp.nstr(high,60),'max_choices':hc,
                               'theta16_held_at_cached_value':True,
                               'count':len(candidates)}
    runs.append(result)

record={'status':'NUMERICAL_EXPLORATION_ONLY','native_source_changed':False,
        'moment_pipeline':'theta integral -> original even characteristic -> division-free log-derivative recurrence',
        'cache':{'path':str(cache),'sha256':hashlib.sha256(cache.read_bytes()).hexdigest(),'recorded_dps':data['dps']},
        'source_box_file':{'path':str(certificate),'sha256':hashlib.sha256(certificate.read_bytes()).hexdigest()},
        'boxes_rational':boxes,'runs':runs}
Path('/tmp/native-boundary-next-pivot.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps({'status':record['status'],'pivot':runs[-1]['odd_four_pivot'],
                  'threshold':runs[-1]['odd_four_threshold'],'relative_margin':runs[-1]['relative_margin'],
                  'sampled_corners':runs[-1]['sampled_corners'],'variations':runs[-1]['variations']},indent=2))
