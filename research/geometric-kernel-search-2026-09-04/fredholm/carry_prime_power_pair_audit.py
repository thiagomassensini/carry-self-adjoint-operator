import math, json, time
import mpmath as mp
start=time.monotonic()
P=10_000_000
sieve=bytearray(b'\1')*(P+1)
sieve[0:2]=b'\0\0'
for p in range(2,math.isqrt(P)+1):
 if sieve[p]:
  a=p*p;sieve[a:P+1:p]=b'\0'*((P-a)//p+1)
primes=[p for p in range(2,P+1) if sieve[p]]

def ratios(h):
 return {'R2_g0g2_g1sq':h[0]*h[2]/h[1]**2,'R3_g0sqg3_g1cube':h[0]**2*h[3]/h[1]**3,'adjacent_g1g3_g2sq':h[1]*h[3]/h[2]**2}
def interval_ratios(lo,hi):
 return {'R2_g0g2_g1sq':[lo[0]*lo[2]/hi[1]**2,hi[0]*hi[2]/lo[1]**2],
 'R3_g0sqg3_g1cube':[lo[0]**2*lo[3]/hi[1]**3,hi[0]**2*hi[3]/lo[1]**3],
 'adjacent_g1g3_g2sq':[lo[1]*lo[3]/hi[2]**2,hi[1]*hi[3]/lo[2]**2]}
rows=[]
for bound in [1_000_000,10_000_000]:
 pp=[p for p in primes if p<=bound]
 h=[math.fsum(1/((p-1)*math.log(p)**(2*n+2)) for p in pp) for n in range(4)]
 tail=[(bound/(bound-1))/((2*n+1)*math.log(bound)**(2*n+1)) for n in range(4)]
 # Deliberately generous numerical margin around double precision sums.
 lo=[v-1e-10 for v in h];hi=[h[n]+tail[n]+1e-10 for n in range(4)]
 rows.append({'prime_cutoff':bound,'prime_count':len(pp),'g_prefix':h,'analytic_all_integer_tail_upper':tail,
              'ratios_prefix':ratios(h),'ratio_enclosures_with_1e_minus10_numerical_margin':interval_ratios(lo,hi)})

def native(dps):
 mp.mp.dps=dps
 # A(u)=2 sum_{n>=1} exp(u/2-pi*n*n*exp(2u)).
 # For u>=0, n>8 contributes less than a constant times exp(-81*pi).
 def A(u):
  v=mp.exp(2*u);return 2*mp.exp(u/2)*sum(mp.exp(-mp.pi*n*n*v) for n in range(1,9))
 aa=[mp.quad(lambda u:u**(2*j)*A(u),[0,mp.mpf('.125'),mp.mpf('.25'),mp.mpf('.5'),1,2,4,6]) for j in range(4)]
 mu=[mp.mpf('.5')-aa[0]/4]
 for j in range(1,4):mu.append((2*j)*(2*j-1)*aa[j-1]-aa[j]/4)
 # For c_4 need A_8.
 a8=mp.quad(lambda u:u**8*A(u),[0,mp.mpf('.125'),mp.mpf('.25'),mp.mpf('.5'),1,2,4,6])
 mu.append(8*7*aa[3]-a8/4)
 c=[(-1)**j*mu[j]/mp.factorial(2*j) for j in range(5)]
 h=[]
 for n in range(4):h.append((-(n+1)*c[n+1]-sum(h[k]*c[n-k] for k in range(n)))/c[0])
 return {'precision_dps':dps,'A_even':[str(a) for a in aa]+[str(a8)],'h':[str(v) for v in h],
         'ratios':{k:str(v) for k,v in ratios(h).items()}}
result={'construction':'S_(p,k)=1/log p; u_(p,k)=p^(-k/2)/log p','workers':1,'prime_audit':rows,'native_theta_audit':[native(50),native(80)]}
result['elapsed_seconds']=time.monotonic()-start
print(json.dumps(result,indent=2))
