import json, sys
from multiprocessing import Pool
import pencil_freeness as F
jobs=[]
sd=90000
for m,per in ((800,2),(1600,1)):
    for (s,t) in ((0.0,0.0),(1.0,1.0)):
        for k in range(4 if m==800 else 3):
            sd+=1; jobs.append((m,per,sd,s,t))
with Pool(14) as p: r=p.map(F.work_free,jobs)
agg={}
for x in r: agg.setdefault((x['m'],x['s'],x['t']),[]).append(x['mean'])
out=[]
for (m,s,t),ms in sorted(agg.items()):
    n=len(ms); mu=sum(ms)/n
    var=sum((v-mu)**2 for v in ms)/(n-1)
    phi_a2=2.0*(m-1)/m+s*s
    fp=phi_a2*t*t + s*s*phi_a2 - s*s*t*t
    out.append(dict(m=m,s=s,t=t,chunks=n,mean=mu,sem_from_chunk_scatter=(var/n)**0.5,
                    free_prediction=fp,
                    unrotated=F.phi_abab_sparse(m,[1.0]*(m-1),[1.0]*(m-1),s,t)))
json.dump(out,sys.stdout,indent=1)
