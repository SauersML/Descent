"""T1b: which observed-scale h2 convention does liabilityScaleH2 invert?

Convention A: h2_obs = Var(E[D|G]) / Var(D)          (variance of the true
              conditional mean -- "variance explained by G", nonlinear)
Convention B: h2_obs = Cov(G,D)^2 / (Var(G) Var(D))  (R^2 of the best LINEAR
              predictor of D from G -- what a GWAS on a 0/1 phenotype
              estimates, and what the Lean docstring's step 4 derives)
Both by exact quadrature.  Lean: VarianceComponents.lean:435
    liabilityScaleH2 h2_obs K z = h2_obs*K*(1-K)/z^2
"""
import math
def phi(x): return math.exp(-0.5*x*x)/math.sqrt(2*math.pi)
def Phi(x): return 0.5*math.erfc(-x/math.sqrt(2))
def Phi_inv(p):
    lo,hi=-40.,40.
    for _ in range(200):
        m=.5*(lo+hi)
        if Phi(m)<p: lo=m
        else: hi=m
    return .5*(lo+hi)
n=8000; a,b=-9.,9.; h=(b-a)/n
Q=[(a+i*h, h/3*(1 if i in (0,n) else (4 if i%2 else 2))) for i in range(n+1)]
print(f"{'K':>7}{'h2_l':>7}{'h2obsA':>11}{'h2obsB':>11}{'leanA':>10}{'leanB':>10}{'errA':>9}{'errB':>9}")
for K in (0.5,0.2,0.05,0.01,0.001):
    T=Phi_inv(1-K); z=phi(T)
    for h2 in (0.02,0.1,0.3,0.5,0.8):
        sg=math.sqrt(h2); se=math.sqrt(1-h2)
        m1=m2=cov=0.
        for x,w in Q:
            d=phi(x)*w; p=Phi((sg*x-T)/se)
            m1+=d*p; m2+=d*p*p; cov+=d*(sg*x)*p
        varE=m2-m1*m1; VarD=m1*(1-m1)
        A=varE/VarD
        B=cov*cov/(h2*VarD)
        la=A*K*(1-K)/z**2; lb=B*K*(1-K)/z**2
        print(f"{K:>7}{h2:>7}{A:>11.6f}{B:>11.6f}{la:>10.4f}{lb:>10.4f}{(la-h2)/h2:>9.3f}{(lb-h2)/h2:>9.3f}")
