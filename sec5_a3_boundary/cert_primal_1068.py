#!/usr/bin/env python3
# cert_primal_1068.py — PRIMAL certificate for alpha*(allGraphs[[1068]]) = 2/3: a MINIMAL set of
# linear orders (voters) with rational weights s.t. every arc u->v is forward in >= 2/3 of the mass.
# Independent Python cross-check of the slow R/Rcplex construction. Never materialises the 11! orders:
#   (1) column generation (weighted-MAS DP oracle, LP via PuLP/CBC) -> order pool converging to 2/3;
#   (2) enrich the pool by the C_11 automorphism (+ reverses) so the min-cardinality ILP has options;
#   (3) MIN-CARDINALITY ILP in CPLEX -> fewest certifying orders (proven optimal over the pool);
#   (4) exact rational weights + independent fractions-based verification.
import pulp, cplex
from fractions import Fraction as F

rows = ["01111100000","00110100011","00011100110","00001110011","01000011101",
        "00001001111","11100101000","11110000010","11010011000","10001010101","10100011100"]
n = len(rows); A = [[int(c) for c in r] for r in rows]
assert all(A[i][j]+A[j][i]==1 for i in range(n) for j in range(n) if i!=j) and all(sum(A[i])==5 for i in range(n))
arcs = [(u,v) for u in range(n) for v in range(n) if A[u][v]==1]; E = len(arcs)

def agree_vec(order):
    pos = [0]*n
    for k,x in enumerate(order): pos[x] = k
    return [1 if pos[u] < pos[v] else 0 for (u,v) in arcs]

def oracle(mu):
    W = [[0.0]*n for _ in range(n)]
    for k,(u,v) in enumerate(arcs): W[u][v] = mu[k]
    contrib = [None]*(1<<n); contrib[0] = [0.0]*n
    for S in range(1, 1<<n):
        low = (S & -S).bit_length()-1; cp = contrib[S^(1<<low)]; wl = W[low]
        contrib[S] = [cp[v]+wl[v] for v in range(n)]
    NEG=-1e18; f=[NEG]*(1<<n); f[0]=0.0; par=[-1]*(1<<n)
    for S in range(1<<n):
        fS=f[S]
        if fS<=NEG/2: continue
        cS=contrib[S]
        for v in range(n):
            if S>>v&1: continue
            ns=S|(1<<v); val=fS+cS[v]
            if val>f[ns]: f[ns]=val; par[ns]=v
    S=(1<<n)-1; order=[0]*n
    for k in range(n-1,-1,-1):
        v=par[S]; order[k]=v; S^=(1<<v)
    return f[(1<<n)-1], order

# ---- (1) column generation ----
def solve_dual(pool):
    p = pulp.LpProblem("d", pulp.LpMinimize)
    mu=[pulp.LpVariable(f"m{k}",lowBound=0) for k in range(E)]; lam=pulp.LpVariable("l",lowBound=0)
    p += lam; p += pulp.lpSum(mu)==1
    for O in pool:
        av=agree_vec(O); p += pulp.lpSum(av[k]*mu[k] for k in range(E)) <= lam
    p.solve(pulp.PULP_CBC_CMD(msg=0)); return [mu[k].value() for k in range(E)], lam.value()
pool=[list(range(n))]
for _ in range(500):
    muv,lam = solve_dual(pool); val,O = oracle(muv)
    if val > lam+1e-7: pool.append(O)
    else: break
print(f"(1) column generation: {len(pool)} cut-orders; alpha* = {lam:.6f} (2/3={2/3:.6f})")

# ---- (2) enrich by the order-11 automorphism sig and reverses ----
sig=[1,2,3,5,10,9,7,0,6,4,8]                      # 0-based automorphism (11-cycle)
big=set()
for O in pool:
    for Q0 in (O, O[::-1]):
        Q=Q0
        for _ in range(11): big.add(tuple(Q)); Q=[sig[x] for x in Q]
P=[list(t) for t in big]; AV=[agree_vec(O) for O in P]
print(f"(2) enriched pool: {len(P)} orders (C_11 images + reverses)")

# ---- (3) MIN-CARDINALITY ILP in CPLEX ----
def mincard(P, AV, thr=2.0/3.0):
    m=len(P); c=cplex.Cplex()
    for s in (c.set_results_stream,c.set_log_stream,c.set_warning_stream): s(None)
    c.variables.add(lb=[0]*m, ub=[1]*m, names=[f"x{i}" for i in range(m)])       # 0..m-1
    c.variables.add(obj=[1]*m, types=["B"]*m, names=[f"z{i}" for i in range(m)]) # m..2m-1
    c.objective.set_sense(c.objective.sense.minimize)
    c.linear_constraints.add(lin_expr=[cplex.SparsePair(list(range(m)),[1]*m)], senses=["E"], rhs=[1.0])
    for e in range(E):
        idx=[i for i in range(m) if AV[i][e]]
        # 3*sum(x) >= 2  (exact integer data; avoids the inexact float 2/3 boundary)
        c.linear_constraints.add(lin_expr=[cplex.SparsePair(idx,[3.0]*len(idx))], senses=["G"], rhs=[2.0])
    for i in range(m):
        c.linear_constraints.add(lin_expr=[cplex.SparsePair([i,m+i],[1.0,-1.0])], senses=["L"], rhs=[0.0])
    c.parameters.threads.set(2); c.solve()
    zv=c.solution.get_values(list(range(m,2*m)))
    return [i for i in range(m) if zv[i]>0.5], c.solution.get_status_string()
sel, st = mincard(P, AV)
print(f"(3) CPLEX min-cardinality = {len(sel)} orders  [{st}]")

# ---- (4) exact rational weights + independent verification ----
def weights(sel):
    p=pulp.LpProblem("w",pulp.LpMaximize)
    x=[pulp.LpVariable(f"x{i}",lowBound=0) for i in range(len(sel))]; a=pulp.LpVariable("a")
    p += a; p += pulp.lpSum(x)==1
    for e in range(E): p += pulp.lpSum(AV[sel[i]][e]*x[i] for i in range(len(sel))) >= a
    p.solve(pulp.PULP_CBC_CMD(msg=0)); return [x[i].value() for i in range(len(sel))]
wv=weights(sel); w=[F(v).limit_denominator(10**6) for v in wv]; s=sum(w); w=[wi/s for wi in w]
agr=[sum(w[i] for i in range(len(sel)) if AV[sel[i]][e]) for e in range(E)]
ma=min(agr); tight=sum(1 for g in agr if g==F(2,3))
print(f"(4) exact min-edge-agreement = {ma} = {float(ma):.6f}; certifies >= 2/3: {ma>=F(2,3)}; tight edges: {tight}/{E}")
print(f"\nMINIMAL PRIMAL CERTIFICATE for alpha*=2/3  ({len(sel)} orders, earliest-ranked first, 0-based):")
for i in range(len(sel)):
    nb = sum(1 for e in range(E) if not AV[sel[i]][e])   # #back-arcs of this order (11-level info)
    print(f"  w={str(w[i]):>7}  back-arcs={nb:2d}  order: {P[sel[i]]}")
