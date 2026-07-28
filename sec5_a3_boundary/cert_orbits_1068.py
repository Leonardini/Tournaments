#!/usr/bin/env python3
# cert_orbits_1068.py — how few Aut(T)=C_11 ORBITS can a 2/3-certificate of ce1068 use?
# The §2 minimal certificate uses 6 orders = 2 from each of 3 C_11-orbits. Question: is there a
# certificate whose support lies in only 1 or 2 orbits?
#
# THEORY (used to make this a finite, exact search):
#  * Every arc lies on a 3-cycle => in ANY 2/3-cert every arc is agreed by EXACTLY 2/3 of the mass.
#  * k=1 is impossible: one C_11-orbit has all 11 orders with the same back-count b (sigma preserves it),
#    so total forward-mass = 55-b is an integer, but a cert needs 55*(2/3)=110/3 (non-integer). PROVEN.
#  * Averaging any feasible cert over <sigma> keeps it feasible and makes it UNIFORM within each orbit.
#    So a 2-orbit cert exists  <=>  two orbits A,B and p in (0,1) with, for every arc-orbit class c,
#        p*j_A(c) + (1-p)*j_B(c) = 22/3,     j_X(c) = #orders of orbit X agreeing a rep arc of class c.
#    (uniform weights p/11 on A and (1-p)/11 on B.)  Exact rational search over pool orbits.
import pulp
from fractions import Fraction as F
from itertools import combinations

rows = ["01111100000","00110100011","00011100110","00001110011","01000011101",
        "00001001111","11100101000","11110000010","11010011000","10001010101","10100011100"]
n = len(rows); A = [[int(c) for c in r] for r in rows]
assert all(A[i][j]+A[j][i]==1 for i in range(n) for j in range(n) if i!=j) and all(sum(A[i])==5 for i in range(n))
arcs = [(u,v) for u in range(n) for v in range(n) if A[u][v]==1]; E = len(arcs)
aidx = {a:i for i,a in enumerate(arcs)}
sig = [1,2,3,5,10,9,7,0,6,4,8]                         # 0-based C_11 automorphism (11-cycle)

def agree_vec(order):
    pos=[0]*n
    for k,x in enumerate(order): pos[x]=k
    return tuple(1 if pos[u]<pos[v] else 0 for (u,v) in arcs)

def oracle(mu):
    W=[[0.0]*n for _ in range(n)]
    for k,(u,v) in enumerate(arcs): W[u][v]=mu[k]
    contrib=[None]*(1<<n); contrib[0]=[0.0]*n
    for S in range(1,1<<n):
        low=(S&-S).bit_length()-1; cp=contrib[S^(1<<low)]; wl=W[low]
        contrib[S]=[cp[v]+wl[v] for v in range(n)]
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

# ---- (1) column generation to the same cut-order pool ----
def solve_dual(pool):
    p=pulp.LpProblem("d",pulp.LpMinimize)
    mu=[pulp.LpVariable(f"m{k}",lowBound=0) for k in range(E)]; lam=pulp.LpVariable("l",lowBound=0)
    p+=lam; p+=pulp.lpSum(mu)==1
    for O in pool:
        av=agree_vec(O); p+=pulp.lpSum(av[k]*mu[k] for k in range(E))<=lam
    p.solve(pulp.PULP_CBC_CMD(msg=0)); return [mu[k].value() for k in range(E)], lam.value()
pool=[list(range(n))]
for _ in range(500):
    muv,lam=solve_dual(pool); val,O=oracle(muv)
    if val>lam+1e-7: pool.append(O)
    else: break
print(f"(1) column generation: {len(pool)} cut-orders; alpha* = {lam:.6f}")

# ---- (2) enrich by sigma-images and reverses (the SAME 4114-order pool) ----
big=set()
for O in pool:
    for Q0 in (O,O[::-1]):
        Q=list(Q0)
        for _ in range(11): big.add(tuple(Q)); Q=[sig[x] for x in Q]
P=sorted(big)
print(f"(2) enriched pool: {len(P)} orders")

# ---- arc-orbits under sigma (should be 5 classes of 11) ----
def sig_arc(a): return (sig[a[0]], sig[a[1]])
arc_class={}; classes=[]
for a in arcs:
    if a in arc_class: continue
    cid=len(classes); orb=[]; b=a
    for _ in range(11):
        arc_class[b]=cid; orb.append(b); b=sig_arc(b)
    classes.append(orb)
reps=[orb[0] for orb in classes]
print(f"arc-orbits under C_11: {len(classes)} classes, sizes {[len(o) for o in classes]}")

# ---- order-orbits under sigma ----
def sig_order(O): return tuple(sig[x] for x in O)
seen=set(); orbits=[]
for O in P:
    if O in seen: continue
    orb=[]; Q=O
    for _ in range(11):
        orb.append(Q); seen.add(Q); Q=sig_order(Q)
    orbits.append(orb)
print(f"order-orbits in pool: {len(orbits)} (each size {len(orbits[0])})")

# profile j_X(c) = # orders of orbit X agreeing rep arc of class c ; and back-count (shift-invariant)
def profile(orb):
    j=[0]*len(classes)
    for O in orb:
        av=agree_vec(O)
        for c in range(len(classes)):
            if av[aidx[reps[c]]]: j[c]+=1
    return tuple(j)
profs=[profile(o) for o in orbits]
backs=[E - sum(agree_vec(o[0])) for o in orbits]   # back-count of the orbit (same for all members)
uniq=sorted(set(profs))
print(f"distinct orbit profiles: {len(uniq)} (of {len(orbits)} orbits)")

TGT=F(22,3)   # need p*j_A(c)+(1-p)*j_B(c) = 22/3 for all c
def two_orbit(jA,jB):
    p=None
    for c in range(len(classes)):
        dA,dB=jA[c],jB[c]
        if dA==dB:
            if dA==TGT: continue     # never (integer)
            return None
        pc=(TGT-dB)/F(dA-dB)
        if p is None: p=pc
        elif p!=pc: return None
    if p is None or not (0<p<1): return None
    return p

# ---- k=1 : impossible (report the numeric confirmation) ----
one=[c for c in range(len(classes))]
k1=any(all(F(j)==TGT for j in prof) for prof in profs)
print(f"\nk=1 feasible in pool? {k1}  (theory: impossible, 55-b integer != 110/3)")

# ---- k=2 search over orbit pairs (dedup by profile) ----
prof2orbit={}
for oi,pr in enumerate(profs): prof2orbit.setdefault(pr,oi)
found=[]
plist=list(prof2orbit.keys())
for pa,pb in combinations(plist,2):
    p=two_orbit(pa,pb)
    if p is not None: found.append((p,pa,pb,prof2orbit[pa],prof2orbit[pb]))
print(f"\nk=2 orbit-pairs that certify 2/3 (uniform p/11, (1-p)/11): {len(found)}")
for p,pa,pb,oa,ob in found[:12]:
    print(f"  p={p}  backs=({backs[oa]},{backs[ob]})  profA={pa} profB={pb}")

if found:
    p,pa,pb,oa,ob=found[0]
    print(f"\n=== A 2-ORBIT CERTIFICATE (masses p={p} on orbit A, {1-p} on orbit B) ===")
    print(f"arc-orbit reps (class order): {reps}")
    for tag,orb,mass in (("A",orbits[oa],p),("B",orbits[ob],1-p)):
        print(f"-- orbit {tag}: mass {mass}, each of 11 orders weight {mass/11}, back-count {backs[oa if tag=='A' else ob]}")
        for O in orb: print(f"     {list(O)}")
    # exact verification: every arc agreed exactly 2/3
    w={}
    for O in orbits[oa]: w[O]=w.get(O,F(0))+p/11
    for O in orbits[ob]: w[O]=w.get(O,F(0))+(1-p)/11
    agr=[sum(w[O] for O in w if agree_vec(O)[e]) for e in range(E)]
    print(f"\nVERIFY: min arc-agreement = {min(agr)}, all == 2/3 ? {all(g==F(2,3) for g in agr)}; support size {sum(1 for v in w.values() if v>0)}")
else:
    print("\nNo 2-orbit certificate within the pool. => within this pool the minimum is 3 orbits (as in §2).")
    print("REFINE next: widen the orbit set (more cut-orders / all near-tight orbits) and repeat the pair search.")
