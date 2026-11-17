"""Certificates for the paper-1 appendix "Conjecture 2 fails at every order n >= 11" (1-based labels as in the
manuscript).  T* = majority of rho, sigma, tau (Section 4).  W12 = T* with the arc 7 -> 1 reversed, plus a vertex 12
beaten only by 7.  For W12 and for C3[T*, TT_1, TT_1] (n = 13) this prints and re-checks: a 3-voter profile inducing
it (found by a small ILP, then verified), strong connectivity, an optimal order (FAS) and a minimum 3-cycle hitting
set (HS3), both from Gurobi with proven optimality, and FAS once more from the exact DP (mas_dp.c here; build it with cc -O3 -o mas_dp mas_dp.c).
One thread.  Usage: python3 appendix_conj2_certs.py"""
import sys, os, subprocess, tempfile, itertools
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
import gurobipy as gp
from gurobipy import GRB
from hs3 import solve_hs3, solve_fas, substitute, triangles, _env
import networkx as nx

def maj(orders, n):
    pos = [{v: i for i, v in enumerate(o)} for o in orders]
    return [[u != v and sum(p[u] < p[v] for p in pos) >= 2 for v in range(1, n + 1)] for u in range(1, n + 1)]
def profile3(A):   # three linear orders whose majority is A (ILP feasibility), 1-based output
    n = len(A); m = gp.Model(env=_env()); m.Params.Threads = 1
    y = {(p, u, v): m.addVar(vtype=GRB.BINARY) for p in range(3) for u in range(n) for v in range(u + 1, n)}
    pre = lambda p, u, v: y[(p, u, v)] if u < v else 1 - y[(p, v, u)]
    for p in range(3):
        for u, v, w in itertools.combinations(range(n), 3):
            m.addConstr(pre(p, u, v) + pre(p, v, w) - pre(p, u, w) <= 1); m.addConstr(pre(p, u, v) + pre(p, v, w) - pre(p, u, w) >= 0)
    for u in range(n):
        for v in range(n):
            if A[u][v]: m.addConstr(gp.quicksum(pre(p, u, v) for p in range(3)) >= 2)
    m.optimize(); assert m.Status == GRB.OPTIMAL
    before = lambda p, u, v: y[(p, u, v)].X > 0.5 if u < v else y[(p, v, u)].X < 0.5      # u precedes v for voter p
    return [tuple(1 + v for v in sorted(range(n), key=lambda v: sum(before(p, u, v) for u in range(n) if u != v)))
            for p in range(3)]
def mas_dp(A):
    n = len(A)
    with tempfile.NamedTemporaryFile("w", suffix=".txt") as f:
        f.write(" ".join(str(sum(1 << u for u in range(n) if A[u][v])) for v in range(n)) + "\n"); f.flush()
        return int(subprocess.run([os.path.join(HERE, "mas_dp"), f.name, str(n), "0", "1"],
                                  capture_output=True, text=True, check=True).stdout.split()[2])
def report(name, A):
    n = len(A); print(f"== {name}: n = {n}, out-degrees {sorted(sum(r) for r in A)}")
    g = nx.DiGraph([(u, v) for u in range(n) for v in range(n) if A[u][v]]); print("   strong:", nx.is_strongly_connected(g))
    P = profile3(A); assert maj(P, n) == A; print("   3-voter profile (verified):", *P, sep="\n      ")
    f = solve_fas(A); h = solve_hs3(A); assert f["optimal"] and h["optimal"]
    print(f"   FAS = {f['ub']} (optimal order {tuple(v + 1 for v in f['order'])}); exact DP: {mas_dp(A)}")
    print(f"   HS3 = {h['ub']} ({h['ntri']} cyclic triangles)")
    return f["ub"], h["ub"]

rho = (4, 5, 6, 11, 8, 9, 10, 2, 7, 1, 3); sig = (9, 1, 2, 3, 7, 5, 6, 4, 11, 10, 8); tau = (10, 8, 3, 7, 11, 1, 2, 6, 4, 5, 9)
T = maj([rho, sig, tau], 11)
W = [r[:] + [False] for r in T] + [[False] * 12]
assert W[6][0]; W[6][0], W[0][6] = False, True                 # reverse 7 -> 1
for x in range(11):
    if x == 6: W[6][11] = True                                    # 7 -> 12
    else: W[11][x] = True                                         # 12 -> everything else
report("T*", T); report("W12", W)
TT = lambda a: [[i < j for j in range(a)] for i in range(a)]
C3 = [[False, True, False], [False, False, True], [True, False, False]]
report("C3[T*, TT_1, TT_1]", substitute(C3, [T, TT(1), TT(1)]))
