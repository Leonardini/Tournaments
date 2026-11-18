"""Level-0 check of the computed facts behind Appendix C ("Conjecture 2 at every order"): T* and W12.

Free tools only: FAS by an exact Held-Karp subset DP (pure Python), HS3 (fewest arcs meeting every
directed 3-cycle) by OR-Tools CP-SAT with proven optimality.  Vertex labels are 1-based, as in the paper.

  A  T* (majority of the paper's printed rho, sigma, tau): regular, strong, FAS = 17 > 16 = HS3.
  B  W12 (T* with 7 -> 1 reversed, plus a vertex 12 beaten only by 7): the paper's profile induces it,
     it is strong, has 60 directed 3-cycles, the paper's order leaves 17 arcs backward, FAS = 17, HS3 = 16.

Usage: python3 verify_appendix_c.py        (a few seconds)"""
import itertools, sys
from ortools.sat.python import cp_model

def maj(orders, n):                       # adjacency A[u][v] = u -> v, 0-based, from 1-based orders
    pos = [{v: i for i, v in enumerate(o)} for o in orders]
    m = len(orders)
    return [[u != v and 2 * sum(p[u + 1] < p[v + 1] for p in pos) > m for v in range(n)] for u in range(n)]

def fas(A):                               # exact: g[S] = min over v in S of g[S - v] + |out(v) & S|
    n = len(A); out = [sum(1 << v for v in range(n) if A[u][v]) for u in range(n)]
    g = [0] * (1 << n)
    for S in range(1, 1 << n):
        best = 10 ** 9; T = S
        while T:
            v = (T & -T).bit_length() - 1; T &= T - 1
            c = g[S & ~(1 << v)] + bin(out[v] & S).count("1")
            if c < best: best = c
        g[S] = best
    return g[(1 << n) - 1]

def triangles(A):
    n = len(A)
    return [(a, b, c) for a, b, c in itertools.combinations(range(n), 3)
            if (A[a][b] and A[b][c] and A[c][a]) or (A[a][c] and A[c][b] and A[b][a])]

def hs3(A):                               # minimum number of arcs meeting every directed 3-cycle
    n = len(A); m = cp_model.CpModel()
    x = {(u, v): m.NewBoolVar("") for u in range(n) for v in range(n) if A[u][v]}
    arc = lambda a, b: (a, b) if A[a][b] else (b, a)
    for a, b, c in triangles(A):
        m.AddBoolOr([x[arc(a, b)], x[arc(b, c)], x[arc(c, a)]])
    m.Minimize(sum(x.values()))
    s = cp_model.CpSolver(); s.parameters.num_workers = 1
    assert s.Solve(m) == cp_model.OPTIMAL
    return round(s.ObjectiveValue())

def strong(A):
    n = len(A)
    def reach(adj):
        seen = {0}; stack = [0]
        while stack:
            u = stack.pop()
            for v in range(n):
                if adj(u, v) and v not in seen: seen.add(v); stack.append(v)
        return len(seen) == n
    return reach(lambda u, v: A[u][v]) and reach(lambda u, v: A[v][u])

ok = True
def claim(label, cond):
    global ok
    print(f"  [{'PASS' if cond else 'FAIL'}] {label}"); ok &= bool(cond)


print("A. T*")
rho, sig, tau = (4, 5, 6, 11, 8, 9, 10, 2, 7, 1, 3), (10, 8, 9, 1, 2, 3, 7, 5, 6, 4, 11), (3, 7, 11, 1, 2, 6, 4, 5, 9, 10, 8)
T = maj([rho, sig, tau], 11)                                       # the profile as printed in the paper
old = [(4, 5, 6, 11, 8, 9, 10, 2, 7, 1, 3), (9, 1, 2, 3, 7, 5, 6, 4, 11, 10, 8), (10, 8, 3, 7, 11, 1, 2, 6, 4, 5, 9)]
claim("the paper's profile and the Level-1 script's profile induce the same T*", maj(old, 11) == T)
claim("regular (every out-degree 5) and strong", all(sum(r) == 5 for r in T) and strong(T))
fT, hT = fas(T), hs3(T)
claim(f"FAS(T*) = {fT} = 17 and HS3(T*) = {hT} = 16", (fT, hT) == (17, 16))

print("B. W12")
W = [r[:] + [False] for r in T] + [[False] * 12]
assert W[6][0]; W[6][0], W[0][6] = False, True                   # reverse 7 -> 1
for x in range(11):
    if x == 6: W[6][11] = True                                    # 7 -> 12
    else: W[11][x] = True                                         # 12 beats every other vertex
P12 = [(1, 2, 7, 12, 3, 5, 6, 4, 11, 9, 10, 8), (6, 11, 12, 8, 9, 10, 1, 2, 3, 7, 4, 5), (4, 5, 10, 8, 9, 3, 7, 12, 11, 1, 2, 6)]
claim("the paper's three orders induce W12", maj(P12, 12) == W)
claim(f"strong, with {len(triangles(W))} = 60 directed 3-cycles", strong(W) and len(triangles(W)) == 60)
order = (12, 11, 10, 8, 9, 1, 2, 3, 7, 6, 4, 5); pos = {v - 1: i for i, v in enumerate(order)}
back = sum(W[u][v] and pos[u] > pos[v] for u in range(12) for v in range(12))
fW, hW = fas(W), hs3(W)
claim(f"the paper's order leaves {back} = 17 arcs backward; FAS = {fW} = 17; HS3 = {hW} = 16", (back, fW, hW) == (17, 17, 16))

print("ALL APPENDIX C CHECKS PASS" if ok else "SOME APPENDIX C CHECK FAILED")
sys.exit(0 if ok else 1)
