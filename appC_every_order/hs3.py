"""Shared HS3 code: tournament builders, cyclic triangles, and the minimum 3-cycle hitting-set ILP
(paper 1, App. ilp-hitting) on Gurobi with Threads=1.

Symmetry breaking (`sb`), each valid only for the stated host class:
  "vt"    vertex-transitive host: translate the vertex of max d+ to 0  =>  d+(0) >= d+(v) for all v,
          where d+(v) = # hitting-set arcs leaving v.
  "paley" Paley(q) (x -> a x + b, a a nonzero square, are automorphisms; checked in paley_adj):
          additionally multiply by u^-1 for the S-out-neighbour u of 0 of max d+ (fixes 0, sends u -> 1)
          =>  x_{0->1} = 1  and  d+(1) >= d+(u) - M (1 - x_{0->u}) for u in N+(0).
"""
import itertools
import gurobipy as gp
from gurobipy import GRB


def paley_adj(q):
    """Paley tournament on GF(q), q = 3 mod 4 prime or 27; vertex 0 = 0, vertex 1 = 1."""
    if q == 27:  # GF(3)[x]/(x^3 - x + 1)
        els = list(itertools.product(range(3), repeat=3))
        def mul(a, b):
            c = [0] * 5
            for i in range(3):
                for j in range(3):
                    c[i + j] += a[i] * b[j]
            for k in (4, 3):  # x^3 = x - 1
                t = c[k]; c[k] = 0; c[k - 2] += t; c[k - 3] -= t
            return tuple(v % 3 for v in c[:3])
        add = lambda a, b: tuple((x + y) % 3 for x, y in zip(a, b))
        sub = lambda a, b: tuple((x - y) % 3 for x, y in zip(a, b))
        zero, one = (0, 0, 0), (1, 0, 0)
    else:
        els = list(range(q)); mul = lambda a, b: a * b % q
        add = lambda a, b: (a + b) % q; sub = lambda a, b: (a - b) % q; zero, one = 0, 1
    els.sort(key=lambda e: (e != zero, e != one))
    sq = {mul(a, a) for a in els if a != zero}
    assert len(sq) == (q - 1) // 2
    idx = {e: i for i, e in enumerate(els)}
    adj = [[False] * q for _ in range(q)]
    for a in els:
        for b in els:
            if a != b and sub(b, a) in sq:
                adj[idx[a]][idx[b]] = True
    for a in sq:  # every x -> a x + b (a square) is an automorphism
        for b in els:
            g = [idx[add(mul(a, e), b)] for e in els]
            assert sorted(g) == list(range(q))
            assert all(adj[g[i]][g[j]] == adj[i][j] for i in range(q) for j in range(q))
    return adj


def inmask_adj(inm):
    """adj[u][v] <=> u->v, from per-vertex in-masks (bit u of inm[v])."""
    n = len(inm)
    return [[bool(inm[v] >> u & 1) for v in range(n)] for u in range(n)]


def mckay_inmasks(bits, n):
    """McKay catalogue / gentourng bits (lower triangle column-major = upper triangle row-major;
    bit 0 <=> larger -> smaller) to per-vertex in-masks, as hs3fas.c decode()."""
    inm = [0] * n; k = 0
    for j in range(n):
        for i in range(j + 1, n):
            if bits[k] == "0": inm[j] |= 1 << i
            else: inm[i] |= 1 << j
            k += 1
    assert k == len(bits)
    return inm


def check_tournament(adj):
    n = len(adj)
    for u in range(n):
        for v in range(n):
            assert u == v or adj[u][v] != adj[v][u]


def triangles(adj, verts=None):
    verts = range(len(adj)) if verts is None else verts
    return [(a, b, c) for a, b, c in itertools.combinations(sorted(verts), 3)
            if (adj[a][b] and adj[b][c] and adj[c][a]) or (adj[a][c] and adj[c][b] and adj[b][a])]


_ENV = None
def _env():
    global _ENV
    if _ENV is None:
        _ENV = gp.Env(empty=True); _ENV.setParam("OutputFlag", 0); _ENV.start()
    return _ENV


def solve_hs3(adj, verts=None, tl=3600, sb=None, logfile=None, weights=None, pool=0):
    """Min # arcs (within `verts`) meeting every cyclic triangle.  Returns a dict with ub (size of the
    verified incumbent), lb, optimal, runtime, nodes, ntri.  Threads=1 always.
    weights: optional {(u, v): w} on arcs u->v (default 1); ub is then the weight of the incumbent.
    pool: if > 0, also return 'pool', up to that many OPTIMAL hitting sets (sets of arcs (u, v)), each verified,
    and 'pool_complete' (True iff fewer than `pool` were found, i.e. the list is all of them)."""
    n = len(adj); verts = list(range(n)) if verts is None else sorted(verts)
    tris = triangles(adj, verts)
    m = gp.Model(env=_env())
    m.Params.Threads = 1; m.Params.TimeLimit = tl
    if logfile:
        m.Params.LogFile = logfile; m.Params.DisplayInterval = 60
    m.Params.Symmetry = 2
    x = {(u, v): m.addVar(vtype=GRB.BINARY) for u in verts for v in verts if adj[u][v]}
    e = lambda u, v: x[(u, v)] if adj[u][v] else x[(v, u)]
    for a, b, c in tris:
        m.addConstr(e(a, b) + e(b, c) + e(a, c) >= 1)
    if sb in ("vt", "paley"):
        assert verts == list(range(n))
        dp = [gp.quicksum(x[(v, u)] for u in range(n) if adj[v][u]) for v in range(n)]
        for v in range(1, n):
            m.addConstr(dp[0] >= dp[v])
        if sb == "paley":
            assert adj[0][1]
            M = (n - 1) // 2
            m.addConstr(x[(0, 1)] == 1)
            for u in range(2, n):
                if adj[0][u]:
                    m.addConstr(dp[1] >= dp[u] - M * (1 - x[(0, u)]))
    elif sb:
        raise ValueError(sb)
    wt = (lambda k: 1) if weights is None else (lambda k: weights[k])
    m.setObjective(gp.quicksum(wt(k) * v for k, v in x.items()), GRB.MINIMIZE)
    if pool:
        m.Params.PoolSearchMode = 2; m.Params.PoolSolutions = pool; m.Params.PoolGap = 0
    m.optimize()
    ub = None
    if m.SolCount:
        H = {k for k, v in x.items() if v.X > 0.5}; ub = sum(wt(k) for k in H)
        assert all({(a, b), (b, a), (b, c), (c, b), (a, c), (c, a)} & H for a, b, c in tris)
    res = dict(ub=ub, lb=m.ObjBound, optimal=m.Status == GRB.OPTIMAL, runtime=m.Runtime,
               nodes=m.NodeCount, ntri=len(tris))
    if pool:
        P = []
        for i in range(m.SolCount):
            m.Params.SolutionNumber = i
            H = frozenset(k for k, v in x.items() if v.Xn > 0.5)
            if sum(wt(k) for k in H) != ub: continue
            assert all({(a, b), (b, a), (b, c), (c, b), (a, c), (c, a)} & H for a, b, c in tris)
            P.append(H)
        res["pool"] = P; res["pool_complete"] = m.SolCount < pool
    return res


def solve_fas(adj, tl=3600, logfile=None):
    """Min feedback arc set by the linear-ordering ILP (paper 1, App. ilp-fas; same model as
    DRT27Scout/minfas_bound.py): b_uv = 1 iff u precedes v, transitivity on every triple, minimise backward
    arcs.  Gurobi, Threads=1.  Returns dict(ub, lb, optimal, runtime, order) with the order re-counted."""
    n = len(adj)
    m = gp.Model(env=_env()); m.Params.Threads = 1; m.Params.TimeLimit = tl
    if logfile:
        m.Params.LogFile = logfile; m.Params.DisplayInterval = 60
    b = {(u, v): m.addVar(vtype=GRB.BINARY) for u in range(n) for v in range(u + 1, n)}
    pre = lambda u, v: b[(u, v)] if u < v else 1 - b[(v, u)]
    for u, v, w in itertools.combinations(range(n), 3):
        m.addConstr(pre(u, v) + pre(v, w) - pre(u, w) <= 1)
        m.addConstr(pre(u, v) + pre(v, w) - pre(u, w) >= 0)
    m.setObjective(gp.quicksum(1 - pre(u, v) for u in range(n) for v in range(n) if adj[u][v]), GRB.MINIMIZE)
    m.optimize()
    val = lambda u, v: b[(u, v)].X if u < v else 1 - b[(v, u)].X
    order = sorted(range(n), key=lambda v: sum(val(u, v) > 0.5 for u in range(n) if u != v))
    pos = {v: i for i, v in enumerate(order)}
    back = sum(1 for u in range(n) for v in range(n) if adj[u][v] and pos[u] > pos[v])
    assert back == round(m.ObjVal)
    return dict(ub=back, lb=m.ObjBound, optimal=m.Status == GRB.OPTIMAL, runtime=m.Runtime, order=order)


def substitute(Q, blocks):
    """Lexicographic substitution Q[T_1, ..., T_k]: vertex i of Q replaced by tournament blocks[i]."""
    off = [0]
    for B in blocks:
        off.append(off[-1] + len(B))
    n = off[-1]; A = [[False] * n for _ in range(n)]
    for i, B in enumerate(blocks):
        for x in range(len(B)):
            for y in range(len(B)):
                A[off[i] + x][off[i] + y] = B[x][y]
        for j, C in enumerate(blocks):
            if i != j and Q[i][j]:
                for x in range(len(B)):
                    for y in range(len(C)):
                        A[off[i] + x][off[j] + y] = True
    return A
