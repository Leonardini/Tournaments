"""Level-0 check of the paper's appendix "Conjecture 2 at every order, and the rotational tournaments".

Free tools only: FAS by an exact Held-Karp subset DP (pure Python), HS3 (fewest arcs meeting every
directed 3-cycle) by OR-Tools CP-SAT with proven optimality.  Vertex labels are 1-based, as in the paper.

  A  T* (majority of the paper's printed rho, sigma, tau): regular, strong, FAS = 17 > 16 = HS3.
  B  W12 (T* with 7 -> 1 reversed, plus a vertex 12 beaten only by 7): the paper's profile induces it,
     it is strong, has 60 directed 3-cycles, the paper's order leaves 17 arcs backward, FAS = 17, HS3 = 16.
  C  C3[T*, TT_1, TT_1] (n = 13): 3-inducible by the block-profile construction of the substitution lemma,
     strong, FAS = 18, HS3 = 17 (gap 1).
  D  The substitution theorem, FAS and HS3 formulas, on random substitutions with small blocks.
  E  The rotational tournaments: the explicit 3-voter profile induces RT_n for every odd n <= 201, and
     HS3(RT_n) = FAS(RT_n) = (n^2 - 1)/8 for n <= 13 (direct computation, independent of the proof).
The proof's exponential-sum identity and slack are checked exactly, for every k, by rt_totient_weights.py.

Usage: python3 verify_appendix_c.py        (under 10 seconds)"""
import itertools, random, sys
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

def substitute(Q, blocks):
    off = [0]
    for B in blocks: off.append(off[-1] + len(B))
    n = off[-1]; A = [[False] * n for _ in range(n)]
    for i, B in enumerate(blocks):
        for j, C in enumerate(blocks):
            for x in range(len(B)):
                for y in range(len(C)):
                    A[off[i] + x][off[j] + y] = B[x][y] if i == j else Q[i][j]
    return A

def wfas(Q, w):                           # weighted FAS of a small Q by brute force over orders
    k = len(Q); best = 10 ** 9
    for p in itertools.permutations(range(k)):
        c = sum(w[p[j]][p[i]] for i in range(k) for j in range(i + 1, k) if Q[p[j]][p[i]])
        best = min(best, c)
    return best

def whs3(Q, w):                           # weighted HS3 of a small Q by brute force over arc subsets
    arcs = [(u, v) for u in range(len(Q)) for v in range(len(Q)) if Q[u][v]]
    tri = triangles(Q); arc = lambda a, b: (a, b) if Q[a][b] else (b, a)
    best = 10 ** 9
    for r in range(len(arcs) + 1):
        for S in itertools.combinations(arcs, r):
            Sset = set(S)
            if all(arc(a, b) in Sset or arc(b, c) in Sset or arc(c, a) in Sset for a, b, c in tri):
                best = min(best, sum(w[u][v] for u, v in S))
        if best < 10 ** 9 and r * min(min(row) for row in w) >= best: break
    return best

ok = True
def claim(label, cond):
    global ok
    print(f"  [{'PASS' if cond else 'FAIL'}] {label}"); ok &= bool(cond)

TT = lambda a: [[i < j for j in range(a)] for i in range(a)]
C3 = [[False, True, False], [False, False, True], [True, False, False]]

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

print("C. C3[T*, TT_1, TT_1], n = 13")
G = substitute(C3, [T, TT(1), TT(1)])
# block profile of the substitution lemma: voter v lists the blocks in the order of C3's v-th voter,
# and the vertices of each block in the order of that block's v-th voter
c3p = [(1, 2, 3), (2, 3, 1), (3, 1, 2)]
blk = {1: [rho, sig, tau], 2: [(1,), (1,), (1,)], 3: [(1,), (1,), (1,)]}; off = {1: 0, 2: 11, 3: 12}
prof = [tuple(off[b] + x for b in c3p[v] for x in blk[b][v]) for v in range(3)]
claim("C3 is the majority of its three cyclic orders", maj(c3p, 3) == C3)
claim("the block profile induces C3[T*, TT_1, TT_1]", maj(prof, 13) == G)
fG, hG = fas(G), hs3(G)
claim(f"strong; FAS = {fG} = 18 and HS3 = {hG} = 17", strong(G) and (fG, hG) == (18, 17))

print("D. The substitution theorem on random substitutions")
rnd = random.Random(20261117); trials = 0; good = True
for _ in range(40):
    k = rnd.choice([3, 4, 5]); Q = [[False] * k for _ in range(k)]
    for i, j in itertools.combinations(range(k), 2):
        if rnd.random() < 0.5: Q[i][j] = True
        else: Q[j][i] = True
    blocks = []
    for _ in range(k):
        a = rnd.choice([1, 2, 3, 3, 4]); B = [[False] * a for _ in range(a)]
        for i, j in itertools.combinations(range(a), 2):
            if rnd.random() < 0.5: B[i][j] = True
            else: B[j][i] = True
        blocks.append(B)
    if sum(map(len, blocks)) > 14: continue
    A = substitute(Q, blocks); w = [[len(blocks[i]) * len(blocks[j]) for j in range(k)] for i in range(k)]
    good &= fas(A) == sum(fas(B) for B in blocks) + wfas(Q, w)
    good &= hs3(A) == sum(hs3(B) if len(B) >= 3 else 0 for B in blocks) + whs3(Q, w)
    trials += 1
claim(f"FAS and HS3 formulas hold on all {trials} random substitutions (n <= 14)", good and trials >= 25)

print("E. Rotational tournaments RT_n")
def rt(n):
    k = (n + 1) // 2
    return [[(v - u) % n in range(1, k) for v in range(n)] for u in range(n)]
prof_ok = True
for n in range(3, 202, 2):
    k = (n + 1) // 2
    s1 = tuple(range(1, n + 1)); s3 = tuple(list(range(k + 1, n + 1)) + list(range(1, k + 1)))
    s2 = [None] * n                                   # x < k at position 2(k-1-x), x >= k at 2(n-1-x)+1 (0-based labels)
    for x in range(n): s2[2 * (k - 1 - x) if x < k else 2 * (n - 1 - x) + 1] = x + 1
    prof_ok &= maj([s1, tuple(s2), s3], n) == rt(n)
claim("the explicit 3-voter profile induces RT_n for every odd n = 3..201", prof_ok)
vals = {n: (fas(rt(n)), hs3(rt(n))) for n in range(3, 14, 2)}
claim("HS3(RT_n) = FAS(RT_n) = (n^2-1)/8 for n = 3..13: " + ", ".join(f"{n}:{h}" for n, (f, h) in vals.items()),
      all(f == h == (n * n - 1) // 8 for n, (f, h) in vals.items()))

print("ALL APPENDIX C CHECKS PASS" if ok else "SOME APPENDIX C CHECK FAILED")
sys.exit(0 if ok else 1)
