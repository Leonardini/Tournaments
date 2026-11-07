#!/usr/bin/env python3
"""FAS(T) versus HS3(T) on every regular tournament on 11 vertices, split by 3-inducibility.

Backs the sentence after Counterexample 4.2: FAS(T) = HS3(T) for every regular tournament
T on 11 vertices except T*, and among the 1,223 regular tournaments on 11 vertices, 48 of
them 3-inducible, T* is the only one with HS3(T) < FAS(T).

  FAS(T) = minimum number of arcs whose reversal makes T acyclic.
  HS3(T) = minimum number of arcs meeting every directed 3-cycle of T.
  HS3 <= FAS always: reversing a feedback arc set leaves no directed 3-cycle.

Each quantity is computed by two independent exact engines, which must agree:
  * FAS:  Held-Karp DP over the 2^11 vertex subsets (here, with an optimal order recovered
          and its backward arcs recounted) and hs3fas.c.
  * HS3:  the 0/1 integer program
              min sum_a x_a   s.t.  x_a + x_b + x_c >= 1 for every directed 3-cycle {a,b,c},
                                    x in {0,1}^(arcs of T)
          solved to proven optimality by OR-Tools CP-SAT (here, solution rechecked), and the
          branch and bound of hs3fas.c.
  * 3-inducibility: ../appendices/margin1_scan.c, and here a CP-SAT model of three linear
          orders in which every arc u -> v has u before v in at least two of them.

Every step that is guaranteed to succeed asserts, so the script either confirms the
claim or stops with an error that names what broke.

Usage (reg11_fas_hs3.sh runs it):
  reg11_fas_hs3.py <catalogue_bits.txt> <margin1_scan_emitn.out> <hs3fas.out> <tstar_index> [workers<=4]
Catalogue entries are counted from 1 in catalogue order.
"""
import sys
import time
from collections import Counter
from itertools import combinations
from multiprocessing import Pool

from ortools.sat.python import cp_model

# The counts the paper states (after Counterexample 4.2). They are recomputed below and
# the script fails if any differs.
PAPER_N_REGULAR = 1223        # regular tournaments on 11 vertices
PAPER_N_INDUCIBLE = 48        # of them 3-inducible
PAPER_VIOLATORS = 1           # with HS3 < FAS, and that one is T*
PAPER_TSTAR = (17, 16)        # (FAS, HS3) of T*, Counterexample 4.2


def log(msg):
    print(f"[{time.strftime('%H:%M:%S')}] {msg}", file=sys.stderr, flush=True)


def parse(bits, n):
    """McKay format: upper triangle row by row, bit 1 iff i -> j (i < j). Returns A[u][v]."""
    assert len(bits) == n * (n - 1) // 2, f"line of length {len(bits)} for n = {n}"
    A = [[0] * n for _ in range(n)]
    k = 0
    for i in range(n):
        for j in range(i + 1, n):
            assert bits[k] in "01", f"non-binary character {bits[k]!r}"
            if bits[k] == "1":
                A[i][j] = 1
            else:
                A[j][i] = 1
            k += 1
    return A


def arcs(A):
    n = len(A)
    return [(u, v) for u in range(n) for v in range(n) if A[u][v]]


def three_cycles(A):
    cyc = []
    for a, b, c in combinations(range(len(A)), 3):
        if A[a][b] and A[b][c] and A[c][a]:
            cyc.append(((a, b), (b, c), (c, a)))
        elif A[b][a] and A[c][b] and A[a][c]:
            cyc.append(((a, c), (c, b), (b, a)))
    return cyc


def fas_held_karp(A):
    """Maximum acyclic subgraph by DP over vertex subsets: g[S] is the largest number of
    forward arcs in an order of S, obtained by choosing the last vertex v of S (the arcs
    from S - v into v are then forward). FAS = (number of arcs) - g[all]."""
    n = len(A)
    inmask = [sum(1 << u for u in range(n) if A[u][v]) for v in range(n)]
    full = (1 << n) - 1
    g = [0] * (full + 1)
    last = [-1] * (full + 1)
    for S in range(1, full + 1):
        best, bv = -1, -1
        for v in range(n):
            if S >> v & 1:
                prev = S ^ (1 << v)
                val = g[prev] + bin(inmask[v] & prev).count("1")
                if val > best:
                    best, bv = val, v
        g[S], last[S] = best, bv
    order, S = [], full
    while S:
        order.append(last[S])
        S ^= 1 << last[S]
    order.reverse()
    pos = {v: i for i, v in enumerate(order)}
    fas = len(arcs(A)) - g[full]
    backward = sum(1 for (u, v) in arcs(A) if pos[u] > pos[v])
    assert backward == fas, "the recovered optimal order does not attain the DP value"
    return fas


def hs3_ilp(A):
    """HS3 by the 0/1 integer program in the module docstring, solved by CP-SAT.
    Feasible (take every arc) and bounded (>= 0) by construction, so anything other than
    a proven optimum is a hard failure."""
    E = arcs(A)
    cyc = three_cycles(A)
    m = cp_model.CpModel()
    x = {e: m.NewBoolVar(f"x{e}") for e in E}
    for c in cyc:
        m.Add(sum(x[e] for e in c) >= 1)
    m.Minimize(sum(x.values()))
    s = cp_model.CpSolver()
    s.parameters.num_workers = 1
    # Solve with the full LP relaxation and cuts, as an ILP solver would: without them a
    # single CP-SAT worker needs tens of seconds to prove optimality on some entries, with
    # them a few milliseconds.
    s.parameters.linearization_level = 2
    st = s.Solve(m)
    assert st == cp_model.OPTIMAL, f"HS3 program is feasible and bounded, but CP-SAT says {s.StatusName(st)}"
    H = {e for e in E if s.Value(x[e])}
    assert all(any(e in H for e in c) for c in cyc), "the optimal arc set misses a 3-cycle"
    assert len(H) == round(s.ObjectiveValue())
    return len(H)


def inducible3_cpsat(A):
    """Is T the majority tournament of three linear orders? Integer positions p[k][v],
    all different for each voter k; for each arc u -> v, Booleans b_k <=> p[k][u] < p[k][v]
    with b_1 + b_2 + b_3 >= 2. Permuting the voters maps solutions to solutions, so
    ordering them by the position of vertex 0 loses nothing."""
    n = len(A)
    m = cp_model.CpModel()
    p = [[m.NewIntVar(0, n - 1, f"p{k}_{v}") for v in range(n)] for k in range(3)]
    for k in range(3):
        m.AddAllDifferent(p[k])
    for (u, v) in arcs(A):
        bs = []
        for k in range(3):
            b = m.NewBoolVar("")
            m.Add(p[k][u] < p[k][v]).OnlyEnforceIf(b)
            m.Add(p[k][u] > p[k][v]).OnlyEnforceIf(b.Not())
            bs.append(b)
        m.Add(sum(bs) >= 2)
    m.Add(p[0][0] <= p[1][0])
    m.Add(p[1][0] <= p[2][0])
    s = cp_model.CpSolver()
    s.parameters.num_workers = 1
    st = s.Solve(m)
    assert st in (cp_model.OPTIMAL, cp_model.FEASIBLE, cp_model.INFEASIBLE), \
        f"3-inducibility model undecided: {s.StatusName(st)}"
    if st == cp_model.INFEASIBLE:
        return False
    for (u, v) in arcs(A):   # recheck the three orders found
        assert sum(s.Value(p[k][u]) < s.Value(p[k][v]) for k in range(3)) >= 2
    return True


def work(item):
    idx, bits, n = item
    A = parse(bits, n)
    fas = fas_held_karp(A)
    hs3 = hs3_ilp(A)
    assert hs3 <= fas, f"entry {idx}: HS3 = {hs3} > FAS = {fas}, which is impossible"
    return idx, inducible3_cpsat(A), fas, hs3


def read_margin1_scan(path):
    """margin1_scan.c with 'emitn' prints one 'N <bits>' line per tournament that is not
    3-inducible, and nothing else on stdout."""
    nonind = set()
    for ln in open(path):
        f = ln.split()
        assert len(f) == 2 and f[0] == "N", f"unexpected margin1_scan line {ln!r}"
        nonind.add(f[1])
    return nonind


def read_hs3fas(path, n):
    """hs3fas.c prints up to 20 'MISMATCH idx k: FAS=f HS3=h ...' lines, up to 20 'HARD'
    lines, and one summary line 'n=<n>: <total> tournaments; <m> with HS3<FAS; <h> HARD ...'."""
    mism, summary = {}, None
    for ln in open(path):
        if ln.startswith("MISMATCH"):
            f = ln.split()
            mism[int(f[2].rstrip(":"))] = (int(f[3].split("=")[1]), int(f[4].split("=")[1]))
        elif ln.startswith(f"n={n}:"):
            assert summary is None, "two summary lines from hs3fas"
            summary = ln.split()
        else:
            raise AssertionError(f"unexpected hs3fas line {ln!r}")
    assert summary is not None, "hs3fas printed no summary line"
    total, n_mism, n_hard = int(summary[1]), int(summary[3]), int(summary[6])
    assert n_hard == 0, f"hs3fas left {n_hard} tournaments unresolved"
    assert n_mism == len(mism) and n_mism <= 20, "hs3fas lists only its first 20 mismatches"
    return total, mism


def main():
    assert len(sys.argv) in (5, 6), __doc__
    bits_f, scan_f, hs3fas_f, tstar_idx = sys.argv[1], sys.argv[2], sys.argv[3], int(sys.argv[4])
    workers = int(sys.argv[5]) if len(sys.argv) > 5 else 4
    assert 1 <= workers <= 4, "at most 4 worker processes"

    cat = [ln.strip() for ln in open(bits_f) if ln.strip()]
    m = len(cat[0])
    n = round((1 + (1 + 8 * m) ** 0.5) / 2)
    assert n * (n - 1) // 2 == m and all(len(b) == m for b in cat)
    log(f"{len(cat)} tournaments on {n} vertices; T* is entry {tstar_idx}")

    t0 = time.time()
    res = {}
    with Pool(workers) as pool:
        items = [(i, b, n) for i, b in enumerate(cat, 1)]
        for k, r in enumerate(pool.imap_unordered(work, items, chunksize=8), 1):
            res[r[0]] = r[1:]
            if k % 200 == 0 or k == len(cat):
                log(f"{k}/{len(cat)} solved, {time.time() - t0:.0f}s")
    assert sorted(res) == list(range(1, len(cat) + 1))

    # second engine for 3-inducibility
    nonind = read_margin1_scan(scan_f)
    for i, b in enumerate(cat, 1):
        assert res[i][0] == (b not in nonind), f"entry {i}: CP-SAT and margin1_scan.c disagree on 3-inducibility"
    # second engine for FAS and HS3
    total, c_mism = read_hs3fas(hs3fas_f, n)
    assert total == len(cat), f"hs3fas read {total} tournaments, the catalogue has {len(cat)}"
    viol = {i: (fas, hs3) for i, (_, fas, hs3) in res.items() if fas != hs3}
    assert viol == c_mism, f"FAS != HS3 at {viol} here, at {c_mism} in hs3fas.c"

    inducible = [i for i in res if res[i][0]]
    for label, ids in (("3-inducible", inducible),
                       ("not 3-inducible", [i for i in res if not res[i][0]])):
        dist = Counter(res[i][1:] for i in ids)
        print(f"{label}: {len(ids)} tournaments; (FAS, HS3) -> count "
              f"{dict(sorted(dist.items()))}; HS3 < FAS at entries {sorted(i for i in ids if i in viol)}")

    # the paper's claim, as cross-checks of its stated counts
    assert len(cat) == PAPER_N_REGULAR, f"{len(cat)} regular tournaments, the paper says {PAPER_N_REGULAR}"
    assert len(inducible) == PAPER_N_INDUCIBLE, f"{len(inducible)} 3-inducible, the paper says {PAPER_N_INDUCIBLE}"
    assert len(viol) == PAPER_VIOLATORS, f"{len(viol)} with HS3 < FAS, the paper says {PAPER_VIOLATORS}"
    assert list(viol) == [tstar_idx], f"HS3 < FAS at entries {sorted(viol)}, not only at T* (entry {tstar_idx})"
    assert res[tstar_idx] == (True, *PAPER_TSTAR), f"T* has (3-inducible, FAS, HS3) = {res[tstar_idx]}"
    print(f"CONFIRMED: of the {len(cat)} regular tournaments on {n} vertices, {len(inducible)} are "
          f"3-inducible, and HS3 < FAS only for T* (entry {tstar_idx}, FAS = {PAPER_TSTAR[0]}, "
          f"HS3 = {PAPER_TSTAR[1]}), which is 3-inducible")


if __name__ == "__main__":
    main()
