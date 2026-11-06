#!/usr/bin/env python3
"""Minimum covers of the 17,674 non-3-inducible 9-tournaments by obstacle classes, two readings:
  (M) containment: a class covers T if T contains the class's support as a subdigraph (arcs oriented as in T);
  (S) own obstacles: a class covers T if it is one of T's own minimal obstacles.
Among minimum covers, the one with the least total multiplicity is reported (a secondary objective).

Inputs: n9_minimal_obstacles.tsv (build_catalogue.py), the1054.txt, g8set_16620.txt, face1054_*.jsonl and
face16620_*.jsonl.  Containment is decided by networkx VF2 (subgraph monomorphism) and igraph LAD, which must
agree.  Covers are exact 0/1 programs solved by CP-SAT (count first, then total multiplicity at that count).
"""
import glob, json
from fractions import Fraction
import networkx as nx
from networkx.algorithms.isomorphism import DiGraphMatcher
import igraph as ig
from ortools.sat.python import cp_model
from build_catalogue import canon, mults


def read_tournaments(path):
    return [[[int(c) for c in r] for r in line.split()] for line in open(path) if line.split()]


def contains(A, arcs):
    T = nx.DiGraph(); n = len(A)
    T.add_nodes_from(range(n)); T.add_edges_from((u, v) for u in range(n) for v in range(n) if A[u][v])
    S = nx.DiGraph(); S.add_edges_from(arcs)
    vf2 = next(DiGraphMatcher(T, S).subgraph_monomorphisms_iter(), None) is not None
    Ti = ig.Graph(n=n, edges=list(T.edges()), directed=True)
    verts = sorted(S.nodes()); pos = {v: i for i, v in enumerate(verts)}
    Si = ig.Graph(n=len(verts), edges=[(pos[u], pos[v]) for u, v in arcs], directed=True)
    lad = Ti.subisomorphic_lad(Si, induced=False)
    assert vf2 == lad, "networkx VF2 and igraph LAD disagree on containment"
    return vf2


def lex_cover(sets, cost, label):
    """sets[i] = the columns covering row i.  Minimum number of columns, then least total cost."""
    ncol = len(cost)
    for i, s in enumerate(sets):
        assert s, f"{label}: row {i} has no covering column"
    res = []
    for stage in (0, 1):
        md = cp_model.CpModel(); x = [md.NewBoolVar("") for _ in range(ncol)]
        for s in sets:
            md.AddBoolOr([x[j] for j in s])
        if stage == 0:
            md.Minimize(sum(x))
        else:
            md.Add(sum(x) == res[0]); md.Minimize(sum(cost[j] * x[j] for j in range(ncol)))
        sv = cp_model.CpSolver(); sv.parameters.num_workers = 1
        assert sv.Solve(md) == cp_model.OPTIMAL, f"{label}: cover not proven optimal"
        res.append(int(sv.ObjectiveValue()))
        chosen = [j for j in range(ncol) if sv.Value(x[j])]
    assert len(chosen) == res[0] and sum(cost[j] for j in chosen) == res[1]
    return res[0], res[1], chosen


def main():
    cls = []
    for line in list(open("n9_minimal_obstacles.tsv"))[1:]:
        f = dict(zip(open("n9_minimal_obstacles.tsv").readline().rstrip("\n").split("\t"), line.rstrip("\n").split("\t")))
        arcs, m = [], []
        for a in f["arclist"].split(";"):
            uv, x = a.split(":"); u, v = uv.split(">"); arcs.append((int(u), int(v))); m.append(int(x))
        cls.append(dict(id=f["id"], alpha=Fraction(f["alpha"]), arcs=arcs, total=sum(m), key=canon(arcs, m)))
    ids = [c["id"] for c in cls]; cost = [c["total"] for c in cls]; g8 = ids.index("G8")
    T1054 = read_tournaments("the1054.txt"); T16 = read_tournaments("g8set_16620.txt")
    assert len(T1054) == 1054 and len(T16) == 16620

    # (M) containment.  Containing an obstacle's support bounds alpha*(T) by the obstacle's value, so a class
    # whose value is below every alpha* of the 1,054 cannot be contained in any of them: skip those checks.
    f1054 = [json.loads(l) for p in glob.glob("face1054_*.jsonl") for l in open(p)]
    amin = min(Fraction(json.loads(l)["alpha"]) for p in glob.glob("face1054_*.jsonl") for l in open(p))
    M = [[j for j, c in enumerate(cls) if c["alpha"] >= amin and contains(A, c["arcs"])] for A in T1054]
    assert all(g8 not in s for s in M), "a tournament of the 1,054 contains G8"
    k, c, ch = lex_cover(M, cost, "(M) 1,054")
    witness = None
    for t, A in enumerate(T16):
        assert contains(A, cls[g8]["arcs"]), f"tournament {t} of the 16,620 does not contain G8"
        if witness is None and not any(contains(A, cl["arcs"]) for j, cl in enumerate(cls) if j != g8):
            witness = t
    assert witness is not None, "G8 not forced: solve the full 17,674-row cover instead"
    print(f"(M) containment: the 1,054 need {k} classes (total multiplicity {c}): {' '.join(ids[j] for j in ch)}")
    print(f"    all 16,620 contain G8, and tournament {witness} of g8set_16620.txt contains none of the other classes,")
    print(f"    so G8 is in every cover and covers all 16,620.  Minimum cover of the 17,674: {k + 1} classes")
    print(f"    (G8 + the above; total multiplicity {c + cost[g8]}).")

    # (S) own obstacles
    key2j = {cl["key"]: j for j, cl in enumerate(cls)}
    def own(recs):
        return [sorted({key2j[canon([tuple(a) for a in s["arcs"]], mults(s["y"]))] for s in r["supports"]})
                for r in sorted(recs, key=lambda r: r["idx"])]
    r16 = [json.loads(l) for p in glob.glob("face16620_*.jsonl") for l in open(p)]
    S1054 = own(f1054); S16 = own(r16)
    k1, c1, ch1 = lex_cover(S1054, cost, "(S) 1,054")
    below = [s for s, r in zip(S16, sorted(r16, key=lambda r: r["idx"])) if Fraction(r["alpha"]) < Fraction(13, 20)]
    k2, c2, ch2 = lex_cover(below, cost, "(S) 16,620 below 13/20")
    print(f"(S) own obstacles: the 1,054 need {k1} classes (total multiplicity {c1}): {' '.join(ids[j] for j in ch1)}")
    print(f"    the {len(below)} of the 16,620 with alpha* < 13/20 need {k2} (total {c2}): {' '.join(ids[j] for j in ch2)};")
    print(f"    the others have only G8.  Minimum cover of the 17,674: {k1 + k2 + 1} classes.")


if __name__ == "__main__":
    main()
