#!/usr/bin/env python3
"""verify_cA6_profiles.py -- checks the two profiles of cA6 in cA6_profiles.txt (standard library only).

cA6 is the self-converse 11-vertex tournament of Appendix C.3 of paper 1 whose predictability 2/3 needs
9 voters to attain.  The file gives a majority-of-5 inducing profile ('five') and a 9-voter profile of
8 types ('nine').  The script checks that:
  * both profiles list every vertex 1..11 exactly once per order, with 5 and 9 voters;
  * both have the same majority tournament (this is cA6), and it is self-converse;
  * in the 9-voter profile every arc is backed by at least 6 of the 9 voters (2/3).
Any failure stops it with an AssertionError naming the check.  Usage: verify_cA6_profiles.py [file]
"""
import sys
from itertools import combinations, permutations
from pathlib import Path

N = 11


def read(path):
    sections, cur = {}, None
    for line in Path(path).read_text().splitlines():
        line = line.strip()
        if not line or line.startswith("#"):
            continue
        if line in ("nine", "five"):
            cur = sections.setdefault(line, [])
            continue
        assert cur is not None, f"order before a section header: {line!r}"
        mult, _, order = line.rpartition(":") if ":" in line else ("1", None, line)
        cur.append((int(mult), [int(x) for x in order.split()]))
    return sections


def majority(profile):
    """arcs (u, v) with u before v in more voters than not, and the support of each arc"""
    voters = sum(m for m, _ in profile)
    arcs = {}
    for u, v in combinations(range(1, N + 1), 2):
        s = sum(m for m, o in profile if o.index(u) < o.index(v))
        assert 2 * s != voters, f"tie on {u},{v}"
        arcs[(u, v) if 2 * s > voters else (v, u)] = max(s, voters - s)
    return arcs


def self_converse(arcs):
    """some permutation maps T onto its converse; search with out-degree pruning"""
    out = {x: {v for (u, v) in arcs if u == x} for x in range(1, N + 1)}
    inn = {x: {u for (u, v) in arcs if v == x} for x in range(1, N + 1)}
    order = list(range(1, N + 1))

    def extend(f):
        if len(f) == N:
            return True
        x = order[len(f)]
        for y in range(1, N + 1):
            if y in f.values() or len(out[x]) != len(inn[y]):
                continue
            # converse: x -> z in T must map to f(z) -> f(x)
            if all((f[z] in out[y]) == (z in inn[x]) for z in f):
                f[x] = y
                if extend(f):
                    return True
                del f[x]
        return False

    return extend({})


def main():
    path = sys.argv[1] if len(sys.argv) > 1 else Path(__file__).resolve().parent / "cA6_profiles.txt"
    sec = read(path)
    for name, voters, types in (("five", 5, 5), ("nine", 9, 8)):
        prof = sec[name]
        assert sum(m for m, _ in prof) == voters and len(prof) == types, f"{name}: {voters} voters, {types} types"
        for _, o in prof:
            assert sorted(o) == list(range(1, N + 1)), f"{name}: {o} is not an order of 1..{N}"
    a5, a9 = majority(sec["five"]), majority(sec["nine"])
    assert set(a5) == set(a9), "the two profiles induce different tournaments"
    assert min(a9.values()) >= 6, "some arc has fewer than 6 of 9 voters behind it"
    assert self_converse(a5), "the tournament is not self-converse"
    print(f"cA6: the 5- and 9-voter profiles induce the same self-converse tournament on {N} vertices; "
          f"in the 9-voter profile every arc has at least {min(a9.values())} of 9 voters (2/3)")


if __name__ == "__main__":
    main()
