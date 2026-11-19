#!/usr/bin/env python3
"""Paper 1, after Proposition cf-six-voters: the three circulants settled by computation in
Theorem thm:circulant-family (n = 21, 27, 45) are 5-inducible, although no six progressions with
steps in D back every arc 4:2.

For each n this script
  1. reads the five orders in circulant_five_voters.txt and checks that their majority tournament is
     the circulant of e (connection set S = {s : sum_i (s e_i mod n) = n});
  2. checks, with an integer program over the 3n progressions P(a, d_i), d_i = e_i^{-1}, that no choice
     of two progressions of each step makes every arc backward in exactly two of the six:
        y_{i,a} in {0, 1, 2},  sum_a y_{i,a} = 2 (each i),
        sum_{(i,a): arc backward in P(a, d_i)} y_{i,a} = 2  (every arc);
     infeasibility of this system is the claim.
Usage: python3 circulant_five_voters.py   (needs numpy and scipy; a few seconds)
"""
import sys
import numpy as np
from scipy.optimize import milp, LinearConstraint, Bounds

CASES = {21: (1, 4, 16), 27: (1, 7, 19), 45: (1, 13, 31)}


def connection_set(n, e):
    return {s for s in range(1, n) if sum(s * x % n for x in e) == n}


def read_profiles(path):
    prof, cur = {}, None
    for line in open(path):
        line = line.strip()
        if line.startswith("# n="):
            cur = int(line.split()[1][2:]); prof[cur] = []
        elif line:
            prof[cur].append([int(x) for x in line.split()])
    return prof


def main():
    prof = read_profiles("circulant_five_voters.txt")
    for n, e in CASES.items():
        S = connection_set(n, e)
        V = prof[n]
        if len(V) != 5 or any(sorted(v) != list(range(n)) for v in V):
            sys.exit(f"n={n}: the file does not hold five orders of Z_{n}")
        pos = [{x: i for i, x in enumerate(v)} for v in V]
        for a in range(n):
            for b in range(n):
                if (b - a) % n in S and sum(p[a] < p[b] for p in pos) < 3:
                    sys.exit(f"n={n}: arc {a}->{b} lacks a majority")
        cols = [(i, a) for i in range(3) for a in range(n)]
        rows = [[1 if c[0] == i else 0 for c in cols] for i in range(3)]
        rows += [[1 if ((v - a) * e[i] % n) < (s * e[i] % n) else 0 for (i, a) in cols]
                 for s in sorted(S) for v in range(n)]
        r = milp(np.zeros(len(cols)), constraints=LinearConstraint(np.array(rows), 2, 2),
                 integrality=np.ones(len(cols)), bounds=Bounds(0, 2))
        if r.status != 2:
            sys.exit(f"n={n}: the six-progression system is not reported infeasible (status {r.status})")
        print(f"n={n}: five voters induce the circulant of e={e}; no six progressions (two per step) back every arc 4:2")
    print("PASS")


if __name__ == "__main__":
    main()
