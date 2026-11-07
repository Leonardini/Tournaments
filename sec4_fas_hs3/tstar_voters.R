# The three voters whose majority tournament is T* (Counterexample 4.2), in the
# manuscript's labelling (vertices 1..11). Stated once here and `source`d by
# make_tstar_figs.R and reg11_catalogue.R, so the figure and the regular n = 11
# census always describe the same tournament.
tstar_voters = list(c(4, 5, 6, 11, 8, 9, 10, 2, 7, 1, 3),
                    c(10, 8, 9, 1, 2, 3, 7, 5, 6, 4, 11),
                    c(3, 7, 11, 1, 2, 6, 4, 5, 9, 10, 8))

# Majority tournament of a profile of linear orders on 1..n, as an adjacency
# matrix with A[i, j] = 1 iff a strict majority ranks i before j.
majority_matrix = function(voters) {
  n = length(voters[[1]])
  L = matrix(0, n, n)
  for (v in voters) {
    stopifnot(sort(v) == 1:n)
    for (a in 1:(n - 1)) for (b in (a + 1):n) L[v[a], v[b]] = L[v[a], v[b]] + 1
  }
  stopifnot(all(L + t(L) + diag(n) * length(voters) == length(voters)),  # every pair ranked by all
            all(L != t(L) | diag(n) == 1))                                # no ties (odd profile)
  (L > t(L)) * 1
}
