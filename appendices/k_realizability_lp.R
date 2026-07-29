#!/usr/bin/env Rscript
#
# Realizability LP with primal and dual solution extraction

MAX_PERMS = 8L
print(paste("Pre-generating permutations"))
for (ind in 1:MAX_PERMS) {
  print(ind)
  assign(paste0("PERMS", ind), pracma::perms(1:ind))
}

library(Rcplex)
library(pracma)
library(combinat)
library(Matrix)

source("Utilities.R")
source("HittingSet.R")
source("minimum_set_cover.R")

find_all_minimal_fas = function(tournament) {
  n = nrow(tournament)
  G = graph_from_adjacency_matrix(tournament, mode = "directed")
  tournamentEdges = as_edgelist(G)
  fasList = list()
  pos = 1
  numEdges = choose(n, 2)
  allCombinations = hcube(rep(2L, nrow(tournamentEdges))) - 1L
  allSizes = rowSums(allCombinations)
  allCombinations = allCombinations[order(allSizes), , drop = FALSE]
  totalCombinations = 2^nrow(tournamentEdges)
  stopifnot(totalCombinations == nrow(allCombinations))
  explored = rep(FALSE, totalCombinations)
  explored[1] = TRUE # The empty set is not a FAS (except for the trivial case of a transitive tournament)
  for (comb in 1:totalCombinations) {
    if (comb %% 1000 == 0) { print(comb) }
    if (explored[comb]) {
      next
    }
    curUsed = which(allCombinations[comb, ] == 1)
    curSize = length(curUsed)
    modifiedG = reverse_edges(G, E(G)[curUsed])
    if (is_dag(modifiedG)) {
      fasList[[pos]] = tournamentEdges[curUsed, , drop = FALSE]
      supersets = which(rowSums(allCombinations[, curUsed, drop = FALSE]) == curSize)
      explored[supersets] = TRUE
      pos = pos + 1
    }
  }
  fasList
}

test_all_counterexamples = function(allGraphs, primitiveOnly = TRUE, strong = TRUE, maxVoters = 5L) {
  if (primitiveOnly) {
    goodGraphs = sapply(allGraphs, function(tournament) {
      G = graph_from_adjacency_matrix(tournament, mode = "directed")
      n_comps = count_components(G, mode = "strong")
      n_comps == 1
    })
    allGraphs = allGraphs[goodGraphs]
  }
  n_graphs = length(allGraphs)
  n = nrow(allGraphs[[1]])
  results = vector("list", n_graphs)
  permutations = get(paste0("PERMS", n))
  for (ind in 1:n_graphs) {
    cat(sprintf("Processing graph %d of %d\n", ind, n_graphs))
    tournament = allGraphs[[ind]]
    allTriangles = getDirectedTriangles(tournament)
    usedPairs = rbind(allTriangles[, c(1, 2)], allTriangles[, c(2, 3)], allTriangles[, c(1, 3)])
    usedPairs = unique(cbind(pmin(usedPairs[,1], usedPairs[,2]), pmax(usedPairs[,1], usedPairs[,2])))
    if (nrow(usedPairs) == 0) {
      cat("Skipping transitive tournament\n")
      next
    }
    if (nrow(usedPairs) == choose(n, 2)) {
      cat("Skipping tournament with all edges in a triangle\n")
      next
    }
    allPairs = combn2(1:n)
    goodPairs = which(!duplicated(rbind(allPairs, usedPairs), fromLast = TRUE)[1:nrow(allPairs)])
    finalPairs = matrix(0, nrow = length(goodPairs), ncol = 2)
    rind = 1
    for (pos in goodPairs) {
      curPair = allPairs[pos, ]
      if (tournament[curPair[1], curPair[2]] == 1) {
        finalPairs[rind, ] = curPair
      } else {
        finalPairs[rind, ] = rev(curPair)
      }
      rind = rind + 1
    }
    goodInds = (finalPairs[, 1] - 1) * n + finalPairs[, 2]
    FAS = find_all_minimal_fas(tournament)
    goodFASInds = c()
    pos = 1L
    for (index in 1:length(FAS)) {
      fas = FAS[[index]]
      fasInds = (fas[, 1] - 1) * n + fas[, 2]
      if (any(fasInds %in% goodInds)) {
        goodFASInds[pos] = index
        pos = pos + 1L
      }
    }
    curResults = vector("list", length(goodFASInds))
    for (pos in 1:length(goodFASInds)) {
      index = goodFASInds[pos]
      curMinFAS = c(FAS[index], FAS[-index])
      lp_data = build_counterexample_lp(permutations, tournament, curMinFAS, maxVoters = maxVoters, strong = strong, minimum = FALSE)
      curResults[[pos]] <- Rcplex(
        cvec = lp_data$cvec,
        Amat = lp_data$Amat,
        bvec = lp_data$bvec,
        sense = lp_data$sense,
        lb = lp_data$lb,
        ub = lp_data$ub,
        vtype = "I",
        objsense = "min",
        control = list(trace = 0)
      )
    }
    results[[ind]] = curResults
  }
  results
}

process_result <- function(result, n) {
  status <- result$status
  objective <- result$obj
  primal <- result$xopt
  perms <- get(paste0("PERMS", n))
  n_perms <- nrow(perms)
  perm_primals <- primal[1:n_perms]
  n_nonzero_primal <- sum(perm_primals > 0)
  solution <- perms[which(perm_primals > 0), , drop = FALSE]
  weights <- perm_primals[which(perm_primals > 0)]
  solution <- t(apply(solution, 1, invertPerm))
  splitSolution <- split(solution, row(solution))
  splitSolution <- rep(splitSolution, weights)
  names(splitSolution) <- paste0("pi", 1:length(splitSolution))
  checkTournament <- solution_to_tournament(splitSolution, simplify = FALSE)
  totalWeight <- sum(weights)
  checkTournament <- pmax(2 * checkTournament - totalWeight, 0)
  solution <- cbind(solution, weight = weights)
  list(
    status = status,
    objective = objective,
    solution = solution,
    checkTournament = checkTournament
  )
}

build_counterexample_lp <- function(permutations, tournament, minFAS, maxVoters = 5L, strong = FALSE, minimum = FALSE) {
  # Inputs: a list of permutations to be used as possible votes, a tournament (adjacency matrix),
  # and a list of minimal FAS's (each FAS is a list of edges of the tournament)
  # The target FAS is assumed to be the first one; its total weight must be minimal among all of them
  # Variables: X[pi] = coefficient of the permutation pi in the counterexample; M[e] = the margin on edge e
  # If minimum = TRUE, also add Y[pi] which is 1 if pi is active in the counterexample, and 0 otherwise
  # Constraints: sum over pi supporting edge e of X[pi] - Sum over pi supporting edge rev(e) of X[pi] = M[e], e in T
  # M[e] >= 1 for each edge e in the target tournament
  # Sum over all X[pi] <= maxVoters
  # For each other minimal FAS F: Sum over e in F of M[e] >= Sum over e in targetFAS of M[e] + d (if strong = TRUE, d = 1; else d = 0)
  # If minimum = TRUE: X[pi] <= maxVoters * Y[pi] for each pi
  # Objective: none (feasibility problem) or minimize sum over pi of the Y[pi] (if minimum = TRUE)
  n_perms <- nrow(permutations)
  n <- nrow(tournament)
  n_edges <- choose(n, 2)
  stopifnot(near(sum(tournament), n_edges))  # Must be a tournament
  cat(sprintf("Building counterexample LP for %d permutations of order %d\n", n_perms, n))
  L <- length(minFAS)
  targetFAS <- minFAS[[1]]
  cat(sprintf("Target FAS has %d edges; there are %d other minimal FAS's\n", nrow(targetFAS), L - 1))
  # The variables are ordered as: X[1], X[2], ..., X[n_perms], M[e1], M[e2], ..., M[e_choose(n,2)]
  cvec <- rep(0, n_perms + n_edges)  # No objective, just feasibility
  bvec <- c(
    rep(0, n_edges),      # For sum over pi supporting edge e of X[pi] - sum over pi supporting edge rev(e) of X[pi] = M[e]
    rep(1, n_edges),      # For M[e] >= 1 for every edge e in the tournament
    maxVoters,            # For sum over all X[pi] <= maxVoters
    rep(strong, L - 1)    # For other FAS constraints
  )
  sense <- c(
    rep("E", n_edges),    # For sum over pi supporting edge e of X[pi] - sum over pi supporting edge rev(e) of X[pi] = M[e]
    rep("G", n_edges),    # For M[e] >= 1 for every edge e in the tournament
    rep("L", 1),          # For sum over all X[pi] <= maxVoters
    rep("G", L - 1)       # For other FAS constraints
  )
  # Bounds
  lb <- rep(0, n_perms + n_edges)
  ub <- rep(as.double(maxVoters), n_perms + n_edges)
  # Build constraint matrix
  Amat <- matrix(0, nrow = n_edges * 2 + L, ncol = n_perms + n_edges)
  # 1. Sum over pi supporting edge e of X[pi] - Sum over pi supporting edge rev(e) of X[pi] = M[e] for each edge e in T
  # 2. M[e] >= 1 for each edge e in the tournament
  edgeList = which(tournament == 1, arr.ind = TRUE)
  edgeIndices = (edgeList[, 1] - 1) * n + edgeList[, 2] 
  for (pos in 1:n_edges) {
    i = edgeList[pos, 1]
    j = edgeList[pos, 2]
    # Find which permutations support this edge
    Amat[pos, 1:n_perms] <- 2L * as.integer(permutations[, i] < permutations[, j]) - 1L
    Amat[pos, n_perms + pos] <- -1
    # M[e] >= 1
    Amat[n_edges + pos, n_perms + pos] <- 1
  }
  # 4. Sum over all X[pi] <= maxVoters
  Amat[n_edges * 2 + 1, 1:n_perms] <- 1
  # 5. For each other minimal FAS F: Sum over e in F of M[e] <= Sum over e in targetFAS of M[e]
  targetFASInds = (targetFAS[,1] - 1) * n + targetFAS[,2]
  targetInds = match(targetFASInds, edgeIndices)
  Amat[n_edges * 2 + (2:L), n_perms + targetInds] <- -1
  for (l in 2:L) {
    curFAS <- minFAS[[l]]
    curFASInds = (curFAS[,1] - 1) * n + curFAS[,2]
    curInds = match(curFASInds, edgeIndices)
    Amat[n_edges * 2 + l, n_perms + curInds] <- Amat[n_edges * 2 + l, n_perms + curInds] + 1
    # NOTE: any common edges between targetFAS and curFAS should cancel out in this way!
  }
  if (minimum) {
    # Add Y[pi] variables
    cvec <- c(cvec, rep(1, n_perms))  # Minimize sum of Y[pi]
    bvec <- c(bvec, rep(0, n_perms))
    sense <- c(sense, rep("L", n_perms))
    lb <- c(lb, rep(0, n_perms))
    ub <- c(ub, rep(1, n_perms))
    # Expand constraint matrix
    Amat_new <- matrix(0, nrow = nrow(Amat) + n_perms, ncol = ncol(Amat) + n_perms)
    Amat_new[1:nrow(Amat), 1:ncol(Amat)] <- Amat
    Amat <- Amat_new
    # Add constraints: X[pi] <= maxVoters * Y[pi] for each pi
    for (pi_ind in 1:n_perms) {
      Amat[nrow(Amat) - n_perms + pi_ind, pi_ind] <- 1
      Amat[nrow(Amat) - n_perms + pi_ind, ncol(Amat) - n_perms + pi_ind] <- -maxVoters
    }
  }
  cat(sprintf("LP has %d variables, %d constraints\n", ncol(Amat), nrow(Amat)))
  return(list(
    cvec = cvec,
    Amat = Amat,
    bvec = bvec,
    sense = sense,
    lb = lb,
    ub = ub,
    n_edges = n_edges,
    n_perms = n_perms
  ))
}

build_obstacle_lp <- function(permutations, targetFraction, breakSym = FALSE, feasibleOnly = FALSE) {
  # Variables: X[i,j] = 1 if and only if the edge i -> j is part of the obstacle; 
  # totalEdges = number of edges in the obstacle (derived variable)
  # Constraints: X[i, j] + X[j, i] <= 1 for all i < j; X[i, i] = 0 for all i
  # sum(i < j) X[pi[i], pi[j]] - targetFraction * totalEdges <= 0 for each permutation pi
  # sum(i != j) X[i, j] - totalEdges = 0
  # Optional symmetry-breaking: sum(j) X[i,j] <= sum(j) X[i+1,j] for every i from 1 to n - 1
  # Objective: maximize totalEdges subject to all the constraints
  # If feasibleOnly = TRUE, only build the LP to check feasibility (no objective)
  n_perms <- nrow(permutations)
  n <- ncol(permutations)
  cat(sprintf("Building obstacle LP for %d permutations of order %d\n", n_perms, n))
  n_edges <- choose(n, 2)
  n_vars <- n * n + 1  # X[i,j] for all (i,j), and totalEdges
  cvec <- c(rep(0, n * n), ifelse(feasibleOnly, 0, -1))  # Maximize totalEdges or test feasibility
  bvec <- c(rep(1, n_edges), rep(0, n + n_perms + ifelse(breakSym, n, 1)))
  lb <- c(rep(0, n * n), 1)
  ub <- c(rep(1, n * n), n_edges)
  sense <- c(rep("L", n_edges), rep("E", n), rep("L", n_perms), "E")
  if (breakSym) {
    sense <- c(sense, rep("L", n - 1))
  }
  # Build constraint matrix
  Amat <- matrix(0, nrow = n_edges + n + n_perms + ifelse(breakSym, n, 1), ncol = n_vars)
  # 1. X[i,j] + X[j,i] <= 1 for all i < j
  pos <- 1
  for (i in 1:n) {
    for (j in 1:n) {
      if (i < j) {
        Amat[pos, (i - 1) * n + j] <- 1
        Amat[pos, (j - 1) * n + i] <- 1
        pos <- pos + 1
      }
    }
  }
  # 2. X[i,i] = 0 for all i
  for (i in 1:n) {
    Amat[pos, (i - 1) * n + i] <- 1
    pos <- pos + 1
  }
  pos <- pos - 1
  # 3. sum(i < j) X[pi[i], pi[j]] - targetFraction * totalEdges <= 0 for each permutation pi
  for (i in 1:n) {
    for (j in 1:n) {
      # Find which permutations support the edge i → j
      # Permutation p^{-1} supports i → j if p(i) < p(j)
      Amat[pos + (1:n_perms), (i - 1) * n + j] = as.integer(permutations[, i] < permutations[, j])
    }
  }
  Amat[pos + (1:n_perms), n * n + 1] <- -targetFraction
  # 4. sum(i != j) X[i,j] - totalEdges = 0
  for (i in 1:n) {
    for (j in 1:n) {
      if (i != j) {
        Amat[n_edges + n + n_perms + 1, (i - 1) * n + j] <- 1
      }
    }
  }
  Amat[n_edges + n + n_perms + 1, n * n + 1] <- -1
  if (breakSym) {
    # 5. Symmetry-breaking constraints: sum(j) X[i,j] <= sum(j) X[i+1,j] for every i from 1 to n - 1
    for (i in 1:(n - 1)) {
      for (j in 1:n) {
        Amat[n_edges + n + n_perms + 1 + i, (i - 1) * n + j] <- 1
        Amat[n_edges + n + n_perms + 1 + i, i * n + j] <- -1
      }
    }
  }
  cat(sprintf("LP has %d variables, %d constraints\n", n_vars, nrow(Amat)))
  return(list(
    cvec = cvec,
    Amat = Amat,
    bvec = bvec,
    sense = sense,
    lb = lb,
    ub = ub,
    n_edges = n_edges,
    n_perms = n_perms
  ))
}

#' Build realizability LP for a tournament
#' @param tournament Adjacency matrix (n×n)
#' @param permutations Matrix of permutations (factorial(n) × n)
#' @return List with cvec, Amat, bvec, sense, lb, ub for LP
build_realizability_lp <- function(tournament, permutations, equal = FALSE) {
  
  n <- nrow(tournament)
  n_perms <- nrow(permutations)
  n_edges <- sum(tournament)
  stopifnot(n_edges == choose(n, 2))
  
  cat(sprintf("Building realizability LP for tournament of order %d\n", n))
  cat(sprintf("Using %d permutations\n", n_perms))
  
  # Variables: x[p] = weight on permutation p (one per permutation); alpha (the value to maximize)
  # Objective: maximize alpha
  
  cvec <- c(rep(0, n_perms), -1)  # Minimize -alpha
  
  # Constraints:
  # 1. For each edge (i,j) in tournament: sum over p where p supports (i,j) of x[p] - alpha >= 0 (= 0 if equal = TRUE)
  # 2. Sum of all x[p] = 1
  # 3. x[p] >= 0
  
  bvec <- c(rep(0, n_edges), 1)
  sense <- c(rep(ifelse(equal, "E", "G"), n_edges), "E")
  # Bounds
  lb <- rep(0, n_perms + 1)
  ub <- rep(1, n_perms + 1)
  
  # Build constraint matrix
  # First: edge coverage constraints
  Amat <- matrix(0L, nrow = n_edges + 1, ncol = n_perms + 1)
  
  pos <- 1
  for (i in 1:(n-1)) {
    print(paste("Processing row", i))
    for (j in (i+1):n) {
      if (tournament[i, j] == 1) {
        # Edge i → j exists
        # Find which permutations support this edge
        # Permutation p^{-1} supports i → j if p(i) < p(j)
        Amat[pos, 1:n_perms] = as.integer(permutations[, i] < permutations[, j])
      } else {
        Amat[pos, 1:n_perms] = as.integer(permutations[, j] < permutations[, i])
      } 
      pos = pos + 1
    }
  }
  Amat[, n_perms + 1] <- c(rep(-1L, n_edges), 0L)  # Coefficient for -alpha
  
  # Second: sum constraint
  Amat[n_edges + 1, ] <- c(rep(1L, n_perms), 0L)
  mode(Amat) = "double"
  
  cat(sprintf("LP has %d variables, %d constraints (%d edge + 1 sum)\n", n_perms + 1, nrow(Amat), n_edges))
  
  return(list(
    cvec = cvec,
    Amat = Amat,
    bvec = bvec,
    sense = sense,
    lb = lb,
    ub = ub,
    n_edges = n_edges,
    n_perms = n_perms
  ))
}

library(slam)

build_realizability_lp_sparse <- function(tournament, permutations, equal = FALSE) {
  
  n <- nrow(tournament)
  P <- nrow(permutations)
  stopifnot(sum(tournament) == choose(n, 2))
  
  # ---- Build directed edge list ----
  edges <- which(tournament == 1, arr.ind = TRUE)
  # Order by unordered pair {i,j}
  edges <- edges[order(pmin(edges[,1], edges[,2]), pmax(edges[,1], edges[,2])), ]
  E <- choose(n, 2)
  edge_u <- edges[,1]
  edge_v <- edges[,2]
  
  n_vars <- P + 1
  alpha_col <- n_vars
  n_cons <- E + 1
  
  # ---- Preallocate ----
  nnz_edges <- E * (P / 2 + 1)
  nnz_total <- nnz_edges + P
  
  I <- integer(nnz_total)
  J <- integer(nnz_total)
  V <- numeric(nnz_total)
  
  ptr <- 1
  
  # ---- Edge constraints ----
  for (e in seq_len(E)) {
    print(e)
    u <- edge_u[e]
    v <- edge_v[e]
    
    supports <- which(permutations[, u] < permutations[, v])
    k <- length(supports)
    stopifnot(k == P / 2)
    
    idx <- ptr:(ptr + k - 1)
    I[idx] <- e
    J[idx] <- supports
    V[idx] <- 1
    ptr <- ptr + k
    
    I[ptr] <- e
    J[ptr] <- alpha_col
    V[ptr] <- -1
    ptr <- ptr + 1
  }
  
  # ---- Sum constraint ----
  idx <- ptr:(ptr + P - 1)
  I[idx] <- E + 1
  J[idx] <- seq_len(P)
  V[idx] <- 1
  ptr <- ptr + P
  
  stopifnot(ptr == nnz_total + 1)
  
  # ---- Sparse matrix ----
  Amat <- simple_triplet_matrix(
    i = I,
    j = J,
    v = V,
    nrow = n_cons,
    ncol = n_vars
  )
  
  # ---- Objective ----
  cvec <- c(rep(0, P), -1)
  
  # ---- RHS / senses ----
  bvec <- c(rep(0, E), 1)
  sense <- c(rep(ifelse(equal, "E", "G"), E), "E")
  
  # ---- Bounds ----
  lb <- rep(0, n_vars)
  ub <- rep(1, n_vars)
  
  cat(sprintf(
    "Sparse LP built correctly: %d vars, %d cons, %d nonzeros\n",
    n_vars, n_cons, nnz_total
  ))
  
  return(list(
    cvec = cvec,
    Amat = Amat,
    bvec = bvec,
    sense = sense,
    lb = lb,
    ub = ub
  ))
}

#' Solve realizability LP and extract primal and dual solutions
#' @param tournament Adjacency matrix (n×n)
#' @param time_limit Time limit in seconds
#' @return List with status, objective, primal solution, dual solution, summary
solve_realizability_lp <- function(tournament, time_limit = 300, equal = FALSE) {
  
  n <- nrow(tournament)
  
  if (n <= MAX_PERMS) {
    permutations <- get(paste0("PERMS", n))
  } else {
    permutations <- pracma::perms(1:n)
  }
  
  n_perms <- nrow(permutations)
  
  # Build LP
  lp_data <- build_realizability_lp(tournament, permutations, equal = equal)
  
  # Solve with Rcplex
  result <- Rcplex(
    cvec = lp_data$cvec,
    Amat = lp_data$Amat,
    bvec = lp_data$bvec,
    sense = lp_data$sense,
    lb = lp_data$lb,
    ub = lp_data$ub,
    objsense = "min",
    control = list(
      trace = 1,
      tilim = time_limit
    )
  )
  
  # Extract solution
  status <- result$status
  objective <- -(result$obj)   # Negate back to maximization
  primal <- result$xopt
  dual <- result$extra$lambda  # Dual variables
  
  perm_primals <- primal[1:n_perms]  # Primal values for permutation weights
  edge_duals <- dual[1:choose(n, 2)]  # Duals for edge constraints
  
  # Build edge mapping for dual values
  edge_dual_map <- matrix(0, n, n)
  edge_idx <- 1
  for (i in 1:(n-1)) {
    for (j in (i+1):n) {
      if (tournament[i, j] == 1) {
        edge_dual_map[i, j] <- edge_duals[edge_idx]
      } else {
        edge_dual_map[j, i] <- edge_duals[edge_idx]
      }
      edge_idx <- edge_idx + 1
    }
  }
  edge_dual_map <- zapsmall(edge_dual_map)
  
  return(list(status = status, objective = objective, primal = perm_primals, edge_dual_map = edge_dual_map))
}

# Example usage:
#
# # Test on a small tournament
# tournament <- matrix(c(
#   0, 1, 1, 0,
#   0, 0, 1, 0,
#   0, 0, 0, 1,
#   1, 1, 0, 0
# ), nrow = 4, byrow = TRUE)
#
# result <- solve_realizability_lp(tournament)
#
# # Access results
# cat(sprintf("\nIs optimal? %s\n", result$is_optimal))
# cat(sprintf("Objective: %.6f\n", result$objective))
# cat(sprintf("Number of non-zero primal variables: %d\n", result$n_nonzero_primal))
# cat(sprintf("Number of positive dual variables: %d\n", result$n_positive_dual))
#
# # For larger tournament (e.g., n=7)
# result_7 <- solve_realizability_lp(counterexample_7vertex, verbose = TRUE)

groupByIsomorphism = function(sampledGraphs) {
  if (!all(sapply(sampledGraphs, is_simple))) {
    print("Simplifying and colorizing graphs")
    sampledGraphs = lapply(sampledGraphs, simplify_and_colorize)
  }
  classified = rep(0, length(sampledGraphs))
  edgeCounts = sapply(sampledGraphs, ecount)
  index = 1
  while (any(classified == 0)) {
    print(paste("There are", sum(classified == 0), "graphs to classify"))
    curMin = min(which(classified == 0))
    baseGraph = sampledGraphs[[curMin]]
    baseEdges = edgeCounts[curMin]
    classified[curMin] = index
    for (j in which(classified == 0)) {
      if (edgeCounts[j] != baseEdges) { next }
      if (isomorphic(baseGraph, sampledGraphs[[j]])) {
        classified[j] = index
      }
    }
    index = index + 1
  }
  classified
}

findIsomorphicCopies = function(targetGraphs, allGraphs, specialIndices = NULL) {
  numTargets = length(targetGraphs)
  numGraphs = length(allGraphs)
  Mat = matrix(FALSE, nrow = numTargets, ncol = numGraphs)
  for (ind in 1:numTargets) {
    print(ind)
    for (jnd in 1:length(allGraphs)) {
      if (is.null(specialIndices) || jnd %in% specialIndices) {
        Mat[ind, jnd] = subgraph_isomorphic(targetGraphs[[ind]], allGraphs[[jnd]])
      } else {
        stopifnot(!subgraph_isomorphic(targetGraphs[[ind]], allGraphs[[jnd]]))
      }
    }
  }
  if (!is.null(specialIndices)) {
    Mat = Mat[, specialIndices]
  }
  Mat
}

checkSubgraph = function(patternGraph, targetGraph) {
  if (is_simple(patternGraph)) {
    return(subgraph_isomorphic(patternGraph, simplify(targetGraph)))
  }
  if (is_simple(targetGraph)) {
    return(FALSE)
  }
  targetWeights = as_adjacency_matrix(targetGraph, sparse = FALSE)
  patternWeights = as_adjacency_matrix(patternGraph, sparse = FALSE)
  subIsom = subgraph_isomorphisms(simplify(patternGraph), simplify(targetGraph))
  L = length(subIsom)
  if (L == 0) {
    return(FALSE)
  }
  for (ind in 1:L) {
    mapping = subIsom[[ind]]
    edgeWeights = targetWeights[mapping, mapping]
    if (all(edgeWeights >= patternWeights)) {
      return(TRUE)
    }
  }
  return(FALSE)
}

findNonDominated = function(listOfMultiGraphs) {
  n = length(listOfMultiGraphs)
  ecounts = sapply(listOfMultiGraphs, ecount)
  simpleEcounts = sapply(listOfMultiGraphs, function(g) { ecount(simplify(g)) })
  Tab = tibble(index = 1:n, ecount = ecounts, simpleEcount = simpleEcounts)
  compTab = Tab %>% 
    inner_join(Tab, by = join_by(ecount < ecount), suffix = c("_G", "_H")) %>%
    filter(simpleEcount_G <= simpleEcount_H)
  dominated = rep(FALSE, n)
  for (ind in 1:nrow(compTab)) {
    i = compTab$index_G[ind]
    j = compTab$index_H[ind]
    if (dominated[j]) { next }
    if (checkSubgraph(listOfMultiGraphs[[i]], listOfMultiGraphs[[j]])) {
      dominated[j] = TRUE
    }
  }
  output = which(!dominated)
  output
}

main = function() {
  load("Counterexamples/Non3RealizableTournaments8.RData")
  
  Res = vector("list", length(badTournaments))
  for (ind in 1:length(badTournaments)) { 
    Res[[ind]] = solve_realizability_lp(badTournaments[[ind]])$edge_dual_map
    print(ind) 
  }
  allDualGraphs = lapply(Res, function(x) { 
    y = which(x > 0, arr.ind = TRUE)
    G = make_graph(edges = t(y), n = 8, directed = TRUE)
  })
  U = groupByIsomorphism(allDualGraphs)
  
  G = allDualGraphs[[1]]
  H = igraph::permute(G, canonical_permutation(G)$labeling)
  pdf("ObstructionC8.pdf"); plot(H); dev.off()
  
  load("Counterexamples/Non3Realisable9.RData")
  badGraphs = lapply(badTournaments, graph_from_adjacency_matrix)
  testResults = sapply(badGraphs, function(x) {subgraph_isomorphic(H, x)})
  
  NUM_SAMPLES = sum(!testResults)
  sampled = which(!testResults)
  sampledGraphs = vector("list", NUM_SAMPLES)
  ResNonMargin1 = vector("list", NUM_SAMPLES)
  for (pos in 1:NUM_SAMPLES) {
    print(pos)
    ind = sampled[pos]
    Res9 = solve_realizability_lp(badTournaments[[ind]])
    ResNonMargin1[[pos]] = Res9
    G9 = which(Res9$edge_dual_map > 0, arr.ind = TRUE)
    sampledGraphs[[pos]] = graph(edges = t(G9), n = 9, directed = TRUE)
  }
  
  minNonZeros = sapply(ResNonMargin1, function(x) { y = x[[length(x)]]; min(y[y > 0]) })
  maxNonZeros = sapply(ResNonMargin1, function(x) { y = x[[length(x)]]; max(y[y > 0]) })
  ratios = round(maxNonZeros / minNonZeros, 5)
  scaledDuals = lapply(1:length(ResNonMargin1), function(x) {
    z = ResNonMargin1[[x]]; mz = minNonZeros[x]; y = z[[length(z)]]; y = round(y/mz, 5) })
  
  scaledSampledGraphs = lapply(scaledDuals, graph_from_adjacency_matrix)
  save(sampledGraphs, scaledSampledGraphs, ResNonMargin1, file = "Counterexamples/Non3RealisableWithDualsMargin1.RData")
    
  load("Counterexamples/Non3RealisableWithMargin1Only.RData")
  counterGraphs = lapply(counterexamples, graph_from_adjacency_matrix)
  testResults2 = sapply(counterGraphs, function(x) {subgraph_isomorphic(H, x)})
  stopifnot(all(!testResults2))
  
  n_counter = length(counterexamples)
  counterObstacles = vector("list", n_counter)
  ResNonMargin1Only = vector("list", n_counter)
  
  for (pos in 1:n_counter) {
    print(pos)
    Res9 = solve_realizability_lp(counterexamples[[pos]], equal = TRUE)
    ResNonMargin1Only[[pos]] = Res9
    G9 = which(Res9$edge_dual_map != 0, arr.ind = TRUE)
    counterObstacles[[pos]] = graph(edges = t(G9), n = 9, directed = TRUE)
  }
  
  allNegEdges = lapply(ResNonMargin1Only, function(x) { which(x$edge_dual_map < 0, arr.ind = TRUE) })
  
  counterObstaclesScaled = lapply(ResNonMargin1Only, function(z) {
    y = z$edge_dual_map; mz = min(y[y > 0]); y = round(y/mz, 5); graph_from_adjacency_matrix(abs(y)) })
  
  save(counterObstacles, counterObstaclesScaled, ResNonMargin1Only, file = "Counterexamples/Non3RealisableWithDualsMargin1Only.RData")
  
  load("Tournaments/tournaments9.RData")
  allG = lapply(allGraphs, graph_from_adjacency_matrix)
  
  counterIndices = match(counterexamples, allGraphs)
  nonMargin1Indices = match(badTournaments, allGraphs)
  
  nonMargin1NonHIndices = nonMargin1Indices[which(!testResults)]
  stopifnot(all(counterIndices %in% nonMargin1NonHIndices))
  
  badGlobalPos = which(!is.na(match(nonMargin1Indices, counterIndices)))
  badPos = which(!is.na(match(nonMargin1NonHIndices, counterIndices)))
  
  ResNonRealisable = ResNonMargin1[-badPos]
  sampledGraphs = sampledGraphs[-badPos]
  scaledSampledGraphs = scaledSampledGraphs[-badPos]
  
  V = groupByIsomorphism(sampledGraphs)
  VV = groupByIsomorphism(scaledSampledGraphs)
  stopifnot(identical(V,VV))
  
  X = groupByIsomorphism(counterObstacles)
  XX = groupByIsomorphism(counterObstaclesScaled)
  stopifnot(identical(X,XX))
  
  firstSampled = sampledGraphs[sapply(1:max(V), function(x) {which(V == x)[1]})]
  firstSampledScaled = scaledSampledGraphs[sapply(1:max(V), function(x) {which(V == x)[1]})]
  extraEdgesS = sapply(firstSampledScaled, function(g) { ecount(g) - ecount(simplify(g)) })
  
  firstCounter = counterObstacles[sapply(1:max(X), function(x) {which(X == x)[1]})]
  firstCounterScaled = counterObstaclesScaled[sapply(1:max(X), function(x) {which(X == x)[1]})]
  extraEdgesC = sapply(firstCounterScaled, function(g) { ecount(g) - ecount(simplify(g)) })
  firstCounterNegEdges = allNegEdges[sapply(1:max(X), function(x) {which(X == x)[1]})]
  
  MatE = findIsomorphicCopies(firstCounter, allG, specialIndices = nonMargin1Indices)
  MatEReduced = MatE[, badGlobalPos]
  mode(MatEReduced) = "double"
  MSC1 = minimum_set_cover(MatEReduced)
  firstCounterMin = firstCounter[which(MSC1$solution == 1)]
  firstCounterScaledMin = firstCounterScaled[which(MSC1$solution == 1)]
  
  firstCounterScaledMinRev = lapply(1:length(firstCounterScaledMin), function(ind1) {
    g1 = firstCounterScaledMin[[ind1]]
    # reverse the negative edges using firstCounterNegEdges
    E1 = as_edgelist(g1)
    negEdges = firstCounterNegEdges[[which(MSC1$solution == 1)[ind1]]]
    if (length(negEdges) > 0) {
      for (pos in 1:nrow(negEdges)) {
        negEdge = negEdges[pos, ]
        badPos = which(E1[,1] == negEdge[1] & E1[,2] == negEdge[2])
        stopifnot(length(badPos) == 1)
        E1[badPos, ] = E1[badPos, c(2,1)]
      }
      g1 = graph_from_edgelist(E1, directed = TRUE)  
    }
  })
  
  MatF = findIsomorphicCopies(firstSampled, allG, specialIndices = nonMargin1Indices)
  MatF = rbind(MatF, testResults)
  MatFReduced = MatF[, -badGlobalPos]
  mode(MatFReduced) = "double"
  MSC2 = minimum_set_cover(MatFReduced)
  firstSampledMin = c(firstSampled, list(H))[which(MSC2$solution == 1)]
  firstSampledScaledMin = c(firstSampledScaled, list(H))[which(MSC2$solution == 1)]
  
  num1 = length(firstCounterMin)
  num2 = length(firstSampledMin)
  Mat = matrix(FALSE, num1, num2)
  for (ind1 in 1:num1) {
    for (ind2 in 1:num2) {
      g1 = firstCounterScaledMinRev[[ind1]]
      g2 = firstSampledScaledMin[[ind2]]
      Mat[ind1, ind2] = checkSubgraph(g2, g1)
    }
  }
  subs = which(Mat == 1, arr.ind = TRUE)
  stopifnot(length(unique(subs[,1])) == num1)
  mode(Mat) = "double"
  MSC3 = minimum_set_cover(t(Mat))
  
  output = list(
    sampledGraphs = sampledGraphs,
    scaledSampledGraphs = scaledSampledGraphs,
    ResNonRealisable = ResNonRealisable,
    firstSampled = firstSampled,
    firstSampledScaled = firstSampledScaled,
    firstSampledMin = firstSampledMin,
    firstSampledScaledMin = firstSampledScaledMin,
    extraEdgesS = extraEdgesS,
    counterObstacles = counterObstacles,
    firstCounter = firstCounter,
    firstCounterScaled = firstCounterScaled,
    firstCounterScaledMin = firstCounterScaledMin,
    firstCounterScaledMinRev = firstCounterScaledMinRev,
    firstCounterMin = firstCounterMin,
    extraEdgesC = extraEdgesC,
    MatE = MatE,
    MatF = MatF,
    Mat = Mat
  )
  save(output, file = "Counterexamples/Non3RealisabilitySummary.RData")
}

getMultiHS3 = function(x) {
  y = simplify(x)
  fMat = as_adjacency_matrix(x, sparse = FALSE)
  Mat = as_adjacency_matrix(y, sparse = FALSE)
  cycles = getDirectedTriangles(Mat)
  Sets = createSetChars(cycles, N = vcount(y))
  extSets = extendMatrix(Sets)
  weightMat = fMat + t(fMat)
  weights = weightMat[combn2(1:vcount(y))]
  hittingSetSize = findHittingSet(extSets, integral = TRUE,  all = FALSE, weights = weights)$obj
  hittingSetSize = as.integer(round(hittingSetSize))
  hittingSetSize
}
