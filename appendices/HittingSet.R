library(lpSolve)
library(cplexAPI)
library(combinat)
library(gtools)
library(igraph)
library(magrittr)
library(matrixStats)
library(microbenchmark)
library(tidyverse)

EPSILON = 1e-8

MAX_NUM_PERMS = 8L
print(paste("Initializing permutations up to size", MAX_NUM_PERMS))
for (ind in 1:MAX_NUM_PERMS) {
  print(ind)
  assign(paste0("PERMS", ind), 
         permutations(n = ind, r = ind),
         envir = .GlobalEnv)
}

invertPerm = function(perm) {
  N = length(perm)
  invPerm = rep(0, N)
  invPerm[perm] = 1:N
  invPerm
}

countInversions = function(perm1, perm2) {
  N = length(perm1)
  invPerm1 = invertPerm(perm1)
  invPerm2 = invertPerm(perm2)
  count = 0
  for (i in 1:(N - 1)) {
    for (j in (i + 1):N) {
      if ((invPerm1[i] > invPerm1[j]) != (invPerm2[i] > invPerm2[j])) {
        count = count + 1
      }
    }
  }
  count
}

createInversionMatrix = function(perm) {
  N = length(perm)
  invPerm = invertPerm(perm)
  invMat = matrix(0, N, N)
  for (i in 1:(N - 1)) {
    for (j in (i + 1):N) {
      if (invPerm[i] > invPerm[j]) {
        invMat[i, j] = 1
      }
    }
  }
  invMat
}

# Constructs a graph adjacency matrix from curMat
# Assumes that curMat has only upper-diagonal non-zeros and the value curMat[i,j] is
# 1, 2 or 3 depending on whether only p1, only p2, or both have an inversion in (i,j)
makeAdjMat = function(curMat) {
  stopifnot(nrow(curMat) == ncol(curMat))
  curMat[curMat == 2] = 1
  curMat[t(curMat) == 3] = 1
  curMat[curMat == 0 & upper.tri(curMat)] = 1
  curMat[curMat == 3] = 0
  curMat
}

# Check if the graph is acyclic after reversing the edges in a given collection
checkReversedEdges = function(curMat, edges, returnOrder = FALSE) {
  pairs = matrix(unlist(edges), ncol = 2, byrow = TRUE)
  allEntries = curMat[pairs]
  if (nrow(pairs) == 1) {
    curMat[pairs[1,1], pairs[1,2]] = 1 - allEntries
    curMat[pairs[1,2], pairs[1,1]]     = allEntries
  } else {
    curMat[pairs]   = 1 - allEntries
    curMat[pairs[,2:1]] = allEntries
  }
  g = graph_from_adjacency_matrix(curMat, mode = "directed")
  output = is_dag(g)
  if (returnOrder) {
    if (output) {
      output = topo_sort(g, mode = "out")
      return(output)
    } else {
      return(NA)
    }
  }
  output
}

nonIsomorphicList = function(N = 6, randomise = FALSE) {
  numPerm = factorial(N)
  allPerm = get(paste0("PERMS", N))
  load(paste0("Tournaments/tournaments", N, "C.RData"))
  matches = rep(FALSE, length(allGraphs))
  inversionMatrices = vector("list", numPerm)
  for (ind in 1:numPerm) {
    curPerm = allPerm[ind, ]
    inversionMatrices[[ind]] = createInversionMatrix(curPerm)
  }
  allPairs = combn2(1:numPerm)
  if (randomise) {
    allPairs = allPairs[sample(nrow(allPairs)), ]
  }
  numPairs = nrow(allPairs)
  print(paste("There are", numPairs, "pairs to check"))
  for (ind in 1:nrow(allPairs)) {
    curRow = allPairs[ind, ]
    ind1 = curRow[[1]]
    ind2 = curRow[[2]]
    curMat1 = inversionMatrices[[ind1]]
    d12 = sum(curMat1)
    curMat2 = inversionMatrices[[ind2]]
    d13 = sum(curMat2)
    d23 = sum(xor(curMat1, curMat2))
    if (d23 < d12 || d23 < d13) { next }
    curMat = curMat1 + curMat2 * 2
    adjMat = makeAdjMat(curMat)
    g = graph_from_adjacency_matrix(adjMat, mode = "directed")
    perm = canonical_permutation(g)$labeling
    adjMat[perm, perm] = adjMat
    curPos = match(list(adjMat), allGraphs)
    if (is.na(curPos)) { stop(paste("Could not find matching graph at", ind1, "and", ind2)) }
    if (matches[curPos] == 0) {
      matches[curPos] = ind1 * numPerm + ind2
      if (sum(matches > 0) %% 100 == 0) {
        print(paste("Found", sum(matches > 0), "unique graphs so far"))
      }
      if (all(matches > 0)) { return(matches) }
    }
  }
  matches
}

exhaustiveCheck = function(N = 6) {
  numPerm = factorial(N)
  allPerm = get(paste0("PERMS", N))
  inversionMatrices = list()
  for (ind in 1:numPerm) {
    curPerm = allPerm[ind, ]
    inversionMatrices[[ind]] = createInversionMatrix(curPerm)
  }
  fracSolutions = matrix(NA, choose(numPerm, 2)/100, 4)
  colnames(fracSolutions) = c("Perm1", "Perm2", "Frac", "Int")  
  pos = 1
  nonAcyclic = matrix(NA, numPerm, 2)
  colnames(nonAcyclic) = c("Perm1", "Perm2")
  altPos = 1
  allGraphs = vector("list", 3^N) # Rough upper bound on number of graphs
  allRecords = matrix(0, 3^N, 5)
  colnames(allRecords) = c("Perm1", "Perm2", "Count", "Size", "Support")
  graphPos = 1
  for (ind1 in 1:(numPerm - 1)) {
    print(ind1)
    curMat1 = inversionMatrices[[ind1]]
    d12 = sum(curMat1)
    for (ind2 in (ind1 + 1):numPerm) {
      curMat2 = inversionMatrices[[ind2]]
      d13 = sum(curMat2)
      d23 = sum(xor(curMat1, curMat2))
      if (d23 < d12 || d23 < d13) { next }
      lowerBound = (d12 + d13 + d23)/2
      # Find all the 3-cycles
      curMat = curMat1 + curMat2 * 2
      cycles = getThreeCycles_fast(curMat)
      numCycles = nrow(cycles)
      if (numCycles > 1) {
        uVals = sort(unique(as.vector(cycles)))
        cycles = matrix(match(cycles, uVals), ncol = 3)
        relevantEdges = unique(rbind(cycles[, 1:2], cycles[, 2:3], cycles[, c(3,1)]))
        g = graph_from_edgelist(relevantEdges, directed = TRUE)
        perm = canonical_permutation(g)$labeling
        cycles = matrix(perm[cycles], ncol = 3)
        cycles = sort3_vectorized(cycles)
        cycles = cycles[, order(cycles[1, ], cycles[2, ], cycles[3, ]), drop = FALSE]
        numVals = max(cycles)
        goodInds = which(allRecords[1:graphPos, "Size"] == numCycles & allRecords[1:graphPos, "Support"] == numVals)
        test = match(list(cycles), allGraphs)
        if (is.na(test)) {
          allGraphs[[graphPos]] = cycles
          allRecords[graphPos, ] = c(ind1, ind2, 1, numCycles, numVals)
          if (graphPos %% 100 == 0) { print(paste("Found", graphPos, "unique graphs so far")) }
          graphPos = graphPos + 1
        }
      }
    }
  }
  allGraphs     = allGraphs[seq_len(graphPos - 1)]
  allRecords    = allRecords[seq_len(graphPos - 1), , drop = FALSE]
  output = list(graphs = allGraphs, records = allRecords)
  output
}

# Direct vectorized sorting for a Kx3 matrix (suggested by Claude)
sort3_vectorized <- function(mat) {
  vec1 <- mat[,1]
  vec2 <- mat[,2] 
  vec3 <- mat[,3]
  # Find min, max, and middle values
  min_val <- pmin(vec1, vec2, vec3)
  max_val <- pmax(vec1, vec2, vec3)
  mid_val <- vec1 + vec2 + vec3 - min_val - max_val
  # Return result as a Kx3 matrix
  output <- rbind(min_val, mid_val, max_val)
  dimnames(output) <- NULL
  output
}

# This function computes the canonical representation of a graph composed of a collection of 3-cycles
# Each cycle is represented as (i,j,k) where i < j < k are the vertices
# The canonical representative is the lexicographically smallest representation of the cycle collection
# under renumbering of the vertices and reordering of the cycles
# For example, rbind(c(1,2,3), c(1,2,4), c(2,3,4)) would be canonical for both itself as well as
# rbind(c(1,2,4), c(1,2,5), c(2,4,5)) and rbind(c(2,3,4), c(2,3,5), c(3,4,5)), and so on.
makeCanonical = function(cycles, prevCanonical = NULL, permuteFully = FALSE) {
  numCycles = nrow(cycles)
  uVals  = sort(unique(as.vector(cycles)))
  numVals = length(uVals)
  cycles = matrix(match(cycles, uVals), ncol = 3)
  if (permuteFully) {
    if (numVals > 3) {
      canonCycles = t(cycles)
      if (!is.null(prevCanonical) && list(canonCycles) %in% prevCanonical) {
        break
      }
      allPerms = get(paste0("PERMS", numVals))
      # Filter down to the permutations that keep one of the cycles mapped to 123 in some order; there will be numCycles * 3! * (numVals - 3)!
      goodPerms = c()
      for (ind in 1:numCycles) {
        goodPerms = c(goodPerms, which(rowSums(allPerms[, cycles[ind, ]] <= 3) == 3))
      }
      for (index in goodPerms) {
        permutedCycles = matrix(allPerms[index, cycles], ncol = 3)
        permutedCycles = sort3_vectorized(permutedCycles) # Note that the result is transposed, which is exactly what we need!
        permutedCycles = permutedCycles[, order(permutedCycles[1,], permutedCycles[2,], permutedCycles[3,]), drop = FALSE]
        # Lexicographic comparison between canonCycles and permutedCycles suggested by Claude: find first differing element
        diff_pos <- Position(function(i) permutedCycles[i] != canonCycles[i], seq_along(canonCycles))
        if (!is.na(diff_pos) && permutedCycles[diff_pos] < canonCycles[diff_pos]) {
          canonCycles = permutedCycles
          if (!is.null(prevCanonical) && list(canonCycles) %in% prevCanonical) {
            break
          }
        }
      }
      cycles = t(canonCycles)
    }
  }
  cycles
}
  
# This function extracts 3-cycles from adjMat, which have the following form:
# (i,j,k) with i < j < k such that (i,j) and (j,k) are inversions in one of the
# permutations (adjMat[i,j] and adjMat[j,k] are 1 or 2) and (i,k) is an inversion
# in both permutations (adjMat[i,k] == 3)
getThreeCycles = function(adjMat) {
  onesOrTwos = which(adjMat == 1 | adjMat == 2, arr.ind = TRUE) %>%
    as_tibble()
  threes = which(adjMat == 3, arr.ind = TRUE) %>%
    as_tibble()
  cycles = inner_join(onesOrTwos, onesOrTwos, by = c("col" = "row"), relationship = "many-to-many") %>%
    set_colnames(c("i", "j", "k")) %>%
    inner_join(threes, by = join_by(i == row, k == col)) %>%
    as.matrix()
  cycles
}

getDirectedTriangles = function(adjMat) {
  N = nrow(adjMat)
  triangles = matrix(0, nrow = choose(N, 3), ncol = 3)
  pos = 1
  for (ind1 in 1:(N - 2)) {
    for (ind2 in (ind1 + 1):(N - 1)) {
      if (adjMat[ind1, ind2] == 1) {
        for (ind3 in (ind2 + 1):N) {
          if (adjMat[ind2, ind3] == 1 && adjMat[ind3, ind1] == 1) {
            triangles[pos,] = c(ind1, ind2, ind3)
            pos = pos + 1
          }
        }
      } 
      if (adjMat[ind2, ind1] == 1) {
        for (ind3 in (ind2 + 1):N) {
          if (adjMat[ind1, ind3] == 1 && adjMat[ind3, ind2] == 1) {
            triangles[pos,] = c(ind1, ind3, ind2)
            pos = pos + 1
          }
        }
      }
    }
  }
  triangles = triangles[seq_len(pos - 1), , drop = FALSE]
  triangles
}

### Faster version of getThreeCycles using only matrices (suggested by Claude)
getThreeCycles_fast <- function(adjMat) {
  # Get indices directly as matrices (no tibble conversion)
  onesOrTwos <- which(adjMat == 1 | adjMat == 2, arr.ind = TRUE)
  threes <- which(adjMat == 3, arr.ind = TRUE)
  if (nrow(onesOrTwos) == 0 || nrow(threes) == 0) {
    return(matrix(nrow = 0, ncol = 3))
  }
  # Pre-allocate result storage
  cycles_list <- vector("list", nrow(threes))
  count <- 0
  # For each (i,k) pair where adjMat[i,k] == 3
  for (idx in 1:nrow(threes)) {
    i <- threes[idx, 1]
    k <- threes[idx, 2]
    # Find all j where adjMat[i,j] is 1 or 2 AND adjMat[j,k] is 1 or 2
    # This is equivalent to the inner join on "col" = "row"
    j_from_i <- onesOrTwos[onesOrTwos[,1] == i, 2]
    j_to_k <- onesOrTwos[onesOrTwos[,2] == k, 1]
    # Find intersection (the common j values)
    j_common <- intersect(j_from_i, j_to_k)
    n_common = length(j_common)
    if (n_common > 0) {
      count <- count + 1
      cycles_list[[count]] <- cbind(rep(i, n_common), j_common, rep(k, n_common))
    }
  }
  # Combine results
  if (count > 0) {
    do.call(rbind, cycles_list[1:count])
  } else {
    matrix(nrow = 0, ncol = 3)
  }
}

mapPairToSingleIndex = function(i, j, N) {
  stopifnot(i < j)
  colInd = choose(N, 2) - choose(N - i + 1, 2) + (j - i)
  colInd
}

mapSingleIndexToPair = function(colInd, N) {
  stopifnot(colInd <= choose(N, 2))
  i = 1
  while (colInd > (N - i)) {
    colInd = colInd - (N - i)
    i = i + 1
  }
  j = i + colInd
  c(i, j)
}

# This function extends a matrix of sets into a matrix where each column
# corresponds to a pair of elements, and each row corresponds to a set.
# An entry is 1 if the set contains both elements of the pair, and 0 otherwise.
extendMatrix = function(Sets) {
  M = nrow(Sets)
  N = ncol(Sets)
  extSets = matrix(0, M, choose(N, 2))
  for (ind in 1:M) {
    curSet = which(Sets[ind, ] == 1)
    stopifnot(length(curSet) == 3)
    i = curSet[1]
    j = curSet[2]
    k = curSet[3]
    colInds = c(mapPairToSingleIndex(i, j, N), mapPairToSingleIndex(i, k, N), mapPairToSingleIndex(j, k, N))
    extSets[ind, colInds] = 1
  }
  return(extSets)
}

findHittingSet = function(extSets, integral = FALSE, all = FALSE, exact = FALSE, weights = NULL) {
  M = nrow(extSets)
  numPairs = ncol(extSets)
  N = (sqrt(8 * numPairs + 1) + 1)/2
  stopifnot(near(N, round(N)))
  if (!is.null(weights)) {
    f.obj = weights
  } else {
    f.obj = rep(1, numPairs)
  }
  f.con = extSets
  f.dir = rep(ifelse(exact, "=", ">="), M)
  # f.dir = rep(ifelse(exact, "E", "G"), M)
  f.rhs = rep(1, M)
  # res = Rcplex(
  #   cvec = f.obj,
  #   Amat = f.con,
  #   bvec = f.rhs,
  #   sense = f.dir,
  #   vtype = rep(ifelse(integral, "B", "C"), numPairs),
  #   control = list(
  #     trace = 0,
  #     tilim = 300
  #   )
  # )
  # usedVars = map(which(res$xopt > 0), mapSingleIndexToPair, N)
  # output = list(obj = res$obj, sol = usedVars)
  res = lp("min", f.obj, f.con, f.dir, f.rhs, all.bin = integral, compute.sens = !integral,
           num.bin.solns = if (all) 1000 else 1, use.rw = if (all) TRUE else FALSE)
  if (all) {
    numSolutions = res$num.bin.solns
    allSolutions = vector("list", numSolutions)
    pos = 0
    size = res$bin.count
    objVal = res$objval
    for (solInd in 1:numSolutions) {
      usedVars = map(which(res$solution[pos + (1:size)] > 0), mapSingleIndexToPair, N)
      allSolutions[[solInd]] = list(obj = objVal, sol = usedVars)
      pos = pos + size
    }
    output = allSolutions
  } else {
    usedVars = map(which(res$solution > 0), mapSingleIndexToPair, N)
    output = list(obj = res$objval, sol = usedVars)
  }
  if (all) {
    output = list(output)
  }
  output
}

conjectureTest = function(N = 6, ind2 = 324, ind3 = 677, delta = FALSE, bicolor = FALSE, greedy = FALSE, returnOrder = FALSE) {
  allPerm = get(paste0("PERMS", N))
  p2 = allPerm[ind2,]
  p3 = allPerm[ind3,]
  if (delta) {
    return(checkMatchesBound(p2, p3))
  } else if (bicolor) {
    return(checkBicolor(p2, p3))
  } else if (greedy) {
    return(checkGreedy(p2, p3))
  } else {
    return(checkHittingSets(p2, p3, returnOrder = returnOrder))
  }
}

checkLPClose = function(adjMat) {
  cycles = getDirectedTriangles(adjMat)
  if (nrow(cycles) <= 1) { return(TRUE) }
  N = nrow(adjMat)
  Sets = createSetChars(cycles, N = N)
  extSets = extendMatrix(Sets)
  hittingSet0 = findHittingSet(extSets, integral = FALSE, all = FALSE)$obj
  hittingSet1 = findHittingSet(extSets, integral = TRUE,  all = FALSE)$obj
  return((hittingSet1 - hittingSet0 < 1 - EPSILON))
}

checkExact = function(adjMat) {
  cycles = getDirectedTriangles(adjMat)
  if (nrow(cycles) <= 1) { return(TRUE) }
  N = nrow(adjMat)
  Sets = createSetChars(cycles, N = N)
  extSets = extendMatrix(Sets)
  value0 = findHittingSet(extSets, integral = TRUE, all = FALSE, exact = FALSE)$obj
  value1 = findHittingSet(extSets, integral = TRUE, all = FALSE, exact = TRUE)$obj
  return(value0 == value1)
}

checkSufficient = function(cycles, adjMat, returnOrder = FALSE, stopEarly = FALSE) {
  N = nrow(adjMat)
  Sets = createSetChars(cycles, N = N)
  extSets = extendMatrix(Sets)
  allHittingSets = findHittingSet(extSets, integral = TRUE, all = TRUE)
  # print(paste0("Number of hitting sets found: ", length(allHittingSets)))
  numFound = 0
  allFound = matrix(nrow = length(allHittingSets), ncol = N)
  pos = 1
  for (hset in allHittingSets) {
    check = checkReversedEdges(adjMat, hset$sol, returnOrder = returnOrder)
    if (stopEarly && !returnOrder && check) {
      return(TRUE)
    }
    if (returnOrder) {
      if (!all(is.na(check))) {
        allFound[pos, ] = check
        pos = pos + 1
      }
    } else {
      numFound = numFound + check
    }
  }
  if (returnOrder) {
    output = allFound[seq_len(pos - 1), , drop = FALSE]
  } else {
    output = c(numFound, length(allHittingSets))
  }
  output
}

checkHittingSets = function(p2, p3, returnOrder = FALSE, stopEarly = FALSE) {
  curMat1 = createInversionMatrix(p2)
  curMat2 = createInversionMatrix(p3)
  curMat = curMat1 + curMat2 * 2
  cycles = getThreeCycles_fast(curMat)
  adjMat = makeAdjMat(curMat)
  output = checkSufficient(cycles, adjMat, returnOrder = returnOrder, stopEarly = stopEarly)
  output
}

createSetChars = function(Sets, N = NA) {
  if (is.na(N)) {
    N = max(Sets)
  }
  M = nrow(Sets)
  Mat = matrix(0, M, N)
  for (ind in 1:M) {
    curSet = Sets[ind, ]
    Mat[ind, curSet] = 1
  }
  Mat
}

checkBadPairs = function(fname = "Record7.txt") {
  N = str_extract(fname, "\\d+") %>% 
    as.integer()
  data = read_lines(fname)
  badPairs = list()
  pairCount = 0
  warnLines = str_which(data, "acyclic")
  pairLines = warnLines - 1
  goodLines = data[pairLines] %>%
    str_remove_all("\\[1\\] ") %>%
    str_split_fixed(" ", n = 2)
  mode(goodLines) = "integer"
  for (ind in 1:nrow(goodLines)) {
    ind2 = goodLines[ind, 1]
    ind3 = goodLines[ind, 2]
    res = conjectureTest(N = N, ind2 = ind2, ind3 = ind3)
    if (!res) {
      print(paste("Bad pair found:", ind2, ind3))
    }
  }
  goodLines
}

makeTestCase = function(p2, p3) {
  curMat1 = createInversionMatrix(p2)
  curMat2 = createInversionMatrix(p3)
  curMat = curMat1 + curMat2 * 2
  cycles = getThreeCycles_fast(curMat)
  cycles
}

greedyHittingSet = function(cycles, by = "standard") {
  N = max(cycles)
  Sets = createSetChars(cycles, N)
  extSets = extendMatrix(Sets)
  M = nrow(extSets)
  numPairs = ncol(extSets)
  covered = rep(FALSE, M)
  hittingSet = list()
  if (by == "mindiff") {
    goodOrder = sapply(1:numPairs, function(colInd) {
      pair = mapSingleIndexToPair(colInd, N)
      c(abs(pair[1] - pair[2]), pair[1])
    }) %>% 
      t() %>%
      as.data.frame() %>%
      do.call(order, .)
    extSets = extSets[, goodOrder, drop = FALSE]
  }
  while (any(!covered)) {
    uncoveredSets = which(!covered)
    pairCounts = colSums(extSets[uncoveredSets, , drop = FALSE])
    bestPairInd = which.max(pairCounts)
    bestPair = mapSingleIndexToPair(bestPairInd, N = N)
    hittingSet[[length(hittingSet) + 1]] = bestPair
    covered = covered | (extSets[, bestPairInd] == 1)
  }
  hittingSet
}

checkConnected = function(p2, p3) {
  cycles = makeTestCase(p2, p3)
  stopifnot(ncol(cycles) == 3)
  if (nrow(cycles) == 1) { return(TRUE) }
  allEdges = unique(rbind(cycles[, 1:2], cycles[, 2:3], cycles[, c(3,1)]))
  testGraph = graph_from_edgelist(allEdges, directed = TRUE)
  is_connected(testGraph)
}

checkMatchesBound = function(p2, p3) {
  curMat1 = createInversionMatrix(p2)
  curMat2 = createInversionMatrix(p3)
  curMat = curMat1 + curMat2 * 2
  cycles = getThreeCycles_fast(curMat)
  uVals = unique(as.vector(cycles))
  numVals = length(uVals)
  numPairs = nrow(unique(rbind(cycles[,-1], cycles[, -2], cycles[, -3])))
  if (numPairs < choose(numVals, 2)) {
    print("There are missing pairs, so the bound does not apply")
    return(TRUE)
  }
  adjMat = makeAdjMat(curMat)
  adjMat = adjMat[uVals, uVals]
  targetOutDegrees = 0:(numVals - 1)
  actualOutDegrees = sort(rowSums(adjMat != 0))
  delta = sum(abs(targetOutDegrees - actualOutDegrees))/2
  Sets = createSetChars(cycles, N = max(cycles))
  extSets = extendMatrix(Sets)
  hittingSetSize = findHittingSet(extSets, integral = TRUE, all = FALSE)$obj
  if (hittingSetSize == delta) {
    print("Hitting set size meets the bound")
    return(TRUE)
  } else {
    print(paste("Hitting set size", hittingSetSize, "is greater than the bound", delta))
    return(FALSE)
  }
}

checkBicolor = function(p2, p3) {
  curMat1 = createInversionMatrix(p2)
  curMat2 = createInversionMatrix(p3)
  adjMat = curMat1 + curMat2 * 2
  cycles = getThreeCycles_fast(adjMat)
  Sets = createSetChars(cycles, N = max(cycles))
  extSets = extendMatrix(Sets)
  hittingSets = findHittingSet(extSets, integral = TRUE, all = TRUE)
  for (hset in hittingSets) {
    curColors = adjMat[matrix(unlist(hset$sol), ncol = 2, byrow = TRUE)]
    if (length(unique(curColors)) <= 2) {
      print("Found a bicoloring that works")
      return(TRUE)
    }
  }
  print("No bicoloring works")
  return(FALSE)
}

checkGreedy = function(p2, p3, by = "mindiff") {
  curMat1 = createInversionMatrix(p2)
  curMat2 = createInversionMatrix(p3)
  curMat = curMat1 + curMat2 * 2
  cycles = getThreeCycles_fast(curMat)
  hittingSet = greedyHittingSet(cycles, by = by)
  adjMat = makeAdjMat(curMat)
  check = checkReversedEdges(adjMat, hittingSet)
  if (check) {
    print("Greedy hitting set works")
  } else {
    print("Greedy hitting set does not work")
  }
  Sets = createSetChars(cycles, N = max(cycles))
  extSets = extendMatrix(Sets)
  optimalHittingSetSize = findHittingSet(extSets, integral = TRUE, all = FALSE)$obj
  if (length(hittingSet) == optimalHittingSetSize) {
    print("Greedy hitting set is optimal")
    return(TRUE)
  } else {
    print(paste("Greedy hitting set size", length(hittingSet), "is larger than optimal size", optimalHittingSetSize))
    return(FALSE)
  }
}

testHypotheses = function(Results, delta = FALSE, bicolor = FALSE, greedy = FALSE, returnOrder = FALSE) {
  N = max(unlist(Results$graphs))
  uniqueConf = Results$records
  numConf = nrow(uniqueConf)
  allTests = vector("list", numConf)
  print(paste("There are", numConf, "unique configurations to test"))
  for (ind in 1:numConf) {
    if (ind %% 100 == 0) { print(ind) }
    curRow = uniqueConf[ind,]
    curTest = conjectureTest(N = N, ind2 = curRow[1], ind3 = curRow[2], delta = delta, bicolor = bicolor, greedy = greedy, returnOrder = returnOrder)
    allTests[[ind]] = curTest
  }
  allTests = do.call(rbind, allTests)
  allTests
}

findCandidates = function(Results) {
  N = max(Results$records[,"Support"])
  miniRes = list(Results$graphs, Results$records)
  miniInds = which(miniRes$records[, "Size"] >= choose(N,2)/3 & miniRes$records[, "Support"] == N)
  miniRes$graphs = miniRes$graphs[miniInds]
  miniRes$records = miniRes$records[miniInds, , drop = FALSE]
  names(miniRes) = c("graphs", "records")
  Q0 = testHypotheses(miniRes, delta = FALSE, bicolor = FALSE, greedy = FALSE, returnOrder = FALSE)
  candidateInds = which(Q0[,1] >= N)
  miniRes$graphs = miniRes$graphs[candidateInds]
  miniRes$records = miniRes$records[candidateInds, , drop = FALSE]
  Q0 = Q0[candidateInds, , drop = FALSE]
  print(paste("There are", nrow(miniRes$records), "candidate configurations remaining"))
  if (nrow(miniRes$records) == 0) {
    return(list(graphs = list(), records = matrix(nrow = 0, ncol = ncol(Results$records)), orders = list()))
  }
  Q1 = testHypotheses(miniRes, delta = FALSE, bicolor = FALSE, greedy = FALSE, returnOrder = TRUE)
  outputs = split(Q1, rep(1:length(candidateInds), Q0[,1]))
  outputs = lapply(outputs, function(x) { matrix(x, ncol = N) })
  finalCandidates = which(sapply(outputs, function(x) {length(unique(x[,1])) == N}))
  finalRes = list(graphs = miniRes$graphs[finalCandidates],
                  records = miniRes$records[finalCandidates, , drop = FALSE],
                  orders = outputs[finalCandidates])
  finalRes
}

testAllHypotheses = function(Results) {
  H0 = testHypotheses(Results, delta = FALSE, bicolor = FALSE, greedy = FALSE)
  H1 = testHypotheses(Results, delta = TRUE, bicolor = FALSE, greedy = FALSE)
  H2 = testHypotheses(Results, delta = FALSE, bicolor = TRUE, greedy = FALSE)
  H3 = testHypotheses(Results, delta = FALSE, bicolor = FALSE, greedy = TRUE)
  data.frame(H0 = H0, H1 = H1, H2 = H2, H3 = H3)
}

postprocessResults = function(Results) {
  Records = Results$records
  Graphs = Results$graphs
  numGraphs = nrow(Records)
  graphSizes = Records[, "Size"]
  graphSupports = Records[, "Support"]
  graphCounts = Records[, "Count"]
  graphIsomorphs = vector("list", numGraphs)
  print(paste("There are", numGraphs, "graphs to process for isomorphism"))
  for (ind in 1:numGraphs) {
    if (ind %% 100 == 0) { print(ind) }
    goodPrevious = ifelse(ind == 1, 0, which(graphSizes[1:(ind-1)] == graphSizes[ind] & graphSupports[1:(ind-1)] == graphSupports[ind]))
    graphIsomorphs[[ind]] = makeCanonical(Graphs[[ind]], permuteFully = TRUE, prevCanonical = graphIsomorphs[goodPrevious])
  }
  goodIndices = which(!duplicated(graphIsomorphs))
  uniqueIsomorphs = graphIsomorphs[goodIndices]
  matchVector = match(graphIsomorphs, uniqueIsomorphs)
  aggregateCounts = sapply(split(graphCounts, matchVector), function(x) {sum(x, na.rm = TRUE)})
  names(aggregateCounts) = NULL
  allRecords = matrix(0, length(uniqueIsomorphs), 5)
  colnames(allRecords) = c("Perm1", "Perm2", "Count", "Size", "Support")
  for (ind in 1:length(uniqueIsomorphs)) {
    firstInd = which(matchVector == ind)[1]
    allRecords[ind, ] = c(Records[firstInd, 1:2], aggregateCounts[ind], graphSizes[firstInd], graphSupports[firstInd])
  }
  output = list(scores = Results$scores, fracSolutions = Results$fracSolutions, nonAcyclic = Results$nonAcyclic, 
                graphs = uniqueIsomorphs, records = allRecords)
  output
}

### This function removes any singleton (isolated) vertices from an input igraph
deleteSingletons = function(iGraph) {
  singletons = V(iGraph)[degree(iGraph) == 0]
  newGraph = delete_vertices(iGraph, singletons)
  newGraph
}

### This auxiliary function converts an igraph into its canonical representative
canonicallyOrderGraph = function(iGraph) {
  output = permute(iGraph, canonical_permutation(iGraph)$labeling)
  output
}

parseTournaments = function(N, filename = paste0("tournaments", N, ".txt")) {
  allTournaments = readLines(filename)
  numTournaments = length(allTournaments)
  print(paste("There are", numTournaments, "tournaments on", N, "vertices"))
  allGraphs = vector("list", numTournaments)
  for (ind in 1:numTournaments) {
    if (ind %% 1000 == 0) { print(ind) }
    adjStr = as.integer(strsplit(allTournaments[ind], "")[[1]])
    adjMat = matrix(0, N, N)
    adjMat[lower.tri(adjMat)] = 1L - adjStr
    adjMat[upper.tri(adjMat)] = 1L - t(adjMat)[upper.tri(adjMat)]
    allGraphs[[ind]] = adjMat
  }
  save(allGraphs, file = str_replace(filename, ".txt", ".RData"))
  allGraphs
}

checkTournaments = function(N, unique = FALSE, LP = FALSE, returnOrder = FALSE, stopEarly = TRUE, filename = NULL) {
  if (!is.null(filename)) {
    load(filename)
  } else {
    load(paste0("tournaments", N, ".RData"))
  }
  numGraphs = length(allGraphs)
  print(paste("Checking", numGraphs, "tournaments on", N, "vertices"))
  output = vector("list", numGraphs)
  pos = 1
  for (ind in 1:numGraphs) {
    if (ind %% 1 == 0) { print(ind) }
    curMat = allGraphs[[ind]]
    if (unique) {
      g = graph_from_adjacency_matrix(curMat, mode = "directed")
      canPerm = canonical.permutation(g)$labeling
      curMat[canPerm, canPerm] = curMat
      output[[pos]] = curMat
      pos = pos + 1
    } else {
      if (LP) {
        res = checkExact(curMat)  ### WAS: res = checkLPClose(curMat)
        if (!res) {
          print(paste("Failure at index", ind))
          return(FALSE)
        }
        output[[ind]] = res
      } else {
        cycles = getDirectedTriangles(curMat)
        if (nrow(cycles) > 0) {
          res = checkSufficient(cycles, curMat, returnOrder = returnOrder, stopEarly = stopEarly)
          if (!returnOrder && stopEarly && !res) {
            print(paste("Failure at index", ind))
            return(FALSE)
          }
          output[[ind]] = res
        }
      }
    }
  }
  if (unique) {
    output = output[seq_len(pos - 1)]
  }
  return(output)
}

generateAndCheckPermutations = function(N) {
  root = N
  power = 1
  while (root %% 2 == 0) {
    root = root/2
    power = power * 2
  }
  if (root == 1) {
    print('N must have an odd factor')
    return(NULL)
  }
  p1 = 1:N
  largeHalf = (root + 1)/2
  smallHalf = (root - 1)/2
  blocks = split(p1, rep(1:root, each = power))
  p2 = blocks[c(smallHalf + (1:largeHalf), 1:smallHalf)] %>%
    do.call(cbind, .) %>%
    as.vector()
  indices = rep(NA, root)
  indices[2 * (1:largeHalf) - 1] = smallHalf + (largeHalf:1)
  indices[2 * (1:smallHalf)] = smallHalf:1
  p3 = blocks[indices] %>%
    do.call(cbind, .) %>%
    as.vector()
  result = checkPermutations(p2, p3)
  result
}

checkPermutations = function(p2, p3) {
  N = length(p2)
  curMat1 = createInversionMatrix(p2)
  curMat2 = createInversionMatrix(p3)
  curMat = curMat1 + curMat2 * 2
  cycles = getThreeCycles_fast(curMat)
  adjMat = makeAdjMat(curMat)
  output = checkSufficient(cycles, adjMat, returnOrder = TRUE, stopEarly = FALSE)
  output = output[do.call(order, as.data.frame(output)), ]
  M = nrow(output)
  fullCheck = rep(NA, N)
  for (ind in 1:N) {
    curShift = shiftVector(1:N, ind)
    goodPos = which(rowSums(output == matrix(curShift, nrow = M, ncol = N, byrow = TRUE)) == N)
    if (length(goodPos) > 0) {
      fullCheck[ind] = goodPos
    }
  }
  output = list(orders = output, shifts = fullCheck)
  output
}

shiftVector = function(Vector, pos) {
  N = length(Vector)
  pos = pos %% N
  if (pos == 0) {
    return(Vector)
  }
  output = c(Vector[(N - pos + 1):N], Vector[1:(N - pos)])
  output
}

findIncomplete = function(filename) {
  N = str_extract(filename, "\\d+") %>% 
    as.integer()
  res = checkTournaments(N, stopEarly = FALSE, filename = filename)
  incompleteInds = which(sapply(res, function(x) {!is.null(x) && x[1] < x[2]}))
  load(filename)
  incompleteGraphs = allGraphs[incompleteInds]
  incompleteGroups = lapply(incompleteGraphs, function(x) {
    g = graph_from_adjacency_matrix(x, mode = "directed")
    autoSize = as.integer(count_automorphisms(g)$group_size)
    if (autoSize > 1) {
      autoGens = automorphism_group(g) %>%
        do.call(rbind, .)
      permGroup = constructPermGroup(autoGens, autoSize)
    } else {
      permGroup = matrix(1:N, ncol = 1)
    }
  })
  output = list(inds = incompleteInds, counts = res[incompleteInds], graphs = incompleteGraphs, groups = incompleteGroups)
  output
}

### This function constructs a permutation group of given size from its generators
### The construction works by an implicit breadth-first search of the Cayley graph
### NOTE: The generators are specified by row, but the group is returned by column
### This functon was improved by ChatGPT's suggestion (namely, using a hash table)
constructPermGroup <- function(generatorList, numElts = NA) {
  n <- ncol(generatorList)
  L <- nrow(generatorList)
  if (is.na(numElts)) {
    numElts <- factorial(n)
  }
  # Initialise storage
  allElts <- matrix(NA_integer_, numElts, n)
  identity <- seq_len(n)
  if (L == 1 && all(generatorList[1,] == identity)) {
    # If only the identity generator is provided, return it
    return(t(generatorList))
  }
  allElts[1:(L + 1), ] <- rbind(identity, generatorList)
  pos <- L + 1
  # Use a hash set of seen permutations (via string keys)
  seen <- new.env(hash = TRUE, parent = emptyenv())
  key <- function(x) paste(x, collapse = ",")
  seen[[key(identity)]] <- TRUE
  for (index in 1:L) seen[[key(generatorList[index, ])]] <- TRUE
  curActive <- 2:(L + 1)
  while (length(curActive) > 0) {
    newActive <- integer(0)
    for (genIndex in 1:L) {
      gen <- generatorList[genIndex, ]
      for (active in curActive) {
        # Apply generator
        newElt <- allElts[active, gen]
        newKey <- key(newElt)
        if (!exists(newKey, envir = seen, inherits = FALSE)) {
          pos <- pos + 1
          allElts[pos, ] <- newElt
          newActive <- c(newActive, pos)
          seen[[newKey]] <- TRUE
        }
      }
    }
    curActive <- newActive
  }
  output <- t(allElts[1:pos, , drop = FALSE])
  output
}

findFAS = function(adjMat) {
  N = nrow(adjMat)
  g = graph_from_adjacency_matrix(adjMat, mode = "directed")
  fasEdges = feedback_arc_set(g, algo = "exact_ip")
  fasEdges
}

findCounterexample = function(N = 11, filename = NULL) {
  if (!is.null(filename)) {
    load(filename)
  } else {
    load(paste0("Tournaments/tournaments", N, ".RData"))
  }
  numGraphs = length(allGraphs)
  print(paste("Checking", numGraphs, "tournaments on", N, "vertices"))
  output = rep(TRUE, numGraphs)
  for (ind in 1:numGraphs) {
    print(ind)
    curMat = allGraphs[[ind]]
    cycles = getDirectedTriangles(curMat)
    if (nrow(cycles) > 0) {
      Sets = createSetChars(cycles, N = N)
      extSets = extendMatrix(Sets)
      hittingSetSize = as.integer(round(findHittingSet(extSets, integral = TRUE,  all = FALSE)$obj))
      fasSize = length(findFAS(curMat))
      result = (hittingSetSize == fasSize)
      if (!result) {
        print(paste("Counterexample found at index", ind))
      }
      output[[ind]] = result
    }
  }
  return(output)
}

# res = microbenchmark(
#   original = nonIsomorphicList(N = 5),
#   randomized = nonIsomorphicList(N = 5, randomise = TRUE),
#   times = 10
# )
