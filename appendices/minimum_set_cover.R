#!/usr/bin/env Rscript
#
# Minimum Set Cover via ILP using Rcplex
#

library(Rcplex)

#' Solve minimum set cover problem
#' @param cover_matrix Binary matrix: rows are sets, columns are elements
#'                     cover_matrix[i,j] = 1 if set i covers element j
#' @param set_names Optional names for sets (row names)
#' @param element_names Optional names for elements (column names)
#' @param time_limit Time limit in seconds
#' @param verbose Print detailed output
#' @return List with selected sets, objective value, and solution details
minimum_set_cover <- function(cover_matrix, 
                              set_names = NULL, 
                              element_names = NULL,
                              time_limit = 300, 
                              verbose = TRUE) {
  
  n_sets <- nrow(cover_matrix)
  n_elements <- ncol(cover_matrix)
  
  if (is.null(set_names)) {
    set_names <- paste0("Set_", 1:n_sets)
  }
  if (is.null(element_names)) {
    element_names <- paste0("Element_", 1:n_elements)
  }
  
  if (verbose) {
    cat(strrep("=", 70))
    cat("\nMinimum Set Cover Problem\n")
    cat(strrep("=", 70))
    cat("\n")
    cat(sprintf("Sets: %d\n", n_sets))
    cat(sprintf("Elements: %d\n", n_elements))
    cat("\n")
  }
  
  # Variables: x[i] = 1 if set i is selected, 0 otherwise
  # Objective: minimize sum of x[i] (number of sets selected)
  
  cvec <- rep(1, n_sets)
  
  # Variable types: all binary
  vtype <- rep("B", n_sets)
  
  # Bounds
  lb <- rep(0, n_sets)
  ub <- rep(1, n_sets)
  
  # Constraints: For each element j, sum over sets i covering j: x[i] >= 1
  # This ensures every element is covered by at least one selected set
  
  # Build constraint matrix: transpose of cover_matrix
  # Row j of Amat corresponds to element j
  # Entry [j,i] = 1 if set i covers element j
  
  Amat <- t(cover_matrix)
  bvec <- rep(1, n_elements)
  sense <- rep("G", n_elements)
  
  if (verbose) {
    cat("Solving ILP...\n")
  }
  
  # Solve
  result <- Rcplex(
    cvec = cvec,
    Amat = Amat,
    bvec = bvec,
    sense = sense,
    vtype = vtype,
    lb = lb,
    ub = ub,
    objsense = "min",
    control = list(
      trace = ifelse(verbose, 1, 0),
      tilim = time_limit
    )
  )
  
  # Extract solution
  status <- result$status
  objective <- result$obj
  solution <- result$xopt
  
  selected_sets <- which(solution > 0.5)
  
  if (verbose) {
    cat("\n")
    cat(strrep("=", 70))
    cat("\nSOLUTION\n")
    cat(strrep("=", 70))
    cat("\n")
    cat(sprintf("Status: %d ", status))
    if (status %in% c(0, 101, 102, 103)) {
      cat("(Optimal)\n")
    } else {
      cat("(Non-optimal)\n")
    }
    cat(sprintf("Objective: %d sets selected\n", objective))
    cat("\nSelected sets:\n")
    for (i in selected_sets) {
      # Count how many elements this set covers
      n_covered <- sum(cover_matrix[i, ])
      cat(sprintf("  %s (covers %d elements)\n", set_names[i], n_covered))
    }
    
    # Verify coverage
    covered_elements <- rep(FALSE, n_elements)
    for (i in selected_sets) {
      covered_elements <- covered_elements | (cover_matrix[i, ] == 1)
    }
    
    n_covered_total <- sum(covered_elements)
    cat(sprintf("\nTotal elements covered: %d/%d\n", n_covered_total, n_elements))
    
    if (n_covered_total < n_elements) {
      cat("WARNING: Not all elements are covered!\n")
      uncovered <- which(!covered_elements)
      cat("Uncovered elements:", paste(element_names[uncovered], collapse = ", "), "\n")
    }
    
    cat(strrep("=", 70))
    cat("\n")
  }
  
  return(list(
    selected_sets = selected_sets,
    selected_set_names = set_names[selected_sets],
    objective = objective,
    solution = solution,
    status = status,
    is_optimal = status %in% c(0, 101, 102, 103),
    cover_matrix = cover_matrix
  ))
}

#' Find multiple minimum set covers (all optimal solutions)
#' @param cover_matrix Binary matrix: rows are sets, columns are elements
#' @param max_solutions Maximum number of solutions to find
#' @param set_names Optional names for sets
#' @param element_names Optional names for elements
#' @param time_limit Time limit in seconds
#' @param verbose Print output
#' @return List of all optimal solutions
find_all_minimum_covers <- function(cover_matrix,
                                    max_solutions = 100,
                                    set_names = NULL,
                                    element_names = NULL,
                                    time_limit = 300,
                                    verbose = TRUE) {
  
  n_sets <- nrow(cover_matrix)
  n_elements <- ncol(cover_matrix)
  
  if (is.null(set_names)) {
    set_names <- paste0("Set_", 1:n_sets)
  }
  if (is.null(element_names)) {
    element_names <- paste0("Element_", 1:n_elements)
  }
  
  # Find first optimal solution
  first_solution <- minimum_set_cover(cover_matrix, set_names, element_names, 
                                     time_limit, verbose = FALSE)
  
  if (!first_solution$is_optimal) {
    cat("First solution not optimal, aborting\n")
    return(list(first_solution))
  }
  
  optimal_value <- first_solution$objective
  
  if (verbose) {
    cat(sprintf("Finding all solutions with %d sets...\n", optimal_value))
  }
  
  all_solutions <- list(first_solution)
  
  # Build base constraints
  cvec <- rep(1, n_sets)
  vtype <- rep("B", n_sets)
  lb <- rep(0, n_sets)
  ub <- rep(1, n_sets)
  
  Amat <- t(cover_matrix)
  bvec <- rep(1, n_elements)
  sense <- rep("G", n_elements)
  
  # Add constraint that objective must equal optimal value
  Amat <- rbind(Amat, rep(1, n_sets))
  bvec <- c(bvec, optimal_value)
  sense <- c(sense, "E")
  
  # Iteratively find new solutions by excluding previous ones
  for (sol_num in 2:max_solutions) {
    # Add constraint to exclude previous solution
    prev_selected <- all_solutions[[sol_num - 1]]$selected_sets
    
    # Constraint: sum of x[i] for i in prev_selected <= |prev_selected| - 1
    exclude_row <- rep(0, n_sets)
    exclude_row[prev_selected] <- 1
    
    Amat <- rbind(Amat, exclude_row)
    bvec <- c(bvec, length(prev_selected) - 1)
    sense <- c(sense, "L")
    
    # Solve
    result <- Rcplex(
      cvec = cvec,
      Amat = Amat,
      bvec = bvec,
      sense = sense,
      vtype = vtype,
      lb = lb,
      ub = ub,
      objsense = "min",
      control = list(trace = 0, tilim = time_limit, threads = 10)
    )
    
    if (!(result$status %in% c(0, 101, 102, 103))) {
      if (verbose) {
        cat(sprintf("No more solutions found after %d\n", sol_num - 1))
      }
      break
    }
    
    if (abs(result$obj - optimal_value) > 1e-6) {
      if (verbose) {
        cat(sprintf("No more optimal solutions (found %d)\n", sol_num - 1))
      }
      break
    }
    
    selected_sets <- which(result$xopt > 0.5)
    
    # Check if duplicate
    is_duplicate <- any(sapply(all_solutions, function(sol) {
      setequal(sol$selected_sets, selected_sets)
    }))
    
    if (is_duplicate) {
      if (verbose) {
        cat(sprintf("Found duplicate, stopping at %d solutions\n", sol_num - 1))
      }
      break
    }
    
    all_solutions[[sol_num]] <- list(
      selected_sets = selected_sets,
      selected_set_names = set_names[selected_sets],
      objective = result$obj
    )
    
    if (verbose && sol_num %% 10 == 0) {
      cat(sprintf("Found %d solutions so far...\n", sol_num))
    }
  }
  
  if (verbose) {
    cat(sprintf("\nFound %d optimal solutions with %d sets each\n",
                length(all_solutions), optimal_value))
  }
  
  return(all_solutions)
}

# Example usage:
#
# # Create example cover matrix
# # Rows = sets, Columns = elements to cover
cover_matrix <- matrix(c(
  1, 1, 0, 0, 0,  # Set 1 covers elements 1,2
  0, 1, 1, 0, 0,  # Set 2 covers elements 2,3
  0, 0, 1, 1, 0,  # Set 3 covers elements 3,4
  1, 0, 0, 1, 1,  # Set 4 covers elements 1,4,5
  0, 0, 0, 1, 1   # Set 5 covers elements 4,5
), nrow = 5, byrow = TRUE)

set_names <- c("A", "B", "C", "D", "E")
element_names <- c("e1", "e2", "e3", "e4", "e5")

# Find minimum set cover
result <- minimum_set_cover(cover_matrix, set_names, element_names)

# Find all optimal solutions
# all_results <- find_all_minimum_covers(cover_matrix, set_names, element_names)

# # For your obstacle problem:
# # Rows = obstacle types
# # Columns = tournaments to cover
# # cover_matrix[i,j] = 1 if obstacle i appears in tournament j
#
# obstacle_cover <- minimum_set_cover(
#   cover_matrix = obstacle_tournament_matrix,
#   set_names = obstacle_names,
#   element_names = tournament_ids
# )
